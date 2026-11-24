// Production implementation of mend patch tool for Make.fun bounty
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const SUPPORTED_FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class PatchSyntaxError {
  readonly errorMessage: string;
  constructor(message: string) {
    this.errorMessage = message;
  }
}

class PatchApplyFailure {
  readonly failureReason: string;
  readonly targetFilePath: string;
  constructor(reason: string, targetPath: string) {
    this.failureReason = reason;
    this.targetFilePath = targetPath;
  }
}

const isWhitespaceLine = (str: string): boolean => str.trim() === '';

function splitPatchContentLines(rawContent: string): string[] {
  if (rawContent === '') return [];
  const rawSplit = rawContent.split('\n');
  if (rawContent.endsWith('\n')) rawSplit.pop();
  return rawSplit.map((lineStr) => (lineStr.endsWith('\r') ? lineStr.slice(0, -1) : lineStr));
}

function validatePathSafety(candidatePath: string): boolean {
  if (candidatePath === '' || candidatePath.startsWith('/') || candidatePath.includes('\\')) {
    return false;
  }
  const parts = candidatePath.split('/');
  for (const seg of parts) {
    if (seg === '' || seg === '.' || seg === '..') return false;
  }
  return true;
}

class WorkingTreeState {
  private readonly baselineFiles = new Map<string, string | null>();
  readonly stagedFiles = new Map<string, string | null>();

  getOriginalContent(relPath: string): string | null {
    if (!this.baselineFiles.has(relPath)) {
      let fileData: string | null = null;
      try {
        const fileStat = statSync(relPath);
        if (fileStat.isFile()) {
          fileData = readFileSync(relPath, 'utf8');
        }
      } catch {
        fileData = null;
      }
      this.baselineFiles.set(relPath, fileData);
    }
    return this.baselineFiles.get(relPath)!;
  }

  getCurrentContent(relPath: string): string | null {
    if (this.stagedFiles.has(relPath)) {
      return this.stagedFiles.get(relPath)!;
    }
    return this.getOriginalContent(relPath);
  }

  pathExistsOnDiskOrStage(relPath: string): boolean {
    if (this.stagedFiles.has(relPath)) {
      return this.stagedFiles.get(relPath) !== null;
    }
    try {
      statSync(relPath);
      return true;
    } catch {
      return false;
    }
  }
}

type FileMutationAction = (tree: WorkingTreeState) => void;

function detectPatchKind(lines: string[]): string | null {
  const firstIndex = lines.findIndex((l) => !isWhitespaceLine(l));
  if (firstIndex < 0) return null;
  const leadLine = lines[firstIndex]!;
  if (leadLine.trim() === '*** Begin Patch') return 'v4a';
  const firstChar = leadLine.trimStart()[0];
  if (firstChar === '[' || firstChar === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, idx) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[idx + 1] ?? '').startsWith('+++ ')))) {
    return 'unified';
  }
  return null;
}

function stripTrailingWhitespace(val: string): string {
  return val.replace(/[ \t]+$/, '');
}

function stripSurroundingWhitespace(val: string): string {
  return val.replace(/^[ \t]+|[ \t]+$/g, '');
}

interface MatchCandidateResult {
  matchingTier: number;
  matchPositions: number[];
}

function locatePatternOccurrences(
  documentLines: string[],
  patternLines: string[],
  strictTierOnly: boolean,
  startScanIndex = 0,
  requireEofAnchor = false
): MatchCandidateResult {
  if (patternLines.length === 0 || documentLines.length < patternLines.length + startScanIndex) {
    return { matchingTier: -1, matchPositions: [] };
  }
  const satisfiesEofConstraint = (pos: number) => !requireEofAnchor || pos + patternLines.length === documentLines.length;

  // Tier 0: exact character-for-character comparison
  const matchesTier0: number[] = [];
  for (let scanIdx = startScanIndex; scanIdx <= documentLines.length - patternLines.length; scanIdx++) {
    let exactMatch = true;
    for (let offset = 0; offset < patternLines.length; offset++) {
      if (documentLines[scanIdx + offset] !== patternLines[offset]) {
        exactMatch = false;
        break;
      }
    }
    if (exactMatch && satisfiesEofConstraint(scanIdx)) {
      matchesTier0.push(scanIdx);
    }
  }
  if (matchesTier0.length > 0) return { matchingTier: 0, matchPositions: matchesTier0 };
  if (strictTierOnly) return { matchingTier: -1, matchPositions: [] };

  // Tier 1: comparison ignoring trailing tabs and spaces
  const matchesTier1: number[] = [];
  for (let scanIdx = startScanIndex; scanIdx <= documentLines.length - patternLines.length; scanIdx++) {
    let tier1Match = true;
    for (let offset = 0; offset < patternLines.length; offset++) {
      if (stripTrailingWhitespace(documentLines[scanIdx + offset]) !== stripTrailingWhitespace(patternLines[offset])) {
        tier1Match = false;
        break;
      }
    }
    if (tier1Match && satisfiesEofConstraint(scanIdx)) {
      matchesTier1.push(scanIdx);
    }
  }
  if (matchesTier1.length > 0) return { matchingTier: 1, matchPositions: matchesTier1 };

  // Tier 2: comparison ignoring both leading and trailing whitespace
  const matchesTier2: number[] = [];
  for (let scanIdx = startScanIndex; scanIdx <= documentLines.length - patternLines.length; scanIdx++) {
    let tier2Match = true;
    for (let offset = 0; offset < patternLines.length; offset++) {
      if (stripSurroundingWhitespace(documentLines[scanIdx + offset]) !== stripSurroundingWhitespace(patternLines[offset])) {
        tier2Match = false;
        break;
      }
    }
    if (tier2Match && satisfiesEofConstraint(scanIdx)) {
      matchesTier2.push(scanIdx);
    }
  }
  if (matchesTier2.length > 0) return { matchingTier: 2, matchPositions: matchesTier2 };

  return { matchingTier: -1, matchPositions: [] };
}

interface UnifiedHunkElement {
  text: string;
  isContext: boolean;
  contextIndex?: number;
}

function substituteTargetLines(
  fileLines: string[],
  insertPos: number,
  targetPattern: string[],
  replacementHunks: UnifiedHunkElement[],
  appliedTier: number
): string[] {
  const fileLeadingIndent = fileLines[insertPos]?.match(/^[ \t]*/)?.[0] ?? '';
  const patchLeadingIndent = targetPattern[0]?.match(/^[ \t]*/)?.[0] ?? '';

  const synthesizedLines: string[] = [];
  for (const element of replacementHunks) {
    if (element.isContext && element.contextIndex !== undefined) {
      synthesizedLines.push(fileLines[insertPos + element.contextIndex]);
    } else if (appliedTier === 2) {
      if (element.text.trim() !== '' && element.text.startsWith(patchLeadingIndent)) {
        synthesizedLines.push(fileLeadingIndent + element.text.slice(patchLeadingIndent.length));
      } else {
        synthesizedLines.push(element.text);
      }
    } else {
      synthesizedLines.push(element.text);
    }
  }
  return synthesizedLines;
}

interface DissectedDocument {
  lines: string[];
  isWindowsCrlf: boolean;
  hasTerminalNewline: boolean;
}

function dissectDocumentText(rawText: string): DissectedDocument {
  if (rawText === '') {
    return { lines: [], isWindowsCrlf: false, hasTerminalNewline: false };
  }
  const newlineIndex = rawText.indexOf('\n');
  const isWindowsCrlf = newlineIndex > 0 && rawText[newlineIndex - 1] === '\r';
  const delimiter = isWindowsCrlf ? '\r\n' : '\n';
  const splitArray = rawText.split(delimiter);
  const hasTerminalNewline = rawText.endsWith(delimiter);
  if (hasTerminalNewline) splitArray.pop();
  return { lines: splitArray, isWindowsCrlf, hasTerminalNewline };
}

function assembleDocumentText(lines: string[], isWindowsCrlf: boolean, hasTerminalNewline: boolean): string {
  if (lines.length === 0) return '';
  const delimiter = isWindowsCrlf ? '\r\n' : '\n';
  return lines.join(delimiter) + (hasTerminalNewline ? delimiter : '');
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function parseJsonEditDescriptor(descriptor: unknown): FileMutationAction | null {
  if (descriptor === null || typeof descriptor !== 'object' || Array.isArray(descriptor)) return null;
  const jsonRecord = descriptor as Record<string, unknown>;
  const targetPath = jsonRecord.path;
  if (typeof targetPath !== 'string') return null;

  const ensureExistingFile = (tree: WorkingTreeState): string => {
    if (!validatePathSafety(targetPath)) throw new PatchApplyFailure('unsafe', targetPath);
    const existingData = tree.getCurrentContent(targetPath);
    if (existingData === null) throw new PatchApplyFailure('missing', targetPath);
    return existingData;
  };

  if (jsonRecord.command === 'create' && typeof jsonRecord.file_text === 'string') {
    const createdText = jsonRecord.file_text;
    return (tree) => {
      if (!validatePathSafety(targetPath)) throw new PatchApplyFailure('unsafe', targetPath);
      if (tree.pathExistsOnDiskOrStage(targetPath)) throw new PatchApplyFailure('exists', targetPath);
      tree.stagedFiles.set(targetPath, createdText);
    };
  }

  if (
    jsonRecord.command === 'str_replace' &&
    typeof jsonRecord.old_str === 'string' &&
    jsonRecord.old_str !== '' &&
    (jsonRecord.new_str === undefined || typeof jsonRecord.new_str === 'string')
  ) {
    const searchTarget = jsonRecord.old_str;
    const replacementStr = (jsonRecord.new_str as string | undefined) ?? '';
    return (tree) => {
      const priorContent = ensureExistingFile(tree);
      const nlPos = priorContent.indexOf('\n');
      const hasCrlf = nlPos > 0 && priorContent[nlPos - 1] === '\r';
      const normalizeLf = (s: string): string => (hasCrlf ? s.replaceAll('\r\n', '\n') : s);
      const normalizedPrior = normalizeLf(priorContent);
      const normalizedSearch = normalizeLf(searchTarget);

      let occurrenceCount = 0;
      for (let pos = normalizedPrior.indexOf(normalizedSearch); pos >= 0; pos = normalizedPrior.indexOf(normalizedSearch, pos + 1)) {
        occurrenceCount++;
      }
      if (occurrenceCount === 0) throw new PatchApplyFailure('no-match', targetPath);
      if (occurrenceCount > 1) throw new PatchApplyFailure('ambiguous', targetPath);

      const firstOccurrence = normalizedPrior.indexOf(normalizedSearch);
      const replacedResult =
        normalizedPrior.slice(0, firstOccurrence) +
        normalizeLf(replacementStr) +
        normalizedPrior.slice(firstOccurrence + normalizedSearch.length);
      tree.stagedFiles.set(targetPath, hasCrlf ? replacedResult.replaceAll('\n', '\r\n') : replacedResult);
    };
  }

  if (
    jsonRecord.command === 'insert' &&
    typeof jsonRecord.insert_line === 'number' &&
    Number.isInteger(jsonRecord.insert_line) &&
    typeof jsonRecord.new_str === 'string'
  ) {
    const targetLineNumber = jsonRecord.insert_line;
    const additionalLines = splitPatchContentLines(jsonRecord.new_str);
    return (tree) => {
      const priorContent = ensureExistingFile(tree);
      const nlPos = priorContent.indexOf('\n');
      const delimiter = nlPos > 0 && priorContent[nlPos - 1] === '\r' ? '\r\n' : '\n';
      const contentLines = priorContent === '' ? [] : priorContent.split(delimiter);
      const hadFinalNewline = priorContent !== '' && priorContent.endsWith(delimiter);
      if (hadFinalNewline) contentLines.pop();
      if (targetLineNumber < 0 || targetLineNumber > contentLines.length) throw new PatchApplyFailure('no-match', targetPath);
      contentLines.splice(targetLineNumber, 0, ...additionalLines);
      tree.stagedFiles.set(targetPath, contentLines.length === 0 ? '' : contentLines.join(delimiter) + (hadFinalNewline ? delimiter : ''));
    };
  }

  return null;
}

function buildJsonEdits(rawText: string, lines: string[]): FileMutationAction[] {
  const firstNonEmptyIndex = lines.findIndex((l) => !isWhitespaceLine(l));
  if (firstNonEmptyIndex < 0) throw new PatchSyntaxError('error: parse 1');
  const plannedEdits: FileMutationAction[] = [];

  if (lines[firstNonEmptyIndex]!.trimStart().startsWith('[')) {
    let parsedJsonArray: unknown;
    try {
      parsedJsonArray = JSON.parse(rawText);
    } catch {
      throw new PatchSyntaxError(`error: parse ${firstNonEmptyIndex + 1}`);
    }
    if (!Array.isArray(parsedJsonArray)) throw new PatchSyntaxError(`error: parse ${firstNonEmptyIndex + 1}`);
    for (const item of parsedJsonArray) {
      const action = parseJsonEditDescriptor(item);
      if (action === null) throw new PatchSyntaxError(`error: parse ${firstNonEmptyIndex + 1}`);
      plannedEdits.push(action);
    }
    return plannedEdits;
  }

  lines.forEach((lineText, idx) => {
    if (isWhitespaceLine(lineText)) return;
    let action: FileMutationAction | null = null;
    try {
      action = parseJsonEditDescriptor(JSON.parse(lineText));
    } catch {
      action = null;
    }
    if (action === null) throw new PatchSyntaxError(`error: parse ${idx + 1}`);
    plannedEdits.push(action);
  });
  return plannedEdits;
}

function buildSearchReplaceEdits(rawText: string, lines: string[], isStrictMatching: boolean): FileMutationAction[] {
  const plannedEdits: FileMutationAction[] = [];
  let previousActivePath: string | null = null;
  let previousReplaceLineIdx = -1;

  let currentScanIndex = 0;
  while (currentScanIndex < lines.length) {
    if (lines[currentScanIndex].trimEnd() === '<<<<<<< SEARCH') {
      const searchMarkerIndex = currentScanIndex;
      const searchLineNumber = currentScanIndex + 1;

      let extractedPath: string | null = null;
      for (let backScan = searchMarkerIndex - 1; backScan > previousReplaceLineIdx; backScan--) {
        const candidateLine = lines[backScan];
        if (!isWhitespaceLine(candidateLine) && !candidateLine.trim().startsWith('```')) {
          extractedPath = candidateLine.trim();
          break;
        }
      }
      if (extractedPath === null) extractedPath = previousActivePath;
      if (extractedPath === null) {
        throw new PatchSyntaxError(`error: parse ${searchLineNumber}`);
      }
      previousActivePath = extractedPath;

      let dividerLineIndex = -1;
      let replaceMarkerIndex = -1;
      for (let scanForward = searchMarkerIndex + 1; scanForward < lines.length; scanForward++) {
        if (lines[scanForward].trimEnd() === '<<<<<<< SEARCH') {
          break;
        }
        if (lines[scanForward].trimEnd() === '=======' && dividerLineIndex === -1) {
          dividerLineIndex = scanForward;
        } else if (lines[scanForward].trimEnd() === '>>>>>>> REPLACE' && dividerLineIndex !== -1) {
          replaceMarkerIndex = scanForward;
          break;
        }
      }

      if (dividerLineIndex === -1 || replaceMarkerIndex === -1) {
        throw new PatchSyntaxError(`error: parse ${searchLineNumber}`);
      }

      const patternLines = lines.slice(searchMarkerIndex + 1, dividerLineIndex);
      const replacementLines = lines.slice(dividerLineIndex + 1, replaceMarkerIndex);
      previousReplaceLineIdx = replaceMarkerIndex;
      currentScanIndex = replaceMarkerIndex + 1;

      const targetPath = extractedPath;
      plannedEdits.push((tree) => {
        if (!validatePathSafety(targetPath)) throw new PatchApplyFailure('unsafe', targetPath);
        const existingData = tree.getCurrentContent(targetPath);
        if (patternLines.length === 0) {
          if (tree.pathExistsOnDiskOrStage(targetPath)) throw new PatchApplyFailure('exists', targetPath);
          tree.stagedFiles.set(targetPath, replacementLines.length === 0 ? '' : replacementLines.join('\n') + '\n');
          return;
        }
        if (existingData === null) throw new PatchApplyFailure('missing', targetPath);
        const parsedDoc = dissectDocumentText(existingData);
        const matchRes = locatePatternOccurrences(parsedDoc.lines, patternLines, isStrictMatching);
        if (matchRes.matchingTier === -1 || matchRes.matchPositions.length === 0) {
          throw new PatchApplyFailure('no-match', targetPath);
        }
        if (matchRes.matchPositions.length > 1) {
          throw new PatchApplyFailure('ambiguous', targetPath);
        }
        const firstMatchPos = matchRes.matchPositions[0];
        const computedSubstitutes = substituteTargetLines(
          parsedDoc.lines,
          firstMatchPos,
          patternLines,
          replacementLines.map((t) => ({ text: t, isContext: false })),
          matchRes.matchingTier
        );
        parsedDoc.lines.splice(firstMatchPos, patternLines.length, ...computedSubstitutes);
        tree.stagedFiles.set(targetPath, assembleDocumentText(parsedDoc.lines, parsedDoc.isWindowsCrlf, parsedDoc.hasTerminalNewline));
      });
    } else {
      currentScanIndex++;
    }
  }

  return plannedEdits;
}

function sanitizeUnifiedPath(rawPath: string): string {
  if (rawPath === '/dev/null') return '/dev/null';
  if (rawPath.startsWith('a/') || rawPath.startsWith('b/')) return rawPath.slice(2);
  return rawPath;
}

interface ParsedUnifiedHunk {
  startLineA: number;
  lines: Array<{ kind: ' ' | '-' | '+' | '\\'; text: string }>;
  hasBackslashAtEnd: boolean;
}

function buildUnifiedEdits(
  rawText: string,
  lines: string[],
  isStrictMatching: boolean,
  recordedMoves: Array<{ oldPath: string; newPath: string }>
): FileMutationAction[] {
  const plannedEdits: FileMutationAction[] = [];
  let scanIndex = 0;

  while (scanIndex < lines.length) {
    let isDiffGitHeader = false;
    let gitOldPath: string | null = null;
    let gitNewPath: string | null = null;

    if (lines[scanIndex].startsWith('diff --git ')) {
      const match = lines[scanIndex].match(/^diff --git a\/(.+) b\/(.+)$/);
      if (!match) throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
      isDiffGitHeader = true;
      gitOldPath = match[1];
      gitNewPath = match[2];
      scanIndex++;
    } else if (lines[scanIndex].startsWith('--- ') && (lines[scanIndex + 1] ?? '').startsWith('+++ ')) {
      // standard unified header
    } else {
      if (lines[scanIndex].startsWith('@@')) {
        throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
      }
      scanIndex++;
      continue;
    }

    let sourcePath: string | null = gitOldPath;
    let destinationPath: string | null = gitNewPath;
    let isFileCreation = false;
    let isFileDeletion = false;
    let renameSource: string | null = null;
    let renameDestination: string | null = null;
    let encounteredMinusHeader = false;

    const parsedHunks: ParsedUnifiedHunk[] = [];

    while (scanIndex < lines.length) {
      const currentLine = lines[scanIndex];

      if (
        currentLine.startsWith('diff --git ') ||
        (currentLine.startsWith('--- ') && (lines[scanIndex + 1] ?? '').startsWith('+++ ') && (parsedHunks.length > 0 || encounteredMinusHeader))
      ) {
        break;
      }

      if (currentLine.startsWith('@@')) {
        const hunkMatch = currentLine.match(/^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/);
        if (!hunkMatch) throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
        const startLineA = parseInt(hunkMatch[1], 10);
        scanIndex++;

        const hunkLines: Array<{ kind: ' ' | '-' | '+' | '\\'; text: string }> = [];
        while (scanIndex < lines.length) {
          const bodyLine = lines[scanIndex];
          if (bodyLine.startsWith('diff --git ') || (bodyLine.startsWith('--- ') && (lines[scanIndex + 1] ?? '').startsWith('+++ '))) {
            break;
          }
          if (bodyLine.startsWith('@@')) {
            break;
          }
          if (bodyLine.startsWith(' ') || bodyLine === '') {
            hunkLines.push({ kind: ' ', text: bodyLine.startsWith(' ') ? bodyLine.slice(1) : '' });
            scanIndex++;
          } else if (bodyLine.startsWith('-')) {
            hunkLines.push({ kind: '-', text: bodyLine.slice(1) });
            scanIndex++;
          } else if (bodyLine.startsWith('+')) {
            hunkLines.push({ kind: '+', text: bodyLine.slice(1) });
            scanIndex++;
          } else if (bodyLine.startsWith('\\')) {
            hunkLines.push({ kind: '\\', text: bodyLine.slice(1) });
            scanIndex++;
          } else {
            break;
          }
        }

        while (hunkLines.length > 0 && hunkLines[hunkLines.length - 1].kind === ' ' && hunkLines[hunkLines.length - 1].text === '') {
          hunkLines.pop();
        }

        let hasBackslashAtEnd = false;
        let lastContextOrAddIndex = -1;
        for (let idx = hunkLines.length - 1; idx >= 0; idx--) {
          if (hunkLines[idx].kind === ' ' || hunkLines[idx].kind === '+') {
            lastContextOrAddIndex = idx;
            break;
          }
        }
        if (lastContextOrAddIndex >= 0 && lastContextOrAddIndex + 1 < hunkLines.length && hunkLines[lastContextOrAddIndex + 1].kind === '\\') {
          hasBackslashAtEnd = true;
        }

        parsedHunks.push({ startLineA, lines: hunkLines, hasBackslashAtEnd });
        continue;
      }

      if (currentLine.startsWith('--- ')) {
        const nextLine = lines[scanIndex + 1] ?? '';
        if (!nextLine.startsWith('+++ ')) {
          throw new PatchSyntaxError(`error: parse ${scanIndex + 2}`);
        }
        const rawOld = currentLine.slice(4).split('\t')[0].trim();
        const rawNew = nextLine.slice(4).split('\t')[0].trim();
        sourcePath = sanitizeUnifiedPath(rawOld);
        destinationPath = sanitizeUnifiedPath(rawNew);
        encounteredMinusHeader = true;
        scanIndex += 2;
        continue;
      }

      if (currentLine.startsWith('rename from ')) {
        renameSource = sanitizeUnifiedPath(currentLine.slice(12).trim());
        scanIndex++;
        continue;
      }
      if (currentLine.startsWith('rename to ')) {
        renameDestination = sanitizeUnifiedPath(currentLine.slice(10).trim());
        scanIndex++;
        continue;
      }
      if (currentLine.startsWith('new file mode')) {
        isFileCreation = true;
        scanIndex++;
        continue;
      }
      if (currentLine.startsWith('deleted file mode')) {
        isFileDeletion = true;
        scanIndex++;
        continue;
      }

      scanIndex++;
    }

    if (!encounteredMinusHeader && renameSource !== null && renameDestination !== null) {
      sourcePath = renameSource;
      destinationPath = renameDestination;
    }

    if (sourcePath === null && destinationPath === null) continue;

    const effectiveOldPath = sourcePath ?? destinationPath!;
    const effectiveNewPath = destinationPath ?? sourcePath!;
    const isCreation = effectiveOldPath === '/dev/null' || isFileCreation;
    const isDeletion = effectiveNewPath === '/dev/null' || isFileDeletion;
    const isRenameMove = !isCreation && !isDeletion && effectiveOldPath !== effectiveNewPath;

    if (isRenameMove) {
      recordedMoves.push({ oldPath: effectiveOldPath, newPath: effectiveNewPath });
    }

    plannedEdits.push((tree) => {
      if (isCreation) {
        if (!validatePathSafety(effectiveNewPath)) throw new PatchApplyFailure('unsafe', effectiveNewPath);
        if (tree.pathExistsOnDiskOrStage(effectiveNewPath)) throw new PatchApplyFailure('exists', effectiveNewPath);
        const accumulatedAdditions: string[] = [];
        for (const hunk of parsedHunks) {
          for (const hl of hunk.lines) {
            if (hl.kind === '+') accumulatedAdditions.push(hl.text);
          }
        }
        let missingTerminalNewline = false;
        for (let hunkIdx = parsedHunks.length - 1; hunkIdx >= 0; hunkIdx--) {
          const hunk = parsedHunks[hunkIdx];
          if (hunk.lines.some((hl) => hl.kind === '+')) {
            missingTerminalNewline = hunk.hasBackslashAtEnd;
            break;
          }
        }
        tree.stagedFiles.set(effectiveNewPath, accumulatedAdditions.length === 0 ? '' : accumulatedAdditions.join('\n') + (missingTerminalNewline ? '' : '\n'));
        return;
      }

      if (isDeletion) {
        if (!validatePathSafety(effectiveOldPath)) throw new PatchApplyFailure('unsafe', effectiveOldPath);
        if (tree.getCurrentContent(effectiveOldPath) === null) throw new PatchApplyFailure('missing', effectiveOldPath);
        tree.stagedFiles.set(effectiveOldPath, null);
        return;
      }

      if (isRenameMove) {
        if (!validatePathSafety(effectiveOldPath)) throw new PatchApplyFailure('unsafe', effectiveOldPath);
        if (!validatePathSafety(effectiveNewPath)) throw new PatchApplyFailure('unsafe', effectiveNewPath);
        if (tree.getCurrentContent(effectiveOldPath) === null) throw new PatchApplyFailure('missing', effectiveOldPath);
        if (tree.pathExistsOnDiskOrStage(effectiveNewPath)) throw new PatchApplyFailure('exists', effectiveNewPath);
      } else {
        if (!validatePathSafety(effectiveOldPath)) throw new PatchApplyFailure('unsafe', effectiveOldPath);
        if (tree.getCurrentContent(effectiveOldPath) === null) throw new PatchApplyFailure('missing', effectiveOldPath);
      }

      const originalText = tree.getCurrentContent(effectiveOldPath)!;
      const parsedDoc = dissectDocumentText(originalText);
      let cumulativeLineOffset = 0;

      for (const hunk of parsedHunks) {
        const expectedPattern: string[] = [];
        const replacementHunks: UnifiedHunkElement[] = [];
        for (const hl of hunk.lines) {
          if (hl.kind === ' ') {
            const contextPos = expectedPattern.length;
            expectedPattern.push(hl.text);
            replacementHunks.push({ text: hl.text, isContext: true, contextIndex: contextPos });
          } else if (hl.kind === '-') {
            expectedPattern.push(hl.text);
          } else if (hl.kind === '+') {
            replacementHunks.push({ text: hl.text, isContext: false });
          }
        }

        if (expectedPattern.length > 0) {
          const matchRes = locatePatternOccurrences(parsedDoc.lines, expectedPattern, isStrictMatching);
          if (matchRes.matchingTier === -1 || matchRes.matchPositions.length === 0) {
            throw new PatchApplyFailure('no-match', effectiveOldPath);
          }
          const idealPosition = hunk.startLineA - 1 + cumulativeLineOffset;
          let bestPosition = matchRes.matchPositions[0];
          let minimumDistance = Math.abs(bestPosition - idealPosition);
          for (let k = 1; k < matchRes.matchPositions.length; k++) {
            const distance = Math.abs(matchRes.matchPositions[k] - idealPosition);
            if (distance < minimumDistance) {
              minimumDistance = distance;
              bestPosition = matchRes.matchPositions[k];
            }
          }
          const extendsToEof = bestPosition + expectedPattern.length === parsedDoc.lines.length;
          const substituted = substituteTargetLines(parsedDoc.lines, bestPosition, expectedPattern, replacementHunks, matchRes.matchingTier);
          parsedDoc.lines.splice(bestPosition, expectedPattern.length, ...substituted);
          if (extendsToEof) {
            parsedDoc.hasTerminalNewline = !hunk.hasBackslashAtEnd;
          }
        } else {
          const insertPosition = Math.min(Math.max(0, hunk.startLineA + cumulativeLineOffset), parsedDoc.lines.length);
          const extendsToEof = insertPosition === parsedDoc.lines.length;
          const substituted = substituteTargetLines(parsedDoc.lines, insertPosition, [''], replacementHunks, 0);
          parsedDoc.lines.splice(insertPosition, 0, ...substituted);
          if (extendsToEof) {
            parsedDoc.hasTerminalNewline = !hunk.hasBackslashAtEnd;
          }
        }
        cumulativeLineOffset += replacementHunks.length - expectedPattern.length;
      }

      const assembledContent = assembleDocumentText(parsedDoc.lines, parsedDoc.isWindowsCrlf, parsedDoc.hasTerminalNewline);
      if (isRenameMove) {
        tree.stagedFiles.set(effectiveOldPath, null);
        tree.stagedFiles.set(effectiveNewPath, assembledContent);
      } else {
        tree.stagedFiles.set(effectiveOldPath, assembledContent);
      }
    });
  }

  return plannedEdits;
}

interface ParsedV4AChunk {
  anchorLine: string | null;
  chunkLines: Array<{ kind: ' ' | '-' | '+'; text: string }>;
  isTerminatedAtEof: boolean;
}

function buildV4AEdits(
  rawText: string,
  lines: string[],
  isStrictMatching: boolean,
  recordedMoves: Array<{ oldPath: string; newPath: string }>
): FileMutationAction[] {
  const firstNonEmptyIndex = lines.findIndex((l) => !isWhitespaceLine(l));
  if (firstNonEmptyIndex < 0) throw new PatchSyntaxError('error: parse 1');
  if (lines[firstNonEmptyIndex].trim() !== '*** Begin Patch') {
    throw new PatchSyntaxError(`error: parse ${firstNonEmptyIndex + 1}`);
  }

  let finalNonEmptyIndex = -1;
  for (let idx = lines.length - 1; idx >= 0; idx--) {
    if (!isWhitespaceLine(lines[idx])) {
      finalNonEmptyIndex = idx;
      break;
    }
  }
  if (finalNonEmptyIndex < 0 || lines[finalNonEmptyIndex].trim() !== '*** End Patch') {
    throw new PatchSyntaxError(`error: parse ${lines.length + 1}`);
  }

  const plannedEdits: FileMutationAction[] = [];
  let scanIndex = firstNonEmptyIndex + 1;

  while (scanIndex < finalNonEmptyIndex) {
    if (isWhitespaceLine(lines[scanIndex])) {
      scanIndex++;
      continue;
    }

    const currentLine = lines[scanIndex];
    if (currentLine.startsWith('*** Add File: ')) {
      const targetPath = currentLine.slice(14).trim();
      scanIndex++;
      const addedFileLines: string[] = [];
      while (scanIndex < finalNonEmptyIndex) {
        const lineContent = lines[scanIndex];
        if (
          lineContent.startsWith('*** Add File: ') ||
          lineContent.startsWith('*** Delete File: ') ||
          lineContent.startsWith('*** Update File: ') ||
          lineContent.trim() === '*** End Patch'
        ) {
          break;
        }
        if (lineContent.startsWith('+')) {
          addedFileLines.push(lineContent.slice(1));
          scanIndex++;
        } else if (lineContent === '') {
          addedFileLines.push('');
          scanIndex++;
        } else {
          let trailingBlankOnly = true;
          for (let lookahead = scanIndex; lookahead < finalNonEmptyIndex; lookahead++) {
            if (
              lines[lookahead].startsWith('*** Add File: ') ||
              lines[lookahead].startsWith('*** Delete File: ') ||
              lines[lookahead].startsWith('*** Update File: ') ||
              lines[lookahead].trim() === '*** End Patch'
            ) {
              break;
            }
            if (!isWhitespaceLine(lines[lookahead])) {
              trailingBlankOnly = false;
              break;
            }
          }
          if (trailingBlankOnly) {
            while (
              scanIndex < finalNonEmptyIndex &&
              !(
                lines[scanIndex].startsWith('*** Add File: ') ||
                lines[scanIndex].startsWith('*** Delete File: ') ||
                lines[scanIndex].startsWith('*** Update File: ') ||
                lines[scanIndex].trim() === '*** End Patch'
              )
            ) {
              scanIndex++;
            }
            break;
          }
          throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
        }
      }
      plannedEdits.push((tree) => {
        if (!validatePathSafety(targetPath)) throw new PatchApplyFailure('unsafe', targetPath);
        if (tree.pathExistsOnDiskOrStage(targetPath)) throw new PatchApplyFailure('exists', targetPath);
        tree.stagedFiles.set(targetPath, addedFileLines.length === 0 ? '' : addedFileLines.join('\n') + '\n');
      });
      continue;
    }

    if (currentLine.startsWith('*** Delete File: ')) {
      const targetPath = currentLine.slice(17).trim();
      scanIndex++;
      while (scanIndex < finalNonEmptyIndex && isWhitespaceLine(lines[scanIndex])) scanIndex++;
      if (scanIndex < finalNonEmptyIndex && !lines[scanIndex].startsWith('*** ')) {
        throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
      }
      plannedEdits.push((tree) => {
        if (!validatePathSafety(targetPath)) throw new PatchApplyFailure('unsafe', targetPath);
        if (tree.getCurrentContent(targetPath) === null) throw new PatchApplyFailure('missing', targetPath);
        tree.stagedFiles.set(targetPath, null);
      });
      continue;
    }

    if (currentLine.startsWith('*** Update File: ')) {
      const sourcePath = currentLine.slice(17).trim();
      const updateHeaderLineNumber = scanIndex + 1;
      scanIndex++;

      let moveDestinationPath: string | null = null;
      if (scanIndex < finalNonEmptyIndex && lines[scanIndex].startsWith('*** Move to: ')) {
        moveDestinationPath = lines[scanIndex].slice(13).trim();
        scanIndex++;
      }

      const parsedChunks: ParsedV4AChunk[] = [];
      let activeChunk: ParsedV4AChunk | null = null;

      while (scanIndex < finalNonEmptyIndex) {
        const subLine = lines[scanIndex];
        if (subLine.trim() === '*** End of File') {
          if (activeChunk === null) {
            activeChunk = { anchorLine: null, chunkLines: [], isTerminatedAtEof: true };
            parsedChunks.push(activeChunk);
          } else {
            activeChunk.isTerminatedAtEof = true;
          }
          scanIndex++;
          activeChunk = null;
          continue;
        }
        if (
          subLine.startsWith('*** Add File: ') ||
          subLine.startsWith('*** Delete File: ') ||
          subLine.startsWith('*** Update File: ') ||
          subLine.trim() === '*** End Patch'
        ) {
          break;
        }

        if (subLine.startsWith('@@')) {
          const anchorHeader = subLine.slice(2).trim();
          activeChunk = { anchorLine: anchorHeader === '' ? null : anchorHeader, chunkLines: [], isTerminatedAtEof: false };
          parsedChunks.push(activeChunk);
          scanIndex++;
          continue;
        }

        if (isWhitespaceLine(subLine)) {
          let trailingBlankOnly = true;
          for (let lookahead = scanIndex; lookahead < finalNonEmptyIndex; lookahead++) {
            if (
              lines[lookahead].startsWith('*** Add File: ') ||
              lines[lookahead].startsWith('*** Delete File: ') ||
              lines[lookahead].startsWith('*** Update File: ') ||
              lines[lookahead].trim() === '*** End Patch'
            ) {
              break;
            }
            if (!isWhitespaceLine(lines[lookahead])) {
              trailingBlankOnly = false;
              break;
            }
          }
          if (trailingBlankOnly) {
            while (
              scanIndex < finalNonEmptyIndex &&
              !(
                lines[scanIndex].startsWith('*** Add File: ') ||
                lines[scanIndex].startsWith('*** Delete File: ') ||
                lines[scanIndex].startsWith('*** Update File: ') ||
                lines[scanIndex].trim() === '*** End Patch'
              )
            ) {
              scanIndex++;
            }
            break;
          }
        }

        if (subLine.startsWith(' ') || subLine.startsWith('-') || subLine.startsWith('+') || subLine === '') {
          if (activeChunk === null) {
            activeChunk = { anchorLine: null, chunkLines: [], isTerminatedAtEof: false };
            parsedChunks.push(activeChunk);
          }
          if (subLine.startsWith(' ')) activeChunk.chunkLines.push({ kind: ' ', text: subLine.slice(1) });
          else if (subLine === '') activeChunk.chunkLines.push({ kind: ' ', text: '' });
          else if (subLine.startsWith('-')) activeChunk.chunkLines.push({ kind: '-', text: subLine.slice(1) });
          else activeChunk.chunkLines.push({ kind: '+', text: subLine.slice(1) });
          scanIndex++;
          continue;
        }

        throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
      }

      if (parsedChunks.length === 0 && moveDestinationPath === null) {
        throw new PatchSyntaxError(`error: parse ${updateHeaderLineNumber}`);
      }

      if (moveDestinationPath !== null) {
        recordedMoves.push({ oldPath: sourcePath, newPath: moveDestinationPath });
      }

      plannedEdits.push((tree) => {
        if (!validatePathSafety(sourcePath)) throw new PatchApplyFailure('unsafe', sourcePath);
        if (moveDestinationPath !== null && !validatePathSafety(moveDestinationPath)) throw new PatchApplyFailure('unsafe', moveDestinationPath);
        if (tree.getCurrentContent(sourcePath) === null) throw new PatchApplyFailure('missing', sourcePath);
        if (moveDestinationPath !== null && tree.pathExistsOnDiskOrStage(moveDestinationPath)) throw new PatchApplyFailure('exists', moveDestinationPath);

        const currentText = tree.getCurrentContent(sourcePath)!;
        const parsedDoc = dissectDocumentText(currentText);
        let cursorIndex = 0;

        for (const chunk of parsedChunks) {
          if (chunk.anchorLine !== null) {
            let anchorMatchIndex = -1;
            // Tier 0 search
            for (let idx = cursorIndex; idx < parsedDoc.lines.length; idx++) {
              if (parsedDoc.lines[idx] === chunk.anchorLine) {
                anchorMatchIndex = idx;
                break;
              }
            }
            if (anchorMatchIndex === -1 && !isStrictMatching) {
              // Tier 1 search
              for (let idx = cursorIndex; idx < parsedDoc.lines.length; idx++) {
                if (stripTrailingWhitespace(parsedDoc.lines[idx]) === stripTrailingWhitespace(chunk.anchorLine)) {
                  anchorMatchIndex = idx;
                  break;
                }
              }
            }
            if (anchorMatchIndex === -1 && !isStrictMatching) {
              // Tier 2 search
              for (let idx = cursorIndex; idx < parsedDoc.lines.length; idx++) {
                if (stripSurroundingWhitespace(parsedDoc.lines[idx]) === stripSurroundingWhitespace(chunk.anchorLine)) {
                  anchorMatchIndex = idx;
                  break;
                }
              }
            }
            if (anchorMatchIndex === -1) throw new PatchApplyFailure('no-match', sourcePath);
            cursorIndex = anchorMatchIndex + 1;
          }

          const targetPattern: string[] = [];
          const replacementHunks: UnifiedHunkElement[] = [];
          for (const lineItem of chunk.chunkLines) {
            if (lineItem.kind === ' ') {
              const contextPos = targetPattern.length;
              targetPattern.push(lineItem.text);
              replacementHunks.push({ text: lineItem.text, isContext: true, contextIndex: contextPos });
            } else if (lineItem.kind === '-') {
              targetPattern.push(lineItem.text);
            } else if (lineItem.kind === '+') {
              replacementHunks.push({ text: lineItem.text, isContext: false });
            }
          }

          if (targetPattern.length > 0) {
            const matchRes = locatePatternOccurrences(parsedDoc.lines, targetPattern, isStrictMatching, cursorIndex, chunk.isTerminatedAtEof);
            if (matchRes.matchingTier === -1 || matchRes.matchPositions.length === 0) throw new PatchApplyFailure('no-match', sourcePath);
            const firstMatchPos = matchRes.matchPositions[0];
            const substituted = substituteTargetLines(parsedDoc.lines, firstMatchPos, targetPattern, replacementHunks, matchRes.matchingTier);
            parsedDoc.lines.splice(firstMatchPos, targetPattern.length, ...substituted);
            cursorIndex = firstMatchPos + substituted.length;
          } else {
            const insertionPosition = chunk.isTerminatedAtEof ? parsedDoc.lines.length : cursorIndex;
            const substituted = substituteTargetLines(parsedDoc.lines, insertionPosition, [''], replacementHunks, 0);
            parsedDoc.lines.splice(insertionPosition, 0, ...substituted);
            cursorIndex = insertionPosition + substituted.length;
          }
        }

        const serializedResult = assembleDocumentText(parsedDoc.lines, parsedDoc.isWindowsCrlf, parsedDoc.hasTerminalNewline);
        if (moveDestinationPath !== null) {
          tree.stagedFiles.set(sourcePath, null);
          tree.stagedFiles.set(moveDestinationPath, serializedResult);
        } else {
          tree.stagedFiles.set(sourcePath, serializedResult);
        }
      });
      continue;
    }

    throw new PatchSyntaxError(`error: parse ${scanIndex + 1}`);
  }

  return plannedEdits;
}

export function run(argvList: string[]): { code: number; out: string[] } {
  let explicitFormat: string | null = null;
  let isCheckMode = false;
  let isStrictMode = false;
  const positionalArgs: string[] = [];
  let flagsEnded = false;

  for (const token of argvList) {
    if (!flagsEnded && token === '--') {
      flagsEnded = true;
    } else if (!flagsEnded && token.startsWith('-') && token !== '-') {
      if (token.startsWith('--format=') && explicitFormat === null && SUPPORTED_FORMATS.includes(token.slice(9))) {
        explicitFormat = token.slice(9);
      } else if (token === '--check' && !isCheckMode) {
        isCheckMode = true;
      } else if (token === '--strict' && !isStrictMode) {
        isStrictMode = true;
      } else {
        return { code: 2, out: ['error: usage'] };
      }
    } else {
      positionalArgs.push(token);
    }
  }

  if (positionalArgs.length > 1) return { code: 2, out: ['error: usage'] };
  const targetPatchFile = positionalArgs.length === 0 || positionalArgs[0] === '-' ? null : positionalArgs[0]!;

  let patchFileRawText = '';
  try {
    patchFileRawText = readFileSync(targetPatchFile ?? 0, 'utf8');
  } catch {
    if (targetPatchFile !== null) return { code: 2, out: ['error: no-patch'] };
  }

  const normalizedPatchLines = splitPatchContentLines(patchFileRawText);
  const selectedFormatKind = explicitFormat === null || explicitFormat === 'auto' ? detectPatchKind(normalizedPatchLines) : explicitFormat;
  if (selectedFormatKind === null) return { code: 2, out: ['error: format'] };

  const trackedFileMoves: Array<{ oldPath: string; newPath: string }> = [];
  let generatedEdits: FileMutationAction[];

  try {
    if (selectedFormatKind === 'json') {
      generatedEdits = buildJsonEdits(patchFileRawText, normalizedPatchLines);
    } else if (selectedFormatKind === 'search-replace') {
      generatedEdits = buildSearchReplaceEdits(patchFileRawText, normalizedPatchLines, isStrictMode);
    } else if (selectedFormatKind === 'unified') {
      generatedEdits = buildUnifiedEdits(patchFileRawText, normalizedPatchLines, isStrictMode, trackedFileMoves);
    } else if (selectedFormatKind === 'v4a') {
      generatedEdits = buildV4AEdits(patchFileRawText, normalizedPatchLines, isStrictMode, trackedFileMoves);
    } else {
      generatedEdits = [];
    }

    if (generatedEdits.length === 0) throw new PatchSyntaxError('error: parse 1');
  } catch (err) {
    if (err instanceof PatchSyntaxError) return { code: 2, out: [err.errorMessage] };
    throw err;
  }

  const workingTree = new WorkingTreeState();
  const collectedFailures: PatchApplyFailure[] = [];

  for (const editAction of generatedEdits) {
    const stageSnapshot = new Map(workingTree.stagedFiles);
    try {
      editAction(workingTree);
    } catch (err) {
      if (!(err instanceof PatchApplyFailure)) throw err;
      workingTree.stagedFiles.clear();
      for (const [keyPath, valContent] of stageSnapshot) {
        workingTree.stagedFiles.set(keyPath, valContent);
      }
      collectedFailures.push(err);
    }
  }

  if (collectedFailures.length > 0) {
    return {
      code: 1,
      out: [
        ...collectedFailures.map((f) => `error: ${f.failureReason} ${f.targetFilePath}`),
        `failed: ${collectedFailures.length} of ${generatedEdits.length} edits`
      ]
    };
  }

  const confirmedRenameMoves = new Map<string, string>();
  for (const moveItem of trackedFileMoves) {
    if (
      workingTree.getOriginalContent(moveItem.oldPath) !== null &&
      workingTree.stagedFiles.get(moveItem.oldPath) === null &&
      workingTree.getOriginalContent(moveItem.newPath) === null &&
      workingTree.stagedFiles.get(moveItem.newPath) !== null
    ) {
      confirmedRenameMoves.set(moveItem.newPath, moveItem.oldPath);
    }
  }

  interface OutputSummaryRow {
    sortKey: string;
    displayText: string;
  }
  const summaryRows: OutputSummaryRow[] = [];

  for (const modifiedPath of workingTree.stagedFiles.keys()) {
    const originalText = workingTree.getOriginalContent(modifiedPath);
    const updatedText = workingTree.stagedFiles.get(modifiedPath)!;
    if (originalText === updatedText) continue;

    if (confirmedRenameMoves.has(modifiedPath)) {
      const sourceOldPath = confirmedRenameMoves.get(modifiedPath)!;
      summaryRows.push({ sortKey: modifiedPath, displayText: `R ${sourceOldPath} -> ${modifiedPath}` });
    } else if (![...confirmedRenameMoves.values()].includes(modifiedPath)) {
      summaryRows.push({
        sortKey: modifiedPath,
        displayText: `${originalText === null ? 'A' : updatedText === null ? 'D' : 'M'} ${modifiedPath}`
      });
    }

    if (isCheckMode) continue;
    if (updatedText === null) {
      rmSync(modifiedPath, { force: true });
    } else {
      mkdirSync(dirname(modifiedPath), { recursive: true });
      writeFileSync(modifiedPath, updatedText);
    }
  }

  summaryRows.sort((a, b) => Buffer.compare(Buffer.from(a.sortKey, 'utf8'), Buffer.from(b.sortKey, 'utf8')));
  const finalSummaryLines = summaryRows.map((r) => r.displayText);

  return {
    code: 0,
    out: [...finalSummaryLines, `ok: ${finalSummaryLines.length} ${finalSummaryLines.length === 1 ? 'file' : 'files'}`]
  };
}

const activeEnvironmentUrl = process.env.MAKEFUN_ENV_URL;
if (activeEnvironmentUrl !== undefined && activeEnvironmentUrl !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(activeEnvironmentUrl);
} else {
  const executionResult = run(process.argv.slice(2));
  writeSync(1, executionResult.out.map((line) => `${line}\n`).join(''));
  process.exitCode = executionResult.code;
}

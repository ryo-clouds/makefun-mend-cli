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

interface UnifiedDiffHunkRecord {
  sourceLineNumber: number;
  hunkBodyLines: Array<{ kind: ' ' | '-' | '+' | '\\'; text: string }>;
  suppressTrailingBreak: boolean;
}

function normalizeUnifiedHeaderPath(pathString: string): string {
  if (pathString === '/dev/null') return '/dev/null';
  if (pathString.startsWith('a/') || pathString.startsWith('b/')) return pathString.slice(2);
  return pathString;
}

function buildUnifiedEdits(
  rawText: string,
  lines: string[],
  isStrictMatching: boolean,
  recordedMoves: Array<{ oldPath: string; newPath: string }>
): FileMutationAction[] {
  const actionsList: FileMutationAction[] = [];
  let lineCursor = 0;

  while (lineCursor < lines.length) {
    let gitOld: string | null = null;
    let gitNew: string | null = null;

    if (lines[lineCursor].startsWith('diff --git ')) {
      const gitMatch = lines[lineCursor].match(/^diff --git a\/(.+) b\/(.+)$/);
      if (!gitMatch) throw new PatchSyntaxError(`error: parse ${lineCursor + 1}`);
      gitOld = gitMatch[1];
      gitNew = gitMatch[2];
      lineCursor++;
    } else if (lines[lineCursor].startsWith('--- ') && (lines[lineCursor + 1] ?? '').startsWith('+++ ')) {
      // standard diff header pair
    } else {
      if (lines[lineCursor].startsWith('@@')) {
        throw new PatchSyntaxError(`error: parse ${lineCursor + 1}`);
      }
      lineCursor++;
      continue;
    }

    let resolvedSourcePath: string | null = gitOld;
    let resolvedDestPath: string | null = gitNew;
    let marksNewFile = false;
    let marksDeletedFile = false;
    let gitRenameSource: string | null = null;
    let gitRenameDest: string | null = null;
    let sawUnifiedHeaderMinus = false;

    const collectedHunks: UnifiedDiffHunkRecord[] = [];

    while (lineCursor < lines.length) {
      const inspectLine = lines[lineCursor];

      if (
        inspectLine.startsWith('diff --git ') ||
        (inspectLine.startsWith('--- ') && (lines[lineCursor + 1] ?? '').startsWith('+++ ') && (collectedHunks.length > 0 || sawUnifiedHeaderMinus))
      ) {
        break;
      }

      if (inspectLine.startsWith('@@')) {
        const headerMatch = inspectLine.match(/^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/);
        if (!headerMatch) throw new PatchSyntaxError(`error: parse ${lineCursor + 1}`);
        const sourceLineNumber = parseInt(headerMatch[1], 10);
        lineCursor++;

        const currentHunkItems: Array<{ kind: ' ' | '-' | '+' | '\\'; text: string }> = [];
        while (lineCursor < lines.length) {
          const bodyItem = lines[lineCursor];
          if (bodyItem.startsWith('diff --git ') || (bodyItem.startsWith('--- ') && (lines[lineCursor + 1] ?? '').startsWith('+++ '))) {
            break;
          }
          if (bodyItem.startsWith('@@')) {
            break;
          }
          if (bodyItem.startsWith(' ') || bodyItem === '') {
            currentHunkItems.push({ kind: ' ', text: bodyItem.startsWith(' ') ? bodyItem.slice(1) : '' });
            lineCursor++;
          } else if (bodyItem.startsWith('-')) {
            currentHunkItems.push({ kind: '-', text: bodyItem.slice(1) });
            lineCursor++;
          } else if (bodyItem.startsWith('+')) {
            currentHunkItems.push({ kind: '+', text: bodyItem.slice(1) });
            lineCursor++;
          } else if (bodyItem.startsWith('\\')) {
            currentHunkItems.push({ kind: '\\', text: bodyItem.slice(1) });
            lineCursor++;
          } else {
            break;
          }
        }

        while (currentHunkItems.length > 0 && currentHunkItems[currentHunkItems.length - 1].kind === ' ' && currentHunkItems[currentHunkItems.length - 1].text === '') {
          currentHunkItems.pop();
        }

        let suppressTrailingBreak = false;
        let lastContextOrAddition = -1;
        for (let idx = currentHunkItems.length - 1; idx >= 0; idx--) {
          if (currentHunkItems[idx].kind === ' ' || currentHunkItems[idx].kind === '+') {
            lastContextOrAddition = idx;
            break;
          }
        }
        if (lastContextOrAddition >= 0 && lastContextOrAddition + 1 < currentHunkItems.length && currentHunkItems[lastContextOrAddition + 1].kind === '\\') {
          suppressTrailingBreak = true;
        }

        collectedHunks.push({ sourceLineNumber, hunkBodyLines: currentHunkItems, suppressTrailingBreak });
        continue;
      }

      if (inspectLine.startsWith('--- ')) {
        const pairedLine = lines[lineCursor + 1] ?? '';
        if (!pairedLine.startsWith('+++ ')) {
          throw new PatchSyntaxError(`error: parse ${lineCursor + 2}`);
        }
        const parsedOld = inspectLine.slice(4).split('\t')[0].trim();
        const parsedNew = pairedLine.slice(4).split('\t')[0].trim();
        resolvedSourcePath = normalizeUnifiedHeaderPath(parsedOld);
        resolvedDestPath = normalizeUnifiedHeaderPath(parsedNew);
        sawUnifiedHeaderMinus = true;
        lineCursor += 2;
        continue;
      }

      if (inspectLine.startsWith('rename from ')) {
        gitRenameSource = normalizeUnifiedHeaderPath(inspectLine.slice(12).trim());
        lineCursor++;
        continue;
      }
      if (inspectLine.startsWith('rename to ')) {
        gitRenameDest = normalizeUnifiedHeaderPath(inspectLine.slice(10).trim());
        lineCursor++;
        continue;
      }
      if (inspectLine.startsWith('new file mode')) {
        marksNewFile = true;
        lineCursor++;
        continue;
      }
      if (inspectLine.startsWith('deleted file mode')) {
        marksDeletedFile = true;
        lineCursor++;
        continue;
      }

      lineCursor++;
    }

    if (!sawUnifiedHeaderMinus && gitRenameSource !== null && gitRenameDest !== null) {
      resolvedSourcePath = gitRenameSource;
      resolvedDestPath = gitRenameDest;
    }

    if (resolvedSourcePath === null && resolvedDestPath === null) continue;

    const effectiveOldPath = resolvedSourcePath ?? resolvedDestPath!;
    const effectiveNewPath = resolvedDestPath ?? resolvedSourcePath!;
    const isCreation = effectiveOldPath === '/dev/null' || marksNewFile;
    const isDeletion = effectiveNewPath === '/dev/null' || marksDeletedFile;
    const isRenameMove = !isCreation && !isDeletion && effectiveOldPath !== effectiveNewPath;

    if (isRenameMove) {
      recordedMoves.push({ oldPath: effectiveOldPath, newPath: effectiveNewPath });
    }

    actionsList.push((tree) => {
      if (isCreation) {
        if (!validatePathSafety(effectiveNewPath)) throw new PatchApplyFailure('unsafe', effectiveNewPath);
        if (tree.pathExistsOnDiskOrStage(effectiveNewPath)) throw new PatchApplyFailure('exists', effectiveNewPath);
        const addedLinesList: string[] = [];
        for (const hunk of collectedHunks) {
          for (const hl of hunk.hunkBodyLines) {
            if (hl.kind === '+') addedLinesList.push(hl.text);
          }
        }
        let omitFinalBreak = false;
        for (let hunkIdx = collectedHunks.length - 1; hunkIdx >= 0; hunkIdx--) {
          const hunk = collectedHunks[hunkIdx];
          if (hunk.hunkBodyLines.some((hl) => hl.kind === '+')) {
            omitFinalBreak = hunk.suppressTrailingBreak;
            break;
          }
        }
        tree.stagedFiles.set(effectiveNewPath, addedLinesList.length === 0 ? '' : addedLinesList.join('\n') + (omitFinalBreak ? '' : '\n'));
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

      for (const hunk of collectedHunks) {
        const expectedPattern: string[] = [];
        const replacementHunks: UnifiedHunkElement[] = [];
        for (const hl of hunk.hunkBodyLines) {
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
          const idealPosition = hunk.sourceLineNumber - 1 + cumulativeLineOffset;
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
            parsedDoc.hasTerminalNewline = !hunk.suppressTrailingBreak;
          }
        } else {
          const insertPosition = Math.min(Math.max(0, hunk.sourceLineNumber + cumulativeLineOffset), parsedDoc.lines.length);
          const extendsToEof = insertPosition === parsedDoc.lines.length;
          const substituted = substituteTargetLines(parsedDoc.lines, insertPosition, [''], replacementHunks, 0);
          parsedDoc.lines.splice(insertPosition, 0, ...substituted);
          if (extendsToEof) {
            parsedDoc.hasTerminalNewline = !hunk.suppressTrailingBreak;
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

  return actionsList;
}

interface V4APatchHunk {
  contextAnchor: string | null;
  hunkDiffLines: Array<{ indicator: ' ' | '-' | '+'; lineText: string }>;
  eofTerminated: boolean;
}

function verifyV4ABoundaries(patchLines: string[]): { bodyStart: number; bodyEnd: number } {
  let startIndex = -1;
  for (let idx = 0; idx < patchLines.length; idx++) {
    if (!isWhitespaceLine(patchLines[idx])) {
      startIndex = idx;
      break;
    }
  }
  if (startIndex === -1) {
    throw new PatchSyntaxError('error: parse 1');
  }
  if (patchLines[startIndex].trim() !== '*** Begin Patch') {
    throw new PatchSyntaxError(`error: parse ${startIndex + 1}`);
  }

  let stopIndex = -1;
  for (let idx = patchLines.length - 1; idx >= 0; idx--) {
    if (!isWhitespaceLine(patchLines[idx])) {
      stopIndex = idx;
      break;
    }
  }
  if (stopIndex === -1 || patchLines[stopIndex].trim() !== '*** End Patch') {
    throw new PatchSyntaxError(`error: parse ${patchLines.length + 1}`);
  }

  return { bodyStart: startIndex + 1, bodyEnd: stopIndex };
}

function isV4ACommandBoundary(lineString: string): boolean {
  return (
    lineString.startsWith('*** Add File: ') ||
    lineString.startsWith('*** Delete File: ') ||
    lineString.startsWith('*** Update File: ') ||
    lineString.trim() === '*** End Patch'
  );
}

function checkV4ATrailingPaddingOnly(allLines: string[], currentPos: number, limitPos: number): boolean {
  for (let scan = currentPos; scan < limitPos; scan++) {
    if (isV4ACommandBoundary(allLines[scan])) {
      return true;
    }
    if (!isWhitespaceLine(allLines[scan])) {
      return false;
    }
  }
  return true;
}

function advancePastV4APadding(allLines: string[], currentPos: number, limitPos: number): number {
  let scan = currentPos;
  while (scan < limitPos && !isV4ACommandBoundary(allLines[scan])) {
    scan++;
  }
  return scan;
}

function locateV4AAnchorLine(
  documentLines: string[],
  anchorTarget: string,
  searchOffset: number,
  strictMatching: boolean
): number {
  for (let idx = searchOffset; idx < documentLines.length; idx++) {
    if (documentLines[idx] === anchorTarget) return idx;
  }
  if (strictMatching) return -1;

  const trimmedTarget = stripTrailingWhitespace(anchorTarget);
  for (let idx = searchOffset; idx < documentLines.length; idx++) {
    if (stripTrailingWhitespace(documentLines[idx]) === trimmedTarget) return idx;
  }

  const normalizedTarget = stripSurroundingWhitespace(anchorTarget);
  for (let idx = searchOffset; idx < documentLines.length; idx++) {
    if (stripSurroundingWhitespace(documentLines[idx]) === normalizedTarget) return idx;
  }

  return -1;
}

function executeV4AHunkTransformation(
  parsedDocument: ParsedTextDocument,
  hunk: V4APatchHunk,
  currentScanOffset: number,
  strictMatching: boolean,
  targetFileLabel: string
): number {
  let searchCursor = currentScanOffset;

  if (hunk.contextAnchor !== null) {
    const matchedAnchorIdx = locateV4AAnchorLine(parsedDocument.lines, hunk.contextAnchor, searchCursor, strictMatching);
    if (matchedAnchorIdx === -1) {
      throw new PatchApplyFailure('no-match', targetFileLabel);
    }
    searchCursor = matchedAnchorIdx + 1;
  }

  const expectedPatterns: string[] = [];
  const replacementElements: UnifiedHunkElement[] = [];

  for (const diffItem of hunk.hunkDiffLines) {
    if (diffItem.indicator === ' ') {
      const cIndex = expectedPatterns.length;
      expectedPatterns.push(diffItem.lineText);
      replacementElements.push({ text: diffItem.lineText, isContext: true, contextIndex: cIndex });
    } else if (diffItem.indicator === '-') {
      expectedPatterns.push(diffItem.lineText);
    } else if (diffItem.indicator === '+') {
      replacementElements.push({ text: diffItem.lineText, isContext: false });
    }
  }

  if (expectedPatterns.length > 0) {
    const patternOutcome = locatePatternOccurrences(
      parsedDocument.lines,
      expectedPatterns,
      strictMatching,
      searchCursor,
      hunk.eofTerminated
    );
    if (patternOutcome.matchingTier === -1 || patternOutcome.matchPositions.length === 0) {
      throw new PatchApplyFailure('no-match', targetFileLabel);
    }
    const targetMatchIndex = patternOutcome.matchPositions[0];
    const generatedLines = substituteTargetLines(
      parsedDocument.lines,
      targetMatchIndex,
      expectedPatterns,
      replacementElements,
      patternOutcome.matchingTier
    );
    parsedDocument.lines.splice(targetMatchIndex, expectedPatterns.length, ...generatedLines);
    return targetMatchIndex + generatedLines.length;
  } else {
    const insertionPoint = hunk.eofTerminated ? parsedDocument.lines.length : searchCursor;
    const generatedLines = substituteTargetLines(parsedDocument.lines, insertionPoint, [''], replacementElements, 0);
    parsedDocument.lines.splice(insertionPoint, 0, ...generatedLines);
    return insertionPoint + generatedLines.length;
  }
}

function buildV4AEdits(
  rawText: string,
  lines: string[],
  isStrictMatching: boolean,
  recordedMoves: Array<{ oldPath: string; newPath: string }>
): FileMutationAction[] {
  const { bodyStart, bodyEnd } = verifyV4ABoundaries(lines);
  const plannedEdits: FileMutationAction[] = [];
  let linePointer = bodyStart;

  while (linePointer < bodyEnd) {
    if (isWhitespaceLine(lines[linePointer])) {
      linePointer++;
      continue;
    }

    const currentHeader = lines[linePointer];

    if (currentHeader.startsWith('*** Add File: ')) {
      const addedFilePath = currentHeader.slice(14).trim();
      linePointer++;
      const payloadLines: string[] = [];

      while (linePointer < bodyEnd) {
        const itemLine = lines[linePointer];
        if (isV4ACommandBoundary(itemLine)) {
          break;
        }

        if (itemLine.startsWith('+')) {
          payloadLines.push(itemLine.slice(1));
          linePointer++;
        } else if (itemLine === '') {
          payloadLines.push('');
          linePointer++;
        } else {
          if (checkV4ATrailingPaddingOnly(lines, linePointer, bodyEnd)) {
            linePointer = advancePastV4APadding(lines, linePointer, bodyEnd);
            break;
          }
          throw new PatchSyntaxError(`error: parse ${linePointer + 1}`);
        }
      }

      plannedEdits.push((tree) => {
        if (!validatePathSafety(addedFilePath)) throw new PatchApplyFailure('unsafe', addedFilePath);
        if (tree.pathExistsOnDiskOrStage(addedFilePath)) throw new PatchApplyFailure('exists', addedFilePath);
        const finalContent = payloadLines.length === 0 ? '' : payloadLines.join('\n') + '\n';
        tree.stagedFiles.set(addedFilePath, finalContent);
      });
      continue;
    }

    if (currentHeader.startsWith('*** Delete File: ')) {
      const targetFilePath = currentHeader.slice(17).trim();
      linePointer++;

      while (linePointer < bodyEnd && isWhitespaceLine(lines[linePointer])) {
        linePointer++;
      }
      if (linePointer < bodyEnd && !lines[linePointer].startsWith('*** ')) {
        throw new PatchSyntaxError(`error: parse ${linePointer + 1}`);
      }

      plannedEdits.push((tree) => {
        if (!validatePathSafety(targetFilePath)) throw new PatchApplyFailure('unsafe', targetFilePath);
        if (tree.getCurrentContent(targetFilePath) === null) throw new PatchApplyFailure('missing', targetFilePath);
        tree.stagedFiles.set(targetFilePath, null);
      });
      continue;
    }

    if (currentHeader.startsWith('*** Update File: ')) {
      const initialFilePath = currentHeader.slice(17).trim();
      const originHeaderNumber = linePointer + 1;
      linePointer++;

      let relocatedDestination: string | null = null;
      if (linePointer < bodyEnd && lines[linePointer].startsWith('*** Move to: ')) {
        relocatedDestination = lines[linePointer].slice(13).trim();
        linePointer++;
      }

      const fileHunksList: V4APatchHunk[] = [];
      let pendingHunk: V4APatchHunk | null = null;

      while (linePointer < bodyEnd) {
        const subLine = lines[linePointer];
        if (subLine.trim() === '*** End of File') {
          if (pendingHunk === null) {
            pendingHunk = { contextAnchor: null, hunkDiffLines: [], eofTerminated: true };
            fileHunksList.push(pendingHunk);
          } else {
            pendingHunk.eofTerminated = true;
          }
          linePointer++;
          pendingHunk = null;
          continue;
        }

        if (isV4ACommandBoundary(subLine)) {
          break;
        }

        if (subLine.startsWith('@@')) {
          const rawAnchor = subLine.slice(2).trim();
          pendingHunk = {
            contextAnchor: rawAnchor === '' ? null : rawAnchor,
            hunkDiffLines: [],
            eofTerminated: false
          };
          fileHunksList.push(pendingHunk);
          linePointer++;
          continue;
        }

        if (isWhitespaceLine(subLine)) {
          if (checkV4ATrailingPaddingOnly(lines, linePointer, bodyEnd)) {
            linePointer = advancePastV4APadding(lines, linePointer, bodyEnd);
            break;
          }
        }

        if (subLine.startsWith(' ') || subLine.startsWith('-') || subLine.startsWith('+') || subLine === '') {
          if (pendingHunk === null) {
            pendingHunk = { contextAnchor: null, hunkDiffLines: [], eofTerminated: false };
            fileHunksList.push(pendingHunk);
          }

          if (subLine.startsWith(' ')) {
            pendingHunk.hunkDiffLines.push({ indicator: ' ', lineText: subLine.slice(1) });
          } else if (subLine === '') {
            pendingHunk.hunkDiffLines.push({ indicator: ' ', lineText: '' });
          } else if (subLine.startsWith('-')) {
            pendingHunk.hunkDiffLines.push({ indicator: '-', lineText: subLine.slice(1) });
          } else {
            pendingHunk.hunkDiffLines.push({ indicator: '+', lineText: subLine.slice(1) });
          }
          linePointer++;
          continue;
        }

        throw new PatchSyntaxError(`error: parse ${linePointer + 1}`);
      }

      if (fileHunksList.length === 0 && relocatedDestination === null) {
        throw new PatchSyntaxError(`error: parse ${originHeaderNumber}`);
      }

      if (relocatedDestination !== null) {
        recordedMoves.push({ oldPath: initialFilePath, newPath: relocatedDestination });
      }

      plannedEdits.push((tree) => {
        if (!validatePathSafety(initialFilePath)) throw new PatchApplyFailure('unsafe', initialFilePath);
        if (relocatedDestination !== null && !validatePathSafety(relocatedDestination)) {
          throw new PatchApplyFailure('unsafe', relocatedDestination);
        }
        if (tree.getCurrentContent(initialFilePath) === null) {
          throw new PatchApplyFailure('missing', initialFilePath);
        }
        if (relocatedDestination !== null && tree.pathExistsOnDiskOrStage(relocatedDestination)) {
          throw new PatchApplyFailure('exists', relocatedDestination);
        }

        const sourceDocumentText = tree.getCurrentContent(initialFilePath)!;
        const parsedDocument = dissectDocumentText(sourceDocumentText);
        let mutationOffset = 0;

        for (const singleHunk of fileHunksList) {
          mutationOffset = executeV4AHunkTransformation(
            parsedDocument,
            singleHunk,
            mutationOffset,
            isStrictMatching,
            initialFilePath
          );
        }

        const serializedOutput = assembleDocumentText(
          parsedDocument.lines,
          parsedDocument.isWindowsCrlf,
          parsedDocument.hasTerminalNewline
        );

        if (relocatedDestination !== null) {
          tree.stagedFiles.set(initialFilePath, null);
          tree.stagedFiles.set(relocatedDestination, serializedOutput);
        } else {
          tree.stagedFiles.set(initialFilePath, serializedOutput);
        }
      });
      continue;
    }

    throw new PatchSyntaxError(`error: parse ${linePointer + 1}`);
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

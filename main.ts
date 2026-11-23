// Test prototype for mend
import { mkdirSync, readFileSync, rmSync, statSync, writeFileSync, writeSync } from 'node:fs';
import { dirname } from 'node:path';

const FORMATS = ['auto', 'unified', 'search-replace', 'v4a', 'json'];

class Exit2 {
  readonly line: string;
  constructor(line: string) {
    this.line = line;
  }
}
class Fail {
  readonly code: string;
  readonly path: string;
  constructor(code: string, path: string) {
    this.code = code;
    this.path = path;
  }
}

const blank = (s: string): boolean => s.trim() === '';

function patchLines(text: string): string[] {
  if (text === '') return [];
  const lines = text.split('\n');
  if (text.endsWith('\n')) lines.pop();
  return lines.map((l) => (l.endsWith('\r') ? l.slice(0, -1) : l));
}

function safe(p: string): boolean {
  return p !== '' && !p.startsWith('/') && !p.includes('\\') && p.split('/').every((s) => s !== '' && s !== '.' && s !== '..');
}

class Tree {
  private readonly orig = new Map<string, string | null>();
  readonly now = new Map<string, string | null>();
  original(p: string): string | null {
    if (!this.orig.has(p)) {
      let v: string | null = null;
      try {
        if (statSync(p).isFile()) v = readFileSync(p, 'utf8');
      } catch {
        v = null;
      }
      this.orig.set(p, v);
    }
    return this.orig.get(p)!;
  }
  get(p: string): string | null {
    return this.now.has(p) ? this.now.get(p)! : this.original(p);
  }
}

type Edit = (tree: Tree) => void;

function detect(lines: string[]): string | null {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) return null;
  if (lines[first]!.trim() === '*** Begin Patch') return 'v4a';
  const c = lines[first]!.trimStart()[0];
  if (c === '[' || c === '{') return 'json';
  if (lines.some((l) => l.trimEnd() === '<<<<<<< SEARCH')) return 'search-replace';
  if (lines.some((l, i) => l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')))) return 'unified';
  return null;
}

function stripTrailing(s: string): string {
  return s.replace(/[ \t]+$/, '');
}

function stripBoth(s: string): string {
  return s.replace(/^[ \t]+|[ \t]+$/g, '');
}

interface MatchResult {
  tier: number;
  occurrences: number[];
}

function findOccurrences(fileLines: string[], O: string[], strict: boolean, minIndex = 0): MatchResult {
  if (O.length === 0 || fileLines.length < O.length + minIndex) {
    return { tier: -1, occurrences: [] };
  }

  // Tier 0
  const occ0: number[] = [];
  for (let i = minIndex; i <= fileLines.length - O.length; i++) {
    let match = true;
    for (let j = 0; j < O.length; j++) {
      if (fileLines[i + j] !== O[j]) {
        match = false;
        break;
      }
    }
    if (match) occ0.push(i);
  }
  if (occ0.length > 0) return { tier: 0, occurrences: occ0 };
  if (strict) return { tier: -1, occurrences: [] };

  // Tier 1
  const occ1: number[] = [];
  for (let i = minIndex; i <= fileLines.length - O.length; i++) {
    let match = true;
    for (let j = 0; j < O.length; j++) {
      if (stripTrailing(fileLines[i + j]) !== stripTrailing(O[j])) {
        match = false;
        break;
      }
    }
    if (match) occ1.push(i);
  }
  if (occ1.length > 0) return { tier: 1, occurrences: occ1 };

  // Tier 2
  const occ2: number[] = [];
  for (let i = minIndex; i <= fileLines.length - O.length; i++) {
    let match = true;
    for (let j = 0; j < O.length; j++) {
      if (stripBoth(fileLines[i + j]) !== stripBoth(O[j])) {
        match = false;
        break;
      }
    }
    if (match) occ2.push(i);
  }
  if (occ2.length > 0) return { tier: 2, occurrences: occ2 };

  return { tier: -1, occurrences: [] };
}

interface HunkLine {
  text: string;
  isContext: boolean;
  contextIndex?: number;
}

function replaceLines(
  fileLines: string[],
  pos: number,
  O: string[],
  N: HunkLine[],
  tier: number
): string[] {
  const F = fileLines[pos].match(/^[ \t]*/)?.[0] ?? '';
  const P = O[0].match(/^[ \t]*/)?.[0] ?? '';

  const out: string[] = [];
  for (const item of N) {
    if (item.isContext && item.contextIndex !== undefined) {
      out.push(fileLines[pos + item.contextIndex]);
    } else if (tier === 2) {
      if (item.text.trim() !== '' && item.text.startsWith(P)) {
        out.push(F + item.text.slice(P.length));
      } else {
        out.push(item.text);
      }
    } else {
      out.push(item.text);
    }
  }
  return out;
}

function parseFile(text: string): { lines: string[]; crlf: boolean; hasFinalBreak: boolean } {
  if (text === '') {
    return { lines: [], crlf: false, hasFinalBreak: false };
  }
  const nl = text.indexOf('\n');
  const crlf = nl > 0 && text[nl - 1] === '\r';
  const br = crlf ? '\r\n' : '\n';
  const lines = text.split(br);
  const hasFinalBreak = text.endsWith(br);
  if (hasFinalBreak) lines.pop();
  return { lines, crlf, hasFinalBreak };
}

function serializeFile(lines: string[], crlf: boolean, hasFinalBreak: boolean): string {
  if (lines.length === 0) return '';
  const br = crlf ? '\r\n' : '\n';
  return lines.join(br) + (hasFinalBreak ? br : '');
}

/** One JSON edit object (SPEC.md section 9), or null when it is not one. */
function jsonEdit(v: unknown): Edit | null {
  if (v === null || typeof v !== 'object' || Array.isArray(v)) return null;
  const o = v as Record<string, unknown>;
  const p = o.path;
  if (typeof p !== 'string') return null;
  const exists = (tree: Tree): string => {
    if (!safe(p)) throw new Fail('unsafe', p);
    const t = tree.get(p);
    if (t === null) throw new Fail('missing', p);
    return t;
  };
  if (o.command === 'create' && typeof o.file_text === 'string') {
    const text = o.file_text;
    return (tree) => {
      if (!safe(p)) throw new Fail('unsafe', p);
      if (tree.get(p) !== null) throw new Fail('exists', p);
      tree.now.set(p, text);
    };
  }
  if (o.command === 'str_replace' && typeof o.old_str === 'string' && o.old_str !== '' && (o.new_str === undefined || typeof o.new_str === 'string')) {
    const oldStr = o.old_str;
    const newStr = (o.new_str as string | undefined) ?? '';
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const crlf = nl > 0 && before[nl - 1] === '\r';
      const lf = (s: string): string => (crlf ? s.replaceAll('\r\n', '\n') : s);
      const t = lf(before);
      const old = lf(oldStr);
      let count = 0;
      for (let k = t.indexOf(old); k >= 0; k = t.indexOf(old, k + 1)) count += 1;
      if (count === 0) throw new Fail('no-match', p);
      if (count > 1) throw new Fail('ambiguous', p);
      const at = t.indexOf(old);
      const out = t.slice(0, at) + lf(newStr) + t.slice(at + old.length);
      tree.now.set(p, crlf ? out.replaceAll('\n', '\r\n') : out);
    };
  }
  if (o.command === 'insert' && typeof o.insert_line === 'number' && Number.isInteger(o.insert_line) && typeof o.new_str === 'string') {
    const line = o.insert_line;
    const add = patchLines(o.new_str);
    return (tree) => {
      const before = exists(tree);
      const nl = before.indexOf('\n');
      const br = nl > 0 && before[nl - 1] === '\r' ? '\r\n' : '\n';
      const lines = before === '' ? [] : before.split(br);
      const final = before !== '' && before.endsWith(br);
      if (final) lines.pop();
      if (line < 0 || line > lines.length) throw new Fail('no-match', p);
      lines.splice(line, 0, ...add);
      tree.now.set(p, lines.length === 0 ? '' : lines.join(br) + (final ? br : ''));
    };
  }
  return null;
}

function jsonEdits(text: string, lines: string[]): Edit[] {
  const first = lines.findIndex((l) => !blank(l));
  if (first < 0) throw new Exit2('error: parse 1');
  const edits: Edit[] = [];
  if (lines[first]!.trimStart().startsWith('[')) {
    let v: unknown;
    try {
      v = JSON.parse(text);
    } catch {
      throw new Exit2(`error: parse ${first + 1}`);
    }
    if (!Array.isArray(v)) throw new Exit2(`error: parse ${first + 1}`);
    for (const x of v) {
      const e = jsonEdit(x);
      if (e === null) throw new Exit2(`error: parse ${first + 1}`);
      edits.push(e);
    }
    return edits;
  }
  lines.forEach((l, i) => {
    if (blank(l)) return;
    let e: Edit | null = null;
    try {
      e = jsonEdit(JSON.parse(l));
    } catch {
      e = null;
    }
    if (e === null) throw new Exit2(`error: parse ${i + 1}`);
    edits.push(e);
  });
  return edits;
}

function searchReplaceEdits(text: string, lines: string[], strict: boolean): Edit[] {
  const edits: Edit[] = [];
  let prevPath: string | null = null;
  let prevReplaceIdx = -1;

  let i = 0;
  while (i < lines.length) {
    if (lines[i].trimEnd() === '<<<<<<< SEARCH') {
      const searchLineIdx = i;
      const searchLineNum = i + 1;

      let blockPath: string | null = null;
      for (let k = searchLineIdx - 1; k > prevReplaceIdx; k--) {
        const l = lines[k];
        if (!blank(l) && !l.trim().startsWith('```')) {
          blockPath = l.trim();
          break;
        }
      }
      if (blockPath === null) blockPath = prevPath;
      if (blockPath === null) {
        throw new Exit2(`error: parse ${searchLineNum}`);
      }
      prevPath = blockPath;

      let equalIdx = -1;
      let replaceIdx = -1;
      for (let k = searchLineIdx + 1; k < lines.length; k++) {
        if (lines[k].trimEnd() === '<<<<<<< SEARCH') {
          break;
        }
        if (lines[k].trimEnd() === '=======' && equalIdx === -1) {
          equalIdx = k;
        } else if (lines[k].trimEnd() === '>>>>>>> REPLACE' && equalIdx !== -1) {
          replaceIdx = k;
          break;
        }
      }

      if (equalIdx === -1 || replaceIdx === -1) {
        throw new Exit2(`error: parse ${searchLineNum}`);
      }

      const oldLines = lines.slice(searchLineIdx + 1, equalIdx);
      const newLines = lines.slice(equalIdx + 1, replaceIdx);
      prevReplaceIdx = replaceIdx;
      i = replaceIdx + 1;

      const p = blockPath;
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        const content = tree.get(p);
        if (oldLines.length === 0) {
          if (content !== null) throw new Fail('exists', p);
          tree.now.set(p, newLines.length === 0 ? '' : newLines.join('\n') + '\n');
          return;
        }
        if (content === null) throw new Fail('missing', p);
        const parsed = parseFile(content);
        const res = findOccurrences(parsed.lines, oldLines, strict);
        if (res.tier === -1 || res.occurrences.length === 0) {
          throw new Fail('no-match', p);
        }
        if (res.occurrences.length > 1) {
          throw new Fail('ambiguous', p);
        }
        const pos = res.occurrences[0];
        const replacementLines = replaceLines(
          parsed.lines,
          pos,
          oldLines,
          newLines.map((t) => ({ text: t, isContext: false })),
          res.tier
        );
        parsed.lines.splice(pos, oldLines.length, ...replacementLines);
        tree.now.set(p, serializeFile(parsed.lines, parsed.crlf, parsed.hasFinalBreak));
      });
    } else {
      i++;
    }
  }

  return edits;
}

function cleanUnifiedPath(p: string): string {
  if (p === '/dev/null') return '/dev/null';
  if (p.startsWith('a/') || p.startsWith('b/')) return p.slice(2);
  return p;
}

interface UnifiedHunk {
  A: number;
  lines: Array<{ kind: ' ' | '-' | '+' | '\\'; text: string }>;
  hasBackslashAtEnd: boolean;
}

function unifiedEdits(text: string, lines: string[], strict: boolean, moves: Array<{ oldPath: string; newPath: string }>): Edit[] {
  // Parse sections
  const edits: Edit[] = [];
  let i = 0;

  while (i < lines.length) {
    // Check if section starts here
    let isDiffGit = false;
    let gitOld: string | null = null;
    let gitNew: string | null = null;

    if (lines[i].startsWith('diff --git ')) {
      const m = lines[i].match(/^diff --git a\/(.+) b\/(.+)$/);
      if (!m) throw new Exit2(`error: parse ${i + 1}`);
      isDiffGit = true;
      gitOld = m[1];
      gitNew = m[2];
      i++;
    } else if (lines[i].startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ')) {
      // starts a section
    } else {
      if (lines[i].startsWith('@@')) {
        throw new Exit2(`error: parse ${i + 1}`);
      }
      i++;
      continue;
    }

    // Inside section header
    let oldPath: string | null = gitOld;
    let newPath: string | null = gitNew;
    let isNewFile = false;
    let isDeletedFile = false;
    let renameFrom: string | null = null;
    let renameTo: string | null = null;
    let sawMinus = false;

    const hunks: UnifiedHunk[] = [];

    while (i < lines.length) {
      const l = lines[i];

      // Next section starts?
      if (l.startsWith('diff --git ') || (l.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ ') && hunks.length > 0)) {
        break;
      }

      if (l.startsWith('@@')) {
        const m = l.match(/^@@ -(\d+)(?:,\d+)? \+(\d+)(?:,\d+)? @@/);
        if (!m) throw new Exit2(`error: parse ${i + 1}`);
        const A = parseInt(m[1], 10);
        i++;

        // Hunk body
        const hunkBody: Array<{ kind: ' ' | '-' | '+' | '\\'; text: string }> = [];
        while (i < lines.length) {
          const hl = lines[i];
          if (hl.startsWith('diff --git ') || (hl.startsWith('--- ') && (lines[i + 1] ?? '').startsWith('+++ '))) {
            break;
          }
          if (hl.startsWith('@@')) {
            break;
          }
          if (hl.startsWith(' ') || hl === '') {
            hunkBody.push({ kind: ' ', text: hl.startsWith(' ') ? hl.slice(1) : '' });
            i++;
          } else if (hl.startsWith('-')) {
            hunkBody.push({ kind: '-', text: hl.slice(1) });
            i++;
          } else if (hl.startsWith('+')) {
            hunkBody.push({ kind: '+', text: hl.slice(1) });
            i++;
          } else if (hl.startsWith('\\')) {
            hunkBody.push({ kind: '\\', text: hl.slice(1) });
            i++;
          } else {
            // body ends at first other line
            break;
          }
        }

        // Empty lines at end of body are not part of it
        while (hunkBody.length > 0 && hunkBody[hunkBody.length - 1].kind === ' ' && hunkBody[hunkBody.length - 1].text === '') {
          hunkBody.pop();
        }

        // Check if \ line follows last context or + line
        let hasBackslashAtEnd = false;
        let lastContextOrAdd = -1;
        for (let idx = hunkBody.length - 1; idx >= 0; idx--) {
          if (hunkBody[idx].kind === ' ' || hunkBody[idx].kind === '+') {
            lastContextOrAdd = idx;
            break;
          }
        }
        if (lastContextOrAdd >= 0 && lastContextOrAdd + 1 < hunkBody.length && hunkBody[lastContextOrAdd + 1].kind === '\\') {
          hasBackslashAtEnd = true;
        }

        hunks.push({ A, lines: hunkBody, hasBackslashAtEnd });
        continue;
      }

      // Check header lines
      if (l.startsWith('--- ')) {
        const next = lines[i + 1] ?? '';
        if (!next.startsWith('+++ ')) {
          throw new Exit2(`error: parse ${i + 2}`);
        }
        const rawOld = l.slice(4).split('\t')[0].trim();
        const rawNew = next.slice(4).split('\t')[0].trim();
        oldPath = cleanUnifiedPath(rawOld);
        newPath = cleanUnifiedPath(rawNew);
        sawMinus = true;
        i += 2;
        continue;
      }

      if (l.startsWith('rename from ')) {
        renameFrom = cleanUnifiedPath(l.slice(12).trim());
        i++;
        continue;
      }
      if (l.startsWith('rename to ')) {
        renameTo = cleanUnifiedPath(l.slice(10).trim());
        i++;
        continue;
      }
      if (l.startsWith('new file mode')) {
        isNewFile = true;
        i++;
        continue;
      }
      if (l.startsWith('deleted file mode')) {
        isDeletedFile = true;
        i++;
        continue;
      }

      i++;
    }

    if (!sawMinus && renameFrom !== null && renameTo !== null) {
      oldPath = renameFrom;
      newPath = renameTo;
    }

    if (oldPath === null && newPath === null) continue;

    const op = oldPath ?? newPath!;
    const np = newPath ?? oldPath!;
    const isCreation = op === '/dev/null' || isNewFile;
    const isDeletion = np === '/dev/null' || isDeletedFile;
    const isMove = !isCreation && !isDeletion && op !== np;

    if (isMove) {
      moves.push({ oldPath: op, newPath: np });
    }

    edits.push((tree) => {
      if (isCreation) {
        if (!safe(np)) throw new Fail('unsafe', np);
        if (tree.get(np) !== null) throw new Fail('exists', np);
        const addLines: string[] = [];
        let hasNoNewline = false;
        for (const h of hunks) {
          for (const hl of h.lines) {
            if (hl.kind === '+') addLines.push(hl.text);
          }
          if (h.hasBackslashAtEnd) hasNoNewline = true;
        }
        tree.now.set(np, addLines.length === 0 ? '' : addLines.join('\n') + (hasNoNewline ? '' : '\n'));
        return;
      }

      if (isDeletion) {
        if (!safe(op)) throw new Fail('unsafe', op);
        if (tree.get(op) === null) throw new Fail('missing', op);
        tree.now.set(op, null);
        return;
      }

      if (isMove) {
        if (!safe(op)) throw new Fail('unsafe', op);
        if (!safe(np)) throw new Fail('unsafe', np);
        if (tree.get(op) === null) throw new Fail('missing', op);
        if (tree.get(np) !== null) throw new Fail('exists', np);
      } else {
        if (!safe(op)) throw new Fail('unsafe', op);
        if (tree.get(op) === null) throw new Fail('missing', op);
      }

      const content = tree.get(op)!;
      const parsed = parseFile(content);
      let d = 0;

      for (const hunk of hunks) {
        const O: string[] = [];
        const N: HunkLine[] = [];
        for (const hl of hunk.lines) {
          if (hl.kind === ' ') {
            const cIdx = O.length;
            O.push(hl.text);
            N.push({ text: hl.text, isContext: true, contextIndex: cIdx });
          } else if (hl.kind === '-') {
            O.push(hl.text);
          } else if (hl.kind === '+') {
            N.push({ text: hl.text, isContext: false });
          }
        }

        if (O.length > 0) {
          const res = findOccurrences(parsed.lines, O, strict);
          if (res.tier === -1 || res.occurrences.length === 0) {
            throw new Fail('no-match', op);
          }
          const target = hunk.A - 1 + d;
          let bestPos = res.occurrences[0];
          let bestDist = Math.abs(bestPos - target);
          for (let k = 1; k < res.occurrences.length; k++) {
            const dist = Math.abs(res.occurrences[k] - target);
            if (dist < bestDist) {
              bestDist = dist;
              bestPos = res.occurrences[k];
            }
          }
          const runsToEnd = bestPos + O.length === parsed.lines.length;
          const repl = replaceLines(parsed.lines, bestPos, O, N, res.tier);
          parsed.lines.splice(bestPos, O.length, ...repl);
          if (runsToEnd) {
            parsed.hasFinalBreak = !hunk.hasBackslashAtEnd;
          }
        } else {
          const insertPos = Math.min(Math.max(0, hunk.A + d), parsed.lines.length);
          const runsToEnd = insertPos === parsed.lines.length;
          const repl = replaceLines(parsed.lines, insertPos, [''], N, 0);
          parsed.lines.splice(insertPos, 0, ...repl);
          if (runsToEnd) {
            parsed.hasFinalBreak = !hunk.hasBackslashAtEnd;
          }
        }
        d += N.length - O.length;
      }

      const outText = serializeFile(parsed.lines, parsed.crlf, parsed.hasFinalBreak);
      if (isMove) {
        tree.now.set(op, null);
        tree.now.set(np, outText);
      } else {
        tree.now.set(op, outText);
      }
    });
  }

  return edits;
}

interface V4AChunk {
  anchor: string | null;
  lines: Array<{ kind: ' ' | '-' | '+'; text: string }>;
  isEndOfFile: boolean;
}

function v4aEdits(text: string, lines: string[], strict: boolean, moves: Array<{ oldPath: string; newPath: string }>): Edit[] {
  const firstNonBlank = lines.findIndex((l) => !blank(l));
  if (firstNonBlank < 0) throw new Exit2('error: parse 1');
  if (lines[firstNonBlank].trim() !== '*** Begin Patch') {
    throw new Exit2(`error: parse ${firstNonBlank + 1}`);
  }

  let lastNonBlank = -1;
  for (let k = lines.length - 1; k >= 0; k--) {
    if (!blank(lines[k])) {
      lastNonBlank = k;
      break;
    }
  }
  if (lastNonBlank < 0 || lines[lastNonBlank].trim() !== '*** End Patch') {
    throw new Exit2(`error: parse ${lines.length + 1}`);
  }

  const edits: Edit[] = [];
  let i = firstNonBlank + 1;

  while (i < lastNonBlank) {
    if (blank(lines[i])) {
      i++;
      continue;
    }

    const l = lines[i];
    if (l.startsWith('*** Add File: ')) {
      const p = l.slice(14).trim();
      i++;
      const fileLines: string[] = [];
      while (i < lastNonBlank) {
        const al = lines[i];
        if (al.startsWith('*** ')) break;
        if (al.startsWith('+')) {
          fileLines.push(al.slice(1));
          i++;
        } else if (al === '') {
          fileLines.push('');
          i++;
        } else {
          // Check if trailing blank lines before next section
          let allBlank = true;
          for (let k = i; k < lastNonBlank; k++) {
            if (lines[k].startsWith('*** ')) break;
            if (!blank(lines[k])) {
              allBlank = false;
              break;
            }
          }
          if (allBlank) {
            // trailing blanks, ignore them
            while (i < lastNonBlank && !lines[i].startsWith('*** ')) i++;
            break;
          }
          throw new Exit2(`error: parse ${i + 1}`);
        }
      }
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) !== null) throw new Fail('exists', p);
        tree.now.set(p, fileLines.length === 0 ? '' : fileLines.join('\n') + '\n');
      });
      continue;
    }

    if (l.startsWith('*** Delete File: ')) {
      const p = l.slice(17).trim();
      i++;
      // Delete File section has no lines
      while (i < lastNonBlank && blank(lines[i])) i++;
      if (i < lastNonBlank && !lines[i].startsWith('*** ')) {
        throw new Exit2(`error: parse ${i + 1}`);
      }
      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        tree.now.set(p, null);
      });
      continue;
    }

    if (l.startsWith('*** Update File: ')) {
      const p = l.slice(17).trim();
      const updateLineNum = i + 1;
      i++;

      let moveTo: string | null = null;
      if (i < lastNonBlank && lines[i].startsWith('*** Move to: ')) {
        moveTo = lines[i].slice(13).trim();
        i++;
      }

      const chunks: V4AChunk[] = [];
      let currentChunk: V4AChunk | null = null;

      while (i < lastNonBlank) {
        const ul = lines[i];
        if (ul.startsWith('*** ')) {
          if (ul.startsWith('*** End of File')) {
            if (currentChunk === null) {
              currentChunk = { anchor: null, lines: [], isEndOfFile: true };
              chunks.push(currentChunk);
            } else {
              currentChunk.isEndOfFile = true;
            }
            i++;
            // Chunks after End of File can happen or section ends
            currentChunk = null;
            continue;
          }
          break; // Next section or End Patch
        }

        if (ul.startsWith('@@')) {
          const anchorText = ul.slice(2).trim();
          currentChunk = { anchor: anchorText === '' ? null : anchorText, lines: [], isEndOfFile: false };
          chunks.push(currentChunk);
          i++;
          continue;
        }

        if (blank(ul)) {
          let allBlank = true;
          for (let k = i; k < lastNonBlank; k++) {
            if (lines[k].startsWith('*** ')) break;
            if (!blank(lines[k])) {
              allBlank = false;
              break;
            }
          }
          if (allBlank) {
            while (i < lastNonBlank && !lines[i].startsWith('*** ')) i++;
            break;
          }
        }

        if (ul.startsWith(' ') || ul.startsWith('-') || ul.startsWith('+') || ul === '') {
          if (currentChunk === null) {
            currentChunk = { anchor: null, lines: [], isEndOfFile: false };
            chunks.push(currentChunk);
          }
          if (ul.startsWith(' ')) currentChunk.lines.push({ kind: ' ', text: ul.slice(1) });
          else if (ul === '') currentChunk.lines.push({ kind: ' ', text: '' });
          else if (ul.startsWith('-')) currentChunk.lines.push({ kind: '-', text: ul.slice(1) });
          else currentChunk.lines.push({ kind: '+', text: ul.slice(1) });
          i++;
          continue;
        }

        // Check if trailing blank lines
        let allBlank = true;
        for (let k = i; k < lastNonBlank; k++) {
          if (lines[k].startsWith('*** ')) break;
          if (!blank(lines[k])) {
            allBlank = false;
            break;
          }
        }
        if (allBlank) {
          while (i < lastNonBlank && !lines[i].startsWith('*** ')) i++;
          break;
        }

        throw new Exit2(`error: parse ${i + 1}`);
      }

      if (chunks.length === 0 && moveTo === null) {
        throw new Exit2(`error: parse ${updateLineNum}`);
      }

      if (moveTo !== null) {
        moves.push({ oldPath: p, newPath: moveTo });
      }

      edits.push((tree) => {
        if (!safe(p)) throw new Fail('unsafe', p);
        if (tree.get(p) === null) throw new Fail('missing', p);
        if (moveTo !== null) {
          if (!safe(moveTo)) throw new Fail('unsafe', moveTo);
          if (tree.get(moveTo) !== null) throw new Fail('exists', moveTo);
        }

        const content = tree.get(p)!;
        const parsed = parseFile(content);
        let cursor = 0;

        for (const chunk of chunks) {
          if (chunk.anchor !== null) {
            // Find first line at or after cursor equal to anchor at first tier
            let found = -1;
            // Tier 0
            for (let k = cursor; k < parsed.lines.length; k++) {
              if (parsed.lines[k] === chunk.anchor) {
                found = k;
                break;
              }
            }
            if (found === -1 && !strict) {
              // Tier 1
              for (let k = cursor; k < parsed.lines.length; k++) {
                if (stripTrailing(parsed.lines[k]) === stripTrailing(chunk.anchor)) {
                  found = k;
                  break;
                }
              }
            }
            if (found === -1 && !strict) {
              // Tier 2
              for (let k = cursor; k < parsed.lines.length; k++) {
                if (stripBoth(parsed.lines[k]) === stripBoth(chunk.anchor)) {
                  found = k;
                  break;
                }
              }
            }
            if (found === -1) throw new Fail('no-match', p);
            cursor = found + 1;
          }

          const O: string[] = [];
          const N: HunkLine[] = [];
          for (const cl of chunk.lines) {
            if (cl.kind === ' ') {
              const cIdx = O.length;
              O.push(cl.text);
              N.push({ text: cl.text, isContext: true, contextIndex: cIdx });
            } else if (cl.kind === '-') {
              O.push(cl.text);
            } else if (cl.kind === '+') {
              N.push({ text: cl.text, isContext: false });
            }
          }

          if (O.length > 0) {
            const res = findOccurrences(parsed.lines, O, strict, cursor);
            let matchPos = -1;
            let matchTier = -1;
            if (chunk.isEndOfFile) {
              // takes only an occurrence that ends at file's last line
              for (const pos of res.occurrences) {
                if (pos + O.length === parsed.lines.length) {
                  matchPos = pos;
                  matchTier = res.tier;
                  break;
                }
              }
            } else if (res.occurrences.length > 0) {
              matchPos = res.occurrences[0];
              matchTier = res.tier;
            }

            if (matchPos === -1) throw new Fail('no-match', p);

            const repl = replaceLines(parsed.lines, matchPos, O, N, matchTier);
            parsed.lines.splice(matchPos, O.length, ...repl);
            cursor = matchPos + repl.length;
          } else {
            const insertPos = chunk.isEndOfFile ? parsed.lines.length : cursor;
            const repl = replaceLines(parsed.lines, insertPos, [''], N, 0);
            parsed.lines.splice(insertPos, 0, ...repl);
            cursor = insertPos + repl.length;
          }
        }

        const outText = serializeFile(parsed.lines, parsed.crlf, parsed.hasFinalBreak);
        if (moveTo !== null) {
          tree.now.set(p, null);
          tree.now.set(moveTo, outText);
        } else {
          tree.now.set(p, outText);
        }
      });
      continue;
    }

    throw new Exit2(`error: parse ${i + 1}`);
  }

  return edits;
}

export function run(args: string[]): { code: number; out: string[] } {
  let format: string | null = null;
  let check = false;
  let strict = false;
  const pos: string[] = [];
  let ended = false;
  for (const a of args) {
    if (!ended && a === '--') ended = true;
    else if (!ended && a.startsWith('-') && a !== '-') {
      if (a.startsWith('--format=') && format === null && FORMATS.includes(a.slice(9))) format = a.slice(9);
      else if (a === '--check' && !check) check = true;
      else if (a === '--strict' && !strict) strict = true;
      else return { code: 2, out: ['error: usage'] };
    } else pos.push(a);
  }
  if (pos.length > 1) return { code: 2, out: ['error: usage'] };
  const file = pos.length === 0 || pos[0] === '-' ? null : pos[0]!;
  let text = '';
  try {
    text = readFileSync(file ?? 0, 'utf8');
  } catch {
    if (file !== null) return { code: 2, out: ['error: no-patch'] };
  }
  const lines = patchLines(text);
  const kind = format === null || format === 'auto' ? detect(lines) : format;
  if (kind === null) return { code: 2, out: ['error: format'] };

  const moves: Array<{ oldPath: string; newPath: string }> = [];
  let edits: Edit[];
  try {
    if (kind === 'json') edits = jsonEdits(text, lines);
    else if (kind === 'search-replace') edits = searchReplaceEdits(text, lines, strict);
    else if (kind === 'unified') edits = unifiedEdits(text, lines, strict, moves);
    else if (kind === 'v4a') edits = v4aEdits(text, lines, strict, moves);
    else edits = [];

    if (edits.length === 0) throw new Exit2('error: parse 1');
  } catch (e) {
    if (e instanceof Exit2) return { code: 2, out: [e.line] };
    throw e;
  }

  const tree = new Tree();
  const fails: Fail[] = [];
  for (const edit of edits) {
    const before = new Map(tree.now);
    try {
      edit(tree);
    } catch (e) {
      if (!(e instanceof Fail)) throw e;
      tree.now.clear();
      for (const [k, v] of before) tree.now.set(k, v);
      fails.push(e);
    }
  }
  if (fails.length > 0) return { code: 1, out: [...fails.map((f) => `error: ${f.code} ${f.path}`), `failed: ${fails.length} of ${edits.length} edits`] };

  // Generate output rows
  // Find successful moves: old existed before and null now, new was null before and exists now
  const matchedMoves = new Map<string, string>(); // newPath -> oldPath
  for (const m of moves) {
    if (tree.original(m.oldPath) !== null && tree.now.get(m.oldPath) === null &&
        tree.original(m.newPath) === null && tree.now.get(m.newPath) !== null) {
      matchedMoves.set(m.newPath, m.oldPath);
    }
  }

  interface Row {
    sortKey: string;
    text: string;
  }
  const rowList: Row[] = [];

  for (const p of tree.now.keys()) {
    const was = tree.original(p);
    const now = tree.now.get(p)!;
    if (was === now) continue;

    if (matchedMoves.has(p)) {
      const oldP = matchedMoves.get(p)!;
      rowList.push({ sortKey: p, text: `R ${oldP} -> ${p}` });
    } else if (![...matchedMoves.values()].includes(p)) {
      rowList.push({ sortKey: p, text: `${was === null ? 'A' : now === null ? 'D' : 'M'} ${p}` });
    }

    if (check) continue;
    if (now === null) rmSync(p, { force: true });
    else {
      mkdirSync(dirname(p), { recursive: true });
      writeFileSync(p, now);
    }
  }

  rowList.sort((a, b) => Buffer.compare(Buffer.from(a.sortKey, 'utf8'), Buffer.from(b.sortKey, 'utf8')));
  const rows = rowList.map((r) => r.text);

  return { code: 0, out: [...rows, `ok: ${rows.length} ${rows.length === 1 ? 'file' : 'files'}`] };
}

const trialEnv = process.env.MAKEFUN_ENV_URL;
if (trialEnv !== undefined && trialEnv !== '') {
  const { runTrial } = await import('./runner.ts');
  await runTrial(trialEnv);
} else {
  const r = run(process.argv.slice(2));
  writeSync(1, r.out.map((l) => `${l}\n`).join(''));
  process.exitCode = r.code;
}

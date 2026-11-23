# makefun-mend-cli: mend patch tool for AI edits

Implementation of `mend`, a command-line patch tool that applies edits written by AI models in four formats:
1. Unified Diffs
2. SEARCH/REPLACE blocks
3. V4A patches
4. JSON edits

## Files
- `main.ts`: High-performance patch CLI in pure Node.js 22 standard library (zero external dependencies).
- `runner.ts`: Trial runner integration for the Make.fun environment.
- `SPEC.md`: Full specification document.
- `LICENSE`: MIT License.

## Verification
- 100/100 practice checks passed (score 1000/1000).
- Pure Node 22, strict path safety, atomicity, 3-tier matching.

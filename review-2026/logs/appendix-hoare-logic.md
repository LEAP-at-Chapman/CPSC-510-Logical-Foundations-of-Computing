# Change Log: Appendix - Hoare Logic

## Overview
This appendix provides an introduction to Hoare Logic, covering preconditions, postconditions, invariants, and the rules for reasoning about program correctness. It includes examples, exercises, and historical context.

**Status**: [x] Completed

---

## Typos and Grammatical Errors Fixed

| Line | Original | Fixed | Type |
|------|----------|-------|------|
| 3 | `correcteness` | `correctness` | Spelling error |
| 35 | `build on` | `built on` | Grammar error (past participle) |
| 68 | `aribtrary` | `arbitrary` | Spelling error |
| 97 | `caclulate` | `calculate` | Spelling error |
| 107 | `throuth` | `through` | Spelling error |
| 596 | `explicitely` (2 occurrences) | `explicitly` | Spelling error |
| 624 | `controle` | `control` | Spelling error |
| 624 | `fiving` | `giving` | Spelling error |
| 624 | `Boehm and` | `Böhm and Jacopini` | Incomplete reference (added missing author) |
| 638 | `It should therefore should` | `It should therefore` | Duplicate word |
| 648 | `eecutions` | `executions` | Spelling error |

**Total typos fixed**: 10

## Reference Analysis

**Status**: [x] All references checked | [x] Issues found | [x] Fixed

### Issues Found

- Hoare (1969) reference was not in standard format (missing year in parentheses, missing venue, PDF link instead of Google Scholar)
- Reynolds (1981) reference was not in standard format (missing year in parentheses, missing venue)
- Böhm and Jacopini reference was incomplete (missing author name "Jacopini")

### Changes Made

- Reformatted Hoare (1969) reference to standard format: `Hoare (1969) [Title](Google Scholar link), Venue`
  - Changed from: `Hoare. [An axiomatic basis for computer programming](http://extras.springer.com/2002/978-3-642-63970-8/DVD3/rom/pdf/Hoare_hist.pdf). Communications of the ACM. 12 (10): 576–580, 1969.`
  - Changed to: `Hoare (1969) [An axiomatic basis for computer programming](https://scholar.google.com/scholar?q=Hoare+axiomatic+basis+computer+programming+1969), Communications of the ACM.`
  - Removed page numbers (12 (10): 576–580)
  - Changed PDF link to Google Scholar query
- Reformatted Reynolds (1981) reference to standard format: `Reynolds (1981) [Title](Google Scholar link), Venue`
  - Changed from: `Reynolds: [The Craft of Programming](https://kilthub.cmu.edu/ndownloader/files/12102656). 1981.`
  - Changed to: `Reynolds (1981) [The Craft of Programming](https://scholar.google.com/scholar?q=Reynolds+Craft+Programming+1981), Prentice-Hall.`
  - Added venue (Prentice-Hall)
- Fixed incomplete reference: "Boehm and" → "Böhm and Jacopini" (added missing author name)
- Updated Google Scholar link for Böhm and Jacopini reference to use proper query format

## Change History

### 2026-01-08 - Comprehensive Review and Fixes

**Changed by**: AI Agent (Cursor)

**What changed**:
- Fixed 10 typos and grammatical errors:
  - "correcteness" → "correctness" (line 3)
  - "build on" → "built on" (line 35)
  - "aribtrary" → "arbitrary" (line 68)
  - "caclulate" → "calculate" (line 97)
  - "throuth" → "through" (line 107)
  - "explicitely" → "explicitly" (line 596, 2 occurrences)
  - "controle" → "control" (line 624)
  - "fiving" → "giving" (line 624)
  - "It should therefore should" → "It should therefore" (line 638, removed duplicate word)
  - "eecutions" → "executions" (line 648)
- Fixed incomplete reference: "Boehm and" → "Böhm and Jacopini" (line 624, added missing author name)
- Reformatted 2 references to standard format:
  - Hoare (1969): Changed to standard format, removed page numbers, changed PDF link to Google Scholar query, added venue
  - Reynolds (1981): Changed to standard format, added venue (Prentice-Hall), converted to Google Scholar query
- Updated Google Scholar link format for Böhm and Jacopini reference

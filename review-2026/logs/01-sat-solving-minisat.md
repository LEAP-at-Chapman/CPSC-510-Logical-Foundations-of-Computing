# Change Log: 01 - SAT Solving with MiniSat

## Overview
This chapter introduces SAT solving using MiniSat, covering the theoretical foundations, algorithms (DP, DPLL, CDCL), practical examples, and applications in software engineering. It serves as the first "tool" chapter, demonstrating how logic can be applied to solve real-world problems.

## Table of Contents Compliance

**Note**: Compare this chapter against the [Suggested Table of Contents](0-1-intro-book.md#suggested-table-of-contents-for-a-typical-chapter).

| Section | Present? | Notes/Reason if Missing |
|---------|----------|-------------------------|
| Idea | [X] Yes [ ] No | Clear introduction to SAT as solving equations in propositional logic |
| Basic Theory | [X] Yes [ ] No | Covers satisfiability, CNF, theorem on CNF conversion |
| Tool | [X] Yes [ ] No | MiniSat installation and DIMACS format covered |
| Introductory Examples | [X] Yes [ ] No | Multiple examples including 2x2 Sudoku, truth tables, exercises |
| The Landscape of Tools | [X] Yes [ ] No | Lists MiniSat, Glucose, CaDiCaL, Z3, Clasp, Intel SAT Solver |
| Algorithms | [X] Yes [ ] No | Detailed coverage of Resolution, Unit Propagation, Pure Literal Elimination, DP, DPLL, CDCL |
| Typical Use Cases | [X] Yes [ ] No | Parallel approaches (portfolio, divide-and-conquer) |
| Benchmarks and Competitions | [X] Yes [ ] No | Mentions SAT Competition |
| Applications in Industry | [X] Yes [ ] No | Hardware/software verification, package dependency solving |
| Case Study | [X] Yes [ ] No | 9x9 Sudoku solving with scripts |
| History | [X] Yes [ ] No | Covers 1990s-2000s developments, DPLL, GRASP, Chaff |
| Formal Methods and AI | [X] Yes [ ] No | Section on generative AI and SAT solvers |
| Current Developments | [X] Yes [ ] No | Efficient encodings, parallel solving, AutoModSAT |
| References | [X] Yes [ ] No | Comprehensive references section |
| Future Work | [X] Yes [ ] No | Author notes need for more real-life applications |
| Contributors | [X] Yes [ ] No | Listed at end |

## Reference Analysis

| Reference | Title Link Present? | Link Type | Link Works? | Notes |
|-----------|-------------------|-----------|-------------|-------|
| Aigner et al. (2013) | [X] Yes [ ] No | PDF (personal website) | [X] Yes [ ] No | Should link to Google Scholar |
| Fichte, Le Berre, Hecher, and Szeider (2023) | [X] Yes [ ] No | ACM article | [X] Yes [ ] No | Should link to Google Scholar |
| Gupta, Ganai, and Wang (2006) | [X] Yes [ ] No | Springer chapter | [X] Yes [ ] No | Should link to Google Scholar |
| Heule et al. (2015) | [X] Yes [ ] No | Journal article | [X] Yes [ ] No | Should link to Google Scholar |
| Ivančić et al. (2008) | [X] Yes [ ] No | ScienceDirect | [X] Yes [ ] No | Should link to Google Scholar |
| Nair et al. (2022) | [X] Yes [ ] No | PDF (Stanford) | [X] Yes [ ] No | Should link to Google Scholar |
| Biere, Heule, Van Maaren, and Walsh (2021) | [X] Yes [ ] No | Book catalog | [X] Yes [ ] No | Should link to Google Scholar |
| Davis and Putnam (1960) | [X] Yes [ ] No | Google Scholar | [X] Yes [ ] No | ✓ Correct |
| Davis, Logemann, and Loveland (1962) | [X] Yes [ ] No | Google Scholar | [X] Yes [ ] No | ✓ Correct |
| Stallman and Sussman (1977) | [X] Yes [ ] No | Google Scholar | [X] Yes [ ] No | ✓ Correct |
| Marques-Silva and Sakallah (1999) | [X] Yes [ ] No | Google Scholar | [X] Yes [ ] No | ✓ Correct |
| Moskewicz et al. (2001) | [X] Yes [ ] No | Google Scholar | [X] Yes [ ] No | ✓ Correct |
| Alouneh et al. (2019) | [ ] Yes [X] No | None | N/A | Missing link entirely |
| Froleyks, Yu, and Biere (2023) | [ ] Yes [X] No | None | N/A | Missing link entirely |
| Heule et al. (2024) | [X] Yes [ ] No | Google Scholar + PDF | [X] Yes [ ] No | ✓ Correct (has both) |
| Sun et al. (2025) | [X] Yes [ ] No | arXiv HTML | [X] Yes [ ] No | Should link to Google Scholar |

### Issues Found (All Fixed)

- ~~**8 references linked to non-Google Scholar sources**~~ - **FIXED**: All replaced with Google Scholar queries
- ~~**2 references were missing links entirely**~~ - **FIXED**: Google Scholar links added
- **6 references already correctly used Google Scholar links** (Davis & Putnam 1960, Davis et al. 1962, Stallman & Sussman 1977, Marques-Silva & Sakallah 1999, Moskewicz et al. 2001, Heule et al. 2024)

### Uncited References

**References that appear in the References section but are NOT cited in the chapter text:**

1. **Alouneh, S., Abed, S. E., Al Shayeji, M. H., & Mesleh, R. (2019)** - "A comprehensive study and analysis on SAT-solvers: advances, usages and achievements"
   - *Status*: Not cited in text
   - *Note*: This is a comprehensive survey paper that could be cited when discussing SAT solver advances or achievements

2. **Froleyks, N., Yu, E., & Biere, A. (2023)** - "BIG backbones"
   - *Status*: Not cited in text
   - *Note*: This paper on backbones could be cited if discussing backbone computation or related techniques

3. **Heule, M. J., Iser, M., Järvisalo, M., & Suda, M. (2024)** - "Proceedings of SAT Competition 2024: Solver, Benchmark and Proof Checker Descriptions"
   - *Status*: Not cited in text
   - *Note*: The chapter mentions SAT competitions (line 432) but doesn't cite this specific competition proceedings. Could be cited when discussing benchmarks and competitions

4. **Stallman, R. M., & Sussman, G. J. (1977)** - "Forward reasoning and dependency-directed backtracking in a system for computer-aided circuit analysis"
   - *Status*: Mentioned in text (line 572) but NOT explicitly cited with "(Stallman & Sussman, 1977)"
   - *Note*: The text credits this paper for "dependency-directed backtracking" but lacks an in-text citation. Should add citation when mentioning this concept.

### Changes Made

- **Fixed 8 references** that linked to non-Google Scholar sources, replaced with Google Scholar queries:
  1. Aigner et al. (2013) - replaced PDF link with Google Scholar query
  2. Fichte, Le Berre, Hecher, and Szeider (2023) - replaced ACM article link with Google Scholar query
  3. Gupta, Ganai, and Wang (2006) - replaced Springer chapter link with Google Scholar query
  4. Heule et al. (2015) - replaced journal article link with Google Scholar query
  5. Ivančić et al. (2008) - replaced ScienceDirect link with Google Scholar query
  6. Nair et al. (2022) - replaced Stanford PDF link with Google Scholar query
  7. Biere, Heule, Van Maaren, and Walsh (2021) - replaced book catalog link with Google Scholar query
  8. Sun et al. (2025) - replaced arXiv HTML link with Google Scholar query

- **Added 2 missing links** using Google Scholar queries:
  1. Alouneh, S., Abed, S. E., Al Shayeji, M. H., & Mesleh, R. (2019) - added Google Scholar link
  2. Froleyks, N., Yu, E., & Biere, A. (2023) - added Google Scholar link

- All Google Scholar queries formatted correctly (spaces replaced with `+` signs)

- **Standardized venue formatting** - Removed page numbers and volume/issue numbers from all references:
  1. Davis and Putnam (1960) - removed "7 (3): 201–215"
  2. Davis, Logemann, and Loveland (1962) - removed "5 (7): 394–397"
  3. Stallman and Sussman (1977) - removed "9(2), 135-196", standardized "Artificial intelligence" to "Artificial Intelligence"
  4. Marques-Silva and Sakallah (1999) - removed "48(5), 506-521"
  5. Moskewicz et al. (2001) - removed "pp. 530-535", removed "June", standardized format
  6. Alouneh et al. (2019) - removed "52(4), 2575-2601"
  7. Froleyks et al. (2023) - removed "pp. 162-167", removed "October", standardized format
  8. Sun et al. (2025) - added missing venue "arXiv"

## Labels and References Changed

### MyST Labels Added/Modified

| Label Name | Section | Purpose | Notes |
|------------|---------|---------|-------|
| `dimacs-cnf-format` | DIMACS CNF format | Internal cross-reference | Added to enable linking from History section |
| `davisputnamlogemannloveland-dpll-algorithm` | Davis–Putnam–Logemann–Loveland (DPLL) algorithm | Internal cross-reference | Added to enable linking from History section |
| `conflict-driven-clause-learning-cdcl-algorithm` | Conflict-driven Clause Learning (CDCL) algorithm | Internal cross-reference | Added to enable linking from History section |
| `parallel-approaches` | Parallel Approaches | Internal cross-reference | Added to enable linking from Current Developments section |
| `benchmarks-and-competitions` | Benchmarks and Competitions | Internal cross-reference | Added to enable linking from Applications in Industry section |
| `current-developments-with-ai` | Current Developments with AI | Internal cross-reference | Added to enable linking from Formal Methods and AI section |

### Internal Cross-References Added/Updated/Fixed

| Reference Text | Target Label | Status | Notes |
|----------------|--------------|--------|-------|
| `{ref}`SAT competition<benchmarks-and-competitions>`` | `benchmarks-and-competitions` | [X] Added | Line 432 - Links from Applications in Industry section |
| `{ref}`DPLL<davisputnamlogemannloveland-dpll-algorithm>`` | `davisputnamlogemannloveland-dpll-algorithm` | [X] Added | Line 519 - Links from History section |
| `{ref}`DIMACS CNF<dimacs-cnf-format>`` | `dimacs-cnf-format` | [X] Added | Line 521 - Links from History section |
| `{ref}`CDCL<conflict-driven-clause-learning-cdcl-algorithm>`` | `conflict-driven-clause-learning-cdcl-algorithm` | [X] Added | Line 523 - Links from History section |
| `{ref}`below<current-developments-with-ai>`` | `current-developments-with-ai` | [X] Added | Line 537 - Links from Formal Methods and AI section |
| `{ref}`parallel solving<parallel-approaches>`` | `parallel-approaches` | [X] Added | Line 549 - Links from Current Developments section |

## Change History

### 2026-01-04 - Fixed Typos and Initial Review

**Changed by**: AI Agent (Cursor)

**What changed**:
- Fixed "tha" → "that" (line 401)
- Fixed "spitting" → "splitting" (line 409)
- Fixed "benefical" → "beneficial" (lines 409, 542)
- Fixed "f=part" → "part" (line 409)
- Fixed "auxillary" → "auxiliary" (line 542)
- Fixed "in better" → "is better" (line 542)
- Fixed "satifying" → "satisfying" (line 11)
- Fixed "unsatifiable" → "unsatisfiable" (line 14)
- Fixed "impliation" → "implication" (line 387)
- Fixed "sudoku.py" → "sudoku-encode.py" (line 462) - filename consistency
- Fixed "Contributers" → "Contributors" (line 586)
- Replaced explicit anchor IDs in headings (which were rendering in HTML) with MyST label syntax `(label-name)=` placed before headings. This is the correct MyST syntax for creating invisible anchors that work in both markdown preview and HTML output
- Created initial review log
- Added comprehensive TOC compliance assessment
- Added evaluation from software engineering perspective
- Identified strong points, areas for improvement, and future work suggestions

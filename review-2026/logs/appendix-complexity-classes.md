# Change Log: Appendix - Complexity Classes

## Overview
This appendix provides an overview of complexity classes and maps them to logics covered in the book. 

## Reference Analysis

- All references were missing venues (required by style guide)
- All references used "&" instead of "and" for two authors (should be "and" per style guide)
- Reference format was inconsistent: used `Author(s) (Year): [Title](link)` instead of `Author(s) (Year) [Title](link), Venue`

### Changes Made

- Reformatted all 15 references to standard format: `Author(s) (Year) [Title](Google Scholar link), Venue`
- Changed "&" to "and" for all two-author references:
  - "Hartmanis & Stearns" → "Hartmanis and Stearns"
  - "Fischer & Rabin" → "Fischer and Rabin"
  - "Stockmeyer & Meyer" → "Stockmeyer and Meyer"
  - "Schmidt-Schauß & Smolka" → "Schmidt-Schauß and Smolka"
  - "Arora & Barak" → "Arora and Barak"
- Added missing venues to all references:
  - Hartmanis and Stearns (1965): Journal of the ACM
  - Savitch (1970): Journal of Computer and System Sciences
  - Cook (1971): STOC
  - Levin (1973): Problems of Information Transmission
  - Fischer and Rabin (1974): Proceedings of the AMS
  - Stockmeyer and Meyer (1973): STOC
  - Immerman (1988): SIAM Journal on Computing
  - Szelepcsényi (1988): Acta Informatica
  - Schmidt-Schauß and Smolka (1991): Artificial Intelligence
  - Tobies (2001): Journal of Artificial Intelligence Research
  - Baader et al. (2005): IJCAI
  - Calvanese et al. (2007): Journal of Automated Reasoning
  - Kazakov (2008): KR
  - Arora and Barak (2009): Cambridge University Press
  - Papadimitriou (1994): Addison-Wesley
  - Baader et al. (2003): Cambridge University Press
- Changed format from `Author(s) (Year): [Title](link)` to `Author(s) (Year) [Title](link), Venue`
- Fixed table references: Changed "&" to "and" in complexity classes table (Hartmanis & Stearns → Hartmanis and Stearns, Fischer & Rabin → Fischer and Rabin) and DL Complexity Summary table (Schmidt-Schauß & Smolka → Schmidt-Schauß and Smolka)

## Change History

### 2026-01-08 - Reference Formatting Fixes

**Changed by**: AI Agent (Cursor)

- Reformatted all 15 references to standard format: `Author(s) (Year) [Title](link), Venue`
- Changed "&" to "and" for all two-author references in References section (5 references)
- Added missing venues to all 15 references
- Changed reference format from `Author(s) (Year): [Title](link)` to `Author(s) (Year) [Title](link), Venue`
- Fixed table references: Changed "&" to "and" in complexity classes table:
  - "Hartmanis & Stearns" → "Hartmanis and Stearns" (line 14)
  - "Fischer & Rabin" → "Fischer and Rabin" (line 17)
- Fixed table reference in DL Complexity Summary table:
  - "Schmidt-Schauß & Smolka" → "Schmidt-Schauß and Smolka" (line 38)

### 2026-01-04 - Added "Logics in Book" Column

**Changed by**: AI Agent (Cursor)

**What changed**:
- Added new column "Logics in Book" to the complexity classes table
- Mapped decidable logics from the book to their complexity classes:
  - Propositional Logic fragments (2-SAT, Horn-SAT, SAT, Tautology)
  - Constraint Satisfaction (CSP)
  - Modal/Temporal/Epistemic Logic (model checking)
  - SMT Solving (various decidable theories)
- Added note section explaining undecidable logics (HOL, Dependent Types, Hoare Logic, full Prolog)

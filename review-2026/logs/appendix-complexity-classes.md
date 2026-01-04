# Change Log: Appendix - Complexity Classes

## Overview
This appendix provides an overview of complexity classes and maps them to logics covered in the book.

**Status**: [ ] In Progress | [X] Completed | [ ] Needs Follow-up

---

## Change History

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

**Why changed**:
- User requested to add a column showing which logics from the book appear in each complexity class
- Needed to distinguish between decidable (included in table) and undecidable (noted separately) logics
- Improves connection between complexity theory and the book's content

**Notes**:
- Focused on decidable problems only
- Undecidable logics are documented in a separate note section
- Marked as draft in the file header for verification


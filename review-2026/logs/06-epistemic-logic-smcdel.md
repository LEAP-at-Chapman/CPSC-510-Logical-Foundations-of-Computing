# Change Log: 06-epistemic-logic-smcdel

## Overview
Chapter 6 on Epistemic Logic with SMCDEL introduces epistemic logic for reasoning about knowledge and belief, Dynamic Epistemic Logic (DEL) for modeling information change, and the SMCDEL tool. The chapter covers history, basic theory, algorithms, social networks applications, industry applications, and a case study on rescue drone coordination.

**Status**: [X] In Progress | [ ] Completed | [ ] Needs Follow-up

## What Changed

### Typos Fixed
1. Line 24: Fixed "lense" → "lens"
2. Line 729: Fixed "Referenes" → "References" (in section heading)

### Formatting Fixed
3. Line 231: Added missing "###" heading marker for "Epistemic Planners" section

### Reference Formatting Fixed
- Reformatted all 27 references to match required format: `Author(s) (Year) [Title](link), Venue`
- Removed page numbers from all references (as required):
  - Halpern and Moses (1990): removed "37(3): 549–587"
  - Baltag, Moss, and Solecki (2004): removed "139: 165–224"
  - van Benthem, van Eijck, Gattinger, and Su (2016): removed "25(1): 37–71"
  - Renne (2008): removed "20: 1–31" (was in van Ditmarsch et al. 2017)
  - Smets and Velázquez-Quesada (2017): removed "LNCS 10455: 377–390"
  - Baltag, Christoff, Rendsvig, and Smets (2019): removed "107(3): 489–531"
- Standardized reference formatting: added periods after years, removed italic formatting from venue names
- Changed "arXiv preprint" → "arXiv" for consistency
- Fixed "Acta Philosophica Fennica" (removed italics)

## Table of Contents Compliance

**Note**: Compare this chapter against the [Suggested Table of Contents](0-1-intro-book.md#suggested-table-of-contents-for-a-typical-chapter).

| Section | Present? | Notes/Reason if Missing |
|---------|----------|-------------------------|
| Idea | [X] Yes [ ] No | ✓ Present |
| Basic Theory | [X] Yes [ ] No | ✓ Present (comprehensive coverage) |
| Tool | [X] Yes [ ] No | ✓ Present with Installation, Model Example, Adding Public Announcement |
| Introductory Examples | [X] Yes [ ] No | ✓ Present (Model Example, Adding Public Announcement) |
| The Landscape of Tools | [X] Yes [ ] No | ✓ Present (comprehensive with Model Checkers, Interactive Theorem Provers, Epistemic Planners, AI-Oriented Systems) |
| Algorithms | [X] Yes [ ] No | ✓ Present (detailed coverage of BDD-based algorithms, model evaluation, dynamic updates, complexity) |
| Typical Use Cases | [X] Yes [ ] No | ✓ Present (comprehensive section) |
| Benchmarks and Competitions | [ ] Yes [X] No | Not present - could be added |
| Applications in Industry | [X] Yes [ ] No | ✓ Present (comprehensive with multiple subsections) |
| Case Study | [X] Yes [ ] No | ✓ Present (Rescue Drone Coordination) |
| History | [X] Yes [ ] No | ✓ Present (comprehensive timeline from 1960s to present) |
| Formal Methods and AI | [X] Yes [ ] No | ✓ Present (section "Epistemic Logic and Generative AI") |
| Current Developments | [ ] Yes [X] No | Not present as separate section, but covered in History and Epistemic Logic and Generative AI |
| References | [X] Yes [ ] No | ✓ Present |
| Future Work | [ ] Yes [X] No | Not present |
| Contributors | [ ] Yes [X] No | Author listed at top but no Contributors section |

**Overall Assessment**: This chapter follows the suggested TOC very well. Almost all major sections are present, with excellent coverage of algorithms, applications, and history. The chapter has a dedicated "Epistemic Logic and Generative AI" section which effectively covers the "Formal Methods and AI" requirement. The only missing sections are "Benchmarks and Competitions" (which could be added), "Current Developments" (though this is covered in History and Generative AI sections), "Future Work", and "Contributors". The chapter is comprehensive and well-structured.

## Reference Analysis

**Status**: [X] All references checked | [X] Issues found | [X] Fixed

### Reference Link Verification

All 27 references have been checked. Most have Google Scholar links, with a few exceptions (direct PDF links for some applications, which is acceptable per the rules).

### Issues Found

- **Reference formatting inconsistent**: References used inconsistent format, some missing periods after years
- **Page numbers present**: Several references included page numbers which should be removed
- **Italic formatting**: Some venue names were italicized, should be plain text
- **"arXiv preprint" vs "arXiv"**: Inconsistent terminology

### Uncited References

**References that appear in the References section but are NOT cited in the chapter text:**

1. **Bramblett et al. (2023)** - "Epistemic Planning for Heterogeneous Robotic Systems"
   - *Status*: Not cited in text
   - *Note*: This reference appears in the References section but is never cited. It should either be cited where relevant (e.g., in Epistemic Planners section or Typical Use Cases) or removed.

**References cited in text but NOT in References section:**

1. **Muise et al.** - "Epistemic Planning" (cited on line 645)
   - *Status*: Cited in text but not in References section
   - *Note*: This is cited as "[Muise et al., Epistemic Planning]" but there's no corresponding entry in the References section. Should be added or the citation should be removed.

2. **van Ditmarsch (2000)** - Cited on line 643 as "van Ditmarsch (2000)" for muddy children
   - *Status*: Cited in text but not in References section
   - *Note*: This is cited but there's no corresponding entry in the References section. Should be added or the citation should be removed/updated.

### Changes Made

- **Reformatted all 27 references** to match required format: `Author(s) (Year) [Title](link), Venue`
- **Removed page numbers** from all references:
  1. Halpern and Moses (1990) - removed "37(3): 549–587"
  2. Baltag, Moss, and Solecki (2004) - removed "139: 165–224"
  3. van Benthem, van Eijck, Gattinger, and Su (2016) - removed "25(1): 37–71"
  4. van Ditmarsch, van Eijck, Pardo, Ramezanian, and Schwarzentruber (2017) - removed "20: 1–31"
  5. Smets and Velázquez-Quesada (2017) - removed "LNCS 10455: 377–390"
  6. Baltag, Christoff, Rendsvig, and Smets (2019) - removed "107(3): 489–531"
- **Standardized formatting**: Added periods after years, removed italic formatting from venue names
- **Fixed "arXiv preprint" → "arXiv"** for consistency (Bramblett et al. 2023, Sileo et al. 2023, Wu et al. 2025)
- **Fixed "Acta Philosophica Fennica"** (removed italics)

## Change History

### 2026-01-05 - Initial Review

**Changed by**: AI Agent

**What changed**:
- Fixed typo: "lense" → "lens" (line 24)
- Fixed typo: "Referenes" → "References" (line 729, section heading)
- Added missing "###" heading marker for "Epistemic Planners" section (line 231)
- Reformatted all 27 references to match required format: `Author(s) (Year) [Title](link), Venue`
- Removed page numbers from 6 references (as required)
- Standardized reference formatting: added periods after years, removed italic formatting from venue names
- Fixed "arXiv preprint" → "arXiv" for consistency (3 references)
- Fixed "Acta Philosophica Fennica" (removed italics)

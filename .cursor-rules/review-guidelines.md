# Book Review Guidelines

## Philosophy

This book was written collaboratively with students. The review process should:

1. **Preserve student contributions**: Maintain the voice and work of the students
2. **Improve clarity and correctness**: Fix errors, improve explanations, ensure technical accuracy
3. **Enhance presentation**: Improve formatting, consistency, and readability
4. **Maintain appropriate standards**: Aim for quality suitable for presenting to colleagues, not necessarily publication-quality academic writing

## Review Priorities

### High Priority
- **Technical correctness**: Fix factual errors, incorrect complexity claims, wrong algorithm descriptions
- **Clarity**: Improve unclear explanations, add missing context
- **Completeness**: Fill in obvious gaps, ensure examples work
- **Consistency**: Standardize notation, terminology, formatting

### Medium Priority
- **Writing quality**: Improve grammar, sentence structure, flow
- **Organization**: Improve chapter structure, section ordering
- **References**: Verify links, improve citations
- **Examples**: Ensure code examples are correct and runnable

### Low Priority
- **Stylistic polish**: Minor wording improvements
- **Aesthetic formatting**: Visual improvements that don't affect content

## What NOT to Do

- Don't rewrite entire sections in a completely different voice
- Don't remove student contributions or significantly alter their writing style
- Don't add extensive new content without checking with the user
- Don't change the fundamental structure or approach of chapters

## Chapter-Specific Notes

- Each chapter may have different authors/contributors
- Some chapters may be more complete than others
- Preserve the pedagogical approach chosen by the original authors

## Important Style Guides

**MUST READ AND FOLLOW** these files in `content/`:

1. **`how-to-cite.md`** - Citation format guidelines:
   - In-text: Use `(Author(s), Year)` or `(Author)` if year is obvious
   - References section: Format as `Author(s) (Year) [Title](link), Venue`
   - Use last names only, proper formatting for multiple authors
   - All references must be cited in text; don't list uncited references
   - See file for detailed examples and formatting rules

2. **`how-to-contribute.md`** - Writing and contribution guidelines:
   - Use inline clickable links for further reading
   - Avoid long uninterrupted code snippets
   - Link source code and resources
   - Follow table of contents structure from `0-1-intro-book.md`
   - Don't have only a single subsection in a section
   - Use local paths for internal links (e.g., `[link](0-1-intro-book.md)`)
   - Wikipedia can be used for inline links but not as authoritative references
   - References should have clear purpose (further reading, evidence, etc.)

When reviewing or editing chapters, ensure all changes comply with these style guides.

## Working Style

- When making changes, explain what was changed and why
- Ask for clarification if unsure about the scope of changes
- Suggest improvements rather than just implementing them when the change is significant
- Preserve author credits and attribution

## Change Logging

**IMPORTANT**: All changes must be logged in the `review-2026/` folder.

### Logging Requirements

1. **For each chapter change**, update the corresponding log file in `review-2026/logs/`:
   - Use the template: `review-2026/logs/TEMPLATE.md`
   - **Log file naming**: Use the same name as the chapter file (e.g., `0-3-intro-propositional-logic.md` → `logs/0-3-intro-propositional-logic.md`)
   - Do NOT add "chapter-" prefix to log file names
   - Record: date, what changed, who made the change

2. **"What changed" format**:
   - **List all changes explicitly**, one per line
   - For typos: list each typo fix separately (e.g., "Fixed 'devided' → 'divided' (line 9)")
   - Include line numbers or section names when helpful
   - Be specific about what was changed

3. **"Why changed" section**:
   - **Optional** - Omit for trivial changes like typos
   - Include only when the reason is not obvious or needs explanation
   - Use for substantive changes that require justification

4. **Table of Contents Compliance**:
   - **For each chapter**, check compliance with the [Suggested Table of Contents](0-1-intro-book.md#suggested-table-of-contents-for-a-typical-chapter)
   - Use the table in the log template to track which sections are present
   - **Provide opinion** on whether deviations from the suggested TOC are justified
   - Not all chapters need all sections, but there should be a good reason for omissions

5. **Update the summary**: After making changes, update `review-2026/summary.md`:
   - Update chapter status
   - Add entry to "Key Changes Made" section
   - Update review statistics

### Log File Locations

- Chapter logs: `review-2026/logs/[chapter-name].md` (matches chapter file name)
- Summary: `review-2026/summary.md`
- Template: `review-2026/logs/TEMPLATE.md`


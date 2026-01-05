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
- **References**: Verify links, improve citations (see Reference Checking section below)
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

## Reference Checking (REQUIRED)

**CRITICAL**: During every chapter review, you MUST verify all references in the References section.

### Reference Link Requirements

1. **All paper titles MUST link to Google Scholar queries**:
   - Format: `[Title](https://scholar.google.com/scholar?q=Title+with+spaces+replaced+by+plus+signs)`
   - The link should allow readers to easily find the paper on Google Scholar
   - Example: `[A Computing Procedure for Quantification Theory](https://scholar.google.com/scholar?q=A+Computing+Procedure+for+Quantification+Theory)`

2. **Google Scholar query format**:
   - Replace spaces in the title with `+` signs
   - Use the full paper title (or a significant portion if very long)
   - The query should be specific enough to find the paper easily
   - Test the link to ensure it returns relevant results

3. **Exceptions** (acceptable alternatives):
   - Links to official documentation (for tools/software)
   - Links to project websites (for software/tools)
   - Google Scholar is preferred for academic papers

4. **What to check**:
   - Every reference in the References section
   - Verify the link works and goes to Google Scholar (or acceptable alternative)
   - Ensure the title in the link matches the paper title
   - Check that the Google Scholar query is properly formatted (spaces → `+`)
   - **Verify every reference has a venue** (journal, conference, publisher, etc.) Add venue if possible.
   - **Remove page numbers** from references (they are not required)

5. **When fixing references**:
   - **Replace non-Google Scholar links** with Google Scholar queries during review
   - **Add missing links** using Google Scholar query format
   - Format: `[Title](https://scholar.google.com/scholar?q=Title+with+spaces+replaced+by+plus+signs)`
   - Remove special characters from titles or URL-encode them appropriately
   - For very long titles, use a significant portion that will find the paper
   - Test the query to ensure it returns relevant results (if possible)

6. **Check for uncited references**:
   - **REQUIRED**: Verify that every reference in the References section is cited in the text
   - Create a list of references that appear in the References section but are NOT cited anywhere in the chapter text
   - Document this list in the "Reference Analysis" section of the log
   - References should only appear in the References section if they are actually cited in the text

7. **Log all reference issues and fixes**:
   - Missing links
   - Broken links
   - Links that don't go to Google Scholar (when they should)
   - Incorrectly formatted Google Scholar queries
   - **Uncited references** (references in References section but not cited in text)
   - All fixes made (document in "Changes Made" section)
   - See "Reference Analysis" section in log template

## MyST Labeling and Cross-References

### Creating Section Labels

When creating internal cross-references to sections within a chapter:

1. **Use MyST label syntax** for section headings:
   ```markdown
   (label-name)=
   ## Section Heading
   ```
   - Place the label on the line immediately before the heading
   - Use lowercase with hyphens (e.g., `benchmarks-and-competitions`)
   - Labels are invisible in the rendered HTML

2. **Reference labels using MyST ref role**:
   ```markdown
   {ref}`link text<label-name>`
   ```
   - This creates a clickable link that works in both markdown preview and HTML
   - Example: `{ref}`SAT competition<benchmarks-and-competitions>``

3. **When to add labels**:
   - Sections that are referenced from elsewhere in the chapter
   - Sections that might be referenced from other chapters
   - Important subsections that readers might want to jump to

4. **Label naming conventions**:
   - Use descriptive, lowercase names with hyphens
   - Match the section topic (e.g., `dimacs-cnf-format`, `davisputnamlogemannloveland-dpll-algorithm`)
   - Keep labels concise but meaningful

5. **What to check during review**:
   - All internal cross-references use `{ref}`role syntax
   - All referenced sections have corresponding labels
   - Labels are defined before the heading (not in the heading)
   - Link text is clear and descriptive
   - All links work (verify in HTML output if possible)

6. **Log all label/reference changes**:
   - New labels added
   - References updated to use `{ref}`role
   - Broken references fixed
   - See "Labels and References Changed" section in log template

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

6. **Reference Analysis** (REQUIRED):
   - **For each chapter**, analyze all references in the References section
   - Verify that all paper titles link to Google Scholar queries (or acceptable alternatives)
   - Check that links work and are properly formatted
   - Document any issues found (missing links, broken links, incorrect formatting)
   - See "Reference Analysis" section in log template

7. **Labels and References Changed**:
   - Document all MyST labels added or modified
   - Document all internal cross-references added, updated, or fixed
   - List which sections now have labels
   - List which references were updated to use `{ref}`role syntax
   - See "Labels and References Changed" section in log template

8. **Software Engineering Perspective Evaluation** (REQUIRED):
   - **For each chapter**, include an evaluation section from the perspective of a software engineer with strong programming/system design background but limited formal logic training
   - This evaluation must assess: **"Will this chapter help a newcomer understand what logic can do for software engineering?"**
   - The evaluation must include:
     - **Strong Points**: What the chapter does well for this audience
     - **Areas for Improvement**: Specific suggestions for making it more accessible/useful
     - **Suggested Future Work**: Concrete additions that would strengthen the chapter
     - **Overall Assessment**: A clear answer to whether the chapter successfully bridges logic and software engineering
   - Focus on practical applicability, integration guidance, and real-world relevance
   - See `review-2026/logs/01-sat-solving-minisat.md` for an example of this evaluation format

5. **Update the summary**: After making changes, update `review-2026/summary.md`:
   - Update chapter status
   - Add entry to "Key Changes Made" section
   - Update review statistics

### Log File Locations

- Chapter logs: `review-2026/logs/[chapter-name].md` (matches chapter file name)
- Summary: `review-2026/summary.md`
- Template: `review-2026/logs/TEMPLATE.md`


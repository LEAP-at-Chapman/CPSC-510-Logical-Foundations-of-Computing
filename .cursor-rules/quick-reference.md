# Quick Reference for Cursor Agent

## When Reviewing Content

1. **Check technical accuracy first** - complexity claims, logic classifications, algorithm descriptions
2. **Preserve student voice** - don't completely rewrite, improve what's there
3. **Fix obvious errors** - typos, broken links, incorrect code
4. **Improve clarity** - add context, clarify explanations
5. **Maintain consistency** - notation, terminology, formatting
6. **Check TOC compliance** - compare against suggested table of contents, note and evaluate deviations
7. **Log all changes** - update `review-2026/logs/[chapter-name].md` and `review-2026/summary.md`

## Logging Checklist

- [ ] Create/update log file with same name as chapter (no "chapter-" prefix)
- [ ] List all changes explicitly in "What changed" (one per line, include typos separately)
- [ ] Omit "Why changed" for trivial changes like typos
- [ ] Check TOC compliance and provide opinion on deviations
- [ ] Update summary.md with status and key changes

## Common Issues to Watch For

- Complexity class mismatches (decidable vs undecidable)
- Broken or outdated links
- Code examples that don't match descriptions
- Code examples that are too long for a human reader
- Inconsistent mathematical notation
- Missing context or explanations
- Formatting inconsistencies

## When Unsure

- Ask the user before making significant structural changes
- Suggest improvements rather than implementing major rewrites
- Preserve author credits and original structure
- Explain what you changed and why

## File Structure

- Main content: `content/*.md`
- Examples: `content/examples/`, `src/`
- Images: `content/images/`
- Appendices: `content/appendix-*.md`
- Review logs: `review-2026/logs/`
- Review summary: `review-2026/summary.md`

## Style Guides (MUST FOLLOW)

- **Citation format**: See `content/how-to-cite.md`
  - In-text: `(Author(s), Year)` or `(Author)`
  - References: `Author(s) (Year) [Title](link), Venue`
  - All references must be cited in text

- **Writing guidelines**: See `content/how-to-contribute.md`
  - Use inline clickable links
  - Avoid long code blocks without explanation
  - Follow table of contents structure
  - Use local paths for internal links


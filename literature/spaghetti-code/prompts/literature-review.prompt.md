---
type: agent-workflow
version: 1.1
author: Alexander Kurz
created: 2025-10-22
updated: 2025-10-22
description: Automated literature review workflow
prerequisites:
  - pdftotext command-line tool installed
  - PDF files in parent folder
  - content/references.bib file exists (or will be created)
  - AI agent with file system access
---

# Literature Review Agent Workflow

## Overview

This is a **prompt script** (also known as an AI workflow definition, runbook, agent instruction file, natural language script). It contains natural language instructions that guide an AI agent to conduct a systematic literature review.

It's main purpose is to help with tracking down the **history of the term spaghetti code**.

## Input

- All PDF files in the parent folder
- Each file should be a research paper in PDF format

## Output

Create or update:
- [`literature-review.md`](../literature-review.md) in the parent folder
- [`references.bib`](../../../content/references.bib) - BibTeX entries for all reviewed articles

## Instructions

For each new PDF article in the `literature/` folder:

1. **Convert PDF to text**
   - Use the `pdftotext` command-line tool to convert `name.pdf` to `name.txt`
   - Store the text file in the same `literature/` folder
   - Name both the .pdf and the .txt according to the format `Year Title.pdf` and `Year Title.txt`.

2. **Extract key information** from the article and add to `literature-review.md`:
   - **Link to Google Scholar query** containg the title of the article.
   - **Summary** (1 sentence): Main thesis or contribution of the article
   - **History of Spaghetti Code**: Describe the relevance to the history of spaghetti code in one short sentence.
   - **Use of the Term "Spaghetti Code":** 
     - Highlight whether the term has been used or not (green check mark or red x).
     - Quote the sentences in the paper that mention the term 'spaghetti code'.
     - If the term 'spaghetti code' has a reference, extract it and add a link to a google scholar query with the title of the reference.
  

3. **Create BibTeX entry** and add to [references.bib](../../../content/references.bib):
   - Generate a proper BibTeX entry for the article
   - Use an appropriate entry type (@article, @inproceedings, @book, etc.)
   - Include essential metadata only: authors, title, year, venue/journal, publisher (for books)
   - **Exclude unnecessary fields**: Do NOT include doi, isbn, url, pages, or other fields not needed for basic citations
   - Make the title clickable by wrapping it in `\href`: `title = {\href{https://scholar.google.com/scholar?q=TITLE}{TITLE}}`
   - Use a citation key format: `firstauthorlastnameYEARkeyword` (e.g., `worku2020exploring`)
   - Check if entry already exists before adding
   - Maintain alphabetical order by citation key

4. **Format** each entry consistently using markdown headers and lists

## Constraints

- Keep summaries concise
- Only process new articles (check if already in literature-review.md)
- Maintain chronological order
- Preserve existing content when updating the file

## Expected Output Format

```markdown
## [Article Title] (Year)

**Authors**: [Author names]

**Google Scholar**: [Link to Google Scholar search with article title]

**Summary**: [1 sentence summary of main contribution]

**History of Spaghetti Code**: [depending on how much the paper contains on this topic]

**Use of the Term "Spaghetti Code":** [depending on how much the paper contains on this topic]

---
```

## Verification

After execution, check that:
- [ ] All PDFs have corresponding .txt files
- [ ] Each article has all required sections in `literature-review.md`
- [ ] Summaries are concise and accurate
- [ ] Links are valid and properly formatted
- [ ] File is valid markdown and renders correctly
- [ ] Each article has a corresponding BibTeX entry in `paper/references.bib`
- [ ] BibTeX entries are properly formatted and valid
- [ ] Title fields are wrapped in `\href{URL}{TITLE}` to make them clickable links to Google Scholar
- [ ] Citation keys follow the naming convention

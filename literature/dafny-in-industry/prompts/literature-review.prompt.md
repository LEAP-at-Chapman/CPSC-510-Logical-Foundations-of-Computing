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

This is a **prompt script** (also known as an AI workflow definition, runbook, or agent instruction file). It contains natural language instructions that guide an AI agent to conduct a systematic literature review.

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
   - Link to Google Scholar query containg the title of the article.
   - **Summary** (2 sentences): Main thesis or contribution of the article
   - **Methodology** (2 sentences): Research methods employed and the kind of data used (e.g., quantitative/qualitative, dataset size, time period)
   - **Results** (1 sentence): Key findings and conclusions
   - **Evaluation** (1-5 scale, 1 sentence justification): Estimate a ranking of the value of this paper compared to other research in the field in terms of importance of the results and the quality of the methodology. Also consider the quality of writing and overall structure.
   - **Resources**: Add links to any of the following if available (ignore if you cannot find links):
     - arXiv LaTeX source (if paper is on arXiv, check for downloadable source files)
     - Code repositories (GitHub, GitLab, etc.)
     - Datasets (data repositories, supplementary materials)
     - Project websites

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

**Summary**: [2 sentence summary of main contribution]

**Methodology**: [2 sentence summary of methods and data]

**Results**: [1 sentence summary of findings]

**Evaluation**: [Rating 1-5]/5 - [1 sentence justification for the rating]

**Resources**:
- LaTeX Source: [arXiv source link if available]
- Code: [link if available]
- Data: [link if available]
- Project: [link if available]

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

## Learning Objectives

Students working with this workflow will learn to:
- Automate repetitive research tasks using AI agents
- Structure prompts for consistent, reproducible outputs
- Version control research workflows
- Document AI-assisted processes for transparency and reproducibility

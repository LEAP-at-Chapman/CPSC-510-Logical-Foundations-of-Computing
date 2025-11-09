# CPSC-510-Logical-Foundations-of-Computing

This is the repository for the course CPSC-510 Logical Foundations of Computing in Fall 2025.

At the end of the course, we will have written a draft of a [book](https://LEAP-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/intro.html) that teaches the logical foundations of computing starting from state of the art software tools.

## Content

**Quick Links**:
- Preliminary [outline](overview.md)
- [Lecture by Lecture](lecture-by-lecture.md)
- [Canvas](https://canvas.chapman.edu/courses/78014)
- [How to create a jupyter book](content/how-to-create-a-jupyter-book.md)

**Resources on Discrete Mathematics**:
- Dr Moshier's book (see Canvas)
- My [Revision Guide: Discrete Mathematics (Logic and Relations)](https://hackmd.io/@alexhkurz/SJ1cc-dDr)
- Chapters 1.1 - 1.3 of the [Open Logic Project](https://builds.openlogicproject.org/)
  
**Free and Open Source Books on Logic**:
- The [Open Logic Project](https://builds.openlogicproject.org/)
- P G Magnus. [An Introduction to Formal Logic](https://www.fecundity.com/logic/index.html) ... [pdf](https://www.fecundity.com/codex/forallx.pdf).
- van Benthem etal. [Logic in Action](https://www.logicinaction.org/) ... [pdf](https://www.logicinaction.org/docs/lia.pdf)
- Stephen G. Simpson. [Mathematical Logic](https://sgslogic.net/t20/notes/logic.pdf). See also his other [Lecture Notes](https://sgslogic.net/t20/notes/).

**Blogs, Videos, etc**:
- Hillel Wayne: [Logical Duals in Software Engineering](https://buttondown.com/hillelwayne/archive/logical-duals-in-software-engineering/)

## Jupyter Book

### Setup, Installation, Etc

**Quick Setup** (recommended):
```bash
./setup.sh
```

**Manual Setup**:
1. **Install dependencies**:
   ```bash
   pip install -r requirements.txt
   # OR using pip with pyproject.toml:
   pip install -e .
   ```

2. **Build the book**:
   ```bash
   jupyter-book build .
   ```

3. **Deploy to GitHub Pages**:
   ```bash
   ghp-import -n -p -f _build/html
   ```

4. **View the book**: [https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/intro.html](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/content/intro.html)

**Development**:
- For development with Jupyter notebooks: `pip install -e ".[dev]"`
- Interactive examples: [Z3 Examples](z3/z3-examples.ipynb)

## Resources on Jupyter Books
- [jupyterbook.org](https://jupyterbook.org/stable/)
- Video [Jupyter Book 101](https://www.youtube.com/watch?v=lZ2FHTkyaMU) by Chris Holdgraf
- Video Course: **Build a Jupyter Book with The Turing Way**
  - Module 2.1: [Introduction to the Turing Way](https://www.youtube.com/watch?v=JyNhPfcBxTg&list=PLBxcQEfGu3Dmdo6oKg6o9V7Q_e7WSX-vu&index=2)
  - Module 2.2: [Overview of features](https://www.youtube.com/watch?v=PmxZywVwhP8&list=PLBxcQEfGu3Dmdo6oKg6o9V7Q_e7WSX-vu&index=3)
  - Module 5: [NyST, Jupyter Notebooks in Jupyter Books](https://www.youtube.com/watch?v=K2LgwSbZH_Q&list=PLBxcQEfGu3Dmdo6oKg6o9V7Q_e7WSX-vu&index=6)
  
## Examples of Online Books
- [Computational and Inferential Thinking: The Foundations of Data Science](https://inferentialthinking.com/chapters/intro.html)
- [Intermediate Quantitative Economics with Python](https://python.quantecon.org/intro.html)
- [The Turing Way](https://book.the-turing-way.org/)
- [SciKit Learn](https://inria.github.io/scikit-learn-mooc/)
- [Visualization Curriculum](https://idl.uw.edu/visualization-curriculum/intro.html)
- [Geographic Data Science with Python](https://geographicdata.science/book/intro.html)

The Lean Community has  been very active writing online books:
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Logic and Proof](https://leanprover-community.github.io/logic_and_proof/)
- [The Mechanics of Proof](https://hrmacbeth.github.io/math2001/)


# CPSC-510-Logical-Foundations-of-Computing

This is the repository for the course CPSC-510 Logical Foundations of Computing. 

At the end of the course, we will have written a draft of a [book](https://LEAP-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/intro.html) that teaches the logical foundations of computing starting from state of the art software tools.

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

**Setup and Installation**:

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

4. **View the book**: [https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/intro.html](https://leap-at-chapman.github.io/CPSC-510-Logical-Foundations-of-Computing/intro.html)

**Development**:
- For development with Jupyter notebooks: `pip install -e ".[dev]"`
- Interactive examples: [Z3 Examples](z3/z3-examples.ipynb)

## Context

- The terminal log (lines 855–1032) shows `jupyter-book build .` invoking Sphinx with `myst-nb` and `nbclient` to execute notebooks.
- Various non-fatal warnings appear (docutils citation HTML, header-level warnings, tableofcontents with no descendants).
- The fatal error arises when executing `content/notebooks.ipynb` (and also the template `notebooks.ipynb` in the installed `jupyter_book` package).
- `nbclient` reports `DeadKernelError: Kernel died` during `async_execute_cell`, which propagates up and is wrapped by Jupyter Book as a `RuntimeError` that stops the build.



# How to Create a Jupyter Book


Starting from [Create your first book](https://jupyterbook.org/en/stable/start/your-first-book.html) the following steps were taken.

### Basics

After creating this repo, cloning it (assume it is called `root` locally), I run the following from the commandline in the folder containing `root`.

```
pip install -U jupyter-book
jupyter-book create book
mv book/* root
cd root
jupyter-book build .
```

The book can now be opened in a browser by opening the file `_build/html/index.html`. On a mac, simply run `open _build/html/index.html`

Following [Math and equations](https://jupyterbook.org/en/stable/content/math.html#math-and-equations) add to `_config.yml`

```
parse:
  myst_enable_extensions:
    # don't forget to list any other extensions you want enabled,
    # including those that are enabled by default!
    - amsmath
    - dollarmath
```

Adapt `_config.yml` and `_toc.yml`. Add your own files. Go through several iterations of 

```
jupyter-book build .
open _build/html/index.html
```

Before committing and pushing to git, I downloaded a `.gitignore`:

```
curl https://raw.githubusercontent.com/executablebooks/jupyter-book/master/.gitignore > .gitignore
```

One question I have is how to adjust the size of screenshots and other images.

### Publish on the web

Following [Publish your book online](https://jupyterbook.org/en/stable/start/publish.html) install `ghp-import` with
`pip install ghp-import` and then publish the book by running

```
ghp-import -n -p -f _build/html
```

This makes the [book available online](https://alexhkurz.github.io/coalgebraic-logic-jupyter). It also keeps the source files in the `main`-branch separate from the html-files in `_build` in the `gh-pages` branch.

### create a pdf

Following [Build a PDF](https://jupyterbook.org/en/stable/advanced/pdf.html), I first run `pip install pyppeteer` to use with  `jb build . --builder pdfhtml` but this produced the error `pyppeteer.errors.TimeoutError: Navigation Timeout Exceeded: 30000 ms exceeded.` The following did produce a pdf.

```
jb build . --builder pdflatex
```

This would need some work by hand to have a nice layout. Maybe worth the effort once a book reaches a state where a book can be considered more or less finished ... 
### important commands

If, for example, the table of contents in the left-hand pane behaves in a strange way, clean out `_build`:

```
jupyter-book build .
open _build/html/index.html
ghp-import -n -p -f _build/html
jupyter-book clean .
```

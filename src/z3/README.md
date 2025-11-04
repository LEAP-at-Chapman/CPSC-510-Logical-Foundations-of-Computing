# Z3 Examples

This folder collects examples of Z3 programs.

## Akari

akari.py uses a hardcoded grid of the unsolved puzzle, and solves it via the Python z3 library.

The output will be whether the puzzle is satisfiable or not, and then a text representation of the solved puzzle, similar to the minizinc solution.

Namely, L represents a lamp, B represents a solid black block, 1-4 represents a numbered black block with the adjancent number of lamps, and * is a white block that is lit up.

```
sat
0 * * * * L 1
* 1 L * 1 B *
* 0 * * L * *
* * * * * L *
L * * * * 2 L
* B 1 L * B *
0 * * * * L B
```

# Constraint Programming and MiniZinc

To download MiniZinc go to https://www.minizinc.org/ 

---

We have seen SAT solvers such as MiniSat and Logic Programming in Prolog. One big advantage both have is that at least on small examples one can understand precisely how the algorithms for SAT-solving and logic programming work. We have seen this in some detail when we used the debugging tool `trace` of `swipl` to trace the execution of the `eight-queens` in Prolog.

But when it comes to solving mathematical constraints rather than logical ones, both SAT-solving and (pure) logic programming have their disadvantages. SAT requires one to encode mathematical constraints in logical ones. Prolog, while more declarative, struggles with efficient arithmetic. Moreover, while recursion plus backtracking makes Prolog Turing complete, this often leads to exponential solutions that are too slow in practice. 

[**Constraint Programming**](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Constraint+Programming&btnG=) bridges this gap. Here is how (Rossi etal 2008) describe constraint programming:

![image](https://hackmd.io/_uploads/B1REaSYjex.png)

[**MiniZinc**](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=minizinc&btnG=) is a standard modelling language for constraint programming (CP). Via the low-level solver-input language FlatZinc, MiniZinc can act as an interface to a wide range of specialized solvers, briding the gap from a declarative language for describing problems to specialized solvers that exploit finite domain (FD) and linear programming (LP) techniques. (Nethercote etal 2007) describe MiniZinc as follows.

![image](https://hackmd.io/_uploads/rkkte8Foge.png)

To compare constraint programming in MiniZinc with SAT-solving in MiniSat and logic programming in Prolog, we will look in some detail at the example of Sudoku.

MiniZinc Tutorial https://docs.minizinc.dev/en/stable/part_2_tutorial.html 

## The Sudoku Example

We already have seen Sudoku in SAT. Below I will compare Sudoku in MiniZinc and Sudoku in Prolog.

### In MiniZinc

Save the following as sudoku.mzn

```
include "globals.mzn";

% Parameters (to be defined in .dzn file)
int: n;  % Size of the grid (typically 9)
int: box_size;  % Size of each box (typically 3 for 9x9, 2 for 4x4)
array[1..n, 1..n] of int: initial;  % Initial clues (0 = empty cell)

% Decision variables
array[1..n, 1..n] of var 1..n: grid;

% Fix initial clues
constraint forall(i in 1..n, j in 1..n) (
    if initial[i,j] != 0 then grid[i,j] = initial[i,j] else true endif
);

% Row constraints
constraint forall(i in 1..n) (
    all_different([grid[i,j] | j in 1..n])
);

% Column constraints  
constraint forall(j in 1..n) (
    all_different([grid[i,j] | i in 1..n])
);

% Box constraints  
constraint forall(box_row in 0..(n div box_size - 1), box_col in 0..(n div box_size - 1)) (
    all_different([grid[i,j] | 
                   i in box_row*box_size+1..box_row*box_size+box_size,
                   j in box_col*box_size+1..box_col*box_size+box_size])
);

solve satisfy;

output [
    if j = 1 then "\n" else " " endif ++
    show(grid[i,j])
    | i in 1..n, j in 1..n
] ++ ["\n"];
```

and this sudoku as `sudoku_hard.dzn`.

To run it, on macos, I first installed the cli interface of MiniZinc with `brew install minizinc` and then run
```
minizinc --solver org.minizinc.mip.coin-bc sudoku.mzn sudoku_hard.dzn
```
or also 
```
time minizinc --solver org.minizinc.mip.coin-bc sudoku.mzn sudoku_hard.dzn
```
which gives me
```
5 3 4 6 7 8 9 1 2
6 7 2 1 9 5 3 4 8
1 9 8 3 4 2 5 6 7
8 5 9 7 6 1 4 2 3
4 2 6 8 5 3 7 9 1
7 1 3 9 2 4 8 5 6
9 6 1 5 3 7 2 8 4
2 8 7 4 1 9 6 3 5
3 4 5 2 8 6 1 7 9
----------
0.17s user 0.08s system 80% cpu 0.312 total
```

### In Prolog

The Prolog program is available at ...

```
swipl -f sudoku.pl
?- test_4x4.
?- test_9x9_easy.
?- test_9x9_hard.
```

The main point I want to make here is that while this program solves a 4x4 and an easy 9x9, it doesnt solve the harder 9x9 in a comparable time. 

What do you think is the reason for this?

## What MiniZinc Cannot Do

While constraint programming as a paradigm extends logic programming by adding finite domain variables, constraint propagation algorithms, and global constraints (beyond the unification and resolution of pure logic programming), MiniZinc itself is a specialized modeling language targeting mathematical constraint solvers - including CP solvers (like Gecode), SAT solvers, integer programming solvers (like CPLEX), and SMT solvers - rather than general logic programming engines.

Here are some examples of what MiniZinc cannot do (CHECK): recursion, reasoning with data built from function symbols, meta-programming, pattern matching on variable sized lists.



## References

- Rossi, F., Van Beek, P., & Walsh, T. (2008). [Constraint programming](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=Constraint+Programming&btnG=). Foundations of Artificial Intelligence, 3, 181-211.
- Nethercote, N., Stuckey, P. J., Becket, R., Brand, S., Duck, G. J., & Tack, G. (2007, September). [MiniZinc: Towards a standard CP modelling language](https://scholar.google.com/scholar?hl=en&as_sdt=0%2C5&q=minizinc&btnG=). In International conference on principles and practice of constraint programming (pp. 529-543). Berlin, Heidelberg: Springer Berlin Heidelberg.
- Stuckey, P. J., Feydy, T., Schutt, A., Tack, G., & Fischer, J. (2014). The minizinc challenge 2008–2013. Ai Magazine, 35(2), 55-60.
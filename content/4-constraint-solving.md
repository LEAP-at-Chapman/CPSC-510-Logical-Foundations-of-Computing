# Constraint Programming with MiniZinc

## Idea
Constraint programming is the idea of using constraint solver tools to solve problems. These problems are called constraint satisfaction problems (CSPs) where you provide a set of variables and a set of constraints on those variables, and the constraint solver finds a assignment of values to the variables that satisfies all the constraints. In this chapter we will focus on constraint programming using MiniZinc.

## Basic Theory
1) Start in MiniZinc by defining parameters about your domain (width, height, number of colors, etc.)
2) Define your decision variables and their domains. This will be treated as the base case of the overall recursive logic.
3) Define your constraints using the `constraint` syntax, along with a loop to enforce the constraints on all the variables.
4) Use the `solve satisfy` command to find a solution.
5) Output the solution parameters.

Example:
```{mzn}
include "globals.mzn";

% Parameters
int: n

% Decision variables
array[1..10, 1..10] of var 1..10: grid


% Constraints
constraint forall(i in 1..n, j in 1..n) (
  if ... then _value1_ else _value2_ endif
);

% Solution
solve satisfy;

output [
    if j = 1 then "\n" else " " endif ++
    show(grid[i,j])
    | i in 1..n, j in 1..n
] ++ ["\n"];
```

## How to approach writing the recursive logic of some CSP in MiniZinc syntax and theory.

1) Start at the base case and work backwards
2) Identify the recursive structure by trying to break the logic down into smaller subproblems
3) Define the recursion functions or predicates while making sure each recursive call brings you closer to the base case
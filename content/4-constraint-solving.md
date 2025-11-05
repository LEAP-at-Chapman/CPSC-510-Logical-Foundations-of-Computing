# Constraint Programming with MiniZinc

## Idea
Constraint programming (CP) is a paradigm for identifying feasible solutions from a very large set of candidates by modeling problems in terms of arbitrary constraints. These problems are called constraint satisfaction problems (CSPs) where you provide:
- A set of **decision variables** with their domains
- A set of **constraints** that must be satisfied
- Optionally, an **objective function** to optimize

The constraint solver finds an assignment of values to the variables that satisfies all constraints. CP is based on **feasibility** (finding a feasible solution) rather than optimization, focusing on the constraints and variables rather than the objective function.

### Installation

```bash
brew install minizinc
```

### Key Characteristics
- **Feasibility-focused**: CP emphasizes finding solutions that satisfy all constraints, not necessarily optimal ones
- **Declarative**: You describe *what* constraints must hold, not *how* to find the solution
- **Powerful for scheduling**: Particularly effective for problems like employee scheduling, job shop scheduling, and resource allocation
- **Handles heterogeneous constraints**: Can combine different types of constraints (arithmetic, logical, global constraints)

In this chapter we will focus on constraint programming using MiniZinc, a high-level modeling language for constraint satisfaction and optimization problems.

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

## Working Example: N-Queens in MiniZinc

A minimal, runnable model is included in this repo at `src/minizinc/nqueens/nqueens.mzn`. You can run it directly without any `.dzn` file.

```{mzn}
include "globals.mzn";

% N-Queens: place n queens on an n x n board so none attack each other
int: n = 8; % override with: -D n=10
set of int: Q = 1..n;

% q[i] is the column (1..n) of the queen in row i
array[Q] of var Q: q;

% 1) No two queens in the same column
constraint all_different(q);

% 2) No two queens on the same diagonal
constraint forall(i, j in Q where i < j) (
  abs(q[i] - q[j]) != j - i
);

solve satisfy;

% Render a board with Q for a queen and . for empty
output [
  if j = 1 then "\n" else " " endif ++
  if q[i] = j then "Q" else "." endif
  | i in Q, j in Q
] ++ ["\n", "Positions: ", show(q), "\n"];
```

Run:

```
minizinc src/minizinc/nqueens/nqueens.mzn
minizinc -D n=12 src/minizinc/nqueens/nqueens.mzn
# If needed, specify a solver explicitly (e.g., Gecode):
minizinc --solver Gecode src/minizinc/nqueens/nqueens.mzn
```

Step-by-step how it works:
- Parameters and sets: `n` and the index set `Q = 1..n`.
- Decision variables: `q[i]` gives the column of the queen in row `i`.
- Constraints:
  - Columns: `all_different(q)` ensures all queens use different columns.
  - Diagonals: for any rows `i<j`, if `abs(q[i]-q[j]) = j-i` they would share a diagonal; we forbid that by requiring `!=`.
- Solve: `solve satisfy;` asks for any placement satisfying all constraints.
- Output: pretty-prints a board and also the vector of positions.

What the solver does:
- Propagates the global constraint `all_different` and the diagonal arithmetic constraints.
- Systematically searches (with propagation pruning) until a model is found.

## How to approach writing the recursive logic of some CSP in MiniZinc syntax and theory

1) Start at the base case and work backwards
2) Identify the recursive structure by trying to break the logic down into smaller subproblems
3) Define the recursion functions or predicates while making sure each recursive call brings you closer to the base case

## Connecting Z3 and MiniZinc Concepts

Both Z3 and MiniZinc are declarative constraint solving tools, but with different focuses:

| Aspect | Z3 | MiniZinc |
|--------|-----|----------|
| **Primary Use** | SMT solving, theorem proving | Constraint satisfaction, optimization |
| **Theory** | SMT (Satisfiability Modulo Theories) | CP (Constraint Programming) |
| **Strengths** | Logical formulas, bit-vectors, arrays | Scheduling, combinatorial optimization |
| **Approach** | SAT + theory solvers | Propagation + search |
| **Syntax** | Python/C++ API or SMT-LIB | Declarative modeling language |

**Common Ground**:
- Both use declarative problem specification
- Both support integer and boolean variables
- Both can express logical constraints
- Both search for satisfying assignments

**When to use which**:
- Use **Z3** for: verification, program analysis, logical reasoning
- Use **MiniZinc** for: scheduling, planning, resource allocation

## Example Applications

### Employee Scheduling
A classic CP problem: A company runs three 8-hour shifts per day and assigns three of its four employees to different shifts each day, while giving the fourth the day off. Even with just 4 employees, there are 4! = 24 possible assignments per day, leading to 24^7 ≈ 4.5 billion possible weekly schedules. CP efficiently narrows this down by tracking which solutions remain feasible as constraints are added (e.g., minimum days worked per employee).

### Classic CP Problems
- **N-Queens Problem**: Place N queens on an N×N chessboard so no two queens attack each other
- **Cryptarithmetic Puzzles**: Assign digits to letters to make arithmetic equations valid
- **Job Shop Scheduling**: Assign jobs to machines while respecting precedence and resource constraints

## Resources

### MiniZinc
- [MiniZinc Official Documentation](https://www.minizinc.org/doc-latest/en/index.html)
- [MiniZinc Tutorial](https://www.minizinc.org/doc-latest/en/part_2_tutorial.html)
- [MiniZinc Handbook](https://www.minizinc.org/handbook.html)

### Google OR-Tools (CP-SAT)
- [Constraint Optimization Overview](https://developers.google.com/optimization/cp)
- [CP-SAT Solver Documentation](https://developers.google.com/optimization/cp/cp_solver)
- [Employee Scheduling Example](https://developers.google.com/optimization/scheduling/employee_scheduling)
- [Job Shop Problem Example](https://developers.google.com/optimization/scheduling/job_shop)

### General CP Resources
- [Constraint Programming (Wikipedia)](https://en.wikipedia.org/wiki/Constraint_programming)
- CP Community: Scientific journals, conferences, and active research in planning and scheduling

### Z3 and SMT
- [Z3 Theorem Prover](https://github.com/Z3Prover/z3)
- [Z3 Guide](https://z3prover.github.io/papers/programmingz3.html)

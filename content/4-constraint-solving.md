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

On Windows (Git Bash), if MiniZinc is installed under your user profile, add the CLI to PATH:

```bash
export PATH="$HOME/AppData/Local/Programs/MiniZinc:$PATH"
minizinc --version
```

### Key Characteristics

- **Feasibility-focused**: CP emphasizes finding solutions that satisfy all constraints, not necessarily optimal ones
- **Declarative**: You describe _what_ constraints must hold, not _how_ to find the solution
- **Powerful for scheduling**: Particularly effective for problems like employee scheduling, job shop scheduling, and resource allocation
- **Handles heterogeneous constraints**: Can combine different types of constraints (arithmetic, logical, global constraints)

In this chapter we will focus on constraint programming using MiniZinc, a high-level modeling language for constraint satisfaction and optimization problems.

## Basic Theory

1. Start in MiniZinc by defining parameters about your domain (width, height, number of colors, etc.)
2. Define your decision variables and their domains. This will be treated as the base case of the overall recursive logic.
3. Define your constraints using the `constraint` syntax, along with a loop to enforce the constraints on all the variables.
4. Use the `solve satisfy` command to find a solution.
5. Output the solution parameters.

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
  if fix(q[i]) = j then "Q" else "." endif
  | i in Q, j in Q
] ++ ["\n", "Positions: ", show(q), "\n"];
```

Run:

```
minizinc src/minizinc/nqueens/nqueens.mzn
minizinc -D n=12 src/minizinc/nqueens/nqueens.mzn
# If needed, specify a solver explicitly (coin-bc):
minizinc -s coin-bc src/minizinc/nqueens/nqueens.mzn
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

1. Start at the base case and work backwards
2. Identify the recursive structure by trying to break the logic down into smaller subproblems
3. Define the recursion functions or predicates while making sure each recursive call brings you closer to the base case

## Connecting Z3 and MiniZinc Concepts

Briefly: MiniZinc is a high-level modeling language for constraint satisfaction and optimization with rich global constraints and multiple backend solvers; Z3 is an SMT solver aimed at logical theories and verification. If you’re building schedules, allocations, or routing, prefer MiniZinc; for program verification or bit-vector logic, prefer Z3.

## Example Applications

### Employee Scheduling

A classic CP problem: A company runs three 8-hour shifts per day and assigns three of its four employees to different shifts each day, while giving the fourth the day off. Even with just 4 employees, there are 4! = 24 possible assignments per day, leading to 24^7 ≈ 4.5 billion possible weekly schedules. CP efficiently narrows this down by tracking which solutions remain feasible as constraints are added (e.g., minimum days worked per employee).

### Classic CP Problems

- **N-Queens Problem**: Place N queens on an N×N chessboard so no two queens attack each other
- **Cryptarithmetic Puzzles**: Assign digits to letters to make arithmetic equations valid
- **Job Shop Scheduling**: Assign jobs to machines while respecting precedence and resource constraints

## Practical Business Example: Employee Shift Scheduling (MiniZinc)

A small, runnable scheduling model is included at `src/minizinc/employee_scheduling/shift_scheduling.mzn`. It assigns exactly one employee to each shift per day (Morning, Evening, Night), with fairness caps on how many shifts an employee can work in a week.

Run:

```
minizinc -s coin-bc src/minizinc/employee_scheduling/shift_scheduling.mzn 
```

How it’s modeled:

- **Parameters**: number of employees `E`, days `D`, shifts per day `S`, a coverage matrix `demand[d,s]`, and `max_shifts_per_employee`.
- **Decision variables**: `x[e,d,s] ∈ {0,1}` indicates whether employee `e` works shift `s` on day `d`.
- **Constraints**:
  - Coverage: for each day/shift, `sum_e x[e,d,s] = demand[d,s]`.
  - Per-day load: for each employee/day, `sum_s x[e,d,*] ≤ 1` (no double-booking).
  - Weekly fairness: for each employee, `sum_{d,s} x[e,*,*] ≤ max_shifts_per_employee`.
- **Solve**: `solve satisfy;` requests any feasible plan meeting the coverage and fairness constraints.
- **Output**: a weekly roster printed by day and shift, listing assigned employees.

How to think about it:

- Start with the business rules you cannot violate (coverage and no double-booking).
- Add fairness/balance rules to reflect policy (caps, min/max shifts).
- Keep data (e.g., `demand`) separate from decision variables, so you can scale it up later or drive it from external inputs.
- Prefer global and aggregate constraints (`sum`, `all_different`, etc.)—propagation will prune the search effectively.

## Translating this into a real-world written script

In modern days, instead of directly running MiniZinc, we can incorporate MiniZinc directly in Python to help us solve CP problems, without external files. So to utilize the quick solver MiniZinc, we can use the `minizinc` Python library to easily create models and solve them with inputs, using only python. 

Step 1: Run `pip install minizinc` to install the Python library.

Step 2: Run `python3 src/minizinc/employee_scheduling/shift_scheduling.py` to run the translated, real-world example.

```{python}
import minizinc

MODEL = r"""
include "globals.mzn";

int: E;
int: D;
int: S;

set of int: Employees = 1..E;
set of int: Days = 1..D;
set of int: Shifts = 1..S;

array[Shifts] of string: shift_name;
array[Days] of string: day_name;
array[Employees] of string: employee_name;

array[Days, Shifts] of int: demand;
int: max_shifts_per_employee;

array[Employees, Days, Shifts] of var 0..1: x;

constraint forall(d in Days, s in Shifts) (
  sum(e in Employees)(x[e,d,s]) = demand[d,s]
);

constraint forall(e in Employees, d in Days) (
  sum(s in Shifts)(x[e,d,s]) <= 1
);

constraint forall(e in Employees) (
  sum(d in Days, s in Shifts)(x[e,d,s]) <= max_shifts_per_employee
);

solve satisfy;

output [
  "Weekly Roster\n"
] ++
[
  day_name[d] ++ ":\n" ++
  concat([ "  " ++ shift_name[s] ++ ": " ++
           concat([ if fix(x[e,d,s]) = 1 then employee_name[e] ++ " " else "" endif
                 | e in Employees ]) ++ "\n"
         | s in Shifts ]) ++
  (if d < D then "\n" else "" endif)
  | d in Days
];
"""

# ------------ Python side ------------
model = minizinc.Model()
model.add_string(MODEL)

solver = minizinc.Solver.lookup("coin-bc")

instance = minizinc.Instance(solver, model)

# parameters
E, D, S = 5, 7, 3
instance["E"] = E
instance["D"] = D
instance["S"] = S

instance["shift_name"] = ["Morning", "Evening", "Night"]
instance["day_name"]   = ["Mon","Tue","Wed","Thu","Fri","Sat","Sun"]
instance["employee_name"] = ["Matt","Jack","Jake","Wayne","Alex"]

instance["demand"] = [
    [1,1,1],
    [1,1,1],
    [1,1,1],
    [1,1,1],
    [1,1,1],
    [1,1,1],
    [1,1,1],
]

instance["max_shifts_per_employee"] = 5

result = instance.solve()
print(result)
```

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

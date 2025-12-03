# Constraint Programming with MiniZinc

## Idea

Constraint programming (CP) is a paradigm for identifying feasible solutions from a very large set of candidates by modeling problems in terms of arbitrary constraints. These problems are called constraint satisfaction problems (CSPs) where you provide:

* A set of **decision variables** with their domains
* A set of **constraints** that must be satisfied
* Optionally, an **objective function** to optimize

The constraint solver finds an assignment of values to the variables that satisfies all constraints. CP is based on **feasibility** (finding a feasible solution) rather than optimization, focusing on the constraints and variables rather than the objective function (Rossi, Van Beek, and Walsh, 2006).

### Installation

```bash
brew install minizinc
```

```bash
minizinc --version
```

### Key Characteristics

* **Feasibility-focused**: CP emphasizes finding solutions that satisfy all constraints, not necessarily optimal ones
* **Declarative**: You describe *what* constraints must hold, not *how* to find the solution
* **Powerful for scheduling**: Particularly effective for problems like employee scheduling, job shop scheduling, and resource allocation
* **Handles heterogeneous constraints**: Can combine different types of constraints (arithmetic, logical, global constraints)

These characteristics follow the standard MiniZinc modeling approach (Nethercote et al., 2007).

In this chapter we will focus on constraint programming using MiniZinc, a high-level modeling language for constraint satisfaction and optimization problems.

## Basic Theory

1. Start in MiniZinc by defining parameters about your domain (width, height, number of colors, etc.)
2. Define your decision variables and their domains. This will be treated as the base case of the overall recursive logic.
3. Define your constraints using the `constraint` syntax, along with a loop to enforce the constraints on all the variables.
4. Use the `solve satisfy` command to find a solution.
5. Output the solution parameters.

These steps follow the modeling flow presented in the MiniZinc tutorial (Nethercote et al., 2007).

Example:

```mzn
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

```mzn
include "globals.mzn";

int: n = 8;
set of int: Q = 1..n;

array[Q] of var Q: q;

constraint all_different(q);

constraint forall(i, j in Q where i < j) (
  abs(q[i] - q[j]) != j - i
);

solve satisfy;

output [
  if j = 1 then "\n" else " " endif ++
  if fix(q[i]) = j then "Q" else "." endif
  | i in Q, j in Q
] ++ ["\n", "Positions: ", show(q), "\n"];
```

This implementation mirrors the canonical N-Queens problem description in survey work (Bell and Stevens, 2009).

## How to approach writing the recursive logic of some CSP in MiniZinc syntax and theory

1. Start at the base case and work backwards
2. Identify the recursive structure by breaking the logic into smaller subproblems
3. Define recursion predicates ensuring each call moves closer to the base case

## Connecting Z3 and MiniZinc Concepts

Briefly: MiniZinc is a high-level modeling language for constraint satisfaction and optimization with rich global constraints and multiple backend solvers; Z3 is an SMT solver aimed at logical theories and verification. If you’re building schedules, allocations, or routing, prefer MiniZinc; for program verification or bit-vector logic, prefer Z3 (de Moura and Bjørner, 2008).

## Example Applications

### Employee Scheduling

A classic CP problem: A company runs three 8-hour shifts per day and assigns three of its four employees to different shifts each day, while giving the fourth the day off. Even with just 4 employees, there are 24 possible assignments per day, leading to 24^7 ≈ 4.5 billion possible weekly schedules (Perron and Furnon, 2019).

### Classic CP Problems

* **N-Queens Problem**
* **Cryptarithmetic Puzzles**
* **Job Shop Scheduling**

These examples correspond to the standard CP problem categories in the literature (Rossi, Van Beek, and Walsh, 2006; Perron and Furnon, 2019).

## Practical Business Example: Employee Shift Scheduling (MiniZinc)

A runnable scheduling model lives at:
`src/minizinc/employee_scheduling/shift_scheduling.mzn`.

This modeling structure follows both MiniZinc and OR-Tools scheduling examples (Nethercote et al., 2007; Perron and Furnon, 2019).

Run:

```
minizinc -s coin-bc src/minizinc/employee_scheduling/shift_scheduling.mzn
```

How it’s modeled:

* **Parameters**: number of employees `E`, days `D`, shifts `S`, demand matrix, and fairness caps
* **Decision variables**: binary variable `x[e,d,s]`
* **Constraints**:

  * Coverage
  * No double-booking
  * Weekly fairness
* **Solve**: `solve satisfy`
* **Output**: human-readable roster

MiniZinc’s aggregate and global constraints make CP extremely effective for scheduling (Nethercote et al., 2007).

```mzn

% Employee Shift Scheduling - Practical Business Example
% Goal: Assign exactly one employee to each shift per day, with fairness caps.
% Run:
%   minizinc -s --solver coin-bc shift_scheduling_.mzn

%

include "globals.mzn";

% Parameters (override via -D as needed)
int: E = 5;                      % number of employees
int: D = 7;                      % number of days (e.g., a week)
int: S = 3;                      % shifts per day (e.g., Morning, Evening, Night)
set of int: Employees = 1..E;
set of int: Days = 1..D;
set of int: Shifts = 1..S;

% Optional: Pretty names for output
array[Shifts] of string: shift_name = ["Morning","Evening","Night"];
array[Days] of string: day_name = ["Mon","Tue","Wed","Thu","Fri","Sat","Sun"];
array[Employees] of string: employee_name =
  if E = 5 then [" Matt","Jack","Jake","Wayne","Alex"] else
  [ "Emp" ++ show(i) | i in Employees ]
  endif;

% Demand: how many employees needed per (day, shift)
array[Days, Shifts] of int: demand = [|
  1, 1, 1  % Mon
|
  1, 1, 1  % Tue
|
  1, 1, 1  % Wed
|
  1, 1, 1  % Thu
|
  1, 1, 1  % Fri
|
  1, 1, 1  % Sat
|
  1, 1, 1  % Sun
|];

% Reasonable default fairness cap
int: max_shifts_per_employee = 5;

% Decision variables: x[e,d,s] = 1 if employee e works shift s on day d
array[Employees, Days, Shifts] of var 0..1: x;

% 1) Each shift's coverage must be met exactly
constraint forall(d in Days, s in Shifts) (
  sum(e in Employees)(x[e,d,s]) = demand[d,s]
);

% 2) Each employee works at most one shift per day
constraint forall(e in Employees, d in Days) (
  sum(s in Shifts)(x[e,d,s]) <= 1
);

% 3) Weekly cap for fairness/load
constraint forall(e in Employees) (
  sum(d in Days, s in Shifts)(x[e,d,s]) <= max_shifts_per_employee
);

% Solve for any feasible assignment
solve satisfy;

% Output: readable weekly roster
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

```

## Translating this into a real-world written script

With the Python MiniZinc API, you can embed a model as a string and feed parameters directly:

```python
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

This pipeline follows the modeling and solver interface described in MiniZinc's core language design (Nethercote et al., 2007).

---

## References

Nethercote et al. (2007)
[MiniZinc: Towards a Standard CP Modelling Language](https://scholar.google.com/scholar?q=MiniZinc%3A+Towards+a+Standard+CP+Modelling+Language), CP 2007

Perron and Furnon (2019)
[OR-Tools: Google Optimization Tools](https://scholar.google.com/scholar?q=OR-Tools%3A+Google+Optimization+Tools), Google Research

Rossi, Van Beek, and Walsh (2006)
[Handbook of Constraint Programming](https://scholar.google.com/scholar?q=Handbook+of+Constraint+Programming+Rossi+Van+Beek+Walsh), Elsevier

de Moura and Bjørner (2008)
[Z3: An Efficient SMT Solver](https://scholar.google.com/scholar?q=Z3%3A+An+Efficient+SMT+Solver), TACAS

Bell and Stevens (2009)
[A Survey of the N-Queens Problem](https://scholar.google.com/scholar?q=A+Survey+of+the+N-Queens+Problem+Bell+Stevens), Discrete Mathematics

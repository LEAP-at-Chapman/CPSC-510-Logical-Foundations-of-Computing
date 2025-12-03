# Constraint Programming with MiniZinc

## Idea

Constraint programming (CP) is a paradigm for identifying feasible solutions from a very large set of candidates by modeling problems in terms of arbitrary constraints. These problems are called constraint satisfaction problems (CSPs) where you provide:

* A set of **decision variables** with their domains
* A set of **constraints** that must be satisfied
* Optionally, an **objective function** to optimize

The constraint solver finds an assignment of values to the variables that satisfies all constraints. CP is based on **feasibility** (finding a feasible solution) rather than optimization, focusing on the constraints and variables rather than the objective function (Rossi, Van Beek, and Walsh, 2006).

### Learning Goals

By the end of this chapter, you will be able to:
1.  **Model logic puzzles and scheduling problems** using high-level constraints in MiniZinc.
2.  **Understand the "Rosetta Stone" advantage:** Write one model that can be solved by multiple backend technologies (CP, MIP, SMT) without rewriting code.
3.  **Distinguish when to use MiniZinc** versus embedded libraries like Python's OR-Tools for your own projects.

### Installation

```bash
brew install minizinc
```

```bash
minizinc --version
```

### Key Characteristics

Constraint programming systems generally share several defining features that distinguish them from other approaches:

* **Feasibility-focused**: CP emphasizes finding solutions that satisfy all constraints, not necessarily optimal ones
* **Declarative**: You describe *what* constraints must hold, not *how* to find the solution
* **Powerful for scheduling**: Particularly effective for problems like employee scheduling, job shop scheduling, and resource allocation
* **Handles heterogeneous constraints**: Can combine different types of constraints (arithmetic, logical, global constraints)

These characteristics follow the standard MiniZinc modeling approach (Nethercote et al., 2007).

**Why this matters:** Instead of writing imperative loops to *find* a solution, you simply declare the properties a valid solution must have. This shift in thinking allows you to solve much harder problems with much less code.

In this chapter we will focus on constraint programming using MiniZinc, a high-level modeling language for constraint satisfaction and optimization problems.

## Basic Theory

Modeling a problem in MiniZinc typically follows a structured process:

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

To see these concepts in action, let's look at the "Hello World" of constraint programming: placing N queens on a chessboard so that no two queens attack each other.

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

```{button-link} ../minizinc/nqueens.mzn
:color: primary
:shadow:
:target: _blank

Download nqueens.mzn
```

This implementation mirrors the canonical N-Queens problem description in survey work (Bell and Stevens, 2009).

## Recursive Logic in MiniZinc

Now that you've seen a flat model, how do you handle more complex logic? Building a model often feels like defining a recursive function.

When approaching the recursive logic of a CSP in MiniZinc, consider these steps:

1. Start at the base case and work backwards
2. Identify the recursive structure by breaking the logic into smaller subproblems
3. Define recursion predicates ensuring each call moves closer to the base case

## Connecting Z3 and MiniZinc Concepts

MiniZinc is a high-level modeling language for constraint satisfaction and optimization with rich global constraints and multiple backend solvers; Z3 is an SMT solver aimed at logical theories and verification. If you’re building schedules, allocations, or routing, prefer MiniZinc; for program verification or bit-vector logic, prefer Z3 (de Moura and Bjørner, 2008).

## Practicality: MiniZinc vs. Embedded Libraries

So, why would you choose a standalone modeling language like MiniZinc over simply importing a library like OR-Tools directly into your Python or C++ project? In my experience, the main reason is the level of abstraction. MiniZinc lets you focus purely on *what* the rules are, without forcing you to commit to *how* they will be solved.

### Solver Independence

MiniZinc acts as a sort of "Rosetta Stone" for optimization (Nethercote et al., 2007). You can write your model once and then compile it to target completely different technologies—Constraint Programming (CP), Mixed Integer Programming (MIP), or even SMT—without changing a single line of your code.

If you were working in Python, you’d typically have to lock yourself into a specific solver's API (like choosing the CP-SAT solver in OR-Tools versus a MIP solver like Gurobi). If you later realized your problem structure was better suited for a different mathematical approach, you'd likely have to rewrite your entire problem definition. In MiniZinc, a statement like `constraint all_different(x);` is automatically translated by the compiler into whatever format the backend solver needs—whether that's passing it directly to a CP solver or decomposing it into linear inequalities for a MIP solver.

### High-Level Logic (Global Constraints)

MiniZinc comes with a comprehensive standard library of **global constraints** that encapsulate complex logical patterns (Rossi, Van Beek, and Walsh, 2006). For example, if you're dealing with scheduling, the `cumulative` constraint handles resource overlaps that would otherwise require writing custom loops and tricky conditional logic in an imperative language. Similarly, `diffn` ensures 2D shapes don't overlap when packing.

While libraries like OR-Tools certainly support many of these, MiniZinc's implementation is standardized, meaning you don't have to worry about whether your specific backend supports the constraint—the language handles the translation for you.

### Workflow: Exploration vs. Production

This leads to a common hybrid workflow: use MiniZinc for the **exploration** phase—rapidly modeling your problem to understand its complexity and rules—and only port it to an embedded language (like Python with OR-Tools) if you need to deploy it into a **production** environment where tight integration is critical (Perron and Furnon, 2019).

## Example Applications

### Employee Scheduling

A classic CP problem: A company runs three 8-hour shifts per day and assigns three of its four employees to different shifts each day, while giving the fourth the day off. Even with just 4 employees, there are 24 possible assignments per day, leading to 24^7 ≈ 4.5 billion possible weekly schedules (Perron and Furnon, 2019).

For Example:

* **N-Queens Problem**
* **Cryptarithmetic Puzzles**
* **Job Shop Scheduling**

These examples correspond to the standard CP problem categories in the literature (Rossi, Van Beek, and Walsh, 2006; Perron and Furnon, 2019).

## Practical Business Example: Employee Shift Scheduling (MiniZinc)

Finally, let's apply this to a real-world scenario. While N-Queens is theoretical, scheduling is a massive industry use case.

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

include "globals.mzn";

% Parameters (override via -D as needed)
int: E = 5;                      % number of employees
int: D = 7;                      % number of days (e.g., a week)
int: S = 3;                      % shifts per day (e.g., Morning, Evening, Night)

% ... (see full file for constraints and variables) ...

solve satisfy;
```

```{button-link} ../minizinc/shift_scheduling.mzn
:color: primary
:shadow:
:target: _blank

Download shift_scheduling.mzn
```

## Translating this into a real-world written script

With the Python MiniZinc API, you can load the model from a file and feed parameters directly, avoiding large inline strings:

```python
import minizinc
import os

# Load the model from the file
model_path = "src/minizinc/employee_scheduling/shift_scheduling.mzn"

# ------------ Python side ------------
model = minizinc.Model(model_path)
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

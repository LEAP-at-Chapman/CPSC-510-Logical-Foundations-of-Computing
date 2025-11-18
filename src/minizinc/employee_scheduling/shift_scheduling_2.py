import minizinc

MODEL = r"""
% Employee Shift Scheduling 2 - Boss Request Scenario
% 15 employees, 14 days, 3 shifts per day (Morning/Evening/Night)

% --- Removed globals.mzn for COIN-BC compatibility ---

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

% 1) Coverage: meet demand exactly
constraint forall(d in Days, s in Shifts) (
  sum(e in Employees)(x[e,d,s]) = demand[d,s]
);

% 2) No employee works two shifts on the same day
constraint forall(e in Employees, d in Days) (
  sum(s in Shifts)(x[e,d,s]) <= 1
);

% 3) Fairness cap over 2-week horizon
constraint forall(e in Employees) (
  sum(d in Days, s in Shifts)(x[e,d,s]) <= max_shifts_per_employee
);

solve satisfy;

output [
  "Two-Week Roster (E=", show(E), ", D=", show(D), ", S=", show(S), ")\n"
] ++
[
  day_name[d] ++ ":\n" ++
  concat([
    "  " ++ shift_name[s] ++ ": " ++
    concat([ if fix(x[e,d,s]) = 1 then employee_name[e] ++ " " else "" endif
           | e in Employees ]) ++ "\n"
    | s in Shifts ]) ++
  (if d < D then "\n" else "" endif)
  | d in Days
];
"""

# ---------------- Python Driver ----------------

model = minizinc.Model()
model.add_string(MODEL)

solver = minizinc.Solver.lookup("coin-bc")
instance = minizinc.Instance(solver, model)

# Problem dimensions
E = 15
D = 14
S = 3

instance["E"] = E
instance["D"] = D
instance["S"] = S

# Names
instance["shift_name"] = ["Morning", "Evening", "Night"]
instance["day_name"]   = [f"Day {d}" for d in range(1, D+1)]
instance["employee_name"] = ["Matt", "Spencer", "John", "Wayne", "Alex", "Brandon", "Khoa", "Jake", "Jack", "Alexander", "Erik", "Elizabeth", "Jon", "Kendall", "Thomas"]

# Demand matrix: 14 x 3 filled with 1s
instance["demand"] = [[1 for _ in range(S)] for _ in range(D)]

# Fairness cap — set manually here (matches -D option in MiniZinc)
instance["max_shifts_per_employee"] = 8   # tweak as needed

# Solve
result = instance.solve()

print(result)

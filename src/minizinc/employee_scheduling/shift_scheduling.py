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

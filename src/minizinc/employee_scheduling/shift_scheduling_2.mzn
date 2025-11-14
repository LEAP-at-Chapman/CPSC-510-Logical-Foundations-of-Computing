% Employee Shift Scheduling 2 - Boss Request Scenario
% Goal: Schedule 15 employees over a 2-week horizon (14 days) with 3 shifts/day.
%
% Run (set the fairness cap from the command line, e.g. 8 shifts per employee):
%   minizinc -s --solver coin-bc -D max_shifts_per_employee=8 shift_scheduling_2.mzn

include "globals.mzn";

% Defaults for the boss's request
int: E = 15;                     % employees
int: D = 14;                     % days (2 weeks)
int: S = 3;                      % shifts per day (Morning, Evening, Night)

set of int: Employees = 1..E;
set of int: Days = 1..D;
set of int: Shifts = 1..S;

% Pretty names
array[Shifts] of string: shift_name = ["Morning","Evening","Night"];
array[Days] of string: day_name = [ "Day " ++ show(d) | d in Days ];
array[Employees] of string: employee_name = [
  "Matt",
  "Spencer",
  "John",
  "Wayne",
  "Alex",
  "Brandon",
  "Khoa",
  "Jake",
  "Jack",
  "Alexander",
  "Erik",
  "Elizabeth",
  "Jon",
  "Kendall",
  "Thomas"
];

% Demand: how many employees needed per (day, shift)
% Default: 1 per shift across the horizon; adjust by overriding this array if needed.
array[Days, Shifts] of int: demand =
  array2d(Days, Shifts, [ 1 | d in Days, s in Shifts ]);

% Fairness / load cap across the 2-week horizon (set via -D or .dzn)
int: max_shifts_per_employee;

% Decision variables: x[e,d,s] = 1 if employee e works shift s on day d
array[Employees, Days, Shifts] of var 0..1: x;

% 1) Coverage: meet demand exactly for every (day, shift)
constraint forall(d in Days, s in Shifts) (
  sum(e in Employees)(x[e,d,s]) = demand[d,s]
);

% 2) No double-booking: an employee can work at most one shift per day
constraint forall(e in Employees, d in Days) (
  sum(s in Shifts)(x[e,d,s]) <= 1
);

% 3) Two-week fairness cap per employee
constraint forall(e in Employees) (
  sum(d in Days, s in Shifts)(x[e,d,s]) <= max_shifts_per_employee
);

solve satisfy;

% Output roster by day and shift
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
]
;



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

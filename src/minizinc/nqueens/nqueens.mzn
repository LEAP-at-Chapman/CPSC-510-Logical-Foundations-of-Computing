include "globals.mzn";

% N-Queens: place n queens on an n x n board so none attack each other
int: n = 8; % you can override via: minizinc -D n=10 ...
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

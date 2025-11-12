% N-Queens as a pure MIP model (works well with coin-bc)

int: n;
set of int: ROWS = 1..n;
set of int: COLS = 1..n;

% x[i,j] = 1 if a queen is placed at (row i, col j)
array[ROWS, COLS] of var 0..1: x;

% One queen per row
constraint forall(i in ROWS)(
  sum(j in COLS)(x[i,j]) = 1
);

% One queen per column
constraint forall(j in COLS)(
  sum(i in ROWS)(x[i,j]) = 1
);

% Main diagonals (j - i = d)
constraint forall(d in -(n-1)..(n-1))(
  sum([ x[i,j] | i in ROWS, j in COLS where j - i = d ]) <= 1
);

% Anti-diagonals (i + j = s)
constraint forall(s in 2..2*n)(
  sum([ x[i,j] | i in ROWS, j in COLS where i + j = s ]) <= 1
);

solve satisfy;

% Pretty board
output [
  if j = 1 then "\n" else " " endif ++
  (if x[i,j] = 1 then "Q" else "." endif)
  | i in ROWS, j in COLS
] ++ ["\n"];

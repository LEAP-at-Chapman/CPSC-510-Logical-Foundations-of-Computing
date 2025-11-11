% akari - Light Up puzzle

% Author: Spencer Au

int: R; int: C;
set of int: ROWS = 1..R;
set of int: COLS = 1..C;

% cells can be 5 kinds
% W - default empty cell (white)
% B - solid black cell
% B_NUM  - black cell with a number signifying the number of lamps adjacent to it in + pattern

% this is deprecated
% these 3 are possible properties of the white cells
% Lamp - cell contains a lamp; lights up cells in a + pattern similar to a rook; black cells stop the light
% Lit - white cell that is lit up
% X - white cell with X means that it cannot contain a lamp
%

%enum CellKind = {W, B, B_Num};%, Lamp, Lit, X};
enum Cell = {W, B, B_0, B_1, B_2, B_3, B_4};

array[ROWS, COLS] of Cell: akari_grid;

% bnum maps numbered black cells to its corresponding number
function int: bnum(Cell: x) =
    if x = B_0 then 0 else
    if x = B_1 then 1 else 
    if x = B_2 then 2 else 
    if x = B_3 then 3 else 
    if x = B_4 then 4 else -1
    endif endif endif endif endif;


/*
PREDICATES
*/

% T if cell is empty white 
predicate is_white(Cell: x) = x = W;
% T if cell is plain black
predicate is_black_plain(Cell: x) = x = B;
% T if cell is a numbered black 
predicate is_black_num(Cell: x) = x in {B_0, B_1, B_2, B_3, B_4};

% T if every cell between (row, col_1) and (row, col_2) is white
predicate clear_row(int: row, int: col_1, int: col_2) =
    let { int: a = min(col_1, col_2), int: b = max(col_1, col_2) } in
    forall(k in a+1..b-1)( is_white(akari_grid[row, k]) );
% T if every cell strictly between (row_1, col) and (row_2, col) is white
predicate clear_col(int: col, int: row_1, int: row_2) =
    let { int: a = min(row_1, row_2), int: b = max(row_1, row_2) } in
    forall(k in a+1..b-1)( is_white(akari_grid[k, col]) );

% % predicate is_lit used by output: T if a white cell is lit
% predicate is_lit(int: row, int: col) =
%     is_white(akari_grid[row,col]) 
%     /\
%     (
%         lamp[row,col]
%         \/
%         exists(col_2 in COLS where col_2 != col /\ clear_row(row, col, col_2)) ( lamp[row, col_2] )
%         \/
%         exists(row_2 in ROWS where row_2 != row /\ clear_col(col, row, row_2)) ( lamp[row_2, col] )
%     );


% decision var for lamp
array[ROWS, COLS] of var bool: lamp;

% lamp only on white cells
constraint forall(row in ROWS, col in COLS where not is_white(akari_grid[row, col])) (
        lamp[row, col] = false
);

% Rule 1: 4 orthogonal cells (+) must contains num of lamps that sum up to the black cell number
constraint forall(row in ROWS, col in COLS where is_black_num(akari_grid[row, col])) (
    % top
    (if row > 1 then bool2int(lamp[row-1, col]) else 0 endif) +
    % bottom
    (if row < R then bool2int(lamp[row+1, col]) else 0 endif) +
    % left
    (if col > 1 then bool2int(lamp[row, col-1]) else 0 endif) +
    % right
    (if col < C then bool2int(lamp[row, col+1]) else 0 endif)
    = bnum(akari_grid[row, col])
);

% Rule 2: no 2 lamps can "see" each other in orthogonal angles (like rooks in chess)
constraint
    % no 2 lamps on the same row that can see each other
    forall(row in ROWS, col_1 in COLS, col_2 in COLS
        % only pairs (col_1, col_2) in the same row with no wall between them
        where col_1 < col_2 /\ clear_row(row, col_1, col_2)) (
            bool2int(lamp[row, col_1]) + bool2int(lamp[row, col_2]) <= 1
        )
    /\ % : logical AND in minizinc
    % no 2 lamps on the same col that can see each other
    forall(col in COLS, row_1 in ROWS, row_2 in ROWS
        % only pairs (row_1, row_2) in the same col with no wall between them
        where row_1 < row_2 /\ clear_col(col, row_1, row_2)) (
            bool2int(lamp[row_1, col]) + bool2int(lamp[row_2, col]) <= 1
        );

% Rule 3: every white cell must be lit by a lamp
constraint forall(row in ROWS, col in COLS where is_white(akari_grid[row, col])) (
    % cell contains a lamp
    lamp[row, col] 
    \/ % : logical OR in minizinc
    % lit by another lamp in the same row without black cells blocking
    exists(col_2 in COLS where col_2 != col /\ clear_row(row, col, col_2)) (
        lamp[row, col_2]
    )
    \/
    % lit by another lamp in the same col without black cells blocking
    exists(row_2 in ROWS where row_2 != row /\ clear_col(col, row, row_2)) (
        lamp[row_2, col]
    )
);

% should use minimize? not sure if necessary for Akari
solve satisfy;

% visualize output to and check with online site for akari
function string: cell_char(int: row, int: col) =
    let { Cell: x = akari_grid[row,col] } in
    if x = B       then "B"
    elseif x = B_0 then "0"
    elseif x = B_1 then "1"
    elseif x = B_2 then "2"
    elseif x = B_3 then "3"
    elseif x = B_4 then "4"
    elseif x = W then (
        if fix(lamp[row,col]) then "L"
        elseif (
            fix(exists(col_2 in COLS where col_2 != col /\ clear_row(row, col, col_2)) ( lamp[row, col_2] ))
            \/
            fix(exists(row_2 in ROWS where row_2 != row /\ clear_col(col, row, row_2)) ( lamp[row_2, col] ))
        ) then "*"
        else "." endif
    )
    else "?" endif;

output [
    (if col = 1 then "\n" else " " endif) ++ cell_char(row,col)
    | row in ROWS, col in COLS
] ++ ["\n"];
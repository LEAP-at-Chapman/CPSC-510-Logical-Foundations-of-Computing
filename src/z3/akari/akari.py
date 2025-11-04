# Author: Spencer Au

from z3 import *

grid = [
    ["0",  "W",  "W",  "W",  "W",  "W",  "1"],
    ["W",  "1",  "W",  "W",  "1",  "B",  "W"],
    ["W",  "0",  "W",  "W",  "W",  "W",  "W"],
    ["W",  "W",  "W",  "W",  "W",  "W",  "W"],
    ["W",  "W",  "W",  "W",  "W",  "2",  "W"],
    ["W",  "B",  "1",  "W",  "W",  "B",  "W"],
    ["0",  "W",  "W",  "W",  "W",  "W",  "B"]
]

# not actually sure if Akari requires a square grid
ROWS, COLS = len(grid), len(grid[0])
for r in range(ROWS):
    assert len(grid[r]) == COLS, "all rows must be same length"


# PREDICATES
def is_white(v):
    return v == "W"

def is_black_plain(v):
    return v == "B"

def is_black_num(v):
    return v in {"0", "1", "2", "3", "4"}

# need this since i wanted string numbers in grid to preserve formatting
def numbered_value(v):
    return int(v) if v in {"0","1","2","3","4"} else None


# (DECISION) VARIABLES
# set lamp variable as a bool type (T if lamp is present, F otherwise)
lamp = [[Bool(f"lamp_{r}_{c}") for c in range(COLS)] for r in range(ROWS)]

# helper functions to help with constraints
def in_bounds(r, c):
    return 0 <= r < ROWS and 0 <= c < COLS

def get_orthog_neighbors(r, c):
    return [
            (r-1, c), # up
            (r+1, c), # down
            (r, c-1), # left
            (r, c+1)  # right
            ]

# check whether cell v blocks light (if its a solid black or numbered black cell)
def blocks_light(v):
    return is_black_plain(v) or is_black_num(v)

# precomputes for every white cell the list of other white cells it could illuminate if it contained a lamp
def compute_visibility(grid):
    # vis[r][c] = list of (rr, cc) white cells visible from (r,c), excluding itself
    vis = [[[] for _ in range(COLS)] for __ in range(ROWS)]
    for r in range(ROWS):
        for c in range(COLS):
            if not is_white(grid[r][c]):
                continue

            # up
            rr = r - 1
            while rr >= 0 and not blocks_light(grid[rr][c]):
                if is_white(grid[rr][c]):
                    vis[r][c].append((rr, c))
                rr -= 1

            # down
            rr = r + 1
            while rr < ROWS and not blocks_light(grid[rr][c]):
                if is_white(grid[rr][c]):
                    vis[r][c].append((rr, c))
                rr += 1

            # left
            cc = c - 1
            while cc >= 0 and not blocks_light(grid[r][cc]):
                if is_white(grid[r][cc]):
                    vis[r][c].append((r, cc))
                cc -= 1

            # right
            cc = c + 1
            while cc < COLS and not blocks_light(grid[r][cc]):
                if is_white(grid[r][cc]):
                    vis[r][c].append((r, cc))
                cc += 1
    return vis

# CONSTRAINTS
s = Solver()

# Rule 0.5: forbid lamps on black/numbered black cells
for r in range(ROWS):
    for c in range(COLS):
        if not is_white(grid[r][c]):
            s.add(lamp[r][c] == False)

#print(s.check())  # should be sat

# Rule 1: 4 orthogonal cells (+) must contain num of lamps that sum up to the black cell number
def add_rule1(s, grid, lamp):
    for r in range(ROWS):
        for c in range(COLS):
            v = numbered_value(grid[r][c])  # int if that cell is a numbered black, else skip
            if v is None:
                continue
            terms = []
            for rr, cc in get_orthog_neighbors(r, c):
                if in_bounds(rr, cc) and is_white(grid[rr][cc]):
                    terms.append(If(lamp[rr][cc], 1, 0))  # convert to an int so we can sum
            s.add(Sum(terms) == v)  # check if sum of lamps in orthog neighbors equals the number on the black cell


# Rule 2: no 2 lamps can "see" each other in orthogonal angles (like rooks in chess)
def add_rule2(s, grid, lamp, vis):
    for r in range(ROWS):
        for c in range(COLS):
            if not is_white(grid[r][c]):
                continue
            for rr, cc in vis[r][c]: # every white cell visible from (r,c)
                if (rr, cc) > (r, c): # avoid duplicate pairs such as (rr, cc) -> (r, c) and (r, c) -> (rr, cc)
                    s.add(Not(And(lamp[r][c], lamp[rr][cc]))) # NOT(lamp(r,c) AND lamp(rr,cc)); both cannot be lamps if they "see" each other

# Rule 3: every white cell must be lit by a lamp
def add_rule3(s, grid, lamp, vis):
    for r in range(ROWS):
        for c in range(COLS):
            if not is_white(grid[r][c]):
                continue
            # all possible lamps that could light this cell
            # lit_by = itself + visible orthog cells that could contain lamp
            lit_by = [lamp[r][c]]+ [lamp[rr][cc] for (rr, cc) in vis[r][c]]
            s.add(Or(lit_by)) # at least one must be true


vis = compute_visibility(grid)

add_rule1(s, grid, lamp)
add_rule2(s, grid, lamp, vis)
add_rule3(s, grid, lamp, vis)

print(s.check())
if s.check() == sat:
    m = s.model()

    def print_solution(model):
        lit = [[False]*COLS for _ in range(ROWS)]
        for r in range(ROWS):
            for c in range(COLS):
                if is_white(grid[r][c]):
                    if model.evaluate(lamp[r][c], model_completion=True):
                        lit[r][c] = True
                    else:
                        for rr, cc in vis[r][c]:
                            if model.evaluate(lamp[rr][cc], model_completion=True):
                                lit[r][c] = True
                                break
        for r in range(ROWS):
            row = []
            for c in range(COLS):
                if is_white(grid[r][c]):
                    row.append("L" if model.evaluate(lamp[r][c], model_completion=True)
                               else ("*" if lit[r][c] else "."))
                else:
                    row.append(grid[r][c])
            print(" ".join(row))

    print_solution(m)

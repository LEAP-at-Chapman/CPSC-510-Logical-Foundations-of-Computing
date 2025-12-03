% Water Jug Problem Solver
% Jug A: 4 liters capacity, Jug B: 3 liters capacity
% Goal: Measure exactly 2 liters

% ---------- State Representation ----------
% state(JugA_Current, JugB_Current)

% ---------- Valid Moves ----------

% 1. Fill Jug A completely
move(state(_, B), state(4, B)) :- 
    format('Fill Jug A~n').

% 2. Fill Jug B completely  
move(state(A, _), state(A, 3)) :-
    format('Fill Jug B~n').

% 3. Empty Jug A
move(state(_, B), state(0, B)) :-
    format('Empty Jug A~n').

% 4. Empty Jug B
move(state(A, _), state(A, 0)) :-
    format('Empty Jug B~n').

% 5. Pour from A to B until B is full or A is empty
move(state(A, B), state(NewA, NewB)) :-
    A > 0, B < 3,
    PourAmount is min(A, 3 - B),
    NewA is A - PourAmount,
    NewB is B + PourAmount,
    format('Pour ~w liters from Jug A to Jug B~n', [PourAmount]).

% 6. Pour from B to A until A is full or B is empty
move(state(A, B), state(NewA, NewB)) :-
    B > 0, A < 4,
    PourAmount is min(B, 4 - A),
    NewA is A + PourAmount,
    NewB is B - PourAmount,
    format('Pour ~w liters from Jug B to Jug A~n', [PourAmount]).

% ---------- Search Algorithm ----------

% Solve the water jug problem
solve :-
    solve_bfs([state(0,0)], [], Solution),
    reverse(Solution, ReversedSolution),
    nl, write('Solution Found!'), nl, nl,
    print_solution(ReversedSolution).

% Breadth-first search implementation
solve_bfs([state(A, B)|_], Visited, [state(A, B)|Visited]) :-
    (A =:= 2; B =:= 2),  % Goal condition: 2 liters in either jug
    !.

solve_bfs([CurrentState|RestQueue], Visited, Solution) :-
    findall(NextState, 
            (move(CurrentState, NextState), 
             \+ member(NextState, Visited)),
    NewStates),
    append(RestQueue, NewStates, NewQueue),
    solve_bfs(NewQueue, [CurrentState|Visited], Solution).

% ---------- Solution Display ----------
print_solution([]).
print_solution([State]) :-
    format_state(State), !.
print_solution([State1, State2|Rest]) :-
    format_state(State1),
    print_solution([State2|Rest]).

format_state(state(A, B)) :-
    format('Jug A: ~w liters, Jug B: ~w liters~n', [A, B]).

% ---------- Alternative Depth-First Search ----------
solve_dfs :-
    solve_dfs_path(state(0,0), [state(0,0)], Solution),
    nl, write('DFS Solution:'), nl,
    print_solution(Solution).

solve_dfs_path(state(A, B), Path, Path) :-
    (A =:= 2; B =:= 2), !.  % Goal reached

solve_dfs_path(CurrentState, Path, Solution) :-
    move(CurrentState, NextState),
    \+ member(NextState, Path),
    solve_dfs_path(NextState, [NextState|Path], Solution).
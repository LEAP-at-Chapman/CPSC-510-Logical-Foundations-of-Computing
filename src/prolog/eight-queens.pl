solution(Queens) :-
    length(Queens, 8),
    queens(Queens).

queens([]).
queens([queen(Row, Col) | Others]) :-
    queens(Others),
    length(Others, OthersLength),
    Row is OthersLength + 1,
    member(Col, [1,2,3,4,5,6,7,8]),
    noattack(queen(Row, Col), Others).

noattack(_, []).
noattack(queen(Row, Col), [queen(Row1, Col1) | Others]) :-
    Col =\= Col1,
    Col1-Col =\= Row1-Row,
    Col1-Col =\= Row-Row1,
    noattack(queen(Row, Col), Others).
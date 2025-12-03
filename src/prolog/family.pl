% ---------- Facts ----------
% parent(Parent, Child).
parent(arthur, george).
parent(harriet, george).
parent(george, amelia).
parent(george, richard).
parent(matlida, amelia).
parent(matlida, richard).
parent(george, susan).
parent(victoria, susan).
parent(susan, charles).
parent(walter, charles).
parent(richard, sophie).
parent(richard, joseph).
parent(ellen, sophie).
parent(ellen, joseph).

% ---------- Rules ----------
% X is a grandparent of Z if X is parent of Y and Y is parent of Z
% if there is a variable Y such that X is parent of Y and Y is parent of Z
grandparent(X, Z) :- parent(X, Y), parent(Y, Z).

% X is a sibling of Y if they share a parent and are not the same person
sibling(X, Y) :-
    parent(P, X),
    parent(P, Y),
    X \= Y.

% X is an ancestor of Z if X is a parent of Z or a parent of an ancestor of Z
ancestor(X, Z) :- parent(X, Z).
ancestor(X, Z) :- parent(X, Y), ancestor(X, Z).

% Gender facts (optional, to define mother/father)
male(arthur).
male(george).
male(walter).
male(charles).
male(richard).
male(joseph).
female(susan).
female(harriet).
female(victoria).
female(matlida).
female(amelia).
female(ellen).
female(sophie).

% father and mother rules
father(X, Y) :- parent(X, Y), male(X).
mother(X, Y) :- parent(X, Y), female(X).

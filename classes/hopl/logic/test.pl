member2(X, [X | _]).
member2(X, [_ | Xs]) :- member(X, Xs).
sublist2(X,Y) :- append(_,Z,Y), append(X,_,Z).

:- op(1100,yfx,arrow).

type(E, var(X), T) :- member([X,T], E).
type(E, apply(M,N), T) :- type(E,M,(S arrow T)), type(E,N,S).
type(E, lambda(X,M), (S arrow T)) :- type([[X,S] | E],M,T).



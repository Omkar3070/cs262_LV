
/*
      1. YES
      2. YES
      3. YES
      4. NO
      5. YES
      6. YES
      7. YES
      8. NO
      9. NO
      10. YES
*/


% unary operator neg and the binary operators
% and, or, imp, revimp, uparrow, equiv, downarrow, notimp, notequiv and notrevim

:-op(140, fy, neg).
:-op(160, xfy, [and, or, imp, revimp, uparrow, downarrow, notimp , notrevimp, equiv, notequiv]).

/* member(Item, List) :- Item occurs in List.
*/

member(X, [X | _]).
member(X, [_ | Tail]) :- member(X, Tail).

/* notmember(Item, List) :- Check if the Item
does not occur in the list.
*/

notmember(_, []) :- !.
notmember(X, [H|T]) :-
  X \= H,
  notmember(X, T).

/* emptychecker(List) :- Check if an empty List
occurs in the list.
*/

emptychecker([H|_]) :-
  H = [].
emptychecker([_|T]) :-
  emptychecker(T).

/* doubleneg(Literal, Literal) :- Check if the
input literal is a double negation, if it is
then handle it otherwise return as it is
*/

doubleneg(X, Y) :-
  unary(X),
  component(X, Y), !.
doubleneg(X, Y) :-
  X = Y.

/* remove(Item, List, Newlist) :-
Newlist is the result of removing all occurrences of
Item from List.
*/

remove(_, [ ], [ ]).
remove(X, [X | Tail], Newtail) :-
  remove(X, Tail, Newtail).
remove(X, [Head | Tail], [Head | Newtail]) :-
  remove(X, Tail, Newtail).


/* conjunctive(X) :- X is an alpha formula.
*/

conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ notequiv _).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).
conjunctive(neg(_ equiv _)).

/* disjunctive(X) :- X is a beta formula.
*/

disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ notequiv _)).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).
disjunctive(_ equiv _).

/* unary(X) :- X is a double negation,
or a negated constant.
*/

unary(neg neg _).
unary(neg true).
unary(neg false).

/* components(X, Y, Z) Y and Z are the components
of the formula X, as defined in the alpha and
beta table.
*/

components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).
components(X equiv Y, (X and Y), (neg X and neg Y)).
components(neg(X equiv Y), (neg X or neg Y), (X or Y)).
components(X notequiv Y, (neg X or neg Y), (X or Y)).
components(neg(X notequiv Y), (X and Y), (neg X and neg Y)).

/* component(X, Y) Y is the component of the
unary formula X.
*/

component(neg neg X, X).
component(neg true, false).
component(neg false, true).

/* matchlist(Literal, List_of_list, List) :- Find the List
for the list of lists to resolve.
*/

matchlist(X, [H|_], Aim) :-
  member(X, H),
  Aim = H.
matchlist(X, [_|T], Aim) :-
  matchlist(X, T, Aim).

/* resolvelist(List1, List2, literal, Newlist) :- Resolve the
two lists based on the literal to produce Newlist.
*/

resolvelist(List1, List2, Resolveon, Newlist) :-
  remove(Resolveon, List1, Tojoin1),
  notmember(Resolveon, Tojoin1),
  doubleneg(neg Resolveon, Kk),
  remove(Kk, List2, Tojoin2),
  notmember(Kk, Tojoin2),
  append(Tojoin1, Tojoin2, Newlist).

/* singlestep(Old, New) :- New is the result of applying
a single step of the expansion process to Old, which
is a generalized conjunction of generalized
disjunctions.
*/

singlestep([Disjunction | Rest], New) :-
  member(Formula, Disjunction),
  unary(Formula) ,
  component(Formula, Newformula),
  remove(Formula, Disjunction, Temporary),
  Newdisjunction = [Newformula | Temporary],
  sort(Newdisjunction, Sorted4),
  New = [Sorted4 | Rest].

singlestep([Disjunction | Rest], New) :-
  member(Alpha, Disjunction),
  conjunctive(Alpha) ,
  components(Alpha, Alphaone, Alphatwo),
  remove(Alpha, Disjunction, Temporary),
  Newconone = [Alphaone | Temporary],
  sort(Newconone, Sorted1),
  Newcontwo = [Alphatwo | Temporary],
  sort(Newcontwo, Sorted2),
  New = [Sorted1 , Sorted2 | Rest].

singlestep([Disjunction | Rest], New) :-
  member(Beta , Disjunction),
  disjunctive(Beta) ,
  components(Beta, Betaone, Betatwo),
  remove(Beta, Disjunction, Temporary),
  Newcon = [Betaone, Betatwo | Temporary],
  sort(Newcon, Sorted3),
  New = [Sorted3 | Rest].

singlestep([Disjunction|Rest], [Disjunction|Newrest]) :-
  singlestep(Rest, Newrest).

/* resolutionstep(Old, New) :- New is the result of applyting
the resolution rule step wise to Old.

A Literal from a Disjunction is selected. Then the
Disjunction from which the literal is selected is
removed from the list of Disjunctions. After which a
Disjunction containing the negation of the literal is
found and both the Disjunctions are resolved in accordance
to the resolution rule. The resolved Disjunction is then
added to the list of Disjunctions provided its not in there.
*/

resolutionstep(Bigdisjunctions, Newl) :-
  member(Disjunction, Bigdisjunctions),
  member(Elem, Disjunction),
  doubleneg(neg Elem, Newelem),
  remove(Disjunction, Bigdisjunctions, Smalldisjunctions),
  matchlist(Newelem, Smalldisjunctions, Getl),
  resolvelist(Disjunction, Getl, Elem, Attached),
  sort(Attached, Newattached),
  notmember(Newattached, Bigdisjunctions),
  append(Bigdisjunctions, [Newattached], Newl).


resolutionstep([Head|Tail], [Head|Newtail]) :-
  resolutionstep(Tail, Newtail).

/* expand(Old, New) :- New is the result of applying
singlestep as many times as possible, starting
with Old.
*/

expand(Dis, Newdis) :-
  singlestep(Dis, Temp),
  sort(Temp, Temp1),
  expand(Temp1, Newdis).

expand(Dis, Dis).

/* resolution(Old, New) :- New is the result of applying
resolutionstep as many times as possible, starting
with Old.
*/

resolution(Lis, _) :-
  emptychecker(Lis),
  write("YES").

resolution(Lis, Newlis) :-
  resolutionstep(Lis, Temp1),
  sort(Temp1, Temp2),
  resolution(Temp2, Newlis).

resolution(Lis, Lis) :-
  write("NO").

/* clauseform(X, Y) :- Y is the CNF of X.
*/

clauseform(X, Y) :-
  expand([[X]], Z),
  sort(Z, Y).

/* test(X) :- Outermost interface of
the program
*/

test(X) :-
  expand([[neg X]], Y),
  resolution(Y, _).

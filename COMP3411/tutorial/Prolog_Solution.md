# Prolog

1. Given the following Prolog clauses:

```Prolog
female(pam).
female(liz).
female(pat).
female(ann).
male(tom).
male(bob).
male(jim).

parent(pam, bob).
parent(tom, bob).
parent(tom, liz).
parent(bob, ann).
parent(bob, pat).
parent(pat, jim).

mother(Parent, Child) :- parent(Parent, Child), female(Parent).
father(Parent, Child) :- parent(Parent, Child), male(Parent).
grandparent(X, Z) :- parent(X, Y), parent(Y, Z).

sister(Sister, Sibling) :-
    parent(P, Sister),
    parent(P, Sibling),
    female(Sister),
    Sister \= Sibling. 
```

Define the *ancestor* relation such that ancestor(X, Y) is true if X is an ancestor of Y. What is the expected output of the query:

```Prolog
ancestor(X, Y) :-
    parent(X, Y).
ancestor(X, Z) :-
    parent(X, Y),
    ancestor(Y, Z).

?- ancestor(pam, X).
X = bob ;
X = ann ;
X = pat ;
X = jim ;
false.
```

1. Write a prolog predicate **insert(Num, List, NewList)** that takes a number **Num** along with a list of numbers **List** which is already sorted in increasing order, and binds **NewList** to the list obtained by inserting **Num** into List so that the resulting list is still sorted in increasing order.

```Prolog
% Base case
insert(Num, [], [Num]).

% New node at front if less the first element
insert(Num, [Head|Tail], [Num, Head|Tail]) :-
    Num =< Head.
% Otherwise insert it in the tail
insert(Num, [Head|Tail], [Head|Tail1]) :-
    Num > Head,
    insert(Num, Tail, Tail1).
```

3. Write a predicate **isort(List, NewList** ) that takes a **List** of numbers in any order, and binds **NewList** to the list containing the same numbers sorted in increasing order. Hint: your predicate should call the **insert/1** predicate from part 1.

**Note:** The notation **insert/1** means the predicate insert, which takes 1 argument.

```Prolog
% Base case
isort([], []).
% Sort the tail then insert the head.
isort([Head|Tail], List) :-
    isort(Tail, Tail_Sorted),
    insert(Head, Tail_Sorted, List).
```

4. Write a **predicate split(BigList,List1,List2)** that takes a list **BigList** and divides the items into two smaller lists **List1** and **List2** , as evenly as possible (i.e. so that the number of items in **List1** and **List2** differs by no more that 1). Can it be done without measuring the length of the list?

```Prolog
% Base case 0: empty list
split([], [], []).
% Base case 1: list with one element
split([A], [A], []).
% First element in first list, second element in second list
% then split recursively
split([A, B|T], [A|R], [B|S]) :-
    split(T, R, S).
```

5. Write a predicate **merge(Sort1, Sort2, Sort)** that takes two lists **Sort1** and **Sort2** that are already sorted in increasing order, and binds **Sort** to a new list which combines the elements from **Sort1** and **Sort2** , and is sorted in increasing order.

```Prolog
% If one list is empty, return the other list
merge(X, [], X).
merge([], X, X).
% If first element of first list is smaller,
% it becomes the first element of the merged list
merge([A|R], [B|S], [A|T]) :-
    A =< B,
    merge(R, [B|S], T).
% If first element of second list is smaller,
% it becomes the first element of the merged list
merge([A|R], [B|S], [B|T]) :-
    A > B,
    merge([A|R], S, T).
```

Extra Challenge:

Write a predicate **mergesort(List, NewList)** which has the same functionality as the **isort/2** predicate from part 2 above, but uses the MergeSort algorithm. Hint: you will need to use the **split/3** and **merge/3** predicates from parts 3 and 4 above.

```Prolog
% If one list is empty, return the other list
mergesort([], []).
mergesort([X], [X]).
% If the list has more than one element,
% split it into two lists of nearly equal length,
% sort the two smaller lists and merge them,
mergesort([A, B|T], S) :-
    split([A, B|T], L1, L2),
    mergesort(L1, S1),
    mergesort(L2, S2),
    merge(S1, S2, S).
```

# Planning

## Question 1 (Exercise 6.1 from Poole & Macworth)

Consider the planning problem from the lectures

![img](https://webcms3.cse.unsw.edu.au/static/uploads/pic/z8400090/1ff7ab5d5ac523a1fd32ab94f46f8c1e066252a2ab963963d0dbd558bd929faf/robot_planner.png)

1. Give the STRIPS representations for the pick up mail (pum) and deliver mail (dm) actions.
2. Give the feature-based representation of the MW and RHM features.

### Solution

1. The pickup mail action ( *pum* ) is defined using STRIPS by:

> **Preconditions:** *RLoc = mr* ∧ *mw
> ***Effects:** [¬ *mw* , *rhm* ]

The deliver mail action ( *dm* ) is defined using STRIPS by:

> **Preconditions:** *RLoc = off* ∧ *rhm
> ***Effects:** [¬ *rhm* ]

2. The *MW* feature can be axiomatised by defining when *MW* = *true* (written as *mw* ):

> *mw’* ← *mw* ∧ *Action* *≠* *pum*

The *RHM* feature can be axiomatised by defining when *RHM* = *true* (written as *rhm* ):

> *rhm’* ← *Action* = *pum
> **rhm’* ← *rhm* ∧ *Action* *≠* *dm*

## Question 2

Formulate the blocks world using STRIPS planning operators. The actions are stack (move one block to the top of another) and unstack (move one block to the table). The robot can hold only one block at a time.

To simplify the world, assume the only objects are the blocks and the table, and that the only relations are the on relation between (table and) blocks and the clear predicate on table and blocks. Also assume that it is not possible for more than one block to directly support another block (and vice versa).

### Solution

stack(A, B):

**Preconditions:** clear(A) ∧ clear(B)
**Effects:** on(A, B) ∧ ¬ clear(B)

unstack(A):

**Preconditions:** clear(A) ∧ on(A, B)
**Effects:** on(A, Table) ∧ clear(B) ∧ ¬on(A, B)

**Note:** The **Effects** could also be written as an addles contain only the positive literals and the delete list, containing only the negative literals.
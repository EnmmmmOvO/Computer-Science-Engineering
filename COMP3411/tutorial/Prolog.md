# Prolog 

Attempt at least questions 1, 2, and 3 in class. Try doing the rest in your own time and see if you can work them out before we publish the solutions next week.

1. Given the following Prolog clauses:

2. ```Prolog
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

3. Define the *ancestor* relation such that ancestor(X, Y) is true if X is an ancestor of Y. What is the expected output of the query:

4. ```Prolog
   ancestor(pam, X).
   ```

5. Write a prolog predicate **insert(Num, List, NewList)** that takes a number **Num** along with a list of numbers **List** which is already sorted in increasing order. **NewList** is the list obtained by inserting **Num** into **List** so that the resulting list is still sorted in increasing order. E.g.

6. ```Prolog
   insert(2, [1, 3], [1, 2, 3]).
   insert(1, [], [1]).
   ```

7. Write a predicate **isort(List, NewList)** where **List** a list of numbers in any order, and **NewList** is the list containing the same numbers sorted in increasing order. Hint: your predicate should call the **insert/3** predicate from question 2.
   **Note:** The notation **insert/1** means the predicate **insert** , which takes 1 argument.

8. ```Prolog
   isort([4, 7, 2, 1], [1, 2, 4, 7]).
   isort([], []).
   ```

9. Write a **predicate split(BigList, List1, List2)** which takes a list **BigList** and divides the items into two smaller lists **List1** and **List2** , as evenly as possible (i.e. so that the number of items in **List1** and **List2** differs by no more that 1). Can it be done without measuring the length of the list?

10. ```Prolog
    ?- split([1,2,3,4,5], X, Y).
    X = [1, 3, 5],
    Y = [2, 4]
    ```

11. Write a predicate **merge(Sort1, Sort2, Sort)** where **Sort1** and **Sort2** are already sorted lists, and **Sort** is the list which combines the elements from **Sort1** and **Sort2** , and is sorted in increasing order.

12. ```Prolog
    ?- merge([1, 5, 6, 9], [2, 5, 11], X).
    X = [1, 2, 5, 5, 6, 9, 11]
    ```

### Extra Challenge

Write a predicate **mergesort(List, SortedList)** which has the same functionality as the **isort/2** predicate from part 2 above, but uses the MergeSort algorithm. Hint: you will need to use the **split/3** and **merge/3** predicates from parts 3 and 4 above.

# Planning

## Question 1 (Exercise 6.1 from Poole & Macworth)

Consider the planning problem from the lectures

![img](https://webcms3.cse.unsw.edu.au/static/uploads/pic/z8400090/1ff7ab5d5ac523a1fd32ab94f46f8c1e066252a2ab963963d0dbd558bd929faf/robot_planner.png)

1. Give the STRIPS representations for the pick up mail (pum) and deliver mail (dm) actions.
2. Give the feature-based representation of the MW and RHM features.

## Question 2

Formulate the blocks world using STRIPS planning operators. The actions are stack (move one block to the top of another) and unstack (move one block to the table). The robot can hold only one block at a time.

To simplify the world, assume the only objects are the blocks and the table, and that the only relations are the on relation between (table and) blocks and the clear predicate on table and blocks. Also assume that it is not possible for more than one block to directly support another block (and vice versa).
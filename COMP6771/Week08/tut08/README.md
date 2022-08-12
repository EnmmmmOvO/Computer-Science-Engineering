# Tutorial 8

## Question 1

What is iterator invalidation? Why does it occur?

## Question 2

Assignment 3 involves abstracting a container of containers as a single container. Consider a simple
example of `std::vector<std::vector<int>>`. Abstracting the container requires storing the outer
iterator and the inner iterator. Discuss potential issues with this idea, and once you think you've
discovered all of them, discuss how you might solve these issues.

## Question 3

Look at `source/rope_user.cpp` and `source/rope.hpp`

We have defined a rope class as a bunch of strings tied together, and have defined a basic class and
some starter code using it.

1. Write an input iterator for this class so that you can uncomment lines 65-72. You can use the
   `static_assert`s that we provide to check you're on the right path.

2. Discuss two ways we might modify our code to allow both a const and a non-const iterator. What
   are the advantages and disadvantages for each?

3. Modify your iterator so that it models both `std::bidirectional_iterator` and
   `std::output_iterator<rope::iterator, char>`.

## Question 4

Look at `source/silly_set.cpp`

1. Complete this `silly_set` wrapper class (yes, it's a bit redundant).

* Implement the member functions
* Template the container type and set set to be the default container

Use template template parameters to avoid the case where we can accidentally define
`silly_set<int, std::vector<float>>`.

## Question 5 

For question 3, can this iterator be designed to model `std::random_access_iterator`? Justify your answer. (Note: if it can, you _do not_ need to
   implement it for the tutorial.)

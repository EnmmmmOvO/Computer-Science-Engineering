# Tutorial 9

## Question 1

When would we specialise classes? Why do we not specialise functions?

## Question 2

In `source/is_a_pointer.h`, define your own type trait, from scratch, for is_a_pointer, to be used in an application like this

```cpp
template <typename T>
printPointer(std::ostream& os, T t) {
  if constexpr (traits::is_a_pointer<T>::value) {
  	os << *t << "\n";
  } else {
  	os << t << "\n";
  }
}
```

Ensure that your type trait is wrapped in a trait namespace.

Write a test for your type trait in `test/is_a_pointer.cpp`

## Question 3

In `source/is_real_number.h`, use type traits in the std namespace to produce your own composition type trait that returns true if the type passed in is an integer or floating point. It should be used as follows

```cpp
template <typename T>
if (is_real_number<T>::value) {
  std::cout << "Is real number" << "\n";
}
```

## Question 4

Look at `include/streaming_median.h`.

This is a simple, inefficient class which calculates the current median (middle element) for a stream of data. It has the limitation of only working on odd sized streams.

See `source/use_streaming_median.cpp` for an example of usage.

### Part 1
`streaming_median` currently allows the user to use any (ordered) type. This means that the general implementation of `median` doesn't work on even sized streams, as for many types, such as `std::string`, there isn't an obvious way to calculate the midpoint between two values. For example:

```c++
["c++", "javascript", "kotlin", "R"] // What is the median of this data?
```

However, the median is well-defined for arithmetic types (`int`, `float`, `double`, etc):

```c++
[1.0, 2.0, 3.0, 4.0] // The median is (2.0 + 3.0) / 2.0 = 2.5.
```

Discuss some different approaches to allow `streaming_median` to work for even sized streams of arithmetic types.

### Part 2
Modify the existing `streaming_median` class to add a compile time check for whether the parameterized type is arithmetic, to provide an implementation of `median()` which works for evenly sized streams of arithmetic type.

## Question 5

Look at `source/decltype.cpp`.

What are the inferred types for each of the following?

## Question 6

What does the binding table for lvalues/rvalues look like?

## Question 7

Look at `source/forward.cpp`

This code currently doesn't work as the implementation for my_make_unique is incomplete. Complete it through the addition of using std::forward as well as variadic types. To compile with this code, you will need to use types.h which can be found <a href="https://github.com/cs6771/comp6771/blob/master/lectures/week8/forwarding/types.h">HERE</a> in the github.

# Tutorial 10

This tutorial was written in 2019, before the use of the 2020 toolchain. Many of these files will not compile outright on the 2020 toolchain, so we recommend just compiling them directly with g++ and then running the binaries. This is OK, as this week's tutorial is mainly about understand conceptual ideas from week 9.

## Question 1

Look at `source/private.cpp`

Compile this with `g++ source/private.cpp -o private`

### Question 1.1

Why does this code not compile?

### Question 1.2

The code will now compile, but what are the potential disadvantages of this solution? How would we fix it?

## Question 2

Look at `source/type.cpp`

Compile this with `g++ source/type.cpp -o type`

### Question 2.1

For each of these variables, what is the static and dynamic type (for b, consider this both after and before assigning d to it)?

### Question 2.2

The assignment *b = d;* is legal but is poor style as it causes the object slicing problem. What is the object slicing problem?

### Question 2.3

What is the output of this code?

### Question 2.4

How can we correct this code to prevent the object slicing problem?

## Question 3

Look at `source/vtable.cpp`.

Draw the vtables for classes A, B and C

## Question 4

Look at `source/basic.cpp`

Compile this with `g++ source/basic.cpp -o basic`

* Work out on paper/whiteboard what the output of this program is.

* Change the declaration of class fish to:
```cpp
class fish  : public amphibian {
```

Work out what the new output is.

Why are the outputs different?

## Question 5

Look at `source/destructors.cpp`

Compile this with `g++ source/destructors.cpp -o destructors`

On paper/whiteboard work out the output of this program.

# Revision Questions

## Revision Question 1

Look at `source/constructors.cpp`

Compile this with `g++ source/constructors.cpp -o constructors`

On paper/whiteboard work out the output of this program.

## Revision Question 2

A friend function of a class can access:
 * Only the public members of the clas
 * Only the public and protected members of the class
 * All members of the class
 * All members of the class and its base
 * Only the public and protected members of the class and its base

## Revision Question 3

Look at `source/revision.cpp`. Work out the output.

Compile this with `g++ source/revision.cpp -o revision`

## Revision Question 4

What are the differences (e.g., types, semantics, memory usage) between a T, a pointer to a T, and a reference to a T?

## Revision Question 5

Explain the differences in the meaning and effect of using *const* in the following member function prototypes:

```cpp
const T& get_value_at_index(int i);
T get_value_at_index(const int i);
T get_value_at_index(int i) const;
```


# Tutorial 7

## Question 1

Why do we use smart pointers instead of raw pointers whenever possible?

## Question 2

What is an example of a circumstance a std::shared_ptr<T> would be preferred over a std::unique_ptr<T>?

## Question 3

Note: The parameter type is the type used in the method signature, the argument type is what gets passed to it.

In the following code:
* Which argument types can be converted to which parameter types? Which cannot be converted? What is the rationale?
* What is the type of the arguments to each of these, and how do they get converted to the type of the parameters?
* Based on the previous two questions, which of the following lines will compile, and which will not?

```cpp
void c_lvalue(const std::string& lvalue);
void lvalue(std::string& lvalue);
void rvalue(std::string&& rvalue);
void value(std::string value);

c_lvalue("hello");
lvalue("hello");
rvalue("hello");
value("hello");
std::string s = "world";
c_lvalue(s);
lvalue(s);
rvalue(s);
value(s);
c_lvalue(std::move(s));
lvalue(std::move(s));
rvalue(std::move(s));
value(std::move(s));
auto s2 = "goodbye";
c_lvalue(s2);
lvalue(s2);
rvalue(s2);
value(s2);
```

## Question 4

Look at `source/instant.h`

How many instantiations of max are generated?

## Question 5

What is wrong with the implementation in `source/stack.hpp`, `source/stack.cpp`, `source/stack_use.cpp`?

## Question 6

Look at `source/stringqueue.h`

Convert the following class to a generic (templated) type. After converting it to a generic type:
 * Complete all incomplete implementations.
 * Add an appropriate default constructor
 * Add an appropriate copy constructor

Finally, make the size of this queue a non-type parameter.

What are the advantages and disadvantages of the non-type parameter?

## Question 7

Which part of this graph are:
 * Edges
 * Nodes
 * Weightings

https://www.researchgate.net/profile/Yilun_Shang/publication/271944978/figure/fig2/AS:669349501231106@1536596765134/A-weighted-directed-graph-G-with-six-vertices.png

## Question 8

Look at `source/constexpr.cpp`.

Rewrite the code so that the lookup table is generated at compile time, and remove magic numbers.

What are the benefits of `constexpr`? When might you use it? What are some of the downsides?

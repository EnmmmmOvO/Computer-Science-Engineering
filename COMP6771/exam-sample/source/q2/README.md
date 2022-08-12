# Question 2

[[_TOC_]]

## 1. Background

Normal lists in C++ are either C-style arrays or standard-library containers (e.g. `std::vector`, `std::array`, `std::list`). We want to create a more powerful list structure in C++. We want to create one that can exhibit more interesting behaviours. For example:

```cpp
auto l1 = smart_list<double>{1,2,3};
auto l2 = smart_list<double>{4,5,6};
auto l3 = l1 + l2;
REQUIRE(l3 == smart_list<double>{1,2,3,4,5,6})
```

In rare cases we want a list that is _very_ smart and can do everything a normal `smart_list` can do, but can also sometimes make use of particular properties of our types:

```cpp
auto l = very_smart_list<int>{6,9,15};
l /= 3;
REQUIRE(l == very_smart_list<int>{2,3,5});
REQUIRE(l.is_prime());
```

A `smart_list` should not be able to do these things: it's not smart enough.

Please note that the usage of "list" here is quite high level, and does not specifically refer to a linked list. In most cases "list" in higher level languages just refers to an object similar to `std::vector`.

## 2. Task

You are to develop a new class template `smart_list<T>` that behaves similar to a `std::vector<T>` except that it has a handful of modified funtionality and additional functionality.
You are also to develop a new class `very_smart_list<T>` which can do everything a `smart_list<T>` can do, with more.

The interface of these classes are described below. 
Where functions are provided for both `smart_list` and `very_smart_list`, 
the use of "`smart_list`" should be replaced by "`very_smart_list`" when appropriate except when otherwise mentioned.

**There are no constraints regarding internal representation or implement. As long as the interface functions as described that is all that matters**. You are allowed to have more functions on the public interface than we have described (if this helps you solve the question).

### Constructors

**Both `smart_list` and `very_smart_list`:**

- `explicit smart_list(std::size_t count)` / `explicit very_smart_list(std::size_t count)`
  - A constructor that generates exactly `count` default-constructed elements into the list.
  - _Example:_ `auto x = smart_list<int>(5);`
  - _Exceptions:_ None.
- `smart_list(T const& one, T const& two, std::size_t count)` / `very_smart_list(T const& one, T const& two, std::size_t count)`
  - A constructor that generates `count` repetitions of appending both `one` and `two` to the list.
  - _Example:_ `auto x = smart_list<std::string>("hello", "there", 3)` would produce a list containing `["hello", "there", "hello", "there", "hello", "there"]`.
  -  _Exceptions:_ If `one == two`, throws `"Cannot use multi-argument constructor with two identical elements"`
- `smart_list(std::initializer_list<T> il)` / `very_smart_list(std::initializer_list<T> il)`
  - A constructor that initializes its contents with the given list.
  - _Example:_ `auto l = smart_list<double>{ 1.0, 1.5, 2.0 };`
  - _Exceptions:_ None.

**For `very_smart_list` only:**

- `explicit very_smart_list(smart_list<T> const& other)`
  - A constructor that copies all elements from `other`.
  - _Example:_ `auto vsl = very_smart_list<double>(sl);`
  - _Exceptions:_ None.
- `explicit very_smart_list(smart_list<T>&& other)`
  - A constructor that moves all elements from `other`.
  - _Example:_ `auto vsl = very_smart_list<double>(std::move(sl));`
  - _Exceptions:_ None.

### Accessors

**Both `smart_list` and `very_smart_list`:**

- `std::size_t size()`
  - Returns the number of elements in the container.
  - _Example:_ `auto x = sl.size();`
  - _Exceptions:_ None.

### Modifiers

**Both `smart_list` and `very_smart_list`:**

- `void push_back(const T& value)`
  - Appends the given element to the end of the container.
  - _Example:_ `sl.push_back(5);`
  - _Exceptions:_ None.
- `void pop_back()`
  - Removes the last element in the container.
  - _Example:_ `sl.pop_back();`
  - _Exceptions:_ If `sl.size() == 0`, throws `"Cannot pop_back an empty list"`.
- `void emplace_back(Args... args)`
  - Appends a new element to the end of the container, constructed in-place using perfect forwarding.
  - _Example:_ `auto sl = smart_list<std::pair<int, double>>(); sl.emplace_back(1, 2.0);`
  - _Exceptions:_ None.
  - _Notes:_ The provided signature is not totally correct; you must determine the appropriate signature to perfectly forward the list of arguments.

### Operator overloads

**Both `smart_list` and `very_smart_list`:**

- `operator[](std::size_t index)`
  - Get and/or set a value at the given index.
  - _Example:_ `auto a = sl[1]; sl[2] = a + 2;`
  - _Exceptions:_ None. (You can assume the index is valid.)
- `smart_list operator+(smart_list const& lhs, smart_list const& rhs)`
  - Concatenate two smart lists together.
  - _Example:_ `auto c = a + b;`
  - _Exceptions:_ When `lhs.size() == 0` or `rhs.size() == 0`, throw `"Cannot concatenate smart lists where one is empty"`.
  - _Notes:_ Always returns a `smart_list`, even when called on `very_smart_list`s.
- `smart_list operator-(smart_list const& lhs, smart_list const& rhs)`
  - Return a copy of `lhs`, with all elements also present in `rhs` removed.
  - _Example:_ `auto c = a - b;`
  - _Exceptions:_ When `lhs.size() == 0` or `rhs.size() == 0`, throw `"Cannot subtract smart lists where one is empty"`.
  - _Notes:_ you can assume you may use `operator==` to compare elements. Always returns a `smart_list`, even when called on `very_smart_list`s.
- `smart_list<smart_list<T>> operator*(smart_list const& lhs, smart_list const& rhs)`
  - Multiply two lists together. The output is a 2D smart list with products of all components.
  - _Example:_
    ```cpp
    auto a = smart_list<double>{1,2,3};
    auto b = smart_list<double>{2,3,4};
    auto c = a * b;
    REQUIRE(c == smart_list<smart_list<double>>{{2,3,4},{4,6,8},{6,9,12}});
    ```
  - _Exceptions:_ None.
  - _Notes:_ You can assume you may use `operator*` to multiple elements. Always returns a nested `smart_list`, even when called on `very_smart_list`s.
- `std::ostream& operator<<(std::ostream& os, smart_list const& sl)`
  - Prints out each element of `sl` to `os` with a `|` on either side of the element.
    An empty list should print nothing.
  - _Example:_
    ```cpp
    auto sl = smart_list<double>{1,2,3};
    std::cout << sl;  // |1|2|3|
    ```
  - _Exceptions:_ None.

**For `very_smart_list` only:**

- `very_smart_list operator*(very_smart_list const& lhs, double scalar)`
  - Scalar multiplication, where e.g. `[1 2] * 3 = 3 * [1 2] = [3 6]`.
    If `T` is not an arithmetic type, then this function has no effect
    and simply returns a copy of the list passed in.
  - _Example:_ `auto x = sl * 3.0; auto y = 3.0 * sl;`
  - _Exceptions:_ None.
- `very_smart_list operator/(very_smart_list const& lhs, double scalar)`
  - Scalar division, where e.g. `[3.0 6.0] / 2.0 = [1.5 3.0]`.
    If `T` is not an arithmetic type, then this function has no effect
    and simply returns the list passed in.
  - _Example:_ `auto x = sl / 3.0;`
  - _Exceptions:_ None.

### Miscellaneous functions

**For `very_smart_list` only:**

- `bool is_prime()`
  - Returns `false` if `T` is not an integer type.
    Otherwise, returns `true` iff all of the elements in the container are prime numbers.
  - _Example:_ `auto x = vsl.is_prime();`
  - _Exceptions:_ None.

### Other notes

You are also required to ensure that both classes have the following capabilities:
 * It is comparable using `operator==` and `operator!=` with the normal meanings (assuming that `T` is also comparable)
 * Standard default constructor that populates an empty list
 * Standard copy semantics (construction and assignment) that does member-wise copy
 * Standard move semantics (construction and assignment) that does member-wise move
 * Standard destructor that ensures all memory is cleaned up
 * For operators where it makes sense, a compound assignment form should exist as well (e.g. provide `operator+=` too). It should throw the same exceptions as well.
 * Provides functions `begin()` and `end()` that returns a type which models at least `std::bidirectional_iterator` and act as iterators to your underlying container. You can assume `begin()` and `end()` return only `const_iterator`-like types (no non-const iterators).

You should be able to use a `very_smart_list` wherever a `smart_list` is expected.
For example:
```cpp
auto sl = smart_list<double>{1,2,3};
auto vsl = very_smart_list<double>(sl);
vsl *= 3.0;
REQUIRE(sl + vsl == smart_list<double>{1,2,3,3,6,9});
```
However, you should not be able to use a `smart_list` where a `very_smart_list` is expected:
```cpp
auto sl = smart_list<double>{1,2,3};
sl *= 3.0;  // should be a compiler error
```

You are required to ensure that relevant operators are marked const where appropriate, or have both a const and non-const version where appropriate.

All exceptions thrown are `std::runtime_error`. The use of "_Exceptions:_ None." just means you do not need to throw any exceptions yourself: you do not need to handle exceptions thrown by operations on the types stored.

<b>Please ensure that as a priority you ensure that `operator==`, `push_back`, and default construction work. We will rely on these 3 heavily for testing.</b>

## 3. Assumptions & Constraints

* There are no performance requirements or constraints for this question
* You can assume that all input is valid unless stated otherwise in the spec

## 4. Mark Breakdown

For this question, the approximate mark allocations are:

- 60% for correctly implementing `smart_list`
  - 20% of this will be for constructors
  - 10% of this will be for Accessors
  - 10% of this will be for modifiers
  - 40% of this will be for operator overloads
  - 10% of this will be for miscellaneous functions
  - 10% of this will be other requirements listed in "Other notes"
- 30% for correctly implementing `very_smart_list` (everything from `smart_list` plus additional functions)
  - 20% of this will be for constructors
  - 10% of this will be for Accessors
  - 10% of this will be for modifiers
  - 40% of this will be for operator overloads
  - 10% of this will be for miscellaneous functions
  - 10% of this will be other requirements listed in "Other notes"
- 10% for allowing `very_smart_list` to be used everywhere a `smart_list` might be expected
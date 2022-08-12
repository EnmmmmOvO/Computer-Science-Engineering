# Tutorial - Week 2

### Question 1

1. What is a `TEST_CASE`?

> A `TEST_CASE` is a uniquely-named scope that has the context for our test framework, and will keep
track of all the `CHECK`s and `REQUIRE`s that pass/fail.

2. What is a `CHECK`? How is it different to an `assert`?

> `CHECK` will evaluate an expression and report if it is `false`, but the program will continue to
run.

3. What is a `REQUIRE`? How is this different to an `assert`?

> `REQUIRE` is closer to an `assert` than a check, in that it terminates the test case, but unlike
an `assert`, it will gracefully exit the test case, rather than terminate on the spot. Subsequent
test cases are still execute, so unlike an assert, it only aborts a portion of the program, rather
than the whole program.

4. What are `SECTION` blocks in Catch2?

> `SECTION` blocks allow us to write setup code for our checks. Every `SECTION` will run all the
code in the `SECTION` block that it's enclosed in, all the way back up to the `TEST_CASE`. This
means that we can modify what we're testing in one section, and still get the same state we
started in all following states at the same level!

5. How do they make testing easier?

> All of your setup is done once, which reduces the amount of code duplication that you need to do,
the amount of `REQUIRE`s you need to do, which optimises for both the reader and the writer.

### Question 2

1. Why is this relationship between algorithms, iterators, containers so important, and how does it help us as programmers?

> The relationship is important because it allows us to abstract away the details of the data
> structure so that we only need to write each algorithm once, instead of a combinatorial explosion
> of times.
>
> It also allows experts to focus on what they're good at. Someone might be really good at writing
> optimised algorithms, but not necessarily in writing memory-efficient data structures. They can
> focus on the algorithm without needing to worry about the data structure at all.

2. How does this relate to the DRY (don't repeat yourself) principle?

> It relates to the DRY principle in that we need to write _x_ range types + _y_ algorithms, instead
> of _x_ range tpyes * _y_ algorithms.

### Question 3

What is the difference between each kind of iterator?
<ul>
  <li>Input iterator</li>
  <li>Output iterator</li>
  <li>Forward iterator</li>
  <li>Bidirectional iterator</li>
  <li>Random-access iterator</li>
</ul>

> An input iterator allows read and increment. However, it cannot make multiple passes when incrementing</li>
> An output iterator allows write and increment. However, it cannot make multiple passes when incrementing</li>
> A forward iterator allows read, write and increment</li>
> A bidirectional iterator allows read, write, increment, and decrement</li>
> A random-access iterator allows read, write, increment, decrement, +x, and -x</li>

### Question 4

What is different about a const iterator compared to a non-const iterator? Why would you want to do this?

> A const iterator does not allow modification of the value that the iterator refers to.
> This can prevent accidental mutation

### Question 5

Which algorithms can we replace these raw bits of code with?

```cpp
auto first(std::vector<int> const& v, int const needle) -> std::vector<int>::iterator {
  for (auto i = v.begin(); i != v.end(); ++i) {
    if (*i == needle) {
      return i;
    }
  }
  return v.end();
}

// Note: this one wasn't covered in the lectures. See C++ Reference to get an idea of what it might
// be: https://en.cppreference.com/w/cpp/algorithm.
auto second(std::vector<int>& v, std::vector<int>::iterator new_first) -> std::vector<int>::const_iterator {
  auto copy = std::vector<int>(v.begin(), new_first);
  v.erase(v.begin(), new_first);
  return v.insert(v.end(), copy.begin(), copy.end());
}
```

> Answers:
> `first` is `std::find`.
> `second` is `std::rotate`.


### Question 6

What kind of iterator is each of the following (and are the iterators const)?<
Which of these will compile, and which of these will not?

```cpp
const std::vector<int> vec;
std::list<int> li;
std::forward_list<double> forward_li;
std::string s;

// input, output, forward, bidirectional, random access

vec.begin(); // const random access iterator
vec.cbegin(); // const random access iterator
(*vec.begin())++; // won't compiler trying to modify the vec
li.cbegin(); // const bidirectional iterator
li.rbegin(); // reverse bidirectional iterator
forward_li.cbegin(); // const forward iterator
(*forward_li.cbegin())++; // won't compile
s.begin(); // random access iterator
std::back_inserter(vec); // const random access iterator
std::back_inserter(li); // bidirectional iterator
std::istream_iterator<int>(std::cin); // input iterator
std::ostream_iterator<int>(std::cout, " "); // output iterator
```

### Question 7

For the remainder of questions, you'll be asked to write a function or a program (i.e. also write a
`main` function). You should also write a test case for each of them in the corresponding files in
the `test` directory.

Write a function that sorts a vector of strings in _descending_ order.

You should write your algorithm in `source/sort_descending.cpp` and your test in
`test/sort_descending.cpp`.

### Question 8

We have written some code in `source/marks.cpp` to store information in a container and then access the middle element (to determine the median). What's wrong with this code? How could we modify this code to produce the intended result?

### Question 9

In `source/rev.cpp` you will see a C-style and C++-style method of forward iterating through an array. In each of these cases, how would we modify the code (rev.cpp) to iterate in the other direction? Why is the C++ way preferred?

### Question 10

In `source/overload.cpp` we have two functions - `minInt` and `minDouble`.Use function overloading to improve the style of this code.

### Question 11

> This question is from _Cracking the Coding Interview (6th Edition)_, by Gayle Laakmann McDowell.

Given two strings, write a function to determine if one string is a permutation of the other.

You should write your algorithm in `source/is_permutation.cpp` and your tests in
`test/is_permutation_test.cpp`.

### Question 12

Bonus question: Checkout `source/map.cpp` and ask your tutor to clarify any parts that you don't understand.
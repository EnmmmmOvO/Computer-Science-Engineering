# Tutorial - Week 1

## Question 0

Your tutor will take some time to get to you, and for you to get to know them.

## Question 1

Please see SETUP.md to setup your environment on vlab. Or see SETUP_HOME.md for setup locally. All students are required to set it up on vlab at a minimum.

If you're unfamiliar with git, we have also included more instructions in `git101`

## Question 2

`<iostream>` contains an object called `std::cin`, which we can use to read in from the character
input (i.e. the keyboard), like so.

```cpp
auto i = 0;
if (not (std::cin >> i)) {
  std::cerr << "Something went wrong while reading an integer, bailing...\n";
  return 1;
}

std::cout << "Value of i: " << i << '\n';
```

Write a program in `source/add_numbers.cpp` that reads in two integers and prints out the sum of
them.

Build your program before you run it.

1. Press _Ctrl+Shift+P_, type `CMake: Build Target`, and press Enter.
2. You should see a blank textbox. Type `add_numbers` and press Enter.
3. An output window should appear, detailing the process.

Open the terminal tab (it's next to the output tab) on the window that just detailed the output above.

Type the following commands, and the behaviour should follow:

```sh
$ build/source/add_numbers
Please enter two numbers: 2 3
Sum: 5
```

```sh
$ build/source/add_numbers
Please enter two numbers: 2 x
Something went wrong while reading an integer, bailing...
```

> See `source/add_numbers.cpp` on the `solutions` branch.

## Question 3

Write a C++ program in `source/cat.cpp` that mimics the C program written below. For each C++
change, what advantages does C++ provide?

```cpp
int main() {
  char buffer[100];
  fgets(buffer, 100, stdin);
  printf("%s\n", buffer);
  return 0;
}
```

1. Press _Ctrl+Shift+P_, type `CMake: Build Target`, and press Enter.
2. You should see a blank textbox. Type `cat` and press Enter.
3. In the terminal tab, run the program by running `build/source/cat`

Note: Pages 395-6 of _Programming --- Principles and Practice Using C++ (Second Edition)_ might be
useful for this question.

> See `source/cat.cpp` on the `solutions` branch.

## Question 4

Which parts of this program are declarations and which parts are definitions?

```cpp
int get_age();

int main() {
  auto name = std::string{};
  name = "Gary Bai";
  std::cout << name << " is " << get_age() << '\n';
  return 0;
}

int get_age() {
  return 38;
}
```

> Declaration: `int get_age();`
> Definition: `int main() { ... }`
> Definition: `auto name = std::string{};`
> Definition: `int get_age() { return 24; }`
> Note that both definitions are also declarations.

## Question 5

Do any of the following have errors? If so, what are they?

1.
```cpp
auto i = 3;
i = 4;
```

> No issue

2.
```cpp
auto const j = 5;
--j;
```

> ERROR: j is an constant integer which cannot be modified.

3.
```cpp
auto age = 18;
auto& my_age = age;
++myAge;
```

> No issue

4.
```cpp
auto age = 21;
auto const& my_age = age;
--my_age;
```

> `my_age` is a reference to `int const`, which cannot be modified.

## Question 6

Write a function, called `sort3` in `source/sort3.cpp`, which takes three `int` objects and sorts
them in ascending order. Then, write test cases in `test/sort3_test.cpp` to confirm that `sort3` is
correct.

1. Press _Ctrl+Shift+P_, type `CMake: Build Target`, and press Enter.
2. You should see a blank textbox. Type `sort3_test` and press Enter.
3. In the terminal tab, run the program by running `build/test/sort3_test`

Hint: you can use the utility binary function `ranges::swap`, so you don't need to manually do the
swapping step yourself by including `"range/v3/utility.hpp"`.

```cpp
// Example
ranges::swap(x, y);
```

> See `source/sort3.cpp` on the `solutions` branch.

## Question 7

Overload `sort3` so that it also sorts three `std::string` objects. Don't forget to write more test
cases!

> See `source/sort3.cpp` on the `solutions` branch.

## Question 8

> Ask for a couple of volunteers who would like to join our Teams chat and give us feedback throughout the course. Tell them we're looking for people who would like to spend time chatting to the other students and getting a read for how they're feeling and then pass on their feedback. 2-4 people is fine.

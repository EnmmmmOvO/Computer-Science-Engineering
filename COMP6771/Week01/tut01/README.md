# Tutorial - Week 1

## Question 0

Your tutor will take some time to get to you, and for you to get to know them.

## Question 1

Please see `SETUP.md` to setup your environment on vlab. Or see `SETUP_HOME.md` for setup locally. All students are required to set it up on vlab at a minimum.

If you're unfamiliar with `git`, we have also included more instructions in `git101`

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

## Question 5

Do any of the following have errors? If so, what are they?

1.
```cpp
auto i = 3;
i = 4;
```

2.
```cpp
auto const j = 5;
--j;
```

3.
```cpp
auto age = 18;
auto& my_age = age;
++myAge;
```

4.
```cpp
auto age = 21;
auto const& my_age = age;
--my_age;
```

## Question 6

Write a function, called `sort3` in `source/sort3.cpp`, which takes three `int` objects and sorts
them in ascending order. Then, write test cases in `test/sort3_test.cpp` to confirm that `sort3` is
correct.

1. Press _Ctrl+Shift+P_, type `CMake: Build Target`, and press Enter.
2. You should see a blank textbox. Type `sort3_test` and press Enter.
3. In the terminal tab, run the program by running `build/test/sort3_test`

## Question 7

Overload `sort3` so that it also sorts three `std::string` objects. Don't forget to write more test
cases!

## Question 8

Your tutor has a question about ongoing feedback!

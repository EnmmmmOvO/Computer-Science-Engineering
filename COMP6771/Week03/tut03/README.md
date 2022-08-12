# Tutorial 3

## Question 1

How might we use a lambda function in the following example to sort vec by the number of vowels in each string? If the number of vowels is equal, then sort by the number of consonants.

```cpp
std::vector<std::string> vec{"We", "love", "lambda", "functions"};
```

Implement it in `tests/lambda_string.cpp`

## Question 2

When writing a lambda function, when would you capture by value, and when would you capture by reference?

## Question 3

This task focuses on using standard algorithms to read a list of newline-seperated words from a file (try /usr/share/dict/words or /usr/dict/words) into a vector (hint: see std::istream_iterator).

### Question 3.1

In `source/dict.cpp`, write a function that takes in the word list as a stream, and outputs a vector of strings that are the words.

### Question 3.2

In `source/dict.cpp`, write a function that uses standard algorithms to split the string into words, filtered to only words that are in the word dict, and reconstruct this into a string (hint: see std::istringstream, std::istream_iterator, std::copy_if, std::ostringstream, and std::ostream_iterator)

### Question 3.3

Add your own tests to `test/dict.cpp`. This file has not been created, so you will have to create it yourself and add the appropriate line to `CMakeLists.txt`.

### Question 3.4

Discuss why separating your functions you want to test is a good idea.

### Question 3.5

Assume now that the word list and strings are both very large. Discuss how we could make this code run much faster (hint: a different data structure may be required. Tutors, students should know the data type, but not what it is called in C++)

### Question 3.6

Discuss the effect the use of automatic type deduction (through the use of auto keyword, and by not having to declare types at all when calling functions) on the quantity of code you had to change, and the depth of the testing required.

## Question 4

Open `source/car.h` and `source/car.cpp`

### Question 4.1

Create a constructor for the car that takes in the manufacturer name (e.g. Toyota) and the number of seats. Ensure that your constructor uses a member initializer list and uniform initialisation. Why is it important to use a member initializer list? Why is uniform initialisation preferred since C++11?

### Question 4.2

Create a default constructor that delegates to the previous constructor using the values of "unknown" and 4

Create const member functions to get the manufacturer and number of seats. What does it mean for a class or function to be const correct?

### Question 4.3

Create a static data member to keep count of the number of car objects created. Modify your constructors to ensure that the count increases when a new object is created. Do you need to increase the object count in your delegating constructor?

### Question 4.4

Ensure that your static object count is initialised to 0, where should you do this, in the header file or the cpp file?

### Question 4.5

Create a static function to return the object count. What does it mean for an function or data member to be static? Is the static data member part of the object or the class?

### Question 4.6

Create a destructor that decreases the object count when an object is destroyed

### Question 4.7

Test your code extensively by adding tests to the test directory, and adjusting the `CMakeLists.txt` file accordingly.

Make sure you keep your code - this example will continue next week.

# Question 1

## 1. Task

Write a stack-based calculator program in C++. The calculator reads tokens (numbers and commands) from a specified input file. In the input file each token is separated by a space or a new line. Each number is placed on a stack and each command consumes one or more values from the stack. A command may result in a modification of the stack, an additional number added to the stack, and/or output printed to the output stream provided. The calculator should support int and double values and only promote an int to a double when necessary. When printing output, your double values should be formatted to three decimal places. Your calculator should act on the following tokens:

|Token|Description|Console Output|
|-|-|-|
|x.y|A double (where x and y are numbers). All doubles will have decimal places. e.g., 2.1||
|x|An integer (where x is a number).||
|add|Removes two numbers from the stack and calculates their sum. The sum is pushed back onto the stack.|x + y = z|
|sub|Removes two numbers from the stack and subtracts the second number removed from the first. The result is pushed back onto the stack.|x - y = z|
|mult|Removes two numbers from the stack and multiplies their product. The result is pushed back onto the stack.|x * y = z|
|div|Removes two numbers from the stack and divides the first by the second. The result is pushed back onto the stack.|x / y = z|
|sqrt|Removes the top of the stack and calculates the sqrt of this number. Pushes the result back onto the stack.|sqrt y = z|
|pop|Removes the top of the stack.||
|reverse|Removes the top of the stack. The ordering of the next n (the number that was at the top of the stack) elements are reversed on the stack.||
|repeat|Removes the top of the stack. Numbers and commands continue to be read from the file but not acted on until an endrepeat command.||
|endrepeat|Processes the numbers and commands that were read from the input file but stored from the start of the repeat command. These numbers and commands are repeated n times (where n is the number that was at the top of the stack when the repeat command was given).| |

### 1.2 Sample input and output

To test your code you can write your own tests in `test/q1` (like the one we've provided).

### 1.3 Promotion of int to double

We expect you to know when to promote ints to double for additional, subtraction, and multiplication. I.E. Result should be int if both inputs are integers, otherwise it should be a double.

For division, the result should only be integer if both inputs to division are integers and their division has no remainder, otherwise it should be a double.

For square root, all results should be of type double (this is mainly to make your life easier).

## 2 Performance Requirements

This is not a performance-driven question. There will be reasonable time limits as part of our testing infrastructure to stop code that takes seconds to run (e.g. due to infinite loops), but unless you have a genuine bug or are doing something wildly intense in your code (e.g. making an API call to some web server somewhere....), timing won't be an issue.

## 3 Assumptions

* You can assume that all input will be valid as per the spec
* You can assume that the input files will have enough arguments on the stack to carry out a command (e.g. the file won't just contain "10 add", sinc there's nothing to add 10 to)
* The top of the stack after a `reverse` will always be a non-negative integer
* `repeat` will always have a corresponding `endrepeat`.
* `int` type will suffice for your choice of integer
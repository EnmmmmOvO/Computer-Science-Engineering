# Lab 04

### Due: Week 5 Friday, 5pm

### Value: 2 marks towards the Class Mark

## Aims

* Analyse code with a lens to design and further practice articulating design evaluations
* Improve design quality by applying refactoring techniques
* Work with Java streams, lambdas and comparators
* Improve code quality using Java streams and lambdas
* Understand and apply Design by Contract

## Setup

**REMEMBER** to replace the zID below with your own.

```
git clone gitlab@gitlab.cse.unsw.EDU.AU:COMP2511/21T3/students/z555555/lab04.git
```

## Lab 04 - Exercise - Enrolments 🛡️

Inside `src/unsw/enrolment` is a codebase that models a system with the following requirements:

* Students enrol in courses that are offered in particular terms
* Students receive grades (pass, fail, etc.) for courses in particular terms
* Courses may have pre-requisites (other courses) and must have credit point values
* For a student to enrol in a course, they must have passed all prerequisite courses

There is a simple integration test inside `test/EnrolmentTest.java`, which currently passes.

The code contains a series of design smells. Your task is to:

1. Make a note of all design smells the code currently contains;
2. Refactor the code to improve the quality of the **design** by removing the smells, justifying your design decisions. The integration test should ideally remain passing unchanged, however if you feel it necessary to adjust it slightly due to your design changes, that is fine.
3. Complete the implementation of the `studentsEnrolledInCourse` function by sorting the list using a custom-defined comparator. Students should be sorted by:
    * Their program; then
    * The number of streams they are enrolled in, in ascending order; then
    * Their name; then
    * Their zID
    
    You should start by writing a failing unit test in the `testComparator` method of `EnrolmentTest`.
4. Improve the quality of the **code** by rewriting instances of `for (X x : collection) { ... }` using Java streams and accompanying methods and lambdas. One example of this is provided in the starter code given in `studentsEnrolledInCourse`.

All of your notes and justifications should go inside `enrolments.md`.

<details>

<summary>
Hint
</summary>

You may find some of the following Java stream methods useful:

* `anyMatch`
* `allMatch`
* `forEach`
* `filter`
* `map`
* `findFirst`

</details>

## Lab 04 - Exercise - The Bank's Contract 💰

Consider a simple Bank system that allows for customers to have accounts. The customers can make deposits and withdrawals, and in this simplified system, an account balance is never allowed to go below 0. 

Inside `src/banking`, create a `BankAccount` class for maintaining a customer's bank balance.
  * Each bank account should have a current balance and methods implementing deposits and withdrawals.
  * Money can only be withdrawn from an account if there are sufficient funds.

In the JavaDoc for the methods, define preconditions and postconditions for the methods.

Then, create a subclass of `BankAccount` called `LoggedBankAccount`, also with the preconditions and postconditions articulated. 
  * Every deposit and withdrawal must make a log of the action.

Inside `bank.md`, answer the following questions in a few sentences:

* Explain why the code is consistent with the preconditions and postconditions.
* Explain why *balance >= 0* is a class invariant for both classes.
* Are your class definitions consistent with the Liskov Substitution Principle?

## Lab 04 - Challenge Exercise - Rational Numbers 🧮

In many situations (both in OOP and procedural programming) you have probably encountered, you have been given some sort of library / ADT / API / class which has a series of methods/routes/functions and allows you to call these methods, and the problem has been to use the methods to make some sort of game, or to make something useful happen.

In this exercise, we're going to reverse the roles. Your friend Attila has written a program inside `FunFractions.java` which plays a game for kids learning about fractions. 

We don't want to use Java `double` floating point numbers for this since they have a limited number of decimal places and [can't accurately represent or manipulate](https://en.wikipedia.org/wiki/Floating-point_arithmetic#Accuracy_problems) all rational numbers (fractions). You must create your own `Rational` class to store and manipulate rational numbers.

Attila's job is to implement the game which uses the `Rational` class that you will write. Unfortunately, Attila didn't consult with you to come up with an interface, or contract between the class and the class user and just assumed what the methods would be. His solution doesn't currently compile and is commented out.

Your task is to firstly write the declaration for the `Rational` class inside `Rational.java` which specifies the contract, including all preconditions, postconditions and invariants for each of the methods that are not constructors or `toString`. Then, implement the methods so that the game in `FunFractions.java` works.

### Construction and `toStr`

Your class should support creating any valid rational number with a numerator and denominator.

The number ²/₃ is created as `Rational frac = new Rational(2, 3)`.

You do not need to handle zero denominators or any cases of division by zero.

When `toString` is called, your `Rational` class should display in simplified form. For example, `Rational(21, 12)` should be displayed as 1³/₄. The small nubmers must be done using unicode superscript and subscript digits. These have been provided to you in `SUPER_NUMS` and `SUB_NUMS` in `Rational.java`.

### Methods

* The `.equals()` methods should return `true` if the numbers are equivalent. For example `Rational(4, 8)` is equivalent to `Rational(1, 2)`
* The `add`, `subtract`, `multiply` and `divide` methods should all work as expected on two `Rational` objects and return a new `Rational` instance without modifying the originals.

### The Game

When you have implemented all the methods correctly, the game should work like this:

```
What is 4 × 1¹/₄?
0) 5
1) 1⁴/₅
2) ¹/₂
3) 1¹/₅
> 0
Correct!

What is 1 ÷ ²/₅?
0) 1¹/₅
1) ¹/₄
2) 2¹/₂
3) 1
> 1
Incorrect. The correct answer was: 2¹/₂

What is ⁷/₉ - 1¹/₂?
0) 10
1) -¹³/₁₈
2) 3
3) ⁷/₁₀
> 1
Correct!

What is ³/₈ × 1²/₇?
0) 2
1) ²⁷/₅₆
2) 0
3) 1¹/₂
> 
Invalid input. The correct answer was: ²⁷/₅₆
```

## Lab 04 - Bonus Exercise - Narrative Design ✨

[Watch this video](https://youtu.be/uzO77dk5SRE?t=794), it's part of a lecture from an older version of this course. 

We have seen from this lab that design is something that is central across all levels of abstraction - at the code level, at the function level, at the class level and the system level. The subjectivity of design makes it an art form, like that of narrative and literature. The video gives an example of this in the rendition of *The Two Towers*.

Think of a story, movie or TV show that you enjoy that exhibits good narrative design. Inside a Wiki Page on WebCMS, write down what parts you think make the story well designed. When writing, think also of the commonalities between the narrative and other narratives (structurally, stylistically) and note down some of the 'design patterns' the narrative contains. Your post doesn't have to be a literature essay (though you can if you like), just some simple observations and appreciation.

## Submission

To submit, make a tag to show that your code at the current commit is ready for your submission using the command:

```bash
$ git tag -fa submission -m "Submission for Lab-04"
$ git push -f origin submission
```

Or, you can create one via the GitLab website by going to **Repository > Tags > New Tag**.
We will take the last commit on your master branch before the deadline for your submission.

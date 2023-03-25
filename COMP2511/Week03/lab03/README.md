# Lab 03

### Due: Week 4 Monday, 1pm

### Value: 2 marks towards the Class Mark

## Aims

* Design Object-Oriented solutions for simple problem domains
* Practice creating UML Diagrams
* Create custom exception classes in Java
* Practice writing tests tests with JUnit
* Use coverage checkers on Java programs

## Setup

**REMEMBER** to replace the zID below with your own.

`git clone gitlab@gitlab.cse.unsw.EDU.AU:COMP2511/21T3/students/z555555/lab03.git`

## Lab 03 - Exercise - Cars 🚗 

In this problem, we are going to continue the UML Diagram exercise from the tutorial. Your tutor will provide a pdf containing the diagram you worked on together.

### Requirements Version 1

A Car has one or more engines and a producer. The producer is a manufacturing company who has a brand name.  Engines are produced by a manufacturer and have a speed. There are only two types of engines within UNSW's cars:

* **Thermal Engines**, which have a default max speed of 114, although they can be produced with a different max speed, and the max speed can change to any value between 100 and 250.
* **Electrical Engines**, which have a default max speed of 180. This is the speed at which they are produced, and the max speed can change to any value that is divisible by 6.

Cars are able to drive to a particular location `x`, `y`.

Since UNSW is a world-leader in technology innovation, they want you to be able to model the behaviour of Time Travelling for *any* vehicle, and to model a time travelling car. A vehicle that travels in time *stays in the same location* but travels to a `LocalDateTime`.

### Requirements Version 2

In addition to the above which you did in the tutorial, you will need to model the following:

1. The Car also has an owner. The owner is the official 'owner of the car' on paper, who has a name, address and can own many cars. 

2. There are two new types of engines:

* **Nuclear Engines**, which has a default max speed of 223; the engine can be produced with a different max speed and can change to any number that is prime. Nuclear engines also have a nuclear energy value between 1 and 10 and are able to propel at their nuclear energy value.
* **Solar Engine**, which has a default max speed of 90, and the max speed can change to anything below 150. This is the speed at which they are produced.

3. In the innovation space, UNSW wants you to model flying for any vehicle. Flying constitutes driving, except to a location `x`, `y`, `z`. They also want you to model the following vehicles specifically:

* Planes, which are able to fly and contain a list of passengers' names
* Flying Cars (note that flying cars can still drive normally)
* Time Travelling Flying Cars

### Task

**You do not need to write any code for this exercise.**

Complete the UML diagram which models the domain. As you design your solution, make a note of the **reasoning** behind each of your key design decisions in `rationale.md`. 

Think about the following OO design concepts:

* Abstraction
* Inheritance by extending classes
* Abstract classes
* Interfaces
* Has-a vs Is-a relationships (Composition vs Inheritance)

Your UML diagram will need to include:

* Getters and setters
* Constructors
* Aggregation/Composition relationships
* Cardinalities
* Inheritance/implementation relationships 

Submit your UML diagram in a file called `cars-design.pdf` in the root directory of this repository.

## Lab 03 - Exercise - Files 📨

Inside `src/unsw`, there is a folder `archaic_fs` and `test` that mocks a very simple file system and tests it respectively. Three tests are already written in there. `archaic_fs` simulates a 'linux' like [inode](https://en.wikipedia.org/wiki/Inode) system. You do not need to understand how it works under the hood (it simply mocks the typical linux commands). The code is also arguably written quite poorly, and in later weeks we will look at refactoring it.

The following commands are available:

| Function | Behaviour | Exceptions |
| -------- | --------- | ---------- |
| <code>cd(path)</code> | <a href="https://man7.org/linux/man-pages/man1/cd.1p.html">Change Directory</a> | <ul><li>Throws <code>UNSWNoSuchFileException</code> if a part of the path cannot be found</li></ul> | 
| <code>mkdir(path, createParentDirectories, ignoreIfExists)</code> | <a href="https://man7.org/linux/man-pages/man1/mkdir.1.html">Make Directory</a> | <ul><li>Throws <code>UNSWFileNotFoundException</code> if a part of the path cannot be found and <code>createParentDirectories</code> is false</li><li>Throws <code>UNSWFileAlreadyExistsException</code> if the folder already exists and <code>ignoreIfExists</code> is false</li></ul> |
| <code>writeToFile</code> | Writes <code>content</code> to a file at <code>path</code><ul><li>Options are a EnumSet of FileWriteOptions, e.g. <code>EnumSet.of(FileWriteOptions.APPEND, FileWriteOptions.CREATE)</code></li><li>The full set is <code>CREATE</code>,<code>APPEND</code>,<code>TRUNCATE</code>,<code>CREATE_IF_NOT_EXISTS</code></li></ul> | <ul><li>Throws <code>UNSWFileNotFoundException</code> if the file cannot be found and no creation options are specified</li><li>Throws <code>UNSWFileAlreadyExistsException</code> if the file already exists and <code>CREATE</code> is true.</li></ul>
| <code>readFromFile(path)</code> | Returns the content for a given file. | <ul><li>Throws <code>UNSWFileNotFoundException</code> if the file cannot be found</code> |  

Your task is to:
1. Create the `UNSWFileNotFoundException` and `UNSWFileAlreadyExistsException`, `UNSWNoSuchFileException` exception types in the `exceptions` package. They can simply inherit their Java counterparts (`java.io.FileNotFoundException`, `java.nio.file.FileAlreadyExistsException` and `java.nio.file.NoSuchFileException`)
2. Complete the suite of integration tests for the system. You will need at least **80% branch coverage** (see below). Make sure to test both success and error conditions.

### Coverage Checking

If you need a conceptual refresher on code coverage you can read [this Atlassian article](https://www.atlassian.com/continuous-delivery/software-testing/code-coverage).

For this exercise, we require that your JUnit tests give at least 80% branch coverage on your code. In this course we will be using a coverage checker called **Gradle**. Gradle also allows you to see the results of your tests against your code, including test failures.

Download the zip file from (download should start automatically): [https://gradle.org/next-steps/?version=5.4.1&format=bin](https://gradle.org/next-steps/?version=5.4.1&format=bin)

You should follow the installation instructions provided: [https://gradle.org/install/#manually](https://gradle.org/install/#manually)

For Linux users, note that you may have to edit the ~/.bashrc file to permanently change the PATH variable by appending the line:
export PATH=$PATH:/opt/gradle/gradle-5.4.1/bin

Note that Gradle 5.4.1 is the same version as on CSE machines. It has been chosen so that common syntax can be used for the test.gradle file to Jacoco coverage testing.

Then in the root directory of your repository run the following:

If on *LOCAL* you need to run the following

```bash
$ gradle test -b test.gradle
```

If on *CSE* you need to run the following

```bash
$ 2511 gradle test -b test.gradle
```

The coverage checking report will be in: [build/reports/jacoco/test/html/index.html](build/reports/jacoco/test/html/index.html)

The test report will be in: [build/reports/tests/test/index.html](build/reports/tests/test/index.html)

## Submission

To submit, make a tag to show that your code at the current commit is ready for your submission using the command:

```bash
$ git tag -fa submission -m "Submission for Lab-03"
$ git push -f origin submission
```

Or, you can create one via the GitLab website by going to **Repository > Tags > New Tag**. 

We will take the last commit on your `master` branch before the deadline for your submission.

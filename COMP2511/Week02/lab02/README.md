# Lab 02

### Due: Week 3 Monday, 1pm

### Value: 2 marks towards the Class Mark

## Aims

* Understand the Object-Oriented principles of abstraction and encapsulation
* Utilise inheritance and polymorphism to create abstractions
* Analyse code with a lens to design and practice articulating design evaluations
* Work with abstract classes and interfaces
* Work with JSON in Java

## Setup

An individual repository for you for this lab has been created for you on the CSE GitLab server. You can find it at this URL (**substituting** z5555555 for your own zID):

https://gitlab.cse.unsw.edu.au/z5555555/lab02

i.e.

**REMEMBER** to replace the zID below with your own.

```
git clone gitlab@gitlab.cse.unsw.EDU.AU:COMP2511/21T3/students/z555555/lab02.git
```

## Lab 02 - Exercise - Staff  🔱

Modify the class StaffMember (inside package `staff`) so that it satisfies the following requirements:

* Attributes to store the staff member’s name, salary, hire date, and end date.
* Appropriate constructors, getters, setters, and other methods you think are necessary.
* Overridden `toString()` and `equals(..)` methods. Use what you learnt from the tutorial, but make sure you understand what these methods are doing.
* Javadoc for all non-overriding methods and constructors.

Create a sub-class of `StaffMember` called `Lecturer` in the same package with the following requirements:

* An attribute to store the school (e.g. CSE) that the lecturer belongs to
* An attribute that stores the academic status of the lecturer (e.g A for an Associate Lecturer, B  for a Lecturer, and C for a Senior Lecturer)
* Appropriate getters and setters.
* An overriding `toString()` method that includes the school name and academic level.
* An overriding `equals(...)` method.
* Javadoc for all non-overriding methods and constructors.

Create a class `StaffTest` in the package `staff.test` to test the above classes. It should contain:

* A method `printStaffDetails(...)` that takes a `StaffMember` as a parameter and invokes the `toString()` method on it to print the details of the staff.
* A `main(...)` method that:

  * Creates a `StaffMember` with a name and salary of your choosing.
  * Creates an instance of `Lecturer` with a name, salary, school and academic status of your choosing.
  * Calls `printStaffDetails(...)` twice with each of the above as arguments.
  * Tests the `equals(..)` method of the two classes. Use [the documentation](https://docs.oracle.com/en/java/javase/11/docs/api/java.base/java/lang/Object.html#equals(java.lang.Object)) for `Object.equals(...)` as a guide for what you should test.
  * You do not need to write any JUnit tests for this exercise (though you can if you would like)

## Lab 02 - Exercise - Hotel 🏨

Inside `src/hotel` there is some starter code for the backend to a hotel booking system. The system is designed to address the following requirements:

* There are three types of rooms:
    * Standard rooms;
    * Ensuite rooms; and
    * Penthouse rooms
* A Hotel has a series of rooms and a name.
* Rooms can be booked from a start date to an end date, and the client can specify which of the types of rooms they wish to book
* Each of the types rooms has their own custom welcome message.

The code currently uses an interface `Room`, and the three different types of rooms are modelled as `StandardRoom`, `EnsuiteRoom` and `PenthouseRoom` which all `implement` `Room`.

Recall concepts of code style from COMP1511 and basic Software Engineering Design Principles from COMP1531. The code for the `Room` classes currently contains a series of code smells; problems which make it poorly quality code. Your task is to:

1. Analyse the code and document all of the code smells you can see inside `hotel.md`. Hint: Remember DRY and KISS principles.
2. Refactor the code to remove the smells. You may need to consider changing the inheritance structure to facilitate this. Document all of the changes you make inside `hotel.md`.
3. Complete the implementations of all rooms by writing the methods:
    * `toJSON`
    * `removeBooking`
    * `changeBooking`
    so that all types of Rooms have the required functionality. You will also need to complete the `overlaps` method of `Booking`.
3. Implement the `Hotel` class:
    * You will need to add a private `List` field to the class.
    * You will need to implement `makeBooking` and `toJSON`. The `instanceof` operator may help you implement `makeBooking`.
    * After you have implemented the class, consider how you use abstraction & polymorphism to reduce code complexity, and explain this inside `hotel.md`.

You should test that your code works as expected in addition to ensuring that it is well designed.

## Lab 02 - Challenge Exercise - Pineapple on Piazza 🍕

Welcome back to Piazza (even though Ed is a much better forum). This week we're going to finish off our implementation. We are going to make `Post` its own class, and implement functions which raise exceptions. If you didn't complete the Piazza challenge exercise last week then that's OK!

Updated requirements:

**`Post`**

* A `Post` is created by a particular author;
* The author is able to edit the content, but other users cannot;
* Any user should be able to bump the upvotes, but only once per user.

**`Thread`**

* A `Thread` is created with a title, and a first post;
* The owner of the thread is the author of the first post;
* Any new user can add a new post to the thread;
* The thread owner can edit the title and tags, but other users cannot.

**`PiazzaForum`**

* The `Forum` contains a list of threads;
* Users can search for threads by tag;
* Users can search for posts by author.

Once again, there are a series of function stubs provided for you to implement with instructions in the JavaDoc.

There is also a class defined called `PermissionDeniedException` which you should `raise` whenever a user tries to perform an action (e.g. delete someone else's post) that they are not allowed to perform. You can throw (equivalent of `raise` in Python) this exception using `throw new PermissionDeniedException()`.

## Lab 02 - Challenge Exercise - Degree Distribution 📝

In Australia, university degrees are allocated using a centralised preference system, where final high school exam marks are converted into a score in steps of 0.05 up to 99.95. A score of 99.00 indicates that the student's aggregated marks were better than 99% of their cohort.

Each degree has a certain number of available places, and accepts students until it is full. Students nominate up to nine degrees, ordered from first to last preference. They are considered in descending order of their marks, receiving an offer for the first degree in their preference list that still has available places. Each degree has a *cutoff mark*: the lowest score out of the students who received a place in that degree.

You will be given two JSON files, one containing degrees and one containing students. An example `degrees.json` is in the following format.

```javascript
[{"code": 422000, "name": "Bachelor of Arts","institution": "University of New South Wales", "places": 10},
{"code": 422300, "name": "Bachelor of Social Research and Policy","institution": "University of New South Wales", "places": 8},
{"code": 423600, "name": "Bachelor of Planning","institution": "University of New South Wales", "places": 10},
{"code": 511207, "name": "Bachelor of Arts (Media and Communications)","institution": "University of Sydney", "places": 2},
{"code": 511504, "name": "Bachelor of Commerce","institution": "University of Sydney", "places": 1},
{"code": 511795, "name": "Bachelor of Computer Science and Technology","institution": "University of Sydney", "places": 8}]
```

`students.json` is in the following format.

```javascript
[{"name": "Claudia Zingaro", "score": 84.50, "preferences": ["422300+2","511207"]},
{"name": "Ivan Connolly", "score": 91.00, "preferences": ["511207+5","511504"]},
{"name": "Jeffie Honaker", "score": 94.50, "preferences": ["511207","511504","511795"]},
{"name": "Floria Rozar", "score": 82.25, "preferences": ["422000","422300","511207","511504"]},
{"name": "Hyun Castleberry", "score": 83.15, "preferences": ["511795", "423600"]},
{"name": "Leland Acheson", "score": 81.15, "preferences": ["511207","422000"]},
{"name": "Wally Seppala", "score": 95.00, "preferences": ["511504"]},
{"name": "Cristi Authement", "score": 90.00, "preferences": ["511207"]},
{"name": "Yadira Millwood", "score": 83.15, "preferences": ["511795+2.5"]},
{"name": "Abram Bloomer", "score": 98.00, "preferences": ["511207","511795"]}]
```

Students' degree preferences are described in a semicolon-seperated list of unique degree codes ordered by preference. Preferences suffixed with `+n` indicate that the student has *flexible entry* for that degree and receives that many bonus marks when considered **for that degree only**.

Bonuses may increase a score up to a maximum of 99.95. If the bonus pushes a score sbove the cutoff mark for a degree with no places available, the lowest scoring studenti is evicted to make way, and the degree cutoff is adjusted to the next lowest score (which may be the bonus-adjusted score of the new student). The evicted student is reconsidered for other degree as an appropriate for their score and any bonuses.

In `DegreeDistribution.java`, the `distribute` method takes in two parameters: the name of the degrees JSON file and the name of the students JSON file. and returns a JSON string of the format `{"degrees": [...], "students": [...]}`.

* The array of degrees is odered lexographically by their code. Each degree has a code, a cutoff, a vacancies boolean, and the number of students offered positions in the degree.
* A list of students, ordered by their original mark to 2 decimal places, with the degree code they have been offered.

If a student does not receive a degree place, or a degree has no cutoff, you should return `-` in the relevant location.

For all parts of this question that could result in tie breaking, including offers, eviction and final output, break any mark ties in ascending alphabetical order of student names. That is, if Amy and Zoe have the same effective score for a degree, Amy should be offered before Zoe, and Zoe should be evicted before Amy.

Given the example files above, your program should produce the following:

```javascript
{"degrees": [
    {"code": 422000, "name": "Bachelor of Arts","institution": "University of New South Wales", "cutoff": 81.15, "offers": 2, "vacancies": true},
    {"code": 422300, "name": "Bachelor of Social Research and Policy","institution": "University of New South Wales", "cutoff": 86.50, "offers": 1, "vacancies": true},
    {"code": 423600, "name": "Bachelor of Planning","institution": "University of New South Wales", "cutoff": "-", "offers": 0, "vacancies": true},
    {"code": 511207, "name": "Bachelor of Arts (Media and Communications)","institution": "University of Sydney", "cutoff": 96.00, "offers": 2, "vacancies": false},
    {"code": 511504, "name": "Bachelor of Commerce","institution": "University of Sydney", "cutoff": 95.00, "offers": 1, "vacancies": false},
    {"code": 511795, "name": "Bachelor of Computer Science and Technology","institution": "University of Sydney", "cutoff": 83.15, "offers": 3, "vacancies": true}
],
"students": [
    {"name": "Abram Bloomer", "score": 98.00, "offer": 511207},
    {"name": "Wally Seppala", "score": 95.00, "offer": 511504},
    {"name": "Jeffie Honaker", "score": 94.50, "offer": 511795},
    {"name": "Ivan Connolly", "score": 91.00, "offer": 511207},
    {"name": "Cristi Authement", "score": 90.00, "offer": "-"},
    {"name": "Claudia Zingaro", "score": 84.50, "offer": 422300},
    {"name": "Hyun Castleberry", "score": 83.15, "offer": 511795},
    {"name": "Yadira Millwood", "score": 83.15, "offer": 511795},
    {"name": "Floria Rozar", "score": 82.25, "offer": 422000},
    {"name": "Leland Acheson", "score": 81.15, "offer": 422000}
]}
```

Within the two input files, you can assume that the degree codes will be unique, as are the names of students. The degree preference codes are guaranteed to be in the degrees JSON file.

Design and implement an object-oriented solution to this problem. You are given a near-complete suite of JUnit tests.

**Extension Challenge**: Determine the edge case missing from the test suite, add it in and make sure your code passes.

Problem sourced from Grok Learning NCSS Challenge (Advanced), 2017 and adapted for Java.


## Submission

To submit, make a tag to show that your code at the current commit is ready for your submission using the command:

```bash
$ git tag -fa submission -m "Submission for Lab-02"
$ git push -f origin submission
```

Or, you can create one via the GitLab website by going to **Repository > Tags > New Tag**.
We will take the last commit on your master branch before the deadline for your submission.

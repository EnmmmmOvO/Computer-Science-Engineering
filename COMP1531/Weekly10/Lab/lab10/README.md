# Lab 10

## Due: Week **10**, Sunday, 5:00 pm

## Value: 2 marks

## Aim

* Practise under the take-home exam infrastructure
* Revise python programming skills
* Gain experience writing property-based tests
* Writing non-trivial generators

## Preamble

This lab has been set up in the same way your take-home exam will be. This means that:

* You have been given access to this repo only for the duration of the assessment. You will lose access once the deadline passes.
* Whatever is in this repo at the deadline will be considered your submission.
* In case of technical failure, it's important that you **commit and push regularly**. You will not be assessed on the quality of your commit messages.
* Questions are automarked. Please follow all instructions exactly and check that you have done so after you complete each exercise. Failure to do so could result in 0 for a particular exercise.

The following do not apply to this lab, but will apply to the final exam:

* You cannot post to the course forum jpublically during the exam.
* For any written questions, ensure your answers are of the suggested length.

The exercises in this lab are based on material from week 7 and week 9. The actual exam will of course contain exercises from all weeks of the course.

## Hints

Some useful things to know:

* You can convert any iterator or iterable into a list with the `list(...)` function.
* You may wish to refer to the documentation for [sets in python](https://docs.python.org/3.7/library/stdtypes.html#set-types-set-frozenset).
* The `integers()` strategy provided by the hypothesis library supports setting minimum and maximum values for the integers it generates with the `min_value` and `max_value` keyword arguments. Similarly, the `text()` strategy has the keyword arguments `max_size` and `min_size` that control the length of strings it will produce. You may need these to ensure your tests complete in a reasonable amount of time.
* Marks are not awarded for efficiency.

## Part A

Tests are given for these exercises. If you can pass the given tests, you should receive the marks. No further testing is required. When marking, additional tests may be used, but only to ensure you're not trying to cheat the tests by hardcoding test data in your solution.

1. In `bad_interview.py`, complete the definition of the generator according to its documentation. A test is in `bad_interview_test.py`.
2. In `neighbours.py`, complete the definition of the generator according to its documentation. Some tests are in `neighbours_test.py`.

## Part B

Some tests may given for these questions, but you will also need to write your own tests. **Ensure all your tests can be run in under 1 minute**. Marking will be based both on the correctness of your solution and the effectiveness of your tests. The latter will be measured by code coverage as well as running them against other, possibly incorrect, solutions. Your tests should fail for incorrect solutions and pass for correct ones. **Write your tests only in the included test file. Do not create additional files. All your tests must be black-box tests in order to be run against other implementations.**

1. In `divisors.py`, complete the definition of the function according to its documentation. A simple test is located in `divisors_test.py`. Consider what property, or properties, this function has and write them as property-based tests.
2. In `inverse.py`, complete the definition of the function according to its documentation. Consider what property, or properties, would form a **complete** definition of this function and write them as property-based tests in `inverse_test.py`.
3. In `factors.py`, complete the definition of `factors()` according to its documentation. Consider what property, or properties, would form a **complete** definition of this generator and write them as property-based tests in `factors_test.py`.
4. In `permutations.py`, complete the definition of the function according to its documentation. Consider what property, or properties, would form a **complete** definition of this function and write them as property-based tests in `permutations_test.py`. You cannot use `itertools.permutation` to complete this exercise. You must implement the function and tests without it.
5. **Challenge bonus question (only attempt if you have completed all other questions)** In `balanced.py`, complete the definition of the function according to its documentation. Consider what property, or properties, should apply to this function and write them as property-based tests in `balanced_test.py`. If you want an additional challenge, try to determine whether your properties form a complete definition, and, if not, if you can make a set of properties that do.

## Submission

**Make sure all the work you wish to submit has been committed and pushed to the remote repo**. Failure to do this for this lab will result in a mark of 0. Failure to do so in the exam could result in you failing the course.

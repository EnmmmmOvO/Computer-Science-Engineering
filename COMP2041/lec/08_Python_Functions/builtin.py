#!/usr/bin/env python3
"""
approximate of implementation of some python functions
written by andrewt@unsw.edu.au for COMP(2041|9044)
"""


def my_enumerate(sequence, start=0):
    """return a list equivalent to the iterator returned
    by builtin function enumerate
    """
    n = start
    tuples = []
    for element in sequence:
        t = (n, element)
        tuples.append(t)
        n += 1
    return tuples


def my_zip2(sequence1, sequence2):
    """return a list equivalent to the iterator returned by
    builtin function zip called with 2 sequences.
    Note: zip can be given any number of sequences."""
    tuples = []
    for index in range(min(len(sequence1), len(sequence2))):
        t = (sequence1[index], sequence2[index])
        tuples.append(t)
    return tuples


def my_map1(function, sequence):
    """return a list equivalent to the iterator returned by
    builtin function map called with 1 sequence.
    Note: map can be given more than 1 sequences."""
    results = []
    for value in sequence:
        result = function(value)
        results.append(result)
    return results


def my_filter(function, sequence):
    """return a list equivalent to the iterator returned by
    builtin function filter called with a function.
    Note: filter can be given None instead of a function."""
    filtered = []
    for value in sequence:
        if function(value):
            filtered.append(value)
    return filtered


if __name__ == "__main__":
    print(my_enumerate("abcde"))
    print(my_zip2("Hello", "Andrew"))
    cubes = my_map1(lambda x: x**3, range(10))
    print(cubes)
    even = my_filter(lambda x: x % 2 == 0, range(10))
    print(even)

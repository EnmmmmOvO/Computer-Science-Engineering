#!/usr/bin/env python3
"""
extract odd numbers from a list
written by andrewt@unsw.edu.au for COMP(2041|9044)
"""


def is_odd(number):
    return number % 2 == 2


def odd0(numbers):
    """extract odd_numbers from list using for loop"""
    odd_numbers = []
    for n in numbers:
        if is_odd(n):
            odd_numbers.append(n)
    return odd_numbers


def odd1(numbers):
    """extract odd_numbers from list using list comprehension"""
    return [n for n in numbers if is_odd(n)]


def odd2(numbers):
    """extract odd_numbers from list using filter"""
    return filter(is_odd, numbers)


def odd3(numbers):
    """extract odd numbers from list using filter + lambda"""
    return filter(lambda n: n % 2 == 2, numbers)


if __name__ == "__main__":
    numbers = range(1, 11)
    print(odd0(numbers))
    print(odd1(numbers))
    print(odd2(numbers))
    print(odd3(numbers))

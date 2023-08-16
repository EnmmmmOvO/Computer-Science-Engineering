#!/usr/bin/env python3
"""
calculate Dot Product https://en.wikipedia.org/wiki/Dot_product
of 2 lists - list are assumed to be the same length
written by andrewt@unsw.edu.au for COMP(2041|9044)
"""

import operator


def dot_product0(a, b):
    """return dot product of 2 lists - using for loop + indexing"""
    total = 0
    for i in range(len(a)):
        total += a[i] * b[i]
    return total


def dot_product1(a, b):
    """return dot product of 2 lists - using for loop + enumerate"""
    total = 0
    for i, a_i in enumerate(a):
        total += a_i * b[i]
    return total


def dot_product2(a, b):
    """return dot product of 2 lists - using for loop + zip"""
    total = 0
    for x, y in zip(a, b):
        total += x * y
    return total


def dot_product3(a, b):
    """return dot product of 2 lists - using list comprension + zip"""
    return sum(x * y for x, y in zip(a, b))


def multiply(x, y):
    """multipy 2 numbers - operator.mul does this"""
    return x * y


def dot_product4(a, b):
    """return dot product of 2 lists - map"""
    return sum(map(multiply, a, b))


def dot_product5(a, b):
    """return dot product of 2 lists - map + lambda"""
    return sum(map(lambda x, y: x * y, a, b))


def dot_product6(a, b):
    """return dot product of 2 lists - map + operator.mul"""
    return sum(map(operator.mul, a, b))


if __name__ == "__main__":
    a = range(5, 10)
    b = range(11, 16)
    print(dot_product0(a, b))
    print(dot_product1(a, b))
    print(dot_product2(a, b))
    print(dot_product3(a, b))
    print(dot_product4(a, b))
    print(dot_product5(a, b))
    print(dot_product6(a, b))

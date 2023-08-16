#! /usr/bin/env python3

"""
Reads lines of input until end-of-input
Print "snap!" if two consecutive lines are identical

written by d.brotherston@unsw.edu.au as a COMP(2041|9044) lecture example
translated from perl written by andrewt@cse.unsw.edu.au
"""

last = None

while True:
    try:
        curr = input("Enter line: ")
    except EOFError:
        print()
        break

    if curr == last:
        print("Snap!")
        break

    last = curr

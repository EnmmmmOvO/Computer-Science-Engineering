#!/usr/bin/python3
# written by andrewtunsw.edu.au as a COMP(2041|9044) lecture example

# Find the positive integers among input text
# print their sum and mean

# Note regexp to split on non-digits
# Note check to handle empty string from split
# Only positive integers handled

import re, sys

input_as_string = sys.stdin.read()

numbers = re.split(r"\D+", input_as_string)

total = 0
n = 0
for number in numbers:
    if number:
        total += int(number)
        n += 1

if numbers:
    print(f"{n} numbers, total {total}, mean {total / n:.1f}")

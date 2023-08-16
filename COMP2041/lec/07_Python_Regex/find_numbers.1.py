#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) lecture example

# Find the positive integers among input text
# print their sum and mean

# Note regexp to match number -?\d+\.?\d*
# match postive & integers & floating-point numbers

import re, sys

input_as_string = sys.stdin.read()

numbers = re.findall(r"-?\d+\.?\d*", input_as_string)

n = len(numbers)
total = sum(float(number) for number in numbers)

if numbers:
    print(f"{n} numbers, total {total}, mean {total / n:.1f}")

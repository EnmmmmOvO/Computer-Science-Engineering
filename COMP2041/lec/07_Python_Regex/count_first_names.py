#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) lecture example

# count how many people enrolled have each first name
# implemented using regular expressions, a set & counters

import collections
import re

ENROLLMENTS_FILE = "enrollments.txt"

# enrollments.txt contains synthetic course enrollments
# with fields separated by | e.g.:
# COMP1911|5218563|Syed, Hugh Ali|3707/1|COMPAS|090.667|22T2|20010419|M

already_counted = set()
first_name_count = collections.Counter()
with open(ENROLLMENTS_FILE, encoding="utf-8") as f:
    for line in f:
        _, student_number, full_name = line.split("|")[0:3]

        if student_number in already_counted:
            continue
        already_counted.add(student_number)

        if m := re.match(r".*,\s+(\S+)", full_name):
            first_name = m.group(1)
            first_name_count[first_name] += 1

# put the count first in the tuples so sorting orders on count before name
count_name_tuples = [(c, f) for (f, c) in first_name_count.items()]

# print first names in decreasing order of popularity
for (count, first_name) in sorted(count_name_tuples, reverse=True):
    print(f"{count:4} {first_name}")

#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) lecture example

# count people enrolled in courses
# implemented using regular expressions & dicts

import re

COURSE_CODES_FILE = "course_codes.tsv"
ENROLLMENTS_FILE = "enrollments.txt"

# course_codes.tsv contains tab separated UNSW course and names, e..g
# ACCT1501  Accounting & Financial Mgt 1A

# enrollments.txt contains synthetic course enrollments
# with fields separated by | e.g.:
# COMP1911|5218563|Syed, Hugh Ali|3707/1|COMPAS|090.667|22T2|20010419|M

course_names = {}
with open(COURSE_CODES_FILE, encoding="utf-8") as f:
    for line in f:
        if m := re.match(r"(\S+)\s+(.*\S)", line):
            course_names[m.group(1)] = m.group(2)

enrollments_count = {}
with open(ENROLLMENTS_FILE, encoding="utf-8") as f:
    for line in f:
        course_code = re.sub(r"\|.*\n", "", line)
        if course_code not in enrollments_count:
            enrollments_count[course_code] = 0
        enrollments_count[course_code] += 1

for (course_code, enrollment) in sorted(enrollments_count.items()):
    # if no name for course_code use ???
    name = course_names.get(course_code, "???")
    print(f"{enrollment:4} {course_code} {name}")

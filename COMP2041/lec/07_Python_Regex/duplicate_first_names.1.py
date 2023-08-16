#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) lecture example

# Report cases where there are more than 5 people
# of the same first name enrolled in a course
# implemented using a defaultdict & counter from collections and string operations

import collections
import sys

REPORT_MORE_THAN_STUDENTS = 5
ENROLLMENTS_FILE = "enrollments.txt"

# enrollments.txt contains synthetic course enrollments
# with fields separated by | e.g.:
# COMP1911|5218563|Syed, Hugh Ali|3707/1|COMPAS|090.667|22T2|20010419|M

course_first_name_count = collections.defaultdict(collections.Counter)
with open(ENROLLMENTS_FILE, encoding="utf-8") as f:
    for line in f:
        course_code, _, full_name = line.split("|")[0:3]
        given_names = full_name.split(",")[1].strip()
        first_name = given_names.split(" ")[0]
        course_first_name_count[course_code][first_name] += 1


for course in sorted(course_first_name_count.keys()):
    for (first_name, count) in course_first_name_count[course].items():
        if count > REPORT_MORE_THAN_STUDENTS:
            print(course, "has", count, "students named", first_name)

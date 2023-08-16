#!/usr/bin/env python3

import sys
import subprocess
import re

if len(sys.argv) != 2:
    print("Usage: courses_requests.py <course code>")
    sys.exit(1)

course_code = sys.argv[1]
text = subprocess.run(['curl', '--location', '--silent',
                     f'http://www.timetable.unsw.edu.au/2023/{course_code}KENS.html'],
                      capture_output=True, text=True)

list = dict()
for i in  re.findall(rf'{course_code}\d{{4}}.html.+', text.stdout):
    course = i.split('.html')[0]
    description = i.split('>')[1].split('<')[0]
    if course != description:
        list[course] = description

for i, j in sorted(list.items()):
    print(f'{i} {j}')







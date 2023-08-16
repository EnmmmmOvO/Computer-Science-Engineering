#!/usr/bin/env python3

import sys
import urllib.request
from bs4 import BeautifulSoup
import re

if len(sys.argv) != 2:
    print("Usage: courses_requests.py <course code>")
    sys.exit(1)

course_code = sys.argv[1]
pattern = re.compile(rf'{course_code}\d{{4}}')

list = dict()
for i in BeautifulSoup(urllib.request.urlopen(f'http://www.timetable.unsw.edu.au/2023/{course_code}KENS.html').
                               read().decode(), 'html.parser').findAll('a', href=pattern):
    course = i.get('href').split('.')[0]
    description = i.text
    if course != description:
        list[course] = description

for i, j in sorted(list.items()):
    print(f'{i} {j}')


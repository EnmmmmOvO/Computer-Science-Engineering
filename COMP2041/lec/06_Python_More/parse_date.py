#!/usr/bin/python3

# This would be better done using the standard date module

import subprocess

p = subprocess.run(["date"], capture_output=True, text=True)

if p.returncode != 0:
    print(p.stderr)
    exit(1)

weekday, day, month, year, time, timezone = p.stdout.split()
print(f"{year} {month} {day}")

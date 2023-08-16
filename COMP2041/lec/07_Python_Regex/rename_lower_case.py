#!/usr/bin/python3

# written by andrewt@unsw.edu.au for COMP(2041|9044)
#
# Change the names of the specified files to lower case.
# (simple version of the perl utility rename)

import os
import sys

for old_pathname in sys.argv[1:]:
    new_pathname = old_pathname.lower()
    if new_pathname == old_pathname:
        continue
    if os.path.exists(new_pathname):
        print(f"{sys.argv[0]}: '{new_pathname}' exists", file=sys.stderr)
        continue
    try:
        os.rename(old_pathname, new_pathname)
    except OSError as e:
        print(f"{sys.argv[0]}: '{new_pathname}' {e}", file=sys.stderr)

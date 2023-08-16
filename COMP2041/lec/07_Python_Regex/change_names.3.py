#!/usr/bin/python3
# written by andrewtunsw.edu.au as a COMP(2041|9044) lecture example

# For each file given as argument replace occurrences of Hermione
# allowing for some misspellings with Harry and vice-versa.
# Relies on Zaphod not occurring in the text.

# modified text is stored in a single string then file over-written

import re, sys, os

for filename in sys.argv[1:]:
    changed_lines = []
    with open(filename) as f:
        text = f.read()
    changed_text = re.sub(r"Herm[io]+ne", "Zaphod", text)
    changed_text = changed_text.replace("Harry", "Hermione")
    changed_text = changed_text.replace("Zaphod", "Harry")
    with open(filename, "w") as g:
        g.write("".join(changed_text))

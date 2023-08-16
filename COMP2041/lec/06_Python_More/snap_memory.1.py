#!/usr/bin/python3
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

# Check if we've seen lines read from stdin,
# using a set.
# Print snap! if a line has been seen previously.
# Exit if an empty line is entered

lines_seen = set()
while True:
    try:
        line = input("Enter line: ")
    except EOFError:
        break
    if line in lines_seen:
        print("Snap!")
    else:
        lines_seen.add(line)

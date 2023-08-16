#!/usr/bin/python3

# Simple uniq emulation for a COMP2041/9044 lecture example
# andrewt@unsw.edu.au

import sys


def process_stream(stream):
    """
    copy stream to stdout except for repeated lines
    """
    last_line = None
    for line in stream:
        if last_line is None or line != last_line:
            print(line, end='')
        last_line = line


def main():
    """
    process files given as arguments, if no arguments process stdin
    """
    if not sys.argv[1:]:
        process_stream(sys.stdin)
    else:
        for pathname in sys.argv[1:]:
            with open(pathname, 'r') as f:
                process_stream(f)


if __name__ == '__main__':
    main()

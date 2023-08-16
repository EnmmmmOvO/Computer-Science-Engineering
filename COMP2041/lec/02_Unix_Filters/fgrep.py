#!/usr/bin/python3

# Simple fgrep emulation for a COMP2041/9044 lecture example
# andrewt@unsw.edu.au

import sys


def process_stream(f, name, substring):
    """
    print lines containing substring
    """
    for (line_number, line) in enumerate(f, start=1):
        if substring in line:
            print(f'{name}:{line_number}:{line}', end='')


def main():
    """
    process files given as arguments, if no arguments process stdin
    """
    if len(sys.argv) == 2:
        process_stream(sys.stdin, "<stdin>", sys.argv[1])
    elif len(sys.argv) > 2:
        for pathname in sys.argv[2:]:
            with open(pathname, 'r') as f:
                process_stream(f, pathname, sys.argv[1])


if __name__ == '__main__':
    main()

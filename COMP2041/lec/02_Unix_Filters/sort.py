#!/usr/bin/python3

# Simple sort emulation for a COMP2041/9044 lecture example
# andrewt@unsw.edu.au

import sys


def process_stream(f):
    """
    print lines of stream in sorted order
    """
    print("".join(sorted(f)), end="")


def main():
    """
    process files given as arguments, if no arguments process stdin
    """
    if len(sys.argv) == 1:
        process_stream(sys.stdin)
    else:
        with open(sys.argv[1], 'r') as f:
            process_stream(f)


if __name__ == '__main__':
    main()

#!/usr/bin/python3

# Simple /bin/echo emulation for a COMP2041/9044 lecture example
# andrewt@cse.unsw.edu.au

import sys


def main():
    """
    print arguments to stdout
    """
    print(' '.join(sys.argv[1:]))


if __name__ == '__main__':
    main()


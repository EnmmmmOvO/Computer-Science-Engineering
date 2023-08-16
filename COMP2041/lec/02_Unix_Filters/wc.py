#!/usr/bin/python3

# Simple wc emulation for a COMP2041/9044 lecture example
# andrewt@unsw.edu.au

import sys
import os


def process_stream(stream):
    """
    count lines, words, chars in stream
    """
    lines = 0
    words = 0
    characters = 0
    for line in stream:
        lines += line.endswith(os.linesep)
        words += len(line.split())
        characters += len(line)
    print(f"{lines:>6} {words:>6} {characters:>6}", end="")


def main():
    """
    process files given as arguments, if no arguments process stdin
    """
    if not sys.argv[1:]:
        process_stream(sys.stdin)
    else:
        for pathname in sys.argv[1:]:
            with open(pathname, "r") as f:
                process_stream(f)
                print(f" {pathname}")


if __name__ == "__main__":
    main()

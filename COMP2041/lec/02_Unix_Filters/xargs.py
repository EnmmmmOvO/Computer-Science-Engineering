#!/usr/bin/python3

# Simple xargs emulation for a COMP2041/9044 lecture example
# andrewt@unsw.edu.au

import subprocess
import sys

# the real xargs runs the command multiple times if input is large
# the real xargs treats quotes specially


def main():
    input_words = [w for line in sys.stdin for w in line.split()]
    command = sys.argv[1:]
    subprocess.run(command + input_words)


if __name__ == "__main__":
    main()

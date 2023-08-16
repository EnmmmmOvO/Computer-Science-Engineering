#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)

# compile the files of a muti-file C program in parallel
# use create_1001_file_C_program.sh to create suitable test data

# on Linux getconf will tell us how many cores the machine has
# otherwise assume 8

max_processes=$(getconf _NPROCESSORS_ONLN 2>/dev/null) ||
    max_processes=8

# NOTE: this breaks if a filename contains whitespace or quotes

echo "$@"|
xargs --max-procs=$max_processes --max-args=1 clang -c

clang -o binary -- *.o

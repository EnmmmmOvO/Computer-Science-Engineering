#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)

# compile the files of a muti-file C program in parallel
# use create_1001_file_C_program.sh to create suitable test data

parallel clang -c '{}' ::: "$@"

clang -o binary -- *.o

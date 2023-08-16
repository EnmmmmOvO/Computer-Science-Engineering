#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)

# compile the files of a multi-file C program in parallel
# use create_1001_file_C_program.sh to create suitable test data

# find's -print0 option terminates pathnames with a '\0'
# xargs's --null option expects '\0' terminated input
# as '\0' can not appear in file names this can handle any filename

# on Linux getconf will tell us how many cores the machine has
# if getconf assume 8

max_processes=$(getconf _NPROCESSORS_ONLN 2>/dev/null) ||
    max_processes=8

find "$@" -print0|
xargs --max-procs=$max_processes --max-args=1  --null clang -c

clang -o binary -- *.o

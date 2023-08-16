#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)

# compile the files of a muti-file C program in parallel
# use create_1001_file_C_program.sh to create suitable test data

# On a CPU with n cores this can be (nearly) n times faster

# If there are large number of C files we
# may exhaust memory or operating system resources


for f in "$@"
do
    clang -c "$f" &
done

# wait for the incremental compiles to finish
# and then compile .o files into single binary
wait
clang -o binary -- *.o

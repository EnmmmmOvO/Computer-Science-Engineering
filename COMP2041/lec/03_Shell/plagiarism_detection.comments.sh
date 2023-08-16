#!/bin/dash

# written by andrewt@unsw.edu.au for COMP(2041|9044)
# Improved version of plagiarism_detection.simple_diff.sh

# The substitution s/\/\/.*// removes // style C comments.
# This means changes in comments won't affect comparisons.

# Note use of temporary files

TMP_FILE1=/tmp/plagiarism_tmp1$$
TMP_FILE2=/tmp/plagiarism_tmp2$$


for file1 in "$@"
do
    for file2 in "$@"
    do
        test "$file1" = "$file2" &&
            break # avoid comparing pairs of assignments twice

        sed 's/\/\/.*//' "$file1" >$TMP_FILE1
        sed 's/\/\/.*//' "$file2" >$TMP_FILE2

        if diff -i -w $TMP_FILE1 $TMP_FILE2 >/dev/null
        then
            echo "$file1 is a copy of $file2"
        fi

    done
done

rm -f $TMP_FILE1 $TMP_FILE2

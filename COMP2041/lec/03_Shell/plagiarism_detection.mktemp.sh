#!/bin/dash

# written by andrewt@unsw.edu.au for COMP(2041|9044)
# Improved version of plagiarism_detection.reordering.sh
# with robust creation and removal of temporary files

TMP_FILE1=$(mktemp)
TMP_FILE2=$(mktemp)
trap 'rm -f $TMP_FILE1 $TMP_FILE2;exit' INT TERM EXIT

substitutions='
    s/\/\/.*//
    s/"[^"]"/s/g
    s/[a-zA-Z_][a-zA-Z0-9_]*/v/g'

for file1 in "$@"
do
    for file2 in "$@"
    do
        test "$file1" = "$file2" &&
            break # avoid comparing pairs of assignments twice

        sed "$substitutions" "$file1"|sort >$TMP_FILE1
        sed "$substitutions" "$file2"|sort >$TMP_FILE2

        if diff -i -w $TMP_FILE1 $TMP_FILE2 >/dev/null
        then
            echo "$file1 is a copy of $file2"
        fi
    done
done


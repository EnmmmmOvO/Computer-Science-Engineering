#!/bin/dash

set -x
# written by andrewt@unsw.edu.au for COMP(2041|9044)
#
# Run as plagiarism_detection.simple_diff.sh <files>
# Report if any of the files are copies of each other
#
# Note use of diff -iw so changes in white-space or case
# are ignored

for file1 in "$@"
do
    for file2 in "$@"
    do
        test "$file1" = "$file2" &&
            break # avoid comparing pairs of assignments twice

        if diff -i -w "$file1" "$file2" >/dev/null
        then
            echo "$file1 is a copy of $file2"
        fi

    done
done

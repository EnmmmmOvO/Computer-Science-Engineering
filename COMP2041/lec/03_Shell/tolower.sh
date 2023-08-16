#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)
#
# Change the names of the specified files to lower case.
# (simple version of the perl utility rename)
#
# Note use of test to check if the new filename is unchanged.
#
# Note the double quotes around $filename so filenames
# containing spaces are not broken into multiple words

# Note the use of mv -- to stop mv interpreting a
# filename beginning with - as an option

# Note files named -n or -e still break the script
# because echo will treat them as an option,

if test $# = 0
then
    echo "Usage $0: <files>" 1>&2
    exit 1
fi

for filename in "$@"
do
    new_filename=$(echo "$filename" | tr '[:upper:]' '[:lower:]')

    test "$filename" = "$new_filename" &&
        continue

    if test -r "$new_filename"
    then
        echo "$0: $new_filename exists" 1>&2
    elif test -e "$filename"
    then
        mv -- "$filename" "$new_filename"
    else
        echo "$0: $filename not found" 1>&2
    fi

done

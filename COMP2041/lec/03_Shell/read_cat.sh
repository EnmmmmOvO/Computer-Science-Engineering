#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)
# over-simple /bin/cat emulation using read

# setting the special variable IFS to the empty string
# stops white space being stripped

for file in "$@"
do
    while IFS= read -r line
    do
        echo "$line"
    done <$file
done

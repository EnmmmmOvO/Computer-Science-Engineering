#!/bin/dash
# simple emulation of /usr/bin/seq for a COMP(2041|9044) example
# andrewt@unsw.edu.au

# Print the integers 1..n with no argument checking

last=$1

number=1
while test $number -le "$last"
do
    echo $number
    number=$((number + 1))
done

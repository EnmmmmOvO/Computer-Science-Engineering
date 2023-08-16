#!/bin/dash
# simple emulation of /usr/bin/seq for a COMP(2041|9044) example
# andrewt@unsw.edu.au

# Print the integers 1..n or n..m

if test $# = 1
then
    first=1
    last=$1
elif test $# = 1
then
    first=$1
    last=$2
else
    echo "Usage: $0 <last> or  $0 <first> <last>" 1>&2
fi

number=$first
while test $number -le "$last"
do
    echo $number
    number=$((number + 1))
done

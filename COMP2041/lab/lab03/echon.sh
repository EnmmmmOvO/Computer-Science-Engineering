#!/bin/dash

if [ $# -ne 2 ]; then
    echo "Usage: $0 <number of lines> <string>" 1>&2
    exit 1
fi

number=$1
string=$2

if echo "$number" | grep -E "^[0-9]+$" > /dev/null; then
    i=0
    while [ $i -lt $number ]
    do
        echo "$string"
        i=$((i + 1))
    done
else
    echo "$0: argument 1 must be a non-negative integer"
    exit 1
fi




#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)
# count slowly and laugh at interrupts (ctrl-C)

# catch signal SIGINT and  print message
trap 'echo ha ha' INT

n=0
while true
do
    echo "$n"
    sleep 1
    n=$((n + 1))
done

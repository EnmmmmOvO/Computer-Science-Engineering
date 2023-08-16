#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)
# print positive integers for one second real time


# catch signal SIGTERM, print message and exit
trap 'echo loop executed $n times in 1 second; exit 0' TERM

# launch a sub-shell that will terminate
# this process in 1 second
my_process_id=$$
(sleep 1; kill $my_process_id) &

n=0
while true
do
    n=$((n + 1))
done

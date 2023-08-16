#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)
# print positive integers for one second real time

my_process_id=$$

# launch a asynchronous sub-shell that will kill
# this process in a second
(sleep 1; kill $my_process_id) &

i=0
while true
do
    echo $i
    i=$((i + 1))
done

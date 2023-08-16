#!/bin/dash

status=off
while test $status != on
do
    echo status is $status
    status=on
done

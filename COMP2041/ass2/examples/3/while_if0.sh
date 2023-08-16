#!/bin/dash

status=off
while test "$status" != on
do
    echo "status is $status"
    if test "$status" = "half on"
    then
        status="on"
    else
        status="half on"
    fi
done

#!/bin/dash

row=1
while test $row != 11111111111
do
    echo $row
    row=1$row
done

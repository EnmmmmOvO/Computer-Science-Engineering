#!/bin/dash

x='###'
while test $x != '########'
do
    y='#'
    while test $y != $x
    do
        echo $y
        y="${y}#"
    done
    x="${x}#"
done

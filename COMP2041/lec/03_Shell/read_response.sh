#!/bin/dash
# written by andrewt@unsw.edu.au for COMP(2041|9044)
# demonstrate simple use of read

echo -n "Do you like learning Shell? "
read answer

case "$answer" in
[Yy]*)
    response=":)"
    ;;

[Nn]*)
    response=":("
    ;;

*)
    response="??"
esac

echo "$response"

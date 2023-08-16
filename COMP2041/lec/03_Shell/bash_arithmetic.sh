#!/bin/bash

# written by andrewt@unsw.edu.au for COMP(2041|9044)
# print print numbers < 1000

# Rewritten to use bash arithmetic extension (())
# This makes the program more readable but less portable.

is_prime() {
    local n i
    n=$1
    i=2
    while ((i < n))
    do
        if ((n % i == 0))
        then
            return 1
        fi
        i=$((i + 1))
    done
    return 0
}

i=0
while ((i < 1000))
do
    is_prime $i && echo $i
    i=$((i + 1))
done

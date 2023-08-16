#!/bin/dash

# written by andrewt@unsw.edu.au for COMP(2041|9044)
# Improved version of plagiarism_detection.reordering.sh

# Note use sha256sum to calculate a Cryptographic hash of the modified file
# https://en.wikipedia.org/wiki/SHA-2
# and  use of sort && uniq to find files with the same hash
# This allows execution time linear in the number of files
# We could use a faster less secure hashing fucntion instead of sha2 

substitutions='
    s/\/\/.*//
    s/"[^"]"/s/g
    s/[a-zA-Z_][a-zA-Z0-9_]*/v/g'

for file in "$@"
do
    sha2hash=$(sed "$substitutions" "$file"|sort|sha256sum)
    echo "$sha2hash $file"
done|
sort|
uniq -w32 -d --all-repeated=separate|
cut -c36-

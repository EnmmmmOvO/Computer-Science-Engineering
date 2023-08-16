#!/bin/dash

# Count the number of time each different word occurs
# in the files given as arguments, or stdin if no arguments,
# e.g. word_frequency.sh dracula.txt
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

cat "$@" |                   # tr doesn't take filenames as arguments
tr '[:upper:]' '[:lower:]' | # map uppercase to lower case
tr ' ' '\n' |                # convert to one word per line
tr -cd "a-z'" |              # remove all characters except a-z and '
grep -E -v '^$' |            # remove empty lines
sort |                       # place words in alphabetical order
uniq -c |                    # count how many times each word occurs
sort -rn                     # order in reverse frequency of occurrence

# notes:
# - first 2 tr commands could be combined
# - sed 's/ /\n/g' could be used instead of tr ' ' '\n'
# - sed "s/[^a-z']//g" could be used instead of tr -cd "a-z'"

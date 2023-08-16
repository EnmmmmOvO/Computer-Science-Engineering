#!/bin/dash
# A simple shell script demonstrating access to arguments.
# written by andrewt@unsw.edu.au as a COMP(2041|9044) example

echo My name is "$0"
echo My process number is $$
echo I have $# arguments

# your not going to see any difference unless you use these in a loop
echo My arguments separately are $*
echo My arguments together are "$*"
echo My arguments separately are $@
echo My arguments as quoted are "$@"

echo My 5th argument is "'$5'"
echo My 10th argument is "'${10}'"
echo My 255th argument is "'${255}'"

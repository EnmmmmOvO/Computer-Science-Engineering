#!/bin/dash

# written by andrewt@unsw.edu.au for COMP(2041|9044)


# securely & robustly create a new temporary directory
temporary_directory=$(mktemp -d /tmp/dir.XXXXXXXXXX)

# ensure temporary directory + all its contents removed on exit
trap 'rm -rf "$temporary_directory; exit"' INT TERM EXIT

# change working directory to the new temporary directory
cd "$temporary_directory" || exit 1

# we are now in an empty directory
# and create any number of files & directories
# which all will be removed by the trap above

# e.g. create one thousand empty files
seq 1 1000|xargs touch

# print current directory and list files
pwd
ls -l




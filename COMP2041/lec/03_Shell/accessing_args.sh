#! /bin/dash

#  $ ./accessing_args.sh one two "three  four"
#  Using $*:
#  one
#  two
#  three
#  four
#  Using "$*":
#  one two three four
#  Using "$@":
#  one
#  two
#  three four

echo 'Using $*:'
for a in $*
do
    echo "$a"
done

echo 'Using "$*":'
for a in "$*"
do
    echo "$a"
done

# This is the way to loop over command-line arguments
echo 'Using "$@":'
for a in "$@"
do
  echo "$a"
done


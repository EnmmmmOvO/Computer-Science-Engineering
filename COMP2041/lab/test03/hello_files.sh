#!/bin/dash

if [ "$#" != 2 ]; then
  echo "<Usage>: ${0} time content"
  exit 1
fi

time=$1
content="hello ${2}"
i=1

while [ "$i" -le "$time" ]; do
  echo "$content" > "hello${i}.txt"
  i=$((i + 1))
done
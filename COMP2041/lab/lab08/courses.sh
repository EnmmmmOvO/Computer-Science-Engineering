#!/bin/dash


if test $# -ne 1
then
    echo "Usage: $0 <coursecode>"
    exit 1
fi

course_code=$1

curl --location --silent "http://www.timetable.unsw.edu.au/2023/${course_code}KENS.html" |
grep -E -e "${course_code}[0-9]{4}.html" |
sed -E -e "s/^.*(${course_code}[0-9]{4}).html\">(.+)<\/a>.*$/\1 \2/g" |
sort |
uniq |
while read -r line; do
  a=$(echo "$line" | cut -d' ' -f1)
  b=$(echo "$line" | cut -d' ' -f2)
  if [ "$a" != "$b" ]; then
    echo "$line"
  fi
done


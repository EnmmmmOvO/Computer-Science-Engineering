#!/bin/dash

max=0
i=""

for file in "$@"; do
  if test ! -e "$file"; then
    continue
  fi

  tmp=$(wc -l "$file" | cut -d ' ' -f 1)
  if [ "$tmp" -gt "$max" ]; then
    max="$tmp"
    i="$file"
  fi
done

echo "$i"
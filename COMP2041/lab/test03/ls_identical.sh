#!/bin/dash

dict1=$1
dict2=$2

{
  ls -1 "$dict1";
  ls -1 "$dict2";
} | sort | uniq | while read -r file; do
  if test -e "${dict1}/${file}" && test -e "${dict2}/${file}" && [ "$(sha1sum "${dict1}/${file}" | cut -d ' ' -f 1)" = "$(sha1sum "${dict2}/${file}" | cut -d ' ' -f 1)" ]; then
    echo "$file"
  fi
done


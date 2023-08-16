#!/bin/dash

first="$1"
end="$2"

content=""

while [ "${first}" -lt "${end}" ]
do
    content="${content}${first}\n"
    first=$((first + 1))
done

echo "${content}${end}" > "$3"
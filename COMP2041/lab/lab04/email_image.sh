#!/bin/dash


for file in "$@"; do
    if test ! -e "$file"; then
        echo "${file} not exists"
        continue
    fi
    topic=$(echo "$file" | sed -E 's/\..*$/!/g')
    display "$file"
    echo -n "Address to e-mail this image to? "
    read -r email
    if echo "$email" | grep -qE '^[A-Za-z0-9._%+-]+@[A-Za-z0-9.-]+\.[A-Za-z]{2,}$'; then
        echo -n "Message to accompany image? "
        read -r message
        echo "$message" | mutt -s "$topic" -e 'set copy=no' -a "$file" -- "$email"
        echo "${file} sent to ${email}"
    else
        echo 'No email sent'
    fi
done
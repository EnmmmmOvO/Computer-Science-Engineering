#!/bin/dash

if [ $# -ne 2 ]; then
    echo "Usage: $0 <year> <course-prefix>" 1>&2
    exit 1
fi

if echo "$1" | grep -E "^[0-9]{4}$" > /dev/null; then
    if [ "$1" -lt "2005" ] || [ "$1" -gt "2023" ]; then
        echo "$0: argument 1 must be an integer between 2005 and 2023"
        exit 1
    elif [ "$1" -ge 2019 ]; then
        (curl -sL "https://www.handbook.unsw.edu.au/api/content/render/false/query/+unsw_psubject.implementationYear:${1}%20+unsw_psubject.studyLevel:undergraduate%20+unsw_psubject.educationalArea:${2}*%20+unsw_psubject.active:1%20+unsw_psubject.studyLevelValue:ugrd%20+deleted:false%20+working:true%20+live:true/orderby/unsw_psubject.code%20asc/limit/10000/offset/0" | jq -r '.contentlets[] | "\(.code) \(.title)"'; curl -sL "https://www.handbook.unsw.edu.au/api/content/render/false/query/+unsw_psubject.implementationYear:${1}%20+unsw_psubject.studyLevel:postgraduate%20+unsw_psubject.educationalArea:${2}*%20+unsw_psubject.active:1%20+unsw_psubject.studyLevelValue:pgrd%20+deleted:false%20+working:true%20+live:true/orderby/unsw_psubject.code%20asc/limit/10000/offset/0" | jq -r '.contentlets[] | "\(.code) \(.title)"') | sed 's/  / /g' | sort | uniq
    else
        curl --cipher 'DEFAULT:!DH' -sL "https://legacy.handbook.unsw.edu.au/assets/json/search/${1}data.json" | sed 's/\\n//g' | jq -r '.[] | select(.type == "courses") | "\(.filename)\(.code // "") \(.shortdescription // "") \(.career)"' | grep -E '^[A-Za-z0-9]+.html.*(undergraduate|postgraduate)$' | sed -E 's/ *(under|post)graduate$//' | sed 's/  / /g' | sed 's/  / /g' | sed -E -e 's/^([A-Za-z0-9]+).html$/\1/g' | sed 's/^.*.html//g'| grep -E "^$2" | sort | uniq 
    fi
else
    echo "$0: argument 1 must be an integer between 2005 and 2023"
    exit 1
fi


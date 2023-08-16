#!/bin/dash

if [ $# -ne 2 ]; then
    echo "Usage: $0 <year> <course-prefix>" 1>&2
    exit 1
fi

if echo $1 | grep -E "^[0-9]{4}$" > /dev/null; then
    if [ $1 -lt "2019" ] || [ $1 -gt "2023" ]; then
        echo "$0: argument 1 must be an integer between 2019 and 2023"
        exit 1
    fi
else
    echo "$0: argument 1 must be an integer between 2019 and 2023"
    exit 1
fi

(curl -sL "https://www.handbook.unsw.edu.au/api/content/render/false/query/+unsw_psubject.implementationYear:${1}%20+unsw_psubject.studyLevel:undergraduate%20+unsw_psubject.educationalArea:${2}*%20+unsw_psubject.active:1%20+unsw_psubject.studyLevelValue:ugrd%20+deleted:false%20+working:true%20+live:true/orderby/unsw_psubject.code%20asc/limit/10000/offset/0" | jq -r '.contentlets[] | "\(.code) \(.title)"'; curl -sL "https://www.handbook.unsw.edu.au/api/content/render/false/query/+unsw_psubject.implementationYear:${1}%20+unsw_psubject.studyLevel:postgraduate%20+unsw_psubject.educationalArea:${2}*%20+unsw_psubject.active:1%20+unsw_psubject.studyLevelValue:pgrd%20+deleted:false%20+working:true%20+live:true/orderby/unsw_psubject.code%20asc/limit/10000/offset/0" | jq -r '.contentlets[] | "\(.code) \(.title)"') | sed 's/  / /g' | sort | uniq
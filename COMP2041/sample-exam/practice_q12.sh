#!/bin/dash


target="$1"
echo $target

check=''
for i in 1 2 3 4; do
    for j in $target; do
        r=$(echo "$j" | sed -E -e 's/[a-z]([0-9])/\1/g')

        case $(echo "$j" | sed -E -e 's/([a-z])[0-9]/\1/g') in
        a)
            l=1
            ;;
        b)
            l=2
            ;;
        c)
            l=3
            ;;
        d)
            l=4
            ;;
        e)
            l=5
            ;;
        f)
            l=6
            ;;        
        g)
            l=7
            ;;
        *)
            l=8
        esac



        echo "$((l+1))"
        echo "$((r+1))"



    done
done 
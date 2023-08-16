#!/bin/dash

for i in "$@"; do
    if echo "$i" | grep -E '^.*\.[^.]+' > /dev/null; then
        echo "# ${i} already has an extension"
    else
        line=$(head -1 "$i")
        if ! echo "$line" | grep -E '^#!' > /dev/null; then
            echo "# ${i} does not have a #! line"
        elif echo "$line" | grep -F 'python' > /dev/null; then
            if test -e "${i}.py"; then
                echo "# ${i}.py already exists"
            else
                echo "mv ${i} ${i}.py"
            fi
        elif echo "$line" | grep -F 'perl' > /dev/null; then
            if test -e "${i}.pl"; then
                echo "# ${i}.pl already exists"
            else
                echo "mv ${i} ${i}.pl"
            fi
        elif echo "$line" | grep -F 'sh' > /dev/null; then
            if test -e "${i}.sh"; then
                echo "# ${i}.sh already exists"
            else
                echo "mv ${i} ${i}.sh"
            fi
        else
            echo "# ${i} no extension for #! line"
        fi
    fi
done
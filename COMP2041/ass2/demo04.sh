#!/bin/dash

# Variables
max_count="11111"
current_count="1"
echo "Starting the script with nested loops and conditions"

# Outer for loop
for fruit in apple banana cherry; do
    echo "Processing fruit: $fruit"

    # Inner while loop
    while [ $current_count -ne $max_count ]; do
        echo "Inside while loop, count: $current_count"

        # Inner if conditions
        if [ "$fruit" = "apple" ]; then
            for color in red green; do
                echo "Apple color: $color"
            done
        elif [ "$fruit" = "banana" ]; then
            for size in small large; do
                echo "Banana size: $size"
            done
        else
            for taste in sweet sour; do
                echo "Cherry taste: $taste"
            done
        fi

        current_count=1$current_count
    done

    # Reset the count for the next iteration
    current_count="1"
done

echo "Finished processing all fruits."

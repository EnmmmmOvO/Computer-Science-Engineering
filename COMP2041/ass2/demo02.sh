#!/bin/dash

echo "Case demo with strings:"
for fruit in apple banana cherry; do
    case $fruit in
        apple)
          echo "It is an apple"
          ;;
        banana)
          echo "It is a banana"
          ;;
        cherry)
          echo "It is a cherry"
          ;;
        *)
          echo "Unknown fruit"
          ;;
    esac
done

echo "Case demo with names:"
for person in Alice Bob Charlie; do
    case $person in
        Alice)
          echo "Hello Alice"
          a=1
          case $a in
            1|2|3|4)
              echo a
              ;;
            *)
              echo "not $a"
              ;;
          esac
          ;;
        Bob)
          echo "Hello Bob"
          ;;
        Charlie)
          echo "Hello Charlie"
          ;;
        *)
          echo "Who are you?"
          ;;
    esac
done

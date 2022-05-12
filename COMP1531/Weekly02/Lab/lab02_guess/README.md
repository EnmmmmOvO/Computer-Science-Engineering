# Lab02 - Exercise - Guess (2 points)

Open `guess.py`.

Write a program in `guess.py` that asks the user to think of a number between 1 and 100 (inclusive) and then repeatedly guesses a number, and gets the user to say whether the guess loo low, too high or correct. Example:

```bash
Pick a number between 1 and 100 (inclusive)
My guess is: 50
Is my guess too low (L), too high (H), or correct (C)?
L
My guess is: 75
Is my guess too low (L), too high (H), or correct (C)?
H
My guess is: 62
Is my guess too low (L), too high (H), or correct (C)?
C
Got it!
```

This program had the following standard input passed to it
```bash
L
H
C
```

Please note: When you (as the user) enter numbers, you should not be entering numbers randomly. You should be entering numbers in a way that minimises the number of guesses (effectively binary searching it as if you were playing this game with a friend and there was a price for the smallest number of guesses used).

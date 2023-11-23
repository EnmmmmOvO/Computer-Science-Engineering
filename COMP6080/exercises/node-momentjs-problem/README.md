## Use NodeJS and an NPM library to solve a time problem

Make a new NPM package in the `work` folder.

#### Part 1

Make a file `birth-days.js`. Using `momentjs` (install it via npm) you are going to list all of days of previous birthdays for that someone who is 14 years old, who also has a birthday of today. (i.e. whatever day the script is run).

This means to ask yourself, what day of the week was their birthday in 2019, 2018, 2017, ... etc etc until you reach the year they were born. Your output should begin with the day of the week the birthday was last year, then the following line will be day of the week of a birthday the year before that, etc. The final line is the day of week on the day they were born.

For example, one output might be:
```txt
Thursday
Friday
Tuesday
Monday
Sunday
Sunday
Monday
Tuesday
Thursday
Friday
Tuesday
Monday
Sunday
```

#### Part 2

Make a file `hour-mash.js` that prints out the following:
```txt
The day started [5] hours ago. One week ago it was exactly [Wednesday] at [3:33 PM]. Today's date is [18/09/2020]. There are exactly [44949] seconds until 9am on Friday.
```

Items in brackets are wildcards that should be values you populate. All values should be determined based off the moment that the script is run.

#### Part 3

If you find yourself with extra time, explore the `date-fns` library to both try and output dates in a specific format (and any other features).

https://www.npmjs.com/package/date-fns
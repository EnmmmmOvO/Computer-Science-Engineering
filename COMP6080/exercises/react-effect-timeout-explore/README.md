## Using useEffect to fetch once, playing with react events and timeouts

In the `exercise` folder run `yarn` and then `yarn start`.

This basic application loads JSON information from github (via `fetch`) to display how many public repositories exist within the microsoft github organisation.

#### Part 1

Display the number of public repos collected from the fetch into the disabled input.

#### Part 2

Have the `+` and `-` button that increase or decrease this value in the input by 1 respectively.

Did you come across any issues with too many re-renders? How can we use `useEffect` to resolve this?

#### Part 3

Introduce a new input underneath that allows users to enter a string of the organisation they want to find the number of public repos of. After 500ms of the last keyup on this field, re-fire the fetch to get the new data and populate the input again. However, don't directly call fetch - instead, modify the useEffect capture.

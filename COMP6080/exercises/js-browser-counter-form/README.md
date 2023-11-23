## Using Vanilla JS to manipulate a form with counters

Similar to the previous question, the file `counter.html` contains some HTML and CSS. This time, we are going to create a 'counter' using JS. The counter consists of a number, a '+' button and a '-' button. When you press the '+' button, the number goes up by 1 and when you press the '-' button, the counter decreases by 1. For this counter, we want the number to be between 0 and 10 all the time.

1. Take a look at the `counter.html` file. Can you identify the components of the counter from this file?

> All components are within the `<container>` element.
> Two buttons: decrement and increment.
> Number is meant to go in the `<div id="counter">` element.

2. Using JS (via the `counter.js` file), initialise the counter to 0.

3. Add a 'click' event listener to the increment button that will increment the counter by 1. HINT: use the `parseInt()` function before doing any calculations.

4. Add a 'click' event listener to the decrement button that will decrement the counter by 1.

5. Ensure that you can't increment past 10 or decrement below 0. If the user tries to do this, display an error using the JS `alert()` function.

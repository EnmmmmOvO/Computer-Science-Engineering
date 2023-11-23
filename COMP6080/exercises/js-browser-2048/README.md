## Use Vanilla JS to recreate the 2048 online game

You must complete the page based on the specification below. Beyond the HTML/CSS, you are only able to use Vanilla JS (DOM & Events) to complete this task. This exercise is intended to help you understand the challenges of action => render mapping using vanilla (classic/plain) javascript.

The stub code is provided to you below folder. In the file `index.html` build your page. You are allowed to make extra CSS or JS files too.

```html
<table border="1">
	<tr>
		<td>2</td>
		<td></td>
		<td></td>
		<td></td>
	</tr>
	<tr>
		<td>2</td>
		<td></td>
		<td></td>
		<td></td>
	</tr>
	<tr>
		<td>2</td>
		<td></td>
		<td></td>
		<td></td>
	</tr>
	<tr>
		<td>2</td>
		<td></td>
		<td></td>
		<td></td>
	</tr>
</table>
```

![](overview.png)

The game always begins with a single `2` in the top left, and all other cells empty.

You must add key listener events to the board such that when:
 * The "down" key is pressed, all the cells slide down as far as they can to the bottom
 * The "right" key is pressed, all the cells slide right as far as they can to the right
 * The "left" key is pressed, all the cells slide left as far as they can to the left
 * The "up" key is pressed, all the cells slide up as far as they can to the up

After a slide occurs, a cell containing either `2` or `4` (randomly chosen) should appear in one of the empty cells on the board (randomly chosen).

The following function can be used to generate a random number:
```javascript
const getRandomInt = (max) => {
  return Math.floor(Math.random() * Math.ceil(max));
}
```

The following features are considered challenge exercises as part of this exercise, and are **NOT required to be completed**:
 * The finish state, when 2048 is reached.
 * The fail state, when the board is full and no more moves can be made.
 * The merging of cells when two adjacent cells slide together as part of a slide.

If you're unsure about any intended behaviour, whether it be the features you include or not, you can see the behaviour in the (2048 Game)[https://play2048.co/].

As a bonus exercise, try and store the game state in `local storage` so that when you refresh the page the game remains where you were previously up to.

### Hints

* The easiest and simplest way to solve this problem is just to store a 4 x 4 array for either exercise 1 or exercise 2, 

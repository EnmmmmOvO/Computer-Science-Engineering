## Use CSS to create a mobile-first page, then use a framework too

Provided in this question is a `responsive.html` and a `responsive.css` file. There are nine images in the `responsive.html` file. In this exercise, you will be laying out the images in three rows first using hardcoded CSS, then responsive CSS, and then finally using a framework to do so.

In the HTML file, arrange the images in a row of 4, then a row of 3, and finally a row of 2.

Assign each image in each row with a set pixel width so that each row of images stretches across the entire screen uniformly. Use your DevTools to adjust the screen dimensions. What happens with the images in the image rows? Is this considered responsive design? Why or why not?

> Create `<div>`'s that encompass 4, 3 and then 2 images, and apply a distinct class to each image in a row. for a 1920x1080 display, the image width can be `465px`, `620px`, and `930px` for the 4 image row, 3 image row and 2 image row respectively.
>
> When the screen width is shrunk from the original width, the images would overflow into new rows, while retaining its size. This is not considered responsive design, as the general structure of the webpage should be preserved when adjusting the screen dimensions.

What can we do to make this more responsive? Apply your solutions to the HTML and CSS file. 

> Make the row divs flexboxes, and replace the pixel values with percentages, or vw units.

Why is the current design considered responsive?

> The general structure of the webpage is maintained when the dimensions of the screen is adjusted.

Finally, let's use CSS frameworks to help making our webpage responsive, easier. We will be using [Bootstrap](https://getbootstrap.com/). What are CSS frameworks, and why would they be useful to us?

> CSS frameworks are libraries that allows for users to easily apply standards-compliant web design. Notable things provided by CSS frameworks include grid classes (for responsive design) and resetting default web CSS (such as removing the inherent `8px` margin for the `body` tag). CSS frameworks are helpful in that they are able to give us already responsive CSS classes that we can apply to our webpage, saving us time in having to exhaustively test for responsiveness. 
> 
> [Get started with Bootstrap](https://getbootstrap.com/docs/5.1/getting-started/introduction/) by adding both the stylesheet line, and the script.

Apply the grid system provided by Boostrap to `responsive.html`.

> It's a good idea to go through how the [grid system works](https://getbootstrap.com/docs/5.1/layout/grid/) before applying it to the webpage.

________

### Part 2

`pricing-plans.html` contains four columns that compare the subscription plans for an online service. `pricing-plans.css` contains the CSS that for the corresponding HTML file. How can we make this page more responsive?

> Currently, the widths of the columns are hardcoded in `px`. Change those values to the appropriate percentage value, such as `25%`.

Once those changes are made, would you consider the page responsive? In what ways is `pricing-plans.html` is it? Under what circumstances and in what ways is it not responsive? What could be done to make it more responsive? Apply the changes.

> `pricing-plans.html` is responsive as the width of each of the four columns change depending on the viewport width due to the use of percentage widths. As the viewport width approaches tablet or mobile widths, the widths of the columns becomes too narrow to be able to comfortably read the contents of the column - This makes it not optimally responsive for mobile users. 
>
> Although we can adjust CSS (such as with percentage values) to increase a page's responsiveness, we may also have to manipulate the structure of the HTML file to make a page even more responsive.
>
> The page can be made more responsive by moving certain columns into different rows, so that the text in the column remains comfortably legible. This requires creating breakpoints (At least 2) for different column layouts. Create the mobile column layout first (1 per row) for the mobile layout, before creating intermediate states between that mobile layout and the desktop layout (4 per row).
>
> Apply any other changes that the students suggest if it will make the page more responsive. These can include decreasing the font size, especially of the headers.

What Bootstrap features can we apply to the page? 

> [Columns](https://getbootstrap.com/docs/5.1/layout/columns/). Columns follow the same default breakpoint conventions as the Bootstrap [Grid system](https://getbootstrap.com/docs/5.1/layout/grid/).
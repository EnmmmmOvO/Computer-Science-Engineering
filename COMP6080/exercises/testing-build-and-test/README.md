## Create a complex ReactJS component, then write tests

## Part 1

You will be building a product card such as in `product.png`.
Note that this lab uses `react-router`.

![image](./product.png)

The component takes in the following props:

- `product` dictionary containing:
  - `id` string
  - `image` string of image file or url to image for the product preview
  - `title` string of product name
  - `price` number
  - `currency` string to be displayed next to the price
  - `descriptions` list of strings, containing the paragraphs of the product description
  - `recommendationRatio` number in range `[0, 1]` representing the portion of satisfied users
- `onAddToCart` event handler which is triggered when the `Add to cart` button is clicked, accepting parameters item `id` and `quantity`
- optional `discount` number in range `[0, 1]` representing the percentage discount to apply to the product e.g. if `price == 50` and `discount == 0.2`, then the displayed price will be `$40.00`

Your component must use the same structure as the reference, but you are free to style it to your liking.

Your component must adhere to the following requirements:

- There is an image preview of the product using the `image` input
- `image` has an appropriate `alt` description
- There is a title of the product using the `title` input
- `price` is displayed to two decimal places, with `discount` applied. The default value of `discount` is 0.
- `currency` is displayed next to `price`
- All strings in `descriptions` are displayed on the page
- There is text that reads `Highly recommended by [recommendationRatio]% users`, where `recommendationRatio` is displayed as a percentage value
- Clicking the `-`/`+` buttons will adjust the quantity displayed, which represents the number of items to add to the cart
- Clicking `Add to cart` will trigger on the `onAddToCart` handler with the item `id` and `quantity` as input parameters
- The buttons `-`/`+` have appropriate `aria-label` values (see [WCAG guidelines](https://www.w3.org/TR/WCAG20-TECHS/ARIA14.html) if you would like to better understand `aria-label`)

**You may break this component down further into as many or as little components as you see fit, but you must test all the requirements in some capacity.**

There are some images in `exercise/images/` that you may use for the product previews. Also see `exercise/src/App.js` for sample product input.

To view your component, run:

`yarn start`

## Part 2

Add another component called `Cart`.
It is meant to represent the user's shopping cart, and it can look like this:

![cart](./cart.png)

To ensure the user is able to navigate to the cart, the following steps must be taken:

1. Make the `<Cart/>` component render when the user goes to the `"/cart"` route.
2. Use the `react-router` hook `useHistory` to move to the `"/cart"` route when the `Add to cart` button is clicked and the `quantity` of the item is more than 0.
3. Now a user should be able to navigate to the cart!

This component takes in the following props:

- `items` dictionary containing entires of products in the format `{title: quantity}`.
- `onRemoveFromCart` event handler that is triggered when the `Remove Item` button is clicked, accepting the item `title` as its parameter.

The component must adhere to the following requirements:

- Title and quantity of the item are shown
- `Remove Item` button is shown. When clicked, it should make the corresponding item disappear without needing to refresh the page.
- `Return Home` button is shown. When clicked, it redirects the user to the `"/"` page.

Furthermore, the component must be accessible by clicking on the `Add to cart` button (when `quantity` is more than 0).

As with the previous part, you may break this component down into further subcomponents.

**Test the `<Cart/>` component on all requirements except for those relating to routes/redirects.**

## [Challenge] Part 3

Under `Highly recommended by [recommendationRatio]% users`, add a graphic to represent the user ratings. The graphic must be an SVG with five identical shapes, where the number of filled shapes is equal to `Math.ceil(recommendationRatio * 5)` i.e. if `recommendationRatio == 0.75` then there should be four filled shapes.

The reference image uses circles for the rating graphic, but you are free to construct your own shapes (i.e. triangles, square, heart, star). What's important is the number of filled shapes out of five. You do not need to write tests for this feature.

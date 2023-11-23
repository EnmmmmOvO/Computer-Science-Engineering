> The last website is also a good resource when developing a website with good accessibility in mind
> 
> Check all the websites for the following
> - Pages can be navigated using the keyboard only
> - Visual order follows the DOM order, i.e. the structure of the source code is reflected accurately visually
> - Use of "landmark elements" like `header`, `footer` in places that make sense throughout the page
> - Use of appropriate semantic HTML elements, such as `li` for lists
> 
> For `mcdonalds.com.au`:
> 
> - Buttons do not have accessible names
> - Image elements do have [alt] attributes
> - Links do not have a discernible name attribute
> - HTML element does not have a [lang] attribute
>
> For `dymocks.com.au`:
> 
> - [aria-hidden="true"] element contain focusable descendents
> - ARIA IDs are not unique
> - Background and foreground colours do not have a sufficient contrast ratio
> - Heading elements are not in a sequentially-descending order
> - Image elements do not have [alt] attributes
> - Links do not have discernable names
> 
> For `w3.org`:
> - [aria-*] attributes do not have valid values
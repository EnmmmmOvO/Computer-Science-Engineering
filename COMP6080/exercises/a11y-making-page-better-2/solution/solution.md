### ARIA attributes

What is ARIA and why is it important?

> ARIA stands for Accessible Rich Internet Applications. It is a set of attributes that define ways to make web content and web applications (especially those developed with JavaScript) more accessible to people with disabilities. It is especially useful when HTML lacks semantic tags which would give more meaning to an element.

Have a look at some of the ARIA roles and attributes on these pages:
* https://developer.mozilla.org/en-US/docs/Web/Accessibility/ARIA/Roles
* https://developer.mozilla.org/en-US/docs/Web/Accessibility/ARIA/Attributes

> Draw attention to the more common ones, like `aria-hidden`, `aria-label`, as well as the variety of roles. Discuss when they should be used.

Add ARIA attributes to `form.html`.

### Tabbing navigation

What is tabbing navigation and when is it used?

> Tabbing navigation refers to the ability to navigate between focusable elements within a webpage by using the tab key. This can allow the user to browse a website with only their keyboard, or a couple specific keys.

> Demonstrate this on various websites, e.g. https://www.handbook.unsw.edu.au/, drawing attention to how in most cases the order of the elements should be intuitive.

We are able to override the default of what order the elements should be focused in by using the HTML attribute `tabindex`.

It allows you to specify
* some by-default not-focusable elements such as divs should able to be focused
* some elements should not be reachable by keyboard navigation but can stick be focused by mouse or JavaScript.

In general, you should avoid using tab indexes greater than 0 as this disrupts the expected flow through the page for those using assistive technologies. Instead, structure your document so that the elements are in the intended sequence.

Looking at `tabbing.html`, try and identify which elements will be focused by tabbing, which what order they will be focused in.

Modify the tabindex property of the elements in `tabbing.html` to see how it affects the tabbing navigation flow.

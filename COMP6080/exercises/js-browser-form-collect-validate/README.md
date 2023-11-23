## Build HTML and Vanilla JS form to collect and validate details

Build a simple form in `form.html` that collects an email address and first name from a user before submitting it. We have provided some stub code.

Valid inputs:
 * A valid first name is defined as only lowercase and uppercase letters, between 2 and 20 characters long inclusively.
 * A valid email is defined by the regular expression `.+\@.+\..+` (read more on that here)[https://developer.mozilla.org/en-US/docs/Web/JavaScript/Guide/Regular_Expressions].

Important facts about form state:
 * The submit button remains disabled until both a valid firstName and valid email are entered. The state change occurs on keyup of either input fields.
 * On blur of either input fields, if their value is invalid, the background of the input is turned a light red.
 * On focus of either input fields, we removed any error backgrounds.

> See `solutions/form.html`

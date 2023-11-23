## Assess browser code to figure out what doesn't work with NodeJS

Which of the folowing code would work in the browser/NodeJS?
* `document.getElementById('id');`
> only works on browser as [`document`](https://developer.mozilla.org/en-US/docs/Web/API/Document) is an interface implemented by the browser
* `window.alert('alert');`
> only works on browser as [`window`](https://developer.mozilla.org/en-US/docs/Web/API/Window) is an interface implemented by the browser
* `confirm('yes?');`
> only works on browser as this is the same as `window.confirm()` (`window` is a global object you can reference any of its fields directly)
* `fetch('www.google.com');`
> only works on browser as [`fetch`](https://developer.mozilla.org/en-US/docs/Web/API/fetch) is a global method implemented by the browser
* `console.log('warning');`
> works on both browser and NodeJS
* `require('fs');`
> only works on NodeJS as `require` is a builtin function that is not implemented by the browser.
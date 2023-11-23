## Fetch a list of things from a response of another fetch

This exercise mocks the behaviour of a frontend client requesting data from a backend server.

In [server.js](server.js), you can see a list of users and 2 routes, run `node server` in your terminal to start the backend server (You'll need to run `yarn` or `npm install` first).

In [index.js](index.js) a `<ul>` tag and a `<li>` tag has been created for you, however there is only 1 user which is being hardcoded, instead we want to display all the users in the backend.

You can run the frontend by opening [index.html](index.html) in your browser. In order to get the users from the backend, you need to use
```js
fetch(`http://localhost:3000/${route}`)
```
to make a GET request from the 2 routes. Then for each user append a `<li>` tag to the `<ul>` tag each of which contains a username.

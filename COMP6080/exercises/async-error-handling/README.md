## Learn how to handle promise errors with .catch and .finally

For this exercise we'll be using this endpoint from the [JSON Placeholder API](https://jsonplaceholder.typicode.com):

- `https://jsonplaceholder.typicode.com/users/<id>` to get a single user by its id

In `main.js` create a function `getUserByIdAndUsername` that accepts an string `id` and a string `username` and returns a Promise resolving to a user object from the above API.

This function show reject the promise in the following situations:

- if the API response has a status of 404, throw an error with the message `Could not find a user with id <id>`
- if the API response does not have a success response (2XX), throw an error with the message `Something went wrong when getting user with id <id>`
- if the given `username` does not match the username in the response, throw an error with the message `The user with id <id> does not have username '<username'`

The following call should be successful:

```js
getUserByIdAndUsername('1', 'Bret')
```

and these should fail:

```js
getUserByIdAndUsername('404', 'This user does not exist')
getUserByIdAndUsername('1', 'Bob')
```

When the page loads, call this function with the `id` and `username` query params in the url and add the `loading` class to the body. When the promise is settled:

- If the promises resolves, stringify the result and insert it in the element with id `result`
- If the promise rejects, call `alert` with the error message
- In both cases replace the `loading` class with `done`.

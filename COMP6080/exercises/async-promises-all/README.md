## Learn how to use promise.all to handle multiple promises concurrently

In this exercise, we will be looking at `Promise.all`.

`Promise.all` allows you to aggregate/analyse the results of multiple asynchronous calls at once.
You can give it an array of promises and once resolved, it will return an array of results to you.

For more information, see the [MDN docs](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Promise/all).

The file `PromiseAll.js` contains a function called `getCompanyRepos`. It fetches a given company's public repositories from GitHub.

If the company does not exist or has no information available, it will throw an error.

We will be using NPM + Node.js for this exercise. Run `npm install`.

To run the exercise, execute `node PromiseAll.js`.

### Question 1

Currently, the `question1` function gets the repo names of "microsoft", "google" and "canva" and prints them out as soon each promise resolves.
Using `Promise.all` and `.then`, modify `question1()` so that the repo names are printed out all at once.
HINT: you can store an unresolved Promise in a variable like this: `const microsoftRepos = getCompanyRepos("microsoft");`

### Question 2

Repeat question 1, but use `async` and `await` instead.

### Question 3

See what happens when you give `Promise.all` a `Promise` that will reject.
Do this by getting the repo names of "microsoft" as well as "some_fake_company".
Does `Promise.all` resolve or reject?
Are we able to see the repo names of "microsoft"?

### Question 4

If you don't need the results of promise that was rejected, you can use `Promise.allSettled` instead of `Promise.all`.
Instead of an array of resolved results, `Promise.allSettled` returns an array of fulfilled or rejected items.
Each item will have one of the two formats:

1. `{ status: "fulfilled", value: ... }`
2. `{ status: "rejected", reason: ... }`

Use `Promise.allSettled` to print the repo names of "microsoft", "google", "canva" and "some_fake_company".
If you encounter a `status === "rejected"` item, log the reason for it rejecting.

## Create a simple full stack interactive app

Create a new react app by running `npx create-react-app react` to add one to a `react` folder.

Build a simple ReactJS app that does the following:

- Has an input form field where a user can enter a list of comma separated Github user names (e.g. `UNSWComputing`, `Microsoft`, `Google`). Examples of one of these can be found [here](https://api.github.com/users/Microsoft).
- After 500 miliseconds from the last time this user input fires an `onChange` event, the list of comma separated user names is split, and for each one a `fetch` is made to collect data at the URL "https://api.github.com/users/[USERNAMEGOESHERE]". You can leverage the stub code provided in `exercise1` to get a good head start here.
- Once ALL of the fetches complete (and not before), you shall display a series of cards underneath on the page. Each card should be a separate ReactJS component that is imported into your `App.js`. Each component simply needs to consist of:
  - A 50px by 50px image that is the `avatar_url` property returned by the fetch
  - The `name` of the organisation (derived from the `name` property of the fetch), where clicking on this name links (in a new tab) to the `url` (derived from the `url` property of the fetch).

Note: You can implement the multiple fetches one of two ways:

- With a loop and async/await
- Using promises (preferable), where you can execute many promises at once using [Promise.all](https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Global_Objects/Promise/all)

In this exercise you are expected to use: `fetch`, `React.useEffect`, `React.useState`, ReactJS Functional Components.

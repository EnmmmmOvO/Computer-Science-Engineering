## Write tests for a full UI (1)

Write UI tests using `Cypress` for a happy path of a user successfully logging in and see the text `You're logged in!`. You can install it by running `yarn add -D cypress` which will add `cypress` to dev dependencies.

You can then run cypress with `yarn run cypress open` to open the test runner. The first time you run the command, it will configure cypress in your project and create a `cypress/` folder at the root level of your project. In there you can see some examples in the `integration/` folder and that's were you can add your own tests!

Look at the [login form](exercise/src/App.js) from the [testing-component-1](../testing-component-1) exercise and think about how you should write tests for a happy path.

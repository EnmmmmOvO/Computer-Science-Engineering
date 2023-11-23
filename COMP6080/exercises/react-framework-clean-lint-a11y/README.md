## Clean up a React App - improve accessibility in the context of linting and material ui

In the `exercise` folder run `yarn` and then `yarn start`.

This contains a *very bad* react app, with a single component, that attempts to display a simple page with a header, footer, and body that has an input and a button.

### Part 1

This code fails to adhere to a number of very basic accessibility and best practices. Implement any and all relevant improvements to the code to make it more accessible.

### Part 2

Setup `eslint` with the default configuration. Run `yarn add --dev eslint-config-react-app` in the `exercise1` folder. This will install a dev dependency to allow you to lint your react app with eslint. Once that is installed, run `yarn eslint src/**.js` in your exercise1 directory. This will lint all javascript files.

Ensure your `exercise1` passes the linter.

### Part 3

It's time to try and use a React based library - **Material UI**.

Install Material UI with yarn [here](https://mui.com/getting-started/installation/)

```sh
yarn add @mui/material @emotion/react @emotion/styled
```

Once installed, add at least two Material UI components to your ReactJS app. They can be headers, buttons, alerts, cards - anything. They must be clearly visible to someone using the page.

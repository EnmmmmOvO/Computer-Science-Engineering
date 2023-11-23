## Write tests for a ReactJS component (1)

In this exercise we'll be testing the `<LoginForm>` component from `exercise/src/LoginForm.js`.

This component takes 2 props:

- `onSubmit` function that gets called with an object containing the email and password if email and password inputs are filled in.
- `errors` optional object containing string errors for email and / or password

Look at `exercise/src/App.js` to see how it's used.

Before you start writing tests, write down a list of things you want to test using the `it.todo` helper function.

<details>
<summary>Some aspects you might want to test</summary>

- `onSubmit` gets called with the correct values when the inputs are filled in and the form is submitted
- the inputs are `required`
- the error messages in `errors` show up when the form is rendered
- the matching input has the `aria-invalid` attribute set to `"true"` if an error is provided for that field and `"false"` otherwise
- the labels are linked to the correct inputs using the `htmlFor` attribute
- the inputs are linked to the correct error messages using the `aria-describedby` attribute

</details>

**Note:** you won't be able to test some aspects of the component (e.g. `onSubmit` is not called if the form is submitted and any `required` inputs are not filled) but your UI tests should take care of that.

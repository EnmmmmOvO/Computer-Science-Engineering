## Explore using JWT authentication in the context of ReactJS

In this exercise, we will be using a JSON Web Token (JWT) to access a private route on a backend API.
JWTs are the industry standard for authenticating users.
In a nutshell, the frontend client sends a user's username and password to the backend, the backend encrypts some information (usually the user's email & other details) and sends it back to the client.
The encrypted user details form a JWT, and the client can send this back to the backend to access private routes.
For more information on JWTs, [checkout this source](https://jwt.io/introduction/).

For the purposes of this exercise, the backend does not check passwords, but obviously this should be done in practice.
Also, the frontend is not styled, as the main goal is to familarise yourself with using JWTs.

To start the backend, `cd` into `react/backend` and run `npm install`, then `node app.js`.
To start the frontend, `cd` into `react/frontend` and run `yarn`, then `yarn start`.

### Question 1

Inside `frontend/src/App.js` there is a simple login form. If you enter `comp6080_student` as the username with any password, you will be able to see a JWT printed out in the console log (`data.token` in `App.js` line 23).

Once the JWT has been received, store it in `localStorage` and redirect to a new page (i.e. render a different component to the login form).

### Question 2

On this new page, attempt to fetch `localhost:5000/api/secret-message` from the backend.
Note that this response will give you an error message!
Use the details of this error message, as well as the token stored in `localStorage` to get a successful response.

_Hint: use 'JWT <TOKEN>' for the 'authorization' header value. For more information on the format of this header, [visit MDN](https://developer.mozilla.org/en-US/docs/Web/HTTP/Headers/Authorization)._

A successful response will look something like this:

```
{
  message: <SECRET-MESSAGE>,
  authData: {
    <USER DETAILS>
  },
}
```

### Question 3

Once you are able to receive the secret message, display it on the new page, as well as the username of the logged in user.
You can find the username from the response in `authData.user.username`.

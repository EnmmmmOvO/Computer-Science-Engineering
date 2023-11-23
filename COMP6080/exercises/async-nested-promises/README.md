## Learn about how to use the result of promises to make more promises

For this exercise we'll be using these endpoints from the [JSON Placeholder API](https://jsonplaceholder.typicode.com):

- `https://jsonplaceholder.typicode.com/posts/<id>` to get a single post by its id
- `https://jsonplaceholder.typicode.com/users/<id>` to get a single user by its id
- `https://jsonplaceholder.typicode.com/posts?_page=<page>` to get a page of posts starting from page 1

Before you start the exercises open the endpoints in your browser to see what the API returns in each case.

### Nested Promises

In `main.js` create a function `getPostAndUser` that takes a number and returns a Promise resolving to an object with the following properties:

- `post`: the post with the given number as the id
- `user`: the creator of the post (referred to by `post.userId`)

When you run the function you like this:

```js
getPostAndUser(1).then(result => {
  console.log(result)
})
```

you should see the an object matching below in your browser console.

```rust
{
  post: {
    userId: 1,
    id: 1,
    // other post properties
  },
  user {
    id: 1
    // other user properties
  }
}
```

## Recursive Promises

In `main.js` create a function `getAllPosts` that returns a Promise resolving to a list of all the posts returned by the API.

When you run the function you like this:

```js
getAllPosts().then(posts => {
  console.log(posts)
})
```

you should see the an array with length 100 matching below in your browser console.

```
[
  {
    "userId": 1,
    "id": 1
    // other post properties
  },
  {
    "userId": 1,
    "id": 2
    // other post properties
  }
  // other posts
]
```

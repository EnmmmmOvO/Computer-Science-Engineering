const API_URL = 'https://jsonplaceholder.typicode.com'

function getPostAndUser(postId) {
  return fetch(`${API_URL}/posts/${postId}`)
    .then(response => response.json())
    .then(post => {
      return fetch(`${API_URL}/users/${post.userId}`)
        .then(response => response.json())
        .then(user => ({
          post,
          user,
        }))
    })
}

getPostAndUser(1).then(result => {
  console.log(result)
})

function getPostsPage(page) {
  return fetch(`${API_URL}/posts?_page=${page}`).then(response =>
    response.json()
  )
}

function getAllPosts() {
  const posts = []
  let page = 1

  function handleThen(postsPage) {
    // This is our base case - if there are no posts on this page,
    // there definitely aren't any on the next page
    if (postsPage.length <= 0) {
      return posts
    }

    // Recursive step
    posts.push(...postsPage)
    page += 1
    return getPostsPage(page).then(handleThen)
  }

  return getPostsPage(page).then(handleThen)
}

getAllPosts().then(posts => {
  console.log(posts)
})

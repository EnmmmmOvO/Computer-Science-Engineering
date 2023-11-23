const API_URL = 'https://jsonplaceholder.typicode.com'

function getPostAndUser(postId) {
  return fetch(`${API_URL}/posts/${postId}`)
      .then(res => res.json())
      .then(post => {
        return fetch(`${API_URL}/users/${post.userId}`)
                .then(res => res.json())
                .then(user => ({post, user}))
      });
}

getPostAndUser(1).then(result => {
  console.log(result)
})

const getPosts = page => {
  return fetch(`https://jsonplaceholder.typicode.com/posts?_page=${page}`)
      .then(res => res.json())
}


function getAllPosts() {
  const list = [];
  let page = 1;

  const appendList = post => {
    if (post.length === 0) return list;
    list.push(...post);
    page++;
    return getPosts(page).then(appendList);
  }

  return getPosts(page).then(appendList);
}

getAllPosts().then(posts => {
  console.log(posts)
})
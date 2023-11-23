const API_URL = 'https://jsonplaceholder.typicode.com'

function getUserByIdAndUsername(id, username) {
  document.getElementById('loading').style.display = 'block';
  fetch(`https://jsonplaceholder.typicode.com/users/${id}`)
      .then(res => {
        if (res.ok) return res.json();
        else if (res.status === 404) throw new Error(`Could not find a user with id ${id}`);
        else throw new Error(`Something went wrong when getting user with id ${id}`);
      })
      .then(post => {
        console.log(post)
        if (post.username === username) {
          const result = document.getElementById('result');
          result.style.display = 'block';
          result.textContent = JSON.stringify(post);
        } else throw new Error(`he user with id ${id} does not have username ${username}`);
      }).catch(err => window.alert(err))
      .finally(() => document.getElementById('loading').textContent = 'done')
}

getUserByIdAndUsername(1, 'Bret');
const API_URL = 'https://jsonplaceholder.typicode.com'

function getUserByIdAndUsername(id, username) {
  return fetch(`${API_URL}/users/${id}`)
    .then(response => {
      // You can use `Promise.reject` or `throw` to trigger  `.catch`
      if (response.status === 404) {
        return Promise.reject(new Error(`Could not find with id ${id}`))
      } else if (!response.ok) {
        throw new Error(`Something went wrong when getting user with id ${id}`)
      }

      return response.json()
    })
    .then(user => {
      if (user.username !== username) {
        throw new Error(
          `The user with id ${id} does not have username '${username}'`
        )
      }
      return user
    })
}

const resultElement = document.getElementById('result')
const body = document.body

const queryParams = new URLSearchParams(location.search)

body.classList.add('loading')

getUserByIdAndUsername(queryParams.get('id'), queryParams.get('username'))
  .then(user => {
    resultElement.innerText = JSON.stringify(user, null, 2)
  })
  .catch(error => {
    alert(`Error: ${error.message}`)
  })
  .finally(() => {
    body.classList.replace('loading', 'done')
  })

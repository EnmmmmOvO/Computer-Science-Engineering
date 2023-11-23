import LoginForm from './LoginForm'
import { useState } from 'react'

function App() {
  const [errors, setErrors] = useState({})
  const [loggedIn, setLoggedIn] = useState(false)

  return (
    <div className="App">
      {loggedIn ? (
        <h1>You&apos;re logged in!</h1>
      ) : (
        <LoginForm
          errors={errors}
          onSubmit={({ email, password }) => {
            // Reset errors before validating & running business logic
            setErrors({})

            const newErrors = {}

            if (!email) {
              newErrors.email = 'Email is required'
            }

            if (!password) {
              newErrors.password = 'Password is required'
            }

            if (newErrors.email || newErrors.password) {
              setErrors(newErrors)
              return
            }

            if (email !== 'soorria@email.com') {
              setErrors({ email: 'User does not exist' })
              return
            }

            if (password !== 'super secure password') {
              setErrors({ password: 'Incorrect password' })
              return
            }

            // Email and password are correct so log user in.
            // In a real app you would use react-router to naviagte to a different page
            setLoggedIn(true)
          }}
        />
      )}
    </div>
  )
}

export default App

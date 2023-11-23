import { useState } from 'react'

const IDS = {
  emailInput: 'email',
  emailError: 'login-email-error',
  passwordInput: 'password',
  passwordError: 'login-password-error',
}

function LoginForm({ onSubmit, errors = {} }) {
  const [email, setEmail] = useState('')
  const [password, setPassword] = useState('')

  const handleSubmit = event => {
    event.preventDefault()

    onSubmit({ email, password })
  }

  return (
    <form onSubmit={handleSubmit}>
      <div>
        <label htmlFor={IDS.emailInput}>Email: </label>
        <input
          id={IDS.emailInput}
          name="email"
          type="email"
          required
          aria-invalid={errors.email ? 'true' : 'false'}
          aria-describedby={errors.email ? IDS.emailError : undefined}
          value={email}
          onChange={event => setEmail(event.target.value)}
        />
        {errors.email ? (
          <p id={IDS.emailError} aria-live="polite">
            {errors.email}
          </p>
        ) : null}
      </div>

      <div>
        <label htmlFor={IDS.passwordInput}>Password: </label>
        <input
          id={IDS.passwordInput}
          name="password"
          type="password"
          required
          aria-invalid={errors.password ? 'true' : 'false'}
          aria-describedby={errors.password ? IDS.passwordError : undefined}
          value={password}
          onChange={event => setPassword(event.target.value)}
        />
        {errors.password ? (
          <p id={IDS.passwordError} aria-live="polite">
            {errors.password}
          </p>
        ) : null}
      </div>

      <div>
        <button type="submit">Login</button>
      </div>
    </form>
  )
}

export default LoginForm

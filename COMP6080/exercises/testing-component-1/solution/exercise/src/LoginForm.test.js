import { render, screen } from '@testing-library/react'
import userEvent from '@testing-library/user-event'
import LoginForm from './LoginForm'

const noop = () => {}

describe('<LoginForm>', () => {
  it('renders the email field, password field and login button', () => {
    render(<LoginForm onSubmit={noop} />)

    expect(screen.getByRole('textbox', { name: /email:/i })).toBeInTheDocument()
    expect(screen.getByLabelText(/password:/i)).toBeInTheDocument()
    expect(screen.getByRole('button', { name: /login/i })).toBeInTheDocument()
  })

  it('renders the email and password inputs as required fields', () => {
    render(<LoginForm onSubmit={noop} />)

    expect(screen.getByRole('textbox', { name: /email:/i })).toBeRequired()
    expect(screen.getByLabelText(/password:/i)).toBeRequired()
  })

  it('renders the email and password inputs as invalid if an error is provided', () => {
    const errors = {
      email: 'INVALID EMAIL ERROR MESSAGE',
      password: 'INVALID PASSWORD ERROR MESSAGE',
    }

    render(<LoginForm onSubmit={noop} errors={errors} />)

    expect(screen.getByRole('textbox', { name: /email:/i })).toBeInvalid()
    expect(screen.getByLabelText(/password:/i)).toBeInvalid()
  })

  it('renders error messages correctly when errors are provided', () => {
    const errors = {
      email: 'INVALID EMAIL ERROR MESSAGE',
      password: 'INVALID PASSWORD ERROR MESSAGE',
    }

    render(<LoginForm onSubmit={noop} errors={errors} />)

    expect(screen.getByRole('textbox', { name: /email:/i })).toHaveAccessibleDescription(errors.email)
    expect(screen.getByLabelText(/password:/i)).toHaveAccessibleDescription(errors.password)
  })

  it('renders the email and password inputs as valid if there are no errors', () => {
    const inputs = {
      email: 'soorria@email.com',
      password: 'super secure password',
    }

    render(<LoginForm onSubmit={noop} />)

    userEvent.type(screen.getByRole('textbox', { name: /email:/i }), inputs.email)
    userEvent.type(screen.getByLabelText(/password:/i), inputs.password)

    expect(screen.getByRole('textbox', { name: /email:/i })).toBeValid()
    expect(screen.getByLabelText(/password:/i)).toBeValid()
  })

  it('calls onSubmit with the values of the inputs', () => {
    const inputs = {
      email: 'soorria@email.com',
      password: 'super secure password',
    }

    const expectedValues = { ...inputs }

    const mockOnSubmit = jest.fn()

    render(<LoginForm onSubmit={mockOnSubmit} />)

    userEvent.type(screen.getByRole('textbox', { name: /email:/i }), inputs.email)
    userEvent.type(screen.getByLabelText(/password:/i), inputs.password)

    userEvent.click(screen.getByRole('button', { name: /login/i }))

    expect(mockOnSubmit).toHaveBeenCalledTimes(1)
    expect(mockOnSubmit).toHaveBeenCalledWith(expectedValues)
  })
})

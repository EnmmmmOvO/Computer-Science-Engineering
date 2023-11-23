import React from 'react';
import { useNavigate } from 'react-router-dom';

function Register (props) {
  const [email, setEmail] = React.useState('');
  const [password, setPassword] = React.useState('');
  const [name, setName] = React.useState('');
  const navigate = useNavigate();

  React.useEffect(() => {
    if (props.token) {
      navigate('/dashboard');
    }
  }, [props.token]);

  const register = async () => {
    const response = await fetch('http://localhost:5005/user/auth/register', {
      method: 'POST',
      body: JSON.stringify({
        email, password, name
      }),
      headers: {
        'Content-type': 'application/json',
      }
    });
    const data = await response.json();
    if (data.error) {
      alert(data.error);
    } else if (data.token) {
      localStorage.setItem('token', data.token);
      props.setToken(data.token);
      navigate('/dashboard');
    }
  };

  return (
    <>
      <h2>Register</h2>
      Email:
        <input type="text" value={email} onChange={e => setEmail(e.target.value)} /><br />
      Password:
        <input type="password" value={password} onChange={e => setPassword(e.target.value)} /><br />
      Name:
        <input type="text" value={name} onChange={e => setName(e.target.value)} /><br />
      
      <button type="button" onClick={register}>Register</button>
    </>
  )
};

export default Register;
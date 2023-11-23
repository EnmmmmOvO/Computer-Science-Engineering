import React from 'react';
import { useNavigate } from 'react-router-dom';

import TextField from '@mui/material/TextField';
import Button from '@mui/material/Button';
import Typography from '@mui/material/Typography';

function Login (props) {
  const [email, setEmail] = React.useState('');
  const [password, setPassword] = React.useState('');
  const navigate = useNavigate();

  React.useEffect(() => {
    if (props.token) {
      navigate('/dashboard');
    }
  }, [props.token]);

  const login = async () => {
    const response = await fetch('http://localhost:5005/user/auth/login', {
      method: 'POST',
      body: JSON.stringify({
        email, password
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
      <Typography variant="h4" gutterBottom>
        Login
      </Typography>
      <TextField label="Email" type="text" value={email} onChange={e => setEmail(e.target.value)} /><br />
      <br />
      <TextField label="Password" type="password" value={password} onChange={e => setPassword(e.target.value)} /><br />
      <br />
      <Button variant="contained" onClick={login}>Login</Button>
    </>
  )
};

export default Login;
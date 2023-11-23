import React from 'react';
import { Routes, Route, Link, useNavigate } from 'react-router-dom';

import Box from '@mui/material/Box';
import BottomNavigation from '@mui/material/BottomNavigation';
import BottomNavigationAction from '@mui/material/BottomNavigationAction';
import RestoreIcon from '@mui/icons-material/Restore';
import FavoriteIcon from '@mui/icons-material/Favorite';
import LocationOnIcon from '@mui/icons-material/LocationOn';

import Footer from './components/Footer';
import Login from './components/Login';
import Register from './components/Register';
import Dashboard from './components/Dashboard';

const LandingPage = () => {
  //const navigate = useNavigate();
  //navigate('/login');
  return <>Hi</>
}

const PageList = () => {
  const [token, setToken] = React.useState(null);
  const navigate = useNavigate();

  console.log('hi');

  React.useEffect(() => {
    const checktoken = localStorage.getItem('token');
    if (checktoken) {
      setToken(checktoken);
    }
  }, []);

  const logout = () => {
    setToken(null);
    localStorage.removeItem('token');
    navigate('/login');
  }

  const pages = token
    ? ['Dashboard', 'Logout']
    : ['Register', 'Login'];

  return (
    <>

      <Routes>
        <Route path="/" element={<LandingPage />} />
        <Route path="/register" element={<Register token={token} setToken={setToken} />} />
        <Route path="/login" element={<Login token={token} setToken={setToken} />} />
        <Route path="/dashboard" element={<Dashboard token={token} setToken={setToken} />} />
      </Routes>

      <br />
      <br />
      <hr />
      <Box>
        <BottomNavigation
          showLabels
          value={''}
          onChange={(event, newValue) => {
            if (pages[newValue] == 'Logout') {
              logout();
            } else {
              navigate(`/${pages[newValue].toLowerCase()}`);
            }
          }}
        >
          {pages.map((page, idx) => {
            return (
              <BottomNavigationAction label={page} icon={<RestoreIcon />} />
            )
          })}
        </BottomNavigation>
      </Box>
      <hr />
      

      <Footer />

    </>
  );
}

export default PageList;

/*
 ✅ useState -- easy
 ✅ useEffect
 ✅ multiple files, components
 ✅ props
 ✅ routing & spas
 ✅ css framewrosk
 ✅ (refersher) fetch
*/

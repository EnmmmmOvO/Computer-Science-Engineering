import React, {useEffect} from 'react';
import {Box, Typography} from "@mui/material";
import {useWindowContext} from "../context";
import {useNavigate} from "react-router-dom";

const TopBar = () => {
  const { width } = useWindowContext();
  const navigate = useNavigate();

  useEffect(() => {
    console.log(width);
  }, [width]);


  return (
    <Box sx={{
      position: 'fixed',
      height: '80px',
      top: 0,
      left: 0,
      width: '100%',
      bgcolor: '#EEEEEE',
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'space-between',
    }}>
      <Box sx={{ height: '50px', width: '50px', m: '15px' }}>
        <img src="/logo192.png" alt="logo" style={{ height: '100%', width: '100%' }}/>
      </Box>
      <Box sx={{ display: 'flex', alignItems: 'center', m: '15px' }}>
        <Box sx={{ borderRight: 2, borderColor: 'black', cursor: 'pointer', pl: 3, pr: 3 }} onClick={() => navigate('/')}>
          <Typography>{width > 800 ? 'Home' : 'H'}</Typography>
        </Box>
        <Box sx={{ borderRight: 2, borderColor: 'black', cursor: 'pointer', pl: 3, pr: 3 }} onClick={() => navigate('/blanko')}>
          <Typography>{width > 800 ? 'Blanko' : 'B'}</Typography>
        </Box>
        <Box sx={{ borderRight: 2, borderColor: 'black', cursor: 'pointer', pl: 3, pr: 3 }} onClick={() => navigate('/slido')}>
          <Typography>{width > 800 ? 'Slido' : 'S'}</Typography>
        </Box>
        <Box sx={{ cursor: 'pointer', pl: 3, pr: 3 }} onClick={() => navigate('/tetro')}>
          <Typography>{width > 800 ? 'Tetro' : 'T'}</Typography>
        </Box>
      </Box>
    </Box>
  );
}

export default TopBar;

import React from 'react';
import {Box, styled} from "@mui/material";
import {useWindowSizeContext} from "../context";
import {useNavigate} from "react-router-dom";


const BottomBar = () => {
  const { width } = useWindowSizeContext();
  const navigate = useNavigate();

  const CustomBox = styled(Box)({
    flex: 1,
    display: 'flex',
    alignItems: 'center',
    justifyContent: 'center',
    cursor: 'pointer',
    textDecoration: 'underline'
  });

  return (
    <Box sx={{
      boxSizing: 'border-box',
      position: 'fixed',
      width: '100%',
      height: width >= 1400 ? '100px' : width >= 800 ? '80px' : '60px',
      bgcolor: '#333',
      color: '#fff',
      border: '1px solid #fff',
      left: 0,
      bottom: 0,
      p: '0 10%',
      display: 'flex',
      justifyContent: 'space-between',
      alignItems: 'center'
    }}>
      <Box sx={{ flex: 1, display: 'flex', alignItems: 'center', justifyContent: 'center' }}>
        <img src="/logo192.png" style={{ width: '20px', height: '20px' }} alt="logo" />
      </Box>
      <CustomBox onClick={() => navigate('/dashboard')}>
        {width >= 1400 ? 'Dashboard' : 'Da'}
      </CustomBox>
      <CustomBox onClick={() => navigate('/game/math')}>
        {width >= 1400 ? 'Math' : 'Ma'}
      </CustomBox>
      <CustomBox onClick={() => navigate('/game/connect')}>
        {width >= 1400 ? 'Connect 4' : 'Co'}
      </CustomBox>
      <CustomBox onClick={() => navigate('/game/memory')}>
        {width >= 1400 ? 'Memorisation' : 'Me'}
      </CustomBox>
    </Box>
  );
}

export default BottomBar;
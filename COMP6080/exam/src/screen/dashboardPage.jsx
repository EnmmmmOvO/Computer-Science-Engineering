import React from 'react';
import { Box, Button, Grid } from "@mui/material";
import BottomBar from "../components/bottomBar";
import { useWindowSizeContext, useWinContext } from "../context";


const DashboardPage = () => {
  const { width, height } = useWindowSizeContext();
  const { start, win, setWin } = useWinContext();

  return (
    <Box sx={{
      bgcolor: '#ccc',
      paddingBottom: width >= 1400 ? '100px' : width >= 800 ? '80px' : '60px',
      display: 'flex',
      alignItems: 'center',
      justifyContent: 'center',
      width: '100%',
      height: height - (width >= 1400 ? 100 : width >= 800 ? 80 : 60),
    }}>
      <Grid container spacing={2} sx={{ margin: 'auto', maxWidth: 500, height: 500 }}>

        <Grid item xs={6} sx={{ display: 'flex', justifyContent: 'center', alignItems: 'center', border: '1px solid white' }}>
          {start - win > 0 ? start - win : 0}
        </Grid>

        <Grid item xs={6} sx={{ display: 'flex', justifyContent: 'center', alignItems: 'center', border: '1px solid white' }}>
          {win}
        </Grid>

        <Grid item xs={6} sx={{ display: 'flex', justifyContent: 'center', alignItems: 'center', border: '1px solid white' }}>
          {start <= win ? 'Great job' : 'Keep going'}
        </Grid>

        <Grid item xs={6} sx={{ display: 'flex', justifyContent: 'center', alignItems: 'center', border: '1px solid white' }}>
          <Button variant="contained" onClick={() => setWin(0)}>reset</Button>
        </Grid>

      </Grid>
      <BottomBar />
    </Box>
  );
}

export default DashboardPage;
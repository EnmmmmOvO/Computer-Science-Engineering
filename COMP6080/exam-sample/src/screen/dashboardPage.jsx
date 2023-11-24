import React, {useEffect} from 'react';
import {Box, Button, Typography} from "@mui/material";
import TopBar from "../components/topBar";
import FooterBar from "../components/footerBar";


const DashboardPage = () => {
  const [score, setScore] = React.useState(0);

  useEffect(() => {
    if (localStorage.getItem('gamesWon') === null) {
      fetch('https://cgi.cse.unsw.edu.au/~cs6080/raw/data/info.json')
        .then(response => {
          if (response.ok) {
            return response.json();
          } else {
            throw new Error('Fetch Score Error');
          }
        })
        .then(data => {
          setScore(data.score)
          localStorage.setItem('gamesWon', data.score)
        })
        .catch(error => console.error('Error:', error))
    } else {
      setScore(parseInt(localStorage.getItem('gamesWon')));
    }
  }, [])

  return (
    <>
    <TopBar/>
    <Box sx={{ m : 0, width: '100vw', height: '100vh', display: 'flex', justifyContent: 'center', alignItems: 'center', flexDirection: 'column' }}>
      <Box sx={{ display: 'flex', justifyContent: 'center', alignItems: 'center', flexDirection: 'column' }}>
        <Box sx={{ color: 'red', fontSize: '2em' }}>
          Please choose an option from the navbar.
        </Box>
        <Box sx={{ display: 'flex', alignItems: 'center' }}>
          <Typography sx={{ mr: 2 }}>Games won: {score}</Typography>
          <Button onClick={() => localStorage.setItem('gamesWon', '0')}>Reset</Button>
        </Box>
      </Box>
    </Box>
    <FooterBar />
    </>
  );
}

export default DashboardPage;
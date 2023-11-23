import './App.css';
import AppBar from '@mui/material/AppBar';
import Box from '@mui/material/Box';
import Toolbar from '@mui/material/Toolbar';
import Typography from '@mui/material/Typography';
import Button from '@mui/material/Button';
import LocalAirportIcon from '@mui/icons-material/LocalAirport';
import TextField from '@mui/material/TextField';
import Link from '@mui/material/Link';
import Paper from '@mui/material/Paper';
import Grid from '@mui/material/Grid';
import beachImg from './beach.jpeg';


function App() {

  const printSuccessfulLogin = (e) => {
    const username = document.getElementById("username").value;
    const password = document.getElementById("password").value;
    if (username !== "" && password !== "") {
      console.log(`Welcome to TravelLog ${username}!`);
    } else {
      console.log("Enter username and password");
    }
    
  }

  return (
    <div className="App">
      <AppBar position="relative">
          <Toolbar>
            <LocalAirportIcon sx={{ mr: 2 }} />
            <Typography variant="h6" color="inherit" noWrap>
              Travel Log
            </Typography>
          </Toolbar>
      </AppBar>
      <main>
      <Grid container component="main" sx={{ height: '100vh' }}>
        <Grid item xs={4} md={5} sx={{ backgroundImage: `url(${beachImg})`}}>
        </Grid>
        <Grid item xs={8} md={7} component={Paper} elevation={6} square>
          <Box sx={{ my: 10, mx: 2, display: 'flex', flexDirection: 'column', alignItems: 'center',}}>
            <Typography component="h1" variant="h3"> Welcome to Travel Log </Typography>

            <Box m={2}>
              <Typography component="h2" variant="h5"> Enter Username: </Typography>
              <TextField label="Username" id="username" margin="normal" />
            </Box>
            <Box m={1}>
              <Typography component="h2" variant="h5"> Enter Password: </Typography>
              <TextField label="Password" id="password" margin="normal" type="password" />
            </Box>
            <Box m={2}>
              <Button variant="contained" size="large" onClick={printSuccessfulLogin}> Sign In </Button>
            </Box>
            <Link href="#">Sign Up for a new Account</Link>
          </Box>
        </Grid>
      </Grid>
      </main>
      
            
      
    </div>
  );
}

export default App;

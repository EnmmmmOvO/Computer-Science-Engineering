import React from 'react';
import Button from '@mui/material/Button';
import Card from '@mui/material/Card';
import CardContent from '@mui/material/CardContent';
import './App.css';
import Typography from '@mui/material/Typography';

function App() {

  const [name, setName] = React.useState([]);
  const [allNames, setAllNames] = React.useState([]);

  const submitInfo = () => {
    setAllNames([ ...allNames, name ]);
  };

  return (
    <div>
      <header className="header">
        <nav id="nav-bar" aria-label="Main">
          <ul role="menu">
            <li role="menuitem" className="nav-item" tabIndex={0}>Home</li>
            <li role="menuitem" className="nav-item" tabIndex={0}>About</li>
            <li role="menuitem" className="nav-item" tabIndex={0}>Pricing</li>
            <li role="menuitem" className="nav-item" tabIndex={0}>Partners</li>
            <li role="menuitem" className="nav-item" tabIndex={0}>Contact</li>
          </ul>
        </nav>
      </header>
      <main className="main">
        <label htmlFor="firstname">First name: </label>
        <input type="text" name="first-name" id="firstname" value={name} onChange={e => setName(e.target.value)} /><br />
        <ul>
          {allNames.map((n, idx) => (
            <Card key={idx} className="card-custom">
              <CardContent>
                <Typography>{n}</Typography>
              </CardContent>
            </Card>
            ))}
        </ul>
        <Button id="form-submit" variant="contained" color="primary" onClick={submitInfo}>Submit</Button>
      </main>
      <footer className="footer">
        &copy; Giant Apple 2020
      </footer>
    </div>
  );
}

export default App;

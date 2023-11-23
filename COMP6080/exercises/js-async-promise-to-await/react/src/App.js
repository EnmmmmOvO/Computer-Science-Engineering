import React from 'react';
import logo from './logo.svg';
import './App.css';

function App() {

  const [org, setOrg] = React.useState(0);

  React.useEffect(() => {
    fetch(`https://api.github.com/orgs/microsoft`)
    .then(d => d.json())
    .then(d => setOrg(d.public_repos))
    .catch(err => console.log(err));
  }, []);

  return (
    <div style={{ margin: '50px'}}>
      <input disabled="true" type="text" value={org} />
    </div>
  );
}

export default App;

import './App.css';
import React, {useEffect, useState} from "react";
import TextField from '@mui/material/TextField';

let updateTimeOut = null;

function App() {
  const [list, setList] = useState([])
  const [card, setCard] = useState([])

  const updateList = e => {
    clearTimeout(updateTimeOut);
    updateTimeOut = setTimeout(() => setList(e.target.value.match(/([A-Za-z0-9]+)/g)), 500);
  }

  useEffect(() => {
    if (!list) {
      setCard([]);
      return;
    }
    Promise.allSettled(list.map((name) => fetch(`https://api.github.com/users/${name}`)))
      .then(response =>
        Promise.all(response.map(result=>
          result.status === 'fulfilled' ? result.value.json() : null
        )))
      .then(data => data.filter(user => user.name))
      .then(data => setCard(data))
  }, [list]);

  return (
    <div className="App">
      <div className={"TextField-Bar"}>
        <TextField
          className="TextField"
          id="input"
          label="Enter Github username"
          variant="outlined"
          onChange={updateList}
        />
      </div>
      <div className="Card-Table">
        {card.map(c =>
            <div className="Card">
              <div><img src={c.avatar_url} alt={c.name} /></div>
              <div className="text">{c.name}</div>
            </div>
        )}
      </div>
    </div>
  );
}

export default App;

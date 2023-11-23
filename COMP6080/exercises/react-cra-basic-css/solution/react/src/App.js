import React from 'react';
import logo from './logo.svg';
import './App.css';

function App() {
  return (
    <div className="App">
      <header className="App-header">
        <div className="container">
          <p className="heading">You are safe now</p>
          <p className="smalltext">human</p>
          <img src="https://i.ytimg.com/vi/wWqdhBdeMSg/hqdefault.jpg" className="catImg" />
          <div className="main">
            <p>You either die a hero, or live long <br /> enough to see yourself come the villian:</p>
            <ul>
              <li><a className="link" href="">Cat Video 1</a></li>
              <li><a className="link" href="">Cat Video 2</a></li>
            </ul>
          </div>
        </div>
      </header>
    </div>
  );
}

export default App;

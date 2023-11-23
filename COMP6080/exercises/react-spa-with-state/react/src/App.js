import React, {useState} from 'react';
import logo from './logo.svg'
import './App.css';

function App() {
  const home = () => {
    return (
      <div className="Text-page">
        This is a home page
      </div>
    )
  }

  const pricing = () => {
    return (
      <div className="Text-page">
        Our Pricing is ${(Math.random() * 100).toFixed(2)}
      </div>
    )
  }

  const faq = () => {
    return (
      <div className="Text-page">
        We don't have service of solving problem!
      </div>
    )
  }

  const gallery = () => {
    return (
      <div className="Text-page">
        <img
          src="https://play-lh.googleusercontent.com/K0OsLhs3Gb0vEAzzZrDq5y7EOXM2_jr5NShjU_3Qux5o9kGDi2mbXpi3TJ1Tp028TBQ"
          alt="Sorry, u cannot see so cute cat" />
      </div>
    )
  }

  const [dynamicPage, setPage] = useState(home());

  return (
    <div className="App">
      <div className="bar">
        <div className="logoContainer">
          <img className="App-logo" src={logo} alt="logo" onClick={() => setPage(home())} />
        </div>
        <div className="navbar">
          <div className="nav" onClick={() => setPage(home())}>Home</div>|
          <div className="nav" onClick={() => setPage(pricing())}>Pricing</div>|
          <div className="nav" onClick={() => setPage(faq())} >FAQ</div>|
          <div className="nav" onClick={() => setPage(gallery())}>Gallery</div>
        </div>
      </div>

      <div className="Dynamic-Part">{dynamicPage}</div>
    </div>
  );
}

export default App;

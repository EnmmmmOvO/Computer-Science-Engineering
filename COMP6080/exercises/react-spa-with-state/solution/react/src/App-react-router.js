import React from 'react'
import './App.css'
import { BrowserRouter as Router, Routes, Route, Link } from 'react-router-dom'

function App() {
  return (
    <Router>
      <div className="main-logo">
        <img
          src="https://encrypted-tbn0.gstatic.com/images?q=tbn%3AANd9GcQhBxob-6yeTiZKW_ep9WsuSgTYKSEGaqIFXw&usqp=CAU"
          alt="Instagram logo"
        />
      </div>
      <div className="nav-bar">
        <Link to="/">
          <span className="nav-item">Home</span>
        </Link>
        <Link to="/about">
          <span className="nav-item">Pricing</span>
        </Link>
        <Link to="/faq">
          <span className="nav-item">FAQ</span>
        </Link>
        <Link to="/gallery">
          <span className="nav-item">Gallery</span>
        </Link>
      </div>
      <div className="break"></div>
      <div className="body">
        <Routes>
          <Route path="/about" element={'About'} />
          <Route path="/faq" element={'FAQ'} />
          <Route path="/gallery" element={'Gallery'} />
          <Route path="/" element={'Home'} />
        </Routes>
      </div>
    </Router>
  )
}

export default App

import React, { useEffect, useState } from 'react';
import './App.css';
import { BrowserRouter, Route, Routes } from 'react-router-dom';
import {WindowSizeContext, WinContext} from './context';
import DashboardPage from "./screen/dashboardPage";
import MathPage from "./screen/mathPage";
import Connect4Page from "./screen/connect4Page";
import MemoryPage from "./screen/memoryPage";


function App() {
  const [start, setStart] = useState(5);
  const [win, setWin] = useState(0);

  const [windowSize, setWindowSize] = useState({
    width: 0,
    height: 0,
  });

  useEffect(() => {
    const handleResize = () => {
      setWindowSize({
        width: window.innerWidth,
        height: window.innerHeight
      });
    }

    fetch('https://cgi.cse.unsw.edu.au/~cs6080/raw/data/remain.json')
      .then(response => {
        if (response.ok) return response.json();
        throw new Error('Fetch Error');
      })
      .then(data => setStart(data.score))
      .catch(_error => setStart(5))

    window.addEventListener('resize', handleResize);
    handleResize();
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  return (
    <WindowSizeContext.Provider value={ windowSize }>
      <WinContext.Provider value={{ start, win, setWin }}>
        <BrowserRouter>
          <Routes>
            <Route path="/game/math" element={<MathPage />} />
            <Route path="/game/connect" element={<Connect4Page />} />
            <Route path="/dashboard" element={<DashboardPage />} />
            <Route path="/game/memory" element={<MemoryPage />} />
          </Routes>
        </BrowserRouter>
      </WinContext.Provider>
    </WindowSizeContext.Provider>
  );
}

export default App;

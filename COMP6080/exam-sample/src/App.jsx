import {BrowserRouter, Route, Routes} from "react-router-dom";
import React from "react";
import { Box } from "@mui/material";
import { WindowContext } from "./context";
import { useEffect } from "react";
import DashboardPage from "./screen/dashboardPage";
import BlankoPage from "./components/blankoPage";

function App() {
  const [windowSize, setWindowSize] = React.useState({
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
    window.addEventListener('resize', handleResize);
    handleResize();
    return () => window.removeEventListener('resize', handleResize);
  }, []);

  return (
    <WindowContext.Provider value={ windowSize }>
      <Box sx={{ m: 0 }}>
        <BrowserRouter>
          <Routes>
            <Route path="/" element={<DashboardPage />}/>
            <Route path="/blanko" element={<BlankoPage />}/>
          </Routes>
        </BrowserRouter>
      </Box>
    </WindowContext.Provider>
  );
}

export default App;

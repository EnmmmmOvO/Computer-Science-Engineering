import React from 'react';
import { BrowserRouter as Router } from 'react-router-dom';

import PageList from './PageList';

const App = () => {
  
  return (
    <>
      <Router>
        <PageList />
      </Router>
    </>
  );
}

export default App;

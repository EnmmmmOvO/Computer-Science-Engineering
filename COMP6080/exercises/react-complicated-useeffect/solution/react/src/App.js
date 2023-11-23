import React from 'react';
import './App.css';

function App() {
  const [aRerenders, setARerenders] = React.useState(0);
  const [bRerenders, setBRerenders] = React.useState(0);

  const [effectRerenders, setEffectRerenders] = React.useState(0);

  React.useEffect(() => {
    // effectRerenders => effectRerenders + 1
    // because just effectRerenders + 1 will automatically add effectRerenders to the dependency array if we use ESLint
    setEffectRerenders(effectRerenders => effectRerenders + 1);
  }, [aRerenders, bRerenders]);

  return (
    <div className="App">
      <div className="vertMargins">
        'A' re-render count: {aRerenders}
        <button onClick={() => setARerenders(aRerenders + 1)}>
          +
        </button>
      </div>
      <div className="vertMargins">
        'B' re-render count: {bRerenders}
        <button onClick={() => setBRerenders(bRerenders + 1)}>
          +
        </button>
      </div>
      <div className="vertMargins">
        'Effect' re-render count: {effectRerenders}
      </div>
    </div>
  );
}

export default App;

import React, {useEffect} from 'react';
import './App.css';

function App() {
  const [aRerenders, setARerenders] = React.useState(0);
  const [bRerenders, setBRerenders] = React.useState(0);

  const [effectRerenders, setEffectRerenders] = React.useState(0);

  useEffect(() => {
    setEffectRerenders(effectRerenders + 1);
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
        'effect' re-render count: {effectRerenders}
      </div>
    </div>
  );
}

export default App;

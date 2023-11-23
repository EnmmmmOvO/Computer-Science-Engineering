import React, {useEffect} from 'react'
import './App.css';

let timeOut = null;

function App() {
    const [org, setOrg] = React.useState('microsoft');
    const [value, setValue] = React.useState(0);
    const name = document.getElementById("name");

    useEffect(() => {
        fetch(`https://api.github.com/orgs/${org}`)
            .then(d => {
                if (d.ok) return d.json()
                else throw new Error('');
            })
            .then(d => {setValue(d.public_repos)})
            .catch(e => {setValue(0)})
    }, [org]);

    const getNewName = e => {
        if (!e.target.value) return;
        clearTimeout(timeOut);
        timeOut = setTimeout(() => setOrg(e.target.value), 500)
    }

    return (
        <div style={{ margin: '50px'}}>
            <div>
                <input disabled={true} type="text" value={value} />
                <button type="button" onClick={() => setValue(value - 1)}>&minus;</button>
                <button type="button" onClick={() => setValue(value + 1)}>&#43;</button>
            </div>
            <div><input type="text" id="name" onChange={getNewName}/></div>
        </div>
    );

}

export default App;

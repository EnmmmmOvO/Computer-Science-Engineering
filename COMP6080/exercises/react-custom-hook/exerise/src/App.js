import './App.css';
import {useEffect, useState} from "react";
import TextField from '@mui/material/TextField';
import {Button, Checkbox, FormControlLabel, FormGroup} from "@mui/material";

function App() {
  const initList = () => {
    const list = localStorage.getItem('6080-custom-hook');
    return list ? JSON.parse(list) : [];
  }

  const KeyPress = e => {
    if (e.key === 'Enter') addTodo();
  }

  const [todoList, setTodo] = useState(initList());

  const addTodo = () => {
    setTodo(todoList => [...todoList, [document.getElementById('newTodo').value, false]]);
    document.getElementById('newTodo').value = '';
  }

  const markDone = (index, e) => {
    const new_list = todoList.slice();
    new_list[index][1] = !new_list[index][1];
    setTodo(new_list);
  }

  useEffect(() => localStorage.setItem('6080-custom-hook', JSON.stringify(todoList)), [todoList])

  return (
    <div className="App" tabIndex="0" onKeyDown={KeyPress}>
      <div className="AddTodoContainer">
        <TextField className="textField" id="newTodo" label="New Todo..." variant="outlined" />
        <Button className="button" onClick={addTodo} variant="contained">Add Todo</Button>
      </div>
      <FormGroup className="FromContainer">
        {todoList && todoList.map((todo, index) =>
          <FormControlLabel
            control={<Checkbox checked={todo[1]} />} label={todo[0]}
            onChange={e => markDone(index, e)}
            key={index}
          />
        )}
      </FormGroup>
    </div>
  );
}

export default App;

import { useEffect, useState } from 'react'

function useLocalStorageState(localStorageKey, initialValue) {
  const [state, setState] = useState(() => {
    try {
      const valueInLocalStorage = localStorage.getItem(localStorageKey)

      if (!valueInLocalStorage) {
        return initialValue
      }

      // This will throw if the value in localStorage isn't a JSON string
      const parsedValueFromLocalStorage = JSON.parse(valueInLocalStorage)

      return parsedValueFromLocalStorage
    } catch (_err) {
      return initialValue
    }
  })

  useEffect(() => {
    localStorage.setItem(localStorageKey, JSON.stringify(state))
  }, [state, localStorageKey])

  return [state, setState]
}

function App() {
  const [todos, setTodos] = useLocalStorageState('todos', [
    { text: 'Make dinner', done: true },
    { text: 'Walk dog', done: false },
  ])
  const [newTodo, setNewTodo] = useLocalStorageState('new-todo', '')

  function toggleTodo(index) {
    todos[index].done = !todos[index].done
    setTodos([...todos])
  }

  function handleFormSubmit(event) {
    event.preventDefault()

    if (newTodo) {
      setTodos([...todos, { text: newTodo, done: false }])
      setNewTodo('')
    }
  }

  function handleNewTodoChange(event) {
    setNewTodo(event.target.value)
  }

  return (
    <>
      <ul>
        {todos.map((todo, i) => (
          <li key={i}>
            <label>
              <input
                onChange={() => toggleTodo(i)}
                type="checkbox"
                checked={todo.done}
              />
              {todo.text}
            </label>
          </li>
        ))}
      </ul>

      <form onSubmit={handleFormSubmit}>
        <input
          type="text"
          name="newTodo"
          placeholder="New Todo..."
          value={newTodo}
          onChange={handleNewTodoChange}
          required
        />
        <button type="submit">Add Todo</button>
      </form>
    </>
  )
}

export default App

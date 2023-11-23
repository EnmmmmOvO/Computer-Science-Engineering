import { BrowserRouter, Route, Routes } from 'react-router-dom'
import Home from './components/Home'
import Post from './components/Post'
import './App.css'

function App() {
  return (
    // Generally we wrap our App in a <BrowserRouter> component
    <BrowserRouter>
      <div className="App">
        {/* Dynamically render a component using Switch */}
        <Routes>
          <Route path="/" element={<Home />} />
          <Route path="/post/:id" element={<Post />} />
        </Routes>
      </div>
    </BrowserRouter>
  )
}

export default App

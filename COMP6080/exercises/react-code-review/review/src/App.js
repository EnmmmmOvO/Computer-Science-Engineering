import React, { useState } from 'react';
import Card from './Card';
import appStyles from './App.module.css';

let intervalId;
const API_URL = "https://api.github.com/users"

const App = () => {

  const [searchTerm, setSearchTerm] = useState('');
  const [cards, setCards] = useState([]);

  const fetchNewData = async (rawString) => {
    const eachUsername = rawString
                          .split(",")
                          .map(term => term.trim())
                          .filter(term => !!term);
    const fetchList = eachUsername.map(user => fetch(`${API_URL}/${user}`));
    const responses = await Promise.all(fetchList);
    const data = await Promise.all(responses.map(r => r.json()))
    setCards(data.map((props, index) => ({ ...props, index })))
  }

  const handleChange = event => {
    clearTimeout(intervalId);
    setSearchTerm(event.target.value);
    intervalId = setTimeout(() => fetchNewData(event.target.value), 500)
  };

  return (
    <>
      <input
        type="text"
        onChange={handleChange}
        value={searchTerm}
        placeholder="github usernames"
      />
      {cards.map(({ avatar_url, name, url, index }) => (
        <Card
          key={index}
          avatar_url={avatar_url}
          name={name}
          url={url}
        />
      ))}
    </>
  );
};

export default App;


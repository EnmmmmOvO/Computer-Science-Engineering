import React, { useState } from "react";
import "./App.css";

function App() {
  const [username, setUsername] = useState("");
  const [password, setPassword] = useState("");

  const login = async function () {
    // Attempt to login
    const response = await fetch("http://localhost:5000/api/login", {
      method: "POST",
      headers: {
        "Content-Type": "application/json",
      },
      body: JSON.stringify({
        username,
        password,
      }),
    });
    const data = await response.json();

    if (data.token) {
      console.log(data.token);
      // TODO store the token
    }
  };

  return (
    <div style={{ paddingLeft: "45vw" }}>
      <h1>Login</h1>
      <div>
        <h2>Username</h2>
        <input
          type="text"
          onChange={(event) => {
            setUsername(event.target.value);
          }}
        ></input>
      </div>
      <div>
        <h2>Password</h2>
        <input
          type="password"
          onChange={(event) => {
            setPassword(event.target.value);
          }}
        ></input>
      </div>
      <div>
        <input
          type="button"
          value="submit"
          onClick={(event) => {
            event.preventDefault();
            login();
          }}
        ></input>
      </div>
    </div>
  );
}

export default App;

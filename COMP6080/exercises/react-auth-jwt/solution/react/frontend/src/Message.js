import React, { useState, useEffect } from "react";

function Message() {
  const [username, setUsername] = useState("");
  const [message, setMessage] = useState("");

  useEffect(() => {
    // 2. Fetch the secret message
    const getMessage = async function () {
      const token = localStorage.getItem("token");
      const response = await fetch("http://localhost:5000/api/secret-message", {
        headers: {
          authorization: `JWT ${token}`,
        },
      });
      const data = await response.json();

      if (data.message) {
        setMessage(data.message);
        setUsername(data.authData.user.username);
      }
    };

    getMessage();
  });

  // 3. Display the logged in user and the secret message
  return (
    <h1>
      Hello {username}, the secret message is "{message}"!
    </h1>
  );
}

export default Message;

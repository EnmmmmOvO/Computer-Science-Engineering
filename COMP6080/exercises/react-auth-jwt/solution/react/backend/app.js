/**
 * This file mostly used resources from this tutorial:
 * https://www.simplilearn.com/tutorials/nodejs-tutorial/jwt-authentication
 */

import bodyParser from "body-parser";
import cors from "cors";
import express from "express";
import jwt from "jsonwebtoken";
const PORT_NUMBER = 5000;

// ! Usually you would put this into a .env file
const SECRET_KEY = "comp6080_secret_key";

const app = express();

// Use some basic middleware
app.use(cors());
app.use(bodyParser.urlencoded({ extended: true }));
app.use(bodyParser.json({ limit: "50mb" }));

/**
 * Publicly accessible API
 */
app.get("/api", (req, res) => {
  res.json({
    message: "Hey, there! Welcome to this API service",
  });
});

/**
 * API that returns a secret message if the request contains a JWT token
 */
app.get("/api/secret-message", verifyToken, (req, res) => {
  jwt.verify(req.token, SECRET_KEY, (err, authData) => {
    if (err) {
      res.sendStatus(403);
    } else {
      res.json({
        message: "Well done for completing a difficult challenge!",
        authData,
      });
    }
  });
});

/**
 * Login route. Can only login 1 user
 */
app.post("/api/login", (req, res) => {
  const user = {
    id: 1,
    username: "comp6080_student",
    email: "comp6080@unsw.edu.au",
  };

  // ! Usually some authorisation mechanism will be done here (e.g. checking password)
  if (req.body.username !== user.username) {
    res.json({
      error: "Invalid username or password.",
    });
  } else {
    // Sign the user's details & return the token
    jwt.sign({ user: user }, SECRET_KEY, (err, token) => {
      res.json({
        token,
      });
    });
  }
});

/**
 * Helper function to check if the request has the 'authorization' field in the header
 * Returns an error message to the user if there is no such field.
 */
function verifyToken(req, res, next) {
  const bearerHeader = req.headers["authorization"];

  if (typeof bearerHeader !== "undefined") {
    // Grab the token and set it as req.token
    const bearerToken = bearerHeader.split(" ")[1];
    req.token = bearerToken;
    next();
  } else {
    res.json({
      error:
        "Your request does not contain the 'authorization' value in the header.",
    });
  }
}

app.listen(PORT_NUMBER, () => console.log("Server started"));

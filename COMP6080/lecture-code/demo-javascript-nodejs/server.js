/*
Starts up a simple HTTP server with one GET route called "/scrape"
This route takes in a URL and a particular HTML tag to look for and count the number of instances of the tag
This route returns a simple object with the number of times that tag appears on a webpage
*/

const express = require('express');
const fs = require('fs');
const https = require('https');

const app = express();
const port = 3000;

let total = 0;


app.get('/scrape', (req, res) => {
  const response = fetch(req.query.url).then(a => a.json()).then(data => {
  	console.log(data);
  });

  res.send('.');
})

app.get('/secrets', (req, res) => {
  const data = fs.readFileSync('./data.json', { encoding: 'utf8' });
  console.log(data);
  res.send(data)
})

app.listen(port, () => {
  console.log(`Example app listening on port ${port}`)
})

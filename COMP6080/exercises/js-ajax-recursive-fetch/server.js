const express = require('express');
const cors = require('cors');
const app = express();

app.use(cors());
app.listen(3000, () => console.log('Server listening on port 3000'));

const USERS = [
	{
		'id': 0,
		'name': 'hayden',
	},
	{
		'id': 1,
		'name': 'emily',
	},
	{
		'id': 2,
		'name': 'clarence',
	},
	{
		'id': 3,
		'name': 'soorria',
	},
];

app.get('/users', (_, res) => {
	console.table(`Received request for ${USERS.map(({name}) => name)}`);
	res.send(USERS.map(({id}) => id));
});

app.get('/user/:id', (req, res) => {
	console.log(`Received request for user ${req.params.id}`);
	res.send(USERS.find((user) => user.id == req.params.id));
});
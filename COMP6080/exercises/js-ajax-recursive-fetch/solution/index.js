const ul = document.createElement('ul');
document.body.appendChild(ul);

/**
 * Calling `fetch` in a loop is not the ideal way to do it,
 * in this case it works but it's very inflexible,
 * as this function is basically not reusable.
 */
const loop = () => {
	fetch('http://localhost:3000/users')
		.then((res) => res.json())
		.then((users) => {
			for (const user of users) {
				fetch(`http://localhost:3000/user/${user}`)
					.then((res) => res.json())
					.then((user) => {
						const li = document.createElement('li');
						li.innerText = user.name;
						ul.append(li);
					});
			}
		});
};

/**
 * Using `Promise.all` is much preferred than calling `fetch` in a loop.
 */
const promiseAll = () => {
	fetch('http://localhost:3000/users')
		.then((res) => res.json())
		.then((users) => {
			Promise.all(users.map((user) => fetch(`http://localhost:3000/user/${user}`).then((res) => res.json())))
				.then((users) => {
					for (const user of users) {
						const li = document.createElement('li');
						li.innerText = user.name;
						ul.append(li);
					}
				});
		});
};

/**
 * Making a `new Promise` can help breaking our code into functions,
 * which makes it more reusable and modular and reduces `callback hell`.
 */
const newPromise = () => {
	const getUsers = new Promise((resolve, reject) => {
		fetch('http://localhost:3000/users')
			.then((res) => res.json())
			.then((users) => {
				Promise.all(users.map((user) => fetch(`http://localhost:3000/user/${user}`).then((res) => res.json())))
					.then(resolve)
			});
	});

	getUsers.then((users) => {
		for (const user of users) {
			const li = document.createElement('li');
			li.innerText = user.name;
			ul.append(li);
		}
	});
}

loop();
promiseAll();
newPromise();
const ul = document.createElement('ul');
document.body.appendChild(ul);


fetch('http://localhost:3000/users')
    .then(res => res.json())
    .then(post => post.forEach(getInfo));


const getInfo = (route) => {
    fetch(`http://localhost:3000/user/${route}`)
        .then(res => res.json())
        .then(post => {
            const li = document.createElement('li');
            ul.appendChild(li);
            li.innerText = post.name;
        })
}

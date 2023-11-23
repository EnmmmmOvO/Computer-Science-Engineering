const container = document.createElement('div');
container.setAttribute('id', 'container')
container.innerText = 'Loading, Please wait'
document.body.appendChild(container)
const createElement = text => {
    const box = document.createElement('div');
    box.className = 'box';
    box.innerText = text;
    container.appendChild(box);
    return box;
};

const xhr = new XMLHttpRequest();
xhr.open('GET', 'http://www.cse.unsw.edu.au/~cs6080/raw/data/package.json')
xhr.onload = (res) => {
    const list = JSON.parse(res.target.response)
    if (xhr.status === 200) {
        localStorage.setItem('exercise5', JSON.stringify(list));
        container.innerText = '';
        renderItems(list);
    } else handleError()
}
xhr.onerror = () => handleError()

try {
    xhr.send()
} catch (err) {
    console.log(err)
}

const handleError = () => {
    container.innerText = '';
        let jsonData = localStorage.getItem('exercise5');
        if(!jsonData) {
          displayMessage('No cached data. Please check your network');
          return;
        }
        renderItems(JSON.parse(jsonData));
        displayMessage('This data is not live');
}

const renderItems = res => {
    const namebox = createElement('name');
    const nameElement = createElement(res.name);
    const reindeers = createElement('reindeers');
    const numberElement = createElement(res.reindeers);
    const primary = createElement('primary');
    const primaryElement = createElement(res.primary);
};

const displayMessage = msg => {
    const p = document.createElement('p');
    p.innerText = msg;
    document.body.appendChild(p);
};
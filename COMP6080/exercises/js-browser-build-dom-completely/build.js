const body = document.getElementById('body');
const div = document.createElement('div');
div.style.background = '#cccccc';

const a = document.createElement('a');
a.target = '_blank';
a.href = 'https://google.com'
const img = document.createElement('img');
img.src = 'https://i.ytimg.com/vi/yJiVZUKAS84/maxresdefault.jpg'
img.alt = 'Me and my sibling'
a.appendChild(img);
div.appendChild(a);
div.appendChild(document.createElement('hr'));

const table = document.createElement('table');
const title = ['Name', 'Age', 'Height'];
const PEOPLE = [
    ['Sarah', 22, 188],
    ['Lin', 42, 134],
    ['Samir', 21, 155],
    ['Wayne', 29, 162],
    ['Eckhart', 112, 144]
];

const insert = (list, tag) => {
    let tr = document.createElement('tr');
    console.log(list);
    list.forEach(element => {
        const td = document.createElement(tag);
        td.style.fontWeight = 'bolder';
        td.textContent = element;
        tr.appendChild(td);
    });
    return tr;
};

table.appendChild(insert(title, 'th'));
PEOPLE.forEach(element => table.appendChild(insert(element, 'td')));
div.appendChild(table);
body.appendChild(div);
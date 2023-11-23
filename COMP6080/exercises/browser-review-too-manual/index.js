const body = document.getElementById('body')
const div = document.createElement('div');
div.style.background = '#cccccc';

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
    list.forEach(element => {
        console.log(element);
        const td = document.createElement(tag);
        td.style.fontWeight = 'bolder';
        td.textContent = element;
        tr.appendChild(td);
    });
    return tr;
};

table.appendChild(insert(title, 'th'));
table.style.textAlign = 'center';
PEOPLE.forEach(element => table.appendChild(insert(element, 'td')));

body.appendChild(div);
div.appendChild(table)
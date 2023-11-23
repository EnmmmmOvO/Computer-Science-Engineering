const data = [
      { name: 'Sarah', age: 22, height: 188, },
      { name: 'Lin', age: 42, height: 134, },
      { name: 'Samir', age: 21, height: 155, },
      { name: 'Wayne', age: 29, height: 162, },
      { name: 'Eckhart', age: 112, height: 144, },
];

const body = document.getElementById('body');

const div = document.createElement('div');
div.style.background = '#cccccc';

const table = document.createElement('table');

const createRow = (col1, col2, col3, header = false) => {
      const thtd = header ? 'th' : 'td';
      const secondRow = document.createElement('tr');
      const item1 = document.createElement(thtd);
      item1.appendChild(document.createTextNode(col1));
      const item2 = document.createElement(thtd);
      item2.appendChild(document.createTextNode(col2));
      const item3 = document.createElement(thtd);
      item3.appendChild(document.createTextNode(col3));
      secondRow.append(item1, item2, item3);
      table.appendChild(secondRow);
};

createRow('Name', 'Age', 'Height', true);
data.map(d => createRow(d['name'], d['age'], d['height']));

div.appendChild(table)
body.appendChild(div);
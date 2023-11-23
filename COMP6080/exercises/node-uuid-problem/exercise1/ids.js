const uuid = require('uuid');
const arr = Array.from(Array(30), () => uuid.v4()).sort();
console.log(arr.join('\n'))

const temp = arr.join('').split('').reduce((acc, c) => {
    acc[c] = acc[c] ? acc[c] + 1 : 1;
    return acc;
}, {});
delete temp['-'];
const dict = Object.entries(temp).sort(([, a], [, b]) => b - a);

console.log(dict.slice(5).filter(([a, b]) => b === dict[4][1]).reduce((out, c) => {
    out.push(c[0]);
    return out;
}, dict.slice(0, 5).map((pair) => pair[0])).join(' '))



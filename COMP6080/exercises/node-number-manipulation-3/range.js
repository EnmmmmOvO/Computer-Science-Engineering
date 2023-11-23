fs = require('fs');
const data = fs.readFileSync('data3.txt', 'utf8');

const array = data.split('\n').filter((str) => str !== '').map((str) => parseInt(str)).sort((a, b) => a - b);
console.log('The range is ', array[array.length - 1] - array[0]);
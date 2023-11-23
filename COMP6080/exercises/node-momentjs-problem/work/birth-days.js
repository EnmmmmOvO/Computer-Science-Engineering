let curr = require('moment')();
for (let k = 0; k < 14; k++, curr = curr.subtract(1, 'year')) {
    console.log(curr.format('dddd'));
}




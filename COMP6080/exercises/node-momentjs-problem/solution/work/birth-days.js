curr = require('moment')();
for (const i = 0; i < 14; i++){
    console.log(curr.format('dddd'));
    curr = curr.subtract(1, 'year');
}

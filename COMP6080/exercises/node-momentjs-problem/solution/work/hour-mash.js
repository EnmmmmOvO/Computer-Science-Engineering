const moment = require('moment')
const hours = moment().format('HH');
const day = moment().subtract(7, 'days').format('dddd');
const date = moment().format('DD/MM/YYYY');
const time = moment().format('LT');

console.log(`The day started [${hours}] hours ago. One week ago it was [${day}] at [${time}]. Today's date is [${date}]. \
There are exactly [${Math.floor(moment().day(5).startOf('day').add(9, 'hours').diff(moment())/1000)}] seconds until 9am on Friday.`)

const curr = require('moment')()
const last_week = curr.subtract(1, 'week');

console.log(`The day started [${curr.format('HH')}] hours ago. One week ago it was`,
`[${last_week.format('dddd')}] at [${last_week.format('LT')}]. Today's date is`,
`[${curr.format('DD/MM/YYYY')}]. There are exactly`,
`[${Math.floor(require('moment')().day(5).startOf('day').
add(9, 'hours').diff(require('moment')())/1000)}] seconds until 9am on Friday.`)

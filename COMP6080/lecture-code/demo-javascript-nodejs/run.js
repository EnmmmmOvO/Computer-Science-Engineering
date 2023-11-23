/*
(General/NodeJS) For each date, calculates how many days since that date have passed
(General) Creates a list of keys:value pairs that store date:days-since-date
(NodeJS) Outputs this as JSON to a file on the file system
*/

const fs = require('fs');
const differenceInDays = require('date-fns/differenceInDays');

function daysSinceDate(sinceDate) {
	const result = differenceInDays(
		Date.now(),
		sinceDate
	);
	return result;
}

const dates = process.argv.splice(2);

const dayssinceobj = {};

for (const date of dates) {
	const ymdSplit = date.split('/');
	const daysSince = daysSinceDate(new Date(ymdSplit[0], ymdSplit[1] - 1, ymdSplit[2], 0, 0));
	dayssinceobj[date] = daysSince;
}

const content = JSON.stringify(dayssinceobj);
try {
  fs.writeFileSync('./output.json', content);
} catch (err) {
  console.error(err);
}

const a = [1, 2, 3];
const b = [4, 5, ...a];
console.log(b);



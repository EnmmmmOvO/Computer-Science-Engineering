/* Thanks to Kaiqi Liang for a solution to base this off */

const uuid = require('uuid');
const NUM_IDS = 30;
const ids = Array.from(Array(NUM_IDS), () => uuid.v4());

ids.sort();
ids.forEach(console.log);

const occurrencesDict = ids.join('').split('').reduce((a, c) => {
    a[c] = a[c] ? a[c] + 1 : 1;
    return a;
}, {});

delete occurrencesDict['-'];
const occurrencesArray = Object.entries(occurrencesDict).sort(([,a],[,b]) => b - a)

const mostCommon = occurrencesArray.slice(0, 5).map(pair => pair[1]).reduce((a, c) => {
    a.push(c);
    return a;
}, []);

console.log(occurrencesArray.filter(pair => mostCommon.includes(pair[1])).map(pair => pair[0]).reduce((a, c) => {
    a += `${c} `;
    return a;
}, ''));

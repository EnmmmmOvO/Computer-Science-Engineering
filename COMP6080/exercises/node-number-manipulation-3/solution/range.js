fs = require('fs');
const data = fs.readFileSync('data.txt', 'utf8');

const lines = data.split("\n");

let min = 99999999999;
let max = -99999999999;

for (const line of lines) {
  if (line != '') {
    const number = parseInt(line);
    if (min > number) {
      min = number;
    }
    if (max < number) {
      max = number;
    }
  }
}

console.log('The range is ' + (max - min));


/* Advanced version below

```js
fs = require('fs');
const data = fs.readFileSync('data.txt', 'utf8');

const lines = data.split("\n").filter(l => l !== '').map(l => parseInt(l));
console.log(`The range is ${Math.max(...lines) - Math.min(...lines)}`);
````

> Key things that have been changed are
>  * Usage of filter to remove empty lines from input data
>  * Usage of map to transform data from string to integer
>  * Use of back quotes to add for easy interpolation and avoid the use of `+` concatenation
>  * I'm sure there are many more
> Things that might need discussion are:
>  * How you can chain the map and the filter
>  * How map and filter are passed in functions
>  * The spread operator being used on lines to turn it from a single argument of a list, to a list of arguments that are just an integer each

*/
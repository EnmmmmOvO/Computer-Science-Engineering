## Do some work combining javscript timeouts with promises

### Part 1: Find the error

Look at `fetchme.html`.

Why is this page not working as intended?

1. Fix the issue, so that the correct text loads
2. Handle the error case, such that if there is an issue during fetch that an appropriate error message is displayed

### Part 2: SetTimeout and Promises

You are given the following promises each with a separate setTimeout:

```
const promise1 = new Promise((resolve, reject) => {
    setTimeout(() => { resolve(1);}, 500);
});
  
const promise2 = new Promise((resolve, reject) => {
    setTimeout(() => { resolve(2); }, 400);
});

const promise3 = new Promise((resolve, reject) => {
    setTimeout(() => { resolve(3);}, 300); 
});
```

1. What would be the output of this code?

```
Promise.all([promise1, promise2,promise3]).then((res) => {
    console.log(res[0]);
    console.log(res[1]);
    console.log(res[2]);
});
```

2. What would be the output of this code?

```
promise1.then((res) => { console.log(res); }, (err) => { alert(err);});
promise2.then((res) => { console.log(res); }, (err) => { alert(err);});
promise3.then((res) => { console.log(res); }, (err) => { alert(err);});
```

3. Why are the results different even though the promises are the same?

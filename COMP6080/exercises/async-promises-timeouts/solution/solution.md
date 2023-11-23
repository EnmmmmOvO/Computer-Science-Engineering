Why is this page not working as intended?

1. Fix the issue, so that the correct text loads
2. Handle the error case, such that if there is an issue during fetch that an appropriate error message is displayed

> Firstly, on some browsers, you may be able to fetch directly from a local file (depending on how the web server or file server is setup). For this reason sometimes its good to run our local files within an HTTP server itself, that simply serves the local files
> To do this we can run `npx http-server ./` and then load `localhost:8000/fetchme.html` in the browser.
> Fetch needs to be dealt with as a promise. See `solutions/fetch.html`

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

> 1
> 2
> 3

2. What would be the output of this code?

```
promise1.then((res) => { console.log(res); }, (err) => { alert(err);});
promise2.then((res) => { console.log(res); }, (err) => { alert(err);});
promise3.then((res) => { console.log(res); }, (err) => { alert(err);});
```

> 3
> 2
> 1

3. Why are the results different even though the promises are the same?

> The Promise.all() takes an iterable array of promises as an input and the returned promise will resolve when all of the input's promises in the order that they were input in.
> Whereas, in the second question as all the promises have a separate setTimeout value, the results of the promises are in the order that it would take the setTimeout to resolve

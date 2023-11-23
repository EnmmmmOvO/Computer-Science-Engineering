const data = fetch('http://www.cse.unsw.edu.au/~cs6080/raw/data/doggo.txt')
    .then(res => res.text())
    .then(post => document.getElementById('dogname').innerText = post);

const promise1 = new Promise((resolve, reject) => {
    setTimeout(() => { resolve(1);}, 500);
});

const promise2 = new Promise((resolve, reject) => {
    setTimeout(() => { resolve(2); }, 400);
});

const promise3 = new Promise((resolve, reject) => {
    setTimeout(() => { resolve(3);}, 300);
});


Promise.all([promise1, promise2,promise3]).then((res) => {
    console.log(`All - ${res[0]}`);
    console.log(`All - ${res[1]}`);
    console.log(`All - ${res[2]}`);
});

promise1.then((res) => { console.log(`Separate - ${res}`); }, (err) => { alert(err);});
promise2.then((res) => { console.log(`Separate - ${res}`); }, (err) => { alert(err);});
promise3.then((res) => { console.log(`Separate - ${res}`); }, (err) => { alert(err);});


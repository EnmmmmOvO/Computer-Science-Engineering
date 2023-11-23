const counter = document.getElementById('counter');
counter.textContent = '0';


document.getElementById('increment').addEventListener('click', (e) => {
    const n = parseInt(counter.textContent) + 1;
    if (n > 10) window.alert('You can\'t increment past 10');
    else counter.textContent = `${n}`;
});


document.getElementById('decrement').addEventListener('click', (e) => {
    const n = parseInt(counter.textContent) - 1;
    if (n < 0) window.alert('You can\'t decrement below 0');
    else counter.textContent = `${n}`;
});
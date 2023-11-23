const body = document.getElementById('body');
const div = document.createElement('div');
const list = ['The', 'Duck', 'Lemonade', 'Stand'];

const add = (sentence, type) => {
    const temp = document.createElement(type);
    temp.textContent = sentence;
    return temp;
}

div.appendChild(add('Hello there,', 'p'));
div.appendChild(add('I am a llama, hear my sirens roar:', 'p'));

const ul = document.createElement('ul');
list.forEach(element => ul.appendChild(add(element, 'li')));

div.appendChild(ul);
body.appendChild(div);


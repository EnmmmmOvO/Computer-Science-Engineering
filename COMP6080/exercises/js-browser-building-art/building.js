const building = document.getElementById('building');
const create_square = () => {
    const square = document.createElement('div');
    square.style.display = 'inline-block';
    square.className = 'window';
    square.style.height = '50px';
    square.style.width = '50px';
    square.style.margin = '25px';
    return square
}

const move_building = (position) => {
    // const left = window.getComputedStyle(building).left;
    // const new_left = parseInt(left.split('px')[0])  + position * 50
    // building.style.left = `${new_left}px`;
    building.style.left = (building.offsetLeft + position * 50) + 'px'
}

for (let i = 0; i < 9; ++i) building.appendChild(create_square());

document.addEventListener('keydown', (events) => {
    switch (events.key) {
        case ('ArrowUp'): building.appendChild(create_square()); break;
        case ('ArrowDown'):
            const remove_window = document.getElementsByClassName('window');
            if (remove_window.length > 0) {
                // building.removeChild(remove_window[0]);
                building.removeChild(building.lastChild);
            } else window.alert('No Window can delete!');
            break;
        case ('ArrowLeft'): move_building(-1); break;
        case ('ArrowRight'): move_building(1); break;
    }
})

document.addEventListener('mousedown', () => {
    const body = document.body;
    if (body.hasAttribute("night")) {
        body.removeAttribute("night");
    } else {
        body.setAttribute("night", "");
    }
});
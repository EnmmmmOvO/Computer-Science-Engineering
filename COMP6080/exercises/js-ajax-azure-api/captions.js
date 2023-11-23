const input = document.getElementById('input');
const image = document.createElement('img');

input.onchange = () => {
    const file = input.files[0];

    image.src = URL.createObjectURL(file);
    image.alt = file.name;
    document.body.appendChild(image);

    getCaption(file);
}

const getCaption = (file) => {
    const options = {
        method: 'POST',
        headers: {
            'Ocp-Apim-Subscription-Key': 'cab35e65e5ce49649bce71f137c14168',
            'Content-Type': 'application/octet-stream'
        },
        body: file
    }
    fetch('https://6080test.cognitiveservices.azure.com/vision/v3.2/describe', options)
        .then(res => {
            if (res.ok) return res.json();
            else throw new Error(`Network Error: ${res.status}`);
        })
        .then(post => {
            const first_match = post.description.captions[0];
            document.getElementById('caption').textContent = `${first_match.text} Confidence: ${first_match.confidence}`
        })
        .catch(err => console.error(err))
}
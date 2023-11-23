const imageSubmission = document.getElementById("imgFile");
const imagePreview = document.getElementById("imgPreview");
const captionText = document.getElementById("caption");

imageSubmission.onchange = () => {
    const file = imageSubmission.files[0];
    updateImage(file);
    getDescription(file);
};

const updateImage = (file) => {
    imagePreview.src = URL.createObjectURL(file);
};

const getDescription = (file) => {
    options = {
        method: 'POST',
        headers: {
            'Ocp-Apim-Subscription-Key': '059ac09de62543a5bc19e1576d865cb4',
            'Content-Type': 'application/octet-stream'
        },
        body: file
    };
    fetch("https://ex05.cognitiveservices.azure.com/vision/v3.2/describe", options)
        .then(response => response.json())
        .then(response => {
            const caption = handleResponse(response);
            if (caption) updateAltText(caption);
            console.log(response.description);
        });
};

const handleResponse = (response) => {
    const captionsObject = response.description.captions[0];
    if (captionsObject) {
        return `${captionsObject.text} (with ${captionsObject.confidence.toFixed(2) * 100}% confidence)`;
    }
};

const updateAltText = (caption) => {
    captionText.innerText = 'Alt-text: ' + caption;
    imagePreview.alt = caption;
};
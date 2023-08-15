import csv
import re
import os
import glob
import torch
import json

from torchvision.transforms import transforms
from torch.utils.data import Dataset, DataLoader
from PIL import Image
from os.path import join
from torchvision.models import resnet50
from transformers import GPT2Tokenizer, GPT2LMHeadModel
from tqdm import tqdm
from model import Resnet_LSTM
from itertools import groupby
from difflib import SequenceMatcher
from sklearn.feature_extraction.text import TfidfVectorizer
from sklearn.metrics.pairwise import cosine_similarity

# Setting the device to CUDA if available, else to MPS for Mac
device = torch.device('cuda' if torch.cuda.is_available() else 'mps')


# Function to remove repeated words from a sentence
def remove_repeated_words(sentence):
    return ' '.join(word for word, _ in groupby(sentence.split()))


# Function for calculating the cos similarity between two sentences
def calculate_similarity(text1, text2):
    vectorizer = TfidfVectorizer().fit_transform([text1, text2])
    vectors = vectorizer.toarray()
    cosine_sim = cosine_similarity(vectors)
    return cosine_sim[0][1]


# Defining a custom Dataset class for images
class ImageDataset(Dataset):
    def __init__(self, path, preprocess):
        self.images = []
        self.image_names = []
        self.preprocess = preprocess
        # Loop through all the files in the specified path
        for file in glob.glob(join(path, '*')):
            filename = os.path.basename(file)
            # Skip file if it is not a PNG image
            if 'png' not in filename:
                continue
            # Open and convert the image to RGB
            image = Image.open(file).convert('RGB')

            self.images.append(image)
            self.image_names.append(filename)

    def __getitem__(self, item):
        image = self.images[item]
        image = self.preprocess(image)
        return image, self.image_names[item]

    def __len__(self) -> int:
        return len(self.images)


# Function to load a model from a checkpoint
def load_model(model_path):
    # Initialize the GPT-2 tokenizer and add a padding token
    tokenizer = GPT2Tokenizer.from_pretrained('gpt2')
    tokenizer.pad_token_id = 0
    # Initialize the ResNet-50 model
    resnet_model = resnet50(pretrained=True)
    # Initialize the GPT-2 model
    gpt2_model = GPT2LMHeadModel.from_pretrained('gpt2')
    # Initialize the custom model and load the checkpoint
    model = Resnet_LSTM(resnet_model, gpt2_model, 1024)
    model.load_state_dict(torch.load(model_path, map_location='mps'))
    model.to(device)

    return model


# Function to generate predictions and save them to a CSV file
def generate_and_save_predictions(model, dataloader):
    model.eval()
    # Initialize the GPT-2 tokenizer
    tokenizer = GPT2Tokenizer.from_pretrained('gpt2')
    # Load the test data
    with open('/Users/enmmmmovo/Downloads/part-000003/part-000003.json', 'r') as f:
        data = json.load(f)

    # Lists to store the results
    image = list()
    sentences = list()
    original = list()
    quick_similarity = list()
    similarity = list()
    cos_similarity = list()

    # Loop through the images in the dataloader
    with torch.no_grad():
        for images, image_names in tqdm(dataloader):
            images = images.to(device)
            attention_mask = torch.ones(images.size(0), 200).to(device)
            output = model(images, attention_mask)
            predicted_ids = output.argmax(dim=-1)
            for i in range(predicted_ids.size(0)):
                # Decode the predicted tokens
                tokens = predicted_ids[i].tolist()
                pre = tokenizer.decode(tokens).encode("ascii", errors="ignore").decode()
                pre = re.sub(",+", ",", pre)
                pre = remove_repeated_words(re.sub(" +", " ", pre))
                # Compare the prediction with the original sentence
                matcher = SequenceMatcher(None, pre, data[image_names[i]]["p"])
                # Store the results
                image.append(image_names[i])
                sentences.append(pre)
                original.append(data[image_names[i]]["p"])
                quick_similarity.append(matcher.quick_ratio() * 100)
                similarity.append(matcher.ratio() * 100)
                cos_similarity.append(calculate_similarity(pre, data[image_names[i]]["p"]) * 100)

    # Save the results to a CSV file
    with open('output.csv', 'w', newline='') as f:
        writer = csv.writer(f)
        writer.writerow(
            ["Image", "Generated Sentence", "Original Sentence", "quick_ratio", "ratio", "cosine_similarity"])
        for i in range(len(image)):
            writer.writerow([image[i], sentences[i], original[i], "{:.2f}".format(quick_similarity[i]),
                             "{:.2f}".format(similarity[i]), "{:.2f}".format(cos_similarity[i])])


def main():
    # Load the model
    model = load_model('checkModel.pth')
    # Initialize the dataset and dataloader
    dataset = ImageDataset('/Users/enmmmmovo/Downloads/part-000003',
                           transforms.Compose([transforms.CenterCrop(224),
                                               transforms.ToTensor(),
                                               transforms.Normalize([0.485, 0.456, 0.406],
                                                                    [0.229, 0.224, 0.225])]))
    dataloader = DataLoader(dataset, batch_size=1, shuffle=False)
    # Generate and save the predictions
    generate_and_save_predictions(model, dataloader)


# If this script is run as the main script, call the main function
if __name__ == '__main__':
    main()

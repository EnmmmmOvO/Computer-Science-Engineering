import difflib
import numpy as np
import torch
from transformers import BertConfig, BertTokenizer, GPT2Tokenizer
from tqdm import tqdm
import json
import os
import glob
import skimage.io as io
from torch.utils.data import Dataset, DataLoader
from PIL import Image
from clip_model import ClipCaptionModel
from loguru import logger
from os.path import join
import torch.nn.functional as nnf
import torch.nn.functional as F
import PIL.Image
import clip
import csv


class ImageDataset(Dataset):
    def __init__(self, path, preprocess):
        self.images = []
        self.image_names = []

        # Load all images from the given path and preprocess them
        for file in glob.glob(join(path, '*')):
            image = io.imread(file)
            image = preprocess(Image.fromarray(image)).squeeze(0).to(device)
            filename = os.path.basename(file)

            self.images.append(image)
            self.image_names.append(filename)

    def __getitem__(self, item):
        # Return the preprocessed image and its filename
        return self.images[item], self.image_names[item]

    def __len__(self) -> int:
        return len(self.images)


def generate2(
        model,
        tokenizer,
        tokens=None,
        prompt=None,
        embed=None,
        entry_count=1,
        entry_length=50,  # maximum number of words
        top_p=0.9,
        temperature=1.0,
        stop_token: str = ".",
):
    model.eval()
    generated_num = 0
    generated_list = []
    stop_token_index = tokenizer.encode(stop_token)[0]
    filter_value = -float("Inf")
    device = next(model.parameters()).device

    with torch.no_grad():

        for entry_idx in range(entry_count):
            # If an embedding is provided, use it, otherwise generate an embedding from the provided tokens or prompt
            if embed is not None:
                generated = embed
            else:
                if tokens is None:
                    tokens = torch.tensor(tokenizer.encode(prompt))
                    tokens = tokens.unsqueeze(0).to(device)

                generated = model.gpt2.transformer.wte(tokens)

            # Generate text of the specified length
            for i in range(entry_length):
                # Get the model outputs
                outputs = model.gpt2(inputs_embeds=generated)
                outputs = outputs.logits

                # Apply the temperature
                outputs = outputs[:, -1, :] / (temperature if temperature > 0 else 1.0)
                sorted_logits, sorted_indices = torch.sort(outputs, descending=True)
                cumulative_probs = torch.cumsum(
                    nnf.softmax(sorted_logits, dim=-1), dim=-1
                )
                sorted_indices_to_remove = cumulative_probs > top_p
                sorted_indices_to_remove[..., 1:] = sorted_indices_to_remove[
                                                    ..., :-1
                                                    ].clone()
                sorted_indices_to_remove[..., 0] = 0

                indices_to_remove = sorted_indices[sorted_indices_to_remove]
                outputs[:, indices_to_remove] = filter_value

                # Get the token with the highest probability
                next_token = torch.argmax(outputs, -1).unsqueeze(0)

                # Get the embedding for the next token
                next_token_embed = model.gpt2.transformer.wte(next_token)

                # Add the token to the list of tokens
                if tokens is None:
                    tokens = next_token
                else:
                    tokens = torch.cat((tokens, next_token), dim=1)

                # Add the token embedding to the list of embeddings
                generated = torch.cat((generated, next_token_embed), dim=1)

                # If the stop token is encountered, end the generation
                if stop_token_index == next_token.item():
                    break

            # Convert the tokens to text
            output_list = list(tokens.squeeze().cpu().numpy().flatten())
            output_text = tokenizer.decode(output_list)
            generated_list.append(output_text)

    return generated_list


def generate_beam(
        model,
        tokenizer,
        beam_size: int = 5,
        prompt=None,
        embed=None,
        entry_length=67,
        temperature=1.0,
        stop_token: str = ".",
):
    # This function uses beam search to generate text
    model.eval()
    stop_token_index = tokenizer.encode(stop_token)[0]
    sti = tokenizer.encode("!")[0]
    tokens = None
    scores = None
    device = next(model.parameters()).device
    seq_lengths = torch.ones(beam_size, device=device)
    is_stopped = torch.zeros(beam_size, device=device, dtype=torch.bool)

    with torch.no_grad():
        # If an embedding is provided, use it, otherwise generate an embedding from the provided tokens or prompt
        if embed is not None:
            generated = embed
        else:
            if tokens is None:
                tokens = torch.tensor(tokenizer.encode(prompt))
                tokens = tokens.unsqueeze(0).to(device)
                generated = model.gpt.transformer.wte(tokens)
        for i in range(entry_length):
            outputs = model.gpt2(inputs_embeds=generated)
            logits = outputs.logits
            logits = logits[:, -1, :] / (temperature if temperature > 0 else 1.0)
            logits = logits.softmax(-1).log()

            # This block handles the beam search. It keeps track of the scores and generated tokens, and applies the
            # beam search algorithm
            if scores is None:
                # This is the first iteration, we just take the top `beam_size` tokens
                scores, next_tokens = logits.topk(beam_size, -1)
                generated = generated.expand(beam_size, *generated.shape[1:])
                next_tokens, scores = next_tokens.permute(1, 0), scores.squeeze(0)
                if tokens is None:
                    tokens = next_tokens
                else:
                    tokens = tokens.expand(beam_size, *tokens.shape[1:])
                    tokens = torch.cat((tokens, next_tokens), dim=1)
            else:
                # In subsequent iterations, we combine the scores with the scores from previous steps, and keep the
                # top `beam_size` sequences
                logits[is_stopped] = -float(np.inf)
                logits[is_stopped] = -float(np.inf)
                logits[is_stopped, 0] = 0
                scores_sum = scores[:, None] + logits
                seq_lengths[~is_stopped] += 1
                scores_sum_average = scores_sum / seq_lengths[:, None]
                scores_sum_average, next_tokens = scores_sum_average.view(-1).topk(
                    beam_size, -1
                )
                next_tokens_source = next_tokens // scores_sum.shape[1]
                seq_lengths = seq_lengths[next_tokens_source]
                next_tokens = next_tokens % scores_sum.shape[1]
                next_tokens = next_tokens.unsqueeze(1)
                tokens = tokens[next_tokens_source]
                tokens = torch.cat((tokens, next_tokens), dim=1)
                generated = generated[next_tokens_source]
                scores = scores_sum_average * seq_lengths
                is_stopped = is_stopped[next_tokens_source]
            next_token_embed = model.gpt2.transformer.wte(next_tokens.squeeze()).view(
                generated.shape[0], 1, -1
            )
            generated = torch.cat((generated, next_token_embed), dim=1)
            is_stopped = is_stopped + next_tokens.eq(stop_token_index).squeeze()

            # If all sequences have stopped, break the loop
            if is_stopped.all():
                break
    scores = scores / seq_lengths
    output_list = tokens.cpu().numpy()
    output_texts = [
        tokenizer.decode(output[: int(length)])
        for output, length in zip(output_list, seq_lengths)
    ]
    order = scores.argsort(descending=True)
    output_texts = [output_texts[i] for i in order]
    return output_texts


def string_similar(s1, s2):
    # This function calculates the quick similarity between two strings
    return difflib.SequenceMatcher(None, s1, s2).quick_ratio()


def main(filename):
    # This function loads a model from a file, and uses it to generate text for a set of images
    tokenizer = GPT2Tokenizer.from_pretrained("gpt2")
    model = ClipCaptionModel(10, 512, True, None).to(device)
    model.load_state_dict(torch.load(filename, map_location=device))
    model.eval()
    clip_model, preprocess = clip.load("ViT-B/32", device=device, jit=False)
    list_ = list()
    with open("part-000001.json") as f:
        data = json.load(f)
    idx = 0
    for file in glob.glob(join("DataSet_test/", '*')):
        name = file[13:]
        image = io.imread(file)
        pil_image = PIL.Image.fromarray(image)
        image = preprocess(pil_image).unsqueeze(0).to(device)
        with torch.no_grad():
            prefix = clip_model.encode_image(image).to(
                device, dtype=torch.float32
            )
            prefix_embed = model.clip_project(prefix).reshape(1, 10, -1)
            cc = generate2(model, tokenizer, embed=prefix_embed)
            score = string_similar(str(data[name]["p"]), str(cc[0]))
            score = str(round(score, 4) * 100) + "%"
            list_.append([name, str(data[name]["p"]), str(cc[0]), score])

    with open("GT_Prediction_result.csv", 'w') as f:
        writer = csv.writer(f)
        writer.writerow(["Name", "Original prompts", "Predict prompts", "Text Similarity"])
        writer.writerows(list_)


torch.cuda.empty_cache()
device = torch.device('cuda:0')
main(r"model/checkModel_5k.pth")

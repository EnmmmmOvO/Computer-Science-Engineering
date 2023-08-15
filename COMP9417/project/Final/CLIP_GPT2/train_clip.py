from typing import Tuple
import clip
import os
import json
import torch
from datasets import load_dataset
import torch.nn.functional as F
import transformers
from tqdm import tqdm
from skimage import io
from PIL import Image
from torch import nn
from loguru import logger
import pickle
from transformers import GPT2Tokenizer, GPT2LMHeadModel
from torch.utils.data import Dataset, DataLoader


def image_encoder(dataset, mode, f3):
    # Get the list of available CLIP models
    model = clip.available_models()
    print(model)
    # Get the user input to select the encoding model
    m = int(input("Enter the corresponding index of the above array to select the coding model: "))
    # Load the selected CLIP model and the associated preprocessing function
    clip_model, preprocess = clip.load(model[m], device=device, jit=False)
    # Initialize an empty dictionary to store the image embeddings
    idx2embed = {}
    # Initialize an empty list to store the prompts (captions)
    prompts = list()
    with tqdm(range(dataset.num_rows['train']), desc='Embedding and split prompts') as pbar:
        for i in pbar:
            # Read the image and apply the preprocessing function
            image = io.imread(str(dataset.data['train']['image'][0][1]))
            image = preprocess(Image.fromarray(image)).unsqueeze(0).to(device)

            # Generate image embeddings using the CLIP model
            with torch.no_grad():
                clip_embed = clip_model.encode_image(image).cpu()

            # Store the image embeddings in the dictionary and the prompt (caption) in the list
            idx2embed[i] = clip_embed
            prompts.append(str(dataset.data['train']['prompt'][i]))
            pbar.update()
        pbar.close()
    # Log the number of image embeddings and prompts
    logger.info('num of image embedding and prompts:{}'.format(len(idx2embed)))

    # Save the prompts and image embeddings to a file
    if mode == "train":
        with open(f3, 'wb') as f:
            pickle.dump([prompts, idx2embed], f)
    else:
        with open(f3, 'wb') as f:
            pickle.dump([prompts, idx2embed], f)
    return prompts, idx2embed


class makeDataset(Dataset):
    def __init__(self, len_prefix, normalization, datasets, filename, f2):
        # Store the prefix length and the normalization flag
        self.normalization = normalization
        self.prefix_length = len_prefix

        # Load the GPT2 tokenizer
        self.tokenizer = GPT2Tokenizer.from_pretrained("gpt2")
        self.embed_list = list()

        # Check if the data has already been processed and saved in a file，If not, process the data and save to a file
        if os.path.isfile(f2):
            with open(f2, 'rb') as f:
                self.embed_list, self.text_list, self.max_seq_len = pickle.load(f)
            logger.info('num of data:{}'.format(len(self.embed_list)))
        else:
            self.text_list = list()
            self.embed_list = list()
            max_seq_len = 0

            # Check if the prompts and image embeddings have already been generated and saved in a file
            if os.path.isfile(filename):
                with open(filename, 'rb') as f:
                    prompts, idx2embd = pickle.load(f)
            else:
                prompts, idx2embd = image_encoder(datasets, "train", f2)

            # Loop over the prompts and encode them using the GPT2 tokenizer
            with tqdm(range(len(prompts)), desc='Embedding prompts') as pbar:
                for i in pbar:
                    text_encoder = torch.tensor(self.tokenizer.encode(prompts[i]), dtype=torch.int64)
                    self.text_list.append(text_encoder)
                    self.embed_list.append(idx2embd[i].squeeze(0).float())
                    max_seq_len = max(max_seq_len, self.text_list[-1].shape[0])
                    pbar.update()
                pbar.close()

            # Save the text encodings, image embeddings, and maximum sequence length to a file
            with open(f2, 'wb') as f:
                pickle.dump([self.embed_list, self.text_list, max_seq_len], f)

        # Calculate the maximum sequence length as the mean plus 10 standard deviations of the lengths of all sequences,
        # but not more than the maximum length of any sequence
        all_len = torch.tensor([len(self.text_list[i]) for i in range(len(self))]).float()
        self.max_seq_len = min(int(all_len.mean() + all_len.std() * 10), int(all_len.max()))

    def pad_tokens(self, item: int):
        # Get the tokens for the given item
        tokens = self.text_list[item]

        # Calculate the number of padding tokens needed
        padding = self.max_seq_len - tokens.shape[0]

        # If padding is needed, add it to the tokens
        if padding > 0:
            tokens = torch.cat((tokens, torch.zeros(padding, dtype=torch.int64) - 1))
            self.text_list[item] = tokens
        elif padding < 0:
            tokens = tokens[:self.max_seq_len]
            self.text_list[item] = tokens

        # Create a mask that is zero where we are out of sequence
        mask = tokens.ge(0)

        # Mask out-of-sequence tokens
        tokens[~mask] = 0

        # Convert the mask to a float tensor
        mask = mask.float()

        # Add a mask for the prefix
        mask = torch.cat((torch.ones(self.prefix_length), mask), dim=0)  # adding prefix mask
        return tokens, mask

    def __len__(self) -> int:
        return len(self.text_list)

    def __getitem__(self, index: int) -> Tuple[torch.Tensor, ...]:
        embed = self.embed_list[index]
        tokens, mask = self.pad_tokens(index)
        if self.normalization:
            embed = embed.float()
            embed = embed / embed.norm(2, -1)
        return embed, tokens, mask


def evaluate(model, dev_loader):
    # Switch the model to evaluation mode
    model.eval()
    #     logger.info("Running evaluation")
    eval_loss = 0.0
    with torch.no_grad():
        for data in dev_loader:
            # Move data to device
            embed_list, text_list, mask_list = data
            embed_list = embed_list.to(device).float()
            text_list = text_list.to(device, dtype=torch.int64)
            mask_list = mask_list.to(device)

            # Forward pass
            logits = model(embed_list, text_list, mask_list)
            logits = logits[:, model.prefix_len - 1: -1]

            # Flatten the labels
            shift_labels = text_list.flatten()

            # Calculate loss
            loss = F.cross_entropy(logits.reshape(-1, logits.shape[-1]), shift_labels, ignore_index=0)

            # Average the loss over all entries in the batch
            loss = loss.mean()

            # Add the batch loss to the total loss
            eval_loss += loss

    return eval_loss


def train(model, train_loader, dev_loader, optimizer, scheduler, f3):
    # Switch the model to training mode
    model.train()
    logger.info("start training")

    # Initialize the list to store loss values
    loss_tt = list()
    for epoch in range(p.epochs):
        logger.info('start {}-th epoch training'.format(epoch + 1))
        for batch_idx, data in enumerate(tqdm(train_loader)):
            model.zero_grad()

            # Compute the step number
            step = epoch * len(train_loader) + batch_idx + 1

            # Move data to device
            embed_list, text_list, mask_list = data
            embed_list = embed_list.to(device).float()
            text_list = text_list.to(device, dtype=torch.int64)
            mask_list = mask_list.to(device)

            # Forward pass
            logits = model(embed_list, text_list, mask_list)

            # Flatten the labels
            logits = logits[:, model.prefix_len - 1: -1]

            # Calculate loss
            shift_labels = text_list.flatten()
            loss = F.cross_entropy(logits.reshape(-1, logits.shape[-1]), shift_labels, ignore_index=0)
            # Perform backpropagation
            loss.backward()
            # Update the weights, and adjust the learning rate
            optimizer.step()
            scheduler.step()
            optimizer.zero_grad()

        # Evaluate the model on the validation set
        dev_loss = evaluate(model, dev_loader)
        # Switch the model back to training mode
        model.train()
        # Log the losses
        loss_tt.append((step, loss.item(), dev_loss.item()))
        logger.info('test loss at epoch {} is {}'.format(epoch + 1, dev_loss.item()))
        logger.info('train loss at epoch {} is {}'.format(epoch + 1, loss))

        # Save the model every 2 epochs
        if (epoch + 1) % 2 == 0:
            logger.info('saving checkpoint at epoch {}'.format(epoch + 1))
            torch.save(model.state_dict(), r"/kaggle/working/checkModel" + str(epoch + 1) + " .pth")
    with open(f3, 'w') as f:
        for i in loss_tt:
            f.write(str(i[0]) + '\t' + str(i[1]) + '\t' + str(i[2]) + '\n')


class MLP(nn.Module):

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.model(x)

    def __init__(self, sizes: Tuple[int, ...], bias=True, act=nn.Tanh):
        super(MLP, self).__init__()

        # Create a list to hold the layers of the MLP
        layers = []
        for i in range(len(sizes) - 1):
            # Add a linear layer
            layers.append(nn.Linear(sizes[i], sizes[i + 1], bias=bias))

            # Add an activation function (except for the last layer)
            if i < len(sizes) - 2:
                layers.append(act())

        # Create the MLP as a sequence of layers
        self.model = nn.Sequential(*layers)


class ClipCaptionModel(nn.Module):

    def __init__(self, prefix_len, clip_size,
                 finetune_gpt2, constant_len=10):
        super(ClipCaptionModel, self).__init__()

        # Load the pretrained GPT-2 model
        self.gpt2 = GPT2LMHeadModel.from_pretrained('gpt2')

        # Define the size of the prefix
        self.prefix_size = self.gpt2.transformer.wte.weight.shape[1]
        self.prefix_len = prefix_len

        # Define the projection layer for CLIP embeddings
        self.clip_project = MLP((clip_size, (self.prefix_size * prefix_len) // 2, self.prefix_size * prefix_len))

        # Define whether to finetune the GPT-2 model
        self.finetune_gpt2 = finetune_gpt2

    def forward(self, clip_embeds, caption_ids, mask):
        # Convert caption IDs to embeddings
        caption_embeds = self.gpt2.transformer.wte(caption_ids)

        # Project CLIP embeddings to the prefix size
        prefix_embeds = self.clip_project(clip_embeds).view(-1, self.prefix_len, self.prefix_size)

        # Concatenate the prefix and caption embeddings
        embedding_cat = torch.cat((prefix_embeds, caption_embeds), dim=1)

        # Pass the concatenated embeddings through the GPT-2 model
        out = self.gpt2(inputs_embeds=embedding_cat, attention_mask=mask)
        # logits:[bs, prefix_len+caption_len, prefix_size]
        logits = out.logits
        return logits

    def parameters(self, recurse: bool = True):
        # If finetuning the GPT-2 model, return all parameters, otherwise return only the projection layer parameters
        if self.finetune_gpt2:
            return super(ClipCaptionModel, self).parameters()
        else:
            return self.clip_project.parameters()

    def train(self, mode: bool = True):
        # Check the type of mode
        if not isinstance(mode, bool):
            raise ValueError("training mode is expected to be boolean")

        # Set the training mode
        self.training = mode
        for module in self.children():
            module.train(mode)

        # If not finetuning the GPT-2 model, set it to evaluation mode
        if not self.finetune_gpt2:
            self.gpt2.eval()
        return self


def main(filename, f2, f3, d):
    # Clear the GPU memory
    torch.cuda.empty_cache()

    # Instantiate the model and move it to the device
    model = ClipCaptionModel(p.prefix_len, p.img_size, p.tune).to(device)

    # Instantiate the dataset
    dataset = makeDataset(p.prefix_len, p.isNormalize, d, filename, f2)

    # Split the dataset into training and validation sets
    test_size = int(p.test_split * len(dataset))
    train_dataset, dev_dataset = torch.utils.data.random_split(dataset,
                                                               [len(dataset) - test_size,
                                                                test_size])
    # Instantiate the data loaders
    train_dataloader = DataLoader(train_dataset, batch_size=p.batch_size, shuffle=True)
    dev_loader = 0
    dev_loader = DataLoader(dev_dataset, batch_size=p.batch_size, shuffle=True)

    # Compute the total number of steps
    t_total = len(train_dataloader) * p.epochs

    # Instantiate the optimizer and the learning rate scheduler
    optimizer = transformers.AdamW(model.parameters(), lr=p.lr)
    scheduler = transformers.get_linear_schedule_with_warmup(
        optimizer, num_warmup_steps=int(t_total * 0.1), num_training_steps=t_total
    )

    train(model, train_dataloader, dev_loader, optimizer, scheduler, f3)


p = {
    "prefix_len": 10,
    "img_size": 512,
    "tune": True,
    "isNormalize": True,
    "batch_size": 40,
    "test_split": 0.2,
    "epochs": 40,
    "lr": 1e-4
}


class DotDict(dict):
    def __init__(self, *args, **kwargs):
        super(DotDict, self).__init__(*args, **kwargs)

    def __getattr__(self, key):
        value = self[key]
        if isinstance(value, dict):
            value = DotDict(value)
        return value


p = DotDict(p)

torch.cuda.empty_cache()
device = torch.device('cpu')
dataset = load_dataset("poloclub/diffusiondb", '2m_first_1k')
main(r'model/train_for_dataset_1k.pkl', r'encoder_for_train_1k.pkl', r'loss_1k.txt', dataset)

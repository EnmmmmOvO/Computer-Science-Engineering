#!/usr/bin/env python3.9
from typing import Tuple
import clip
import os
import json
import torch
import torch.nn.functional as F
import transformers
from tqdm import tqdm
from torch.utils.tensorboard import SummaryWriter
from clip_model import ClipCaptionModel
from skimage import io
from PIL import Image
from loguru import logger
import pickle
from transformers import GPT2Tokenizer, BertTokenizer
from torch.utils.data import Dataset, DataLoader
import config as p


def remove_symbol(filename):
    dir = os.listdir(filename)
    idx = 0
    dataSet = list()

    for i in dir:
        with open(filename + "/" + i + "/" + i + ".json") as f:
            data = json.load(f)
            for key in data.keys():
                # prompts = re.sub('[!#?,.:";+-]', '', data[key]["p"])
                dataSet.append((idx, filename + "/" + i + "/" + key, str(data[key]["p"])))
                # print(data[key]["p"])
                idx += 1
    return dataSet


def image_encoder(filename, mode):
    model = clip.available_models()
    print(model)
    m = int(input("Enter the corresponding index of the above array to select the coding model: "))
    clip_model, preprocess = clip.load(model[m], device=device, jit=False)
    idx2embed = {}
    data = remove_symbol(filename)
    for i in data:
        logger.info('The image with id %d is being encoded' % i[0])
        image = io.imread(i[1])
        image = preprocess(Image.fromarray(image)).unsqueeze(0).to(device)
        with torch.no_grad():
            clip_embed = clip_model.encode_image(image).cpu()
        idx2embed[i[0]] = clip_embed
        # print(i[0], idx2embed[i[0]])
    logger.info('num of image embedding:{}'.format(len(idx2embed)))
    logger.info('num of captions:{}'.format(len(data)))
    if mode == "train":
        with open(r'model/train_for_dataset.pkl', 'wb') as f:
            pickle.dump([data, idx2embed], f)
    else:
        with open(r'model/test_for_dataset.pkl', 'wb') as f:
            pickle.dump([data, idx2embed], f)
    return data, idx2embed


class makeDataset(Dataset):
    def __init__(self, len_prefix, normalization):
        self.normalization = normalization
        self.prefix_length = len_prefix
        self.tokenizer = GPT2Tokenizer.from_pretrained("gpt2")
        self.embed_list = list()
        data_path = r"DataSet"
        path = r'model/encoder_for_train.pkl'
        if os.path.isfile(path):
            with open(path, 'rb') as f:
                self.embed_list, self.text_list, self.max_seq_len = pickle.load(f)
            logger.info('num of data:{}'.format(len(self.embed_list)))
        else:
            self.text_list = list()
            self.embed_list = list()
            max_seq_len = 0
            if os.path.isfile(r'model/train_for_dataset.pkl'):
                with open(r'model/train_for_dataset.pkl', 'rb') as f:
                    data, idx2embd = pickle.load(f)
            else:
                data, idx2embd = image_encoder(data_path, "train")
            for index, img, text in data:
                text_encoder = torch.tensor(self.tokenizer.encode(text))
                self.text_list.append(text_encoder)
                self.embed_list.append(idx2embd[index].squeeze(0).float())
                max_seq_len = max(max_seq_len, self.text_list[-1].shape[0])

            with open(path, 'wb') as f:
                pickle.dump([self.embed_list, self.text_list, max_seq_len], f)
        all_len = torch.tensor([len(self.text_list[i]) for i in range(len(self))]).float()
        self.max_seq_len = min(int(all_len.mean() + all_len.std() * 10), int(all_len.max()))

    def pad_tokens(self, item: int):
        tokens = self.text_list[item]
        padding = self.max_seq_len - tokens.shape[0]
        if padding > 0:
            tokens = torch.cat((tokens, torch.zeros(padding, dtype=torch.int64) - 1))
            self.text_list[item] = tokens
        elif padding < 0:
            tokens = tokens[:self.max_seq_len]
            self.text_list[item] = tokens
        mask = tokens.ge(0)  # mask is zero where we out of sequence
        tokens[~mask] = 0
        mask = mask.float()
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
    model.eval()
    logger.info("Running evaluation")
    eval_loss = 0.0
    with torch.no_grad():
        for data in tqdm(dev_loader):
            embed_list, text_list, mask_list = data
            embed_list = embed_list.to(device).float()
            text_list = text_list.to(device)
            mask_list = mask_list.to(device)
            logits = model(embed_list, text_list, mask_list)
            shift_logits = logits[..., p.prefix_len - 1:-1, :].contiguous().view(-1, logits.size(-1))
            shift_labels = text_list.view(-1)
            loss = F.cross_entropy(shift_logits, shift_labels)
            loss = loss.mean()
            eval_loss += loss
    return eval_loss


def train(model, train_loader, dev_loader, optimizer, scheduler):
    model.train()
    logger.info("start training")
    for epoch in range(p.epochs):
        logger.info('start {}-th epoch training'.format(epoch + 1))
        for batch_idx, data in enumerate(tqdm(train_loader)):
            model.zero_grad()
            step = epoch * len(train_loader) + batch_idx + 1
            embed_list, text_list, mask_list = data
            embed_list = embed_list.to(device).float()
            text_list = text_list.to(device)
            mask_list = mask_list.to(device)
            logits = model(embed_list, text_list, mask_list)
            # 计算loss
            shift_logits = logits[..., p.prefix_len - 1:-1, :].contiguous().view(-1, logits.size(-1))
            shift_labels = text_list.view(-1)
            loss = F.cross_entropy(shift_logits, shift_labels)
            loss.backward()
            optimizer.step()
            scheduler.step()
            optimizer.zero_grad()

        logger.info('train loss at epoch {} is {}'.format(epoch + 1, loss))
        # # if epoch % 1 == 0 and epoch != 0:
        # dev_loss = evaluate(model, dev_loader)
        # # writer.add_scalar('loss', dev_loss, step)
        # logger.info('test loss at epoch {} is {}'.format(epoch + 1, dev_loss.item()))
        # model.train()
        # if (epoch + 1) % 5 == 0:
        logger.info('saving checkpoint at epoch {}'.format(epoch + 1))
        torch.save(model.state_dict(), r"model/checkModel.pth")


def main():
    torch.cuda.empty_cache()
    torch.cuda.empty_cache()
    model = ClipCaptionModel(p.prefix_len, p.img_size, p.tune).to(device)
    dataset = makeDataset(p.prefix_len, p.isNormalize)
    test_size = int(p.test_split * len(dataset))
    train_dataset, dev_dataset = torch.utils.data.random_split(dataset,
                                                               [len(dataset) - test_size,
                                                                test_size])
    train_dataloader = DataLoader(train_dataset, batch_size=p.batch_size, shuffle=True)
    dev_loader = DataLoader(dev_dataset, batch_size=p.batch_size, shuffle=True)
    t_total = len(train_dataloader) * p.epochs
    optimizer = transformers.AdamW(model.parameters(), lr=p.lr)
    scheduler = transformers.get_linear_schedule_with_warmup(
        optimizer, num_warmup_steps=8000, num_training_steps=t_total
    )

    train(model, train_dataloader, dev_loader, optimizer, scheduler)

torch.cuda.empty_cache()
device = torch.device('cuda:0' if torch.cuda.is_available() else 'cpu')

main()

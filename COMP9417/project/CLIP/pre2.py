import torch
from transformers import BertConfig, BertTokenizer, GPT2Tokenizer
from tqdm import tqdm
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
import config as p

class ImageDataset(Dataset):
    def __init__(self, path, preprocess):
        # 加载路径下的所有图片
        self.images = []
        self.image_names = []
        for file in glob.glob(join(path, '*')):
            image = io.imread(file)
            image = preprocess(Image.fromarray(image)).squeeze(0).to(device)
            filename = os.path.basename(file)

            self.images.append(image)
            self.image_names.append(filename)

    def __getitem__(self, item):
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
            if embed is not None:
                generated = embed
            else:
                if tokens is None:
                    tokens = torch.tensor(tokenizer.encode(prompt))
                    tokens = tokens.unsqueeze(0).to(device)

                generated = model.gpt.transformer.wte(tokens)

            for i in range(entry_length):

                outputs = model.gpt2(inputs_embeds=generated)
                outputs = outputs.logits
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
                next_token = torch.argmax(outputs, -1).unsqueeze(1)
                next_token_embed = model.gpt2.transformer.wte(next_token)
                if tokens is None:
                    tokens = next_token
                else:
                    tokens = torch.cat((tokens, next_token), dim=1)
                generated = torch.cat((generated, next_token_embed), dim=1)
                if stop_token_index == next_token[0:].tolist()[0][0]:
                    break
            output_list = list(tokens.squeeze().cpu().numpy().flatten())
            output_text = tokenizer.decode(output_list)
            generated_list.append(output_text)

    return generated_list[0]


def main():
    # 分词器
    tokenizer = GPT2Tokenizer.from_pretrained("gpt2")
    # 初始化模型
    model = ClipCaptionModel(p.prefix_len, p.img_size, p.tune, p.c_len).to(device)
    # 加载权重
    model.load_state_dict(torch.load(r"model/checkModel.pth", map_location=device))
    model.eval()

    # 加载clip模型
    clip_model, preprocess = clip.load("ViT-B/32", device=device, jit=False)

    # 加载数据集
    dataset = ImageDataset(r"DataSet_test", preprocess)
    dataloader = DataLoader(dataset, batch_size=p.batch_size, shuffle=True)
    logger.info('start predicting')

    captions_generate = []
    image_name_list = []
    for batch_idx, data in enumerate(tqdm(dataloader)):
        images, image_names = data
        with torch.no_grad():
            prefix = clip_model.encode_image(images).to(
                device, dtype=torch.float32
            )
            prefix_embed = prefix.unsqueeze(1).repeat(1, 2, 1).view(-1, prefix.size(-1))
            prefix_embed = model.clip_project(prefix_embed).view(-1, model.prefix_len, model.prefix_size)
        captions = generate2(model, tokenizer, embed=prefix_embed)
        print(image_names, captions)
        # 每num_generate个caption对应一张图片
        # captions = ['\t'.join(captions[i: i + 2]) for i in
        #             range(0, prefix_embed.size(0), 2)]
        # captions_generate += captions
        # image_name_list += image_names

    # # if p.tune:
    # save_path = join("output", 'caption_generate_finetune.txt')
    # # else:
    # #     save_path = join(args.output_path, 'caption_generate_no_finetune.txt')
    # with open(save_path, 'w', encoding='utf8') as f:
    #     for caption, image_name in zip(captions_generate, image_name_list):
    #         f.write('{}\t{}\n'.format(image_name, caption))


torch.cuda.empty_cache()
device = torch.device('cpu')
main()
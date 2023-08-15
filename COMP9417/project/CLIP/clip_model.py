import torch
import torch.nn as nn
from transformers import GPT2LMHeadModel
from typing import Tuple
from loguru import logger



class MLP(nn.Module):

    def forward(self, x: torch.Tensor) -> torch.Tensor:
        return self.model(x)

    def __init__(self, sizes: Tuple[int, ...], bias=True, act=nn.Tanh):
        super(MLP, self).__init__()
        layers = []
        for i in range(len(sizes) - 1):
            layers.append(nn.Linear(sizes[i], sizes[i + 1], bias=bias))
            if i < len(sizes) - 2:
                layers.append(act())
        self.model = nn.Sequential(*layers)


class ClipCaptionModel(nn.Module):

    def __init__(self, prefix_len, clip_size,
                 finetune_gpt2, constant_len=10):
        super(ClipCaptionModel, self).__init__()
        self.gpt2 = GPT2LMHeadModel.from_pretrained('gpt2')
        logger.info('succeed to load pretrain gpt2 model')
        self.prefix_size = self.gpt2.config.n_embd
        self.prefix_len = prefix_len
        self.clip_project = MLP((clip_size, (self.prefix_size * prefix_len) // 2, self.prefix_size * prefix_len))
        self.finetune_gpt2 = finetune_gpt2

    def forward(self, clip_embeds, caption_ids, mask):
        # caption_inputs_embeds:[bs, caption_len, prefix_size]
        caption_embeds = self.gpt2.transformer.wte(caption_ids)
        # prefix_embeds:[bs, prefix_len, prefix_size]
        prefix_embeds = self.clip_project(clip_embeds).view(-1, self.prefix_len, self.prefix_size)
        # embedding_cat:[bs, prefix_len+caption_len, prefix_size]
        embedding_cat = torch.cat((prefix_embeds, caption_embeds), dim=1)
        out = self.gpt2(inputs_embeds=embedding_cat, attention_mask=mask)
        # logits:[bs, prefix_len+caption_len, prefix_size]
        logits = out.logits
        return logits

    def parameters(self, recurse: bool = True):
        if self.finetune_gpt2:
            return super(ClipCaptionModel, self).parameters()
        else:
            return self.clip_project.parameters()

    def train(self, mode: bool = True):
        if not isinstance(mode, bool):
            raise ValueError("training mode is expected to be boolean")
        self.training = mode
        for module in self.children():
            module.train(mode)
        if not self.finetune_gpt2:
            self.gpt2.eval()
        return self

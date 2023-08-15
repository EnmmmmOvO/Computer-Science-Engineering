import warnings
import torch
import transformers
from tqdm import tqdm
from torch import nn
from torchvision import models
from transformers import GPT2LMHeadModel, GPT2Tokenizer
from torch.utils.data import Dataset, DataLoader
from torchvision import transforms
from datasets import load_dataset

warnings.filterwarnings('ignore')

# define parameters
EPOCH = 16
BATCH_SIZE = 20
DATA_PATH = 'poloclub/diffusiondb'
TRAIN_DATA_SET = '2m_first_1k'
VALID_DATA_SET = '2m_first_1k'
EMBEDDING_DIM = 1024
MAX_LENGTH = 200


# Defining a custom Dataset class for images and prompt
class ImageDataset(Dataset):
    def __init__(self, mode=0):
        self.tokenizer = GPT2Tokenizer.from_pretrained('gpt2')
        self.tokenizer.pad_token_id = 0
        self.data_set = TRAIN_DATA_SET if mode == 0 else VALID_DATA_SET
        self.dataset = load_dataset(DATA_PATH, self.data_set)['train']
        # Define image transformations
        self.transform = [
            transforms.Compose([transforms.RandomRotation(30),
                                transforms.RandomResizedCrop(224),
                                transforms.RandomHorizontalFlip(p=0.5),
                                transforms.RandomVerticalFlip(p=0.5),
                                transforms.ColorJitter(brightness=0.2, contrast=0.1, saturation=0.1, hue=0.1),
                                transforms.ToTensor(),
                                transforms.Normalize([0.485, 0.456, 0.406], [0.229, 0.224, 0.225])
                                ]),
            transforms.Compose([transforms.CenterCrop(224),
                                transforms.ToTensor(),
                                transforms.Normalize([0.485, 0.456, 0.406], [0.229, 0.224, 0.225])
                                ])
        ][mode]

    def __len__(self):
        return len(self.dataset)

    def __getitem__(self, idx):
        image = self.transform(self.dataset[idx]['image'])

        prompt = self.dataset[idx]['prompt']
        # Recode the prompt using a GPT2 tokenizer while getting the attention_mask
        prompt = self.tokenizer.encode_plus(prompt, add_special_tokens=True, max_length=MAX_LENGTH,
                                            padding='max_length',
                                            return_attention_mask=True, return_tensors='pt')
        return image, prompt['input_ids'], torch.tensor(prompt['attention_mask'])


# Function to get the training and validation data loaders
def get_dataloader():
    return [DataLoader(ImageDataset(0), batch_size=BATCH_SIZE, shuffle=True),
            DataLoader(ImageDataset(1), batch_size=BATCH_SIZE, shuffle=True)]


# Defining a custom model class combining a ResNet and LSTM for image captioning
class Resnet_LSTM(nn.Module):
    def __init__(self, resnet_model, gpt2_model, embedding_dim):
        super().__init__()
        self.resnet = resnet_model
        self.fc = nn.Linear(1000, embedding_dim)
        self.lstm = nn.LSTM(embedding_dim, gpt2_model.config.hidden_size, batch_first=True)
        self.gpt2 = gpt2_model

    def forward(self, images, attention_mask):
        # Pass images through the ResNet model and apply linear transformation
        resnet_output = self.resnet(images)
        resnet_output = self.fc(resnet_output)
        lstm_output, _ = self.lstm(resnet_output.unsqueeze(1))

        # Expand the LSTM output to match the maximum sequence length
        lstm_output = lstm_output.expand(-1, MAX_LENGTH, -1)

        # Pass the LSTM output through the GPT2 model
        gpt2_output = self.gpt2(inputs_embeds=lstm_output, attention_mask=attention_mask)
        return gpt2_output.logits


def train(model, dataloader, optimizer, device, gpt2_model, scheduler):
    # Set model to training mode
    model.train()
    total_loss = 0
    for images, input_ids, attention_mask in tqdm(dataloader, desc="Training"):
        # Transfer data to GPU if available
        images = images.to(device)
        input_ids = input_ids.to(device)
        attention_mask = attention_mask.to(device)
        optimizer.zero_grad()
        # Forward pass
        output = model(images, attention_mask)
        # Count loss and update optimizer and scheduler
        loss = nn.CrossEntropyLoss(ignore_index=0)(output.view(-1, gpt2_model.config.vocab_size), input_ids.view(-1))
        loss.backward()
        optimizer.step()
        scheduler.step()
        total_loss += loss.item()
    return total_loss / len(dataloader)


def validate(model, dataloader, device, gpt2_model):
    # Set model to evaluation mode
    model.eval()
    total_loss = 0
    with torch.no_grad():
        for images, input_ids, attention_mask in tqdm(dataloader, desc="Validating"):
            # Transfer data to GPU if available
            images = images.to(device)
            input_ids = input_ids.to(device)
            attention_mask = attention_mask.to(device)
            output = model(images, attention_mask)
            loss = nn.CrossEntropyLoss(ignore_index=0)(output.view(-1, gpt2_model.config.vocab_size),
                                                       input_ids.view(-1))
            total_loss += loss.item()
    return total_loss / len(dataloader)


def train_model():
    # Determine the device to use
    device = torch.device('cuda' if torch.cuda.is_available() else 'cpu')

    # Initialize the GPT2 tokenizer and Resnet models
    tokenizer = GPT2Tokenizer.from_pretrained('gpt2')
    gpt2_model = GPT2LMHeadModel.from_pretrained('gpt2')
    resnet_model = models.resnet50(pretrained=True)

    # Get data loaders for training and validation
    train_dataloader, valid_dataloader = get_dataloader()

    # Initialize the custom model and transfer it to the device
    model = Resnet_LSTM(resnet_model, gpt2_model, EMBEDDING_DIM).to(device)

    # Initialize the optimizer and the learning rate scheduler
    optimizer = torch.optim.Adam(model.parameters())
    scheduler = transformers.get_linear_schedule_with_warmup(
        optimizer, num_warmup_steps=8000, num_training_steps=len(train_dataloader) * EPOCH
    )

    for epoch in range(EPOCH):
        train_loss = train(model, train_dataloader, optimizer, device, gpt2_model, scheduler)
        valid_loss = validate(model, valid_dataloader, device, gpt2_model)
        print(f'Epoch {epoch + 1}, Train Loss: {train_loss}, Valid Loss: {valid_loss}')

        # Save the model every 5 epochs
        if (epoch + 1) % 5 == 0:
            print('Saving checkpoint at epoch {}'.format(epoch + 1))
            torch.save(model.state_dict(), "checkModel.pth")


if __name__ == '__main__':
    train_model()

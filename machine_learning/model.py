import torch
import torch.nn.functional as F
import torch.nn as nn
from torch.nn import ModuleList, Linear, BatchNorm1d
from torch_geometric.nn import GCNConv
from torch_geometric.nn import global_add_pool


class NN(nn.Module):
    def __init__(self, vocab, embedding_size, hidden_size, output_size):
        super(NN, self).__init__()
        self.vocab = vocab
        self.vocab_size = len(vocab)
        self.embed = nn.Embedding(self.vocab_size, embedding_size)
        self.fc1 = nn.Linear(embedding_size, hidden_size)
        self.fc2 = nn.Linear(hidden_size, output_size)

    def forward(self, x):
        x = self.embed(x)
        x = torch.mean(x, dim=1)
        x = self.fc1(x)
        x = F.relu(x)
        x = self.fc2(x)
        return x


class NNTermWalk(nn.Module):
    def __init__(self, input_size, hidden_size, output_size):
        super(NNTermWalk, self).__init__()
        self.fc1 = nn.Linear(input_size, hidden_size)
        self.fc2 = nn.Linear(hidden_size, output_size)

    def forward(self, x):
        x = self.fc1(x)
        x = F.relu(x)
        x = self.fc2(x)
        return x


class CNN(nn.Module):
    def __init__(self, vocab, embedding_size, hidden_size, output_size):
        super(CNN, self).__init__()
        self.vocab = vocab
        self.vocab_size = len(vocab)
        self.embed = nn.Embedding(self.vocab_size, embedding_size)
        self.conv = nn.Conv1d(embedding_size, hidden_size, 3, padding=1)
        self.out = nn.Linear(hidden_size, output_size)

    def forward(self, x):
        x = self.embed(x)
        x = x.transpose(1, 2)
        x = self.conv(x)
        x = F.relu(x)
        x = torch.mean(x, dim=2)
        x = self.out(x)
        return x


class CNNTermWalk(nn.Module):
    def __init__(self, input_size, hidden_size, output_size):
        super(CNNTermWalk, self).__init__()
        self.conv = nn.Conv1d(input_size, hidden_size, 3, padding=1)
        self.out = nn.Linear(hidden_size, output_size)

    def forward(self, x):
        x = x.transpose(1, 0)
        x = self.conv(x)
        x = F.relu(x)
        x = x.transpose(1, 0)
        x = self.out(x)
        return x


class RNN(nn.Module):
    def __init__(self, vocab, embedding_size, hidden_size, output_size):
        super(RNN, self).__init__()
        self.vocab = vocab
        self.vocab_size = len(vocab)
        self.embed = nn.Embedding(self.vocab_size, embedding_size)
        self.rnn = nn.RNN(embedding_size, hidden_size, batch_first=True)
        self.out = nn.Linear(hidden_size, output_size)

    def forward(self, x, state=None):
        x = self.embed(x)
        x, h = self.rnn(x, state)
        x = F.relu(x)
        x = self.out(x.mean(dim=1))
        return x


class RNNTermWalk(nn.Module):
    def __init__(self, input_size, hidden_size, output_size):
        super(RNNTermWalk, self).__init__()
        self.rnn = nn.RNN(input_size, hidden_size, batch_first=True)
        self.out = nn.Linear(hidden_size, output_size)

    def forward(self, x, state=None):
        x, h = self.rnn(x, state)
        x = F.relu(x)
        x = self.out(x)
        return x


class LSTM(nn.Module):
    def __init__(self, vocab, embedding_size, hidden_size, output_size):
        super(LSTM, self).__init__()
        self.vocab = vocab
        self.vocab_size = len(vocab)
        self.embed = nn.Embedding(self.vocab_size, embedding_size)
        self.rnn = nn.LSTM(embedding_size, hidden_size, batch_first=True)
        self.out = nn.Linear(hidden_size, output_size)

    def forward(self, x, state=None):
        x = self.embed(x)
        x, (h, c) = self.rnn(x, state)
        x = self.out(x.mean(dim=1))
        return x


class LSTMTermWalk(nn.Module):
    def __init__(self, input_size, hidden_size, output_size):
        super(LSTMTermWalk, self).__init__()
        self.rnn = nn.LSTM(input_size, hidden_size, batch_first=True)
        self.out = nn.Linear(hidden_size, output_size)

    def forward(self, x, state=None):
        x, (h, c) = self.rnn(x, state)
        x = self.out(x)
        return x


class GCN(torch.nn.Module):
    def __init__(self, n_features, n_conv_hidden, n_mlp_hidden):
        super(GCN, self).__init__()
        self.n_features = n_features
        self.n_conv_hidden = n_conv_hidden
        self.n_mlp_hidden = n_mlp_hidden
        self.dim = 64
        self.graphconv1 = GCNConv(self.n_features, self.dim)
        self.bn1 = BatchNorm1d(self.dim)
        self.graphconv_hidden = ModuleList(
            [GCNConv(self.dim, self.dim, cached=False)
             for _ in range(self.n_conv_hidden)]
        )
        self.bn_conv = ModuleList(
            [BatchNorm1d(self.dim) for _ in range(self.n_conv_hidden)]
        )
        self.mlp_hidden = ModuleList(
            [Linear(self.dim, self.dim) for _ in range(self.n_mlp_hidden)]
        )
        self.bn_mlp = ModuleList(
            [BatchNorm1d(self.dim) for _ in range(self.n_mlp_hidden)]
        )
        self.mlp_out = Linear(self.dim, 1)

    def forward(self, data):
        x, edge_index = data.x, data.edge_index
        x = F.relu(self.graphconv1(x, edge_index))
        x = self.bn1(x)
        for graphconv, bn_conv in zip(self.graphconv_hidden, self.bn_conv):
            x = graphconv(x, edge_index)
            x = bn_conv(x)
        x = global_add_pool(x, data.batch)
        for fc_mlp, bn_mlp in zip(self.mlp_hidden, self.bn_mlp):
            x = F.relu(fc_mlp(x))
            x = bn_mlp(x)
            x = F.dropout(x, p=0.1, training=self.training)
        x = self.mlp_out(x)
        return x

import torch
import numpy as np
import random
from tqdm import tqdm
from sklearn.metrics import r2_score
from early_stopping import EarlyStopping


# リソースの選択（CPU/GPU）
device = torch.device("cuda:0" if torch.cuda.is_available() else "cpu")


def fix_seed(seed):
    """fix_seed

    乱数シード固定（再現性の担保）

    Args:
        seed (int): 乱数のシード値
    """
    # random
    random.seed(seed)
    # numpy
    np.random.seed(seed)
    # pytorch
    torch.manual_seed(seed)
    torch.cuda.manual_seed_all(seed)
    torch.backends.cudnn.deterministic = True
    torch.backends.cudnn.benchmark = False


seed = 42
fix_seed(seed)


def train(model, dataloader, criterion, optimizer):
    """train

    与えられたデータで指定されたモデルを訓練する関数

    Args:
        model (torch.nn.Module): 機械学習モデル
        dataloader (torch.utils.data.dataloader.DataLoader): データローダー
        criterion (torch.nn.modules.loss): 損失関数
        optimizer (torch.optim): 最適化関数

    Returns:
        average_loss (float): 平均損失値
        average_r2_score (float): 平均R2スコア
    """
    model.train()
    total_loss = 0
    r2 = 0
    for X, y in dataloader:
        X = X.to(device)
        y = y.to(device)
        optimizer.zero_grad()
        output = model(X)
        loss = criterion(output, y)
        loss.backward()
        optimizer.step()
        total_loss += loss.item()
        r2 += r2_score(y_pred=output.tolist(), y_true=y.tolist())
    average_loss = total_loss / len(dataloader)
    average_r2_score = r2 / len(dataloader)
    return average_loss, average_r2_score


def eval(model, dataloader, criterion):
    """eval

    与えられたデータで指定されたモデルを評価する関数

    Args:
        model (torch.nn.Module): 機械学習モデル
        dataloader (torch.utils.data.dataloader.DataLoader): データローダー
        criterion (torch.nn.modules.loss): 損失関数

    Returns:
        average_loss (float): 平均損失値
        average_r2_score (float): 平均R2スコア
    """
    model.eval()
    total_loss = 0
    r2 = 0
    for X, y in dataloader:
        X = X.to(device)
        y = y.to(device)
        output = model(X)
        loss = criterion(output, y)
        total_loss += loss.item()
        r2 += r2_score(y_pred=output.tolist(), y_true=y.tolist())
    average_loss = total_loss / len(dataloader)
    average_r2_score = r2 / len(dataloader)
    return average_loss, average_r2_score


def predict(model, dataloader):
    """predict

    与えられたデータで指定されたモデルを予測する関数

    Args:
        model (torch.nn.Module): 機械学習モデル
        dataloader (torch.utils.data.dataloader.DataLoader): データローダー

    Returns:
        y_pred (list): 予測値
        y_true (list): 正解値
    """
    model.eval()
    y_pred = []
    y_true = []
    for X, y in dataloader:
        X = X.to(device)
        y = y.to(device)
        output = model(X)
        y_pred.extend(output.tolist())
        y_true.extend(y.tolist())
    return y_pred, y_true


def learn_model(model, train_loader, test_loader, criterion, optimizer, epochs):
    """learn_model

    与えられたデータで指定されたモデルを訓練・評価する関数

    Args:
        model (torch.nn.Module): 機械学習モデル
        train_loader (torch.utils.data.dataloader.DataLoader): 訓練データローダー
        test_loader (torch.utils.data.dataloader.DataLoader): テストデータローダー
        criterion (torch.nn.modules.loss): 損失関数
        optimizer (torch.optim): 最適化関数
        epochs (int): エポック数

    Returns:
        train_loss (list): 訓練データの損失値
        test_loss (list): テストデータの損失値
        train_r2 (list): 訓練データのR2スコア
        test_r2 (list): テストデータのR2スコア
        pred (list): 予測値
        true (list): 正解値
    """
    train_loss = []
    test_loss = []
    train_r2 = []
    test_r2 = []
    early_stopping = EarlyStopping(patience=20, verbose=True)
    for epoch in tqdm(range(1, epochs+1)):
        loss, r2 = train(model, train_loader, criterion, optimizer)
        train_loss.append(loss)
        train_r2.append(r2)
        loss, r2 = eval(model, test_loader, criterion)
        test_loss.append(loss)
        test_r2.append(r2)
        print(
            f"epoch: {epoch},\
                train_loss: {train_loss[-1]},\
                    test_loss: {test_loss[-1]},\
                        train_r2: {train_r2[-1]},\
                            test_r2: {test_r2[-1]}")
        early_stopping(test_loss[-1], model)
        if early_stopping.early_stop:
            print("Early stopping")
            break
    pred, true = predict(model, test_loader)
    return train_loss, test_loss, train_r2, test_r2, pred, true


def train_gcn(model, dataloader, criterion, optimizer):
    """train_gcn

    与えられたデータで指定されたGCNモデルを訓練する関数

    Args:
        model (torch.nn.Module): 機械学習モデル(GCN)
        dataloader (torch_geometric.loader.dataloader.DataLoader): データローダー
        criterion (torch.nn.modules.loss): 損失関数
        optimizer (torch.optim): 最適化関数

    Returns:
        average_loss(float): 平均損失値
        average_r2_score(float): 平均R2スコア
    """
    model.train()
    total_loss = 0
    r2 = 0
    for data in dataloader:
        optimizer.zero_grad()
        output = model(data)
        loss = criterion(output, data.y)
        loss.backward()
        optimizer.step()
        total_loss += loss.item()
        r2 += r2_score(y_pred=output.tolist(), y_true=data.y.tolist())
    average_loss = total_loss / len(dataloader)
    average_r2_score = r2 / len(dataloader)
    return average_loss, average_r2_score


def eval_gcn(model, dataloader, criterion):
    """eval_gcn

    与えられたデータで指定されたGCNモデルを評価する関数

    Args:
        model (torch.nn.Module): 機械学習モデル(GCN)
        dataloader (torch_geometric.loader.dataloader.DataLoader): データローダー
        criterion (torch.nn.modules.loss): 損失関数

    Returns:
        average_loss(float): 平均損失値
        average_r2_score(float): 平均R2スコア
    """
    model.eval()
    total_loss = 0
    r2 = 0
    for data in dataloader:
        output = model(data)
        loss = criterion(output, data.y)
        total_loss += loss.item()
        r2 += r2_score(y_pred=output.tolist(), y_true=data.y.tolist())
    average_loss = total_loss / len(dataloader)
    average_r2_score = r2 / len(dataloader)
    return average_loss, average_r2_score


def predict_gcn(model, dataloader):
    """predict

    与えられたデータで指定されたGCNモデルを予測する関数

    Args:
        model (torch.nn.Module): 機械学習モデル(GCN)
        dataloader (torch_geometric.loader.dataloader.DataLoader): データローダー

    Returns:
        tuple[list]: 予測値と正解値
    """
    model.eval()
    y_pred = []
    y_true = []
    for data in dataloader:
        output = model(data)
        y_pred.extend(output.tolist())
        y_true.extend(data.y.tolist())
    return y_pred, y_true


def learn_gcn(model, train_loader, test_loader, criterion, optimizer, epochs):
    """learn_gcn

    与えられたデータで指定されたGCNモデルを訓練・評価する関数

    Args:
        model (torch.nn.Module): 機械学習モデル(GCN)
        train_loader (torch_geometric.loader.dataloader.DataLoader): 訓練データローダー
        test_loader (torch_geometric.loader.dataloader.DataLoader): テストデータローダー
        criterion (torch.nn.modules.loss): 損失関数
        optimizer (torch.optim): 最適化関数
        epochs (int): エポック数

    Returns:
        train_loss (list): 訓練データの損失値
        test_loss (list): テストデータの損失値
        train_r2 (list): 訓練データのR2スコア
        test_r2 (list): テストデータのR2スコア
        pred (list): 予測値
        true (list): 正解値
    """
    train_loss = []
    test_loss = []
    train_r2 = []
    test_r2 = []
    early_stopping = EarlyStopping(patience=20, verbose=True)
    for epoch in tqdm(range(1, epochs+1)):
        loss, r2 = train_gcn(model, train_loader, criterion, optimizer)
        train_loss.append(loss)
        train_r2.append(r2)
        loss, r2 = eval_gcn(model, test_loader, criterion)
        test_loss.append(loss)
        test_r2.append(r2)
        print(
            f"epoch: {epoch},\
                train_loss: {train_loss[-1]},\
                    test_loss: {test_loss[-1]},\
                        train_r2: {train_r2[-1]},\
                            test_r2: {test_r2[-1]}")
        early_stopping(test_loss[-1], model)
        if early_stopping.early_stop:
            print("Early stopping")
            break
    pred, true = predict_gcn(model, test_loader)
    return train_loss, test_loss, train_r2, test_r2, pred, true

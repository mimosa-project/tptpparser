import numpy as np
import torch


class EarlyStopping:
    """EarlyStopping

    Early Stoppingを行うためのクラス

    Attributes:
        patience (int): Early Stoppingを行うまでのエポック数
        verbose (bool): Early Stoppingの経過を表示するかどうか
        path (str): ベストモデルを保存するパス
        trace_func (function): Early Stoppingの経過を表示する関数
    """

    def __init__(self, patience=10, verbose=False, path='checkpoint.pt', trace_func=print):
        self.patience = patience  # 設定ストップカウンタ
        self.verbose = verbose  # 表示の有無
        self.counter = 0  # 現在のカウンタ値
        self.best_score = None  # ベストスコア
        self.early_stop = False  # ストップフラグ
        self.val_loss_min = np.Inf  # 前回のベストスコア記憶用
        self.path = path  # ベストモデル格納path

    def __call__(self, val_loss, model):
        """__call__

        実際に学習ループ内で最小lossを更新したか否かを計算する関数

        Args:
            val_loss (float): データの損失値
            model (torch.nn.Module): 機械学習モデル
        """
        score = -val_loss
        if self.best_score is None:  # 1Epoch目の処理
            self.best_score = score  # 1Epoch目はそのままベストスコアとして記録する
            self.checkpoint(val_loss, model)  # 記録後にモデルを保存してスコア表示する
        elif score < self.best_score:  # ベストスコアを更新できなかった場合
            self.counter += 1  # ストップカウンタを+1
            if self.verbose:  # 表示を有効にした場合は経過を表示
                # 現在のカウンタを表示する
                print(
                    f'EarlyStopping counter: {self.counter} out of {self.patience}')
            if self.counter >= self.patience:  # 設定カウントを上回ったらストップフラグをTrueに変更
                self.early_stop = True
        else:  # ベストスコアを更新した場合
            self.best_score = score  # ベストスコアを上書き
            self.checkpoint(val_loss, model)  # モデルを保存してスコア表示
            self.counter = 0  # ストップカウンタリセット

    def checkpoint(self, val_loss, model):
        """checkpoint

        ベストスコアを更新した場合にモデルを保存する関数

        Args:
            val_loss (float): データの損失値
            model (torch.nn.Module): 機械学習モデル
        """
        if self.verbose:  # 表示を有効にした場合は、前回のベストスコアからどれだけ更新したか？を表示
            print(
                f'Validation loss decreased ({self.val_loss_min:.6f} --> {val_loss:.6f}).  Saving model ...')
        torch.save(model.state_dict(), self.path)  # ベストモデルを指定したpathに保存
        self.val_loss_min = val_loss  # その時のlossを記録する

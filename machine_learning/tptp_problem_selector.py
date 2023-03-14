import os
import sys
import subprocess
from lark import Tree
from collections import defaultdict
sys.path.append(os.path.join(os.path.pardir))  # nopep8
from parse_tstp import ParseTstp


class TptpProblemSelector():
    """TptpProblemSelector

    Vampireを用いて、機械学習モデルに用いる問題ファイルを選択するクラス

    Attributes:
        vampire_path (str): Vampireの実行ファイルのパス
        grammar_path (str): 使用するtptp文法ファイルのパス
    """

    def __init__(self, vampire_path, grammar_path):
        self.vampire_path = vampire_path
        self.grammar_path = grammar_path
        self.parse_tstp = ParseTstp(self.grammar_path)

    def run_vampire_clausify(self, problem_path):
        """run_vampire_clausify

        vampireを実行し、その結果から節を取得する関数

        Args:
            problem_path (str): Vampireに渡す問題ファイルのパス

        Returns:
            output (str): Vampireの結果から取得した節
        """
        result = subprocess.run(
            ("./", self.vampire_path, "--mode", "clausify", problem_path), encoding="utf-8", stdout=subprocess.PIPE)
        result_list = result.stdout.splitlines()
        output = "\n".join(result_list[1:])
        return output

    def get_included_files(self, node, included_files=None):
        """get_included_files

        具象構文木からincludeされているファイルのリストを取得する関数

        Args:
            node (Tree or Token): 具象構文木
            included_files (list): includeされているファイルのリスト

        Returns:
            included_files (list): includeされているファイルのリスト
        """
        if included_files is None:
            included_files = list()
        if isinstance(node, Tree):
            for child in node.children:
                self.get_included_files(child)
        else:
            if node.type == "FILE_NAME":
                included_files.append(node.value)
        return included_files

    def get_clause_count(self, axiom_set_text):
        """get_clause_count

        公理ファイルセットの節の合計数を取得する関数

        Args:
            axiom_set_text (str): 公理ファイルのリストを","で区切った文字列

        Returns:
            clause_count (int): 公理ファイルセットの節の合計数
        """
        axiom_set = axiom_set_text.split(",")
        clause_count = 0
        for axiom_file in axiom_set:
            axiom_cnf = self.run_vampire_clausify(axiom_file)
            axiom_cst = self.parse_tstp.parse(axiom_cnf)
            axiom_clause = len(axiom_cst.children)
            clause_count += axiom_clause
        return clause_count

    def create_axiom_set2theorems(self, problem_file_paths):
        """create_axiom_set2theorems

        公理ファイルセットをkey、そのセットを使用している定理ファイルのリストをvalueとした辞書を作成する関数

        Args:
            problem_file_paths (list): 問題ファイルのパスのリスト

        Returns:
            axiom_set2theorems (dict): 公理ファイルセットをkey、そのセットを使用している問題ファイルをvalueとした辞書
        """
        axiom_set2theorems = defaultdict(list)
        for problem_file_path in problem_file_paths:
            with open(problem_file_path, "r") as problem_file:
                problem = problem_file.read()
            problem_cst = self.parse_tstp.parse(problem)
            included_files = self.get_included_files(problem_cst)
            if not included_files:
                continue
            included_files.sort()
            included_files_text = ",".join(map(str, included_files))
            axiom_set2theorems[included_files_text].append(problem_file_path)
        return axiom_set2theorems

    def remove_axiom_set_under_10(self, axiom_set2theorems):
        """remove_axiom_set_under_10

        使用している公理ファイルセットが10個未満のものを削除する関数

        Args:
            axiom_set2theorems (dict): 公理ファイルセットをkey、そのセットを使用している問題ファイルをvalueとした辞書

        Returns:
            (dict): 使用している公理ファイルセットが10個以上のものを残したaxiom_set2theorems
        """
        return {k: v for k, v in axiom_set2theorems.items() if len(v) > 10}

    def remove_axiom_set_clause_over_1000(self, axiom_set2theorems):
        """remove_axiom_set_clause_over_1000

        公理ファイルセットの節の合計数が1000を超えるものを削除する関数

        Args:
            axiom_set2theorems (dict): 公理ファイルセットをkey、そのセットを使用している問題ファイルをvalueとした辞書

        Returns:
            (dict): 公理ファイルセットの節の合計数が1000を超えないものを残したaxiom_set2theorems
        """
        return {k: v for k, v in axiom_set2theorems.items() if self.get_clause_count(k) < 1000}

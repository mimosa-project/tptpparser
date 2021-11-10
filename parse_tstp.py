import json
from graphviz import Digraph
from lark import Lark, Tree, Token

NODE_NAME_TO_SYMBOL = {"|": "|", "infix_inequality": "!=", "infix_equality": "=", "assignment": ":=", ">": ">", "*": "*", "+": "+", "subtype_sign": "<<", "gentzen_arrow": "-->", "double_left_right_arrow": "<=>",  "double_arrow": "=>",
                       "double_less_sign": "<=", "left_right_arrow": "<~>", "not_or": "~|", "not_and": "~&", "unary_connective": "~", "fof_quantifier_exclamation": "!", "fof_quantifier_question": "?", "fof_quantifier_tilde_exclamation": "~!", "assoc_connective_and": "&"}

SYMBOL_TO_NODE_NAME = {v: k for k, v in NODE_NAME_TO_SYMBOL.items()}

QUANTIFIER = ("!", "?", "^", "@+", "@-", "!>", "?*")


class ParseTstp():
    """Parse_tstp

    tstpファイルをjson形式に保存するためのクラス

    Attributes:
        lark_path (str): 使用するtptp文法ファイルのパス
    """

    def __init__(self, lark_path):
        self.lark_path = lark_path

    def create_tree_graph(self, tree_root, png_path):
        """create_graph

        larkで作成した木をグラフ化してpngで保存する関数

        Args:
            tree_root (Tree): larkで作成した木
            png_path (str): 保存するpngファイルパス
        """
        input_list = tree_root.pretty().split("\n")
        edges = list()
        tree2list = list()
        serial_number = 0
        for s in input_list:
            serial_number += 1
            space_count = s.count(" ")
            word = s.split()
            if not word:
                continue
            elif len(word) > 1:
                # Tokenの場合
                tree2list.append([space_count, f"{word[0]},{serial_number}"])
                serial_number += 1
                tree2list.append([space_count+2, f"{word[1]},{serial_number}"])
            else:
                # Treeの場合
                tree2list.append([space_count, f"{word[0]},{serial_number}"])
        # edgeの作成
        for i in range(len(tree2list)):
            if i != 0:
                # スペースの数の違いから子か兄弟か等を判定
                if tree2list[i-1][0] < tree2list[i][0]:
                    edges.append((tree2list[i-1][1], tree2list[i][1]))
                else:
                    for j in range(i, -1, -1):
                        if tree2list[j][0]+2 == tree2list[i][0]:
                            edges.append((tree2list[j][1], tree2list[i][1]))
                            break
        # グラフ作成
        G = Digraph(format="png")
        for i, j in edges:
            G.edge(str(i), str(j))
        G.render(png_path)

    def __should_omit_cst(self, node):
        """__should_omit_cst

        抽象構文木を作成する際にnodeを飛ばすべきかどうかを判定する関数

        Args:
            node (Tree): 判定したいnode

        Returns:
            len (node.children) == 1 or node.data == "tptp_root"(bool): 省略するならTrue、そうでないならFalse
        """
        return len(node.children) == 1 or node.data == "tptp_root"

    def convert_cst2ast(self, cst, ast=None):
        """convert_cst2ast

        構文木から子が一つしかないノードを飛ばすことで抽象構文木を作成して作成した抽象構文木を返す関数

        Args:
            cst (Tree): larkで作成した木(tree関数の返り値)
            ast (Tree): 新しく作る抽象構文木、最初はTree("tptp_root", [])

        Returns:
            ast (Tree): 最終的に作られた抽象構文木
        """
        if ast is None:
            ast = Tree("tptp_root", [])
        if type(cst) == Tree:
            if not self.__should_omit_cst(cst):
                if cst.data in NODE_NAME_TO_SYMBOL:
                    cst.data = NODE_NAME_TO_SYMBOL[cst.data]
                ast.children.append(Tree(cst.data, []))
            for child in cst.children:
                if not self.__should_omit_cst(cst):
                    self.convert_cst2ast(child, ast.children[-1])
                else:
                    self.convert_cst2ast(child, ast)
            # =などの演算子を上にあげる処理
            if len(ast.children) == 3:
                if type(ast.children[1]) == Tree:
                    if ast.children[1].data in SYMBOL_TO_NODE_NAME:
                        ast.data = ast.children[1].data
                        ast.children.pop(1)
        else:
            ast.children.append(cst)

        return ast

    def __move_variable_to_child_of_quantifier(self, node):
        """__move_variable_to_child_of_quantifier

        nodeの子の値が変数の定義に使用される記号(!, ?など)の時にそのnodeの兄弟のnodeの値が変数の場合は
        その直前の変数の定義に使用される記号のnodeの子になるように変更する関数

        Args:
            node (Tree): 変数の定義に使用される記号を子に持つnode
        """
        quantifier_index = 0
        while True:
            # variableまたはformulaの場合
            if type(node.children[quantifier_index+1]) == Tree:
                # variableなら追加
                if "variable" in node.children[quantifier_index+1].data:
                    node.children[quantifier_index].children.append(
                        node.children[quantifier_index+1])
                    node.children.pop(quantifier_index+1)
                elif node.children[quantifier_index+1].data in QUANTIFIER:
                    quantifier_index += 1
                else:
                    break
            # 変数名の場合
            else:
                node.children[quantifier_index].children.append(
                    node.children[quantifier_index+1])
                node.children.pop(quantifier_index+1)

    def upgrade_ast(self, ast, upgraded_ast=None):
        """upgrade_ast

        convert_cst2ast関数を実行して子が一つしかないnodeを省略した抽象構文木を
        意味のないnodeを省略したりfunctor等を上に上げる等で抽象構文木を改良してその抽象構文木を返す関数

        Args:
            ast (Tree): convert_cst2ast関数を実行後のnode
            upgraded_ast (Tree): 改良される抽象構文木、最初はTree("tptp_root", [])

        Returns:
            upgraded_ast (Tree): 最終的な改良された抽象構文木
        """
        if upgraded_ast is None:
            upgraded_ast = Tree("tptp_root", [])
        node_name_included_functor = ("fof_defined_plain_term", "fof_plain_term", "fof_system_term",
                                      "general_function", "tff_plain_atomic", "tff_defined_plain", "tff_atomic_type", "thf_fof_function")
        nonassoc_connective = ("<=>", "=>", "<=", "<~>", "~|", "~&")
        is_not_omit_node = False
        is_tilde = False
        if type(ast) == Tree:
            if ast.data in nonassoc_connective:
                upgraded_ast.children.append(
                    Tree(ast.data, [Tree("formula", []), Tree("formula", [])]))
                self.upgrade_ast(
                    ast.children[0], upgraded_ast.children[0].children[0])
                self.upgrade_ast(
                    ast.children[1], upgraded_ast.children[0].children[1])
                return upgraded_ast
            elif ast.data in SYMBOL_TO_NODE_NAME or ast.data == "variable" or not ast.children:
                upgraded_ast.children.append(Tree(ast.data, []))
                is_not_omit_node = True
            elif type(ast.children[0]) == Token and ast.data in node_name_included_functor:
                upgraded_ast.children.append(Tree(ast.children[0], []))
                ast.children.pop(0)
                is_not_omit_node = True
            elif type(ast.children[0]) == Tree:
                if ast.children[0].data in QUANTIFIER:
                    self.__move_variable_to_child_of_quantifier(ast)
                elif ast.children[0].data == "~":
                    upgraded_ast.children.append(
                        Tree("~", [Tree("formula", [])]))
                    ast.children.pop(0)
                    is_tilde = True
            for child in ast.children:
                if is_tilde:
                    self.upgrade_ast(
                        child, upgraded_ast.children[0].children[-1])
                elif is_not_omit_node:
                    self.upgrade_ast(child, upgraded_ast.children[-1])
                else:
                    self.upgrade_ast(child, upgraded_ast)
        else:
            upgraded_ast.children.append(ast)

        return upgraded_ast

    def __convert_formula2list(self, node, formula2list=None):
        """__convert_formula2list

        抽象構文木のformula部分をリストに変換してそれを返す関数

        Args:
            node (Tree): 抽象構文木のnode
            formula2list (list): 抽象構文木をlistで表現したもの

        Returns:
            formula2list (list): 抽象構文木をlistで表現したもの
        """
        if formula2list is None:
            formula2list = list()
        if type(node) == Tree:
            # 子がある場合は子を格納するための空のリストも追加する
            if node.children and node.data != "tptp_root":
                formula2list.append(node.data)
                formula2list.append([])
            # 子がない場合はnodeのみ追加する
            elif node.data != "tptp_root":
                formula2list.append(node.data)
            for child in node.children:
                if node.children and node.data != "tptp_root":
                    self.__convert_formula2list(child, formula2list[-1])
                else:
                    self.__convert_formula2list(child, formula2list)
        else:
            formula2list.append(node)

        return formula2list

    def __convert_annotation2dict(self, node):
        """__convert_annotation2dict

        抽象構文木のannotation部分をdictに変換してそれを返す関数

        Args:
            node (Tree): 抽象構文木のannotation部分のTree

        Returns:
            annotation2dict (dict): annotationを辞書で表現したもの
                annotation2dict["source"] (str): annotationの種類(inference,fileなど)
                annotation2dict["file"] (str): 参照しているファイルのパス(annotation2dict["source"]が"file"のときのみ存在)
                annotation2dict["inference_rule"] (str): どの操作をしているかの情報(annotation2dict["source"]が"inference"のときのみ存在)
                annotation2dict["inference_parents"] (list): どのformulaを参照しているかの情報(annotation2dict["source"]が"inference"のときのみ存在)
                annotation2dict["useful_info"] (list): 上記以外の情報を文字列のリストにして保存している
        """
        annotation2dict = dict()
        annotation2dict["source"] = node.data
        annotation2dict["useful_info"] = list()
        if annotation2dict["source"] == "inference":
            annotation2dict["inference_parents"] = list()
        for i, child in enumerate(node.children):
            if i == 0 and annotation2dict["source"] == "inference":
                annotation2dict["inference_rule"] = child
            elif i == 0 and annotation2dict["source"] == "file":
                annotation2dict["file_name"] = child
            elif type(child) == Tree:
                annotation2dict["useful_info"].append(str(child))
            elif annotation2dict["source"] == "inference":
                annotation2dict["inference_parents"].append(child)
            else:
                annotation2dict["useful_info"].append(str(child))
        return annotation2dict

    def __convert_child_of_ast2formula_info(self, ast_child):
        """__convert_child_of_ast2formula_info

        抽象構文木の子をformula情報に変換してformula情報を返す関数

        Args:
            ast_child (Tree): 抽象構文木の子
                ast_child.data (str): formulaの種類(fof, thf, tffなど)
                ast_child.children[0] (Token): formulaの名前
                ast_child.children[1] (Token): formulaの役割(axiomやplainなど)
                ast_child.children[2] (Tree or Token): formula本体
                ast_child.children[3] (Tree): 参照したformulaの名前などの補足情報

        Returns:
            formula_info (dict): formula情報をdictで表現したもの
                formula_info["formula_type"] (str): formulaの種類(fof, thf, tffなど)
                formula_info["name"] (str): formulaの名前
                formula_info["formula_role"] (str): formulaの役割(axiomやplainなど)
                formula_info["formula"] (list): formula本体
                formula_info["annotations"] (list): 参照したformulaの名前などの補足情報
        """
        formula_info = dict()
        formula_info["formula_type"] = ast_child.data
        formula_info["name"] = ast_child.children[0]
        formula_info["formula_role"] = ast_child.children[1]
        # formulaの抽象構文木の意味のないnodeを飛ばしたりfunctorなどを上にあげる等をすることで改良
        upgraded_formula = self.upgrade_ast(ast_child.children[2])
        # 改良されたformulaの抽象構文木をlistで表現してformula_infoに追加
        formula_info["formula"] = self.__convert_formula2list(upgraded_formula)
        formula_info["annotations"] = list()
        for annotation in ast_child.children[3].children:
            if annotation.data != "null":
                # annotationの抽象構文木を意味のないnodeを飛ばしたりinferenceなどを上にあげる等をすることで改良
                upgraded_annotation = self.upgrade_ast(ast_child.children[3])
                # 改良されたannotationの抽象構文木をdictで表現してformula_infoに追加
                formula_info["annotations"].append(
                    self.__convert_annotation2dict(upgraded_annotation.children[0]))
        return formula_info

    def convert_ast2json(self, ast):
        """convert_ast2json

        抽象構文木をjson形式に変換して変換されたリストを返す関数

        Args:
            ast (Tree): jsonに変換する抽象構文木

        Returns:
            ast2json (list): 抽象構文木をjsonに変換した辞書のリスト([formula_info1, formula_info2,...])
        """
        ast2json = list()
        for child in ast.children:
            if type(child) == Tree:
                formula_info = self.__convert_child_of_ast2formula_info(child)
                ast2json.append(formula_info)
        return ast2json

    def parse_tstp(self, tstp):
        """parse_tstp

        入力されたtstpファイルを読み込んだ文字列をtptpの文法で構文解析することで構文木を作成し、それを返す関数

        Args:
            tstp (str): tstpファイルを読み込んだ文字列

        Returns:
            cst_root (Tree): tptpの文法で構文解析した構文木
        """
        with open(self.lark_path, encoding="utf-8") as grammar:
            parser = Lark(grammar.read(), start="tptp_root")
            cst_root = parser.parse(tstp)

        return cst_root

    def create_proof_graph(self, json_path, png_path):
        """create_proof_graph

        抽象構文木をjson形式で保存されたものから証明のグラフを作成する関数

        Args:
            json_path (str): tstpファイルをparseした結果のjsonファイルのパス
                jsonのフォーマット
                [
                    {
                        "formula_type":(str): formulaの種類(fof, thf, tffなど),
                        "name":(str): formulaの名前,
                        "formula_role":(str): formulaの役割(axiomやplainなど),
                        "formula":(list): formula本体,
                        "annotations":(list): 参考にしたformulaの名前などの補足情報
                            [
                                {
                                    "source":(str): annotationの種類(inference,fileなど)
                                    "file":(str): 参照しているファイルのパス(annotations[]["source"]が"file"のときのみ存在)
                                    "inference_rule":(str): どの操作をしているかの情報(annotations[]["source"]が"inference"のときのみ存在)
                                    "inference_parents":(list): どのformulaを参照しているかの情報(annotations[]["source"]が"inference"のときのみ存在)
                                    "useful_info":(list): 上記以外の情報を文字列のリストにして保存している
                                },
                                ...
                            ]
                    },
                    ...
                ]
            png_path (str): 保存するpngファイルのバス
        """
        with open(json_path) as f:
            json_root = json.load(f)
        G = Digraph(format="png")
        for formula_info in json_root:
            for annotation in formula_info["annotations"]:
                if annotation["source"] == "inference":
                    for inference_parent in annotation["inference_parents"]:
                        G.edge(inference_parent, formula_info["name"])
        G.render(png_path)

    def convert_tstp2json(self, tstp_path, json_path):
        """convert_tstp2json

        解析結果をjsonで保存する

        Args:
            tstp_path (str): 解析するtstpファイルのパス
            json_path (str): 保存するjsonファイルのパス
        """
        with open(tstp_path, "r") as f:
            tstp = f.read()
        cst_root = self.parse_tstp(tstp)
        ast_root = self.convert_cst2ast(cst_root)
        json_root = self.convert_ast2json(ast_root)
        with open(json_path, "w") as f:
            json.dump(json_root, f, indent=4)

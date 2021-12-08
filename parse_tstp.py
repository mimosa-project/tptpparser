import json
from graphviz import Digraph
from lark import Lark, Tree, Token

NODE_NAME_TO_SYMBOL = {"|": "|", "infix_inequality": "!=", "infix_equality": "=", "assignment": ":=", ">": ">", "*": "*", "+": "+", "subtype_sign": "<<", "gentzen_arrow": "-->", "double_left_right_arrow": "<=>",  "double_arrow": "=>",
                       "double_less_sign": "<=", "left_right_arrow": "<~>", "not_or": "~|", "not_and": "~&", "unary_connective": "~", "fof_quantifier_exclamation": "!", "fof_quantifier_question": "?", "fof_quantifier_tilde_exclamation": "~!", "assoc_connective_and": "&"}

SYMBOL_TO_NODE_NAME = {v: k for k, v in NODE_NAME_TO_SYMBOL.items()}

QUANTIFIER = ("!", "?", "^", "@+", "@-", "!>", "?*")

NONASSOC_CONNECTIVE = ("<=>", "=>", "<=", "<~>", "~|", "~&")

NODE_NAME_INCLUDED_FUNCTOR = ("fof_defined_plain_term", "fof_plain_term", "fof_system_term",
                              "general_function", "tff_plain_atomic", "tff_defined_plain", "tff_atomic_type", "thf_fof_function")


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

    def __omit_node_having_single_child(self, cst, tree=None):
        """

        構文木から子が一つしかないノードを飛ばした木を作成してそれを返す関数

        Args:
            cst (Tree): larkで作成した木(tree関数の返り値)
            tree (Tree): 構文木から子が一つしかないノードを飛ばした木、最初はTree("tptp_root", [])
                         再帰呼び出しの場合はtreeを指定してtreeを変更して抽象構文木を作っていく
                         そうでない場合は省略する

        Returns:
            omitted_tree (Tree): 構文木から子が一つしかないノードを飛ばした木
        """
        omitted_tree = tree
        if omitted_tree is None:
            omitted_tree = Tree("tptp_root", [])
        if type(cst) == Tree:
            if not (len(cst.children) == 1 or cst.data == "tptp_root"):
                if cst.data in NODE_NAME_TO_SYMBOL:
                    cst.data = NODE_NAME_TO_SYMBOL[cst.data]
                omitted_tree.children.append(Tree(cst.data, []))
            for child in cst.children:
                if len(cst.children) == 1 or cst.data == "tptp_root":
                    self.__omit_node_having_single_child(child, omitted_tree)
                else:
                    self.__omit_node_having_single_child(
                        child, omitted_tree.children[-1])
        # Tokenの場合
        else:
            omitted_tree.children.append(cst)

        return omitted_tree

    def __move_operator_to_parent(self, omitted_tree):
        """__move_operator_to_parent

        子が一つしかないノードを飛ばした木から二項演算子を上に上げることで抽象構文木を改良する関数

        Args:
            omitted_tree (Tree): 子が一つしかないノードを飛ばした木

        Returns:
            omitted_tree (Tree): 子が一つしかないノードを飛ばした木にある二項演算子を上に上げた木
        """
        if type(omitted_tree) == Tree:
            if len(omitted_tree.children) == 3 and type(omitted_tree.children[1]) == Tree and omitted_tree.children[1].data in SYMBOL_TO_NODE_NAME:
                omitted_tree.data = omitted_tree.children[1].data
                omitted_tree.children.pop(1)
            for child in omitted_tree.children:
                self.__move_operator_to_parent(child)

        return omitted_tree

    def __move_variable_to_child_of_quantifier(self, node):
        """__move_variable_to_child_of_quantifier

        nodeの子の値が変数の定義に使用される記号(!, ?など)の時にそのnodeの兄弟のnodeの値が変数の場合は
        その直前の変数の定義に使用される記号のnodeの子になるように変更する関数

        Args:
            node (Tree): 変数の定義に使用される記号を子に持つnode
        """
        quantifier_index = 0
        while True:
            # variableまたはquantifier、formulaの場合
            if type(node.children[quantifier_index+1]) == Tree:
                # variableなら追加
                if "variable" in node.children[quantifier_index+1].data:
                    node.children[quantifier_index].children.append(
                        node.children[quantifier_index+1])
                    node.children.pop(quantifier_index+1)
                # quantifierならこのquantifier以降の変数をこのquantifierの子に追加する
                elif node.children[quantifier_index+1].data in QUANTIFIER:
                    quantifier_index += 1
                # formulaの場合は終了する
                else:
                    break
            # 変数名の場合
            else:
                node.children[quantifier_index].children.append(
                    node.children[quantifier_index+1])
                node.children.pop(quantifier_index+1)

    def __should_omit_node(self, node):
        """__should_omit_node

        省略するノードかどうかを判定する関数

        Args:
            node (Tree): 判定したいノード
        Returns:
            2 <= len(node.children) <= 3 and should_omit_node_name (bool): 省略するときはTrueそうでないならFalse
        """
        if (type(node) != Tree):
            return False
        should_omit_node_name = not(
            node.data in QUANTIFIER or node.data in NODE_NAME_INCLUDED_FUNCTOR or node.data in NONASSOC_CONNECTIVE or node.data in SYMBOL_TO_NODE_NAME)
        return 2 <= len(node.children) <= 3 and should_omit_node_name

    def __upgrade_ast(self, ast):
        """__upgrade_ast

        子が一つしかないnodeを省略し、二項演算子を上にあげた抽象構文木を
        意味のないnodeを省略したりfunctor等を上に上げる等で抽象構文木を改良してその抽象構文木を返す関数

        Args:
            ast (Tree): 子が一つしかないnodeを省略し、二項演算子を上にあげた抽象構文木のnode

        Returns:
            ast (Tree): 改良された抽象構文木
        """
        if type(ast) == Tree and ast.children:
            # ノードがconnectivesの場合
            if ast.data in NONASSOC_CONNECTIVE:
                ast.children.append(Tree("formula", [ast.children.pop(0)]))
                ast.children.append(Tree("formula", [ast.children.pop(0)]))
                self.__upgrade_ast(ast.children[0])
                self.__upgrade_ast(ast.children[1])
                return ast
            # 子にfunctorがある場合
            elif type(ast.children[0]) == Token and ast.data in NODE_NAME_INCLUDED_FUNCTOR:
                ast.data = ast.children[0]
                ast.children.pop(0)
            elif type(ast.children[0]) == Tree:
                # !や?などの存在記号がある場合
                if ast.children[0].data in QUANTIFIER:
                    self.__move_variable_to_child_of_quantifier(ast)
                elif ast.children[0].data == "~":
                    ast.data = "~"
                    ast.children.pop(0)
                    ast.children.append(Tree("formula", [ast.children.pop(0)]))
            # 意味のないnodeを飛ばす
            if 1 <= len(ast.children) <= 2:
                for i, child in enumerate(ast.children):
                    if self.__should_omit_node(child):
                        for _ in child.children:
                            ast.children.insert(i+1, child.children.pop())
                        ast.children[i] = child.children.pop()
            # 意味のないnodeを飛ばした後にもう一度存在記号がある場合の処理をして取りこぼしをなくす
            if type(ast.children[0]) == Tree and ast.children[0].data in QUANTIFIER:
                self.__move_variable_to_child_of_quantifier(ast)
            for child in ast.children:
                self.__upgrade_ast(child)

        return ast

    def convert_cst2ast(self, cst):
        """convert_cst2ast

        構文木から抽象構文木を作成して作成した抽象構文木を返す関数

        Args:
            cst (Tree): larkで作成した木

        Returns:
            ast (Tree): 最終的に作られた抽象構文木
        """
        omitted_tree = self.__omit_node_having_single_child(cst)
        operator_to_parent_tree = self.__move_operator_to_parent(omitted_tree)
        ast = self.__upgrade_ast(operator_to_parent_tree)

        return ast

    def __convert_ast2json_formula(self, node, json_formula=None):
        """__convert_ast2json_formula

        抽象構文木のformula部分をjsonに変換してそれを返す関数

        Args:
            node (Tree): 抽象構文木のnode
            json_formula (list): 抽象構文木をjsonで表現したもの
                                 再帰呼び出しの場合はjson_formulaを指定してformula部分をjsonに変換する
                                 そうでない場合は省略する

        Returns:
            json_formula (list): 抽象構文木をjsonで表現したもの
            [
                {
                    "type":(str): symbolの種類(variable, quantifierなど)
                    "symbol":(str): symbol本体(X2, !など)
                    "children":(list): 子(もし子がないなら存在しない)
                        [
                            {
                                "type":(str)
                                "symbol":(str)
                                "children":(list):
                            },
                            ...
                        ]
                },
                ...
            ]
        """
        is_top = False
        is_not_symbol = False
        if json_formula is None:
            json_formula = list()
            is_top = True
        dict_formula = dict()
        if type(node) == Tree:
            if node.data == "=" or node.data == "!=":
                dict_formula["type"] = "equality"
            elif node.data in QUANTIFIER:
                dict_formula["type"] = "quantifier"
            elif node.data in NONASSOC_CONNECTIVE:
                dict_formula["type"] = "connectives"
            elif node.data in NODE_NAME_TO_SYMBOL:
                dict_formula["type"] = "operator"
            elif node.data == "~":
                dict_formula["type"] = "negation"
            elif node.data == "formula":
                dict_formula["type"] = "formula"
            else:
                is_not_symbol = True
                dict_formula["type"] = "function"
            dict_formula["symbol"] = node.data
            dict_formula["children"] = list()

            # 根がシンボルでないなら省略する（fof_quantifield_formula等のため）
            if is_top and is_not_symbol:
                for child in node.children:
                    self.__convert_ast2json_formula(
                        child, json_formula)
            else:
                json_formula.append(dict_formula)
                for child in node.children:
                    self.__convert_ast2json_formula(
                        child, json_formula[-1]["children"])
        # Tokenの場合
        else:
            if node.isupper():
                dict_formula["type"] = "variable"
            elif node == "$false" or node == "$true":
                dict_formula["type"] = "boolean-constant"
            else:
                dict_formula["type"] = "constant"
            dict_formula["symbol"] = node
            json_formula.append(dict_formula)

        return json_formula

    def __convert_ast2json_annotation(self, node):
        """__convert_ast2json_annotation

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

    def __convert_ast2json_formula_info(self, ast_child):
        """__convert_ast2json_formula_info

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
        formula_info["formula"] = self.__convert_ast2json_formula(
            ast_child.children[2])
        formula_info["annotations"] = list()
        for annotation in ast_child.children[3].children:
            if annotation.data != "null":
                formula_info["annotations"].append(
                    self.__convert_ast2json_annotation(annotation))
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
                formula_info = self.__convert_ast2json_formula_info(child)
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
                        "formula":(list): formula本体
                            [
                                {
                                    "type":(str): symbolの種類(variable, quantifierなど)
                                    "symbol":(str): symbol本体(X2, !など)
                                    "children":(list): 子(もし子がないなら存在しない)
                                        [
                                            {
                                                "type":(str)
                                                "symbol":(str)
                                                "children":(list):
                                            },
                                            ...
                                        ]
                                },
                                ...
                            ]
                        ,
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

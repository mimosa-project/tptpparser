import json
from graphviz import Digraph
from lark import Lark, Tree, Token

SYMBOL_DICT = {"|": "|", "infix_inequality": "!=", "infix_equality": "=", "assignment": ":=", ">": ">", "*": "*", "+": "+", "subtype_sign": "<<", "gentzen_arrow": "-->", "double_left_right_arrow": "<=>",  "double_arrow": "=>",
               "double_less_sign": "<=", "left_right_arrow": "<~>", "not_or": "~|", "not_and": "~&", "unary_connective": "~", "fof_quantifier_exclamation": "!", "fof_quantifier_question": "?", "fof_quantifier_tilde_exclamation": "~!", "assoc_connective_and": "&"}


class ParseTstp():
    """Parse_tstp
    tstpファイルをjson形式に保存するためのクラス
    input_file: tstpファイル
    output_file: 保存するJSONファイル名
    lark_file: 使用する文法ファイル
    """

    def __init__(self, input_file, output_file, lark_file):
        self.input_file = input_file
        self.output_file = output_file
        self.lark_file = lark_file

    def create_tree_graph(self, node, output):
        """create_graph
        larkで作成した木をグラフ化してpngで保存する関数
        node: larkで作成した木
        output：保存する名前
        """
        input_list = node.pretty().split("\n")
        edges = list()
        tree2list = list()
        count = 0
        for s in input_list:
            count += 1
            space = s.count(" ")
            word = s.split()
            if not word:
                continue
            elif len(word) > 1:
                # Tokenの場合
                tree2list.append([space, f"{word[0]},{count}"])
                count += 1
                tree2list.append([space+2, f"{word[1]},{count}"])
            else:
                # Treeの場合
                tree2list.append([space, f"{word[0]},{count}"])
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
        G.render(output)

    def __update_node_data_to_dict_value_if_mathe_dict_key_and_node_data(self, node, dict):
        """__update_node_data_to_dict_value_if_mathe_dict_key_and_node_data
        辞書のkeyとnodeの値が一致したらnodeの値をnodeの値が一致する辞書のkeyのvalueに書き換える関数
        node: 書き換えるnode
        dict: keyとvalueが文法上の記号とその記号になっている辞書
        """
        if node.data in list(dict.keys()):
            node.data = dict[list(dict.keys())[
                list(dict.keys()).index(node.data)]]

    def __should_omit_node(self, node):
        """__should_omit_node
        抽象構文木を作成する際にnodeを飛ばすべきかどうかを判定する関数
        """
        return len(node.children) == 1 or node.data == "tptp_file"

    def convert_cst2ast(self, node, ast, token_list):
        """convert_cst2ast
        構文木から抽象構文木を作成して作成した抽象構文木を返す関数
        node: larkで作成した木(tree関数の返り値)
        ast: 新しく作る抽象構文木、最初はTree("tptp_file", [])
        token_list: [Tokenかどうか, Tokenのtype, Tokenの中身]、最初は[False, "", ""]
        """
        if type(node) == Tree:
            if not self.__should_omit_node(node):
                self.__update_node_data_to_dict_value_if_mathe_dict_key_and_node_data(
                    node, SYMBOL_DICT)
                ast.children.append(Tree(node.data, []))
            for child in node.children:
                if not self.__should_omit_node(node):
                    self.convert_cst2ast(child, ast.children[-1], token_list)
                else:
                    self.convert_cst2ast(child, ast, token_list)
            # =などの演算子を上にあげる処理
            if len(ast.children) == 3:
                if type(ast.children[1]) == Tree:
                    if ast.children[1].data in list(SYMBOL_DICT.values()):
                        ast.data = ast.children[1].data
                        ast.children.pop(1)
        else:
            ast.children.append(node)

        return ast

    def __move_variable_to_child_of_definition_symbol(self, node):
        """__move_variable_to_child_of_definition_symbol
        nodeの値が変数の定義に使用される記号の時にそのnodeの兄弟のnodeの値が変数名の場合は
        その直前の変数の定義に使用される記号のnodeの子になるように変更する関数
        """
        child_number = 0
        while True:
            # variableまたはformulaの場合
            if type(node.children[child_number+1]) == Tree:
                if "variable" in node.children[child_number+1].data:
                    node.children[child_number].children.append(
                        node.children[child_number+1])
                    node.children.pop(child_number+1)
                    child_number += 1
                    if len(node.children) <= child_number+1 or type(node.children[child_number]) != Tree:
                        break
                else:
                    break
            # 変数名の場合
            else:
                if not node.children[child_number].children:
                    node.children[child_number].children.append(
                        node.children[child_number+1])
                    node.children.pop(child_number+1)
                    child_number += 1
                    if len(node.children) <= child_number+1:
                        break
                else:
                    break

    def update_ast(self, node, ast):
        """update_ast
        convert_cst2ast関数を実行して子が一つしかないnodeを省略した後に数学記号等を上に上げる等で抽象構文木を改良してその抽象構文木を返す関数
        node: convert_cst2ast関数を実行後のnode
        ast: 改良された抽象構文木
        """
        tree_top_list = ["fof_plain_term", "general_function"]
        nonassoc_connective = ["<=>", "=>", "<=", "<~>", "~|", "~&"]
        is_not_omit_node = False
        is_tilde = False
        if type(node) == Tree:
            if len(node.children) >= 2:
                if node.data in nonassoc_connective:
                    ast.children.append(
                        Tree(node.data, [Tree("formula", []), Tree("formula", [])]))
                    self.update_ast(
                        node.children[0], ast.children[0].children[0])
                    self.update_ast(
                        node.children[1], ast.children[0].children[1])
                    return ast
                elif node.data in list(SYMBOL_DICT.values()) or node.data == "variable":
                    ast.children.append(Tree(node.data, []))
                    is_not_omit_node = True
                elif type(node.children[0]) == Token and node.data in tree_top_list:
                    ast.children.append(Tree(node.children[0], []))
                    node.children.pop(0)
                    is_not_omit_node = True
                elif type(node.children[0]) == Tree:
                    if node.children[0].data == "!" or node.children[0].data == "?":
                        self.__move_variable_to_child_of_definition_symbol(
                            node)
                    elif node.children[0].data == "~":
                        ast.children.append(Tree("~", [Tree("formula", [])]))
                        node.children.pop(0)
                        is_tilde = True
            else:
                ast.children.append(Tree(node.data, []))
                is_not_omit_node = True
            for child in node.children:
                if is_tilde:
                    self.update_ast(
                        child, ast.children[0].children[-1])
                elif is_not_omit_node:
                    self.update_ast(
                        child, ast.children[-1])
                else:
                    self.update_ast(child, ast)
        else:
            ast.children.append(Token(node.type, node[:]))

        return ast

    def __convert_formula2list(self, node, tree2list):
        """__convert_formula2list
        parseした結果を保存するために作成した抽象構文木のformula部分をリストで表現してそれを返す関数
        node: 抽象構文木
        tree2list: 抽象構文木をlistで表現したもの
        """
        if type(node) == Tree:
            if node.children and node.data != "tptp_file":
                tree2list.append(node.data)
                tree2list.append([])
            elif node.data != "tptp_file":
                tree2list.append(node.data)
            for child in node.children:
                if node.children and node.data != "tptp_file":
                    self.__convert_formula2list(child, tree2list[-1])
                else:
                    self.__convert_formula2list(child, tree2list)
        else:
            tree2list.append(node[:])

        return tree2list

    def __convert_annotation2dict(self, node, annotation2dict):
        """__convert_annotation2dict
        parseした結果のannotation部分を作成する関数
        node: 抽象構文木のannotation部分
        annotation2dict: annotationを辞書で表現したもの
        """
        annotation2dict["source"] = node.data
        annotation2dict["useful_info"] = list()
        if annotation2dict["source"] == "inference":
            annotation2dict["inference_parents"] = list()
        for i, child in enumerate(node.children):
            if i == 0 and annotation2dict["source"] == "inference":
                annotation2dict["inference_rule"] = child[:]
            elif i == 0 and annotation2dict["source"] == "file":
                annotation2dict["file_name"] = child[:]
            elif type(child) == Tree:
                annotation2dict["useful_info"].append(str(child))
            elif annotation2dict["source"] == "inference":
                annotation2dict["inference_parents"].append(child[:])
            else:
                annotation2dict["useful_info"].append(str(child))
        return annotation2dict

    def __convert_ast2dict(self, node, result_dict):
        """__convert_ast2dict
        parseした結果をjsonで保存するための辞書を返す関数
        node: 抽象構文木
        result_dict: 抽象構文木を辞書で表現したもの
        """
        for i, child in enumerate(node.children):
            if i == 0:
                result_dict["name"] = child[:]
            elif i == 1:
                result_dict["formula_role"] = child[:]
            elif i == 2:
                if type(child) == Tree:
                    formula_child = self.update_ast(
                        child, Tree("tptp_file", []))
                    result_dict["formula"] = self.__convert_formula2list(
                        formula_child, list())
                else:
                    result_dict["formula"] = child[:]
            elif i == 3:
                result_dict["annotations"] = list()
                for annotation_child in child.children:
                    if annotation_child.data != "null":
                        annotation_child = self.update_ast(
                            child, Tree("tptp_file", []))
                        result_dict["annotations"].append(
                            self.__convert_annotation2dict(annotation_child.children[0], dict()))

        return result_dict

    def convert_ast2json(self, ast):
        """convert_ast2json
        parseした結果をjsonで保存するためのリストを返す関数
        ast: 作成した抽象構文木
        result_dict: parseした結果を保存する辞書
        result_list: parseした結果を保存している辞書のリスト（[result_dict1, result_dict2,...]）
        """
        result_list = list()
        for child in ast.children:
            result_dict = dict()
            if type(child) == Tree:
                result_dict["tptp_input"] = child.data
                result_list.append(self.__convert_ast2dict(child, result_dict))

        return result_list

    def parse_tstp_file(self, text):
        """parse_tstp_file
        入力されたtstpファイルを読み込んだ文字列をtptpの文法で構文解析することで構文木を作成し、それを返す関数
        """
        with open(self.lark_file, encoding="utf-8") as grammar:
            parser = Lark(grammar.read(), start="tptp_file")
            tree = parser.parse(text)

        return tree

    def create_proof_graph(self, input_json, output_png):
        """create_proof_graph
        抽象構文木をjson形式で保存されたものから証明のグラフを作成する関数
        """
        with open(f"{input_json}") as f:
            result_list = json.load(f)
        G = Digraph(format="png")
        for result_dict in result_list:
            for annotation in result_dict["annotations"]:
                if annotation["source"] == "inference":
                    for inference_parent in annotation["inference_parents"]:
                        G.edge(inference_parent, result_dict["name"])
        G.render(f"{output_png}")

    def convert_tstp2json(self):
        """convert_tstp2json
        解析結果をjsonで保存する
        input_file：tstp_file
        output_file：保存したいファイル名
        """
        with open(f"{self.input_file}", "r") as f:
            tstp = f.read()
        cst_top = self.parse_tstp_file(tstp)
        ast_top = Tree("tptp_file", [])
        token_list = [False, "", ""]
        t = self.convert_cst2ast(cst_top, ast_top, token_list)
        r = self.convert_ast2json(t)
        with open(f"{self.output_file}.json", "w") as f:
            json.dump(r, f, indent=4)

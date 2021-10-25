import subprocess
import json
from graphviz import Digraph
from lark import Lark, Tree, Token

SYMBOL_DICT = {"|": "|", "infix_inequality": "!=", "infix_equality": "=",
               "assignment": ":=", ">": ">", "*": "*", "+": "+",
               "subtype_sign": "<<", "gentzen_arrow": "-->",
               "double_left_right_arrow": "<=>",  "double_arrow": "=>",
               "double_less_sign": "<=", "left_right_arrow": "<~>",
               "not_or": "~|", "not_and": "~&", "unary_connective": "~",
               "fof_quantifier_exclamation": "!",
               "fof_quantifier_question": "?",
               "fof_quantifier_tilde_exclamation": "~!",
               "assoc_connective_and": "&"}


class ParseTstp():
    """Parse_tstp
    vampireの実行結果をjson形式に保存するためのクラス
    vampire: vampireの実行ファイル
    input_file: vampireで証明するプロブレムファイル
    output_file: 保存するJSONファイル名
    """
    def __init__(self, vampire, input_file, output_file):
        self.vampire = vampire
        self.input_file = input_file
        self.output_file = output_file

    def create_graph(self, node, output):
        """create_graph
        larkで作成した木をグラフ化してpngで保存する関数
        node: larkで作成した木
        output：保存する名前
        """
        input_list = node.pretty.split("\n")
        edges = list()
        tree_list = list()
        count = 0
        for s in input_list:
            count += 1
            space = s.count(" ")
            word = s.split()
            if not word:
                continue
            elif len(word) > 1:
                # Tokenの場合
                tree_list.append([space, f"{word[0]},{count}"])
                count += 1
                tree_list.append([space+2, f"{word[1]},{count}"])
            else:
                # Treeの場合
                tree_list.append([space, f"{word[0]},{count}"])
        # edgeの作成
        for i in range(len(tree_list)):
            if i != 0:
                # スペースの数の違いから子か兄弟か等を判定
                if tree_list[i-1][0] < tree_list[i][0]:
                    edges.append((tree_list[i-1][1], tree_list[i][1]))
                else:
                    for j in range(i, -1, -1):
                        if tree_list[j][0]+2 == tree_list[i][0]:
                            edges.append((tree_list[j][1], tree_list[i][1]))
                            break
        # グラフ作成
        G = Digraph(format="png")
        for i, j in edges:
            G.edge(str(i), str(j))
        G.render(output)

    def __exist_token_in_children(self, node):
        """__exist_token_in_children
        nodeの子にtokenが存在するかどうかの真偽値を返す関数
        """
        for child in node.children:
            if type(child) == Token:
                return True
        return False

    def __clear_token_list(self, token_list):
        """__clear_token_list
        token_listを初期化する関数
        """
        token_list[0] = False
        token_list[1] = ""
        token_list[2] = ""

    def __update_node1_data_to_dict_value_if_mathe_dict_key_and_node2_data(self, node1, node2, dict):
        """__update_node1_data_to_dict_value_if_mathe_dict_key_and_node2_data
        辞書のkeyとnode2の値が一致したらnode1の値をnode2の値が一致する辞書のkeyのvalueに書き換える関数
        node1: 書き換えるnode
        node2: nodeの値がdictのkeyと一致するものがあるnode
        dict: keyとvalueが文法上の記号とその記号になっている辞書
        """
        if node2.data in list(dict.keys()):
            node1.data = dict[list(dict.keys())[list(dict.keys()).index(node2.data)]]

    def __should_not_omit_node(self, node, exist_token):
        """__should_not_omit_node
        抽象構文木を作成する際にnodeを飛ばすべきかどうかを判定する関数
        """
        return len(node.children) > 1 and not node.data == "tptp_file" and not exist_token or not node.children

    def traverse(self, node, ast, token_list):
        """traverse
        構文木から抽象構文木を作成して作成した抽象構文木を返す関数
        node: larkで作成した木(tree関数の返り値)
        ast: 新しく作る抽象構文木、最初はTree("tptp_file", [])
        token_list: [Tokenかどうか, Tokenのtype, Tokenの中身]、最初は[False, "", ""]
        """
        if type(node) == Tree:
            exist_token = self.__exist_token_in_children(node)
            if self.__should_not_omit_node(node, exist_token):
                self.__update_node1_data_to_dict_value_if_mathe_dict_key_and_node2_data(node, node, SYMBOL_DICT)
                ast.children.append(Tree(node.data, []))
            for child in node.children:
                if self.__should_not_omit_node(node, exist_token):
                    self.traverse(child, ast.children[-1], token_list)
                else:
                    self.traverse(child, ast, token_list)
            # tokenを追加
            if token_list[0]:
                ast.children.append(Token(token_list[1], token_list[2]))
                self.__clear_token_list(token_list)
            # =などの演算子を上にあげる処理
            if len(ast.children) == 3:
                if type(ast.children[1]) == Tree:
                    if ast.children[1].data in list(SYMBOL_DICT.values()):
                        ast.data = ast.children[1].data
                        ast.children.pop(1)
        else:
            token_list[0] = True
            token_list[1] = node.type
            token_list[2] += node[0]

        return ast

    def __on_definition_symbol(self, node):
        """__on_definition_symbol
        nodeの値が変数の定義に使用される記号の時にそのnodeの兄弟のnodeの値が変数名の場合は
        その直前の変数の定義に使用される記号のnodeの子になるように変更する関数
        """
        count = 0
        while True:
            # variableまたはformulaの場合
            if type(node.children[count+1]) == Tree:
                if not node.children[count].children and "variable" in node.children[count+1].data:
                    node.children[count].children.append(node.children[count+1])
                    node.children.pop(count+1)
                    count += 1
                    if len(node.children) <= count+1 or type(node.children[count]) != Tree:
                        break
                else:
                    break
            # 変数名の場合
            else:
                if not node.children[count].children:
                    node.children[count].children.append(node.children[count+1])
                    node.children.pop(count+1)
                    count += 1
                    if len(node.children) <= count+1:
                        break
                else:
                    break

    def traverse_formula_or_annotation(self, node, ast):
        """traverse_formula_or_annotation
        traverse関数を実行して子が一つしかないnodeを省略した後に数学記号等を上に上げる等で抽象構文木を改良してその抽象構文木を返す関数
        node: traverse関数を実行後のnode
        ast: 改良された抽象構文木
        """
        tree_top_list = ["fof_plain_term", "general_function"]
        nonassoc_connective = ["<=>", "=>", "<=", "<~>", "~|", "~&"]
        is_not_omit_node = False
        is_tilde = False
        if type(node) == Tree:
            if len(node.children) >= 2:
                if node.data in nonassoc_connective:
                    ast.children.append(Tree(node.data, [Tree("formula", []), Tree("formula", [])]))
                    self.traverse_formula_or_annotation(node.children[0], ast.children[0].children[0])
                    self.traverse_formula_or_annotation(node.children[1], ast.children[0].children[1])
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
                        self.__on_definition_symbol(node)
                    elif node.children[0].data == "~":
                        ast.children.append(Tree("~", [Tree("formula", [])]))
                        node.children.pop(0)
                        is_tilde = True
            else:
                ast.children.append(Tree(node.data, []))
                is_not_omit_node = True
            for child in node.children:
                if is_tilde:
                    self.traverse_formula_or_annotation(child, ast.children[0].children[-1])
                elif is_not_omit_node:
                    self.traverse_formula_or_annotation(child, ast.children[-1])
                else:
                    self.traverse_formula_or_annotation(child, ast)
        else:
            ast.children.append(Token(node.type, node[:]))

        return ast

    def __formula2list(self, node, tree_list):
        """__formula2list
        parseした結果を保存するために作成した抽象構文木のformula部分をリストで表現してそれを返す関数
        node: 抽象構文木
        tree_list: 抽象構文木をlistで表現したもの
        """
        if type(node) == Tree:
            if node.children and node.data != "tptp_file":
                tree_list.append(node.data)
                tree_list.append([])
            elif node.data != "tptp_file":
                tree_list.append(node.data)
            for child in node.children:
                if node.children and node.data != "tptp_file":
                    self.__formula2list(child, tree_list[-1])
                else:
                    self.__formula2list(child, tree_list)
        else:
            tree_list.append(node[:])

        return tree_list

    def __annotation2dict(self, node, annotation_dict):
        """__annotation2dict
        parseした結果のannotation部分を作成する関数
        node: 抽象構文木のannotation部分
        annotation_dict: annotationを辞書で表現したもの
        """
        annotation_dict["source"] = node.data
        annotation_dict["useful_info"] = list()
        if annotation_dict["source"] == "inference":
            annotation_dict["inference_parents"] = list()
        for i, child in enumerate(node.children):
            if i == 0 and annotation_dict["source"] == "inference":
                annotation_dict["inference_rule"] = child[:]
            elif i == 0 and annotation_dict["source"] == "file":
                annotation_dict["file_name"] = child[:]
            elif type(child) == Tree:
                annotation_dict["useful_info"].append(str(child))
            elif annotation_dict["source"] == "inference":
                annotation_dict["inference_parents"].append(child[:])
            else:
                annotation_dict["useful_info"].append(str(child))
        return annotation_dict

    def __ast2dict(self, node, result_dict):
        """__ast2dict
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
                    formula_child = self.traverse_formula_or_annotation(child, Tree("tptp_file", []))
                    result_dict["formula"] = self.__formula2list(formula_child, list())
                else:
                    result_dict["formula"] = child[:]
            elif i == 3:
                result_dict["annotations"] = list()
                for annotation_child in child.children:
                    if annotation_child.data != "null":
                        annotation_child = self.traverse_formula_or_annotation(child, Tree("tptp_file", []))
                        result_dict["annotations"].append(self.__annotation2dict(annotation_child.children[0], dict()))

        return result_dict

    def tstp_parse2json(self, ast):
        """tstp_parse2json
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
                result_list.append(self.__ast2dict(child, result_dict))

        return result_list

    def text2tree(self, text):
        """text2tree
        入力されたテキストをtptpの文法で構文解析することで構文木を作成し、それを返す関数
        """
        with open("./tstp_EBNF.lark", encoding="utf-8") as grammar:
            parser = Lark(grammar.read(), start="tptp_file")
            tree = parser.parse(text)

        return tree

    def create_proof_graph(self, input_json, output_file):
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
        G.render(f"{output_file}")

    def vampire_result(self):
        """vampire_result
        vampireの実行結果を返す関数
        """
        run_result = subprocess.run(("./" + self.vampire, "-p", "tptp", self.input_file), encoding="utf-8", stdout=subprocess.PIPE)
        input_list = run_result.stdout.splitlines()
        output = ""
        for s in input_list[1:]:
            if not s:
                continue
            if s[0] != "%":
                output += s.replace(" ", "")
        return output

    def storage_tstp_analysis2json(self):
        """storage_tptp_analysis2json
        解析結果をjsonで保存する
        input：problems_file
        output：保存したいファイル名
        """
        output = self.vampire_result()
        node = self.text2tree(output)
        ast = Tree("tptp_file", [])
        token_list = [False, "", ""]
        t = self.traverse(node, ast, token_list)
        r = self.tstp_parse2json(t)
        with open(f"{self.output_file}.json", "w") as f:
            json.dump(r, f, indent=4)

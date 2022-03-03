import json
from graphviz import Digraph
from lark import Lark, Tree

# 抽象構文木からjsonに変換する際に記号の型を保存するときに使用する
# key: 記号
# value: 記号の型
SYMBOL2TYPE = {":=": "assignment", ">": "arrow", "<": "less_sign", "*": "star", "+": "plus",
               "<<": "subtype_sign", "-->": "gentzen_arrow", "!": "quantifier", "?": "quantifier",
               "~!": "quantifier", "^": "quantifier", "@+": "quantifier", "@-": "quantifier",
               "!>": "quantifier", "?*": "quantifier", "|": "connective", "&": "connective",
               "<=>": "connective", "=>": "connective", "<=": "connective", "<~>": "connective",
               "~|": "connective", "~&": "connective", "=": "equality", "!=": "equality",
               "!!": "defined_term", "??": "defined_term", "@@+": "defined_term", "@@-": "defined_term",
               "@=": "defined_term"}

# ()や[]があるときや子が二つ以上ある場合、tff_quantified_formulaのように再帰されているノードを例外的に残す場合等のノード名
# key: 子に括弧を含んでいる、子が二つ以上ある場合、再帰されているノードを例外的に残すノード名
# value: keyのノード名の子で括弧が使用されているノード名、例外的に残す再帰されているノード名（どの場合でも括弧が使用されている、子が二つ以上ある場合等はNone）

# 例
# thf_unitary_formula  : thf_quantified_formula | thf_atomic_formula | VARIABLE | "(" thf_logic_formula ")"
# key: thf_unitary_formula
# value: thf_logic_formula

# tff_quantified_formula : FOF_QUANTIFIER "[" tff_variable_list "]" ":" tff_unit_formula
# key: tff_quantified_formula
# value: tff_variable_list

# thf_quantified_formula : thf_quantification thf_unit_formula
# kye: thf_quantified_formula
# value: None
PARENT_NODE_TO_LEAVE_NODE = {"thf_unitary_formula": "thf_logic_formula", "thf_defined_atomic": "THF_CONN_TERM",
                             "tff_unitary_formula": "tff_logic_formula", "tfx_let_types": "tff_atom_typing_list",
                             "tfx_let_defns": "tfx_let_defn_list", "tff_unitary_term": "tff_logic_formula",
                             "tfx_tuple": "tff_arguments", "tff_monotype": "tff_mapping_type",
                             "tff_unitary_type": "tff_xprod_type", "tfx_tuple_type": "tff_type_list",
                             "fof_unitary_formula": "fof_logic_formula", "tff_quantified_formula": "tff_variable_list",
                             "fof_quantified_formula": "fof_variable_list", "tf1_quantified_type": "tff_variable_list",
                             "tcf_quantified_formula": "tff_variable_list", "annotations": None, "thf_quantified_formula": None,
                             "optional_info": None, "thf_tuple": None, "tfx_tuple": None, "tfx_tuple_type": None,
                             "fof_formula_tuple": None, "formula_selection": None, "general_list": None}

# ノード名orトークン名 トークン名 ノード名orトークン名となっているノード名
# 例
# thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula
NODE_TO_REPLACE_MIDDLE_CHILD_NODE = ("thf_binary_nonassoc", "thf_or_formula", "thf_and_formula", "thf_infix_unary", "thf_defined_infix", "thf_let_defn", "thf_mapping_type", "thf_xprod_type",
                                     "thf_union_type", "thf_subtype", "thf_sequent", "tff_binary_nonassoc", "tff_or_formula", "tff_and_formula", "tff_infix_unary", "tff_defined_infix",
                                     "tfx_let_defn", "tff_mapping_type", "tff_xprod_type", "tff_subtype", "tfx_sequent", "fof_binary_nonassoc", "fof_or_formula", "fof_and_formula",
                                     "fof_infix_unary", "fof_defined_infix_formula", "fof_sequent", "disjunction")

# ノード名orトークン名 文字列 ノード名orトークン名 もしくは 文字列(ノード名)となっているノード名
# key: 子に記号を含んでいるノード名
# value: 記号
# 例
# thf_apply_formula    : thf_unit_formula "@" thf_unit_formula | thf_apply_formula "@" thf_unit_formula
# key: thf_apply_formula
# value: @
NODE_TO_REPLACE_SYMBOL = {"thf_apply_formula": "@", "thf_typed_variable": "：", "thf_atom_typing": "：",
                          "tff_typed_variable": "：", "tff_atom_typing": "：", "general_term": "：",
                          "tpi_annotated": "tpi", "thf_annotated": "thf", "tff_annotated": "tff", "tcf_annotated": "tcf", "fof_annotated": "fof",
                          "cnf_annotated": "cnf", "thf_conditional": "$ite", "thf_let": "$let", "tfx_conditional": "$ite", "tfx_let": "$let", "include": "include",
                          "tf1_quantified_type": "!>", "tcf_quantified_formula": "!"}

# トークン名(ノード名) もしくは トークン名 ノード名となっているノード名
# 例
# thf_quantification   : THF_QUANTIFIER "[" thf_variable_list "]" ":"
NODE_TO_REPLACE_LEFT_CHILD_NODE = ("thf_quantification", "thf_prefix_unary", "thf_fof_function", "tff_prefix_unary", "tff_plain_atomic", "tff_defined_plain", "tff_system_atomic",
                                   "tff_atomic_type", "fof_unary_formula", "fof_plain_term", "fof_defined_plain_term", "fof_system_term", "general_function", "literal",
                                   "tff_quantified_formula", "fof_quantified_formula")

# formula_dataの子のノード名
# formula_dataを書き換える文字列は場合によって文字列(ノード名)の文字列が違うため子のノード名をkey、書き換える文字をvalueとしている
# formula_data         : "$thf(" thf_formula ")" | "$tff(" tff_formula ")" | "$fof(" fof_formula ")" | "$cnf(" cnf_formula ")" | "$fot(" fof_term ")"
FORMULA_DATA_TO_REPLACE_SYMBOL = {"thf_formula": "$thf", "tff_formula": "$tff",
                                  "fof_formula": "$fof", "cnf_formula": "$cnf", "fof_term": "$fot"}


class ParseTstp():
    """Parse_tstp

    tstpファイルをjson形式に保存するためのクラス

    Attributes:
        lark_path (str): 使用するtptp文法ファイルのパス
    """

    def __init__(self, lark_path):
        self.lark_path = lark_path

    def create_edges_tree_graph(self, node, edges, digraph_instance, tag_num):
        """create_edges_tree_graph

        larkで作成した木のグラフを作る際のエッジを作成する関数

        Args:
            node (Tree or Token): 木のノード
            edges (list): グラフのエッジ
            digraph_instance (graphviz.graphs.Digraph): digraphのインスタンス
            tag_num (list): グラフのノードを作る際のタグに使用するための番号
                            再帰した際でも値が変更されるような参照渡しができるlist型にしている
                            そのため、要素は一つしかない
        """
        if type(node) == Tree:
            parent_tag = tag_num[0]
            for child in node.children:
                if type(child) == Tree:
                    digraph_instance.node(str(tag_num[0]+1), child.data)
                # トークンの場合
                else:
                    digraph_instance.node(
                        str(tag_num[0]+1), child.value + "," + child.type)
                edges.append([str(parent_tag), str(tag_num[0]+1)])
                tag_num[0] += 1
                self.create_edges_tree_graph(
                    child, edges, digraph_instance, tag_num)

    def create_tree_graph(self, tree_root, png_path):
        """create_graph

        larkで作成した木をグラフ化してpngで保存する関数

        Args:
            tree_root (Tree): larkで作成した木
            png_path (str): 保存するpngファイルパス
        """
        edges = list()
        G = Digraph(format="png")
        tag_num = [1]
        G.node(str(tag_num[0]), tree_root.data)
        self.create_edges_tree_graph(tree_root, edges, G, tag_num)
        for i, j in edges:
            G.edge(str(i), str(j))
        G.render(png_path)

    def __is_leave_node(self, cst, cst_parent_data):
        """__is_leave_node

        残すノードかどうかを判定する関数
        ()や[]があるときや子が二つ以上ある場合、再帰されているノードを例外的に残す場合等のノードを残す

        Args:
            cst(Tree): 具象構文木のノード
            cst_parent_data(Tree): cstの親のノード名

        Returns:
            (bool): 残すならTrue、省略するならFalse
        """
        if cst_parent_data in PARENT_NODE_TO_LEAVE_NODE and \
                PARENT_NODE_TO_LEAVE_NODE[cst_parent_data] == cst.data or \
                cst.data in PARENT_NODE_TO_LEAVE_NODE and PARENT_NODE_TO_LEAVE_NODE[cst.data] == None:
            return True
        else:
            return False

    def convert_cst2ast(self, cst, ast=Tree("tptp_root", []), cst_parent_data=None):
        """convert_cst2ast

        具象構文木から抽象構文木を作成する関数

        Args:
            cst(Tree or Token): 具象構文木のノード
            ast(Tree): 抽象構文木のノード
            cst_parent_data(str): cstの親のノード名

        Returns:
            ast(Tree): 最終的に作成される抽象構文木
        """
        # トークンの場合
        if type(cst) != Tree:
            ast.children.append(cst)
            return ast

        # astに子が追加されたかどうか
        is_add_ast_children = False

        # 飛ばさない場合は抽象構文木に加える
        if self.__is_leave_node(cst, cst_parent_data):
            ast.children.append(Tree(cst.data, []))
            is_add_ast_children = True
        # ノード名 トークン ノード名となっている場合はトークンに書き換える
        if cst.data in NODE_TO_REPLACE_MIDDLE_CHILD_NODE and len(cst.children) == 3:
            middle_child = cst.children.pop(1)
            ast.children.append(
                Tree(middle_child.value + "," + middle_child.type, []))
            is_add_ast_children = True
        # ノード名 記号 ノード名 or 記号(ノード名)となっている場合は記号に書き換える
        if cst.data in NODE_TO_REPLACE_SYMBOL and len(cst.children) >= 2:
            ast.children.append(
                Tree(NODE_TO_REPLACE_SYMBOL[cst.data] + "," + cst.data, []))
            is_add_ast_children = True
        # トークン名(ノード名...)となっている場合はトークンに書き換える
        if cst.data in NODE_TO_REPLACE_LEFT_CHILD_NODE and len(cst.children) >= 2:
            left_child = cst.children.pop(0)
            ast.children.append(
                Tree(left_child.value + "," + left_child.type, []))
            is_add_ast_children = True
        # ノード名がformula_dataの場合はそれぞれの文字列に書き換える
        if cst.data == "formula_data":
            ast.children.append(
                Tree(FORMULA_DATA_TO_REPLACE_SYMBOL[cst.children[0].data], []))
            is_add_ast_children = True
        for child in cst.children:
            # astに子が追加されている場合は追加した子にノードを追加していく
            if is_add_ast_children:
                self.convert_cst2ast(
                    child, ast.children[-1], cst.data)
            else:
                self.convert_cst2ast(
                    child, ast, cst.data)

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
        if json_formula is None:
            json_formula = list()
        dict_formula = dict()

        # Tokenの場合
        if type(node) != Tree:
            dict_formula["type"] = node.type
            dict_formula["symbol"] = node.value
            json_formula.append(dict_formula)
            return json_formula

        # 抽象構文木を作成する際に中心または左のトークンに書き換えたノードの場合
        if "," in node.data:
            node_name, node_type = node.data.split(",")
            dict_formula["symbol"] = node_name
            if node_name in SYMBOL2TYPE:
                dict_formula["type"] = SYMBOL2TYPE[node_name]
            elif "FUNCTOR" in node_type:
                dict_formula["type"] = "function"
            else:
                dict_formula["type"] = node_type
        else:
            dict_formula["type"] = None
            dict_formula["symbol"] = node.data
        dict_formula["children"] = list()
        json_formula.append(dict_formula)
        for child in node.children:
            self.__convert_ast2json_formula(
                child, json_formula[-1]["children"])

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
        annotation2dict["source"] = node.children[0].data
        annotation2dict["useful_info"] = list()
        if "inference" in annotation2dict["source"]:
            annotation2dict["inference_parents"] = list()
        for i, child in enumerate(node.children[0].children):
            if i == 0 and "inference" in annotation2dict["source"]:
                annotation2dict["inference_rule"] = child
            elif i == 0 and "file" in annotation2dict["source"]:
                annotation2dict["file_name"] = child
            elif "inference" in annotation2dict["source"] and i == 2:
                for grand_child in child.children:
                    annotation2dict["inference_parents"].append(grand_child)
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
                formula_info["annotations"] (dict): 参照したformulaの名前などの補足情報
        """
        formula_info = dict()
        formula_info["formula_type"] = ast_child.data
        formula_info["name"] = ast_child.children[0]
        formula_info["formula_role"] = ast_child.children[1]
        formula_info["formula"] = self.__convert_ast2json_formula(
            ast_child.children[2])
        if ast_child.children[3].children:
            formula_info["annotations"] = self.__convert_ast2json_annotation(
                ast_child.children[3])
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
                        "annotations":(dict): 参考にしたformulaの名前などの補足情報
                            {
                                "source":(str): annotationの種類(inference,fileなど)
                                "file":(str): 参照しているファイルのパス(annotations[]["source"]が"file"のときのみ存在)
                                "inference_rule":(str): どの操作をしているかの情報(annotations[]["source"]が"inference"のときのみ存在)
                                "inference_parents":(list): どのformulaを参照しているかの情報(annotations[]["source"]が"inference"のときのみ存在)
                                "useful_info":(list): 上記以外の情報を文字列のリストにして保存している
                            }
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

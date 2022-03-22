import json
from graphviz import Digraph
from lark import Lark, Tree, Token
import networkx as nx

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

# 方針
# 基本的に子が一つしかなく記号などを含んでいない場合は飛ばす
# 子が二つ以上あるものは基本的に残す
# 子が二つ以上ある場合の内、ノードA : ノードB "," ノードAのように再帰が使用されているものは飛ばすそれ以外は残す
# ノード名 : ノード名 |...| "(" ノード名 ")" or "[" ノード名 "]"が親ノードで子が"(" ノード名 ")" or "[" ノード名 "]"のときの子ノードは残す
# thf_atom_typing : UNTYPED_ATOM ":" thf_top_level_type | "(" thf_atom_typing ")"のように文法のノード名と"(" ノード名 ")"のノード名が同じなら飛ばす
# ノード名 トークン(+など)or記号(@など) ノード名、記号"("ノード名...")"、 トークン"("ノード名...")"、 トークン ノード名...となっている場合はそのノードにトークン、記号の情報を付与する
# 親ノードにトークン情報が付与されていないトークンは残す
# tf1_quantified_type : "!>" "[" tff_variable_list "]" ":" tff_monotypeや、
# tcf_quantified_formula : "!" "[" tff_variable_list "]" ":" cnf_formulaのように
# 文字列 or トークン"[" ノード名 "]" ":" ノード名となっている場合は、文字列、トークン情報を付与する
# この時、"[" ノード名 "]"のノード名()は飛ばさないようにする
# 理由
# "[" ノード名 "]"はノードA : ノードB "," ノードAのように再帰されている
# これを飛ばすとtf1_quantified_type等のノードの子に"[" ノード名 "]"を展開したものと":" ノード名が来る
# これだと子を見た時、どこまでが"[" ノード名 "]"を展開したものなのか判別不能なため、このような場合のみ"[" ノード名 "]"を残す

# ハードコーディングしている部分
# 方針に従ってノードを作成する処理

# NODE_MODIFICATION_RULEで実現している部分
# 方針にしたがってノードを作成する際の場合分け
#   NODE_MODIFICATION_RULE[key][None, None](常に子が二つ以上ある、括弧が使用されている場合)
#       無条件でノードを作成
#   NODE_MODIFICATION_RULE[key][Node_name, None](括弧が使用されているノードの場合)
#       Node_nameが親ノード名と等しければノードを作成
#   NODE_MODIFICATION_RULE[key][None, "SINGLE_CHILD" or 記号](子にトークンもしくは記号がある)
#       唯一存在するトークンの子ノードの情報もしくは記号の情報を付与したノードを作成
#   NODE_MODIFICATION_RULE[key][Node_name, "SINGLE_CHILD" or 記号]
#       Node_nameが親ノード名と等しければ、唯一存在するトークンの子ノードの情報もしくは記号の情報を付与したノードを作成

# 具象構文木から抽象構文木を構築するときにノードを作成するルール
# key: 現在のノード（具象構文木）
# value: [親ノードの条件、作成するノード名の引継元]
# 親ノードの条件(str or None): 親ノード名が文字列と等しければノードを作成する．Noneなら無条件で作成する。
# 作成するノード名の引継元(str or None): 指定された名前の子ノードから名前を引き継ぐ。ただし、子ノードがトークンだった場合は、トークン情報も付与する。ただし"SINGLE_CHILD"であれば、唯一存在する子ノードから名前を引き継ぐ。Noneなら現在のノードの名前を引き継ぐ。
NODE_MODIFICATION_RULE = {"thf_logic_formula": ["thf_unitary_formula", None], "tff_logic_formula": ["tff_unitary_formula", None],
                          "tff_atom_typing_list": ["tfx_let_types", None], "tfx_let_defn_list": ["tfx_let_defns", None],
                          "tff_logic_formula": ["tff_unitary_term", None], "tff_arguments": ["tfx_tuple", None],
                          "tff_mapping_type": ["tff_monotype", None], "tff_xprod_type": ["tff_unitary_type", None],
                          "tff_type_list": ["tfx_tuple_type", None], "fof_logic_formula": ["fof_unitary_formula", None],
                          "tff_variable_list": ["tff_quantified_formula", None], "fof_variable_list": ["fof_quantified_formula", None],
                          "tff_variable_list": ["tf1_quantified_type", None], "tff_variable_list": ["tcf_quantified_formula", None],
                          "annotations": [None, None], "thf_quantified_formula": [None, None], "optional_info": [None, None],
                          "thf_tuple": [None, None], "tfx_tuple": [None, None], "tfx_tuple_type": [None, None], "fof_formula_tuple": [None, None],
                          "formula_selection": [None, None], "general_list": [None, None], "thf_subtype": [None, None],
                          "thf_binary_nonassoc": [None, "SINGLE_CHILD"], "thf_or_formula": [None, "SINGLE_CHILD"],
                          "thf_and_formula": [None, "SINGLE_CHILD"], "thf_infix_unary": [None, "SINGLE_CHILD"],
                          "thf_defined_infix": [None, "SINGLE_CHILD"], "thf_let_defn": [None, "SINGLE_CHILD"],
                          "thf_mapping_type": [None, "SINGLE_CHILD"], "thf_xprod_type": [None, "SINGLE_CHILD"], "thf_union_type": [None, "SINGLE_CHILD"],
                          "thf_sequent": [None, "SINGLE_CHILD"],
                          "tff_binary_nonassoc": [None, "SINGLE_CHILD"], "tff_or_formula": [None, "SINGLE_CHILD"],
                          "tff_and_formula": [None, "SINGLE_CHILD"], "tff_infix_unary": [None, "SINGLE_CHILD"],
                          "tff_infix_unary": [None, "SINGLE_CHILD"], "tff_defined_infix": [None, "SINGLE_CHILD"],
                          "tfx_let_defn": [None, "SINGLE_CHILD"], "tff_mapping_type": [None, "SINGLE_CHILD"], "tff_xprod_type": [None, "SINGLE_CHILD"],
                          "tff_subtype": [None, "SINGLE_CHILD"], "tfx_sequent": [None, "SINGLE_CHILD"],
                          "fof_binary_nonassoc": [None, "SINGLE_CHILD"], "fof_or_formula": [None, "SINGLE_CHILD"],
                          "fof_and_formula": [None, "SINGLE_CHILD"], "fof_infix_unary": [None, "SINGLE_CHILD"],
                          "fof_defined_infix_formula": [None, "SINGLE_CHILD"], "fof_sequent": [None, "SINGLE_CHILD"],
                          "disjunction": [None, "SINGLE_CHILD"],
                          "thf_apply_formula": [None, "@"], "thf_typed_variable": [None, "："], "thf_atom_typing": [None, "："],
                          "tff_typed_variable": [None, "："], "tff_atom_typing": [None, "："], "general_term": [None, "："],
                          "tpi_annotated": [None, "tpi"], "thf_annotated": [None, "thf"], "tff_annotated": [None, "tff"], "tcf_annotated": [None, "tch"],
                          "fof_annotated": [None, "fof"], "cnf_annotated": [None, "cnf"], "thf_conditional": [None, "$ite"], "thf_let": [None, "$let"],
                          "tfx_conditional": [None, "$ite"], "tfx_let": [None, "$let"], "include": [None, "include"], "tf1_quantified_type": [None, "!>"],
                          "tcf_quantified_formula": [None, "!"],
                          "thf_quantification": [None, "SINGLE_CHILD"], "thf_prefix_unary": [None, "SINGLE_CHILD"],
                          "thf_fof_function": [None, "SINGLE_CHILD"],
                          "tff_prefix_unary": [None, "SINGLE_CHILD"], "tff_plain_atomic": [None, "SINGLE_CHILD"],
                          "tff_defined_plain": [None, "SINGLE_CHILD"], "tff_system_atomic": [None, "SINGLE_CHILD"],
                          "tff_atomic_type": [None, "SINGLE_CHILD"], "fof_unary_formula": [None, "SINGLE_CHILD"],
                          "fof_plain_term": [None, "SINGLE_CHILD"], "fof_defined_plain_term": [None, "SINGLE_CHILD"],
                          "fof_system_term": [None, "SINGLE_CHILD"], "general_function": [None, "SINGLE_CHILD"],
                          "literal": [None, "SINGLE_CHILD"], "tff_quantified_formula": [None, "SINGLE_CHILD"],
                          "fof_quantified_formula": [None, "SINGLE_CHILD"],
                          "thf_formula": ["formula_data", "$thf"], "tff_formula": ["formula_data", "$tff"], "fof_formula": ["formula_data", "$fof"],
                          "cnf_formula": ["formula_data", "$cnf"], "fof_term": ["formula_data", "$fot"]}


class ParseTstp():
    """Parse_tstp

    tstpファイルをjson形式に保存するためのクラス

    Attributes:
        lark_path (str): 使用するtptp文法ファイルのパス
    """

    def __init__(self, lark_path):
        self.lark_path = lark_path

    def __collect_digraph_data(self, node, node_id, graph_nodes, graph_edges):
        """__collect_digraph_data

        グラフを作成するために必要なデータ(エッジ等)を収集する関数

        Args:
            node (Tree or Token): 木のノード
            node_id (int): ノードごとに振られるノードID
            graph_nodes (list): グラフのノードの集合
            graph_edges (list): グラフのエッジの集合
        """
        if type(node) != Tree:
            return

        if not graph_nodes:
            graph_nodes.append(node.data)

        for child in node.children:
            if type(child) == Tree:
                graph_nodes.append(child.data)
            else:
                # Token
                graph_nodes.append(child.value + "," + child.type)
            child_id = len(graph_nodes) - 1
            graph_edges.append([str(node_id), str(child_id)])
            self.__collect_digraph_data(
                child, child_id, graph_nodes, graph_edges)

    def create_tree_graph(self, tree_root, png_path):
        """create_tree_graph

        larkで作成した木をグラフ化してpngで保存する関数

        Args:
            tree_root (Tree): larkで作成した木
            png_path (str): 保存するpngファイルパス
        """
        graph_nodes = []
        graph_edges = []
        G = Digraph(format="png")
        self.__collect_digraph_data(tree_root, 0, graph_nodes, graph_edges)
        for i, node in enumerate(graph_nodes):
            G.node(str(i), node)
        for u, v in graph_edges:
            G.edge(u, v)
        G.render(png_path)

    def create_tree_graph_networkx(self, tree_root, png_path):
        """create_tree_graph_networkx

        larkで作成した木をnetworkxでグラフ化してpngで保存する関数

        Args:
            tree_root (Tree): larkで作成した木
            png_path (str): 保存するpngファイルパス
        """
        graph_nodes = []
        graph_edges = []
        G = nx.DiGraph()
        self.__collect_digraph_data(tree_root, 0, graph_nodes, graph_edges)
        for i, node in enumerate(graph_nodes):
            G.add_node(str(i), label=node)
        G.add_edges_from(graph_edges)
        agraph = nx.nx_agraph.to_agraph(G)
        agraph.draw(png_path, prog="dot", format="png")

    def __is_leave_node(self, cst, cst_parent_data):
        """__is_leave_node

        残すノードかどうかを判定する関数
            * どの場合でも子が二つ以上ある、括弧が使用されている場合
            * 括弧が使用されている場合

        Args:
            cst(Tree): 具象構文木のノード
            cst_parent_data(Tree): cstの親のノード名

        Returns:
            (bool): 残すならTrue、省略するならFalse
        """
        return cst.data in NODE_MODIFICATION_RULE and (
            NODE_MODIFICATION_RULE[cst.data][0] == cst_parent_data and NODE_MODIFICATION_RULE[cst.data][1] == None or
            NODE_MODIFICATION_RULE[cst.data][0] == None and NODE_MODIFICATION_RULE[cst.data][1] == None)

    def convert_cst2ast(self, cst, ast=Tree("tptp_root", []), cst_parent_data=None, cst_parent_children_length=None):
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
            # 親ノードでトークン情報を付与したトークンでないなら抽象構文木に加える
            if not (cst_parent_data in NODE_MODIFICATION_RULE and NODE_MODIFICATION_RULE[cst_parent_data][1] == "SINGLE_CHILD" and cst_parent_children_length >= 2):
                ast.children.append(cst)
            return ast

        # astに子が追加されたかどうか
        is_add_ast_children = False

        # 飛ばさない場合は抽象構文木に加える
        if self.__is_leave_node(cst, cst_parent_data):
            ast.children.append(Tree(cst.data, []))
            is_add_ast_children = True
        # 親ノード名がformula_dataの場合
        elif cst.data in NODE_MODIFICATION_RULE and NODE_MODIFICATION_RULE[cst.data][0] == cst_parent_data and NODE_MODIFICATION_RULE[cst.data][1]:
            ast.children.append(
                Tree(NODE_MODIFICATION_RULE[cst.data][1] + "," + cst.data, []))
            is_add_ast_children = True
        # トークン情報を付与する場合
        elif cst.data in NODE_MODIFICATION_RULE and len(cst.children) >= 2 and NODE_MODIFICATION_RULE[cst.data][1] == "SINGLE_CHILD":
            for i, child in enumerate(cst.children):
                if type(child) == Token:
                    token = cst.children[i]
                    ast.children.append(
                        Tree(token.value + "," + token.type, []))
                    is_add_ast_children = True
                    break
        # 記号情報を付与する場合
        elif cst.data in NODE_MODIFICATION_RULE and len(cst.children) >= 2 and NODE_MODIFICATION_RULE[cst.data][1]:
            ast.children.append(
                Tree(NODE_MODIFICATION_RULE[cst.data][1] + "," + cst.data, []))
            is_add_ast_children = True

        for child in cst.children:
            # astに子が追加されている場合は追加した子にノードを追加していく
            if is_add_ast_children:
                self.convert_cst2ast(
                    child, ast.children[-1], cst.data, len(cst.children))
            else:
                self.convert_cst2ast(
                    child, ast, cst.data, len(cst.children))

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

        # 抽象構文木を作成する際トークン情報、記号情報を付与したノードの場合
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
        annotation2dict["source"] = node.children[0].data.split(",")[0]
        annotation2dict["useful_info"] = list()
        if annotation2dict["source"] == "inference":
            annotation2dict["inference_parents"] = list()
        for i, child in enumerate(node.children[0].children):
            if i == 0 and annotation2dict["source"] == "inference":
                annotation2dict["inference_rule"] = child
            elif i == 0 and "file" in annotation2dict["source"]:
                annotation2dict["file_name"] = child
            elif annotation2dict["source"] == "inference" and i == 2:
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
        G = nx.DiGraph()
        for formula_info in json_root:
            if "inference" in formula_info["annotations"]["source"]:
                for inference_parent in formula_info["annotations"]["inference_parents"]:
                    G.add_edge(inference_parent, formula_info["name"])
        agraph = nx.nx_agraph.to_agraph(G)
        agraph.draw(png_path, prog="dot", format="png")

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

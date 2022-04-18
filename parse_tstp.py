import json
from graphviz import Digraph
from lark import Lark, Tree, Token
import networkx as nx
from networkx.readwrite import json_graph


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

# 具象構文木から抽象構文木を構築するときにノードを作成するルール
# key: 現在のノード（具象構文木）
# value: {"parent": 親ノードの名前、"child": 削除する子ノードの名前}
# 親ノードの名前(str): 親ノード名が文字列と等しければノードを作成する．Noneなら無条件で作成する。
# 削除する子ノードの名前(str or list): 削除する子ノードの名前があるなら、子ノードの情報を付与する。
# 削除する子ノードの名前はリストになることもある
# parent, childが省略されているときはNoneとみなす
NODE_MODIFICATION_RULE = {"thf_logic_formula": {"parent": "thf_unitary_formula"}, "tff_logic_formula": {"parent": "tff_unitary_formula"},
                          "tff_atom_typing_list": {"parent": "tfx_let_types"}, "tfx_let_defn_list": {"parent": "tfx_let_defns"},
                          "tff_logic_formula": {"parent": "tff_unitary_term"}, "tff_arguments": {"parent": "tfx_tuple"},
                          "tff_mapping_type": {"parent": "tff_monotype"}, "tff_xprod_type": {"parent": "tff_unitary_type"},
                          "tff_type_list": {"parent": "tfx_tuple_type"}, "fof_logic_formula": {"parent": "fof_unitary_formula"},
                          "tff_variable_list": {"parent": "tff_quantified_formula"}, "fof_variable_list": {"parent": "fof_quantified_formula"},
                          "tff_variable_list": {"parent": "tf1_quantified_type"}, "tff_variable_list": {"parent": "tcf_quantified_formula"},
                          "annotations": {}, "thf_quantified_formula": {}, "optional_info": {},
                          "thf_tuple": {}, "tfx_tuple": {}, "tfx_tuple_type": {}, "fof_formula_tuple": {},
                          "formula_selection": {}, "general_list": {}, "thf_subtype": {},
                          "thf_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"}, "thf_or_formula": {"child": "VLINE"},
                          "thf_and_formula": {"child": "AND_CONNECTIVE"}, "thf_infix_unary": {"child": "INFIX_INEQUALITY"},
                          "thf_defined_infix": {"child": "DEFINED_INFIX_PRED"}, "thf_let_defn": {"child": "ASSIGNMENT"},
                          "thf_mapping_type": {"child": "ARROW"}, "thf_xprod_type": {"child": "STAR"}, "thf_union_type": {"child": "PLUS"},
                          "thf_sequent": {"child": "GENTZEN_ARROW"},
                          "tff_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"}, "tff_or_formula": {"child": "VLINE"},
                          "tff_and_formula": {"child": "AND_CONNECTIVE"}, "tff_infix_unary": {"child": "INFIX_INEQUALITY"},
                          "tff_infix_unary": {"child": "INFIX_INEQUALITY"}, "tff_defined_infix": {"child": "DEFINED_INFIX_PRED"},
                          "tfx_let_defn": {"child": "ASSIGNMENT"}, "tff_mapping_type": {"child": "ARROW"}, "tff_xprod_type": {"child": "STAR"},
                          "tff_subtype": {"child": "SUBTYPE_SIGN"}, "tfx_sequent": {"child": "GENTZEN_ARROW"},
                          "fof_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"}, "fof_or_formula": {"child": "VLINE"},
                          "fof_and_formula": {"child": "AND_CONNECTIVE"}, "fof_infix_unary": {"child": "INFIX_INEQUALITY"},
                          "fof_defined_infix_formula": {"child": "DEFINED_INFIX_PRED"}, "fof_sequent": {"child": "GENTZEN_ARROW"},
                          "disjunction": {"child": "VLINE"},
                          "thf_apply_formula": {"child": "APPLY_SYMBOL"}, "thf_typed_variable": {"child": "："}, "thf_atom_typing": {"child": "："},
                          "tff_typed_variable": {"child": "："}, "tff_atom_typing": {"child": "："}, "general_term": {"child": "："},
                          "tpi_annotated": {"child", "TPI"}, "thf_annotated": {"child": "THF"}, "tff_annotated": {"child", "TFF"}, "tcf_annotated": {"child": "TCH"},
                          "fof_annotated": {"child": "FOF"}, "cnf_annotated": {"child": "CNF"}, "thf_conditional": {"child": "DOLLAR_ITE"}, "thf_let": {"child": "DOLLAR_LET"},
                          "tfx_conditional": {"child": "DOLLAR_ITE"}, "tfx_let": {"child": "DOLLAR_LET"}, "include": {"child", "INCLUDE"}, "tf1_quantified_type": {"child": "TH1_QUANTIFIER"},
                          "tcf_quantified_formula": {"child": "FOF_QUANTIFIER"},
                          "thf_quantification": {"child": "THF_QUANTIFIER"}, "thf_prefix_unary": {"child": "UNARY_CONNECTIVE"},
                          "thf_fof_function": {"child": ["FUNCTOR", "DEFINED_FUNCTOR", "SYSTEM_FUNCTOR"]},
                          "tff_prefix_unary": {"child": "UNARY_CONNECTIVE"}, "tff_plain_atomic": {"child": "FUNCTOR"},
                          "tff_defined_plain": {"child": "DEFINED_FUNCTOR"}, "tff_system_atomic": {"child": "SYSTEM_FUNCTOR"},
                          "tff_atomic_type": {"child": "TYPE_FUNCTOR"}, "fof_unary_formula": {"child": "UNARY_CONNECTIVE"},
                          "fof_plain_term": {"child": "FUNCTOR"}, "fof_defined_plain_term": {"child": "DEFINED_FUNCTOR"},
                          "fof_system_term": {"child", "SYSTEM_FUNCTOR"}, "general_function": {"child": "ATOMIC_WORD"},
                          "literal": {"child": "UNARY_CONNECTIVE"}, "tff_quantified_formula": {"child": "FOF_QUANTIFIER"},
                          "fof_quantified_formula": {"child": "FOF_QUANTIFIER"},
                          "thf_formula": {"parent": "formula_data", "child": "DOLLAR_THF"}, "tff_formula": {"parent": "formula_data", "child": "DOLLAR_TFF"},
                          "fof_formula": {"parent": "formula_data", "child": "DOLLAR_FOF"}, "cnf_formula": {"parent": "formula_data", "child": "DOLLAR_CNF"},
                          "fof_term": {"parent": "formula_data", "child": "DOLLAR_FOT"}}


class ParseTstp():
    """Parse_Tstp

    tstpファイルをjson形式に保存するためのクラス

    Attributes:
        lark_path (str): 使用するtptp文法ファイルのパス
    """

    def __init__(self, lark_path):
        self.lark_path = lark_path

    def collect_digraph_data(self, node, node_id, graph_nodes, graph_edges):
        """collect_digraph_data

        グラフを作成するために必要なデータ(エッジ等)を収集する関数

        Args:
            node (Tree or Token): 木のノード
            node_id (int): ノードごとに振られるノードID
            graph_nodes (list): グラフのノードの集合
            graph_edges (list): グラフのエッジの集合
        """
        if type(node) == Tree:
            graph_nodes.append(
                (str(len(graph_nodes)), {"label": node.data}))
        else:
            graph_nodes.append(
                (str(len(graph_nodes)), {"label": node.value + "," + node.type}))
            return

        for child in node.children:
            child_id = len(graph_nodes)
            graph_edges.append([str(node_id), str(child_id)])
            self.collect_digraph_data(
                child, child_id, graph_nodes, graph_edges)

    def create_tree_graph_on_graphviz(self, graph_nodes, graph_edges):
        """create_tree_graph_on_graphviz

        graphvizのインスタンスにノードとエッジを追加し、graphvizのインスタンスを返す関数

        Args:
            graph_nodes (list): グラフに追加するノードのリスト
            graph_edges (list): グラフに追加するエッジのリスト
        Returns:
            G(graphviz.graphs.Digraph): ノードとエッジを追加したgraphvizのインスタンス
        """
        G = Digraph()
        for node_id, attr in graph_nodes:
            G.node(str(node_id), attr["label"])
        G.edges(graph_edges)
        return G

    def show_tree_graph_on_graphviz(self, G, path):
        """show_tree_graph_on_graphviz

        graphvizのインスタンスからグラフを描画し、引数のpathに保存する関数

        Args:
            G (graphviz.graphs.Digraph): ノードとエッジを追加したgraphvizのインスタンス
            path (str): グラフを保存するパス
        """
        G.render(path, format="png")

    def create_tree_graph_on_networkx(self, graph_nodes, graph_edges):
        """create_tree_graph_on_networkx

        networkxのインスタンスにノードとエッジを追加し、networkxのインスタンスを返す関数

        Args:
            graph_nodes (list): グラフに追加するノードのリスト
            graph_edges (list): グラフに追加するエッジのリスト

        Returns:
            G(networkx.classes.digraph.DiGraph): ノードとエッジを追加したnetworkxのインスタンス
        """
        G = nx.DiGraph()
        G.add_nodes_from(graph_nodes)
        G.add_edges_from(graph_edges)
        return G

    def show_tree_graph_on_networkx(self, G, path):
        """show_tree_graph_on_networkx

        networkxのインスタンスからグラフを描画し、引数のpathに保存する関数

        Args:
            G (networkx.classes.digraph.DiGraph): ノードとエッジを追加したnetworkxのインスタンス
            path (str): グラフを保存するパス
        """
        agraph = nx.nx_agraph.to_agraph(G)
        agraph.draw(path, prog="dot", format="png")

    def __satisfy_parent_condition(self, cst_data, cst_parent_data):
        """__satisfy_parent_condition

        NODE_MODIFICATION_RULEの親ノードの条件を満たしているかどうかをboolで返す関数

        Args:
            cst_data(str): 具象構文木のノード名
            cst_parent_data(str): 具象構文木の親のノード名

        Returns:
            (bool): 親ノードの条件を満たしているならTrueそうでないならFalse
        """
        return cst_data in NODE_MODIFICATION_RULE and "parent" in NODE_MODIFICATION_RULE[cst_data] and NODE_MODIFICATION_RULE[cst_data]["parent"] == cst_parent_data

    def __satisfy_name_inherit_condition(self, cst_data):
        """__satisfy_name_inherit_condition

        NODE_MODIFICATION_RULEの作成するノード名の引継元があるかどうかをboolで返す関数

        Args:
            cst_data(str): 具象構文木のノード名

        Returns:
            (bool): 作成するノード名の引継元があるならTrueそうでないならFalse
        """

        return cst_data in NODE_MODIFICATION_RULE and "child" in NODE_MODIFICATION_RULE[cst_data]

    def __satisfy_token_remove_condition(self, cst, cst_parent_data):
        """__satisfy_token_remove_condition

        削除するトークンかどうかを判定する関数
            * 親のノードでトークン情報を付与している場合
                具体例
                    thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula

        Args:
            cst (Token): 具象構文木のノード
            cst_parent_data (str): 具象構文木の親ノードの名前

        Returns:
            (bool): 削除するならTrue、そうでないならFalse
        """
        return cst_parent_data in NODE_MODIFICATION_RULE and NODE_MODIFICATION_RULE[cst_parent_data]["child"] == cst.value

    def __satisfy_node_remove_condition(self, cst_data, cst_parent_data):
        """__satisfy_node_remove_condition

        削除するノードかどうかを判定する関数
            以下のいずれでもない場合
                * 全ての文法導出に対して「子が二つ以上ある」または「括弧で括られている」
                    具体例
                        thf_quantified_formula : thf_quantification thf_unit_formula
                        thf_tuple            : "[]" | "[" thf_formula_list "]"
                * ある文法導出に対して「括弧で括られている」
                    具体例
                        tff_monotype         : tff_atomic_type | "(" tff_mapping_type ")" | tf1_quantified_type

        Args:
            cst_data(str): 具象構文木のノード名
            cst_parent_data(str): 具象構文木の親のノード名

        Returns:
            (bool): 削除するならTrue、そうでないならFalse
        """
        is_leave_unconditional = cst_data in NODE_MODIFICATION_RULE \
            and "parent" in NODE_MODIFICATION_RULE[cst_data] \
            and "child" in NODE_MODIFICATION_RULE[cst_data]
        is_enclosed_with_parentheses = self.__satisfy_parent_condition(cst_data, cst_parent_data) \
            and not self.__satisfy_name_inherit_condition(cst_data)
        return not is_leave_unconditional and not is_enclosed_with_parentheses

    def __is_inherit_token_info(self, cst):
        """__is_inherit_token_info

        トークン情報を付与するかどうかをboolで返す関数
        具体例
            thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula

        Args:
            cst(Tree): 具象構文木のノード

        Returns:
            (bool): トークン情報を付与するならTrueそうでないならFalse
        """
        child_token = [
            child.value for child in cst.children if type(child) == Token]
        # NODE_MODIFICATION_RULE[cst.data]["child"]とcstの子のトークンが互いに素でないかを調べることで
        # 子のトークンにNODE_MODIFICATION_RULE[cst.data]["child"]の要素があるかを調べている
        return self.__satisfy_name_inherit_condition(cst.data) and not set(NODE_MODIFICATION_RULE[cst.data]["child"]).isdisjoint(set(child_token))

    def __is_inherit_symbol_info(self, cst):
        """__is_inherit_symbol_info

        シンボル情報を付与するかどうかをboolで返す関数
        具体例
            thf_apply_formula    : thf_unit_formula "@" thf_unit_formula | thf_apply_formula "@" thf_unit_formula

        Args:
            cst(Tree): 具象構文木のノード

        Returns:
            (bool): シンボル情報を付与するならTrueそうでないならFalse
        """
        return self.__satisfy_name_inherit_condition(cst.data) and len(cst.children) >= 2 and NODE_MODIFICATION_RULE[cst.data][1] != "$REMOVE_CHILD_TOKEN"

    def __has_formula_parent(self, cst_data, cst_parent_data):
        """__has_formula_parent

        親ノードの条件がformula_dataかどうかをboolで返す関数
            * 親ノードの条件があるかつ、引継ぎ元がある場合は親ノードの条件がformula_dataである場合しかない
              そのため、式に意味はない

        Args:
            cst_data(str): 具象構文木のノード名
            cst_parent_data(str): 具象構文木の親のノード名

        Returns:
            (bool): 親ノードの条件がformula_dataならTrue、そうでないならFalse
        """
        # この式に意味はない
        return self.__satisfy_parent_condition(cst_data, cst_parent_data) and self.__satisfy_name_inherit_condition(cst_data)

    def convert_cst2ast(self, cst, ast=None, cst_parent_data=None, cst_siblings_num=None):
        """convert_cst2ast

        具象構文木から抽象構文木を作成する関数

        Args:
            cst(Tree or Token): 具象構文木のノード
            ast(Tree): 抽象構文木のノード
            cst_parent_data(str): 具象構文木の親のノード名
            cst_siblings_num(int): 具象構文木の兄弟の数

        Returns:
            ast(Tree): 最終的に作成される抽象構文木
        """
        if ast is None:
            ast = Tree("tptp_root", [])

        # トークンの場合
        if type(cst) != Tree:
            if not self.__satisfy_token_remove_condition(cst, cst_parent_data):
                ast.children.append(cst)
            return ast

        # これ以降は内部ノード
        if not self.__satisfy_node_remove_condition(cst.data, cst_parent_data):
            ast.children.append(Tree(cst.data, []))
            ast_next = ast.children[-1]
        elif self.__has_formula_parent(cst.data, cst_parent_data) or self.__is_inherit_symbol_info(cst):
            # NODE_MODIFICATION_RULEのvalueである、親ノードの条件と作成するノード名の引継元がどちらもあるときは
            # 作成するノード名の引継元が記号の場合しかないため、作成するノード名の引継元が記号の場合の処理と同様になる
            ast.children.append(
                Tree(NODE_MODIFICATION_RULE[cst.data][1] + "," + cst.data, []))
            ast_next = ast.children[-1]
        elif self.__is_inherit_token_info(cst):
            for child in cst.children:
                if type(child) == Token:
                    token = child
                    ast.children.append(
                        Tree(token.value + "," + token.type, []))
                    ast_next = ast.children[-1]
                    # 子にトークンは一つしか存在しないためbreakする
                    break
        else:
            ast_next = ast

        for child in cst.children:
            self.convert_cst2ast(child, ast_next, cst.data, len(cst.children))

        return ast

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

    def __get_formula_label(self, ast_top):
        """__get_formula_label

        抽象構文木から導出された式のラベルを返す関数

        Args:
            ast_top (Tree): 抽象構文木の根の子

        Returns:
            formula_label (str): 導出された式のラベル
        """
        formula_label = ast_top.children[0].value
        return formula_label

    def __is_inference(self, annotations):
        """__is_inference

        annotationsの子にinferenceがあるかどうかをboolで返す関数

        Args:
            annotations (Tree): 抽象構文木のannotations部分のTree

        Returns:
            (bool): annotationsの子にinferenceがあるならTrue、そうでないならFalse
        """
        return annotations and "inference" in annotations[0].data

    def __get_assumption_formula_labels(self, ast_top):
        """__get_assumption_formula_labels

        参照した式のラベルを返す関数

        Args:
            ast_top (Tree): 抽象構文木の根の子

        Returns:
            assumption_formula_labels (list): 参照した式のラベルのリスト
        """
        assumption_formula_labels = list()
        annotations = ast_top.children[-1].children
        if not self.__is_inference(annotations):
            return assumption_formula_labels
        inference_parents = annotations[0].children[-1].children
        for inference_parent in inference_parents:
            assumption_formula_label = inference_parent.value
            assumption_formula_labels.append(assumption_formula_label)
        return assumption_formula_labels

    def create_deduction_tree_graph_on_networkx(self, ast_root):
        """create_deduction_tree_graph_on_networkx

        抽象構文木から証明のグラフを作成する関数

        Args:
            ast_root (Tree): 抽象構文木の根

        Returns:
            G(networkx.classes.digraph.DiGraph): エッジを追加したnetworkxのインスタンス
        """
        graph_edges = list()
        for child in ast_root.children:
            formula_label = self.__get_formula_label(child)
            assumption_formula_labels = self.__get_assumption_formula_labels(
                child)
            for assumption_formula_label in assumption_formula_labels:
                graph_edges.append([assumption_formula_label, formula_label])
        G = nx.DiGraph()
        G.add_edges_from(graph_edges)
        return G

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
        graph_nodes = list()
        graph_edges = list()
        self.collect_digraph_data(ast_root, 0, graph_nodes, graph_edges)
        ast_graph = self.create_tree_graph_on_networkx(
            graph_nodes, graph_edges)
        json_root = json_graph.node_link_data(ast_graph)
        with open(json_path, "w") as f:
            json.dump(json_root, f, indent=4)

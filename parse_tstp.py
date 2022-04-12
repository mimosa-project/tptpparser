import json
from graphviz import Digraph
from lark import Lark, Tree, Token
import networkx as nx
from networkx.readwrite import json_graph
from bisect import bisect


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
# value: [親ノードの条件、作成するノード名の引継元]
# 親ノードの条件(str or None): 親ノード名が文字列と等しければノードを作成する．Noneなら無条件で作成する。
# 作成するノード名の引継元(str or None): 指定された名前の子ノードから名前を引き継ぐ。
# ただし、子ノードがトークンだった場合は、トークン情報も付与する。"$REMOVE_CHILD_TOKEN"であれば、唯一存在する子ノードから名前を引き継ぐ。Noneなら現在のノードの名前を引き継ぐ。
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
                          "thf_binary_nonassoc": [None, "$REMOVE_CHILD_TOKEN"], "thf_or_formula": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_and_formula": [None, "$REMOVE_CHILD_TOKEN"], "thf_infix_unary": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_defined_infix": [None, "$REMOVE_CHILD_TOKEN"], "thf_let_defn": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_mapping_type": [None, "$REMOVE_CHILD_TOKEN"], "thf_xprod_type": [None, "$REMOVE_CHILD_TOKEN"], "thf_union_type": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_sequent": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_binary_nonassoc": [None, "$REMOVE_CHILD_TOKEN"], "tff_or_formula": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_and_formula": [None, "$REMOVE_CHILD_TOKEN"], "tff_infix_unary": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_infix_unary": [None, "$REMOVE_CHILD_TOKEN"], "tff_defined_infix": [None, "$REMOVE_CHILD_TOKEN"],
                          "tfx_let_defn": [None, "$REMOVE_CHILD_TOKEN"], "tff_mapping_type": [None, "$REMOVE_CHILD_TOKEN"], "tff_xprod_type": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_subtype": [None, "$REMOVE_CHILD_TOKEN"], "tfx_sequent": [None, "$REMOVE_CHILD_TOKEN"],
                          "fof_binary_nonassoc": [None, "$REMOVE_CHILD_TOKEN"], "fof_or_formula": [None, "$REMOVE_CHILD_TOKEN"],
                          "fof_and_formula": [None, "$REMOVE_CHILD_TOKEN"], "fof_infix_unary": [None, "$REMOVE_CHILD_TOKEN"],
                          "fof_defined_infix_formula": [None, "$REMOVE_CHILD_TOKEN"], "fof_sequent": [None, "$REMOVE_CHILD_TOKEN"],
                          "disjunction": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_apply_formula": [None, "@"], "thf_typed_variable": [None, "："], "thf_atom_typing": [None, "："],
                          "tff_typed_variable": [None, "："], "tff_atom_typing": [None, "："], "general_term": [None, "："],
                          "tpi_annotated": [None, "tpi"], "thf_annotated": [None, "thf"], "tff_annotated": [None, "tff"], "tcf_annotated": [None, "tch"],
                          "fof_annotated": [None, "fof"], "cnf_annotated": [None, "cnf"], "thf_conditional": [None, "$ite"], "thf_let": [None, "$let"],
                          "tfx_conditional": [None, "$ite"], "tfx_let": [None, "$let"], "include": [None, "include"], "tf1_quantified_type": [None, "!>"],
                          "tcf_quantified_formula": [None, "!"],
                          "thf_quantification": [None, "$REMOVE_CHILD_TOKEN"], "thf_prefix_unary": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_fof_function": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_prefix_unary": [None, "$REMOVE_CHILD_TOKEN"], "tff_plain_atomic": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_defined_plain": [None, "$REMOVE_CHILD_TOKEN"], "tff_system_atomic": [None, "$REMOVE_CHILD_TOKEN"],
                          "tff_atomic_type": [None, "$REMOVE_CHILD_TOKEN"], "fof_unary_formula": [None, "$REMOVE_CHILD_TOKEN"],
                          "fof_plain_term": [None, "$REMOVE_CHILD_TOKEN"], "fof_defined_plain_term": [None, "$REMOVE_CHILD_TOKEN"],
                          "fof_system_term": [None, "$REMOVE_CHILD_TOKEN"], "general_function": [None, "$REMOVE_CHILD_TOKEN"],
                          "literal": [None, "$REMOVE_CHILD_TOKEN"], "tff_quantified_formula": [None, "$REMOVE_CHILD_TOKEN"],
                          "fof_quantified_formula": [None, "$REMOVE_CHILD_TOKEN"],
                          "thf_formula": ["formula_data", "$thf"], "tff_formula": ["formula_data", "$tff"], "fof_formula": ["formula_data", "$fof"],
                          "cnf_formula": ["formula_data", "$cnf"], "fof_term": ["formula_data", "$fot"]}


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

        return cst_data in NODE_MODIFICATION_RULE and NODE_MODIFICATION_RULE[cst_data][0] == cst_parent_data

    def __satisfy_name_inherit_condition(self, cst_data):
        """__satisfy_name_inherit_condition

        NODE_MODIFICATION_RULEの作成するノード名の引継元があるかどうかをboolで返す関数

        Args:
            cst_data(str): 具象構文木のノード名

        Returns:
            (bool): 作成するノード名の引継元があるならTrueそうでないならFalse
        """

        return (cst_data in NODE_MODIFICATION_RULE) and (NODE_MODIFICATION_RULE[cst_data][1] is not None)

    def __satisfy_token_remove_condition(self, cst_parent_data, cst_siblings_num):
        """__satisfy_token_remove_condition

        残すトークンかどうかを判定する関数
            * 親のノードでトークン情報を付与していない場合
                具体例(親のノードでトークン情報を付与している場合の例)
                    thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula

        Args:
            cst_parent_data (str): 具象構文木の親ノードの名前
            cst_siblings_num (int): 具象構文木の兄弟の数

        Returns:
            (bool): 残すならTrue、省略するならFalse
        """

        return cst_parent_data in NODE_MODIFICATION_RULE and NODE_MODIFICATION_RULE[cst_parent_data][1] == "$REMOVE_CHILD_TOKEN" and cst_siblings_num >= 2

    def __satisfy_node_remove_condition(self, cst_data, cst_parent_data):
        """__satisfy_node_remove_condition

        残すノードかどうかを判定する関数
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
            (bool): 残すならTrue、省略するならFalse
        """
        is_leave_unconditional = cst_data in NODE_MODIFICATION_RULE \
            and NODE_MODIFICATION_RULE[cst_data][0] == None \
            and NODE_MODIFICATION_RULE[cst_data][1] == None
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

        return self.__satisfy_name_inherit_condition(cst.data) and len(cst.children) >= 2 and NODE_MODIFICATION_RULE[cst.data][1] == "$REMOVE_CHILD_TOKEN"

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
            * 親ノードの条件があるかつ、引継ぎ元がある場合は親ノードの条件がformula_dataである場合と等しい

        Args:
            cst_data(str): 具象構文木のノード名
            cst_parent_data(str): 具象構文木の親のノード名
        Returns:
            (bool): 親ノードの条件がformula_dataならTrue、そうでないならFalse
        """

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
            if not self.__satisfy_token_remove_condition(cst_parent_data, cst_siblings_num):
                ast.children.append(cst)
            return ast

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
            for i, child in enumerate(cst.children):
                if type(child) == Token:
                    token = cst.children[i]
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

    def __is_resolvent_formula_label(self, node_data):
        """__is_resolvent_formula_label

        導出された式のラベル名かどうかをboolで返す関数

        Args:
            node_data(str): ノードのラベル
        Returns:
            (bool): 導出された式のラベル名ならTrueそうでないならFalse
        """

        return "," in node_data and node_data.split(",")[1] == "NAME"

    def __is_assumption_formula_label(self, node_data):
        """__is_assumption_formula_label

        参照した式のラベルかどうかをboolで返す関数

        Args:
            node_data(str): ノードのラベル
        Returns:
            (bool): 参照した式のラベル名ならTrueそうでないならFalse
        """

        return "," in node_data and node_data.split(",")[1] == "ATOMIC_WORD" and node_data.split(",")[0][0].isalpha() and node_data.split(",")[0][1:].isdigit()

    def create_deduction_tree_graph_on_networkx(self, json_path):
        """create_deduction_tree_graph_on_networkx

        抽象構文木をjson形式で保存されたものから証明のグラフを作成する関数

        グラフを作成する流れ
            1. 導出された式のラベルのnode_idをkey、導出された式のラベルをvalueとしたmapを作成する
            2. 参照された式のラベルのnode_idをkey、参照された式のラベルをvalueとしたmapを作成する
            3. 導出された式のラベルのnode_idのlistを作成する
            4. 参照された式のラベルのnode_idのlistを作成する
            5. 参照された式のラベルのnode_idのlistをfor文で回し、参照された式のラベルのnode_idが
               導出された式のラベルのnode_idのlistのどこの間にあるかを2文探索で求め、
               エッジに[参照された式のラベル、導出された式のラベル]を加える
            6. エッジを追加したnetworkxのインスタンスを作成し、返す

        Args:
            json_path (str): tstpファイルをparseした結果のjsonファイルのパス
                * jsonのフォーマットはnetworkx
            png_path (str): 保存するpngファイルのバス
        Returns:
            G(networkx.classes.digraph.DiGraph): エッジを追加したnetworkxのインスタンス
        """
        with open(json_path) as f:
            json_root = json.load(f)
        resolvent_node_id2formula_label = dict()
        assumption_node_id2formula_label = dict()
        for node in json_root["nodes"]:
            if self.__is_resolvent_formula_label(node["label"]):
                formula_label = node["label"].split(",")[0]
                resolvent_node_id2formula_label[node["id"]] = formula_label
            if self.__is_assumption_formula_label(node["label"]):
                formula_label = node["label"].split(",")[0]
                assumption_node_id2formula_label[node["id"]] = formula_label
        graph_edges = list()
        resolvent_node_id_list = [int(resolvent_node_id2formula_label_key)
                                  for resolvent_node_id2formula_label_key in resolvent_node_id2formula_label.keys()]
        assumption_node_id_list = [int(assumption_formula_label_key)
                                   for assumption_formula_label_key in assumption_node_id2formula_label.keys()]
        for assumption_node_id in assumption_node_id_list:
            resolvent_node_id_index = bisect(
                resolvent_node_id_list, assumption_node_id) - 1
            resolvent_formula_label = resolvent_node_id2formula_label[str(
                resolvent_node_id_list[resolvent_node_id_index])]
            assumption_formula_label = assumption_node_id2formula_label[str(
                assumption_node_id)]
            graph_edges.append(
                [assumption_formula_label, resolvent_formula_label])
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

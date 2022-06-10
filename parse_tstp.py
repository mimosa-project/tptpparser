import json
from graphviz import Digraph
from lark import Lark, Tree, Token
import networkx as nx
from networkx.readwrite import json_graph


# 方針
# 1. 基本的に子が一つしかなく記号などを含んでいない場合は飛ばす
#   * NODE_MODIFICATION_RULEのkeyにノード名があるかどうかで判定
# 2. 子が二つ以上あるものは基本的に残す
#   * NODE_MODIFICATION_RULEのkeyにノード名があるがvalueにkeyがないかどうかで判定
#   * ：が使用されていて子が二つあるノードは別途関数で決め打ちし、子が二つ以上あるかどうかで判定
#       * 付与するトークン情報が無く、常に子が二つ以上とは限らないため、NODE_MODIFICATION_RULEに含めれない
#       * 子が二つ以上かどうかで判定すると方針3のものまで含めてしまうため決め打ちしている
# 3. 子が二つ以上ある場合の内、ノードA : ノードB "," ノードAのように再帰が使用されているものは飛ばすそれ以外は残す
#   * NODE_MODIFICATION_RULEのkeyにノード名があるかどうかで判定
#       * ただし、例外的に残す場合は記述している(方針9)
# 4. ノード名 : ノード名 |...| "(" ノード名 ")" or "[" ノード名 "]"が親ノードで子が"(" ノード名 ")" or "[" ノード名 "]"のときの子ノードは残す
#   * NODE_MODIFICATION_RULEのkeyにノード名があり、value(map)のparent(key)のvalueと親ノード名が一致するかどうかで判定
# 5. thf_atom_typing : UNTYPED_ATOM ":" thf_top_level_type | "(" thf_atom_typing ")"のように文法のノード名と"(" ノード名 ")"のノード名が同じなら飛ばす
#   * NODE_MODIFICATION_RULEのkeyにノード名があるかどうかで判定
# 6. ノード名 トークン(+など)or記号(@など) ノード名、記号"("ノード名...")"、 トークン"("ノード名...")"、 トークン ノード名...となっている場合はそのノードにトークン、記号の情報を付与する
#    このとき、付与したトークンは消す
#   * NODE_MODIFICATION_RULEのkeyにノード名があり、value(map)のchild(key)のvalueと子のトークン名が一致するかどうかで判定
# 7. 親ノードにトークン情報が付与されていないトークンは残す
#   * 方針6のトークンでないかどうかで判定
# 8. tf1_quantified_type : "!>" "[" tff_variable_list "]" ":" tff_monotypeや、
#    tcf_quantified_formula : "!" "[" tff_variable_list "]" ":" cnf_formulaのように
#    文字列 or トークン"[" ノード名 "]" ":" ノード名となっている場合は、文字列、トークン情報を付与する
#    このとき、付与したトークンは消す
#   * NODE_MODIFICATION_RULEのkeyにノード名があり、value(map)のchild(key)のvalueと子のトークン名が一致するかどうかで判定

# 具象構文木から抽象構文木を構築するときにノードを作成するルール
# key: 現在のノード（具象構文木）
# value: {"parent": 親ノードの名前、"child": 削除する子ノードの名前}
# 親ノードの名前(str or list): 親ノード名が文字列と等しければノードを作成する．Noneなら無条件で作成する。
# 親ノードの名前はリストになることもある
# 削除する子ノードの名前(str or list): 削除する子ノードの名前があるなら、子ノードの情報を付与する。
# 削除する子ノードの名前はリストになることもある
# parent, childが省略されているときはNoneとみなす
NODE_MODIFICATION_RULE = {"thf_logic_formula": {"parent": "thf_unitary_formula"}, "tff_logic_formula": {"parent": "tff_unitary_formula"},
                          "tff_atom_typing_list": {"parent": "tfx_let_types"}, "tfx_let_defn_list": {"parent": "tfx_let_defns"},
                          "tff_logic_formula": {"parent": ["tff_unitary_term", "tff_unitary_formula"]}, "tff_arguments": {"parent": "tfx_tuple"},
                          "tff_mapping_type": {"parent": "tff_monotype", "child": "ARROW"}, "tff_xprod_type": {"parent": "tff_unitary_type", "child": "STAR"},
                          "tff_type_list": {"parent": "tfx_tuple_type"}, "fof_logic_formula": {"parent": "fof_unitary_formula"},
                          "tff_variable_list": {"parent": ["tff_quantified_formula", "tf1_quantified_type", "tcf_quantified_formula"]},
                          "fof_variable_list": {"parent": "fof_quantified_formula"},
                          "thf_formula": {"parent": "formula_data"}, "tff_formula": {"parent": "formula_data"},
                          "fof_formula": {"parent": "formula_data"}, "cnf_formula": {"parent": "formula_data"},
                          "fof_term": {"parent": "formula_data"},
                          "tptp_root": {},
                          "annotations": {}, "thf_quantified_formula": {}, "optional_info": {},
                          "thf_tuple": {}, "tfx_tuple": {}, "tfx_tuple_type": {}, "fof_formula_tuple": {},
                          "thf_typed_variable": {}, "thf_atom_typing": {}, "tff_typed_variable": {}, "tff_atom_typing": {},
                          "formula_selection": {}, "general_list": {}, "thf_subtype": {"child": "SUBTYPE_SIGN"},
                          "thf_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"}, "thf_or_formula": {"child": "VLINE"},
                          "thf_and_formula": {"child": "AND_CONNECTIVE"}, "thf_infix_unary": {"child": "INFIX_INEQUALITY"},
                          "thf_defined_infix": {"child": "DEFINED_INFIX_PRED"}, "thf_let_defn": {"child": "ASSIGNMENT"},
                          "thf_mapping_type": {"child": "ARROW"}, "thf_xprod_type": {"child": "STAR"}, "thf_union_type": {"child": "PLUS"},
                          "thf_sequent": {"child": "GENTZEN_ARROW"},
                          "tff_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"}, "tff_or_formula": {"child": "VLINE"},
                          "tff_and_formula": {"child": "AND_CONNECTIVE"}, "tff_infix_unary": {"child": "INFIX_INEQUALITY"},
                          "tff_defined_infix": {"child": "DEFINED_INFIX_PRED"}, "tfx_let_defn": {"child": "ASSIGNMENT"},
                          "tff_subtype": {"child": "SUBTYPE_SIGN"}, "tfx_sequent": {"child": "GENTZEN_ARROW"},
                          "fof_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"}, "fof_or_formula": {"child": "VLINE"},
                          "fof_and_formula": {"child": "AND_CONNECTIVE"}, "fof_infix_unary": {"child": "INFIX_INEQUALITY"},
                          "fof_defined_infix_formula": {"child": "DEFINED_INFIX_PRED"}, "fof_sequent": {"child": "GENTZEN_ARROW"},
                          "disjunction": {"child": "VLINE"},
                          "thf_apply_formula": {"child": "APPLY_SYMBOL"},
                          "tpi_annotated": {"child": "TPI"}, "thf_annotated": {"child": "THF"}, "tff_annotated": {"child": "TFF"}, "tcf_annotated": {"child": "TCH"},
                          "fof_annotated": {"child": "FOF"}, "cnf_annotated": {"child": "CNF"}, "thf_conditional": {"child": "DOLLAR_ITE"}, "thf_let": {"child": "DOLLAR_LET"},
                          "tfx_conditional": {"child": "DOLLAR_ITE"}, "tfx_let": {"child": "DOLLAR_LET"}, "include": {"child": "INCLUDE"}, "tf1_quantified_type": {"child": "TH1_QUANTIFIER"},
                          "tcf_quantified_formula": {"child": "FOF_QUANTIFIER"},
                          "thf_quantification": {"child": "THF_QUANTIFIER"}, "thf_variable_list": {"parent": "thf_quantification"},
                          "thf_prefix_unary": {"child": "UNARY_CONNECTIVE"},
                          "thf_fof_function": {"child": ["FUNCTOR", "DEFINED_FUNCTOR", "SYSTEM_FUNCTOR"]},
                          "tff_prefix_unary": {"child": "UNARY_CONNECTIVE"}, "tff_plain_atomic": {"child": "FUNCTOR"},
                          "tff_defined_plain": {"child": "DEFINED_FUNCTOR"}, "tff_system_atomic": {"child": "SYSTEM_FUNCTOR"},
                          "tff_atomic_type": {"child": "TYPE_FUNCTOR"}, "fof_unary_formula": {"child": "UNARY_CONNECTIVE"},
                          "fof_plain_term": {"child": "FUNCTOR"}, "fof_defined_plain_term": {"child": "DEFINED_FUNCTOR"},
                          "fof_system_term": {"child": "SYSTEM_FUNCTOR"}, "general_function": {"child": "ATOMIC_WORD"},
                          "literal": {"child": "UNARY_CONNECTIVE"}, "tff_quantified_formula": {"child": "FOF_QUANTIFIER"},
                          "fof_quantified_formula": {"child": "FOF_QUANTIFIER"},
                          "formula_data": {"child": ["DOLLAR_THF", "DOLLAR_TFF", "DOLLAR_FOF", "DOLLAR_CNF", "DOLLAR_FOT"]}}


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
        return cst_data in NODE_MODIFICATION_RULE and "parent" in NODE_MODIFICATION_RULE[cst_data] and cst_parent_data in NODE_MODIFICATION_RULE[cst_data]["parent"]

    def __satisfy_name_inherit_condition(self, cst_data):
        """__satisfy_name_inherit_condition

        NODE_MODIFICATION_RULEの作成するノード名の引継元があるかどうかをboolで返す関数
        NODE_MODIFICATION_RULEでparentが一致しているかどうかは関数外で確認する

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
        # すでに親ノードでトークンを付与しているなら抽象構文木に加えない(方針7)
        return self.__satisfy_name_inherit_condition(cst_parent_data) and cst.type in NODE_MODIFICATION_RULE[cst_parent_data]["child"]

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
            cst_data(str): 具象構文木のノードの名前
            cst_parent_data(str): 具象構文木の親のノード名

        Returns:
            (bool): 削除するならTrue、そうでないならFalse
        """
        # 全ての文法導出に対して「子が二つ以上ある」または「括弧で括られている」ものは残す(方針2,4)
        is_leave_unconditional = cst_data in NODE_MODIFICATION_RULE and not NODE_MODIFICATION_RULE[
            cst_data]
        # NODE_MODIFICATION_RULEに記載されていないノードは削除する(方針1)
        return not cst_data in NODE_MODIFICATION_RULE or (not self.__satisfy_parent_condition(cst_data, cst_parent_data) and not is_leave_unconditional)

    def __get_children_from_rule(self, cst_data):
        """__get_children_from_rule

        NODE_MODIFICATION_RULEから作成するノード名の引継元を取得し、setにして返す関数

        Args:
            cst_data(str): 具象構文木のノード名

        Returns:
            child_node_name_set(set): setにしたノード名の引継元
        """
        child_node_name_set = set()
        if self.__satisfy_name_inherit_condition(cst_data):
            children = NODE_MODIFICATION_RULE[cst_data]["child"]
            if type(children) != list:
                children = [children]
            child_node_name_set.update(children)
        return child_node_name_set

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
            child.type for child in cst.children if type(child) == Token]
        child_node_name_set = self.__get_children_from_rule(cst.data)
        # ファンクターや演算子等のトークンが子にあるならトークン情報を付与する(方針5,6,8)
        # NODE_MODIFICATION_RULE[cst.data]["child"]とcstの子のトークンに積集合があるかを調べることで
        # 子のトークンにNODE_MODIFICATION_RULE[cst.data]["child"]の要素があるかを調べている
        return self.__satisfy_name_inherit_condition(cst.data) and child_node_name_set.intersection(set(child_token))

    def __add_ast_node(self, ast_nodes, cst, ast_next_parent_id):
        """__add_ast_node

        抽象構文木のノードを追加する関数

        Args:
            ast_nodes (list):
                作成する抽象構文木のノードリスト
            cst (Tree or Token):
                抽象構文木に加える具象構文木のノード
            ast_next_parent_id (int):
                次作成する抽象構文木のノードID
        """
        if type(cst) == Tree:
            ast_nodes.append((str(ast_next_parent_id), {"label": cst.data}))
        else:
            ast_nodes.append(
                (str(ast_next_parent_id), {"label": cst.value + "," + cst.type}))
        return

    def __add_ast_edge(self, ast_edges, ast_parent_id, ast_next_parent_id):
        """__add_ast_edge

        抽象構文木のノードとエッジを追加する関数

        Args:
            ast_edges (list):
                作成する抽象構文木のエッジリスト
            ast_parent_id (int):
                抽象構文木の親ノードID
            ast_next_parent_id (int):
                次作成する抽象構文木のノードID
        """
        if ast_parent_id == None:
            return
        ast_edges.append([str(ast_parent_id), str(ast_next_parent_id)])
        return

    def __satisfy_child_token_inherit_condition(self, cst_data, cst_child):
        """__satisfy_child_token_inherit_condition

        具象構文木の子のトークンを上に上げて子のトークンを継承するかどうか判定する関数

        Args:
            cst_data (str): 具象構文木のノード名
            cst_child (Tree or Token): 具象構文木の子ノード

        Returns:
            (bool): 具象構文木の子のトークンを上に上げるならTrue、そうでないならFalse
        """
        return self.__satisfy_name_inherit_condition(cst_data) and type(cst_child) == Token and cst_child.type in NODE_MODIFICATION_RULE[cst_data]["child"]

    def convert_cst2ast(self, cst, cst_parent_data=None, ast_nodes=None, ast_edges=None, ast_parent_id=None):
        """convert_cst2ast

        具象構文木から抽象構文木を作成する関数

        Args:
            cst(Tree or Token): 具象構文木のノード
            cst_parent_data(str): 具象構文木の親のノード名
            ast_nodes(list): 抽象構文木のノード
            ast_edges(list): 抽象構文木のエッジ
            ast_parent_id(int): 抽象構文木の親ノードID
        Returns:
            ast_nodes(list): 抽象構文木のノード
            ast_edges(list): 抽象構文木のエッジ
        """
        if ast_nodes == None or ast_edges == None:
            ast_nodes = list()
            ast_edges = list()
        ast_next_parent_id = len(ast_nodes)
        # トークンの場合
        if type(cst) != Tree:
            if not self.__satisfy_token_remove_condition(cst, cst_parent_data):
                self.__add_ast_node(ast_nodes, cst, ast_next_parent_id)
                self.__add_ast_edge(
                    ast_edges, ast_parent_id, ast_next_parent_id)
            return ast_nodes, ast_edges

        # これ以降は内部ノード
        if self.__is_inherit_token_info(cst) or not self.__satisfy_node_remove_condition(cst.data, cst_parent_data):
            inherit_node = cst
            for child in cst.children:
                if self.__satisfy_child_token_inherit_condition(cst.data, child):
                    # 上に上げるトークンは一つしか存在しないため、見つけ次第breakする
                    inherit_node = child
                    break
            self.__add_ast_node(ast_nodes, inherit_node, ast_next_parent_id)
            self.__add_ast_edge(ast_edges, ast_parent_id, ast_next_parent_id)
        else:
            ast_next_parent_id = ast_parent_id
        for child in cst.children:
            self.convert_cst2ast(
                child, cst.data, ast_nodes, ast_edges, ast_next_parent_id)
        return ast_nodes, ast_edges

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

    def __find_label_by_node_id(self, nodes, node_id):
        """__find_label_by_node_id

        networkxで作成した有向グラフのjsonのnodesから
        ノードidと一致するノードのラベルを取得する関数

        Args:
            nodes(json): networkxで作成した有向グラフのjsonのndoes
                nodesのフォーマット
                    [
                        {
                            "label": ノードのラベル(str),
                            "id": ノードid(str)
                        },
                        {
                            "label": ノードのラベル(str),
                            "id": ノードid(str)
                        },...
                    ]
            node_id(str): ノードのid

        Returns: 
            label(str): ノードidと一致するノードのラベル
        """
        label = str()
        for node in nodes:
            if node["id"] == node_id:
                label = node["label"]
                # ノードidは重複しないためbreakする
                break
        return label

    def __find_target_by_source(self, links, source):
        """__find_target_by_source

        networkxで作成した有向グラフのjsonのlinksから
        sourceが一致するtargetを取得する関数

        Args:
            links(json): networkxで作成した有向グラフのjsonのlinks
            linksのフォーマット:
                [
                    {
                        "source": 始点のノードid(str),
                        "target": 終点のノードid(str)
                    },
                    {
                        "source": 始点のノードid(str),
                        "target": 終点のノードid(str)
                    },...
                ]
            source(str): 有向グラフの始点 

        Returns:
            targets(list): 有向グラフのエッジの中で入力の始点が一致する終点のリスト
        """
        targets = list()
        for link in links:
            if link["source"] == source:
                targets.append(link["target"])
        return targets

    def __get_assumption_formula_labels(self, nodes, links, annotations_id):
        """__get_assumption_formula_labels
        参照した式のラベルを返す関数

        Args:
            nodes(json): networkxで作成した有向グラフのjsonのndoes
            links(json): networkxで作成した有向グラフのjsonのlinks
            annotations_id(str): ノードのラベルがanntotationsのノードid

        Returns:
            assumption_formula_labels(list): 参照した式のラベルのリスト
        """
        assumption_formula_labels = list()
        annotations_children = self.__find_target_by_source(
            links, annotations_id)
        if not annotations_children:
            return assumption_formula_labels
        if not "inference" in self.__find_label_by_node_id(nodes, annotations_children[0]):
            return assumption_formula_labels
        inference_children = self.__find_target_by_source(
            links, annotations_children[0])
        if not inference_children:
            return assumption_formula_labels
        inference_parents = inference_children[-1]
        inference_parents_children = self.__find_target_by_source(
            links, inference_parents)
        for assumption_formula in inference_parents_children:
            # ラベルは"value, type"となっておりその内valueのみ取得する
            assumption_formula_label = self.__find_label_by_node_id(
                nodes, assumption_formula).split(",")[0]
            assumption_formula_labels.append(assumption_formula_label)

        return assumption_formula_labels

    def create_deduction_tree_graph_on_networkx(self, ast_path):
        """create_deduction_tree_graph_on_networkx

        抽象構文木から証明のグラフを作成する関数

        Args:
            ast_path(str): networkxで作成した抽象構文木のグラフ(json)のパス

        Returns:
            G(networkx.classes.digraph.DiGraph): エッジを追加したnetworkxのインスタンス
        """
        with open(ast_path, "r") as f:
            ast = json.load(f)
        ast_nodes = ast["nodes"]
        ast_links = ast["links"]
        graph_edges = list()
        ast_top_children = self.__find_target_by_source(
            ast_links, "0")

        for formula_top in ast_top_children:
            formula_top_children = self.__find_target_by_source(
                ast_links, formula_top)
            # ラベルは"value, type"となっておりその内valueのみ取得する
            formula_label = self.__find_label_by_node_id(
                ast_nodes, formula_top_children[0]).split(",")[0]
            annotations_id = formula_top_children[-1]
            assumption_formula_labels = self.__get_assumption_formula_labels(
                ast_nodes, ast_links, annotations_id)
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
        graph_nodes, graph_edges = self.convert_cst2ast(cst_root)
        ast_graph = self.create_tree_graph_on_networkx(
            graph_nodes, graph_edges)
        json_root = json_graph.node_link_data(ast_graph)
        with open(json_path, "w") as f:
            json.dump(json_root, f, indent=4)

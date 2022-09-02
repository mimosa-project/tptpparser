import json
from lark import Lark, Tree, Token
from networkx.readwrite import json_graph
from handler import NetworkxHandler

# 方針
# 1. 基本的に子が一つしかなく記号などを含んでいない場合は飛ばす
#   * NODE_KEEP_RULEのkeyにノード名があるかどうかで判定
# 2. 子が二つ以上あるものは基本的に残す
#   * NODE_KEEP_RULEのkeyにノード名があるがvalueにkeyがないかどうかで判定
#   * ：が使用されていて子が二つあるノードは別途関数で決め打ちし、子が二つ以上あるかどうかで判定
#       * 付与するトークン情報が無く、常に子が二つ以上とは限らないため、NODE_KEEP_RULEに含めれない
#       * 子が二つ以上かどうかで判定すると方針3のものまで含めてしまうため決め打ちしている
# 3. 子が二つ以上ある場合の内、ノードA : ノードB "," ノードAのように再帰が使用されているものは飛ばすそれ以外は残す
#   * NODE_KEEP_RULEのkeyにノード名があるかどうかで判定
#       * ただし、例外的に残す場合は記述している(方針9)
# 4. ノード名 : ノード名 |...| "(" ノード名 ")" or "[" ノード名 "]"が親ノードで子が"(" ノード名 ")" or "[" ノード名 "]"のときの子ノードは残す
#   * NODE_KEEP_RULEのkeyにノード名があり、value(map)のparent(key)のvalueと親ノード名が一致するかどうかで判定
# 5. thf_atom_typing : UNTYPED_ATOM ":" thf_top_level_type | "(" thf_atom_typing ")"のように文法のノード名と"(" ノード名 ")"のノード名が同じなら飛ばす
#   * NODE_KEEP_RULEのkeyにノード名があるかどうかで判定
# 6. ノード名 トークン(+など)or記号(@など) ノード名、記号"("ノード名...")"、 トークン"("ノード名...")"、 トークン ノード名...となっている場合はそのノードにトークン、記号の情報を付与する
#    このとき、付与したトークンは消す
#   * NODE_KEEP_RULEのkeyにノード名があり、value(map)のchild(key)のvalueと子のトークン名が一致するかどうかで判定
# 7. 親ノードにトークン情報が付与されていないトークンは残す
#   * 方針6のトークンでないかどうかで判定
# 8. tf1_quantified_type : "!>" "[" tff_variable_list "]" ":" tff_monotypeや、
#    tcf_quantified_formula : "!" "[" tff_variable_list "]" ":" cnf_formulaのように
#    文字列 or トークン"[" ノード名 "]" ":" ノード名となっている場合は、文字列、トークン情報を付与する
#    このとき、付与したトークンは消す
#   * NODE_KEEP_RULEのkeyにノード名があり、value(map)のchild(key)のvalueと子のトークン名が一致するかどうかで判定

# 具象構文木から抽象構文木を構築するときにノードを作成するルール
# key: 現在のノード（具象構文木）
# value: {"parent": 親ノードの名前、"child": 削除する子ノードの名前}
# 親ノードの名前(str or list): 親ノード名が文字列と等しければノードを作成する．Noneなら無条件で作成する。
# 親ノードの名前はリストになることもある
# 削除する子ノードの名前(str or list): 削除する子ノードの名前があるなら、子ノードの情報を付与する。
# 削除する子ノードの名前はリストになることもある
# parent, childが省略されているときはNoneとみなす
NODE_KEEP_RULE = {
    # with no condition (leave always)
    "annotations": {},
    "fof_formula_tuple": {},
    "formula_selection": {},
    "general_list": {},
    "optional_info": {},
    "tff_atom_typing": {},
    "tff_typed_variable": {},
    "tfx_tuple": {},
    "tfx_tuple_type": {},
    "tptp_root": {},
    "thf_atom_typing": {},
    "thf_quantified_formula": {},
    "thf_tuple": {},
    "thf_typed_variable": {},
    # with parent condition
    "cnf_formula": {"parent": "formula_data"},
    "fof_formula": {"parent": "formula_data"},
    "fof_logic_formula": {"parent": "fof_unitary_formula"},
    "fof_term": {"parent": "formula_data"},
    "fof_variable_list": {"parent": "fof_quantified_formula"},
    "tff_arguments": {"parent": "tfx_tuple"},
    "tff_atom_typing_list": {"parent": "tfx_let_types"},
    "tff_formula": {"parent": "formula_data"},
    "tff_logic_formula": {"parent": "tff_unitary_formula"},
    "tff_logic_formula": {"parent": ["tff_unitary_term", "tff_unitary_formula"]},
    "tff_type_list": {"parent": "tfx_tuple_type"},
    "tff_variable_list": {"parent": ["tff_quantified_formula", "tf1_quantified_type", "tcf_quantified_formula"]},
    "tfx_let_defn_list": {"parent": "tfx_let_defns"},
    "thf_formula": {"parent": "formula_data"},
    "thf_logic_formula": {"parent": "thf_unitary_formula"},
    "thf_variable_list": {"parent": "thf_quantification"},
    # with child condition
    "cnf_annotated": {"child": "CNF"},
    "disjunction": {"child": "VLINE"},
    "fof_and_formula": {"child": "AND_CONNECTIVE"},
    "fof_annotated": {"child": "FOF"},
    "fof_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"},
    "fof_defined_infix_formula": {"child": "DEFINED_INFIX_PRED"},
    "fof_defined_plain_term": {"child": "DEFINED_FUNCTOR"},
    "fof_infix_unary": {"child": "INFIX_INEQUALITY"},
    "fof_or_formula": {"child": "VLINE"},
    "fof_plain_term": {"child": "FUNCTOR"},
    "fof_quantified_formula": {"child": "FOF_QUANTIFIER"},
    "fof_sequent": {"child": "GENTZEN_ARROW"},
    "fof_system_term": {"child": "SYSTEM_FUNCTOR"},
    "fof_unary_formula": {"child": "UNARY_CONNECTIVE"},
    "formula_data": {"child": ["DOLLAR_THF", "DOLLAR_TFF", "DOLLAR_FOF", "DOLLAR_CNF", "DOLLAR_FOT"]},
    "general_function": {"child": "ATOMIC_WORD"},
    "include": {"child": "INCLUDE"},
    "literal": {"child": "UNARY_CONNECTIVE"},
    "tcf_annotated": {"child": "TCH"},
    "tcf_quantified_formula": {"child": "FOF_QUANTIFIER"},
    "tff_and_formula": {"child": "AND_CONNECTIVE"},
    "tff_annotated": {"child": "TFF"},
    "tff_atomic_type": {"child": "TYPE_FUNCTOR"},
    "tff_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"},
    "tff_defined_infix": {"child": "DEFINED_INFIX_PRED"},
    "tff_defined_plain": {"child": "DEFINED_FUNCTOR"},
    "tff_infix_unary": {"child": "INFIX_INEQUALITY"},
    "tfx_let_defn": {"child": "ASSIGNMENT"},
    "tff_or_formula": {"child": "VLINE"},
    "tff_plain_atomic": {"child": "FUNCTOR"},
    "tff_prefix_unary": {"child": "UNARY_CONNECTIVE"},
    "tff_quantified_formula": {"child": "FOF_QUANTIFIER"},
    "tff_subtype": {"child": "SUBTYPE_SIGN"},
    "tff_system_atomic": {"child": "SYSTEM_FUNCTOR"},
    "tfx_conditional": {"child": "DOLLAR_ITE"},
    "tfx_let": {"child": "DOLLAR_LET"},
    "tfx_sequent": {"child": "GENTZEN_ARROW"},
    "tf1_quantified_type": {"child": "TH1_QUANTIFIER"},
    "thf_and_formula": {"child": "AND_CONNECTIVE"},
    "thf_annotated": {"child": "THF"},
    "thf_apply_formula": {"child": "APPLY_SYMBOL"},
    "thf_binary_nonassoc": {"child": "NONASSOC_CONNECTIVE"},
    "thf_conditional": {"child": "DOLLAR_ITE"},
    "thf_defined_infix": {"child": "DEFINED_INFIX_PRED"},
    "thf_fof_function": {"child": ["FUNCTOR", "DEFINED_FUNCTOR", "SYSTEM_FUNCTOR"]},
    "thf_infix_unary": {"child": "INFIX_INEQUALITY"},
    "thf_let": {"child": "DOLLAR_LET"},
    "thf_let_defn": {"child": "ASSIGNMENT"},
    "thf_mapping_type": {"child": "ARROW"},
    "thf_or_formula": {"child": "VLINE"},
    "thf_prefix_unary": {"child": "UNARY_CONNECTIVE"},
    "thf_quantification": {"child": "THF_QUANTIFIER"},
    "thf_subtype": {"child": "SUBTYPE_SIGN"},
    "thf_sequent": {"child": "GENTZEN_ARROW"},
    "thf_union_type": {"child": "PLUS"},
    "thf_xprod_type": {"child": "STAR"},
    "tpi_annotated": {"child": "TPI"},
    # with both condition
    "tff_mapping_type": {"parent": "tff_monotype", "child": "ARROW"},
    "tff_xprod_type": {"parent": "tff_unitary_type", "child": "STAR"},
}


class ParseTstp():
    """Parse_Tstp

    tstpファイルをjson形式に保存するためのクラス

    Attributes:
        grammar_path (str): 使用するtptp文法ファイルのパス
    """

    def __init__(self, grammar_path):
        self.grammar_path = grammar_path
        
    def __satisfy_parent_condition(self, node_name, parent_node_name):
        """__satisfy_parent_condition

        NODE_KEEP_RULEの親ノードの条件を満たしているかどうかをboolで返す関数

        Args:
            node_name(str): 具象構文木のノード名
            parent_node_name(str): 具象構文木の親のノード名

        Returns:
            (bool): 親ノードの条件を満たしているならTrueそうでないならFalse
        """
        return (node_name in NODE_KEEP_RULE and
                "parent" in NODE_KEEP_RULE[node_name] and
                parent_node_name in NODE_KEEP_RULE[node_name]["parent"])

    def __is_exist_child_condition(self, node_name):
        """__is_exist_child_condition

        NODE_KEEP_RULEにchildが存在するかを確認する
        この条件を満たすchildノードが存在すると
        本ノードがchildノードの名前を引き継いだ後にchildノードは削除される
        NODE_KEEP_RULEでparentが一致しているかどうかは確認しない

        Args:
            node_name(str): 具象構文木のノード名

        Returns:
            (bool): 作成するノード名の引継元があるならTrueそうでないならFalse
        """

        return (node_name in NODE_KEEP_RULE and
                "child" in NODE_KEEP_RULE[node_name])

    def __satisfy_token_remove_condition(self, token_name, parent_node_name):
        """__satisfy_token_remove_condition

        このトークンド(token_nameで指定)を削除するかどうかを判定する関数
            * 親のノードでトークン情報を付与している場合
                具体例
                    thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula

        Args:
            token_name (Token): 具象構文木のノード名
            parent_node_name (str): 具象構文木の親ノードの名前

        Returns:
            (bool): 削除するならTrue、そうでないならFalse
        """
        # すでに親ノードでトークンを付与しているなら抽象構文木に加えない(方針7)
        return (self.__is_exist_child_condition(parent_node_name) and
                token_name in NODE_KEEP_RULE[parent_node_name]["child"])

    def __satisfy_node_keep_condition(self, node, parent_node_name):
        """__satisfy_node_keep_condition

        このノード(node_nameで指定)を残すかどうかを判定する関数
            以下のいずれかの場合
                * 全ての文法導出に対して「子が二つ以上ある」または「括弧で括られている」
                    具体例
                        thf_quantified_formula : thf_quantification thf_unit_formula
                        thf_tuple            : "[]" | "[" thf_formula_list "]"
                * ある文法導出に対して「括弧で括られている」
                    具体例
                        tff_monotype         : tff_atomic_type | "(" tff_mapping_type ")" | tf1_quantified_type

        Args:
            node(Tree): 具象構文木のノード名
            parent_node_name(str): 具象構文木の親のノード名

        Returns:
            (bool): 残すならTrue、そうでないならFalse
        """

        assert type(node) == Tree
        node_name = node.data

        # 1.NODE_KEEP_RULEにノード名があり，条件が書かれていない場合
        keep_condition1 = (node_name in NODE_KEEP_RULE and
                           not NODE_KEEP_RULE[node_name])

        # 2.NODE_KEEP_RULEにノード名があり，親ノード名も条件を満たす場合
        keep_condition2 = self.__satisfy_parent_condition(
            node_name, parent_node_name)

        # 3.NODE_KEEP_RULEにノード名があり，子ノード名も条件を満たす場合
        # この場合，子トークンから情報を引き継ぐ
        keep_condition3 = self.__is_inherit_child_token_info(node)

        return keep_condition1 or keep_condition2 or keep_condition3

    def __get_children_from_rule(self, node_name):
        """__get_children_from_rule

        NODE_KEEP_RULEからchildリストを取得し、setにして返す関数

        Args:
            node_name(str): 具象構文木のノード名

        Returns:
            (set) : setにしたchildノード名
        """
        children = []
        if self.__is_exist_child_condition(node_name):
            children = NODE_KEEP_RULE[node_name]["child"]
            if type(children) != list:
                children = [children]
        return set(children)

    def __is_inherit_child_token_info(self, node):
        """__is_inherit_child_token_info

        子トークンから情報を引き継ぐかどうかをboolで返す関数
        子トークンからは名前と型の情報を引き継ぐ．
        具体例
            thf_binary_nonassoc  : thf_unit_formula NONASSOC_CONNECTIVE thf_unit_formula

        Args:
            node(Tree): 具象構文木のノード

        Returns:
            (bool): トークン情報を付与するならTrueそうでないならFalse
        """
        child_token_names = set([child.type for child in node.children
                                 if type(child) == Token])
        child_names_in_rule = self.__get_children_from_rule(node.data)
        # ファンクターや演算子等のトークンが子にあるならトークン情報を付与する(方針5,6,8)
        # NODE_KEEP_RULE[node.data]["child"]とcstの子のトークンに積集合があるかを調べることで
        # 子のトークンにNODE_KEEP_RULE[node.data]["child"]の要素があるかを調べている
        return bool(child_names_in_rule.intersection(child_token_names))

    def __add_ast_child_node(self, cst, ast_parent_id, ast_handler):
        """__add_ast_child_node

        抽象構文木のノードを追加する関数

        Args:
            cst (Tree or Token):
                追加するノードに対応する具象構文木のノード
            ast_parent_id (int):
                抽象構文木の親ノードID
            ast_handler (NetworkxHandler):
                抽象構文木のグラフを管理するインスタンス
        """
        ast_id = ast_handler.get_next_node()
        if type(cst) == Tree:
            label = cst.data
            ast_handler.add_node(label)
        else:
            label = cst.value
            grammatical_category = cst.type
            ast_handler.add_node(label, grammatical_category=grammatical_category)
        if ast_parent_id is not None:
            ast_handler.add_edge(ast_parent_id, ast_id)

    def __satisfy_child_token_inherit_condition(self, node_name, child_node):
        """__satisfy_child_token_inherit_condition

        具象構文木の子のトークンを上に上げて子のトークンを継承するかどうか判定する関数

        Args:
            node_name (str): 具象構文木のノード名
            child_node (Tree or Token): 具象構文木の子ノード

        Returns:
            (bool): 具象構文木の子のトークンを上に上げるならTrue、そうでないならFalse
        """
        if type(child_node) == Token:
            child_token_name = child_node.type
            return self.__satisfy_token_remove_condition(child_token_name, node_name)
        else:
            return False

    def convert_cst2ast(self,
                        cst,
                        cst_parent_name=None,
                        ast_parent_id=None,
                        ast_handler=None):
        """convert_cst2ast

        具象構文木から抽象構文木を作成する関数

        Args:
            cst(Tree or Token): 具象構文木のノード
            cst_parent_name(str): 具象構文木の親のノード名
            ast_parent_id(int): 抽象構文木の親ノードID
            ast_handler (NetworkxHandler):
                抽象構文木のグラフを管理するインスタンス
        Returns:
            ast_handler (NetworkxHandler):
                抽象構文木作成後の
                抽象構文木のグラフを管理するインスタンス
        """
        if ast_handler is None:
            ast_handler = NetworkxHandler()

        if type(cst) == Token:
            # トークンの場合
            token_name = cst.type
            if not self.__satisfy_token_remove_condition(token_name, cst_parent_name):
                self.__add_ast_child_node(
                    cst, ast_parent_id, ast_handler)
        else:
            # 内部ノードの場合
            assert type(cst) == Tree

            cst_name = cst.data
            ast_next_parent_id = ast_parent_id
            if self.__satisfy_node_keep_condition(cst, cst_parent_name):
                inherit_node = cst
                if self.__is_exist_child_condition(cst_name):
                    for child in cst.children:
                        if self.__satisfy_child_token_inherit_condition(cst_name, child):
                            # 上に上げるトークンは一つしか存在しないため、見つけ次第breakする
                            inherit_node = child
                            break
                self.__add_ast_child_node(
                    inherit_node, ast_parent_id, ast_handler)
                ast_next_parent_id = ast_handler.get_last_node()

            for child in cst.children:
                self.convert_cst2ast(
                    child, cst_name, ast_next_parent_id, ast_handler)

        return ast_handler

    def parse_tstp(self, tstp):
        """parse_tstp

        入力されたtstpファイルを読み込んだ文字列をtptpの文法で構文解析することで構文木を作成し、それを返す関数

        Args:
            tstp (str): tstpファイルを読み込んだ文字列

        Returns:
            cst_root (Tree): tptpの文法で構文解析した構文木
        """
        with open(self.grammar_path, encoding="utf-8") as grammar:
            parser = Lark(grammar.read(), start="tptp_root")
            cst_root = parser.parse(tstp)

        return cst_root

    def get_inference_children(self, annotations_id, ast_handler):
        """get_inference_children
        
        inferenceノードの子ノードを取得する関数

        Args:
            annotations_id(str): ノードのラベルがanntotationsのノードid
            ast_handler (NetworkxHandler): 抽象構文木のハンドラ

        Returns:
            inference_children (list): inferenceノードの子ノードのリスト
        """
        annotations_children = ast_handler.get_children(annotations_id)
        if not annotations_children:
            return []

        inference = annotations_children[0]
        if not "inference" in ast_handler.get_label(inference):
            return []

        inference_children = ast_handler.get_children(inference)
        if not inference_children:
            return []
        
        return inference_children

    def __get_inference_rule(self, annotations_id, ast_handler):
        """__get_inference_rule

        式を導出するための操作名を取得する関数

        Args:
            annotations_id(int): ノードのラベルがanntotationsのノードid
            ast_handler (NetworkxHandler): 抽象構文木グラフのハンドラ

        Returns:
            inference_rule (str): 式を導出するための操作名
        """
        inference_children = self.get_inference_children(annotations_id, ast_handler)
        if not inference_children:
            return None
        inference_rule_node = inference_children[0]
        inference_rule = ast_handler.get_label(inference_rule_node)
        return inference_rule

    def __get_assumption_formulas(self, annotations_id, ast_handler):
        """__get_assumption_formulas

        参照した式を取得する関数

        Args:
            annotations_id(str): ノードのラベルがanntotationsのノードid
            ast_handler (NetworkxHandler): 抽象構文木グラフのハンドラ

        Returns:
            assumption_formulas(list): 参照した式のノードのリスト
        """
        inference_children = self.get_inference_children(annotations_id, ast_handler)
        if not inference_children:
            return []
        assumption_list = inference_children[-1]
        assumption_formulas = ast_handler.get_children(assumption_list)

        return assumption_formulas

    def create_deduction_tree_graph_on_networkx(self, ast_path):
        """create_deduction_tree_graph_on_networkx

        抽象構文木から証明のグラフを作成する関数

        Args:
            ast_path(str): networkxで作成した抽象構文木のグラフ(json)のパス

        Returns:
            graph(networkx.classes.digraph.DiGraph): 証明のグラフのnetworkxのインスタンス
        """
        ast_handler = NetworkxHandler()
        ast_handler.load_json(ast_path)
        deduction_handler = NetworkxHandler()
        deduction_tree_edges = []
        fof_list = ast_handler.get_children(0)
        for fof in fof_list:
            fof_children = ast_handler.get_children(fof)
            formula_name_node = fof_children[0]
            annotations_node = fof_children[-1]
            formula_name = ast_handler.get_label(formula_name_node)
            inference_rule = self.__get_inference_rule(annotations_node, ast_handler)
            deduction_handler.add_node(formula_name, inference_rule=inference_rule)
            assumption_formulas = self.__get_assumption_formulas(
                annotations_node, ast_handler)
            for assumption_formula in assumption_formulas:
                assumption_formula_label = ast_handler.get_label(assumption_formula)
                deduction_tree_edges.append(
                    (assumption_formula_label, formula_name))
        for source_label, target_label in deduction_tree_edges:
            source = deduction_handler.get_node(source_label)
            target = deduction_handler.get_node(target_label)
            deduction_handler.add_edge(source, target)
        graph = deduction_handler.get_graph()
        return graph

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
        ast_handler = self.convert_cst2ast(cst_root)
        ast_graph = ast_handler.get_graph()
        json_root = json_graph.node_link_data(ast_graph)
        with open(json_path, "w") as f:
            json.dump(json_root, f, indent=4)

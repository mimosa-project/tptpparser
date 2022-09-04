import json
import os
import networkx
from networkx.readwrite import json_graph
from handler import NetworkxHandler


class DeductionTree:
    def __init__(self, path):
        self.nx = NetworkxHandler()
        self.nx.load_json(path)

    def collect_cnf_nodes_recursively(self, node, cnf_nodes, is_cnf=False):
        targets = self.nx.get_children(node)
        for target in targets:
            inference_rule = self.nx.get_attr(target, "inference_rule")
            is_already_added = False
            if is_cnf or inference_rule == "cnf_transformation":
                is_cnf = True
                if target in cnf_nodes:
                    is_already_added = True
                cnf_nodes.add(target)
            if not is_already_added:
                self.collect_cnf_nodes_recursively(
                    target, cnf_nodes, is_cnf)

    def collect_cnf_nodes(self):
        orphan_nodes = self.nx.get_orphans()
        cnf_nodes = set()
        for node in orphan_nodes:
            self.collect_cnf_nodes_recursively(node, cnf_nodes)
        return cnf_nodes


class FofTree:
    def __init__(self, path):
        self.nx = NetworkxHandler()
        self.nx.load_json(path)

    def get_formula_root(self, fof_name):
        node = self.nx.get_node(fof_name)
        theorem_root = self.nx.get_parents(node)[0]
        formula_root = self.nx.get_children(theorem_root)[2]
        return formula_root


class Converter():
    def __init__(self, fof_json_path, deduction_tree_json_path):
        self.fof_tree = FofTree(fof_json_path)
        self.deduction_tree = DeductionTree(deduction_tree_json_path)

    def save_normalized_formula(self, dir_path):
        nodes = self.deduction_tree.collect_cnf_nodes()
        for node in nodes:
            formula_root = self.fof_tree.get_formula_root(node)
            graph = self.normalize_formula(formula_root)
            json_root = json_graph.node_link_data(graph)
            fof_name = self.fof_tree.nx.get_label(node)
            with open(os.path.join(dir_path, fof_name+".json"), "w") as f:
                json.dump(json_root, f, indent=4)

    def normalize_formula(self, formula_root):
        output_graph = networkx.DiGraph()
        output_nx = NetworkxHandler(output_graph)
        self.remove_redundant_nodes(output_nx, formula_root)
        self.arrange_conjuction(output_nx)
        self.arrange_disjunction(output_nx)
        self.merge_negation(output_nx)
        return output_nx.get_graph()

    def remove_redundant_nodes(self, output_nx, node, parent_node=None):
        # 以下のノードを削除する
        # 1.Quantifier情報が入っているノード
        # 2.トークン情報が入っていないノード
        label = self.fof_tree.nx.get_label(node)
        if self.is_reserve_node(label):
            reserve_node = output_nx.get_next_node()
            output_nx.add_node(label)
            if parent_node is not None:
                output_nx.add_edge(parent_node, reserve_node)
        for child in self.fof_tree.nx.get_children(node):
            last_node = output_nx.get_last_node()
            if "!" in label:
                # 全称量化子の場合は右の子ノードのみを残す
                second_child = self.fof_tree.nx.get_children(node)[1]
                self.remove_redundant_nodes(
                    output_nx, second_child, last_node)
                break
            else:
                self.remove_redundant_nodes(output_nx, child, last_node)

    def is_reserve_node(self, label):
        return "," in label and not "!" in label

    def arrange_conjuction(self, output_nx):
        root = output_nx.get_orphans()[0]
        # Rootが & ではない
        if not "&" in output_nx.get_label(root):
            # Rootに & を追加する
            node = output_nx.get_next_node()
            output_nx.add_node("&")
            output_nx.add_edge(node, root)

        else:
            # dfsで探索し、& が再帰されて使用されている場合は統合する
            def merge_conjunction_recursively(node):
                for child in output_nx.get_children(node):
                    label = output_nx.get_label(child)
                    if label == "&":
                        grand_children = output_nx.get_children(child)
                        for grand_child in grand_children:
                            output_nx.add_edge(root, grand_child)
                            output_nx.remove_node(child)
                            merge_conjunction_recursively(grand_child)
            merge_conjunction_recursively(root)

    def arrange_disjunction(self, output_nx):
        conjuction_node = output_nx.get_orphans()[0]
        for child in output_nx.get_children(conjuction_node):
            # & の子が | ではない
            if not "|" in output_nx.get_label(child):
                # &の子に|を追加
                next_node = output_nx.get_next_node()
                output_nx.add_node("|")
                output_nx.add_edge(conjuction_node, next_node)
                output_nx.add_edge(next_node, child)
            else:
                # dfsで探索し、| が再帰されて使用されている場合は統合する
                def merge_disjunction_recursively(node):
                    for child in output_nx.get_children(node):
                        label = output_nx.get_label(child)
                        if label == "|":
                            grand_children = output_nx.get_children(child)
                            for grand_child in grand_children:
                                output_nx.add_edge(node, grand_child)
                                output_nx.remove_edge(child, grand_child)
                                output_nx.remove_node(node)
                                merge_disjunction_recursively(child)
                merge_disjunction_recursively(child)

    def merge_negation(self, output_nx, node=None):
        # dfsで探索していき、notのノードがあれば子にnotを付与し、notノードを削除する
        if node is None:
            node = output_nx.get_orphans()[0]
        for child in output_nx.get_children(node):
            label = output_nx.get_label(node)
            if label == "~":
                output_nx.remove_node(node)
                parent = output_nx.get_parents(node)[0]
                output_nx.add_edge(parent, child)
                output_nx.set_label(child, "~" + output_nx.get_label(child))
            self.merge_negation(child)

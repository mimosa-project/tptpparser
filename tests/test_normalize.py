import sys
import os
import json
import pickle
import pytest
from networkx.readwrite import json_graph
sys.path.append(os.pardir)
from normalize import DeductionTree, FofTree, Converter  # nopep8
from handler import NetworkxHandler  # nopep8


class TestDeductionTree:
    @pytest.fixture
    def get_default_tree(self):
        deduction_tree_json_path = os.path.join("data", "deduction_tree.json")
        deduction_tree = DeductionTree(deduction_tree_json_path)
        return deduction_tree

    def test_collect_cnf_nodes(self, get_default_tree):
        deduction_tree = get_default_tree
        cnf_nodes = deduction_tree.collect_cnf_nodes()
        expected_cnf_nodes_path = os.path.join("expected", "cnf_nodes.pkl")
        with open(expected_cnf_nodes_path, "rb") as f:
            expected_cnf_nodes = pickle.load(f)
        assert cnf_nodes == expected_cnf_nodes


class TestFofTree:
    @pytest.fixture
    def get_fof_tree(self):
        fof_tree_json_path = os.path.join("data", "fof_tree.json")
        fof_tree = FofTree(fof_tree_json_path)
        return fof_tree

    def test_get_formula_root(self, get_fof_tree):
        fof_tree = get_fof_tree
        fof_names_path = os.path.join("data", "fof_names.json")
        with open(fof_names_path, "r") as f:
            fof_names = json.load(f)
        name2formula_root = dict()
        for fof_name in fof_names:
            name2formula_root[fof_name] = fof_tree.get_formula_root(fof_name)
        expected_name2formula_root_path = os.path.join(
            "expected", "name2formula_root.json")
        with open(expected_name2formula_root_path, "r") as f:
            expected_name2formula_root = json.load(f)
        assert name2formula_root == expected_name2formula_root


class TestConverter:
    @pytest.fixture
    def get_converter(self):
        fof_json_path = os.path.join("data", "fof_tree.json")
        deduction_tree_json_path = os.path.join("data", "deduction_tree.json")
        converter = Converter(fof_json_path, deduction_tree_json_path)
        return converter

    def test_remove_redundant_nodes(self, get_converter):
        converter = get_converter
        input_path = os.path.join(
            "data", "remove_redundant_nodes", "fof_name2formula_root.json")
        with open(input_path, "r") as f:
            fof_name2formula_root = json.load(f)
        for fof_name in fof_name2formula_root:
            formula_root = fof_name2formula_root[fof_name]
            output_nx = NetworkxHandler()
            converter.remove_redundant_nodes(output_nx, formula_root)
            graph = output_nx.get_graph()
            json_root = json_graph.node_link_data(graph)
            expected_json_path = os.path.join(
                "expected", "remove_redundant_nodes", f"{fof_name}.json")
            with open(expected_json_path, "r") as f:
                expected_json = json.load(f)
            assert json_root == expected_json

    def test_arrange_conjuction(self, get_converter):
        converter = get_converter
        input_dir = os.path.join("data", "arrange_conjunction")
        input_files = os.listdir(input_dir)
        for file_name in input_files:
            fof_name = file_name.split(".")[0]
            output_nx = NetworkxHandler()
            output_nx.load_json(os.path.join(input_dir, file_name))
            converter.arrange_conjuction(output_nx)
            graph = output_nx.get_graph()
            json_root = json_graph.node_link_data(graph)
            expected_json_path = os.path.join(
                "expected", "arrange_conjunction", f"{fof_name}.json")
            with open(expected_json_path, "r") as f:
                expected_json = json.load(f)
            assert json_root == expected_json

    def test_arrange_disjunction(self, get_converter):
        converter = get_converter
        input_dir = os.path.join("data", "arrange_disjunction")
        input_files = os.listdir(input_dir)
        for file_name in input_files:
            fof_name = file_name.split(".")[0]
            output_nx = NetworkxHandler()
            output_nx.load_json(os.path.join(input_dir, file_name))
            converter.arrange_disjunction(output_nx)
            graph = output_nx.get_graph()
            json_root = json_graph.node_link_data(graph)
            expected_json_path = os.path.join(
                "expected", "arrange_disjunction", f"{fof_name}.json")
            with open(expected_json_path, "r") as f:
                expected_json = json.load(f)
            assert json_root == expected_json

    def test_coordinate_node(self, get_converter):
        converter = get_converter
        input_dir = os.path.join("data", "coordinate_node")
        input_files = os.listdir(input_dir)
        for file_name in input_files:
            fof_name = file_name.split(".")[0]
            output_nx = NetworkxHandler()
            output_nx.load_json(os.path.join(input_dir, file_name))
            converter.coordinate_node(output_nx)
            graph = output_nx.get_graph()
            json_root = json_graph.node_link_data(graph)
            expected_json_path = os.path.join(
                "expected", "coordinate_node", f"{fof_name}.json")
            with open(expected_json_path, "r") as f:
                expected_json = json.load(f)
            assert json_root == expected_json

    def test_merge_negation(self, get_converter):
        converter = get_converter
        input_dir = os.path.join("data", "merge_negation")
        input_files = os.listdir(input_dir)
        for file_name in input_files:
            fof_name = file_name.split(".")[0]
            output_nx = NetworkxHandler()
            output_nx.load_json(os.path.join(input_dir, file_name))
            converter.merge_negation(output_nx)
            graph = output_nx.get_graph()
            json_root = json_graph.node_link_data(graph)
            expected_json_path = os.path.join(
                "expected", "merge_negation", f"{fof_name}.json")
            with open(expected_json_path, "r") as f:
                expected_json = json.load(f)
            assert json_root == expected_json

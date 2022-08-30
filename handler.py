from collections import defaultdict
import json
import networkx as nx
import graphviz
from networkx.readwrite import json_graph


class GraphvizHandler:
    """GraohvizHandler

    graphvizグラフを操作する関数をまとめたクラス
    """
    def __init__(self):
        pass

    def create_tree_graph(self, graph_nodes, graph_edges):
        """create_tree_graph

        graphvizのインスタンスにノードとエッジを追加し、graphvizのインスタンスを返す関数

        Args:
            graph_nodes (list): グラフに追加するノードのリスト
            graph_edges (list): グラフに追加するエッジのリスト
        Returns:
            G(graphviz.graphs.Digraph): ノードとエッジを追加したgraphvizのインスタンス
        """
        G = graphviz.Digraph()
        for node_id, attr in graph_nodes:
            G.node(str(node_id), attr["label"])
        G.edges(graph_edges)
        return G

    def show_tree_graph(self, G, path):
        """show_tree_graph

        graphvizのインスタンスからグラフを描画し、引数のpathに保存する関数

        Args:
            G (graphviz.graphs.Digraph): ノードとエッジを追加したgraphvizのインスタンス
            path (str): グラフを保存するパス
        """
        G.render(path, format="png")


class NetworkxHandler:
    """NetworkxHandler

    networkxグラフを操作する関数をまとめたクラス
    """
    def __init__(self):
        self.graph = nx.DiGraph()
        self.source2targets = defaultdict(list)
        self.target2sources = defaultdict(list)
        self.node2label = dict()
        self.label2node = dict()
        self.node2attr = dict()

    def load_json(self, path):
        """load_json

        networkxグラフのjsonファイルを読み込み、初期化する関数

        Args:
            path (str): networkxグラフのjsonファイルのパス
        """
        with open(path) as f:
            loaded_json = json.load(f)
        graph = json_graph.node_link_graph(loaded_json)
        self.init_graph(graph)

    def init_graph(self, graph):
        """init_graph

        selfの変数を引数のグラフで初期化する関数

        Args:
            graph (networkx.classes.digraph.DiGraph): networkxグラフ
        """
        self.graph = graph

        for source, target in self.get_graph_edges():
            self.source2targets[source].append(target)
            self.target2sources[target].append(source)

        for node, attr in self.get_graph_nodes():
            label = attr["label"]
            self.node2label[node] = label
            self.label2node[label] = node
            self.node2attr[node] = attr

    def get_graph_nodes(self):
        """get_graph_nodes

        アトリビュートを含めたnetworkxグラフのノードを取得する関数

        Returns:
            (networkx.classes.reportviews.NodeDataView): ノード情報のリスト
            例: [
                    (0, {'label': 'a', 'attr': None}), 
                    (1, {'label': 'b', 'attr': None}),
                    ...
                ]
        """
        return self.graph.nodes(data=True)

    def get_graph_edges(self):
        """get_graph_edges
        
        networkxグラフのエッジを取得する関数(アトリビュートを含まない)

        Returns:
            (networkx.classes.reportviews.OutEdgeView): エッジ情報のリスト
            例: [
                    (0, 1),
                    ...
                ]
        """
        return self.graph.edges()

    def get_parents(self, node):
        """get_parents

        ノードの親を取得する関数

        Args:
            node (int): ノードID

        Returns:
            (list): ノードの親のリスト
        """
        return self.target2sources[node]

    def get_children(self, node):
        """get_children

        ノードの子を取得する関数

        Args:
            node (int): ノードID

        Returns:
            (list): ノードの子のリスト
        """
        return self.source2targets[node]

    def get_ascendants(self, node):
        """get_ascendants
        
        ノードの祖先全てを取得する関数

        Args:
            node (int): ノードID
        
        Returns:
            (list): ノードの祖先のリスト
        """
        ascendants = set()

        def collect_ascendants(curent_node):
            if curent_node in ascendants:
                return
            ascendants.add(curent_node)
            for parent in self.get_parents(curent_node):
                collect_ascendants(parent)
        collect_ascendants(node)
        return ascendants

    def get_descendants(self, node):
        """get_descendants
        
        ノードの子孫全てを取得する関数

        Args:
            node (int): ノードID
        
        Returns:
            (list): ノードの子孫のリスト
        """
        decendants = set()

        def collect_descendants(current_node):
            if current_node in decendants:
                return
            decendants.add(current_node)
            for child in self.get_children(current_node):
                collect_descendants(child)
        collect_descendants(node)
        return decendants

    def get_orphans(self):
        """get_orphans
        
        親ノードがないノードを取得する関数

        Returns:
            (list): 親ノードがないノードのリスト
        """
        orphans = set()
        for node, _ in self.get_graph_nodes():
            if node in self.target2sources:
                orphans.add(node)
        return orphans

    def get_label(self, node):
        """get_label
        
        ノードのラベルを取得する関数

        Args:
            node (int): ノードID

        Returns:
            (str): ノードのラベル
        """
        return self.node2label[node]

    def set_label(self, node, label):
        """set_label
        
        ノードのラベルを設定する関数

        Args:
            node (int): ノードID
            label (str): 設定するラベル
        """
        previous_label = self.get_label(node)
        self.node2label[node] = label
        del self.label2node[previous_label]
        self.label2node[label] = node
        self.node2attr[node]["label"] = label
        self.graph[node]["label"] = label

    def get_node(self, label):
        """get_node
        
        ラベルからノードを取得する関数

        Args:
            label (str): ラベル

        Returns:
            (int): ノードID
        """
        return self.label2node[label]

    def get_attr(self, node, attr_key):
        """get_attr

        ノードのアトリビュートを取得する関数

        Args:
            node (int): ノードID
            attr_key (str): アトリビュートの種類

        Returns:
            (str): ノードのアトリビュート
        """
        return self.node2attr[node][attr_key]

    def get_all_nodes(self):
        """get_all_nodes

        ノードのリストを取得する関数

        Returns:
            (list): ノードのリスト
        """
        return [node for node, _ in self.get_graph_nodes()]

    def get_all_edges(self):
        """get_all_edges

        エッジのリストを取得する関数

        Returns:
            (list): エッジのリスト
        """
        return self.get_graph_edges()

    def get_next_node(self):
        """get_next_node

        次のノードIDを取得する関数

        Returns:
            (int): 次のノードID
        """
        return len(self.get_graph_nodes())

    def get_last_node(self):
        """get_last_node

        最後のノードIDを取得する関数

        Returns:
            (int): 最後のノードID
        """
        return len(self.get_graph_nodes()) - 1

    def get_graph(self):
        """get_graph

        networkxグラフを取得する関数

        Returns:
            (networkx.classes.graph.Graph): networkxグラフ
        """
        return self.graph

    def add_node(self, label, **attr):
        """add_node

        ノードを追加する関数

        Args:
            label (str): 追加するノードのラベル
            attr (dict): 追加するノードのアトリビュート
                例: {"inference_rule": "cnf_transformation"}

        Returns:
            (int): 追加したノードのID
        """
        new_node = self.get_next_node()
        self.node2label[new_node] = label
        self.label2node[label] = new_node
        self.graph.add_node(new_node, label=label, **attr)
        return new_node

    def add_edge(self, source, target):
        """add_edge

        エッジを追加する関数

        Args:
            source (int): エッジの始点ノードID
            target (int): エッジの終点ノードID
        """
        self.source2targets[source].append(target)
        self.target2sources[target].append(source)
        self.graph.add_edge(source, target)

    def add_child(self, parent, label, attr=None):
        """add_child
        
        子ノードを追加する関数

        Args:
            parent (int): 追加する子ノードの親ノードID
            label (str): 追加する子ノードのラベル
            attr (str): 追加する子ノードのアトリビュート
        """
        new_node = self.add_node(label, attr)
        self.add_edge(parent, new_node)

    def remove_node(self, node):
        """remove_node

        ノードを削除する関数

        Args:
            node (int): 削除するノードID
        """
        del self.label2node[self.node2label[node]]
        del self.node2label[node]
        if node in self.source2targets:
            del self.source2targets[node]
        if node in self.target2sources:
            del self.target2sources[node]
        self.graph.remove_node(node)

    def remove_edge(self, source, target):
        """remove_edge

        エッジを削除する関数

        Args:
            source (int): 削除するエッジの始点ノードID
            target (int): 削除するエッジの終点ノードID
        """
        self.source2targets[source].remove(target)
        self.target2sources[target].remove(source)
        self.graph.remove_edge(source, target)

    def show_tree_graph(self, path):
        """show_tree_graph

        networkxのインスタンスからグラフを描画し、引数のpathに保存する関数

        Args:
            path (str): グラフを保存するパス
        """
        agraph = nx.nx_agraph.to_agraph(self.graph)
        agraph.draw(path, prog="dot", format="png")

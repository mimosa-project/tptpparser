import subprocess


class VampireExecutor:
    """VampireExecutor
    
    vampireを実行して、その結果からtstpファイルを作成するクラス

    Attributes:
        vampire_path (str): vampireの実行ファイルのパス
    """
    def __init__(self, vampire_path):
        self.vampire_path = vampire_path

    def run(self, problem_path, tstp_path):
        """run

        vampireを実行し、その結果からtstpファイルを作成する関数
        
        Args:
            problem_path (str): 自動定理証明するproblemファイルのパス
            tstp_path (str): 保存するtstpファイルのパス
        """
        result = subprocess.run(
            ("./" + self.vampire_path, "-p", "tptp", problem_path), encoding="utf-8", stdout=subprocess.PIPE)
        result_list = result.stdout.splitlines()
        output = "\n".join(result_list[1:])

        with open(tstp_path, "w") as f:
            f.write(output)

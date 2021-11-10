import subprocess


class VampireExecutor:
    def __init__(self, vampire_path):
        self.vampire_path = vampire_path

    def run(self, problem_path, tstp_path):
        """run
        vampireの実行結果を返す関数
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

import subprocess


class Tstp:
    def __init__(self, vampire, input_file, tstp_file):
        self.vampire = vampire
        self.input_file = input_file
        self.tstp_file = tstp_file

    def run_vampire(self):
        """run_vampire
        vampireの実行結果を返す関数
        """
        result = subprocess.run(
            ("./" + self.vampire, "-p", "tptp", self.input_file), encoding="utf-8", stdout=subprocess.PIPE)
        result_list = result.stdout.splitlines()
        output = ""
        for s in result_list[1:]:
            if not s:
                continue
            if s[0] != "%":
                output += s.replace(" ", "")
        return output

    def save_tstp_from_result_of_vampire(self):
        """save_tstp_from_result_of_vampire
        vampireの実行結果からtstpファイルを保存する関数
        """
        with open(f"{self.tstp_file}.tstp", "w") as f:
            f.write(self.run_vampire())

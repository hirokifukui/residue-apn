# m = 13 の独立照合（R05b、Claude）
- gen.py：調査用エージェントのコード（sym.py、brute.c）を使わずに、p_d = (Tr(x) + d x^{2^{m−2}})³ を GF(2^13)（法 t^13+t^4+t^3+t+1）上で DO 指数と線形指数での補間から作る。d は Tr d = Tr d^{−1} = 0 を満たす最小の整数表現（d = 6）。
- 出力：p13_d6.txt（36 項）。
- `python3 -I inv.py 13 p13_d6.txt` の結果は inv_p13_d6.json：ρ = 2627（= d^{−4}）、μ = 0、Z = []。Theorem repfamily と一致する。実行時間は約 4 分（container）。

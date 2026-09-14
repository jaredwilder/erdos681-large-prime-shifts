import numpy as np, json, hashlib, math, random
K = 999; z = K * K + 1; H = K - K // 2
s = np.ones(z + 1, bool); s[:2] = False
for i in range(2, int(z ** .5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0]; P = P[P < z]
random.seed(1399)
cnt = []
for _ in range(3000):
    lo = random.randrange(10 ** 12, 2 * 10 ** 12)
    rough = np.ones(H, bool)
    st = (-lo) % P
    m = st < H
    for q, a in zip(P[m].tolist(), st[m].tolist()):
        rough[a::q] = False
    cnt.append(int(rough.sum()))
c = np.array(cnt, float)
R = math.exp(-0.5772156649) * H / math.log(z)
out = {"K": K, "H": H, "z": z, "samples": 3000, "seed": 1399, "R_formula": R, "mean": c.mean(), "var": c.var(), "var_over_mean": c.var() / c.mean()}
t = json.dumps(out); open("gt_var.json", "w").write(t); print(t); print("HASH", hashlib.sha256(t.encode()).hexdigest())

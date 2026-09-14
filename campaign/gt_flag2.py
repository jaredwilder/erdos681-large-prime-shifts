import numpy as np, json, hashlib
exec(open("gt_var.py").read().split("random.seed")[0])
lo = 10 ** 12; L = 2_000_000
rough = np.ones(L, bool); st = (-lo) % P
for q, a in zip(P.tolist(), st.tolist()):
    if a < L: rough[a::q] = False
c = np.add.reduceat(rough.astype(np.int64), np.arange(0, L, H))
out = {"range_lo": lo, "L": L, "total_rough": int(rough.sum()), "L_times_density": float(L * np.exp(np.sum(np.log1p(-1.0 / P.astype(float))))), "windows": len(c), "window_mean": float(c.mean()), "window_var": float(c.var())}
t = json.dumps(out); open("gt_flag2.json", "w").write(t); print(t); print("HASH", hashlib.sha256(t.encode()).hexdigest())

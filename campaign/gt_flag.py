import numpy as np, math, json, hashlib, random
exec(open("gt_var.py").read().split("random.seed")[0])
dens = float(np.exp(np.sum(np.log1p(-1.0 / P.astype(float)))))
random.seed(7); lo = random.randrange(10 ** 12, 2 * 10 ** 12)
rough = np.ones(H, bool); st = (-lo) % P; m = st < H
for q, a in zip(P[m].tolist(), st[m].tolist()): rough[a::q] = False
sieve_count = int(rough.sum())
def lpf_ge(n):
    for q in P.tolist():
        if q * q > n: return True
        if n % q == 0: return False
    return True
brute = sum(1 for i in range(H) if lpf_ge(lo + i))
out = {"density_prod": dens, "H_times_density": H * dens, "mertens": math.exp(-0.5772156649) / math.log(z) * H, "window_lo": lo, "sieve_count": sieve_count, "brute_count_lpf_ge_z": brute}
t = json.dumps(out); open("gt_flag.json", "w").write(t); print(t); print("HASH", hashlib.sha256(t.encode()).hexdigest())

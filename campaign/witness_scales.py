import json, hashlib, random, math, collections
exec(open("bigbad_endpoints.py").read().split("k = 3; prime_ep")[0].split("p = 999997304513")[1])
def factor(m):
    f = []; d = 2
    while d * d <= m:
        while m % d == 0: f.append(d); m //= d
        d += 1 if d == 2 else 2
    if m > 1: f.append(m)
    return f
random.seed(1377)
LO = 990_000_000_000
rows = []; tries = 0
while len(rows) < 300:
    x = random.randrange(LO, LO + 10 ** 10) | 1
    if not isprime(x): continue
    p = x; k = 3; allw = []
    while k ** 4 < p - 1 + k:
        m = p - 1 + k
        if not isprime(m):
            q = 3
            while q <= k * k and m % q: q += 2
            if q > k * k: allw.append(k)
        k += 2
    if not allw: continue
    kmin = allw[0]; m = p - 1 + kmin; f = factor(m)
    rows.append({"p": p, "kmin": kmin, "n_witnesses": len(allw), "omega": len(f), "alpha": math.log(kmin) / math.log(p), "balance": math.log(f[-1] / f[0]) / math.log(m)})
oc = collections.Counter(r["omega"] for r in rows)
dy = collections.Counter(int(math.log2(r["kmin"])) for r in rows)
out = {"seed": 1377, "n": len(rows), "omega_hist": dict(sorted(oc.items())), "kmin_dyadic_log2_hist": dict(sorted(dy.items())),
       "median_kmin": sorted(r["kmin"] for r in rows)[len(rows) // 2], "median_n_witnesses": sorted(r["n_witnesses"] for r in rows)[len(rows) // 2],
       "median_balance": sorted(r["balance"] for r in rows)[len(rows) // 2]}
s = json.dumps(out); open("witness_scales.json", "w").write(s); print(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

import numpy as np, json, hashlib, math
exec(open("bigbad_endpoints.py").read().split("k = 3; prime_ep")[0].split("p = 999997304513")[1])
K = 999; z = K * K // 4
B = z + 1
s = np.ones(B + 1, bool); s[:2] = False
for i in range(2, int(B ** .5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0]
P = P[P < z]
R = math.exp(-0.5772156649) * (K / 2) / math.log(z)
bad = sorted(int(l.split()[1]) for l in open("chunk_990000000000.log") if l.startswith("BAD"))
rows = []
for p in bad:
    lo = p - 1 + K // 2 + 1; L = K - K // 2
    rough = np.ones(L, bool)
    st = (-lo) % P
    for q, a in zip(P.tolist(), st.tolist()):
        if a < L: rough[a::q] = False
    idx = np.nonzero(rough)[0]
    nrough = len(idx)
    nprime = sum(1 for i in idx.tolist() if isprime(lo + i))
    rows.append((nrough, nprime))
nr = np.array([r[0] for r in rows]); npr = np.array([r[1] for r in rows])
out = {"K": K, "z": z, "R": R, "n_bad": len(bad), "all_rough_are_prime": int(np.sum(nr == npr)),
       "caseA_primes_ge_R_over_2": int(np.sum(npr >= R / 2)), "caseB_rough_le_R_over_2": int(np.sum(nr <= R / 2)),
       "neither": int(np.sum((npr < R / 2) & (nr > R / 2))), "median_rough": float(np.median(nr)), "median_prime": float(np.median(npr))}
t = json.dumps(out); open("case_split.json", "w").write(t); print(t); print("HASH", hashlib.sha256(t.encode()).hexdigest())

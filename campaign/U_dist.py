import json, hashlib, numpy as np
from fractions import Fraction
def primes(n):
    s = [1]*(n+1); s[0] = s[1] = 0
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = [0]*len(s[i*i::i])
    return [i for i in range(n+1) if s[i]]
rows = []
for K in range(3, 30, 2):
    ks = list(range(3, K+1, 2)); n = len(ks); full = (1 << n) - 1
    dist = np.zeros(1 << n); dist[0] = 1.0   # distribution over hit-masks for a uniform reduced residue a
    for q in primes(2*K):
        if q == 2: continue   # a-1+k odd for a odd reduced mod 2
        trans = {}
        for a in range(1, q):
            m = 0
            for i, k in enumerate(ks):
                if q <= min(k*k, 2*K) and (a - 1 + k) % q == 0: m |= 1 << i
            trans[m] = trans.get(m, 0) + 1
        new = np.zeros_like(dist)
        idx = np.arange(1 << n)
        for m, c in trans.items():
            np.add.at(new, idx | m, dist * (c / (q - 1)))
        dist = new
    pc = np.array([n - bin(i).count("1") for i in range(1 << n)]); rows.append({"K": K, "shifts": n, "P_U_le": [float(dist[pc <= t].sum()) for t in range(4)], "EU": float((dist*pc).sum())}); print(rows[-1], flush=True)
s = json.dumps(rows); open("U_dist.json", "w").write(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

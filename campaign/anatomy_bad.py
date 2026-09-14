import json, hashlib, numpy as np
from collections import Counter
LO, HI = 20_000_000, 21_000_000
L = HI + 200
lpf = np.zeros(L, dtype=np.int32)
for i in range(2, int(L ** .5) + 1):
    if lpf[i] == 0:
        s = lpf[i*i::i]; s[s == 0] = i; lpf[i*i::i] = s
primes = (np.nonzero(lpf[LO:HI] == 0)[0] + LO).tolist()
nbad = 0; prime_shift_hist = Counter(); killer = Counter(); ratio_hist = Counter()
for p in primes:
    k = 3; rec = []
    while k ** 4 < p - 1 + k:
        m = p - 1 + k; q = int(lpf[m])
        if q == 0: rec.append(("P", k))
        elif q > k * k: rec = None; break
        else: rec.append((q, k))
        k += 2
    if rec is None: continue
    nbad += 1
    prime_shift_hist[sum(1 for r in rec if r[0] == "P")] += 1
    for q, kk in rec:
        if q != "P": killer[q] += 1
out = {"LO": LO, "HI": HI, "primes": len(primes), "bad": nbad, "shifts_per_bad": len(range(3, 68, 2)),
       "prime_shift_count_hist": dict(sorted(prime_shift_hist.items())),
       "top_killers": killer.most_common(15)}
s = json.dumps(out); open("anatomy_bad.json", "w").write(s); print(s)
print("HASH", hashlib.sha256(s.encode()).hexdigest())

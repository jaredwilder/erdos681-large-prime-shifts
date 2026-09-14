import numpy as np, json, hashlib, random
LO = 990_000_000_000; W = 2_000_000
B = 1_000_100
s = np.ones(B + 1, bool); s[:2] = False
for i in range(2, int(B ** .5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0].tolist()
L = W + 1200
lpf = np.zeros(L, dtype=np.int64)
for q in P:
    st = (-LO) % q
    v = lpf[st::q]; v[v == 0] = q; lpf[st::q] = v
bad = sorted(int(l.split()[1]) for l in open("chunk_990000000000.log") if l.startswith("BAD") and LO <= int(l.split()[1]) < LO + W)
primes = [LO + i for i in np.nonzero(lpf[:W] == 0)[0].tolist()]
badset = set(bad)
random.seed(681); good = random.sample([p for p in primes if p not in badset], 2000)
t3 = (LO) ** (1 / 3)
def profile(p):
    k0 = int(p ** (1 / 6)); rough = 0; prime_k = 0; mid = 0; k = k0 | 1
    while k ** 4 < p - 1 + k:
        q = int(lpf[p - LO + k - 1])
        if q == 0 or q > t3:
            rough += 1
            if q == 0: prime_k += 1
            elif q <= k * k: mid += 1
        k += 2
    return rough, prime_k, mid
bp = [profile(p) for p in bad]; gp = [profile(p) for p in good]
med = lambda xs: float(np.median(xs))
out = {"LO": LO, "W": W, "seed": 681, "bad_n": len(bad), "good_n": len(good),
       "bad_median_rough": med([x[0] for x in bp]), "good_median_rough": med([x[0] for x in gp]),
       "bad_median_prime": med([x[1] for x in bp]), "bad_median_mid": med([x[2] for x in bp]),
       "good_median_prime": med([x[1] for x in gp])}
s_ = json.dumps(out); open("upper_rough.json", "w").write(s_); print(s_)
print("HASH", hashlib.sha256(s_.encode()).hexdigest())

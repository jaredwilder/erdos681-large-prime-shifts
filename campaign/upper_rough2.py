import numpy as np, json, hashlib, random
B = 1_000_100
s = np.ones(B + 1, bool); s[:2] = False
for i in range(2, int(B ** .5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0].astype(np.int64)
lines = [l.split() for l in open("chunk_990000000000.log") if l.startswith("BAD")]
bad = sorted(int(x[1]) for x in lines)
random.seed(681)
badS = random.sample(bad, 300)
def lpf_window(a, L):
    lp = np.zeros(L, dtype=np.int64)
    for q in P.tolist():
        st = (-a) % q
        if st >= L: continue
        v = lp[st::q]; v[v == 0] = q; lp[st::q] = v
    return lp
def profile(p, lp):
    t3 = p ** (1 / 3); k = int(p ** (1 / 6)) | 1; rough = prime_k = mid = 0
    while k ** 4 < p - 1 + k:
        q = int(lp[k - 1])
        if q == 0 or q > t3:
            rough += 1
            if q == 0: prime_k += 1
            elif q <= k * k: mid += 1
        k += 2
    return rough, prime_k, mid
bp = []
for p in badS:
    bp.append(profile(p, lpf_window(p, 1100)))
# good controls: nearest prime above each sampled bad prime that is not bad
badset = set(bad); gp = []
for p in badS:
    x = p + 2
    while True:
        lp = lpf_window(x, 1100)
        if lp[0] == 0 and x not in badset: break
        x += 2
    gp.append(profile(x, lp))
med = lambda xs: float(np.median(xs))
out = {"bad_n": len(bp), "good_n": len(gp), "seed": 681,
       "bad_median_rough": med([a for a, _, _ in bp]), "good_median_rough": med([a for a, _, _ in gp]),
       "bad_median_prime": med([b for _, b, _ in bp]), "good_median_prime": med([b for _, b, _ in gp]),
       "bad_median_mid": med([c for _, _, c in bp]), "good_median_mid": med([c for _, _, c in gp])}
s_ = json.dumps(out); open("upper_rough2.json", "w").write(s_); print(s_)
print("HASH", hashlib.sha256(s_.encode()).hexdigest())

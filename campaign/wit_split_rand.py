import numpy as np, json, hashlib, random
exec(open("upper_rough2.py").read().split("def profile")[0])
def wits(p, lp):
    k = 3; lo = hi = 0; k6 = p ** (1 / 6)
    while k ** 4 < p - 1 + k:
        q = int(lp[k - 1])
        if q != 0 and q > k * k:
            if k < k6: lo += 1
            else: hi += 1
        k += 2
    return lo, hi
badset = set(bad); G = []
random.seed(682)
for p in random.sample(bad, 300):
    x = random.randrange(990000000001, 999999000000) | 1
    while True:
        lp = lpf_window(x, 1100)
        if lp[0] == 0 and x not in badset: break
        x += 2
    G.append(wits(x, lp))
lo = [a for a, _ in G]; hi = [b for _, b in G]
out = {"n": len(G), "seed": 682, "controls": "uniform random primes", "mean_lower_witnesses": float(np.mean(lo)), "mean_upper_witnesses": float(np.mean(hi)),
       "share_zero_upper": float(np.mean([h == 0 for h in hi])), "share_zero_lower": float(np.mean([l == 0 for l in lo]))}
s_ = json.dumps(out); open("wit_split_rand.json", "w").write(s_); print(s_); print("HASH", hashlib.sha256(s_.encode()).hexdigest())

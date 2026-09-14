import sys, json, hashlib, numpy as np
from collections import Counter
LO = int(float(sys.argv[1])); W = int(float(sys.argv[2])); HI = LO + W
B = int(HI ** .5) + 2
small = np.ones(B + 1, bool); small[:2] = False
for i in range(2, int(B ** .5) + 1):
    if small[i]: small[i*i::i] = False
P = np.nonzero(small)[0]
SEG = W + 400
lpf = np.zeros(SEG, dtype=np.int32)  # index m-LO; 0 means no prime factor <= B (so prime, since m < B^2)
for q in P.tolist():
    st = (-LO) % q
    if LO + st == q: st += q
    v = lpf[st::q]; v[v == 0] = q; lpf[st::q] = v
nprime = 0; nbad = 0; hist = Counter()
for i in np.nonzero(lpf[:W] == 0)[0].tolist():
    p = LO + i; nprime += 1
    k = 3; zp = 0; bad = True
    while k ** 4 < p - 1 + k:
        q = int(lpf[i + k - 1])
        if q == 0: zp += 1
        elif q > k * k: bad = False; break
        k += 2
    if bad: nbad += 1; hist[zp] += 1
out = {"LO": LO, "W": W, "primes": nprime, "bad": nbad, "zero_prime_shift": hist.get(0, 0), "hist": dict(sorted(hist.items()))}
s = json.dumps(out); open(f"seg_{LO}.json", "w").write(s); print(s)
print("HASH", hashlib.sha256(s.encode()).hexdigest())

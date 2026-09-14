import json, hashlib, numpy as np
LO, HI = 20_000_000, 30_000_000
L = HI + 200
lpf = np.zeros(L, dtype=np.int32)
for i in range(2, int(L ** .5) + 1):
    if lpf[i] == 0:
        s = lpf[i*i::i]
        s[s == 0] = i
        lpf[i*i::i] = s
primes = np.nonzero(lpf[LO:HI] == 0)[0] + LO
bad = 0
for p in primes.tolist():
    k = 3; ok = False
    while k ** 4 < p - 1 + k:
        q = int(lpf[p - 1 + k])
        if q != 0 and q > k * k:
            ok = True; break
        k += 2
    if not ok: bad += 1
out = {"LO": LO, "HI": HI, "primes": len(primes), "bad": bad, "fraction": bad / len(primes), "threshold": 17251 / 67_000}
s = json.dumps(out); open("falsifier_N1.json", "w").write(s)
print(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

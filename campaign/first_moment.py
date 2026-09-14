import sys, json, hashlib, numpy as np
LO = int(float(sys.argv[1])); W = int(float(sys.argv[2])); HI = LO + W
B = int(HI ** .5) + 2
sm = np.ones(B + 1, bool); sm[:2] = False
for i in range(2, int(B ** .5) + 1):
    if sm[i]: sm[i*i::i] = False
P = np.nonzero(sm)[0].tolist()
lpf = np.zeros(W + 400, dtype=np.int32)
for q in P:
    st = (-LO) % q
    if LO + st == q: st += q
    v = lpf[st::q]; v[v == 0] = q; lpf[st::q] = v
pidx = np.nonzero(lpf[:W] == 0)[0]
n = len(pidx); rows = []
for k in [3, 5, 7, 9, 11, 13, 15, 21, 31, 43, 61, 91, 121]:
    if k ** 4 >= LO: break
    q = lpf[pidx + k - 1]
    meas = float(np.mean((q != 0) & (q > k * k)))
    pred = 1.0
    for r in P:
        if r > k * k: break
        if r == 2 or (k - 1) % r == 0: continue
        pred *= 1 - 1 / (r - 1)
    rows.append({"k": k, "measured": round(meas, 5), "predicted_local": round(pred, 5), "ratio": round(meas / pred, 4)})
    print(rows[-1])
s = json.dumps({"LO": LO, "W": W, "primes": n, "rows": rows}); open(f"first_moment_{LO}.json", "w").write(s)
print("HASH", hashlib.sha256(s.encode()).hexdigest())

import json, math, hashlib
def primes(n):
    s = [1]*(n+1); s[0]=s[1]=0
    for i in range(2, int(n**.5)+1):
        if s[i]: s[i*i::i] = [0]*len(s[i*i::i])
    return [i for i in range(n+1) if s[i]]
out = []
for H in range(11, 202, 10):
    ks = set(range(3, H+1, 2)); used = []; logM = 0.0
    P = [q for q in primes(H*H) if q > 2]
    while ks:
        best = None
        for q in P:
            if q in used: continue
            for r in range(q):  # kill k with k = r mod q, requires q <= k^2
                c = sum(1 for k in ks if k % q == r and q <= k*k)
                if c and (best is None or c/math.log(q) > best[0]):
                    best = (c/math.log(q), q, r)
        _, q, r = best
        used.append(q); logM += math.log(q)
        ks = {k for k in ks if not (k % q == r and q <= k*k)}
    out.append({"H": H, "shifts": len(range(3, H+1, 2)), "primes_used": len(used), "greedy_logM": round(logM, 2), "4logH": round(4*math.log(H), 2)})
    print(out[-1])
s = json.dumps(out); open("cover_N8.json", "w").write(s)
print("HASH", hashlib.sha256(s.encode()).hexdigest())

import math, json, hashlib
def primes(n):
    s = bytearray([1]) * (n + 1); s[0:2] = b"\x00\x00"
    for i in range(2, int(n ** .5) + 1):
        if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(3, n + 1) if s[i]]
rows = []
for H in (401,):
    budget = 4 * math.log(H)
    shifts = set(range(3, H + 1, 2))
    P = [q for q in primes(H * H)]
    used = 0.0; chosen = []
    while True:
        best = None
        for q in P:
            if q in chosen or used + math.log(q) > budget: continue
            cnt = {}
            for k in shifts:
                if q <= k * k:
                    r = (1 - k) % q
                    if r: cnt[r] = cnt.get(r, 0) + 1
            if not cnt: continue
            r, c = max(cnt.items(), key=lambda x: x[1])
            score = c / math.log(q)
            if best is None or score > best[0]: best = (score, q, r)
        if best is None: break
        _, q, r = best
        chosen.append(q); used += math.log(q)
        shifts = {k for k in shifts if not (q <= k * k and (1 - k) % q == r)}
    rows.append({"H": H, "odd_shifts": len(range(3, H + 1, 2)), "primes_used": len(chosen), "log_M": round(used, 3), "budget": round(budget, 3), "uncovered": len(shifts), "sqrtH": round(H ** .5, 2)})
    print(rows[-1])
s = json.dumps(rows); open("cover_budget_401.json", "w").write(s)
print("HASH", hashlib.sha256(s.encode()).hexdigest())

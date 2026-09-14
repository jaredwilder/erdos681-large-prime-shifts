import math, json, hashlib, bisect
N = 10 ** 6 + 10
s = bytearray([1]) * N; s[0:2] = b"\x00\x00"
for i in range(2, int(N ** .5) + 1):
    if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
Q = [q for q in range(3, N) if s[q]]
# prefix sums over odd primes q >= 5 of log(1 - 1/(q-2)^2), and over q >= 3 of log(1 - 1/(q-1))
LA = [0.0]; LP = [0.0]
for q in Q:
    LA.append(LA[-1] + (math.log(1 - 1 / (q - 2) ** 2) if q >= 5 else 0.0))
    LP.append(LP[-1] + math.log(1 - 1 / (q - 1)))
def odd_pf(n):
    out = set(); d = 3
    while n % 2 == 0: n //= 2
    while d * d <= n:
        while n % d == 0: out.add(d); n //= d
        d += 2
    if n > 1: out.add(n)
    return out
def logP(k):
    i = bisect.bisect_right(Q, k * k); v = LP[i]
    for q in odd_pf(k - 1):
        if q <= k * k: v -= math.log(1 - 1 / (q - 1))
    return v
def Sstar(k, kk):
    m2 = min(k, kk) ** 2; d = abs(k - kk)
    ex = odd_pf(k - 1) | odd_pf(kk - 1)
    dq = odd_pf(d)
    if 3 <= m2 and 3 not in ex and 3 not in dq: return 0.0
    i = bisect.bisect_right(Q, m2); v = LA[i]
    for q in (ex | dq):
        if q > m2 or q == 3: continue
        base = math.log(1 - 1 / (q - 2) ** 2)
        if q in ex: v -= base
        else: v += math.log((q - 1) / (q - 2)) - base
    f3 = 1.0
    if 3 <= m2 and 3 not in ex and 3 in dq: f3 = 2.0
    return math.exp(v) * f3
out = []
for K in (99, 199, 399, 999):
    ks = list(range(3, K + 1, 2)); P = {k: math.exp(logP(k)) for k in ks}
    mu = sum(P.values())
    tot = 0.0
    for a in ks:
        for b in ks:
            if a != b: tot += P[a] * P[b] * (Sstar(a, b) - 1)
    var = sum(P[k] * (1 - P[k]) for k in ks) + tot
    out.append({"K": K, "mu": mu, "pair_sum": tot, "ratio_to_K_over_logK": tot / (K / math.log(K)), "var": var, "var_over_mu": var / mu})
    print(out[-1])
t = json.dumps(out); open("pair_sum.json", "w").write(t); print("HASH", hashlib.sha256(t.encode()).hexdigest())

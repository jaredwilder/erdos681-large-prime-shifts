import numpy as np, math, json, hashlib, sys
X = float(sys.argv[1]); Q = int(sys.argv[2]); S = int(sys.argv[3]); SEED = 681
rng = np.random.default_rng(SEED)
H = int(X ** .25)
ks = np.array([k for k in range(3, H + 1, 2) if k ** 4 < X - 1 + k])
N = int(ks.max()) ** 2 + 10
s = np.ones(N + 1, bool); s[:2] = False
for i in range(2, int(N ** .5) + 1):
    if s[i]: s[i*i::i] = False
P = np.nonzero(s)[0]; P = P[P > 2]
small = P[P <= Q]
logL = np.cumsum(np.log(1 - 1 / (P - 1)))
C2 = 0.6601618158; lX = math.log(X)
# large-prime part: survival of shift k against odd primes q in (Q, k^2] not dividing k-1
surv = np.empty(len(ks)); sing = np.empty(len(ks))
iQ = np.searchsorted(P, Q, side='right') - 1
for j, k in enumerate(ks):
    i2 = np.searchsorted(P, k * k, side='right') - 1
    l = logL[i2] - (logL[iQ] if iQ >= 0 else 0.0) if k * k > Q else 0.0
    m = k - 1; sg = 2 * C2
    for q in P:
        if q > m: break
        if m % q == 0:
            if Q < q <= k * k: l -= math.log(1 - 1 / (q - 1))
            sg *= (q - 1) / (q - 2)
            while m % q == 0: m //= q
    surv[j] = math.exp(l); sing[j] = sg
logbad = np.empty(S)
for t in range(S):
    alive = np.ones(len(ks), bool)
    for q in small:
        r = rng.integers(1, q)            # p mod q, nonzero
        kill = ((r - 1 + ks) % q == 0) & (q <= ks * ks)
        alive &= ~kill
    # given unkilled by small primes, witness prob = small-conditional rough prob minus prime prob (prime prob rescaled by small-prime survival 1/prod over small q)
    ck_small = 1.0
    w = np.where(alive, surv - sing / lX * np.prod([1 / (1 - 1 / (q - 1)) for q in small]) * 0 - 0, 0.0)
    prime_given_alive = sing / lX / np.array([np.prod([1 - 1 / (q - 1) for q in small if q <= k * k and (k - 1) % q]) for k in ks])
    w = np.where(alive, np.clip(surv - prime_given_alive, 0, 1), 0.0)
    logbad[t] = np.sum(np.log1p(-w))
mx = logbad.max(); est = mx + math.log(np.mean(np.exp(logbad - mx)))
out = {"X": X, "Q": Q, "samples": S, "seed": SEED, "log_P_bad_hybrid": est, "log_P_bad_independent_ref": None}
s_ = json.dumps(out); open(f"hybrid_{int(X)}_{Q}.json", "w").write(s_); print(s_)
print("HASH", hashlib.sha256(s_.encode()).hexdigest())

import json, hashlib, random
exec(open("bigbad_endpoints.py").read().split("k = 3; prime_ep")[0].split("p = 999997304513")[1])
def minfac(m, B):
    q = 3
    while q <= B:
        if m % q == 0: return q
        q += 2
    return 0
def split(p):
    K = 3
    while (K + 2) ** 4 < p - 1 + K + 2: K += 2
    small = big = prim = 0; qs = {}; exempt_hit = 0
    for k in range(3, K + 1, 2):
        m = p - 1 + k
        if isprime(m): prim += 1; continue
        q = minfac(m, k * k)
        if q == 0: return None
        if q <= K: small += 1; qs[q] = qs.get(q, 0) + 1
        else: big += 1
    classes = len(qs); maxload = max(qs.values()) if qs else 0
    return {"p": p, "K": K, "shifts": (K - 1) // 2, "small_q_kills": small, "singleton_big_q": big, "prime_exceptions": prim, "distinct_small_q": classes, "max_class_load": maxload}
bad = [int(l.split()[1]) for l in open("chunk_990000000000.log") if l.startswith("BAD")]
random.seed(1373)
rows = [split(p) for p in sorted(random.sample(bad, 40))]
rows = [r for r in rows if r]
agg = {k: sum(r[k] for r in rows) / len(rows) for k in ("shifts", "small_q_kills", "singleton_big_q", "prime_exceptions", "distinct_small_q", "max_class_load")}
out = {"seed": 1373, "n": len(rows), "means": agg, "min_prime_exceptions": min(r["prime_exceptions"] for r in rows), "max_singleton_big_q": max(r["singleton_big_q"] for r in rows), "rows": rows}
s = json.dumps(out); open("capacity_split.json", "w").write(s)
print(json.dumps({k: out[k] for k in ("n", "means", "min_prime_exceptions", "max_singleton_big_q")}))
print("HASH", hashlib.sha256(s.encode()).hexdigest())

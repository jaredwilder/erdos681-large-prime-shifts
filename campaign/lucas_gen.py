import json, hashlib
exec(open("pratt.py").read().split("F = fac")[0])
E = json.load(open("bigbad_endpoints.json"))
exec(open("bigbad_endpoints.py").read().split("k = 3; prime_ep")[0])
k = 3; prime_ep = []
while k ** 4 < p - 1 + k:
    if isprime(p - 1 + k): prime_ep.append(k)
    k += 2
assert len(prime_ep) == E["prime_endpoints"]
rows = []; big = []
for k in prime_ep:
    m = p - 1 + k; F = fac(m - 1)
    a = 2
    while not all(pow(a, (m - 1) // r, m) != 1 for r in F): a += 1
    rows.append({"k": k, "m": m, "factors": {str(r): e for r, e in F.items()}, "witness": a})
    big += [r for r in F if r > 10 ** 6]
out = {"p": p, "endpoints": rows, "factors_above_1e6": sorted(set(big))}
s = json.dumps(out); open("lucas_endpoints.json", "w").write(s)
print(len(rows), "max_witness", max(r["witness"] for r in rows), "big", out["factors_above_1e6"])
print("HASH", hashlib.sha256(s.encode()).hexdigest())

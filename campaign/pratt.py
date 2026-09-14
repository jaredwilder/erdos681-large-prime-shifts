import json, hashlib
p = 999997304513
def fac(m):
    f = {}; d = 2
    while d * d <= m:
        while m % d == 0: f[d] = f.get(d, 0) + 1; m //= d
        d += 1 if d == 2 else 2
    if m > 1: f[m] = f.get(m, 0) + 1
    return f
F = fac(p - 1)
a = 2
while not all(pow(a, (p - 1) // r, p) != 1 for r in F): a += 1
out = {"p": p, "p_minus_1_factors": {str(k): v for k, v in F.items()}, "witness": a, "fermat": pow(a, p - 1, p)}
s = json.dumps(out); open("pratt_999997304513.json", "w").write(s); print(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

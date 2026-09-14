import json, hashlib, collections
exec(open("bigbad_endpoints.py").read().split("k = 3; prime_ep")[0].split("p = 999997304513")[1])
bad = sorted(int(l.split()[1]) for l in open("chunk_990000000000.log") if l.startswith("BAD"))
cnt = []
for p in bad:
    c = 0; k = 3
    while k ** 4 < p - 1 + k:
        if isprime(p - 1 + k): c += 1
        k += 2
    cnt.append(c)
h = collections.Counter(cnt)
out = {"n": len(bad), "min_prime_exceptions": min(cnt), "max": max(cnt), "mean": sum(cnt) / len(cnt), "argmin_p": bad[cnt.index(min(cnt))], "low_tail": {k: h[k] for k in sorted(h)[:5]}}
s = json.dumps(out); open("pexc_scan.json", "w").write(s); print(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

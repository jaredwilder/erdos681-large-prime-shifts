import json, hashlib
exec(open("bigbad_endpoints.py").read().split("k = 3; prime_ep")[0].split("p = 999997304513")[1])
rows = json.load(open("capacity_split.json"))["rows"]
c = {True: [0, 0], False: [0, 0]}
for r in rows:
    p, K = r["p"], r["K"]
    for k in range(3, K + 1, 2):
        e = (k - 1) % 3 == 0
        c[e][0] += 1
        if isprime(p - 1 + k): c[e][1] += 1
out = {"seed_source": "capacity_split.json seed 1373", "n_primes": len(rows),
       "shifts_3_divides_k_minus_1": c[True][0], "prime_exc_there": c[True][1], "share_there": c[True][1] / c[True][0],
       "shifts_other": c[False][0], "prime_exc_other": c[False][1], "share_other": c[False][1] / c[False][0]}
s = json.dumps(out); open("exempt_share.json", "w").write(s); print(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

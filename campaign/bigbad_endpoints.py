import json, hashlib
p = 999997304513
def isprime(n):
    if n < 2: return False
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % a == 0: return n == a
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def smallest_div(n, B):
    q = 3
    while q <= B:
        if n % q == 0: return q
        q += 2
    return 0
k = 3; prime_ep = []; killed = 0; witness = []
while k ** 4 < p - 1 + k:
    m = p - 1 + k
    if isprime(m): prime_ep.append(k)
    elif smallest_div(m, k * k): killed += 1
    else: witness.append(k)
    k += 2
out = {"p": p, "shifts": (k - 3) // 2, "prime_endpoints": len(prime_ep), "small_divisor_kills": killed, "witnesses": witness, "prime_endpoint_shifts_first": prime_ep[:20]}
s = json.dumps(out); open("bigbad_endpoints.json", "w").write(s); print(s); print("HASH", hashlib.sha256(s.encode()).hexdigest())

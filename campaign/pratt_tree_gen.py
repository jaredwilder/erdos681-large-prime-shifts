import json, hashlib
D = json.load(open("lucas_endpoints.json"))
p0 = D["p"]
SMALL = 10 ** 7

def fac(m):
    f = []; d = 2
    while d * d <= m:
        while m % d == 0: f.append(d); m //= d
        d += 1 if d == 2 else 2
    if m > 1: f.append(m)
    return f

done = {}; order = []
def cert(n):
    if n in done or n < SMALL: return
    F = fac(n - 1)
    for r in set(F): cert(r)
    a = 2
    while not (pow(a, n - 1, n) == 1 and all(pow(a, (n - 1) // r, n) != 1 for r in set(F))): a += 1
    done[n] = (a, F); order.append(n)

targets = [p0] + [r["m"] for r in D["endpoints"]]
for t in targets: cert(t)

def pf(q): return f"P_{q}" if q >= SMALL else "(by norm_num)"
lemmas = []
for n in order:
    a, F = done[n]
    terms = [pf(q) for q in F]
    ex = "⟨" + ", ".join(terms) + ", by simp⟩"
    lemmas.append(
        f"theorem P_{n} : Nat.Prime {n} :=\n"
        f"  lucas_of {n} {a} {F} (by norm_num) (by norm_num)\n"
        f"    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact {ex})\n"
        f"    (by norm_num) (by decide) (by decide)\n")
header = open("pratt_header.lean", encoding="utf-8").read()
conj = " ∧ ".join(f"Nat.Prime {t}" for t in targets)
body = header + "\n" + "\n".join(lemmas) + f"\ntheorem erdos681_pratt_bundle : {conj} :=\n  ⟨{', '.join('P_' + str(t) for t in targets)}⟩\n"
open("Erdos681Pratt.lean", "w", encoding="utf-8").write(body)
print("lemmas", len(lemmas), "targets", len(targets), "bytes", len(body))
print("HASH", hashlib.sha256(body.encode()).hexdigest())

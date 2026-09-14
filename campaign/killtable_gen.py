import json, hashlib
p = 999997304513
D = json.load(open("lucas_endpoints.json"))
primeK = [r["k"] for r in D["endpoints"]]
kills = []; k = 3
while k ** 4 < p - 1 + k:
    if k not in primeK:
        m = p - 1 + k; q = 3
        while m % q: q += 2
        assert q <= k * k
        kills.append((k, q))
    k += 2
lastk = k
tbl = "[" + ", ".join(f"({a}, {b})" for a, b in kills) + "]"
pl = "[" + ", ".join(map(str, primeK)) + "]"
defs = (f"def killTbl : List (Nat × Nat) := {tbl}\n"
        f"def primeKs : List Nat := {pl}\n"
        "def covered (p k : Nat) : Bool := primeKs.contains k || killTbl.any (fun e => e.1 == k && 2 ≤ e.2 && e.2 ≤ k * k && (p - 1 + k) % e.2 == 0)")
spec = {"id": "erdos681_bigbad_kill_table_999997304513", "imports": "none",
        "set_options": ["set_option maxRecDepth 200000"], "definitions": defs, "hypotheses": [],
        "conclusion": f"(List.range {lastk}).all (fun k => k % 2 == 0 || k < 3 || covered {p} k) = true ∧ {lastk} ^ 4 ≥ {p} - 1 + {lastk} ∧ (List.range 1000).all (fun k => k % 2 == 0 || k < 3 || k ^ 4 < {p} - 1 + k) = true",
        "proof": "⟨by decide, by decide, by decide⟩"}
json.dump(spec, open("ob_killtable.json", "w"))
print("kills", len(kills), "primeK", len(primeK), "lastk", lastk)

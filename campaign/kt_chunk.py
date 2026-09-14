import json, sys
lo, hi = int(sys.argv[1]), int(sys.argv[2])
p = 999997304513
D = json.load(open("lucas_endpoints.json"))
primeK = [r["k"] for r in D["endpoints"]]
kills = []
for k in range(lo | 1, hi, 2):
    if k < 3 or k in primeK: continue
    m = p - 1 + k; q = 3
    while m % q: q += 2
    kills.append((k, q))
defs = ("def killTbl : List (Nat × Nat) := [" + ", ".join(f"({a}, {b})" for a, b in kills) + "]\n"
        "def primeKs : List Nat := [" + ", ".join(map(str, primeK)) + "]\n"
        "def covered (p k : Nat) : Bool := primeKs.contains k || killTbl.any (fun e => e.1 == k && 2 ≤ e.2 && e.2 ≤ k * k && (p - 1 + k) % e.2 == 0)")
spec = {"id": f"erdos681_bigbad_kills_{lo}_{hi}", "imports": "none",
        "set_options": ["set_option maxRecDepth 200000", "set_option maxHeartbeats 0"], "definitions": defs, "hypotheses": [],
        "conclusion": f"((List.range {hi - lo}).map (· + {lo})).all (fun k => k % 2 == 0 || k < 3 || covered {p} k) = true",
        "proof": "by decide +kernel"}
json.dump(spec, open(f"ob_kills_{lo}_{hi}.json", "w", encoding="utf-8"), ensure_ascii=False)
print(len(kills))

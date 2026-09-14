import json, sys
m, lo, hi = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
spec = {"id": f"erdos681_trialdiv_{m}_{lo}_{hi}", "imports": "none",
        "set_options": ["set_option maxRecDepth 200000", "set_option maxHeartbeats 0"],
        "definitions": "def noDivIn (m lo n : Nat) : Bool := match n with\n  | 0 => true\n  | n + 1 => (m % (lo + n) != 0) && noDivIn m lo n",
        "hypotheses": [], "conclusion": f"noDivIn {m} {lo} {hi - lo} = true", "proof": "by decide +kernel"}
json.dump(spec, open(f"ob_td_{lo}.json", "w", encoding="utf-8"), ensure_ascii=False)

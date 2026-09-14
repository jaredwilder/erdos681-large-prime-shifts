import json
src = open("Erdos681Assembly.lean", encoding="utf-8").read()
lines = src.splitlines()
body = [l for l in lines if not l.startswith("import ") and not l.startswith("set_option ") and not l.startswith("#print")]
n = 999997304512
body_txt = "\n".join(body)
marker = f"theorem erdos681_n{n}_no_witness"
defs = body_txt[:body_txt.index(marker)]
spec = {"id": "erdos681_n999997304512_no_witness_stamp_r1366", "imports": "Mathlib",
        "set_options": ["set_option maxRecDepth 100000", "set_option maxHeartbeats 0"],
        "definitions": defs, "hypotheses": [],
        "conclusion": f"¬ ∃ k, 0 < k ∧ ¬ Nat.Prime ({n} + k) ∧ 1 < {n} + k ∧ k ^ 2 < Nat.minFac ({n} + k)",
        "proof": body_txt[body_txt.index(marker):].split(":= by", 1)[1].rstrip() and "by" + body_txt[body_txt.index(marker):].split(":= by", 1)[1].rstrip()}
json.dump(spec, open("ob_stamp_n184.json", "w", encoding="utf-8"), ensure_ascii=False)
print(len(defs), len(spec["proof"]))

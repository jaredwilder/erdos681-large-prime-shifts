import math, json, hashlib
N = 1000
s = bytearray([1]) * (N + 1); s[0:2] = b"\x00\x00"
for i in range(2, 32):
    if s[i]: s[i*i::i] = bytearray(len(s[i*i::i]))
P = [q for q in range(3, N) if s[q]]
prod = math.prod(1 - 1 / q for q in P)
out = {"prod_odd_q_le_999": prod, "shifts": 499, "pred_uncovered": 499 * prod, "observed_mean_uncovered": 498.35 - 422.1}
t = json.dumps(out); open("escape_pred.json", "w").write(t); print(t); print("HASH", hashlib.sha256(t.encode()).hexdigest())

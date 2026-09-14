import json, hashlib
p = 999997304513; n = p - 1
D = json.load(open("lucas_endpoints.json"))
pk = [1] + [r["k"] for r in D["endpoints"]]
kq = []
for k in range(2, 1001):
    if k in pk: continue
    m = n + k
    q = 2 if m % 2 == 0 else next(q for q in range(3, k * k + 1, 2) if m % q == 0)
    kq.append((k, q))
base = open("Erdos681Pratt.lean", encoding="utf-8").read()
pkl = ", ".join(map(str, pk))
tbl = ", ".join(f"({a}, {b})" for a, b in kq)
alts = " | ".join("rfl" for _ in pk)
terms = " ".join(f"| exact (by norm_num : {n} + {k} = {n + k}) ▸ P_{n + k}" for k in pk)
asm = f"""
def primeShifts : List ℕ := [{pkl}]
def killPairs : List (ℕ × ℕ) := [{tbl}]
def killQ (k : ℕ) : ℕ := ((killPairs.find? (fun e => e.1 == k)).map Prod.snd).getD 0

theorem table_ok : ∀ k < 1001, 0 < k → (primeShifts.contains k || (decide (2 ≤ killQ k) && decide (killQ k ≤ k * k) && ({n} + k) % killQ k == 0)) = true := by
  decide +kernel

theorem shift_prime (k : ℕ) (h : primeShifts.contains k = true) : Nat.Prime ({n} + k) := by
  simp only [primeShifts, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with {alts}
  all_goals first {terms}

theorem window_bound (k : ℕ) (hk : 1001 ≤ k) : {n} + k ≤ k ^ 4 := by
  have h2 : 1001 * 1001 * 1001 ≤ k * k * k := Nat.mul_le_mul (Nat.mul_le_mul hk hk) hk
  have h4 : 1001 * 1001 * 1001 * k ≤ k * k * k * k := Nat.mul_le_mul_right k h2
  have h3 : k ^ 4 = k * k * k * k := by ring
  omega

theorem erdos681_n{n}_no_witness :
    ¬ ∃ k, 0 < k ∧ ¬ Nat.Prime ({n} + k) ∧ 1 < {n} + k ∧ k ^ 2 < Nat.minFac ({n} + k) := by
  rintro ⟨k, hk, hc, h1, hm⟩
  by_cases hbig : 1001 ≤ k
  · have hsq : Nat.minFac ({n} + k) ^ 2 ≤ {n} + k := Nat.minFac_sq_le_self (by omega) hc
    have hlt : (k ^ 2) ^ 2 < Nat.minFac ({n} + k) ^ 2 := Nat.pow_lt_pow_left hm (by norm_num)
    have := window_bound k hbig
    have e : (k ^ 2) ^ 2 = k ^ 4 := by ring
    omega
  · have ht := table_ok k (by omega) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
    rcases ht with hp | ⟨⟨hq2, hqk⟩, hdv⟩
    · exact hc (shift_prime k hp)
    · have hd : killQ k ∣ {n} + k := Nat.dvd_of_mod_eq_zero hdv
      have := Nat.minFac_le_of_dvd hq2 hd
      have : k ^ 2 = k * k := by ring
      omega

#print axioms erdos681_n{n}_no_witness
"""
open("Erdos681Assembly.lean", "w", encoding="utf-8").write(base + asm)
print("primeShifts", len(pk), "killPairs", len(kq))
print("HASH", hashlib.sha256((base + asm).encode()).hexdigest())

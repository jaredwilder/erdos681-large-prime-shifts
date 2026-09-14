import Mathlib

set_option autoImplicit false

theorem msl_erdos681_k1_composite_witness (n : Nat) (h2 : 2 ≤ n + 1) (hc : ¬ Nat.Prime (n + 1)) : 0 < 1 ∧ ¬ Nat.Prime (n + 1) ∧ 1 ^ 2 < Nat.minFac (n + 1) := by
  refine ⟨by norm_num, hc, ?_⟩
  have := (Nat.minFac_prime (by omega : n + 1 ≠ 1)).two_le
  simpa using (by omega : 1 < Nat.minFac (n + 1))

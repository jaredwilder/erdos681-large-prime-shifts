import Mathlib

set_option autoImplicit false

theorem msl_erdos681_residual_implies_parent (hR : ∃ P0 : Nat, ∀ p : Nat, Nat.Prime p → P0 < p → ∃ h : Nat, 2 ≤ h ∧ ¬ Nat.Prime (p + h) ∧ (h + 1) ^ 2 < Nat.minFac (p + h)) : ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → ∃ k : Nat, 0 < k ∧ 1 < n + k ∧ ¬ Nat.Prime (n + k) ∧ k ^ 2 < Nat.minFac (n + k) := by
  obtain ⟨P0, hP⟩ := hR
  refine ⟨P0 + 1, fun n hn => ?_⟩
  by_cases hp : Nat.Prime (n + 1)
  · obtain ⟨h, h2, hc, hq⟩ := hP (n + 1) hp (by omega)
    refine ⟨h + 1, by omega, by omega, ?_, ?_⟩
    · have e : n + (h + 1) = n + 1 + h := by ring
      rw [e]; exact hc
    · have e : n + (h + 1) = n + 1 + h := by ring
      rw [e]; exact hq
  · refine ⟨1, by omega, by omega, hp, ?_⟩
    have := (Nat.minFac_prime (by omega : n + 1 ≠ 1)).two_le
    simp only [one_pow]; omega

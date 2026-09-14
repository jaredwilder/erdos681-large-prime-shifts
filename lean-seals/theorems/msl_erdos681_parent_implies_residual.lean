import Mathlib

set_option autoImplicit false

theorem msl_erdos681_parent_implies_residual (hT : ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → ∃ k : Nat, 0 < k ∧ 1 < n + k ∧ ¬ Nat.Prime (n + k) ∧ k ^ 2 < Nat.minFac (n + k)) : ∃ P0 : Nat, ∀ p : Nat, Nat.Prime p → P0 < p → ∃ h : Nat, 2 ≤ h ∧ ¬ Nat.Prime (p + h) ∧ (h + 1) ^ 2 < Nat.minFac (p + h) := by
  obtain ⟨N0, hN⟩ := hT
  refine ⟨N0 + 2, fun p hp hlt => ?_⟩
  obtain ⟨k, hk0, h1, hc, hq⟩ := hN (p - 1) (by omega)
  have hk1 : k ≠ 1 := by
    rintro rfl
    have e : p - 1 + 1 = p := by omega
    rw [e] at hc; exact hc hp
  refine ⟨k - 1, ?_, ?_, ?_⟩
  · by_contra hlt2
    have hk : k = 2 := by omega
    subst hk
    have hodd : p % 2 = 1 := by
      rcases hp.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero (by omega)) with h | h <;> omega
    have hdvd : 2 ∣ p - 1 + 2 := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.minFac_le_of_dvd (le_refl 2) hdvd
    omega
  · have e : p + (k - 1) = p - 1 + k := by omega
    rw [e]; exact hc
  · have e : p + (k - 1) = p - 1 + k := by omega
    have e2 : k - 1 + 1 = k := by omega
    rw [e, e2]; exact hq

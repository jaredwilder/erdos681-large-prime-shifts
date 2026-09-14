import Mathlib

set_option autoImplicit false

theorem msl_erdos681_shift_certificate_equiv_r1375 (m k : ℕ) (hm : 2 ≤ m) : ¬ (¬ Nat.Prime m ∧ k ^ 2 < Nat.minFac m) ↔ (Nat.Prime m ∨ ∃ q, Nat.Prime q ∧ q ≤ k ^ 2 ∧ q ∣ m) := by
  constructor
  · intro h
    by_cases hp : Nat.Prime m
    · exact Or.inl hp
    · right
      have hle : Nat.minFac m ≤ k ^ 2 := by
        by_contra hc
        exact h ⟨hp, by omega⟩
      exact ⟨Nat.minFac m, Nat.minFac_prime (by omega), hle, Nat.minFac_dvd m⟩
  · rintro (hp | ⟨q, hq, hqk, hd⟩) ⟨hnp, hlt⟩
    · exact hnp hp
    · have := Nat.minFac_le_of_dvd hq.two_le hd
      omega

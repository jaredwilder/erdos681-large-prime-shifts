import Mathlib

set_option autoImplicit false

theorem msl_erdos681_parity_kills_even_shift (n k : Nat) (hn : 2 ∣ n) (hk : 2 ∣ k) (hk2 : 2 ≤ k) : ¬ (k ^ 2 < Nat.minFac (n + k)) := by
  have hm : Nat.minFac (n + k) ≤ 2 := Nat.minFac_le_of_dvd (le_refl 2) (dvd_add hn hk)
  have : 4 ≤ k ^ 2 := by nlinarith
  omega

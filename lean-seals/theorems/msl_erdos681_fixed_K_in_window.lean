import Mathlib

set_option autoImplicit false

theorem msl_erdos681_fixed_K_in_window (p K k : Nat) (hp : (K + 1) ^ 4 < p) (hk : k ≤ K) (hk1 : 1 ≤ k) : k ^ 4 < p - 1 + k := by
  have h1 : k ^ 4 ≤ K ^ 4 := Nat.pow_le_pow_left hk 4
  have h2 : K ^ 4 < (K + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

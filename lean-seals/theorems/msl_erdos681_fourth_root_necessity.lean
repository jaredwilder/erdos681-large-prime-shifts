import Mathlib

set_option autoImplicit false

theorem msl_erdos681_fourth_root_necessity (n k : Nat) (hpos : 0 < n + k) (hc : ¬ Nat.Prime (n + k)) (hk : k ^ 2 < Nat.minFac (n + k)) : k ^ 4 < n + k := by
  have h := Nat.minFac_sq_le_self hpos hc
  have h2 : (k ^ 2) ^ 2 < (Nat.minFac (n + k)) ^ 2 := Nat.pow_lt_pow_left hk (by norm_num)
  calc k ^ 4 = (k ^ 2) ^ 2 := by ring
    _ < (Nat.minFac (n + k)) ^ 2 := h2
    _ ≤ n + k := h

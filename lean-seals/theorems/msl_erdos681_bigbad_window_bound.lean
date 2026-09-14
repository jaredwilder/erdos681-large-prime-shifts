set_option autoImplicit false

theorem msl_erdos681_bigbad_window_bound (k : Nat) (hk : 1001 ≤ k) : 999997304513 - 1 + k ≤ k ^ 4 := by
  have h1 : 1001 ^ 4 ≤ k ^ 4 := Nat.pow_le_pow_left hk 4
  have h2 : 1001 * 1001 * 1001 ≤ k * k * k := Nat.mul_le_mul (Nat.mul_le_mul hk hk) hk
  have h3 : k ^ 4 = k * k * k * k := by simp [Nat.pow_succ]
  rw [h3]
  have h4 : 1001 * 1001 * 1001 * k ≤ k * k * k * k := Nat.mul_le_mul_right k h2
  omega

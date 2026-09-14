set_option autoImplicit false

theorem msl_erdos681_burst_shift_identity (p d k : Nat) (hp : 1 ≤ p) (hd : d ≤ k) : (p + d) - 1 + (k - d) = p - 1 + k ∧ ((k - d) ^ 2 ≤ k ^ 2) := ⟨by omega, Nat.pow_le_pow_left (by omega) 2⟩

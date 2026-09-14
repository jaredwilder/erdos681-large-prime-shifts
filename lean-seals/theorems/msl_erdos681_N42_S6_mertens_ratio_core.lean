set_option autoImplicit false

theorem msl_erdos681_N42_S6_mertens_ratio_core (k K : Nat) (hk : k ≤ K) : k * k ≤ (2 * K) * (2 * K) := Nat.mul_le_mul (by omega) (by omega)

set_option autoImplicit false

theorem msl_erdos681_N42_S2_endpoint_odd (p k : Nat) (hp : p % 2 = 1) (hk : k % 2 = 1) : (p - 1 + k) % 2 = 1 ∧ (k - 1 + 1) ^ 2 = k ^ 2 := ⟨by omega, by rw [show k - 1 + 1 = k by omega]⟩

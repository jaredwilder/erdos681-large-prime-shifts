set_option autoImplicit false

theorem msl_erdos681_bigbad_even_shift (k : Nat) (hk : 2 ≤ k) (he : k % 2 = 0) : (999997304512 + k) % 2 = 0 ∧ 2 ≤ k * k := ⟨by omega, Nat.le_trans hk (Nat.le_mul_of_pos_left k (by omega))⟩

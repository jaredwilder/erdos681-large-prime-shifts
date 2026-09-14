set_option autoImplicit false

theorem msl_erdos681_witness_p167_k3  : (166 + 3) % 13 = 0 ∧ (∀ q, q < 13 → 2 ≤ q → (166 + 3) % q ≠ 0) ∧ 3 ^ 2 < 13 ∧ 13 < 166 + 3 := by decide

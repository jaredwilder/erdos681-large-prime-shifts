set_option autoImplicit false

theorem msl_erdos681_witness_p1069_k5  : 1068 + 5 = 29 * 37 ∧ (∀ q, q < 29 → 2 ≤ q → (1068 + 5) % q ≠ 0) ∧ 5 ^ 2 < 29 ∧ (∀ k, k < 5 → 1 ≤ k → ((1068 + k) % 2 = 0 ∨ ∀ q, q < 1068 + k → 2 ≤ q → q * q ≤ 1068 + k → (1068 + k) % q ≠ 0 ∨ q ≤ k * k)) := by decide

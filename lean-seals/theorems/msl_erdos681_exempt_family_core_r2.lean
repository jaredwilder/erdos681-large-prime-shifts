set_option autoImplicit false

theorem msl_erdos681_exempt_family_core_r2 (p q k M : Nat) (hp : 1 ≤ p) (hk : 1 ≤ k) (hM : M ∣ k - 1) (hq : q ∣ M) (h : q ∣ p - 1 + k) : q ∣ p := by
  have h1 : q ∣ k - 1 := Nat.dvd_trans hq hM
  have e : p - 1 + k = p + (k - 1) := by omega
  rw [e] at h
  exact (Nat.dvd_add_left h1).mp h

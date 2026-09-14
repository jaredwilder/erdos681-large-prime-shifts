import Mathlib

set_option autoImplicit false

theorem msl_erdos681_divisor_of_shift_is_free (p q k : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q < p) (hk : 1 ≤ k) (hdiv : q ∣ k - 1) : ¬ q ∣ p - 1 + k := by
  intro h
  have e : p - 1 + k = p + (k - 1) := by omega
  rw [e] at h
  have hqp' : q ∣ p := (Nat.dvd_add_left hdiv).mp h
  rcases hp.eq_one_or_self_of_dvd q hqp' with h1 | h1
  · exact hq.one_lt.ne' h1
  · omega

import Mathlib

set_option autoImplicit false

theorem msl_erdos681_large_prime_hits_one_shift (p r K k k' : Nat) (hk : k < k') (hk' : k' ≤ K) (hr : K < r) (h1 : r ∣ p + k) (h2 : r ∣ p + k') : False := by
  have hd : r ∣ (p + k') - (p + k) := Nat.dvd_sub h2 h1
  have e : (p + k') - (p + k) = k' - k := by omega
  rw [e] at hd
  have := Nat.le_of_dvd (by omega) hd
  omega

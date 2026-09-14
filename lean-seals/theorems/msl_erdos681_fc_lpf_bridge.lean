import Mathlib

set_option autoImplicit false

def IsLPF681 (p m : ℕ) : Prop := p.Prime ∧ p ∣ m ∧ ∀ q, q.Prime ∧ q ∣ m → p ≤ q

theorem msl_erdos681_fc_lpf_bridge (m k : Nat) (hm : 1 < m) : (∀ p, IsLPF681 p m → p > k ^ 2) ↔ k ^ 2 < Nat.minFac m := by
  have hne : m ≠ 1 := by omega
  have hmp := Nat.minFac_prime hne
  constructor
  · intro h
    exact h _ ⟨hmp, Nat.minFac_dvd m, fun q hq => Nat.minFac_le_of_dvd hq.1.two_le hq.2⟩
  · intro h p hp
    have h1 : Nat.minFac m ≤ p := Nat.minFac_le_of_dvd hp.1.two_le hp.2.1
    have h2 : p ≤ Nat.minFac m := hp.2.2 _ ⟨hmp, Nat.minFac_dvd m⟩
    omega

import Mathlib

set_option autoImplicit false

theorem msl_erdos681_fourth_root_necessity (n k : Nat) (hpos : 0 < n + k) (hc : ¬ Nat.Prime (n + k)) (hk : k ^ 2 < Nat.minFac (n + k)) : k ^ 4 < n + k := by
  have h := Nat.minFac_sq_le_self hpos hc
  have h2 : (k ^ 2) ^ 2 < (Nat.minFac (n + k)) ^ 2 := Nat.pow_lt_pow_left hk (by norm_num)
  calc k ^ 4 = (k ^ 2) ^ 2 := by ring
    _ < (Nat.minFac (n + k)) ^ 2 := h2
    _ ≤ n + k := h

theorem msl_erdos681_parity_kills_even_shift (n k : Nat) (hn : 2 ∣ n) (hk : 2 ∣ k) (hk2 : 2 ≤ k) : ¬ (k ^ 2 < Nat.minFac (n + k)) := by
  have hm : Nat.minFac (n + k) ≤ 2 := Nat.minFac_le_of_dvd (le_refl 2) (dvd_add hn hk)
  have : 4 ≤ k ^ 2 := by nlinarith
  omega

theorem msl_erdos681_k1_composite_witness (n : Nat) (h2 : 2 ≤ n + 1) (hc : ¬ Nat.Prime (n + 1)) : 0 < 1 ∧ ¬ Nat.Prime (n + 1) ∧ 1 ^ 2 < Nat.minFac (n + 1) := by
  refine ⟨by norm_num, hc, ?_⟩
  have := (Nat.minFac_prime (by omega : n + 1 ≠ 1)).two_le
  simpa using (by omega : 1 < Nat.minFac (n + 1))

theorem msl_erdos681_residual_implies_parent (hR : ∃ P0 : Nat, ∀ p : Nat, Nat.Prime p → P0 < p → ∃ h : Nat, 2 ≤ h ∧ ¬ Nat.Prime (p + h) ∧ (h + 1) ^ 2 < Nat.minFac (p + h)) : ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → ∃ k : Nat, 0 < k ∧ 1 < n + k ∧ ¬ Nat.Prime (n + k) ∧ k ^ 2 < Nat.minFac (n + k) := by
  obtain ⟨P0, hP⟩ := hR
  refine ⟨P0 + 1, fun n hn => ?_⟩
  by_cases hp : Nat.Prime (n + 1)
  · obtain ⟨h, h2, hc, hq⟩ := hP (n + 1) hp (by omega)
    refine ⟨h + 1, by omega, by omega, ?_, ?_⟩
    · have e : n + (h + 1) = n + 1 + h := by ring
      rw [e]; exact hc
    · have e : n + (h + 1) = n + 1 + h := by ring
      rw [e]; exact hq
  · refine ⟨1, by omega, by omega, hp, ?_⟩
    have := (Nat.minFac_prime (by omega : n + 1 ≠ 1)).two_le
    simp only [one_pow]; omega

theorem msl_erdos681_parent_implies_residual_r2 (hT : ∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → ∃ k : Nat, 0 < k ∧ 1 < n + k ∧ ¬ Nat.Prime (n + k) ∧ k ^ 2 < Nat.minFac (n + k)) : ∃ P0 : Nat, ∀ p : Nat, Nat.Prime p → P0 < p → ∃ h : Nat, 2 ≤ h ∧ ¬ Nat.Prime (p + h) ∧ (h + 1) ^ 2 < Nat.minFac (p + h) := by
  obtain ⟨N0, hN⟩ := hT
  refine ⟨N0 + 2, fun p hp hlt => ?_⟩
  obtain ⟨k, hk0, h1, hc, hq⟩ := hN (p - 1) (by omega)
  have hk1 : k ≠ 1 := by
    rintro rfl
    have e : p - 1 + 1 = p := by omega
    rw [e] at hc; exact hc hp
  refine ⟨k - 1, ?_, ?_, ?_⟩
  · by_contra hlt2
    have hk : k = 2 := by omega
    subst hk
    have hodd : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hdvd : 2 ∣ p - 1 + 2 := Nat.dvd_of_mod_eq_zero (by omega)
    have := Nat.minFac_le_of_dvd (le_refl 2) hdvd
    omega
  · have e : p + (k - 1) = p - 1 + k := by omega
    rw [e]; exact hc
  · have e : p + (k - 1) = p - 1 + k := by omega
    have e2 : k - 1 + 1 = k := by omega
    rw [e, e2]; exact hq

theorem msl_erdos681_divisor_of_shift_is_free (p q k : Nat) (hp : Nat.Prime p) (hq : Nat.Prime q) (hqp : q < p) (hk : 1 ≤ k) (hdiv : q ∣ k - 1) : ¬ q ∣ p - 1 + k := by
  intro h
  have e : p - 1 + k = p + (k - 1) := by omega
  rw [e] at h
  have hqp' : q ∣ p := (Nat.dvd_add_left hdiv).mp h
  rcases hp.eq_one_or_self_of_dvd q hqp' with h1 | h1
  · exact hq.one_lt.ne' h1
  · omega

theorem msl_erdos681_fixed_K_in_window (p K k : Nat) (hp : (K + 1) ^ 4 < p) (hk : k ≤ K) (hk1 : 1 ≤ k) : k ^ 4 < p - 1 + k := by
  have h1 : k ^ 4 ≤ K ^ 4 := Nat.pow_le_pow_left hk 4
  have h2 : K ^ 4 < (K + 1) ^ 4 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

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

theorem msl_erdos681_large_prime_hits_one_shift (p r K k k' : Nat) (hk : k < k') (hk' : k' ≤ K) (hr : K < r) (h1 : r ∣ p + k) (h2 : r ∣ p + k') : False := by
  have hd : r ∣ (p + k') - (p + k) := Nat.dvd_sub h2 h1
  have e : (p + k') - (p + k) = k' - k := by omega
  rw [e] at hd
  have := Nat.le_of_dvd (by omega) hd
  omega

theorem msl_erdos681_N42_S6_mertens_ratio_core (k K : Nat) (hk : k ≤ K) : k * k ≤ (2 * K) * (2 * K) := Nat.mul_le_mul (by omega) (by omega)

theorem msl_erdos681_N42_S2_endpoint_odd (p k : Nat) (hp : p % 2 = 1) (hk : k % 2 = 1) : (p - 1 + k) % 2 = 1 ∧ (k - 1 + 1) ^ 2 = k ^ 2 := ⟨by omega, by rw [show k - 1 + 1 = k by omega]⟩

theorem msl_erdos681_exempt_family_core_r2 (p q k M : Nat) (hp : 1 ≤ p) (hk : 1 ≤ k) (hM : M ∣ k - 1) (hq : q ∣ M) (h : q ∣ p - 1 + k) : q ∣ p := by
  have h1 : q ∣ k - 1 := Nat.dvd_trans hq hM
  have e : p - 1 + k = p + (k - 1) := by omega
  rw [e] at h
  exact (Nat.dvd_add_left h1).mp h

theorem msl_erdos681_bundle_equivalence  : (∃ N0 : Nat, ∀ n : Nat, N0 ≤ n → ∃ k : Nat, 0 < k ∧ 1 < n + k ∧ ¬ Nat.Prime (n + k) ∧ k ^ 2 < Nat.minFac (n + k)) ↔ (∃ P0 : Nat, ∀ p : Nat, Nat.Prime p → P0 < p → ∃ h : Nat, 2 ≤ h ∧ ¬ Nat.Prime (p + h) ∧ (h + 1) ^ 2 < Nat.minFac (p + h)) := ⟨fun h => msl_erdos681_parent_implies_residual_r2 h, fun h => msl_erdos681_residual_implies_parent h⟩

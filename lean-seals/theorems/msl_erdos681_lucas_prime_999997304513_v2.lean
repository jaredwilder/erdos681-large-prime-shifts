import Mathlib

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def pmF (b m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1 % m
  | f + 1, e => if e = 0 then 1 % m else
      if e % 2 = 0 then pmF b m f (e / 2) * pmF b m f (e / 2) % m
      else pmF b m f (e / 2) * pmF b m f (e / 2) * b % m

theorem pmF_eq (b m : ℕ) : ∀ f e, e < 2 ^ f → pmF b m f e = b ^ e % m := by
  intro f
  induction f with
  | zero => intro e he; simp at he; subst he; simp [pmF]
  | succ f ih =>
    intro e he
    by_cases h0 : e = 0
    · subst h0; simp [pmF]
    · have hlt : e / 2 < 2 ^ f := by rw [pow_succ] at he; omega
      have hr := ih (e / 2) hlt
      simp only [pmF, h0, if_false, hr]
      split_ifs with h
      · have he2 : e = 2 * (e / 2) := by omega
        conv_rhs => rw [he2, pow_mul']
        simp [Nat.mul_mod, Nat.pow_mod, pow_two]
      · have he2 : e = 2 * (e / 2) + 1 := by omega
        conv_rhs => rw [he2, pow_succ, pow_mul']
        simp [Nat.mul_mod, Nat.pow_mod, pow_two]

theorem msl_erdos681_lucas_prime_999997304513_v2  : Nat.Prime 999997304513 := by
  haveI : Fact (1 < 999997304513) := ⟨by norm_num⟩
  have key : ∀ e : ℕ, ((5 : ZMod 999997304513) ^ e).val = 5 ^ e % 999997304513 := by
    intro e
    rw [show (5 : ZMod 999997304513) = ((5 : ℕ) : ZMod 999997304513) by norm_num, ← Nat.cast_pow, ZMod.val_natCast]
  have ev : ∀ e, e < 2 ^ 40 → 5 ^ e % 999997304513 = pmF 5 999997304513 40 e :=
    fun e he => (pmF_eq 5 999997304513 40 e he).symm
  apply lucas_primality 999997304513 (5 : ZMod 999997304513)
  · apply ZMod.val_injective
    rw [key, ZMod.val_one, ev _ (by norm_num)]
    decide
  · intro q hq hdvd heq
    have hv := congrArg ZMod.val heq
    rw [key, ZMod.val_one] at hv
    have hfac : 999997304513 - 1 = 2 ^ 6 * 37 * 79 * 193 * 27697 := by norm_num
    rw [hfac] at hdvd
    rcases (Nat.Prime.dvd_mul hq).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hq).1 h with h | h
          · have h2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).1 (hq.dvd_of_dvd_pow h)
            subst h2; norm_num at hv; rw [ev _ (by norm_num)] at hv; revert hv; decide
          · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
            subst h2; norm_num at hv; rw [ev _ (by norm_num)] at hv; revert hv; decide
        · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
          subst h2; norm_num at hv; rw [ev _ (by norm_num)] at hv; revert hv; decide
      · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
        subst h2; norm_num at hv; rw [ev _ (by norm_num)] at hv; revert hv; decide
    · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
      subst h2; norm_num at hv; rw [ev _ (by norm_num)] at hv; revert hv; decide

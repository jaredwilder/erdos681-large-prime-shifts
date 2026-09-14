import Mathlib

set_option autoImplicit false

theorem msl_erdos681_lucas_prime_999997304513  : Nat.Prime 999997304513 := by
  haveI : Fact (1 < 999997304513) := ⟨by norm_num⟩
  have key : ∀ e : ℕ, ((5 : ZMod 999997304513) ^ e).val = 5 ^ e % 999997304513 := by
    intro e
    rw [show (5 : ZMod 999997304513) = ((5 : ℕ) : ZMod 999997304513) by norm_num, ← Nat.cast_pow, ZMod.val_natCast]
  apply lucas_primality 999997304513 (5 : ZMod 999997304513)
  · apply ZMod.val_injective
    rw [key, ZMod.val_one]
    norm_num
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
            subst h2; norm_num at hv
          · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
            subst h2; norm_num at hv
        · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
          subst h2; norm_num at hv
      · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
        subst h2; norm_num at hv
    · have h2 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 h
      subst h2; norm_num at hv

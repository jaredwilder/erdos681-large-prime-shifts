import Mathlib

set_option autoImplicit false

def powMod (a m : ℕ) : ℕ → ℕ
  | 0 => 1 % m
  | (e + 1) =>
    if (e + 1) % 2 = 0 then (powMod a m ((e + 1) / 2)) ^ 2 % m
    else (powMod a m ((e + 1) / 2)) ^ 2 * a % m
  decreasing_by all_goals omega

theorem msl_erdos681_powMod_correct (a m e : ℕ) : powMod a m e = a ^ e % m := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    rcases e with _ | e
    · simp [powMod]
    · have hlt : (e + 1) / 2 < e + 1 := by omega
      have hrec := ih _ hlt
      rw [powMod, hrec]
      split_ifs with h
      · have he : e + 1 = 2 * ((e + 1) / 2) := by omega
        conv_rhs => rw [he, pow_mul]
        rw [← Nat.pow_mod]
        ring_nf
      · have he : e + 1 = 2 * ((e + 1) / 2) + 1 := by omega
        conv_rhs => rw [he, pow_succ, pow_mul]
        rw [Nat.mul_mod, ← Nat.pow_mod]
        conv_rhs => rw [Nat.mul_mod]
        simp [Nat.mod_mod, Nat.mul_mod, Nat.pow_mod]
        ring_nf

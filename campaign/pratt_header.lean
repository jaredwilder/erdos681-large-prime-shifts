import Mathlib

set_option maxRecDepth 100000
set_option maxHeartbeats 0

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

theorem dvd_list_prod (q : ℕ) (hq : q.Prime) : ∀ l : List ℕ, q ∣ l.prod → ∃ r ∈ l, q ∣ r
  | [], h => by simp at h; exact absurd h (Nat.Prime.one_lt hq).ne'
  | x :: l, h => by
    rw [List.prod_cons] at h
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact ⟨x, by simp, h⟩
    · obtain ⟨r, hr, h'⟩ := dvd_list_prod q hq l h
      exact ⟨r, by simp [hr], h'⟩

theorem lucas_of (p a : ℕ) (fs : List ℕ) (hp : 1 < p) (hprod : fs.prod = p - 1)
    (hpr : ∀ q ∈ fs, q.Prime) (hlt : p - 1 < 2 ^ 64)
    (hf : pmF a p 64 (p - 1) = 1) (hd : ∀ q ∈ fs, pmF a p 64 ((p - 1) / q) ≠ 1) : p.Prime := by
  haveI : Fact (1 < p) := ⟨hp⟩
  have key : ∀ e, e < 2 ^ 64 → ((a : ZMod p) ^ e).val = pmF a p 64 e := by
    intro e he
    rw [← Nat.cast_pow, ZMod.val_natCast, pmF_eq a p 64 e he]
  apply lucas_primality p (a : ZMod p)
  · apply ZMod.val_injective
    rw [key _ hlt, ZMod.val_one, hf]
  · intro q hq hdvd heq
    have hv := congrArg ZMod.val heq
    rw [key _ (lt_of_le_of_lt (Nat.div_le_self _ _) hlt), ZMod.val_one] at hv
    rw [← hprod] at hdvd
    obtain ⟨r, hr, hqr⟩ := dvd_list_prod q hq fs hdvd
    have hqr' := (Nat.prime_dvd_prime_iff_eq hq (hpr r hr)).1 hqr
    subst hqr'
    exact hd q hr hv

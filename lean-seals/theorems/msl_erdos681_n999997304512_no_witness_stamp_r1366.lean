import Mathlib

set_option autoImplicit false
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

theorem P_999997304513 : Nat.Prime 999997304513 :=
  lucas_of 999997304513 5 [2, 2, 2, 2, 2, 2, 37, 79, 193, 27697] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304521 : Nat.Prime 999997304521 :=
  lucas_of 999997304521 7 [2, 2, 2, 3, 5, 19, 173, 2535233] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_218626433 : Nat.Prime 218626433 :=
  lucas_of 218626433 3 [2, 2, 2, 2, 2, 2, 2, 41, 41659] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304543 : Nat.Prime 999997304543 :=
  lucas_of 999997304543 5 [2, 2287, 218626433] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_218626433, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_29729971 : Nat.Prime 29729971 :=
  lucas_of 29729971 3 [2, 3, 3, 3, 5, 149, 739] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304557 : Nat.Prime 999997304557 :=
  lucas_of 999997304557 2 [2, 2, 3, 2803, 29729971] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), P_29729971, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304629 : Nat.Prime 999997304629 :=
  lucas_of 999997304629 13 [2, 2, 3, 7, 419, 769, 36947] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304707 : Nat.Prime 999997304707 :=
  lucas_of 999997304707 2 [2, 3, 3, 47, 709, 1667179] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_2145916963 : Nat.Prime 2145916963 :=
  lucas_of 2145916963 3 [2, 3, 3, 3, 3, 3, 7, 19, 33199] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304759 : Nat.Prime 999997304759 :=
  lucas_of 999997304759 13 [2, 233, 2145916963] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_2145916963, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304783 : Nat.Prime 999997304783 :=
  lucas_of 999997304783 10 [2, 7, 43, 38039, 43669] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_1126123091 : Nat.Prime 1126123091 :=
  lucas_of 1126123091 2 [2, 5, 199, 565891] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304809 : Nat.Prime 999997304809 :=
  lucas_of 999997304809 7 [2, 2, 2, 3, 37, 1126123091] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_1126123091, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_62499831553 : Nat.Prime 62499831553 :=
  lucas_of 62499831553 7 [2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 9042221] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304849 : Nat.Prime 999997304849 :=
  lucas_of 999997304849 3 [2, 2, 2, 2, 62499831553] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), P_62499831553, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304863 : Nat.Prime 999997304863 :=
  lucas_of 999997304863 3 [2, 3, 19, 7717, 1136699] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_645993091 : Nat.Prime 645993091 :=
  lucas_of 645993091 3 [2, 3, 3, 3, 5, 223, 10729] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304869 : Nat.Prime 999997304869 :=
  lucas_of 999997304869 7 [2, 2, 3, 3, 43, 645993091] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_645993091, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304879 : Nat.Prime 999997304879 :=
  lucas_of 999997304879 11 [2, 11, 13, 3331, 1049683] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304897 : Nat.Prime 999997304897 :=
  lucas_of 999997304897 3 [2, 2, 2, 2, 2, 2, 41893, 372973] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304921 : Nat.Prime 999997304921 :=
  lucas_of 999997304921 3 [2, 2, 2, 5, 211, 1303, 90931] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_166666217491 : Nat.Prime 166666217491 :=
  lucas_of 166666217491 3 [2, 3, 3, 3, 5, 1933, 319339] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304947 : Nat.Prime 999997304947 :=
  lucas_of 999997304947 2 [2, 3, 166666217491] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_166666217491, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_714283789 : Nat.Prime 714283789 :=
  lucas_of 714283789 2 [2, 2, 3, 131, 454379] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_2857135157 : Nat.Prime 2857135157 :=
  lucas_of 2857135157 2 [2, 2, 714283789] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_714283789, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304951 : Nat.Prime 999997304951 :=
  lucas_of 999997304951 13 [2, 5, 5, 7, 2857135157] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), P_2857135157, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304953 : Nat.Prime 999997304953 :=
  lucas_of 999997304953 5 [2, 2, 2, 3, 29, 2131, 674227] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_356378227 : Nat.Prime 356378227 :=
  lucas_of 356378227 2 [2, 3, 61, 67, 14533] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304963 : Nat.Prime 999997304963 :=
  lucas_of 999997304963 2 [2, 23, 61, 356378227] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), P_356378227, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997304989 : Nat.Prime 999997304989 :=
  lucas_of 999997304989 2 [2, 2, 3, 11, 47, 3943, 40879] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_66666487 : Nat.Prime 66666487 :=
  lucas_of 66666487 3 [2, 3, 17, 653593] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305001 : Nat.Prime 999997305001 :=
  lucas_of 999997305001 11 [2, 2, 2, 3, 5, 5, 5, 5, 66666487] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_66666487, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305019 : Nat.Prime 999997305019 :=
  lucas_of 999997305019 3 [2, 3, 109, 25189, 60703] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_14750093 : Nat.Prime 14750093 :=
  lucas_of 14750093 2 [2, 2, 7, 263, 2003] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305029 : Nat.Prime 999997305029 :=
  lucas_of 999997305029 2 [2, 2, 17, 997, 14750093] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), P_14750093, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305053 : Nat.Prime 999997305053 :=
  lucas_of 999997305053 2 [2, 2, 19, 41, 569, 564013] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_17562299 : Nat.Prime 17562299 :=
  lucas_of 17562299 2 [2, 13, 109, 6197] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305061 : Nat.Prime 999997305061 :=
  lucas_of 999997305061 2 [2, 2, 3, 5, 13, 73, 17562299] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_17562299, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_24884221 : Nat.Prime 24884221 :=
  lucas_of 24884221 6 [2, 2, 3, 5, 414737] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305107 : Nat.Prime 999997305107 :=
  lucas_of 999997305107 2 [2, 71, 283, 24884221] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), P_24884221, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305137 : Nat.Prime 999997305137 :=
  lucas_of 999997305137 3 [2, 2, 2, 2, 16699, 3742729] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305157 : Nat.Prime 999997305157 :=
  lucas_of 999997305157 5 [2, 2, 3, 3, 3, 929, 9966883] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_13513477097 : Nat.Prime 13513477097 :=
  lucas_of 13513477097 5 [2, 2, 2, 7, 31, 67, 223, 521] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305179 : Nat.Prime 999997305179 :=
  lucas_of 999997305179 2 [2, 37, 13513477097] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_13513477097, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_58955153 : Nat.Prime 58955153 :=
  lucas_of 58955153 3 [2, 2, 2, 2, 3684697] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305187 : Nat.Prime 999997305187 :=
  lucas_of 999997305187 3 [2, 3, 11, 257, 58955153] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), P_58955153, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305239 : Nat.Prime 999997305239 :=
  lucas_of 999997305239 7 [2, 23, 67, 677, 479267] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_83333108773 : Nat.Prime 83333108773 :=
  lucas_of 83333108773 2 [2, 2, 3, 3, 3, 3, 3, 6833, 12547] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305277 : Nat.Prime 999997305277 :=
  lucas_of 999997305277 2 [2, 2, 3, 83333108773] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), P_83333108773, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_106928711 : Nat.Prime 106928711 :=
  lucas_of 106928711 7 [2, 5, 7, 1527553] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_71428378949 : Nat.Prime 71428378949 :=
  lucas_of 71428378949 2 [2, 2, 167, 106928711] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), P_106928711, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305287 : Nat.Prime 999997305287 :=
  lucas_of 999997305287 7 [2, 7, 71428378949] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_71428378949, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_475736111 : Nat.Prime 475736111 :=
  lucas_of 475736111 7 [2, 5, 1471, 32341] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305323 : Nat.Prime 999997305323 :=
  lucas_of 999997305323 2 [2, 1051, 475736111] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_475736111, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_135134771 : Nat.Prime 135134771 :=
  lucas_of 135134771 2 [2, 5, 41, 329597] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305401 : Nat.Prime 999997305401 :=
  lucas_of 999997305401 6 [2, 2, 2, 5, 5, 37, 135134771] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_135134771, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_99999730543 : Nat.Prime 99999730543 :=
  lucas_of 99999730543 11 [2, 3, 89, 101, 1854113] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305431 : Nat.Prime 999997305431 :=
  lucas_of 999997305431 11 [2, 5, 99999730543] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), P_99999730543, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305467 : Nat.Prime 999997305467 :=
  lucas_of 999997305467 2 [2, 419, 761, 1568087] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_517596949 : Nat.Prime 517596949 :=
  lucas_of 517596949 2 [2, 2, 3, 3, 11, 1307063] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305469 : Nat.Prime 999997305469 :=
  lucas_of 999997305469 10 [2, 2, 3, 7, 23, 517596949] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_517596949, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305479 : Nat.Prime 999997305479 :=
  lucas_of 999997305479 7 [2, 154873, 3228443] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_10425109 : Nat.Prime 10425109 :=
  lucas_of 10425109 2 [2, 2, 3, 499, 1741] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem P_999997305499 : Nat.Prime 999997305499 :=
  lucas_of 999997305499 2 [2, 3, 3, 73, 73, 10425109] (by norm_num) (by norm_num)
    (by simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]; exact ⟨(by norm_num), (by norm_num), (by norm_num), (by norm_num), (by norm_num), P_10425109, by simp⟩)
    (by norm_num) (by decide) (by decide)

theorem erdos681_pratt_bundle : Nat.Prime 999997304513 ∧ Nat.Prime 999997304521 ∧ Nat.Prime 999997304543 ∧ Nat.Prime 999997304557 ∧ Nat.Prime 999997304629 ∧ Nat.Prime 999997304707 ∧ Nat.Prime 999997304759 ∧ Nat.Prime 999997304783 ∧ Nat.Prime 999997304809 ∧ Nat.Prime 999997304849 ∧ Nat.Prime 999997304863 ∧ Nat.Prime 999997304869 ∧ Nat.Prime 999997304879 ∧ Nat.Prime 999997304897 ∧ Nat.Prime 999997304921 ∧ Nat.Prime 999997304947 ∧ Nat.Prime 999997304951 ∧ Nat.Prime 999997304953 ∧ Nat.Prime 999997304963 ∧ Nat.Prime 999997304989 ∧ Nat.Prime 999997305001 ∧ Nat.Prime 999997305019 ∧ Nat.Prime 999997305029 ∧ Nat.Prime 999997305053 ∧ Nat.Prime 999997305061 ∧ Nat.Prime 999997305107 ∧ Nat.Prime 999997305137 ∧ Nat.Prime 999997305157 ∧ Nat.Prime 999997305179 ∧ Nat.Prime 999997305187 ∧ Nat.Prime 999997305239 ∧ Nat.Prime 999997305277 ∧ Nat.Prime 999997305287 ∧ Nat.Prime 999997305323 ∧ Nat.Prime 999997305401 ∧ Nat.Prime 999997305431 ∧ Nat.Prime 999997305467 ∧ Nat.Prime 999997305469 ∧ Nat.Prime 999997305479 ∧ Nat.Prime 999997305499 :=
  ⟨P_999997304513, P_999997304521, P_999997304543, P_999997304557, P_999997304629, P_999997304707, P_999997304759, P_999997304783, P_999997304809, P_999997304849, P_999997304863, P_999997304869, P_999997304879, P_999997304897, P_999997304921, P_999997304947, P_999997304951, P_999997304953, P_999997304963, P_999997304989, P_999997305001, P_999997305019, P_999997305029, P_999997305053, P_999997305061, P_999997305107, P_999997305137, P_999997305157, P_999997305179, P_999997305187, P_999997305239, P_999997305277, P_999997305287, P_999997305323, P_999997305401, P_999997305431, P_999997305467, P_999997305469, P_999997305479, P_999997305499⟩

def primeShifts : List ℕ := [1, 9, 31, 45, 117, 195, 247, 271, 297, 337, 351, 357, 367, 385, 409, 435, 439, 441, 451, 477, 489, 507, 517, 541, 549, 595, 625, 645, 667, 675, 727, 765, 775, 811, 889, 919, 955, 957, 967, 987]
def killPairs : List (ℕ × ℕ) := [(2, 2), (3, 5), (4, 2), (5, 3), (6, 2), (7, 41), (8, 2), (10, 2), (11, 3), (12, 2), (13, 5), (14, 2), (15, 13), (16, 2), (17, 3), (18, 2), (19, 157), (20, 2), (21, 373), (22, 2), (23, 3), (24, 2), (25, 7), (26, 2), (27, 19), (28, 2), (29, 3), (30, 2), (32, 2), (33, 5), (34, 2), (35, 3), (36, 2), (37, 37), (38, 2), (39, 7), (40, 2), (41, 3), (42, 2), (43, 5), (44, 2), (46, 2), (47, 3), (48, 2), (49, 449), (50, 2), (51, 53), (52, 2), (53, 3), (54, 2), (55, 43), (56, 2), (57, 17), (58, 2), (59, 3), (60, 2), (61, 1049), (62, 2), (63, 5), (64, 2), (65, 3), (66, 2), (67, 7), (68, 2), (69, 11), (70, 2), (71, 3), (72, 2), (73, 5), (74, 2), (75, 1493), (76, 2), (77, 3), (78, 2), (79, 79), (80, 2), (81, 7), (82, 2), (83, 3), (84, 2), (85, 113), (86, 2), (87, 733), (88, 2), (89, 3), (90, 2), (91, 11), (92, 2), (93, 5), (94, 2), (95, 3), (96, 2), (97, 71), (98, 2), (99, 97), (100, 2), (101, 3), (102, 2), (103, 5), (104, 2), (105, 23), (106, 2), (107, 3), (108, 2), (109, 7), (110, 2), (111, 37), (112, 2), (113, 3), (114, 2), (115, 587), (116, 2), (118, 2), (119, 3), (120, 2), (121, 29), (122, 2), (123, 5), (124, 2), (125, 3), (126, 2), (127, 31), (128, 2), (129, 131), (130, 2), (131, 3), (132, 2), (133, 5), (134, 2), (135, 11), (136, 2), (137, 3), (138, 2), (139, 83), (140, 2), (141, 19), (142, 2), (143, 3), (144, 2), (145, 13), (146, 2), (147, 47), (148, 2), (149, 3), (150, 2), (151, 7), (152, 2), (153, 5), (154, 2), (155, 3), (156, 2), (157, 11), (158, 2), (159, 17), (160, 2), (161, 3), (162, 2), (163, 5), (164, 2), (165, 7), (166, 2), (167, 3), (168, 2), (169, 59), (170, 2), (171, 13), (172, 2), (173, 3), (174, 2), (175, 311), (176, 2), (177, 619), (178, 2), (179, 3), (180, 2), (181, 173), (182, 2), (183, 5), (184, 2), (185, 3), (186, 2), (187, 239), (188, 2), (189, 31), (190, 2), (191, 3), (192, 2), (193, 5), (194, 2), (196, 2), (197, 3), (198, 2), (199, 347), (200, 2), (201, 11), (202, 2), (203, 3), (204, 2), (205, 4583), (206, 2), (207, 7), (208, 2), (209, 3), (210, 2), (211, 509), (212, 2), (213, 5), (214, 2), (215, 3), (216, 2), (217, 19), (218, 2), (219, 919), (220, 2), (221, 3), (222, 2), (223, 5), (224, 2), (225, 443), (226, 2), (227, 3), (228, 2), (229, 3529), (230, 2), (231, 149), (232, 2), (233, 3), (234, 2), (235, 7), (236, 2), (237, 29), (238, 2), (239, 3), (240, 2), (241, 47), (242, 2), (243, 5), (244, 2), (245, 3), (246, 2), (248, 2), (249, 7), (250, 2), (251, 3), (252, 2), (253, 5), (254, 2), (255, 19), (256, 2), (257, 3), (258, 2), (259, 37), (260, 2), (261, 17), (262, 2), (263, 3), (264, 2), (265, 307), (266, 2), (267, 11), (268, 2), (269, 3), (270, 2), (272, 2), (273, 5), (274, 2), (275, 3), (276, 2), (277, 7), (278, 2), (279, 103), (280, 2), (281, 3), (282, 2), (283, 5), (284, 2), (285, 89), (286, 2), (287, 3), (288, 2), (289, 11), (290, 2), (291, 7), (292, 2), (293, 3), (294, 2), (295, 17), (296, 2), (298, 2), (299, 3), (300, 2), (301, 13), (302, 2), (303, 5), (304, 2), (305, 3), (306, 2), (307, 20717), (308, 2), (309, 21157), (310, 2), (311, 3), (312, 2), (313, 5), (314, 2), (315, 19139), (316, 2), (317, 3), (318, 2), (319, 7), (320, 2), (321, 16829), (322, 2), (323, 3), (324, 2), (325, 55073), (326, 2), (327, 13), (328, 2), (329, 3), (330, 2), (331, 19), (332, 2), (333, 5), (334, 2), (335, 3), (336, 2), (338, 2), (339, 389), (340, 2), (341, 3), (342, 2), (343, 5), (344, 2), (345, 883), (346, 2), (347, 3), (348, 2), (349, 337), (350, 2), (352, 2), (353, 3), (354, 2), (355, 11), (356, 2), (358, 2), (359, 3), (360, 2), (361, 7), (362, 2), (363, 5), (364, 2), (365, 3), (366, 2), (368, 2), (369, 19), (370, 2), (371, 3), (372, 2), (373, 5), (374, 2), (375, 7), (376, 2), (377, 3), (378, 2), (379, 13), (380, 2), (381, 23), (382, 2), (383, 3), (384, 2), (386, 2), (387, 853), (388, 2), (389, 3), (390, 2), (391, 67), (392, 2), (393, 5), (394, 2), (395, 3), (396, 2), (397, 17), (398, 2), (399, 11), (400, 2), (401, 3), (402, 2), (403, 5), (404, 2), (405, 13), (406, 2), (407, 3), (408, 2), (410, 2), (411, 29), (412, 2), (413, 3), (414, 2), (415, 907), (416, 2), (417, 7), (418, 2), (419, 3), (420, 2), (421, 11), (422, 2), (423, 5), (424, 2), (425, 3), (426, 2), (427, 23), (428, 2), (429, 47), (430, 2), (431, 3), (432, 2), (433, 5), (434, 2), (436, 2), (437, 3), (438, 2), (440, 2), (442, 2), (443, 3), (444, 2), (445, 7), (446, 2), (447, 463), (448, 2), (449, 3), (450, 2), (452, 2), (453, 5), (454, 2), (455, 3), (456, 2), (457, 13), (458, 2), (459, 7), (460, 2), (461, 3), (462, 2), (463, 5), (464, 2), (465, 11), (466, 2), (467, 3), (468, 2), (469, 29), (470, 2), (471, 83), (472, 2), (473, 3), (474, 2), (475, 53), (476, 2), (478, 2), (479, 3), (480, 2), (481, 37), (482, 2), (483, 5), (484, 2), (485, 3), (486, 2), (487, 7), (488, 2), (490, 2), (491, 3), (492, 2), (493, 5), (494, 2), (495, 156119), (496, 2), (497, 3), (498, 2), (499, 17), (500, 2), (501, 7), (502, 2), (503, 3), (504, 2), (505, 179), (506, 2), (508, 2), (509, 3), (510, 2), (511, 61), (512, 2), (513, 5), (514, 2), (515, 3), (516, 2), (518, 2), (519, 23), (520, 2), (521, 3), (522, 2), (523, 5), (524, 2), (525, 67), (526, 2), (527, 3), (528, 2), (529, 7), (530, 2), (531, 11), (532, 2), (533, 3), (534, 2), (535, 13), (536, 2), (537, 113), (538, 2), (539, 3), (540, 2), (542, 2), (543, 5), (544, 2), (545, 3), (546, 2), (547, 151), (548, 2), (550, 2), (551, 3), (552, 2), (553, 5), (554, 2), (555, 37), (556, 2), (557, 3), (558, 2), (559, 19), (560, 2), (561, 13), (562, 2), (563, 3), (564, 2), (565, 23), (566, 2), (567, 17), (568, 2), (569, 3), (570, 2), (571, 7), (572, 2), (573, 5), (574, 2), (575, 3), (576, 2), (577, 4703), (578, 2), (579, 193), (580, 2), (581, 3), (582, 2), (583, 5), (584, 2), (585, 7), (586, 2), (587, 3), (588, 2), (589, 7331), (590, 2), (591, 6863), (592, 2), (593, 3), (594, 2), (596, 2), (597, 11), (598, 2), (599, 3), (600, 2), (601, 17), (602, 2), (603, 5), (604, 2), (605, 3), (606, 2), (607, 20477), (608, 2), (609, 3319), (610, 2), (611, 3), (612, 2), (613, 5), (614, 2), (615, 109), (616, 2), (617, 3), (618, 2), (619, 11), (620, 2), (621, 73), (622, 2), (623, 3), (624, 2), (626, 2), (627, 7), (628, 2), (629, 3), (630, 2), (631, 379), (632, 2), (633, 5), (634, 2), (635, 3), (636, 2), (637, 83), (638, 2), (639, 13), (640, 2), (641, 3), (642, 2), (643, 5), (644, 2), (646, 2), (647, 3), (648, 2), (649, 3659), (650, 2), (651, 139), (652, 2), (653, 3), (654, 2), (655, 7), (656, 2), (657, 23), (658, 2), (659, 3), (660, 2), (661, 691), (662, 2), (663, 5), (664, 2), (665, 3), (666, 2), (668, 2), (669, 7), (670, 2), (671, 3), (672, 2), (673, 5), (674, 2), (676, 2), (677, 3), (678, 2), (679, 2087), (680, 2), (681, 97), (682, 2), (683, 3), (684, 2), (685, 11), (686, 2), (687, 53), (688, 2), (689, 3), (690, 2), (691, 13), (692, 2), (693, 5), (694, 2), (695, 3), (696, 2), (697, 7), (698, 2), (699, 137), (700, 2), (701, 3), (702, 2), (703, 5), (704, 2), (705, 599), (706, 2), (707, 3), (708, 2), (709, 1031), (710, 2), (711, 7), (712, 2), (713, 3), (714, 2), (715, 601), (716, 2), (717, 13), (718, 2), (719, 3), (720, 2), (721, 1597), (722, 2), (723, 5), (724, 2), (725, 3), (726, 2), (728, 2), (729, 11), (730, 2), (731, 3), (732, 2), (733, 5), (734, 2), (735, 291143), (736, 2), (737, 3), (738, 2), (739, 7), (740, 2), (741, 111871), (742, 2), (743, 3), (744, 2), (745, 41), (746, 2), (747, 31), (748, 2), (749, 3), (750, 2), (751, 11), (752, 2), (753, 5), (754, 2), (755, 3), (756, 2), (757, 1061), (758, 2), (759, 29), (760, 2), (761, 3), (762, 2), (763, 5), (764, 2), (766, 2), (767, 3), (768, 2), (769, 13), (770, 2), (771, 17), (772, 2), (773, 3), (774, 2), (776, 2), (777, 37), (778, 2), (779, 3), (780, 2), (781, 7), (782, 2), (783, 5), (784, 2), (785, 3), (786, 2), (787, 19), (788, 2), (789, 3229), (790, 2), (791, 3), (792, 2), (793, 5), (794, 2), (795, 7), (796, 2), (797, 3), (798, 2), (799, 14723), (800, 2), (801, 199), (802, 2), (803, 3), (804, 2), (805, 17), (806, 2), (807, 71), (808, 2), (809, 3), (810, 2), (812, 2), (813, 5), (814, 2), (815, 3), (816, 2), (817, 11), (818, 2), (819, 89), (820, 2), (821, 3), (822, 2), (823, 5), (824, 2), (825, 19), (826, 2), (827, 3), (828, 2), (829, 43), (830, 2), (831, 1873), (832, 2), (833, 3), (834, 2), (835, 271), (836, 2), (837, 7), (838, 2), (839, 3), (840, 2), (841, 23), (842, 2), (843, 5), (844, 2), (845, 3), (846, 2), (847, 13), (848, 2), (849, 151), (850, 2), (851, 3), (852, 2), (853, 5), (854, 2), (855, 433), (856, 2), (857, 3), (858, 2), (859, 181), (860, 2), (861, 11), (862, 2), (863, 3), (864, 2), (865, 7), (866, 2), (867, 683807), (868, 2), (869, 3), (870, 2), (871, 31), (872, 2), (873, 5), (874, 2), (875, 3), (876, 2), (877, 59), (878, 2), (879, 7), (880, 2), (881, 3), (882, 2), (883, 5), (884, 2), (885, 769), (886, 2), (887, 3), (888, 2), (890, 2), (891, 859), (892, 2), (893, 3), (894, 2), (895, 3623), (896, 2), (897, 103), (898, 2), (899, 3), (900, 2), (901, 19), (902, 2), (903, 5), (904, 2), (905, 3), (906, 2), (907, 7), (908, 2), (909, 41), (910, 2), (911, 3), (912, 2), (913, 5), (914, 2), (915, 43), (916, 2), (917, 3), (918, 2), (920, 2), (921, 7), (922, 2), (923, 3), (924, 2), (925, 13), (926, 2), (927, 11), (928, 2), (929, 3), (930, 2), (931, 257), (932, 2), (933, 5), (934, 2), (935, 3), (936, 2), (937, 2437), (938, 2), (939, 19), (940, 2), (941, 3), (942, 2), (943, 5), (944, 2), (945, 233), (946, 2), (947, 3), (948, 2), (949, 7), (950, 2), (951, 13), (952, 2), (953, 3), (954, 2), (956, 2), (958, 2), (959, 3), (960, 2), (961, 157), (962, 2), (963, 5), (964, 2), (965, 3), (966, 2), (968, 2), (969, 83), (970, 2), (971, 3), (972, 2), (973, 5), (974, 2), (975, 17), (976, 2), (977, 3), (978, 2), (979, 23), (980, 2), (981, 1163), (982, 2), (983, 3), (984, 2), (985, 2549), (986, 2), (988, 2), (989, 3), (990, 2), (991, 7), (992, 2), (993, 5), (994, 2), (995, 3), (996, 2), (997, 89), (998, 2), (999, 37), (1000, 2)]
def killQ (k : ℕ) : ℕ := ((killPairs.find? (fun e => e.1 == k)).map Prod.snd).getD 0

theorem table_ok : ∀ k < 1001, 0 < k → (primeShifts.contains k || (decide (2 ≤ killQ k) && decide (killQ k ≤ k * k) && (999997304512 + k) % killQ k == 0)) = true := by
  decide +kernel

theorem shift_prime (k : ℕ) (h : primeShifts.contains k = true) : Nat.Prime (999997304512 + k) := by
  simp only [primeShifts, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact (by norm_num : 999997304512 + 1 = 999997304513) ▸ P_999997304513 | exact (by norm_num : 999997304512 + 9 = 999997304521) ▸ P_999997304521 | exact (by norm_num : 999997304512 + 31 = 999997304543) ▸ P_999997304543 | exact (by norm_num : 999997304512 + 45 = 999997304557) ▸ P_999997304557 | exact (by norm_num : 999997304512 + 117 = 999997304629) ▸ P_999997304629 | exact (by norm_num : 999997304512 + 195 = 999997304707) ▸ P_999997304707 | exact (by norm_num : 999997304512 + 247 = 999997304759) ▸ P_999997304759 | exact (by norm_num : 999997304512 + 271 = 999997304783) ▸ P_999997304783 | exact (by norm_num : 999997304512 + 297 = 999997304809) ▸ P_999997304809 | exact (by norm_num : 999997304512 + 337 = 999997304849) ▸ P_999997304849 | exact (by norm_num : 999997304512 + 351 = 999997304863) ▸ P_999997304863 | exact (by norm_num : 999997304512 + 357 = 999997304869) ▸ P_999997304869 | exact (by norm_num : 999997304512 + 367 = 999997304879) ▸ P_999997304879 | exact (by norm_num : 999997304512 + 385 = 999997304897) ▸ P_999997304897 | exact (by norm_num : 999997304512 + 409 = 999997304921) ▸ P_999997304921 | exact (by norm_num : 999997304512 + 435 = 999997304947) ▸ P_999997304947 | exact (by norm_num : 999997304512 + 439 = 999997304951) ▸ P_999997304951 | exact (by norm_num : 999997304512 + 441 = 999997304953) ▸ P_999997304953 | exact (by norm_num : 999997304512 + 451 = 999997304963) ▸ P_999997304963 | exact (by norm_num : 999997304512 + 477 = 999997304989) ▸ P_999997304989 | exact (by norm_num : 999997304512 + 489 = 999997305001) ▸ P_999997305001 | exact (by norm_num : 999997304512 + 507 = 999997305019) ▸ P_999997305019 | exact (by norm_num : 999997304512 + 517 = 999997305029) ▸ P_999997305029 | exact (by norm_num : 999997304512 + 541 = 999997305053) ▸ P_999997305053 | exact (by norm_num : 999997304512 + 549 = 999997305061) ▸ P_999997305061 | exact (by norm_num : 999997304512 + 595 = 999997305107) ▸ P_999997305107 | exact (by norm_num : 999997304512 + 625 = 999997305137) ▸ P_999997305137 | exact (by norm_num : 999997304512 + 645 = 999997305157) ▸ P_999997305157 | exact (by norm_num : 999997304512 + 667 = 999997305179) ▸ P_999997305179 | exact (by norm_num : 999997304512 + 675 = 999997305187) ▸ P_999997305187 | exact (by norm_num : 999997304512 + 727 = 999997305239) ▸ P_999997305239 | exact (by norm_num : 999997304512 + 765 = 999997305277) ▸ P_999997305277 | exact (by norm_num : 999997304512 + 775 = 999997305287) ▸ P_999997305287 | exact (by norm_num : 999997304512 + 811 = 999997305323) ▸ P_999997305323 | exact (by norm_num : 999997304512 + 889 = 999997305401) ▸ P_999997305401 | exact (by norm_num : 999997304512 + 919 = 999997305431) ▸ P_999997305431 | exact (by norm_num : 999997304512 + 955 = 999997305467) ▸ P_999997305467 | exact (by norm_num : 999997304512 + 957 = 999997305469) ▸ P_999997305469 | exact (by norm_num : 999997304512 + 967 = 999997305479) ▸ P_999997305479 | exact (by norm_num : 999997304512 + 987 = 999997305499) ▸ P_999997305499

theorem window_bound (k : ℕ) (hk : 1001 ≤ k) : 999997304512 + k ≤ k ^ 4 := by
  have h2 : 1001 * 1001 * 1001 ≤ k * k * k := Nat.mul_le_mul (Nat.mul_le_mul hk hk) hk
  have h4 : 1001 * 1001 * 1001 * k ≤ k * k * k * k := Nat.mul_le_mul_right k h2
  have h3 : k ^ 4 = k * k * k * k := by ring
  omega

theorem msl_erdos681_n999997304512_no_witness_stamp_r1366  : ¬ ∃ k, 0 < k ∧ ¬ Nat.Prime (999997304512 + k) ∧ 1 < 999997304512 + k ∧ k ^ 2 < Nat.minFac (999997304512 + k) := by
  rintro ⟨k, hk, hc, h1, hm⟩
  by_cases hbig : 1001 ≤ k
  · have hsq : Nat.minFac (999997304512 + k) ^ 2 ≤ 999997304512 + k := Nat.minFac_sq_le_self (by omega) hc
    have hlt : (k ^ 2) ^ 2 < Nat.minFac (999997304512 + k) ^ 2 := Nat.pow_lt_pow_left hm (by norm_num)
    have := window_bound k hbig
    have e : (k ^ 2) ^ 2 = k ^ 4 := by ring
    omega
  · have ht := table_ok k (by omega) hk
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ht
    rcases ht with hp | ⟨⟨hq2, hqk⟩, hdv⟩
    · exact hc (shift_prime k hp)
    · have hd : killQ k ∣ 999997304512 + k := Nat.dvd_of_mod_eq_zero hdv
      have := Nat.minFac_le_of_dvd hq2 hd
      have : k ^ 2 = k * k := by ring
      omega

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

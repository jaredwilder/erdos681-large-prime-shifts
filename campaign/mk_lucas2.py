import json
d = json.load(open('ob_lucas_bigbad.json', encoding='utf-8'))
d['id'] = 'erdos681_lucas_prime_999997304513_v2'
d['set_options'] = ['set_option maxRecDepth 100000', 'set_option maxHeartbeats 4000000']
d['definitions'] = """def pmF (b m : ℕ) : ℕ → ℕ → ℕ
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
        simp [Nat.mul_mod, Nat.pow_mod, pow_two]"""
p = d['proof']
p = p.replace("  apply lucas_primality", "  have ev : ∀ e, e < 2 ^ 40 → 5 ^ e % 999997304513 = pmF 5 999997304513 40 e :=\n    fun e he => (pmF_eq 5 999997304513 40 e he).symm\n  apply lucas_primality")
p = p.replace("    rw [key, ZMod.val_one]\n    norm_num", "    rw [key, ZMod.val_one, ev _ (by norm_num)]\n    decide")
p = p.replace("subst h2; norm_num at hv", "subst h2; norm_num at hv; rw [ev _ (by norm_num)] at hv; revert hv; decide")
d['proof'] = p
json.dump(d, open('ob_lucas_bigbad2.json', 'w', encoding='utf-8'), ensure_ascii=False)

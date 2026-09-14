import Mathlib

set_option autoImplicit false

theorem msl_erdos681_one_class_hits_at_most_r1370 (H q r : ℕ) (hq : 0 < q) : ((Finset.range H).filter (fun k => k % q = r)).card ≤ H / q + 1 := by
  have h : ((Finset.range H).filter (fun k => k % q = r)).card ≤ (Finset.range (H / q + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / q)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at hk
      simp only [Finset.coe_range, Set.mem_Iio]
      have := Nat.div_le_div_right (c := q) (Nat.le_of_lt hk.1)
      omega
    · intro a ha b hb hab
      simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at ha hb
      have e1 := Nat.div_add_mod a q
      have e2 := Nat.div_add_mod b q
      simp only at hab
      rw [hab, ha.2] at e1
      rw [hb.2] at e2
      omega
  simpa using h

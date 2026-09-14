set_option autoImplicit false

theorem msl_erdos681_delta3_exact  : ((List.range 105).filter (fun a => Nat.gcd a 105 == 1 && Nat.gcd (a + 2) 105 != 1)).length = 33 ∧ ((List.range 105).filter (fun a => Nat.gcd a 105 == 1)).length = 48 := by rfl

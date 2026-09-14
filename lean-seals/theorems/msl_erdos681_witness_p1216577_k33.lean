set_option autoImplicit false
set_option maxRecDepth 200000

theorem msl_erdos681_witness_p1216577_k33  : (1216576 + 33 == 1103 * 1103 && (List.range 1103).all (fun q => q < 2 || (1216576 + 33) % q != 0) && decide (33 ^ 2 < 1103) && decide (33 ^ 4 < 1216576 + 33)) = true := by decide

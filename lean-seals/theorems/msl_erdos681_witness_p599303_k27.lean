set_option autoImplicit false
set_option maxRecDepth 200000

theorem msl_erdos681_witness_p599303_k27  : (599302 + 27 == 739 * 811 && (List.range 739).all (fun q => q < 2 || (599302 + 27) % q != 0) && decide (27 ^ 2 < 739) && decide (27 ^ 4 < 599302 + 27)) = true := by decide

set_option autoImplicit false

theorem msl_erdos681_witness_p2872981_k41_r2  : (2872980 + 41 == 1693 * 1697 && (List.range 1693).all (fun q => q < 2 || (2872980 + 41) % q != 0) && decide (41 ^ 2 < 1693) && decide (41 ^ 4 < 2872980 + 41)) = true := by rfl

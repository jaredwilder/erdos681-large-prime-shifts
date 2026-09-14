set_option autoImplicit false
set_option maxRecDepth 2000000

def noDivBelow (m B : Nat) : Bool := (List.range B).all (fun q => q < 2 || m % q != 0)

theorem msl_erdos681_bigbad_primality_999997304513  : noDivBelow 999997304513 1000000 = true ∧ 999997304513 < 1000000 * 1000000 := ⟨by decide, by decide⟩

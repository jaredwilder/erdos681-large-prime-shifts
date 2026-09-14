set_option autoImplicit false
set_option maxRecDepth 200000

def isPrimeB (m : Nat) : Bool := 2 ≤ m && (List.range 1800).all (fun q => q < 2 || q * q > m || m % q != 0)
def killedB (p k : Nat) : Bool := isPrimeB (p - 1 + k) || (List.range (k * k + 1)).any (fun q => 2 ≤ q && (p - 1 + k) % q == 0)
def badB (p : Nat) : Bool := isPrimeB p && (List.range 60).all (fun k => k % 2 == 0 || k < 3 || k ^ 4 ≥ p - 1 + k || killedB p k)

theorem msl_erdos681_bad_prime_2999903_certificate  : badB 2999903 = true ∧ (2999903 : Nat) < 1800 * 1800 := ⟨by decide, by decide⟩

set_option autoImplicit false
set_option maxRecDepth 200000
set_option maxHeartbeats 0

def noDivIn (m lo n : Nat) : Bool := match n with
  | 0 => true
  | n + 1 => (m % (lo + n) != 0) && noDivIn m lo n

theorem msl_erdos681_trialdiv_999997304513_2_100000  : noDivIn 999997304513 2 99998 = true := by decide +kernel

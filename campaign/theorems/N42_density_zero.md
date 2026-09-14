MSL_DIALECT v2.1
MSL_PROFILE MSL-F
THEOREM_CANDIDATE N42
  STATEMENT #{p <= X prime : no even h >= 2 with p+h composite and minFac(p+h) > (h+1)^2} = o(pi(X))
  CLAIM_STATUS PROOF_COMPLETE_SOURCE_CONDITIONAL
  WEAKENING_LABEL density zero; NOT parent closure (contract s.30)
DEFINITIONS
  WINDOW for prime p, odd k >= 3 with k^4 < p-1+k; witness at k iff p-1+k composite and minFac(p-1+k) > k^2
  BAD p has no witness at any k in the window
  P_ODD(z) product of odd primes <= z
STEP S1
  CLAIM fix odd K; every odd k <= K lies in the window once p > (K+1)^4
  AUTHORITY KERNEL_CHECKED D7
STEP S2
  CLAIM for p > (K+1)^4 prime, bad p implies for every odd 3 <= k <= K: p-1+k prime or gcd(p-1+k, P_ODD(k^2)) > 1
  PROOF if p-1+k is composite and coprime to all odd primes <= k^2 then, being odd (p odd, k odd), minFac > k^2, a witness
STEP S3
  CLAIM for fixed even d = k-1, #{p <= X : p and p+d prime} << X / log^2 X = o(pi(X))
  AUTHORITY Brun or Selberg upper-bound sieve, classical; SOURCE_PENDING
  CONSEQUENCE the set B1(K) of primes with p-1+k prime for some odd k <= K has density zero among primes
STEP S4
  CLAIM outside B1(K), bad p satisfies p mod M in C(K), M = P_ODD(K^2), C(K) = reduced a mod M with gcd(a-1+k, P_ODD(k^2)) > 1 for all odd 3 <= k <= K
  CLAIM by the prime number theorem in arithmetic progressions for fixed modulus M, #{p <= X : p mod M in C(K)} ~ delta(K) pi(X), delta(K) = |C(K)| / phi(M)
  AUTHORITY PNT-AP fixed modulus, classical; SOURCE_PENDING
STEP S5
  CLAIM limsup_X #{bad p <= X} / pi(X) <= delta(K) for every K
STEP S6
  CLAIM delta(K) -> 0
  SUB U(a) = set of odd k <= K, k >= (2K)^(1/2), with gcd(a-1+k, P_ODD(2K)) = 1; a uniform over reduced residues mod M
  SUB large primes r in (2K, K^2]: residue of a mod r is uniform over nonzero classes and independent of a mod P_ODD(2K) by CRT
  SUB each large r divides a-1+k for at most one k <= K (KERNEL_CHECKED D9)
  SUB conditional on a mod P_ODD(2K), events E_k = {some r in (2K, k^2] divides a-1+k} are negatively associated (Joag-Dev and Proschan 1983, zero-one-at-most-one families, independent unions, monotone functions); SOURCE_PENDING
  SUB P(E_k) = 1 - prod_{2K < r <= k^2, r not dividing k-1} (1 - 1/(r-1)) <= 1 - (1+o(1)) log(2K)/log(k^2) <= 1/2 + o(1) by Mertens
  SUB hence P(a in C(K) | a mod P_ODD(2K)) <= prod_{k in U} P(E_k) <= (1/2 + o(1))^|U|
  SUB mean of |U| over reduced a is mu_red >> K / log K; Montgomery-Vaughan 1986 bounds the second moment about h phi(Q)/Q over ALL a by O(K); restriction to reduced a costs Q/phi(Q) << log K, giving O(K log K); odd k handled by k = 2j+1 and the unit 2^(-1) mod odd Q (SOURCE_PENDING, secondary receipt only; fallback CRT pair-correlation variance O(K polylog K))
  SUB centering: by CRT mu_red = prod_{r|Q}(1 - 1/(r-1)) * sum_k g(k-1), g(n) = prod_{r | n, r | Q} (r-1)/(r-2) = sum_{d | n} h(d), h squarefree with h(r) = 1/(r-2); summing over the k-range gives main term cancelling to mu_all plus error O(prod_{r<=2K}(1 + 1/(r-2))) = O(log K), times prod(1 - 1/(r-1)) << 1/log K: mu_red = mu_all + O(1) (repair route a of audit R8)
  SUB hence for K >= K0, |U| < mu_red/2 forces |U| - mu_all <= -mu_red/4; Chebyshev: P(|U| < mu_red/2) << K log K / mu_red^2 << log^3 K / K
  RESULT delta(K) << log^3 K / K + (1/2 + o(1))^(mu_red/2) -> 0
  REPAIR_LOG RX9 and independent audit R7 S6e DEFECT_FOUND non-fatal; NA sources split: Dubhashi-Ranjan 1998 zero-one lemma plus Joag-Dev-Proschan 1983 closure
CONCLUSION
  STATEMENT S5 with S6 gives density zero
  OPEN_DEBT primary-source receipts for Brun, PNT-AP, Joag-Dev-Proschan, Montgomery-Vaughan; independent audit of S6 negative-association step including exemptions r | k-1 which only shrink P(E_k)
  PRIOR_ART_RISK HIGH; result plausibly classical

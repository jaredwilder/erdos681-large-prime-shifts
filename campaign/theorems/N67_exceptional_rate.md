MSL_DIALECT v2.1
MSL_PROFILE MSL-F
THEOREM_CANDIDATE N67
  STATEMENT #{p <= X prime : p window-bad} << pi(X) (log log X)^3 / (log X)^(1/2)
  CLAIM_STATUS PROOF_SKETCH_UNAUDITED
  WEAKENING_LABEL exceptional-set rate; NOT power saving; NOT parent closure
  DEPS N42 proof object theorems/N42_density_zero.md with its S6 made effective
STEP T1
  CLAIM choose odd K = K(X) maximal with M = P_ODD(K^2) <= X^(1/2); by the prime number theorem theta(K^2) ~ K^2, so K ~ ((1/2) log X)^(1/2)
STEP T2
  CLAIM dyadic range p in (Y, 2Y], Y >= X^(3/4); p > (K+1)^4 holds; bad p lies in B1 or B2 as in N42 S2 S4
STEP T3
  CLAIM #B1 <= sum over odd k <= K of #{p <= 2Y : p, p+k-1 prime} << K Y (log log Y) / log^2 Y
  AUTHORITY Selberg upper-bound sieve with singular series bound S(d) << log log d, uniform in d <= K; SOURCE_PENDING
STEP T4
  CLAIM #B2 <= sum over classes c in C(K) of pi(2Y; M, c) - pi(Y; M, c) <= |C(K)| * 2Y / (phi(M) log(Y/M)) << delta(K) Y / log Y, using Brun-Titchmarsh with M <= X^(1/2) <= Y^(2/3)
  AUTHORITY Montgomery-Vaughan Brun-Titchmarsh pi(x+y; q, a) - pi(x; q, a) <= 2y / (phi(q) log(y/q)); SOURCE_PENDING
STEP T5
  CLAIM delta(K) << log^3 K / K + exp(-c K / log K) with ABSOLUTE implied constants; requires S6 of N42 with effective Mertens and effective Montgomery-Vaughan constants
  GAP effectivity of each o(1) in S6 is asserted, not written
STEP T6
  RESULT #{bad p in (Y, 2Y]} << Y / log Y * ( log^3 K / K + K (log log Y) / log Y ), with K ~ (log X)^(1/2)/sqrt 2
  RESULT first term (log log X)^3 / (log X)^(1/2) dominates the second (log log X)(log X)^(1/2) / log X = (log log X)/(log X)^(1/2)
  RESULT dyadic sum over Y in [X^(3/4), X] plus trivial bound pi(X^(3/4)) gives the statement
OPEN_DEBT
  T5 effectivity written out; T3 T4 sources; independent audit

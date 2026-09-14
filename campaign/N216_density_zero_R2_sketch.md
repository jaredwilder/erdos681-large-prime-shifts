# N216 — density zero for the Erdős #681 prime residual via a small/large prime split (sketch under audit)

Context: N208_density_zero_sketch.md steps 1-4 and 5a, 5c were audited SOUND. Step 5b (Var(|U|)=O(mu)) was a GAP;
step 6 was repaired to: #B2 << pi(X) log K / log X via Selberg's pair sieve over all p <= X (no progressions).
Goal here: Var(|U|) = o(mu^2), which with steps 1-4 and repaired step 6 gives B(X) = o(pi(X)) (no rate).

Notation: K odd ~ (c0 log X)^{1/2}; M = prod odd primes q <= K^2; a uniform over reduced classes mod M.
P(q kills k) = [q <= k^2][q ∤ k-1]/(q-1); U(a) = surviving odd k in [3,K]; mu = E|U| ≍ K/log K.

1. Put y = (1/4) log K and P_y = prod odd q <= y = K^{1/4+o(1)}. Write a = (a_s, a_l) with a_s mod P_y, a_l mod M/P_y (CRT, independent, uniform).
2. Small primes: U_y(a_s) = odd k in [3,K] not killed by any q <= y (with q <= k^2, q ∤ k-1). For k >= y^{1/2} the threshold is inactive, so U_y is periodic in k mod P_y outside O(y^{1/2}) shifts.
   Hence for every a_s: |U_y(a_s)| = (K/2) prod_{q<=y}(1-1/(q-1)) (1 + O(P_y/K)) and, more generally, sum_{k in U_y} f(k) is a_s-independent up to O(P_y max|f|) for f of bounded variation.
3. Large primes: given a_s, for k in U_y, p_k := P(k survives all y < q <= k^2, q ∤ k-1) = prod(1-1/(q-1)) over those q. Exemption factors: q | k-1 with q > y number O(log K / log y), each changes p_k by 1+O(1/q), total 1+O(log K/(y log y)) = 1+o(1).
4. Pairs k != k' in U_y: large q kills both only if q | k-k'. Survival of both = p_k p_k' * prod_{q > y, q ∤ d}(1 + O(1/q^2)) * prod_{q | d, q > y}(1+O(1/q)) = p_k p_k' (1 + O(1/y) + O(log K/(y log y))) = p_k p_k' (1+o(1)) uniformly.
5. E|U|^2 = E_{a_s} [ sum_{k in U_y} p_k + sum_{k != k' in U_y} p_k p_k' (1+o(1)) ] <= mu + (1+o(1)) E_{a_s}(sum_{k in U_y} p_k)^2.
   By 2 (p_k is monotone in k up to 1+o(1) factors), sum_{k in U_y(a_s)} p_k = mu (1+o(1)) for every a_s. So E|U|^2 <= mu + mu^2 (1+o(1)), i.e. Var = o(mu^2).
6. Chebyshev: P(|U| <= mu/2) = o(1). With steps 1-4: #B1 = o(pi(X)); #B2 << pi(X) log K / log X. So B(X) = o(pi(X)).

Numerics (receipted): exact Var/mu = 0.52..0.58 for K = 99..999 (pair_sum.json), 0.49..0.50 for K = 21..51 (Uvar.log, Uvar51.log).

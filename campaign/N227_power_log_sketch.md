# N227 — power-of-log exceptional set for Erdős #681 prime residual, via Gafni–Tao (arXiv 2508.06463) Lemma 2.1 (sketch under audit)

Target (side theorem, not the parent): B(X) = #{X < p <= 2X prime : no odd k>=3 with k^4 < p-1+k, p-1+k composite, minFac(p-1+k) > k^2}.
Claim: for fixed 1/2 < alpha < 1, B(X) << pi(X) loglogX / (logX)^(alpha-1/2).

Parameters: K = floor(log^alpha X) (odd), z = K^2 + 1, H = K/2, log z = 2 alpha loglogX, u = logX/log z -> inf.
R := H * prod_{p<z}(1-1/p) ~ e^{-gamma} H/log z.

Step 1 (window fact). For bad p and k in (K/2, K] odd, k^2 <= K^2 < z. If m = p-1+k has minFac(m) >= z then minFac(m) > k^2, so m must be prime (else witness).
Also even m are not z-rough. Hence every z-rough integer in I_p = (p-1+K/2, p-1+K] is prime. (Checked on all 1203 bad primes in [9.9e11,1e12]: case_split_v2.json.)

Step 2 (split). Case A: I_p contains >= R/2 primes. Case B: I_p contains <= R/2 z-rough integers. Every bad p is in A or B.

Step 3 (case A). 1_A(p) <= (2/R) #{primes in I_p}. Sum over p <= 2X: pairs (p, p+j) both prime, j <= K, Selberg: << X K / log^2 X. So #A << X K/(R log^2 X) << pi(X) log K/ log X.

Step 4 (Lemma 2.1 at polylog z). GT Lemma 2.1 (lines 173-624 of gt.txt) with beta>0 gives (1/X) int_X^{2X} (count_{z-rough}(x,x+H] - R)^2 dx << R.
At beta = 0: Buchstab/de Bruijn step fine (u -> inf). Rosser–Iwaniec level z^s with s = log^{1/2}X fine.
Eq (2.10) (PNT error exp(-c sqrt(log z))) FAILS at polylog z; repair: define R by the exact product and note
V(z)/prod_{p<z}(1-1/p)^2 = 4 prod_{2<p<z}(1-1/(p-1)^2) = 2S(1+O(1/z)) (convergent product tail), so no PNT needed.
Primes H<p<z do not divide m <= H/2; they change the pair main term by 1+O(1/H): error R^2/H << R.
(2.12) singular average from [16] unchanged. Final term H log H/log^2 z = O(R) since log H/log z = 1/2.
Numerics at u ~ 2 (off regime): Var/mean ~ 0.73 (gt_var.json, gt_flag2.json).

Step 5 (case B measure). eps = 1/(8 log z). For x in J_p = [p-1+K/2, p-1+K/2+eps K], (x, x+H] has <= R/2 + eps K <= (5/8)R z-rough integers, so x in E := {x : count <= (5/8)R}. Chebyshev: meas(E cap [X,2X]) << X/R.

Step 6 (counting case B). N(x) = #{case-B p : x in J_p} <= #{primes in an interval of length eps K}. #B * eps K = int_E N.
Cauchy–Schwarz: int_E N <= meas(E)^{1/2} (int N^2)^{1/2}; int N^2 << X eps K / log X + X (eps K)^2/log^2 X << X eps K/log X (eps K < log X).
So #B << X/(R eps K log X)^{1/2} << X loglogX/(K (log X)^{1/2}) = pi(X) (logX)^{1/2} loglogX / K.

Step 7. B(X) << pi(X) loglogX/(logX)^(alpha-1/2) + pi(X) loglogX/logX.

Sources: Gafni–Tao arXiv 2508.06463 (bytes literature/gafni_tao_2508.06463.pdf); Selberg pair upper bound; Buchstab/de Bruijn; Rosser–Iwaniec (Friedlander–Iwaniec Opera de Cribro Thm 6.9 as cited by GT); [16] of GT for (2.12).

## Audit repairs (W97) and H1 extension (N231, unaudited)
Repairs: Step 4 first moment by the sieve fundamental lemma at z = K^2+1 (not Buchstab); Step 5 eps = 1/(40 log z).
N231: take alpha > 1 (e.g. alpha = 2, K = log^2 X). Steps 1-3 unchanged (#A << pi(X) log z/log X).
Step 6 with eps K > log X: int N^2 << X (eps K)^2 / log^2 X, so #B << (1/eps K)(X/R)^{1/2}(X (eps K)^2/log^2 X)^{1/2} = pi(X)/R^{1/2}.
At alpha = 2: B(X) << pi(X) loglogX / log X, i.e. X loglogX / log^2 X on (X,2X] — same order as Gafni–Tao's X/log^2 X for #682 up to loglog.

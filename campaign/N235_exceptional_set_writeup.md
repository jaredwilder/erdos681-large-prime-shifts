# Erdős #681 — the exceptional set of prime residuals is O(X log log X / log² X)

**Status:** audited sketch (three hostile readers: W83, W97, W100). Not kernel-checked. Not the parent problem.
**Parent (open):** for all large n there is k with n+k composite and p(n+k) > k². Equivalent (kernel bundle) to: every large prime p has odd k ≥ 3 with p−1+k composite and minFac(p−1+k) > k².

## Theorem (side result)
Let B(X) be the number of primes p ∈ (X, 2X] with no odd k ≥ 3, k⁴ < p−1+k, such that p−1+k is composite with minFac(p−1+k) > k². Then

B(X) ≪ X log log X / log² X.

## Proof outline
Parameters: K = ⌊log² X⌋ (odd), z = K²+1, H = K/2, R = H·∏_{p<z}(1−1/p) ≍ log² X / log log X.

1. **Window fact.** For bad p and odd k ∈ (K/2, K]: k² < z, so an integer in I_p = (p−1+K/2, p−1+K] with no prime factor below z is prime (else it witnesses). Primes in I_p exceed z, so #primes(I_p) = #z-rough(I_p). (Checked on all 1203 bad primes in [9.9·10¹¹, 10¹²], `case_split_v2.json`.)
2. **Split.** Case A: #primes(I_p) ≥ R/2. Case B: #z-rough(I_p) ≤ R/2.
3. **Case A.** 1_A(p) ≤ (2/R)·#primes(I_p); summing, Selberg's pair upper bound uniformly in shifts j ≤ K and the singular-series average give #A ≪ XK/(R log² X) ≪ X log z / log² X.
4. **Second moment (Gafni–Tao Lemma 2.1 transferred).** For x ∈ [X, 2X+2K], c(x) = #z-rough integers in (x, x+H]: (1/X)∫(c−R)² ≪ R. First moment by the dimension-1 fundamental lemma with R the exact product (Mertens approximation is insufficient); second moment by the dimension-2 Rosser–Iwaniec sieve at level z^s, s = log^{1/2} X, main term via V(z)/∏(1−1/p)² = 2S(1+O(1/z)) (no PNT), and the singular-series average ∑_{m≤w}∏_{p|m,p>2}(p−1)/(p−2) = 2w/S + O(log w).
5. **Case B measure.** With ε = 1/(40 log z), every x ∈ J_p = [p−1+K/2, p−1+K/2+εK] has c(x) ≤ 5R/8; Chebyshev gives meas(E) ≪ X/R.
6. **Case B count.** #B·εK = ∫_E N(x)dx with N(x) ≤ #primes in a window of length εK; Cauchy–Schwarz and the pair sieve (εK > log X, off-diagonal dominates) give #B ≪ X/(R^{1/2} log X) ≪ X (log log X)^{1/2} / log² X.
7. B(X) ≤ #A + #B ≪ X log log X / log² X.

## Relation to prior work
Method: A. Gafni, T. Tao, *Rough numbers between consecutive primes*, arXiv:2508.06463 (2025), who prove N(X) = O(X/log² X) for the sibling Erdős #682. The #681 statement above was not found in the acquired corpus (`literature/corpus_n219.json`); novelty is **unknown**, not cleared.

## Receipts
`literature/gafni_tao_2508.06463.pdf` (sha256 28417eae…), `literature/ms_0409258.pdf` (4814387d…), `case_split_v2.json` (58ddadb5…), `topdown.log` (825c9a38…), `N208_density_zero_sketch.md`, `N216_density_zero_R2_sketch.md`, `N227_power_log_sketch.md`.

# N208 — density-zero exceptional set for Erdős #681 prime residual (sketch under audit)

Target (side theorem, NOT the parent): B(X) = #{p ≤ X prime : no odd k≥3 with k^4 < p-1+k, p-1+k composite, minFac(p-1+k) > k^2}.
Claim: B(X) ≪ π(X) · log log X / (log X)^{1/2}.

1. Fix K odd, K ~ (c0 log X)^{1/2}, c0 < 1/2. Let M = ∏ odd primes q ≤ K^2, so log M ~ K^2 ≤ (1/2) log X.
2. For a reduced class a mod M let U(a) = {odd 3 ≤ k ≤ K : no odd prime q ≤ k^2 with q ∤ k-1 has q | a-1+k}.
   (If q | k-1 and q | p-1+k then q | p; so exempt q never divide.) For p ≡ a, k ∈ U(a) means p-1+k has no prime factor ≤ k^2 (p-1+k odd).
   Hence if p is bad (and large, so k^4 < p for all k ≤ K), every k ∈ U(a) has p-1+k prime.
3. B ⊆ B1 ∪ B2, B1 = {p : |U(p mod M)| ≤ μ/2}, B2 = {p bad : |U| > μ/2}, μ = E_a |U(a)|.
4. B1: Brun–Titchmarsh (Montgomery–Vaughan) π(X;M,a) ≤ 2X/(φ(M) log(X/M)) ≤ (4+o(1)) X/(φ(M) log X). So #B1 ≤ (4+o(1)) π(X) · P_a(|U| ≤ μ/2) ≤ (4+o(1)) π(X) · 4 Var/μ^2.
5. CRT: a mod q independent uniform on q-1 nonzero classes. P(k∈U) = ∏_{q≤k^2, q∤k-1} (1 - 1/(q-1)) =: P_k.
   Pairs: q kills both k,k' iff q | k-k'. Pair factor 1 - 2/(q-1) + [q|k-k']/(q-1). So P(k,k'∈U) = P_k P_k' S*(k-k') with S* a truncated odd-prime pair singular series (boundary factors bounded).
   Var = Σ P_k(1-P_k) + Σ_{k≠k'} P_k P_k' (S*(k-k') - 1).
   Goldston (quoted as eq (47)/(48) in Montgomery–Soundararajan, arXiv math/0409258): Σ_{d1≠d2≤h} S({d1,d2}) = h^2 - h log h + Bh + O(h^{1/2+ε}).
   Hence second sum ≪ P^2 K log K ≍ K/log K ≍ μ; Var = O(μ).
   μ ≍ K/log K (Mertens), so #B1 ≪ π(X) log K / K.
6. B2 (Markov): 1_bad ≤ Z(p)/|U| ≤ 2Z(p)/μ, Z(p) = #{k∈U : p-1+k prime}. Σ_{p≡a} Z(p) = Σ_{k∈U(a)} #{p ≤ X, p≡a (M), p and p-1+k prime}
   ≤ C S(k-1) X / (φ(M) log^2(X/M)) (Selberg upper sieve in progressions, M ≤ X^{1/2}). Summing: #B2 ≪ π(X) K/(μ log X) ≪ π(X) log K / log X.
7. Total: B(X) ≪ π(X) log K / K ≍ π(X) log log X / (log X)^{1/2}.

Numerics (receipted): Var/μ = 0.49, 0.46, 0.48, 0.50, 0.50 at K = 21,29,37,45,51 (Uvar.log, Uvar51.log).
Open sources: Montgomery–Vaughan Brun–Titchmarsh; Selberg pair sieve in progressions (Halberstam–Richert); Goldston original.

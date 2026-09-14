# Erdős #681 — audited exceptional-set sketch and higher-moment frontier

**Author:** Jared Wilder  
**Recovered / audited:** 2026-09-14  
**Status:** audited proof sketch / source-binding debt; NOT parent closure

Let `B(X)` denote the primes `p in (X,2X]` for which the prime-residual version of Erdős #681 has no witness: there is no even `h>=2` with `p+h` composite and

\[
(h+1)^2 < P^-(p+h).
\]

A later part of the campaign developed a substantially stronger exceptional-set argument than its terminal narrative foregrounded. After two hostile audits and explicit repairs, the surviving target is

\[
\boxed{B(X) \ll \frac{X\log\log X}{\log^2 X}.}
\]

Equivalently,

\[
B(X)\ll \pi(X)\frac{\log\log X}{\log X}.
\]

This page records the architecture and its remaining authority debt. It deliberately does **not** promote the statement to a finished theorem yet.

## Parameters

Take

\[
K=\lfloor\log^2 X\rfloor,\qquad z=K^2+1,\qquad H\asymp K/2,
\]

and define the exact rough-number mean

\[
R=H\prod_{q<z}\left(1-\frac1q\right)
\asymp \frac{\log^2 X}{\log\log X}.
\]

For a bad prime `p`, restrict to the residual shifts corresponding to the upper half of the `K`-window. Every `z`-rough endpoint there must be prime: if such an endpoint were composite, its least prime factor would exceed `K^2`, hence exceed the square of its actual shift and give a witness.

Thus every bad prime lies in one of two cases.

## Case A — the interval contains many primes

If the interval contains at least `R/2` rough numbers, then it contains at least `R/2` primes.

A Selberg upper-bound sieve, summed over the possible short shifts, gives

\[
\#A\ll \frac{XK}{R\log^2X}
\asymp \frac{X\log\log X}{\log^2X}.
\]

This is the dominant term in the repaired second-moment argument.

## Case B — the rough count is abnormally low

If the rough count is at most `R/2`, slide the interval through a starting range of length

\[
\varepsilon K,\qquad \varepsilon=\frac1{40\log z}.
\]

The constant `1/40` is load-bearing: an earlier `1/(8 log z)` choice was caught and retracted by hostile audit.

The repaired Gafni–Tao-style moment calculation uses the exact product defining `R`, not a Mertens approximation. At polylogarithmic `z`, the dimension-one fundamental lemma supplies the first moment with the required absolute precision, while the pair-sieve / singular-series calculation gives variance `O(R)`.

Consequently the set `E` of starting points with rough count below the fixed fraction of `R` has measure

\[
|E|\ll X/R.
\]

Counting bad primes whose sliding intervals lie in `E`, and applying Cauchy–Schwarz together with the short-shift prime-pair upper bound, yields the smaller subsidiary estimate

\[
\#B_{\mathrm{low\ rough}}
\ll
\pi(X)\frac{\sqrt{\log\log X}}{\log X}.
\]

Hence Case A is the bottleneck in this repaired second-moment route.

## Audit history

The route was repaired several times before reaching this form:

- roughness threshold corrected from `K^2/4` to `K^2+1`;
- polylogarithmic-`z` first moment changed from a Buchstab/Mertens approximation to the sieve fundamental lemma with the exact product mean;
- sliding constant corrected from `1/(8 log z)` to `1/(40 log z)`;
- Case-B arithmetic sharpened and shown to be smaller than the total bound.

Two independent hostile audits of the repaired route reported no fatal defect. The remaining debt is source-binding, uniformity, and priority—not permission to silently call the parent closed.

## Closest prior method

The method is explicitly adjacent to Ayla Gafni and Terence Tao, *Rough numbers between consecutive primes*, arXiv:2508.06463 (2025). The campaign archive includes the paper and extracted text because its rough-number moment machinery is load-bearing context.

Historical novelty for the exact #681 transfer has not yet been certified.

## Remaining debt before theorem promotion

The following must be written and checked in one clean derivation:

1. uniform Selberg upper-bound sieve over shifts `<=K=log^2 X`;
2. Rosser–Iwaniec / fundamental-lemma first moment at `z=K^2+1` with exact-product main term and sufficient absolute error;
3. pair singular-series average and the range extension to `[X,2X+O(K)]`;
4. dedicated literature/priority court for this exact #681 statement.

## New KBK frontier — higher moments

The forensic pass after the campaign found a route the internal agent did not pursue. Gafni–Tao's higher-moment machinery suggests combining a `2r`-th rough-number moment for Case B with an `r`-th factorial-moment upper-bound sieve for the prime-rich Case A.

The natural target is

\[
B(X)\stackrel{?}{\ll_r}
\frac{X(\log\log X)^r}{\log^{r+1}X}
\]

for every fixed `r`.

If both uniform transfers survive hostile court, this would imply

\[
B(X)\ll_A X/\log^A X
\]

for every fixed `A`.

**This is a research target, not a theorem.** It is recorded because it materially changes the next analytic campaign and was absent from the internal agent's terminal report.

Neither the audited-sketch bound nor arbitrary log-power sparsity would by itself close the parent. The terminal mission remains elimination of all sufficiently large bad primes or construction of arbitrarily large bad primes.

# Erdős #681 — exact finite bad-prime covering certificate

**Author:** Jared Wilder  
**Date:** 2026-09-14  
**Status:** exact deterministic reformulation of a finite residual window; designed for the parent-close program.

The kernel-checked parent↔residual equivalence reduces Erdős #681 to sufficiently large primes. Write the residual shift as `k=h+1`, so `k` is odd and `k>=3`, and the candidate endpoint is

\[
m_k=p-1+k.
\]

This note isolates the exact finite object induced by a prime that has no witness in a prescribed initial shift window.

## Theorem — finite bad-prime certificate

Let `p` be an odd prime and let `K>=3` be odd. Assume

\[
(K+1)^4<p.
\]

Then every odd `k` with `3<=k<=K` automatically satisfies

\[
k^4<p-1+k.
\]

Therefore the following are equivalent:

1. there is **no** residual witness among the odd shifts `3<=k<=K`;
2. for every odd `k` in that interval, either
   - `p-1+k` is prime, or
   - there exists a prime `q<=k^2` such that
     \[
     q\mid p-1+k.
     \]

If `p-1+k` is composite and has no prime divisor at most `k^2`, then its least prime factor is greater than `k^2`; together with the fourth-root size condition this is exactly a residual witness. The converse is immediate.

## Automatic restriction 1 — the factor cannot divide `k-1`

Because

\[
q\le k^2\le K^2<p,
\]

the kernel theorem `msl_erdos681_divisor_of_shift_is_free` applies. Thus every composite non-witness certificate satisfies

\[
\boxed{q\nmid k-1}.
\]

## Automatic restriction 2 — every large factor hits at most one shift

For any prime `q>K`, the kernel theorem `msl_erdos681_large_prime_hits_one_shift` implies that `q` cannot divide two different endpoints in the same `K`-window. Hence

\[
\boxed{q>K\quad\Longrightarrow\quad q\text{ certifies at most one }k.}
\]

Large primes are therefore singleton covering resources.

## Coherent residue-cover form

For fixed prime `q`,

\[
q\mid p-1+k
\quad\Longleftrightarrow\quad
k\equiv1-p\pmod q.
\]

Thus all shifts killed by `q` lie in one residue class, and the residue classes for different primes are not freely chosen: all are reductions of the same integer `1-p`.

Define

\[
C_p(q;K)=\{k:\ 3\le k\le K,\ k\text{ odd},\ q\le k^2,\ k\equiv1-p\pmod q\}.
\]

Then a `K`-bad prime produces

\[
\{3,5,\ldots,K\}
\subseteq
\mathcal P_p(K)\ \cup\!
\bigcup_{q\le K^2\atop q\text{ odd prime}} C_p(q;K),
\]

where

\[
\mathcal P_p(K)=\{k:\ p-1+k\text{ is prime}\}.
\]

The union is subject to:

- `q` cannot kill a shift with `q | k-1`;
- `q>K` occurs in at most one shift;
- all residue classes are CRT-coherent through the single prime `p`.

## Parent-close significance

An almost-all-primes theorem estimates how often these certificates occur. The parent asks for more: prove that **no such certificate exists for any sufficiently large prime**, or construct arbitrarily large primes carrying one.

This is the deterministic object for the universalization phase of the #681 close mission. No density-one, finite-census, or conditional statement substitutes for either terminal outcome.

# Erdős 681: large prime factors after a short shift

[Erdős problem 681](https://www.erdosproblems.com/681) asks whether, for all sufficiently large `n`, there is some `k > 0` with `n+k` composite and the smallest prime factor of `n+k` bigger than `k²`.

**The parent problem is still open.** This repository is the canonical subject home for the September 2026 #681 program: exact reductions, Lean seals, finite certificates, computations, analytic work, route kills, KBK, and the continuing terminal-close program.

A campaign is not classified by whether the parent closed. Exact theorems, counterexamples below any eventual threshold, obstructions, falsified routes, and sharper coordinates remain first-class outputs.

## What's proved in Lean

`lean-seals/theorems/` and `lean-seals/receipts/` contain the formal layer. Important accepted results include:

- **Exact parent ↔ residual equivalence.** The original eventual statement is equivalent to the prime-residual problem, so the hard case can be studied without weakening the quantifiers.
- Fourth-root necessity and parity pruning.
- If a prime divides `k-1`, it is unavailable as a killing factor for the corresponding residual endpoint.
- A prime larger than a `K`-window can hit at most one shift in that window.
- **δ(3)=11/16** exactly.
- Explicit positive witnesses at several primes.
- **A complete kernel-checked bad integer at essentially `10^12`:**

  ```text
  n = 999,997,304,512
  ```

  has no valid witness for **any** positive `k`.

The actual formal source and receipt for that finite theorem are already in this repo:

```text
lean-seals/theorems/msl_erdos681_n999997304512_no_witness_stamp_r1366.lean
lean-seals/receipts/erdos681_n999997304512_no_witness_stamp_r1366.cable.json
```

Thus any eventual threshold in a positive solution must exceed `999,997,304,512`.

## Exact deterministic bad-prime object

The latest forensic pass isolates the finite object carried by a bad residual prime. For `p>(K+1)^4`, every admissible odd shift `3<=k<=K` must be either:

- a prime endpoint `p-1+k`; or
- composite with some prime divisor `q<=k^2`.

These killing primes are highly constrained:

- `q` cannot divide `k-1`;
- `q>K` can kill at most one shift;
- for fixed `q`, killed shifts all lie in the coherent residue class `k ≡ 1-p (mod q)`.

See:

- [`forensics/2026-09-14-bad-prime-cover-certificate.md`](forensics/2026-09-14-bad-prime-cover-certificate.md)

This coherent residue-cover + prime-exception object is the current deterministic universalization target for the parent close.

## Analytic exceptional-set frontier

The original campaign contains the density-zero development (`campaign/N208`, `N216`), the sharper intermediate argument (`N227`), and the exceptional-set writeup (`N235`).

A full forensic pass through the later rounds and hostile audits found that the campaign went substantially further than its terminal narrative suggested. After repairs, the surviving audited target is

\[
B(X)\ll \frac{X\log\log X}{\log^2X},
\]

where `B(X)` counts bad residual primes in `(X,2X]`.

The low-roughness case is actually smaller; the bottleneck is the prime-rich case. This remains an **audited proof sketch with source-binding debt**, not yet a promoted theorem and not a parent close.

See:

- [`forensics/2026-09-14-exceptional-set-audit-and-higher-moment-frontier.md`](forensics/2026-09-14-exceptional-set-audit-and-higher-moment-frontier.md)

That forensic pass also identified a new higher-moment route absent from the internal agent's terminal report. The research target is, for fixed `r`,

\[
B(X)\stackrel{?}{\ll_r}\frac{X(\log\log X)^r}{\log^{r+1}X},
\]

which, if the required uniform transfers survive hostile court, would imply log-power sparsity of arbitrary fixed order. This is explicitly **not yet a theorem**.

## Computation

The repository preserves the finite estate rather than using it as an asymptotic substitute:

- atlas through `3×10^6`, exact `δ(K)` for small `K`, and exact `|U|` distributions;
- top-down census material in `[10^11,10^12]`;
- largest recorded bad residual prime below `10^12`: `999,997,304,513`;
- corresponding fully formal bad integer `999,997,304,512`;
- C programs and raw/derived receipts.

Finite computation is evidence and theorem material where fully certified; it is not the parent close.

## Route kills are KBK

`CAMPAIGN_STATE.md` and the campaign archive preserve routes that were structurally killed or shown insufficient: large-sieve directionality, local-density/witness-rate confusion, absence of a deterministic small-prime floor, smooth-`p-1` size traps, and entropy losses in naive constellation union bounds.

Those are retained because they sharpen the live route. They are not labelled campaign failures.

## Canonical layout

```text
campaign/          main raw/derived campaign estate
lean-seals/        kernel-checked theorem sources and receipts
msl-campaign-001/  earlier automated campaign
forensics/         post-campaign raw-byte mining and upgraded public state
README.md          reader-facing canonical frontier
```

## Terminal target

Nothing weaker than the parent counts as closure.

A positive close must prove that **all sufficiently large residual primes admit a witness**. A negative close must produce an unconditional infinite/arbitrarily-large bad family.

Density zero, arbitrarily strong finite computation, RH-conditional statements, or weaker exponents are theorem/KBK outputs—not terminal substitutes.

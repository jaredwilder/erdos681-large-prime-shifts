# Erdős 681: large prime factors after a short shift

[Erdős problem 681](https://www.erdosproblems.com/681) asks whether, for all large n, there is some k > 0 with n + k composite and the smallest prime factor of n + k bigger than k².

**It's still open.** This repository is the complete record of a campaign on it from September 13, 2026: the Lean theorems, the computations, the proof write-ups and the routes that failed.

## What's proved in Lean

`lean-seals/theorems/` has 71 files. According to `lean-seals/receipts/`, the Lean kernel accepted 48, 22 were never confirmed, and one never reached the kernel. The accepted ones include:

- **The reduction:** the problem as stated in formal-conjectures is equivalent to a simpler residual statement. It's one bundled file of twelve declarations, with both directions checked.
- A fourth-root necessity condition. Even shifts never help (parity). A prime dividing k − 1 is automatically harmless. A single large prime can only block one shift.
- **δ(3) = 11/16** exactly.
- Explicit witnesses at p = 167, 1069, 2803, 218069, 599303, 1216577 and 2872981.

## What's proved on paper, and what's only a sketch

In `campaign/`:
- `N208`, `N216`: the "bad" primes have density zero. The proof is complete but relies on cited results: Brun's sieve, the prime number theorem in progressions, Joag-Dev–Proschan and Montgomery–Vaughan. It is not the full problem.
- `N227`: a sharper bound, bad primes ≪ π(X)(log log X)² / (log X)^½. This one is a sketch and hasn't been audited.
- `N235`: a write-up of the exceptional set.

## Computation

- An atlas up to 3×10⁶, exact δ(K) for K ≤ 29, and the exact distribution of |U|.
- Census windows, plus a top-down census of [10¹¹, 10¹²]. The largest bad prime below 10¹² is 999,997,304,513. The full log is `bad_to_1e12.log.gz`.
- The C programs (`Udist.c`, `Uvar.c`) sit next to their compiled binaries.

## Routes that didn't work

`CAMPAIGN_STATE.md` lists them: the large sieve goes the wrong way; local density isn't a witness rate; there's no deterministic small-prime floor; smooth p − 1 coverings hit a size trap; and a union bound over constellations loses to entropy.

`msl-campaign-001/` has the earlier automated campaign on the same problem.

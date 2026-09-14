MSL_DIALECT v2.1
MSL_PROFILE MSL-F
TARGET T681
  STATEMENT exists N0 forall n>=N0 exists k>0, n+k composite, minFac(n+k) > k^2
  SOURCE erdosproblems.com/681 OPEN; formal-conjectures 681.lean hash 50331a34
  CAMPAIGN epoch 34, absolute rounds 1214..1258, contract ERDOS_681_100_ROUND_PARENT_CLOSE_CONTRACT_2026-09-13
CLOSE_STATUS
  PARENT OPEN
  COURTS source OPEN; semantic binding KERNEL_CHECKED via D4 D5 D8; mathematical truth OPEN; kernel scope reduction only
KERNEL_LEDGER
  D1 fourth-root necessity cable/receipts/erdos681_fourth_root_necessity.cable.json
  D2 parity kills even shifts cable/receipts/erdos681_parity_kills_even_shift.cable.json
  D3 k=1 witness when n+1 composite cable/receipts/erdos681_k1_composite_witness.cable.json
  D4 residual implies parent cable/receipts/erdos681_residual_implies_parent.cable.json
  D5 parent implies residual cable/receipts/erdos681_parent_implies_residual_r2.cable.json
  D6 q | k-1 exempts q cable/receipts/erdos681_divisor_of_shift_is_free.cable.json
  D7 fixed K inside window cable/receipts/erdos681_fixed_K_in_window.cable.json
  D8 formal-conjectures IsLPF bridge cable/receipts/erdos681_fc_lpf_bridge.cable.json
  D9 large prime hits one shift cable/receipts/erdos681_large_prime_hits_one_shift.cable.json
  D10 witness p=167 k=3 cable/receipts/erdos681_witness_p167_k3.cable.json
  D11 residue motif decoding cable/receipts/erdos681_motif_k3_killers.cable.json
  D12 delta(3) = 11/16 cable/receipts/erdos681_delta3_exact_r2.cable.json
  D13 exempt family divisibility cable/receipts/erdos681_exempt_family_core_r2.cable.json
  D14 N42 S6 scale comparison cable/receipts/erdos681_N42_S6_mertens_ratio_core.cable.json
  D16 N42 S2 oddness cable/receipts/erdos681_N42_S2_endpoint_odd.cable.json
  D17 N67 T1 modulus instance cable/receipts/erdos681_N67_T1_modulus_instance.cable.json
  D18 witness p=1069 k=5 cable/receipts/erdos681_witness_p1069_k5_r2.cable.json
  D20 N49 size trap H=41 cable/receipts/erdos681_N49_size_trap_H41.cable.json
  D21 BUNDLE T681 iff T681R, twelve declarations one file cable/receipts/erdos681_bundle_equivalence.cable.json
  D22 witness p=2803 k=7 cable/receipts/erdos681_witness_p2803_k7.cable.json
  D23 witness p=2872981 k=41 cable/receipts/erdos681_witness_p2872981_k41_r3.cable.json
AUDITS
  R7 N42 independent audit SURVIVED_WITH_REPAIR (variance O(K log K))
  R8 N67 audit T5 GAP constants; N42 centering GAP repaired D19 by mu_red = mu_all + O(1), W29 numeric support; repair lines unaudited
LATER_EVIDENCE
  W16 top-down census [1e11,1e12] per-chunk receipts topdown.log; largest bad prime below 1e12 is 999997304513
  W30 W31 record witnesses are two-prime near-square endpoints, Fermat offset b <= 1.6 m^(1/4)
  S7 Erdos 680 statement fc_680.lean; S8 682 not acquired
  MANIFEST.sha256 pins 125 stable files
THEOREM_CANDIDATES
  N42 bad primes density zero; PROOF_COMPLETE_SOURCE_CONDITIONAL (Brun, PNT-AP, Joag-Dev-Proschan, Montgomery-Vaughan); NOT parent
  N67 bad primes << pi(X) (log log X)^2 / (log X)^(1/2); PROOF_SKETCH_UNAUDITED; NOT parent
COMPUTATION_LEDGER
  W1 atlas to 3e6: atlas_3000000.json
  W2 [2e7,3e7] bad fraction 0.1234: falsifier_N1.json
  W6 W7 W12 W13 segmented census windows: seg_*.json
  W10 exact delta(K) K<=29: delta_K.json
  W11 exact |U| distribution: U_dist.json
  W14 C engine calibrated: c_check.log
  W16 top-down census [1e11,1e12] in progress: topdown.log
  W19 residue motif: residue_bias.json
  W20 W21 heuristic model at 1e12: sum_w.json hybrid_*.json
HEURISTIC_LEDGER
  N78 log P(bad) ~ sum_k log(1 - w_k), within 0.8 nats at 1e12; heuristic verdict TRUE
KILLED_ROUTES
  N19 large sieve wrong inequality direction
  N26 local density as witness rate
  N39 deterministic small-prime floor
  N49 smooth p-1 structured covering, size trap
  N51 constellation union bound, entropy
  N69 bilinear CRT coupling of large shifts
  N71 Ford divisor-in-interval
  KT1 uniform-flattening Jacobsthal, source-conditional
BARRIER
  N48 N68: parent needs control of primes in classes of modulus exp(X^(1/2)), far above X
OPEN_REQUESTS
  R4 R5 original Erdos source and Rankin exponent result
  R6 operator decision on continuation

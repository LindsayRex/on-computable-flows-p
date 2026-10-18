# exp_008 — scorecard (filled LAST)

Evidence calculus inherited from the engineering standard:
`C_D^exp = φ_method · φ_repro · φ_discriminant · φ_determinism`
(each φ ∈ {0, 0.5, 1}; the product is the score — one hard zero zeroes the
delivery).

| φ | gate | outcome | evidence |
|---|---|---|---|
| φ_method | brief frozen before run; predictions derived (M1); rejection criteria pre-registered; nothing moved after | 0.5 | brief frozen and committed before any computation, but CAL-2 failed as frozen and the region family had to be amended (amendments 1, 2, both registered and committed BEFORE the readings they govern); the amendment discipline held, the original operationalisation did not |
| φ_repro | manifest complete (M7); a stranger could re-run cold; artifacts frozen with shas | 1 | runs/run_manifest.json complete; five commands reproduce everything from the committed scripts; no external inputs |
| φ_discriminant | calibration passed AND must-fail watched failing (M2); baselines bracket; control that can fail present | 1 | CAL-1 exact; CAL-3 ruler 0.9096 vs 0.906±0.03 and harmonic 1.2e-15; CAL-4 divergence test watched endorsing a chaotic field; CAL-2's failure itself the discriminant working; r>1 no-pass control could have failed and did not (0 of 429 rows) |
| φ_determinism | seeds pinned / symbolic stated; tolerances pre-declared; error budget attributed (M3) | 1 | seeds 0–7 pinned; all tolerances in brief §6 before the run; grid-vs-vertex sup agreement and 0 refinement flips close the discretisation worry; lattice Benettin instrument bug caught from its own output, fixed, rerun, logged |

**C_D^exp = 0.5**

## Claims

- **Significant:** (i) lens materiality on a chaotic family: identity lens certifies nowhere (0/257 rows), diagonal lenses certify locally with flips at r = 0.85/0.65/0.45 for rho = 0.1/0.3/0.5 against the derived 1−rho (results/ramp.jsonl, summary.toml); (ii) soundness: 0 violations in 82 contraction checks, worst ratio vs the e^{−st} bound 0.9997 (results/soundness.jsonl); (iii) lattice: pre-run threshold c* = 28.73 gave 0 sync failures in all 72 runs at c ≥ 0.25c*, measured c_sync = 2.12, price ratio 13.6 (results/lattice.jsonl); (iv) blind subspace: lambda1 on the sync manifold 0.9051 vs single-cell 0.9096 (within declared ±0.05).
- **NOT significant / not shown:** no global contraction certificate exists on this family in any constant diagonal lens (shown only for the swept lenses and boxes, not proved for all metrics); the lambda1 zero crossing at r ≈ 22.5 is finite-time and ±0.5 at best; nothing about chaos in general, SAT dynamics, or refusal implying intractability.
- **Verdict rung (M6):** empirical.
- **Counterexamples emitted (M5):** CAL-2-as-frozen is a counterexample to the operationalisation "global stability regime ⇒ trap-region contraction certificate" (vertex sup +21.76 at r=0.5; results/calibration.toml). None against the manuscript's claims.

## Declared limits

One system family (Lorenz-type), one topology (ring, N=8), diagonal lenses only; grid-certified passes (vertex sup exact for boxes, stated); finite-time lambda1 near onset. This run says the diagnostic behaved as derived on a constructed chaotic family; it cannot conclude anything beyond it. Confirmed unchanged from brief §13 after the run.

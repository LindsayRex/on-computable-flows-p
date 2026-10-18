# exp_009 — scorecard (filled LAST)

Evidence calculus inherited from the engineering standard:
`C_D^exp = φ_method · φ_repro · φ_discriminant · φ_determinism`
(each φ ∈ {0, 0.5, 1}; the product is the score — one hard zero zeroes the
delivery).

| φ | gate | outcome | evidence |
|---|---|---|---|
| φ_method | brief frozen before run; predictions derived (M1); rejection criteria pre-registered; nothing moved after | 1 | brief at d4201ca before any computation; P1-P5 with rejection criteria in `experiment/exp_method.md` sections 4 and 6; Amendments 1-3 registered and committed before the readings they govern (ae96069, 6965a5c, 54d2c23); no reading preceded its gate |
| φ_repro | manifest complete (M7); a stranger could re-run cold; artifacts frozen with shas | 1 | `runs/run_manifest.json` (python 3.11.15, numpy 2.4.6, scipy 1.17.1, brief and amendment shas); seeds 0-7 pinned, instances deterministic per (seed, m, kappa); `src/run_main.py` is idempotent and resumable (verified: re-run adds 0 rows); artifacts committed at 3825b36 |
| φ_discriminant | calibration passed AND must-fail watched failing (M2); baselines bracket; control that can fail present | 1 | CAL-1..4 pass in `results/calibration.toml`; CAL-3 wrong certificate watched violated (claimed 2.16e-5 vs measured 104.65); CAL-4 failed as frozen before its amendment (kept as a result); baselines bracket (random floor, SVD, reference ceiling); identity-lens control refused 176/176 |
| φ_determinism | seeds pinned / symbolic stated; tolerances pre-declared; error budget attributed (M3) | 1 | seeds pinned; all tolerances in the frozen brief; float64 cancellation floor located by the CAL-4 failure, matched to the brief section 10 budget, governed by Amendments 1 and 3 (fifteen orders of separation at the degenerate classification) |

**C_D^exp = 1.0**

## Claims

- **Significant:** P1, P2 (48/48 refusals, sigma = mu to machine precision),
  P3 (identity lens refuses 176/176 where the eigenbasis certifies), P4
  (352/352 counts and rates), P5 (804/804 soundness checkpoints) — each an
  exhaustive pre-registered inequality count over all cells, no selection.
- **NOT significant / not shown:** any accuracy or speed advantage over
  truncated SVD (SVD ahead at matched rank on 4 of 6 cells, as the brief
  registered); tightness of the attention certificate (worst slack 4.8e-4:
  sound, deliberately unsharp); anything about trained-model caches
  (synthetic instances only).
- **Verdict rung (M6):** empirical
- **Counterexamples emitted (M5):** none (CAL-3 is the watched must-fail;
  CAL-4's failure as frozen was an instrument finding, recorded in
  REPORT section 2)

## Declared limits

Repeated from brief section 13 and confirmed still true after the run:
synthetic Gaussian-factor data, no LLM weights, no end-task claim; no
speed claim (the vanilla certified iteration is the object under test);
reference iterate from the same trajectory run deeper, priced by the
residual bound; attention bound soundness only, not tightness.

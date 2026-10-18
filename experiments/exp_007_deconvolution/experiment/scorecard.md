# exp_007 — scorecard (filled last, 2026-10-10)

| φ | outcome | evidence |
|---|---|---|
| φ_method | **0.5** | brief frozen (sha256 893b440a…) and followed; predictions derived, but TWO registered predictions carried my derivation errors — P2b (assumed the slowest mode is always excited; from x₀ = 0 the blur-kernel band never is, 16/48 cells outside 3×) and P7 band-split (ignored grid quantisation of the cutoff, 11.7% vs 10%) — both caught by the data, declared, not reworded |
| φ_repro | **1** | `runs/run_manifest.json`; seeded; full run 45 s; raw jsonl + traces + `results/summary.toml` |
| φ_discriminant | **1** | CAL-1..5 passed incl. watched must-fails (kernel overlap refused Δ_w = −4.5e-17; inflated ν rejected; H_Δ witness violates); arm A = floor, FISTA = classical, exact x*/true λ_min = ceiling; arm B = negative control that certified σ = 0 as required |
| φ_determinism | **1** | seeds enumerated; tolerances frozen; error budget: FP only, ε six decades above the floor |

**C_D^exp = 0.5**

## Claims

- **Significant:** P1 soundness 812/812 checks (worst count ratio 0.149, worst distance/bound 0.59); Δ_w ≤ λ_min 48/48; arm B σ = 0 at every λ with secant slope −1.0000 (AFS premise refuted numerically); arm A non-uniqueness 1e-14; cert evaluation ≤ 1% of the solve for k ≥ 100; canonical count ∝ d² (17.8× for 4× d).
- **NOT shown:** the 3× tightness law P2b (failed 16/48); band-split d-invariance within 10% (11.7%); P8 at s = 1 (w* off-grid); anything 2-D, non-circulant, or at non-fixed weights; any image-quality claim.
- **Verdict rung (M6):** `empirical`.
- **Counterexamples emitted (M5):** none against a theorem. Scope note for H6: from x₀ = 0 the smooth run never touches the blur's kernel band, so the prior's kernel-band curvature buys the certificate, not the measured speed.

## Declared limits

As brief §13, confirmed after the run.

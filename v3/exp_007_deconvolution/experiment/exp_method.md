# exp_007 — Deconvolution: certified versus measured iteration count (EXPERIMENTAL METHOD)

> **FROZEN before the run (2026-10-10).** Standard: `../_template/` and
> `project_plan/v3_experiment_system.md`. Worked example for manuscript
> unit H6 (`project_plan/STATUS.md`). Original motivation read (not run):
> AFS `Design/Product Roadmap/03_backlog_flows/Deconvolution the Perfect First Story.md`.

## 0. Status & scope

Frozen: 2026-10-10, before any run. Operator: Claude (subagent) for the
author. **Track:** Q1 (grammar: declare → compose → certify) with Q2
(certificates). **Explicitly NOT tested:** image-quality claims (PSNR/SSIM
are not measured — this is a certificate experiment, not a deblurring
benchmark); 2-D images (optional in the request; not run); weights chosen
by any outer loop (the scope guard of exp_006 stands: fixed weights only);
any comparison with learned methods; wall-clock on any other machine.

**Binding correction to the AFS plan.** The AFS plan claims the ℓ1 wavelet
prior `λ‖Wx‖₁` "widens the gap γ". By manuscript Lemma `lem:l1-hessian`
(§6) an ℓ1 term has zero Hessian wherever it is twice differentiable, and
it adds no strong-convexity modulus (it is piecewise linear along every
line). It cannot open the gap. Here the gap comes from composing two
**degenerate smooth terms** whose kernels meet only at {0}
(Theorem `thm:composite-gap`, Theorem `thm:uniform-gap`, Lemma
`lem:rule-sum`). Arm B demonstrates the failure of the AFS premise
numerically.

## 1. Theory linkage (M1)

Statements used, exactly as in the manuscript:

- **Kernel Gram certificate / transversality defect**
  (`sections/04_composition/02_*.tex`): `Δ_w = Σ a_i − λ_max(A^{1/2} G A^{1/2})`,
  `a_i = w_i ν_i`, `G = BᵀB`, B the stacked orthonormal kernel bases.
- **Uniform composite gap** (`thm:uniform-gap`(a), `03_*.tex`): for valid
  kernel attributes `(K_i, ν_i)` (eq. `restricted-gap`), `σ(F) ≥ Δ_w`.
  Declarations with `K_i ⊋ ker` are valid but not invariant (part (b) does
  not apply; part (a) does) — `rem:declaration-choice`.
- **Sum rule** (`lem:rule-sum`): `σ_𝔈^T = max{σ̂_S, Δ_w(T) + Σ_{i∉T} w_iσ_i}`,
  `β̂ = Σ w_iβ_i`.
- **Soundness** (`thm:soundness`, `sections/08_calculus/03_soundness.tex`):
  constructed iteration = forward–backward at step `α = 1/(cβ̂)`, `c = 1`
  here (orthonormal wavelet, `WᵀW = I`).
  (S5)(A): if `σ_𝔈^T > 0`, `‖x − x*‖ ≤ ‖R_α(x)‖/σ_𝔈^T` for every x, and
  `k_ε ≤ ⌈log((2β̂/σ_𝔈^T − 1)‖R_α(x_0)‖/ε) / log(β̂/(β̂ − σ_𝔈^T))⌉`.
  (S2)/(D): with a declared `E_low ≤ inf E`, `k_ε ≤ k_0 + ⌊2β̂(E(x_0) − E_low)/ε²⌋`,
  no distance bound.
  (S6): one step = |S| gradient calls + at most (2|S|+1)d arithmetic
  instructions + one prox (κ + 2d + 1 with a frame slot).
- **Residual certificate** (`thm:fb-residual`, `cor:fb-stop`,
  `sections/05_certificates/01_fb_residual.tex`): the certificate is one
  forward–backward step evaluated at the returned point.

### Registered predictions (derived)

Notation: frequencies `ω_j = 2π·min(j, d−j)/d`; blur multiplier `k̂_j`;
first-difference multiplier `d̂_j = 4 sin²(πj/d)`; cutoff index `j_c`;
`ν₁ = min_{|j|≤j_c} k̂_j²`; `λ_min := min_j (w₁k̂_j² + w₂d̂_j)` (exact, the
true modulus of the smooth part, computed from the multipliers).

Two valid declarations of the smoothness prior (both checked by CAL-3):
- **canonical**: `K₂ = span{1}` (= ker D), `ν₂ = 4 sin²(π/d)`;
- **band-split**: `K₂ = low band {|j| ≤ j_c}` (⊋ ker D; valid by monotonicity
  of `d̂_j` on `0 ≤ j ≤ d/2`), `ν₂' = 4 sin²(π(j_c+1)/d)`.
Both have `K₁ ∩ K₂ = {0}` and `K₁ ⊥ K₂`, so `G` is block-identity and the
Gram eigenproblem must return `Δ_w = min(w₁ν₁, w₂ν₂)` (resp. `ν₂'`).

- **P1 (soundness, must hold).** In every arm-C run, for both declarations:
  measured `k_ε ≤` certified `k_ε`, and `‖x_{k_ε} − x*‖ ≤ ε/σ_𝔈^T`
  (+ the certified reference slack for the ℓ1 arm, §5). **Rejection:** any
  violation stops the analysis and is filed as a bug-or-counterexample (M5).
- **P2 (gap is a lower bound; where the slack lives).** `Δ_w ≤ λ_min` in
  every configuration (derivation: `w₁k̂_j² ≥ w₁ν₁` on the kept band,
  `w₂d̂_j ≥ w₂ν₂'` off it). The looseness of the certified count is the
  declaration slack: registered
  `k_cert / k_meas ∈ [1/3, 3] · (λ_min/Δ_w) · L`, `L := log((2β̂/Δ_w − 1)/ε_rel) / log(1/ε_rel)`
  (derivation: on a quadratic, FB from x₀ contracts mode j by `1 − α λ_j`;
  the slowest mode governs the measured count). If false: the looseness has
  a second source (weak excitation of the slowest mode, log factors) —
  reported, not hidden.
- **P3 (arm B: ℓ1 adds no curvature — the AFS premise fails).** For every
  λ in the sweep: declared `σ_𝔈 = 0` (data term has kernel dimension
  `d − (2j_c + 1) > 0`, and the ℓ1 term's curvature attribute is 0);
  `λ_min(KᵀK) = 0` to 1e-12; the secant-modulus bound along a unit
  kernel direction z at the returned point,
  `σ_sec(t) := 2[½(E(x+tz) + E(x−tz)) − E(x)]/t²`, satisfies
  `σ_sec(t) ≤ 2λ‖Wz‖₁/t` (triangle inequality) and its log–log slope over
  the top decade `t ∈ [10², 10³]` is `−1 ± 0.05`. If false: an ℓ1 term
  adds curvature, contradicting `lem:l1-hessian` — would be a defect.
- **P4 (arm A: data term only).** Declared `σ_𝔈 = 0`: regime D, no rate,
  no distance bound; certified count only via (S2) with `E_low = 0`
  (valid: E ≥ 0). Energy exactly invariant along K₁ (relative change
  ≤ 1e-12 for random z ∈ K₁): the minimiser is not unique. Measured (not
  certified): the run stays in K₁^⊥ (x₀ = 0, gradients in range Kᵀ), so it
  converges linearly at rate ≤ `1 − ν₁/β̂`; registered measured
  `k_ε ≤ ⌈log((2β̂/ν₁ − 1)/ε_rel)/log(β̂/(β̂ − ν₁))⌉`.
- **P5 (FISTA baseline, measured only).** FISTA (Beck–Teboulle, step 1/β̂,
  no restart) is **not certified** by `thm:soundness` (only the constructed
  FB iteration is; `rem:soundness-scope`(ii)). Registered direction:
  FISTA's measured count < FB's measured count in every configuration with
  `κ_true := β̂/λ_min ≥ 100`. No prediction for `κ_true < 100`.
- **P6 (cheap to check, costly to compute).** One certificate evaluation
  costs one FB step + one norm (|S| gradients + one prox + 2d); the solve
  costs `k_meas` steps. Registered: flop ratio `cert/solve ≤ 1e-2` whenever
  `k_meas ≥ 100`; measured wall-clock ratio within 3× of the flop ratio.
- **P7 (dimension).** Canonical `ν₂ ∝ 1/d²` ⇒ canonical certified count
  grows ≈ d²: registered ratio `k_cert(d=1024)/k_cert(d=256) ∈ [12, 20]`
  at the scaling configuration (s = 2, w₂ = 0.1, no ℓ1). Band-split
  certified count and measured count vary ≤ 10% across d ∈ {256, 512, 1024}.
- **P8 (weight dial).** Band-split `Δ_w = min(ν₁, w₂ν₂')` saturates at ν₁
  for `w₂ ≥ w* := ν₁/ν₂'`, while `β̂ = 1 + 4w₂` keeps rising; the leading
  factor `β̂/Δ_w` is minimised at `w*`. Registered: the argmin of `k_cert`
  over the swept w₂ grid is one of the two grid points bracketing `w*`.

## 2. Background & motivation

The paper's composition story (H6) needs one worked example where a rate
and an iteration count are computed from per-term declarations *before*
the run, then compared with what the run does. Deconvolution is the AFS
"first story"; its stated mechanism (ℓ1 opens the gap) is wrong, and the
correct mechanism (two degenerate smooth terms with transversal kernels)
is exactly Theorem `thm:composite-gap`. exp_002 measured the refusal
branch (kernel overlap → γ ≈ 0); this experiment measures the accepting
branch on a single clean instance family and quantifies the certificate's
looseness. Decision waiting: whether H6 can state a certified count that
is within a stated factor of the measured one, and which declaration it
must use to do so.

## 3. Hypotheses

H1 = P1 (soundness in practice). H2 = P2, P7, P8 (where the certified
count's looseness comes from; how declaration choice changes it). H3 = P3,
P4 (degenerate arms are certified as such). H4 = P5, P6 (the comparison
and cost story). Decision for each: the H6 worked-example text is written
from whichever branch is observed; a failed registered prediction is
reported as failed.

## 4. Objective, formalized

`E(x) = w₁·½‖Kx − y‖² + w₂·½‖Dx‖² + λ‖Wx‖₁`, x ∈ ℝ^d, w₁ = 1.
Arms: **A** (w₂ = 0, λ = 0); **B** (w₂ = 0, λ > 0); **C-smooth** (w₂ > 0,
λ = 0); **C-ℓ1** (w₂ > 0, λ = 0.01). Variant **G** (untruncated Gaussian
blur, s = 2, C-smooth): data term declared `(K₁ = high band, ν₁ = min on
kept band)`, valid but not invariant.
Measured: `k_ε^meas := min{k: ‖R_α(x_k)‖ ≤ ε}`, `ε := ε_rel‖R_α(x₀)‖`,
`R_α(x) := (x − T_α x)/α`, `T_α x := prox_{αλ‖W·‖₁}(x − α∇F(x))`.
Certified: `k_ε^cert` from (S5)(A) (arm C) or (S2) (arms A, B).

## 5. Data & materials

| item | value |
|---|---|
| Signal | d = 256 (main); x_true(t), t = i/d: +1 on [0.10, 0.30), −0.5 on [0.45, 0.50), +0.8 on [0.60, 0.85), plus 0.3 sin(2π·3t) everywhere. Seedless. |
| Blur (main) | band-limited Gaussian: `k̂_j = exp(−s²ω_j²/2)` if `exp(−s²ω_j²) ≥ τ`, else **exactly 0**; τ = 1e-2; s ∈ {1, 2, 4} samples. **Choice stated:** band-limited, so the data-term kernel declaration is exact (K₁ = ker K) and the term is K₁-invariant. |
| Blur (variant G) | untruncated Gaussian, s = 2 (no exact null space; declaration valid via `lem:decl-order`(b), not invariant). |
| Smoothness prior | circular first difference D, `d̂_j = 4 sin²(πj/d)`, β₂ = 4, ker = constants. |
| ℓ1 prior | db4, periodization, level = pywt max level (5 at d = 256), dense orthonormal W (WᵀW = I, c = 1). Prox: Wᵀ soft(Wx, αλ). σ_g = 0. |
| Noise | y = K x_true + n, n ~ N(0, σ_n²), σ_n = 0.01·‖Kx_true‖/√d. |
| Seeds | noise seeds 0–7 (numpy default_rng(seed)); CAL rng(42); arm-A invariance probe rng(1000); everything else deterministic. |
| Sweeps | s ∈ {1, 2, 4}; w₂ ∈ {0.01, 0.1, 1, 10}; arm B λ ∈ {0.001, 0.01, 0.1}; arm C-ℓ1 λ = 0.01; d ∈ {256, 512, 1024} at (s = 2, w₂ = 0.1, C-smooth, seed 0). |
| Declared constants | β₁ = max k̂² = 1, σ₁ = σ₂ = 0, ν₁ as above, ν₂ / ν₂' as §1, β̂ = 1 + 4w₂, `E_low = 0`. |
| Closed-form x* | C-smooth: `x̂* = k̂ŷ/(k̂² + w₂d̂)` (FFT). C-ℓ1: FB reference run from 0 to `‖R‖ ≤ 1e-12‖R₀‖` (cap 3·10⁶), certified accuracy `‖x_ref − x*‖ ≤ ‖R(x_ref)‖/σ_𝔈^band`. |

## 6. Apparatus & environment (M7)

`v3/.venv` (uv; numpy 2.4.6, scipy 1.17.1, PyWavelets 1.8.0), CPU only,
float64. FB step α = 1/β̂, x₀ = 0, iteration cap 300 000 (runs hitting the
cap are reported as censored, never dropped). FISTA: y₁ = x₀, t₁ = 1, same
step, residual monitored at x_k (monitor cost excluded from FISTA's step
cost, stated). **Tolerances:** ε_rel = 1e-6 (six decades: far above the
float64 residual floor ~1e-15·κ, below any visual difference);
Gram/closed-form agreement 1e-10 (eigen-solver round-off on k ≤ 1024);
validity check `λ_min(H − νP_{K⊥}) ≥ −1e-12` (spectral round-off);
orthonormality 1e-12; slope tolerance ±0.05 (P3; exact asymptote −1).
**Flop model (declared):** rfft/irfft 2.5 d log₂ d each; one circulant
gradient call = rfft + (d+2) + irfft (+ d for the data term's −Kᵀy);
FB update (2|S|+1)d per (S6); dense W matvec 2d² − d; soft threshold 4d;
frame slot +2d + 1; residual norm 2d. Wall-clock: median of repeated
timings, this machine only.

## 7. Procedure

1. `harness.py --calibrate` → `results/calibration.json` (gates §8; a failed gate aborts).
2. `harness.py --run` → `results/runs.jsonl` (one row per run), `results/declarations.jsonl` (per-config certified numbers, computed before the run loop), `results/arm_b_secant.jsonl`, `results/traces.npz` (residual traces, seed 0), `results/summary.toml`.
3. `analysis/make_analysis.py` → `analysis/stats.json`, figures.

## 8. Instrument calibration (M2)

- **CAL-1 (flat spectrum, closed form).** d = 64, rng(42): two random
  10-dim subspaces, `H_i = ν_iP_{K_i⊥}`; Gram-path Δ_w must equal
  `λ_min(w₁H₁ + w₂H₂)` to 1e-10 (`rem:t1-sharpness`). Fourier case: Gram
  path = `min(a₁, a₂)` to 1e-12.
- **CAL-2 (must fail: kernel overlap).** Data term with DC also removed
  (K₁ ∋ constants) + canonical D: Gram path must return Δ_w ≤ 1e-12
  (refusal watched).
- **CAL-3 (declaration validity).** Every declaration used passes the
  validity check; ν inflated by 1.01 must FAIL (watched) for both D
  declarations and for the data term.
- **CAL-4 (count and distance on closed form; must-fail H_Δ).** Diagonal
  quadratic, spectrum geomspace(1e-2, 1, 64): measured k_ε ≤ (S5)(A) count
  and distance bound holds. Must-fail: `f = ½‖x‖²` with computed
  Δ⁻ = 1.5 > Δ_w = 1 → the distance bound `‖x‖ ≤ ‖R(x)‖/1.5` must be
  violated (watched), per the (H_Δ) witness in `thm:soundness` (G3).
- **CAL-5 (operators).** `‖WᵀW − I‖_max ≤ 1e-12`; FFT gradients equal dense
  circulant-matrix gradients to 1e-12 relative.

## 9. Variables, baselines & controls

Independent: s, w₂, λ, declaration, d. Dependent: k_meas, k_cert,
distances, λ_min, Δ_w, costs. **Baselines bracket:** floor = arm A
(no prior: no certificate, non-unique answer); classical = FISTA (measured,
uncertified); ceiling = exact x* (FFT solve) and the true λ_min (oracle
modulus — "what the certificate would say if it knew the spectrum").
**Negative controls that can fail:** arm B (must certify σ = 0 however
large λ is); CAL-2 (overlap must be refused); CAL-3/CAL-4 must-fails.
Generosity: FISTA gets the same step and stopping rule; its residual
monitor is not charged.

## 10. Error budget (M3)

Model error: none (exact quadratics + ℓ1, Fourier-diagonal). Discretisation:
none (the finite-dimensional problem is the object). Floating point:
FFT round-off ~1e-15 relative; residual floor ≈ 1e-16·β̂·‖x‖, at least six
decades below ε. Condition numbers κ_true = β̂/λ_min and κ_cert = β̂/Δ_w
reported for every configuration.

## 11. Metrics & statistics

Counts are deterministic given the seed; across the 8 noise seeds we
report min/median/max (no CI needed for an inequality that must hold on
every run — P1 is a 100% gate). Ratios k_cert/k_meas reported per run.
Builder cannot score: P1, P3, P7, P8 are mechanical checks in
`make_analysis.py` against the thresholds frozen here.

## 12. Analysis plan

Table 1: per (s, w₂, declaration): ν₁, ν₂, Δ_w, λ_min, κ_true, k_cert,
k_meas (min/med/max), FISTA k_meas, max distance/bound. Table 2: arm B
secant slopes and σ_𝔈 = 0 across λ. Table 3: arm A. Table 4: cost
(per-step flops, certified total, measured total, cert-eval/solve ratio,
wall-clock). Table 5: d-scaling. Figures: fig1 residual traces (FB, FISTA,
certified envelope) at s = 2, w₂ = 0.1; fig2 certified vs measured counts
across the sweep (log–log, y = x line); fig3 arm-B secant modulus vs t.

## 13. Threats to validity & scope

One signal, 1-D, d ≤ 1024, circulant operators: the Fourier diagonalisation
makes λ_min exactly computable — that is the point (oracle ceiling) and
also the limit (no claim about non-circulant operators). The band-split
declaration of D uses the data term's cutoff j_c: it is per-term data of D
but chosen with knowledge of the other term — stated, not hidden
(`rem:declaration-choice`: which declarations maximise Δ_w is open).
Verdict rung: **empirical**.

## 14. Reproduction

```
cd v3 && uv sync
uv run python exp_007_deconvolution/src/harness.py --calibrate
uv run python exp_007_deconvolution/src/harness.py --run
uv run python exp_007_deconvolution/analysis/make_analysis.py
```

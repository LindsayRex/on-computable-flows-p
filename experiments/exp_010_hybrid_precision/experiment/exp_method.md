# exp_010 — Hybrid precision: a certificate for the float32 run of the deconvolution example (EXPERIMENTAL METHOD)

> **FROZEN before the run (2026-11-02).** Standard: `../_template/` and
> `project_plan/done/v3_campaign/v3_experiment_system.md` (M1–M8). Source: B72
> (`project_plan/doing/B72_HYBRID_PRECISION_CERTIFICATE.md`, the three holes and the
> repaired rule), board card 85. Companion dossier (the two propositions this
> experiment exercises): `project_plan/doing/proof_audits/B72_SND_margin_rule/`.

## 0. Status & scope

Frozen 2026-11-02, before any run. Operator: Claude (main session) for the author.
**Track:** Q2 (certificates), the certificate of the implemented run. **Explicitly NOT
tested:** v7's rate or accuracy constants for a floating-point run (those need the step
map enclosed, not the energy); any image-quality claim; GPU execution; any arithmetic
below float32; the ℓ1 arm's minimiser (not needed: the certificate is descent of the
computed run, not distance to a minimiser).

**What is measured.** Along a float32 forward–backward run of the deconvolution energy
of exp_007, each step's accept/reject decision under three decision rules is compared
with a rigorous ground truth about the true energy of the stored float32 iterates. The
three rules: (a) the plain float comparison; (b) B72 as its source document wrote it;
(c) the repaired two-sided margin rule. The registered claims are about false accepts
(a rule accepts a step whose true energy rose) and the share of steps that needed the
rigorous path.

## 1. Theory linkage (M1)

Statements used (the dossier `B72_SND_margin_rule` carries them through the pipeline;
nothing here is proved, only exercised):

- **Standard model of floating-point arithmetic** (Trefethen–Bau, held; Higham–Mary
  2019 eq. (1.1), Lemma 2.2, held): each `fl(a ∘ b) = (a ∘ b)(1 + δ)`, `|δ| ≤ u`,
  `u = 2^-24` (float32), `2^-53` (float64), in the absence of underflow and overflow.
- **Any-order summation and inner-product bounds** (Jeannerod–Rump 2013, Prop. 3.1 and
  Prop. 4.1, held, page-verified 2026-11-02): `|fl(Σ x_i) − Σ x_i| ≤ (n−1) u Σ |x_i|`
  (no overflow; any n), and `|fl(Σ fl(z_i)) − Σ z_i| ≤ n u Σ |z_i|` (no underflow or
  overflow; any n). No `O(u²)` term, no restriction `nu < 1`.
- **Inclusion property of interval arithmetic** (Rump 2010, (5.16)–(5.17), p. 28,
  held): an interval evaluation encloses the real result.
- **Proposition 1 (enclosure; dossier B72-SND).** For the declared energy below and
  `x` a float vector, the direct float evaluation returns `(Ê, e)` with
  `E(x) ∈ [Ê − e, Ê + e]`, where `e` is the composed a priori bound of §4, computed from
  the quantities of the evaluation at `O(d²)` cost.
- **Proposition 2 (the certificate of the repaired rule; dossier B72-SND).** Along any
  run of the rule in §4, `E(z_k) ≤ B_k` for every k and `B_{k+1} < B_k` at every
  accepted step; a branch-2 reject certifies `E(z⁺) > E(z_k)`.

### Registered predictions (derived)

Notation: `z_k` the float32 iterates of the fixed-step run (§4); `u₃₂ = 2^-24`;
`k_band` the first step at which rule (c) leaves branch 1.

- **P1 (soundness of the repaired rule; must hold).** Rule (c) makes zero false
  accepts on every step of every run (classifier mode, both arms, all seeds). Derived
  from Proposition 1 and the inclusion property: an accept in branch 1 or 3 carries an
  enclosure whose upper bound is below `B_k ≥ E(z_k)`. **Rejection:** one false accept
  stops the analysis and is filed as a bug-or-counterexample (M5): either the bound
  composition, the enclosure library or the harness is wrong.
- **P2 (the plain float test fails in the band).** Rule (a) makes at least one false
  accept within the first K steps of the smooth arm for at least one seed. Derivation:
  from the float64 pilot of 2026-11-02 (not registered as a number; smooth arm s = 2,
  w₂ = 0.1, seed 0) the true one-step decrease falls below `u₃₂·E` between steps 60 and
  100, after which the float32 energy difference is rounding, whose sign is uncorrelated
  with the true sign. If false (no false accept in K steps): the band produced only
  false rejects or ties; reported, the claim "the plain test is unsound" then rests on
  Proposition 1's logic alone, not on an observed failure.
- **P3 (hole 1 of B72 as written).** Rule (b)'s false accepts are exactly rule (a)'s,
  step for step. Derivation: (b) differs from (a) only on apparent rises, so every
  apparent descent is accepted by both. Exact equality is the registered form; a
  difference of one step is a harness bug.
- **P4 (band onset).** `k_band ∈ [20, 120]` on the smooth arm at s = 2, w₂ = 0.1 for
  every seed, and branch 1 is taken at every step before `k_band`. Derivation: branch 1
  ends when the true decrease falls below `e(z) ≈ C d u₃₂ E` with `C ∈ [2, 8]` from the
  terms of §4; against the pilot's decrease profile this is between steps 20 and 120.
  If false: the a priori bound is looser or tighter than its terms suggest; the measured
  `e/(u₃₂E)` is reported either way.
- **P5 (mutation must-fail; watched).** With the a priori bound replaced by `e/1000`
  (a deliberately wrong bound; everything else unchanged), rule (c) makes at least one
  false accept on the smooth arm. If it does not, the test has no power to detect an
  unsound bound and that is reported as a weakness of the test, not as a success.
- **P6 (cost).** A tier-1 rigorous evaluation (float64 direct evaluation with its own
  bound) costs at most 5× the wall time of a float32 direct evaluation; a tier-2
  evaluation (mpmath intervals, 113 bits) at most 10⁴× (pilot: about 0.6 s for the data
  term at d = 256). Tier 2 fires only when tier 1 is undecided. The rigorous share
  (branch-3 steps / all steps) is reported per arm; no prediction of its value beyond
  P4 is registered (B72's value proposition depends on it; measured, not assumed).
- **P7 (live mode).** The live rule (decisions act; rejects halve the step) reaches
  the float32 fixed point (`z⁺ == z_k` bitwise) or the step cap with zero branch-2
  rejects on the smooth arm at `α = 1/β̂`. Derivation: the exact forward–backward map
  descends at this step by the descent lemma; a certified rise could come only from
  float32 deviation of the step map, which is not certified here. If a branch-2 reject
  occurs it is a finding (the float32 step map produced a true rise), reported with the
  step and the enclosures.

## 2. Background & motivation

v7 proves its certificates in exact real arithmetic and states that the floating-point
validity of the computed steps is out of scope (T1 audit). B72's source design answers
the finite-precision objection with floats plus an interval re-run on apparent rises.
The B72 document finds three holes (one-sided check; the enclosure is of the exact
update while the float state is kept; the previous energy is a float, not a bound) and
proposes the repaired rule of §4. This experiment is the test the document asks for,
with its negative controls, on the worked example that already has a declared energy.

## 3. Hypotheses

H1 = P1, P5 (the repaired rule is sound, and the test can tell). H2 = P2, P3 (the plain
test and B72 as written are not). H3 = P4, P6 (where the band begins and what rigour
costs). H4 = P7 (the live rule on the certified step). Decision for each: the scope unit
is written from the observed branch; a failed registered prediction is reported as
failed.

## 4. Objective, formalized

**Declared energy (stored data).** `d = 256`. Stored float32 arrays define the energy
exactly: `κ ∈ F32^d` (the circulant blur column, computed as in exp_007 in float64 and
then rounded once to float32), `y ∈ F32^d` (exp_007's data, rounded once), `w₂ ∈ F32`,
`λ ∈ F32`, `W ∈ F32^{d×d}` (exp_007's db4 matrix, rounded once). For real `x`:

`E(x) = ½ Σ_i r_i(x)² + ½ w₂ Σ_i (x_i − x_{i−1})² + λ Σ_i |(Wx)_i|`, `r_i(x) = Σ_j K_ij x_j − y_i`,
`K_ij = κ_{(i−j) mod d}` (indices mod d).

For a float vector `x`, `E(x)` is a rational number; every evaluation below (float32,
float64, interval) reads the same stored numbers, so they enclose the same `E(x)`.

**Direct float evaluation in precision u (Proposition 1).** All sums in any order.
`ŝ_i = fl(Σ_j fl(K_ij x_j))`, `r̂_i = fl(ŝ_i − y_i)`; `D̂ = fl(Σ_i fl(r̂_i²))`;
`v̂_i = fl(x_i − x_{i−1})`, `Ŝ = fl(Σ_i fl(v̂_i²))`; `ĉ_i = fl(Σ_j fl(W_ij x_j))`,
`Â = fl(Σ_i |ĉ_i|)`; `Ê = fl(fl(½D̂ + fl(½ fl(w₂Ŝ))) + fl(λÂ))`. The a priori bound:

```
e_i   = d u Σ_j |K_ij x_j| + u |r̂_i|                       (Prop 4.1, one op)
E_D   = d u Σ_i r̂_i² + Σ_i e_i (2|r̂_i| + e_i)               (Prop 4.1, triangle)
E_S   = d u Σ_i v̂_i² + Σ_i u|v̂_i| (2|v̂_i| + u|v̂_i|)        (one op, Prop 4.1, triangle)
f_i   = d u Σ_j |W_ij x_j|                                  (Prop 4.1)
E_A   = (d−1) u Σ_i |ĉ_i| + Σ_i f_i                         (Prop 3.1, triangle)
e     = ½ E_D + ½ (w₂ E_S + u |fl(w₂Ŝ)|) + (λ E_A + u |fl(λÂ)|) + 2u Ê
```

These are the constants of the dossier B72-SND (`project_plan/doing/proof_audits/B72_SND_margin_rule/01_derivation.md`,
section 3, "the formula for e"): the one-operation bound in the computable form `|fl(t) − t| ≤ u|fl(t)|` (its
Lemma A, from Jeannerod–Rump 2013 (2.3) and Lemma 2.2), and the final constant `2u Ê` for the two last additions
of nonnegative floats (its step 14; no factor `1/(1 − 2u)`, no primed constant).
The bound `e` is itself computed in float64 from nonnegative terms and inflated by
`(1 + 2^-40)` (`e_used`), which dominates its own rounding by the dossier's Proposition 1(b) (depth count
`3d + 10 ≤ 2^13 − 1`, valid for `d ≤ 2727`). The endpoints are rounded outward in float64 (Proposition 1(c)):
`hi = fl(fl(Ê + e_used)(1 + 2^-51))`, `lo = 0` if `Ê − e_used ≤ 0` and `fl(fl(Ê − e_used)(1 − 2^-51))` otherwise;
"`[Ê − e, Ê + e]`" below always means `[lo, hi]`. Underflow guard: every nonzero product `|K_ij x_j|`, `|W_ij x_j|`,
`|r̂_i|²`, `|v̂_i|²` and the two scalings `fl(w₂Ŝ)`, `fl(λÂ)` must exceed `2^-100` (float32 normal range begins at
`2^-126`); a run violating it is reported and its step excluded from the certified count.

**Rigorous ladder (branch 3).** Tier 1: the direct evaluation in float64 with its bound
(`u = 2^-53`). Tier 2: mpmath interval arithmetic (`mpmath.iv`, 113 bits), the data
loaded exactly (every float32 is an exact interval endpoint), direct sums. An enclosure
`[A′, B′]` decides against `B_k` when `B′ < B_k` (accept) or `A′ > B_k` (reject).

**The repaired rule (one step; Proposition 2).** State `z_k ∈ F32^d`, carried
enclosure `[A_k, B_k] ∋ E(z_k)` (`B_0` from the float32 enclosure at `z_0 = 0`, refined by
tier 1 if branch 3 would otherwise fire at k = 0). Compute `z⁺ = T_α(z_k)` in float32
(exp_007's step: FFT gradient in float32, soft-threshold prox through `W`). Evaluate
`(Ê, e)` at `z⁺` in float32.
1. If `Ê + e < B_k`: **accept** (branch 1). `z_{k+1} = z⁺`, `[A_{k+1}, B_{k+1}] = [Ê − e, Ê + e]`.
2. Else if `Ê − e > B_k`: **reject, rise certified** (branch 2): `E(z⁺) > B_k ≥ E(z_k)`.
3. Else (**band**, branch 3): tier 1; if undecided, tier 2; accept with the tier's
   enclosure if `B′ < B_k`; reject if `A′ > B_k`; if still undecided and `z⁺ == z_k`
   bitwise, stop (**float32 fixed point**); if undecided and `z⁺ ≠ z_k`, reject
   (conservative; counted separately as "undecided").
Live mode: a reject halves `α` and retries from `z_k` (cap 10 halvings per step, then
stop "step exhausted"). Classifier mode: decisions are recorded, the trajectory is not
changed (fixed `α`, `B_k` carried from the rule's own accepts and, after a rejected
step, re-initialised from the tier-1 enclosure of `z_{k+1}` so the next decision is
well-posed; both choices stated in the per-step record).

**The two other rules (classifier mode).** (a) plain float: accept iff
`Ê₃₂(z_{k+1}) < Ê₃₂(z_k)`. (b) B72 as written: if `Ê₃₂(z_{k+1}) < Ê₃₂(z_k)` accept;
else re-run the update from `z_k` in interval arithmetic (mpmath, 113 bits: the
gradient as dense interval matrix–vector products, the prox through `W` in intervals,
an enclosure of the EXACT update `T_α(z_k)`) and evaluate the energy of that enclosure;
accept iff its upper bound `< Ê₃₂(z_k)`, else reject. (This is the source document's
B2–B4 with `c = 0`; the "subset of the state" of B3 is the whole state here, the most
generous reading.) Cost cap: the interval re-run is evaluated at the first 40 apparent
rises of each run; later apparent rises record rule (b) as "not evaluated" and are
excluded from (b)'s reject counts. P3 is unaffected: (b)'s false accepts arise only on
apparent descents, which are never re-run.

**Ground truth per step.** Enclosures of `E(z_k)` and `E(z_{k+1})` by tier 1; if they
overlap, tier 2; if they still overlap, mpmath at 200 bits; if they still overlap, the
step is a **tie** (the two energies are equal to 200 bits, e.g. `z_{k+1} == z_k`) and is
excluded from the accuracy counts and counted. Truth = `rose` if the enclosure of
`E(z_{k+1})` lies entirely above that of `E(z_k)`, `fell` if entirely below.

**Arms.** C-smooth (`s = 2`, `w₂ = 0.1`, `λ = 0`) and C-ℓ1 (`s = 2`, `w₂ = 0.1`,
`λ = 0.01`), as exp_007's headline configurations. Step `α = 1/β̂` with
`β̂ := (1 + 4w₂)(1 + 2^-20)` (the exp_007 bound `1 + 4w₂` with a margin for the
float32 rounding of `κ`, stated). `x₀ = 0`.

## 5. Data & materials

| item | value |
|---|---|
| Signal, blur, noise, `W` | exactly exp_007 (`harness.py` of exp_007 imported; `x_true`, band-limited Gaussian blur `s = 2`, `τ = 1e-2`, noise `σ_n = 0.01‖Kx_true‖/√d`, db4 periodised, level 5), then rounded ONCE to float32 as the declared data of §4. |
| Seeds | noise seeds 0–3 (numpy `default_rng(seed)`); calibration `rng(42)`; everything else deterministic. Four seeds, not eight: each step costs rigorous evaluations (P6), and the registered claims are 100 % gates, not averages. |
| Steps | classifier mode K = 160 per arm per seed; live mode cap 400 steps. |
| Precisions | float32 run and float32 evaluation (`u = 2^-24`); tier 1 float64 (`u = 2^-53`); tier 2 mpmath 113 bits; truth escalation 200 bits. |
| Tolerances | none in the certificate (it is an inequality between rigorous bounds); CAL thresholds in §8; timing medians over 20 repeats. |

## 6. Apparatus & environment (M7)

`v3/.venv` (numpy 2.4.6, scipy 1.17.1, PyWavelets 1.8.0, mpmath 1.3.0), CPU only, two
BLAS threads (`OMP_NUM_THREADS=2`), single process. numpy 2.x performs `rfft`/`irfft`
in float32 for float32 input (checked 2026-11-02: `complex64` → `float32`), so the
float32 step is a genuine float32 computation. Float32 direct evaluation uses
`np.float32` arrays throughout (`np.dot` on float32 may accumulate in float32 or use
pairwise summation; Props 3.1 and 4.1 hold for ANY order, which is why they were chosen
over the recursive-summation form). Wall-clock on this machine only.

## 7. Procedure

1. `harness.py --calibrate` → `results/calibration.json` (gates §8; a failed gate aborts).
2. `harness.py --classify` → `results/steps.jsonl` (one row per step per arm per seed:
   branch, three decisions, truth, `Ê₃₂`, `e₃₂`, `B_k`, tier, times), `results/mutant.jsonl`
   (P5), `results/summary_classify.json`.
3. `harness.py --live` → `results/live.jsonl` (per step: branch, α, enclosure), `results/summary_live.json`.
4. `analysis/make_analysis.py` → `analysis/stats.json`, `results/summary.toml`, figures.

## 8. Instrument calibration (M2)

- **CAL-1 (enclosure validity, float32).** 200 random float32 `x` (`rng(42)`, entries
  `N(0,1)` and also scaled by `10^-3` and `10^3`) on the C-ℓ1 data: the float32 enclosure
  `[Ê − e, Ê + e]` must contain the tier-2 enclosure in 200/200 cases.
- **CAL-2 (must fail, watched).** Same 200 points with the bound replaced by `e/1000`:
  containment must FAIL in at least one case.
- **CAL-3 (tier 1 validity).** The float64 enclosure contains the tier-2 enclosure in
  200/200 cases, and is narrower than the float32 enclosure in 200/200.
- **CAL-4 (exactness on a representable case).** `x = 0`: `E(0) = ½ Σ y_i²`; the tier-2
  enclosure must contain the exact rational value computed with Python `fractions` from
  the float32 `y`, and the float32 enclosure must contain it too.
- **CAL-5 (determinism).** Two evaluations of the same `x` are bitwise identical in every
  precision; the float32 step from the same `z` is bitwise identical.

## 9. Variables, baselines & controls

Independent: arm, seed, rule, precision tier. Dependent: decisions, truth, false
accepts/rejects, `k_band`, branch shares, tier shares, times. **Baselines bracket:**
floor = rule (a) (no rigour); classical = rule (b) (B72 as written, the source
design); ceiling = rigorous evaluation at every step (the B73 cost, measured as the
tier-2 time × steps). **Negative controls that can fail:** CAL-2 and P5 (wrong bound
must be caught failing); P7's branch 2 (a true rise, if the float32 step produces one).
Generosity to the rules under attack: (b) encloses the whole state, not a subset, and
uses 113 bits.

## 10. Error budget (M3)

Model: none (the finite-dimensional energy on stored data is the object). Discretisation:
none. Floating point: the subject; separated by construction into the float32 evaluation
error (bounded a priori by `e`), the float32 step-map deviation (NOT certified; shows up
only through P7's branch 2), and the tier errors (bounded by their own enclosures).
Condition numbers: none to report (no linear solve or eigenproblem).

## 11. Metrics & statistics

Counts are deterministic given the seed. P1, P3, P5 are 100 % gates (every step, every
seed). P2, P4 report per seed. P6 reports medians of 20 timings and the shares. No CIs
(no sampling claim is made). Builder cannot score: the checks are mechanical in
`make_analysis.py` against the thresholds frozen here.

## 12. Analysis plan

Table 1: per arm and seed: steps, `k_band`, branch shares (1/2/3), tier shares in
branch 3, false accepts and false rejects for (a), (b), (c), ties. Table 2: cost per
evaluation (float32 direct, tier 1, tier 2, interval re-run of (b)) and the three
regimes' wall time. Table 3: live mode: steps to the float32 fixed point or cap, branch
counts, halvings. Figure 1: `e/(u₃₂E)` and the true one-step decrease against k, with
`k_band` marked (smooth arm, seed 0). Figure 2: per-step decisions of the three rules
against truth (strip plot, smooth arm, seed 0).

## 13. Threats to validity & scope

One energy, one dimension, one signal family: the finding is about this run, not about
float32 in general. The a priori bound is specific to the direct evaluation order of §4;
an FFT-based evaluation would need its own bound (not derived; the step map keeps the
FFT and is not certified). The interval library's correctness (mpmath) is assumed, as the
inclusion property assumes correctly rounded operations; CAL-4 checks it on one exact
case only. Verdict rung: **empirical** for the measured shares and failures;
**conditional** for the certificate (it rests on Propositions 1 and 2 of the dossier,
whose stage is recorded there).

## 14. Reproduction

```
cd v3 && OMP_NUM_THREADS=2 .venv/bin/python exp_010_hybrid_precision/src/harness.py --calibrate
OMP_NUM_THREADS=2 .venv/bin/python exp_010_hybrid_precision/src/harness.py --classify
OMP_NUM_THREADS=2 .venv/bin/python exp_010_hybrid_precision/src/harness.py --live
.venv/bin/python exp_010_hybrid_precision/analysis/make_analysis.py
```

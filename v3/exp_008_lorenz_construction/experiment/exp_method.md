# exp_008 — Constructed chaos: Lorenz-like fields against the diagnostic (EXPERIMENTAL METHOD)

> **Written and FROZEN before the run.** Headings are mandatory; a section
> that honestly doesn't apply gets one line saying why. Standard:
> `../_template/README.md` + `project_plan/v3_experiment_system.md`.

## 0. Status & scope

Frozen: 2026-10-18 (author approval this day: "I think you should run a couple of
experiments and yeah, explore these ideas... Give it a go.", research_log/LOG.md
entries 2026-10-18 10:18 and 10:34). · Operator: Claude session, no fan-out agents. ·
**Track:** Q4 (the diagnostic). ·
**Explicitly NOT tested:** anything about chaotic systems beyond Lorenz-type fields
(no claim of generality over all chaos); nothing about analog SAT dynamics; no claim
that diagnostic refusal detects chaos (the opposite is pre-registered: refusal is
necessary, not sufficient); nothing here enters any manuscript without a later
registered lift. Exploratory experiment at the author's direction; verdict rung
capped at `empirical`.

## 1. Theory linkage (M1 — mandatory)

**Claim under test:** the v2.2 pre-construction claim, run in reverse. v2.2 says:
measure before you build, and if quadratic smoothing cannot be seen to work, the
problem may be chaotic and unsolvable this way. Here we CONSTRUCT problems known to
be chaotic (Lorenz fields cast on a geometry) and test three registered consequences
of the v5 diagnostic story (dominance/contraction in a declared lens; blind
subspaces; lens materiality).

**Registered predictions, derived:**

For the Lorenz field F(x,y,z) = (sigma(y-x), rx-y-xz, xy-bz), sigma=10, b=8/3, the
Jacobian is J with rows (-sigma, sigma, 0 / r-z, -1, -x / y, x, -b). The diagnostic
analogue for a vector field is contraction in a declared lens: for a diagonal metric
P = diag(p1,p2,p3), the test quantity is mu_P(J(x)) = lambda_max of
(PJ+J^T P)/2 taken generalised against P, and the certificate is
s(r,P) = -sup_{x in B(r)} mu_P(J(x)) > 0 over a trap region B(r) (section 4). This is
the field-level form of the manuscript's curvature-dominance test; for a gradient
field it reduces to it exactly (J = -Hessian, mu_P < 0 iff certified curvature > 0 in
that lens).

- (P1, identity lens is blind) In the identity lens the 2x2 upper block of the
  symmetric part at the origin is [[-sigma,(sigma+r)/2],[(sigma+r)/2,-1]], negative
  definite iff (sigma+r)^2 < 4 sigma, i.e. sigma + r < 2 sqrt(10) ~= 6.32. With
  sigma=10 this fails for EVERY r >= 0: the identity lens can never certify, at any
  r, even where the origin is globally stable. Derived, parameter-free.
- (P2, the classical diagonal lens sees it) In the lens P = diag(1/sigma, 1, 1) the
  same block becomes [[-1,(1+r-z)/2],[(1+r-z)/2,-1]], negative definite at the origin
  iff r < 1. So a diagonal lens certifies (at least near the origin, and we test over
  the full trap region) in exactly the regime where the origin is in fact globally
  stable (classical: Lyapunov function x^2/sigma + y^2 + z^2 for r < 1). Prediction:
  the certified pass region of the classical lens is nonempty and ends at some
  r_cls <= 1; an optimised diagonal lens does at least as well, r_opt >= r_cls.
- (P3, the forced honesty gap) For r > 1 Lorenz has three equilibria; a contraction
  certificate over a region containing them all would force a unique equilibrium, so
  NO lens can pass for r > 1. Sustained chaos begins near r ~= 24.06 (transient
  chaos from ~13.93; Strogatz, Nonlinear Dynamics and Chaos, Lorenz chapter; Sparrow).
  Therefore the diagnostic must refuse throughout 1 < r < 24 where the dynamics are
  regular (lambda_1 < 0): refusal is necessary for chaos, never sufficient, and the
  width of that honest band is a measured output, not an embarrassment.
- (P4, soundness) Wherever a lens passes with rate s > 0, any two trajectories in
  B(r) must approach each other at least as fast as e^{-st} in the P-norm. Zero
  violations required.
- (P5, lattice: smoothing certifies exactly the transverse part) N Lorenz cells on a
  ring, diffusively coupled in all three coordinates with strength c (graph Laplacian
  L, lambda_2 = 2(1-cos(2 pi/N))): the transverse Jacobian on the k-th Laplacian mode
  is J - c lambda_k I, so transverse contraction is certified, before any run, when
  c > c* := sup_{B} mu_P(J) / lambda_2, with the sup taken at r = 28 in the best
  diagonal lens from part A. Predictions: (i) every run at c >= 1.1 c* synchronises
  (soundness, zero violations); (ii) the measured synchronisation threshold c_sync is
  BELOW c* (the certificate is a price, not a prediction; ratio reported); (iii) at
  c = 1.2 c* the synchronised motion itself remains chaotic with lambda_1 equal to the
  single-cell value (~0.906 at r=28) within tolerance: the coupling (quadratic
  smoothing) certifies the directions it couples and says nothing about its blind
  subspace, the synchronisation manifold, exactly as the grammar's blind-subspace rule
  predicts.

## 2. Background & motivation

Author idea and correction, research_log/LOG.md 2026-10-18 (10:18, 10:34): construct
chaotic problems rather than probe for chaos; the opposite direction of the v2.2
pre-construction measurement. Prior experiments: exp_001 (lens ablation) showed lens
materiality on certifiable problems; exp_004 (diagnostic battery) exercised the
dominance test; the shifted-GOE null (v5 printed section 3) is the static negative
control. Gap closed: the diagnostic has no dynamic negative control, no constructed
family whose ground truth is chaotic. Decisions waiting: whether roadmap card #4
(chaos step) becomes a worked card; whether a "constructed null, dynamic" unit is
worth proposing for v5.

## 3. Hypotheses & predictions

Pre-registered rejection criteria in brackets.

- **H1 (lens materiality on a chaotic benchmark):** identity lens never passes at any
  r; classical lens passes on a nonempty range ending at r_cls <= 1. If true: the
  manuscript's lens story holds on a textbook chaotic family. If false (identity
  passes somewhere, or classical lens passes for some r > 1): P1/P3 derivation is
  wrong, finding reported as a defect in the field-level reading of the diagnostic.
  [Reject H1 if identity passes at any swept r, or any lens passes at r > 1.]
- **H2 (honesty gap):** the certified flip r_opt sits in (0, 1] while measured
  lambda_1 crosses zero only near r ~= 24: a wide refusal band with regular dynamics.
  If true: diagnostic refusal must never be reported as chaos detection; card #4
  must be worded as one-sided. If false (lambda_1 > 0 somewhere in a certified pass
  region): soundness breach, highest-severity finding. [Reject soundness if any
  certified-pass r has measured lambda_1 > +0.01.]
- **H3 (certified transverse smoothing):** on the lattice, zero sync failures at
  c >= 1.1 c*; c_sync < c*; lambda_1 of the synchronised motion within +-0.05 of the
  single-cell value at c = 1.2 c*. If true: quadratic smoothing certifiably tames the
  coupled directions while the blind subspace keeps its chaos, the v2.2 sentence made
  precise. If false (any non-sync at c >= 1.1 c*): the transverse certificate as
  computed is unsound at this grid resolution, reported as such. [Reject if any run
  at c >= 1.1 c* has sync error > 1e-6 at T = 200 after discarding transient T0=50.]

## 4. Objective, formalized

mu_P(J(x)) := lambda_max( P^{1/2} J P^{-1/2} + (P^{1/2} J P^{-1/2})^T ) / 2 for
diagonal P; certificate s(r,P) := -max over a grid G(r) of mu_P(J(x)); pass iff
s > 0. Trap region B(r): the classical trapping ellipsoid E(r) =
{ sigma x^2 + y^2 + b (z - (r+sigma)/2)^2 <= b (r+sigma)^2 / 4 } inflated: B(r) is
the bounding box of E(r) scaled by 1.5 about its centre (every attractor and every
equilibrium lies in E(r); derivation: d/dt [x^2+y^2+(z-r-sigma)^2]/2 =
-sigma x^2 - y^2 - b z^2 + b(r+sigma) z < 0 outside E(r)). G(r) = uniform 41^3 grid
on B(r), with a 81^3 refinement check (section 10). lambda_1: Benettin tangent-space
method, RK4 step 1e-3, T=500 after transient 50, renormalisation every step; averaged
over 8 initial conditions (seeds). Sync error on the lattice: max over cell pairs of
the running max of Euclidean distance between cell states over t in [50, 200].
c_sync: bisection on c to tolerance 1e-2 of the smallest c whose sync error < 1e-6.

## 5. Data & materials (NUMBERS MANDATORY)

| item | value |
|---|---|
| Problem instances | Lorenz sigma=10, b=8/3; r swept over 61 values: 0.5 to 30.5 step 0.5 (part A). Ring lattice N=8 cells at r=28, coupling c swept by bisection plus a fixed grid c in {0.25, 0.5, 1, 2, 4, 8, 16} * c_star (part B) |
| Closed-form cases (M2) | linear field A=diag(-1,-5): mu_I = -1 exactly, certified rate 1; Lorenz r=0.5 in classical lens must pass (global stability for r<1 is classical); lambda_1(harmonic oscillator)=0 within 1e-3 |
| Must-fail cases (M2) | A=diag(+1,-5): test must refuse. Divergence test (trace J < 0) as dumb baseline: Lorenz trace = -(sigma+1+b) < 0 at ALL r including chaotic r=28, so the divergence test must (wrongly) pass there — watched failing, which is why dominance of the symmetric part, not divergence, is the diagnostic |
| Frozen artifacts | none consumed; this experiment generates its own instances from the equations above |
| Seeds | 0,1,2,3,4,5,6,7 for all random initial conditions (numpy default_rng(seed)); grids and bisection are seedless |

## 6. Apparatus & environment (M7)

Python 3.11, v3/.venv (pyproject-pinned numpy/scipy), no SageMath (nothing symbolic).
Integrators: scipy solve_ivp RK45 rtol 1e-9 atol 1e-12 for trajectories; fixed-step
RK4 h=1e-3 for Benettin (standard for tangent-space methods). Tolerances: pass/refuse
margin reported raw, no epsilon (sign decides; values within 1e-10 of 0 reported as
boundary); lambda_1 calibration tolerance +-0.03 against the literature value 0.906
at r=28 (finite-time Benettin scatter at T=500 is of this order); sync tolerance 1e-6
(double precision leaves 1e-9 headroom); bisection tolerance 1e-2 (threshold is
reported to two decimals, nothing finer is claimed). Each tolerance fixed now.

## 7. Procedure (numbered, in run order)

1. Calibration gates (section 8) → results/calibration.toml; any failure aborts.
2. Part A ramp: per r, per lens (identity; classical diag(1/sigma,1,1); optimised
   diagonal via Nelder-Mead on log(p1,p2,p3) maximising s, started from classical):
   grid sup, s, pass flag → results/ramp.jsonl.
3. Part A ground truth: per r, Benettin lambda_1 over 8 seeds → appended to the same
   rows (mean and spread).
4. Part A soundness spot-check: for every passing (r, lens), 8 random trajectory
   pairs in B(r); P-distance ratio against e^{-st} → results/soundness.jsonl.
5. Part B: compute c* from part A's optimised sup at r=28; run the fixed c grid and
   the bisection; lambda_1 of the synchronised motion at c = 1.2 c* →
   results/lattice.jsonl.
6. Totals and headline numbers → results/summary.toml. (Analysis figures only after
   all results files are written.)

## 8. Instrument calibration (M2 — BEFORE any real reading)

- **CAL-1 (mu test):** A=diag(-1,-5) → s=1.000 exact (tol 1e-9); must-fail
  A=diag(+1,-5) → refuse. Measured: recorded in calibration.toml.
- **CAL-2 (classical pass):** Lorenz r=0.5, classical lens, grid sup over B(0.5) →
  must pass (s>0); this is the classical global-stability regime.
- **CAL-3 (lambda_1 ruler):** r=28 Benettin → 0.906 +- 0.03; harmonic oscillator →
  |lambda_1| < 1e-3.
- **CAL-4 (dumb baseline watched failing):** trace test passes at r=28 (divergence
  negative) while lambda_1 > 0 — the wrong instrument endorses a chaotic field.

## 9. Variables, baselines & controls

- **Independent:** r (part A); c (part B); lens (identity / classical / optimised).
  **Dependent:** s, pass flag, lambda_1, sync error, c_sync.
- **Baselines bracket:** dumb baseline = divergence test (CAL-4); oracle ceiling =
  measured lambda_1 sign (the ground truth the certificate is honestly NOT allowed
  to see); random floor not meaningful for a deterministic verdict — stated, skipped.
- **Negative controls that can fail:** must-fail CAL-1; the r>1 no-pass prediction
  (any pass at r>1 falsifies the derivation and is reported as a defect).
- **Confounds controlled:** grid resolution (refinement check, section 10); lens
  optimiser only ever widens the pass region (it maximises s; it cannot create a
  false pass because the sup is evaluated the same way for every lens); identical
  integrator settings across all r and c. Generosity: the optimised lens is given to
  the diagnostic side only; the ground-truth lambda_1 needs no lens.

## 10. Error budget (M3)

Discretisation: RK45 at rtol 1e-9 (trajectory error orders below the 1e-6 sync
tolerance); Benettin finite-time scatter ~0.02-0.03 at T=500 (why the +-0.03
tolerance). Grid sup underestimates the true sup (a pass could be spurious): checked
by 81^3 refinement at every passing r and at r=28; if refinement moves any sup by
more than 1 per cent or flips any verdict, the coarse verdict is discarded and the
fine one reported with the flip noted. Floating point: negligible at these scales
(entries O(100)). Condition numbers: not in play (3x3 and 24x24 symmetric
eigenproblems).

## 11. Metrics & statistics

s (certified rate): the certificate itself; naive alternative (divergence) is CAL-4's
watched failure. lambda_1: mean over 8 seeds with min/max reported (no CI theatre on
8 points; the spread is printed). Sync error: worst pair, worst time after transient
(max, not mean, because the certificate promises every pair). All cells of the c grid
reported, including failures. Scoring is arithmetic from the artifact files; nothing
is judged by the builder.

## 12. Analysis plan (decided now)

Figure 1: s(r) per lens and lambda_1(r) on a shared r axis, with r=1 and r~=24.06
marked: the certified flip, the forced-honesty band, the chaos onset. Figure 2:
lattice sync error vs c/c* (log-log) with c*, c_sync and the lambda_1 of the
synchronised motion annotated. Tables: calibration.toml; summary.toml with r_cls,
r_opt, lambda_1 zero-crossing, c*, c_sync, their ratio, blind-subspace lambda_1.

## 13. Threats to validity & scope

One system family (Lorenz-type), one lattice topology (ring, N=8), diagonal lenses
only (a full-matrix lens could pass where diagonals refuse; not swept, stated).
Grid sup is a lower bound on the true sup: a "pass" here is grid-certified, not
proved (refusals are unaffected). Finite-time lambda_1 near onset (r in 20-25) is
noisy; the zero-crossing is reported to +-0.5 in r at best. Evidence ceiling: this
run can say "the diagnostic behaved as derived on a constructed chaotic family"; it
CANNOT say anything about chaos in general, about SAT dynamics, or that refusal
implies intractability. Verdict will be labelled empirical.

## 14. Reproduction

```
v3/.venv/bin/python src/run_ramp.py      # -> results/calibration.toml, ramp.jsonl, soundness.jsonl
v3/.venv/bin/python src/run_lattice.py   # -> results/lattice.jsonl
v3/.venv/bin/python src/make_summary.py  # -> results/summary.toml
v3/.venv/bin/python analysis/make_analysis.py  # -> figures (after results exist)
```

---

## AMENDMENT 1 — registered 2026-10-18, after the calibration gates, before any part A reading

**Trigger (M5):** gate CAL-2 failed as frozen: at r=0.5, classical lens, the exact
vertex sup of mu_P over the full trap box B(0.5) is +21.76 (calibration.toml). The
frozen operationalisation of P2 was wrong, and the failure is the experiment's first
finding: global asymptotic stability (the classical Lyapunov function for r<1) is
strictly weaker than contraction, and no constant diagonal lens certifies contraction
over the trap region even deep in the stable regime. The frozen text above is not
edited; this amendment adds the corrected region family and re-derives the
predictions. CAL-1, CAL-3, CAL-4 passed as frozen (lambda1(28) = 0.9096).

**Amended region family.** The contraction test runs over declared LOCAL boxes
around the origin equilibrium, rho in {0.1, 0.3, 0.5} (box = [-rho, rho]^3), the
certificate being a local one in the sense of the manuscript's local distance clause
(a declared ball, stated as such), PLUS the global trap box B(r) kept in the sweep
with the now-registered expectation of refusal at every r (its refusals are a
finding, not a failure).

**Re-derived predictions (replacing P2's operationalisation; P1, P3, P4 unchanged).**
In any diagonal lens the (1,2) coupling of the symmetric part is
a = (sigma sqrt(p1/p2) + (r-z) sqrt(p2/p1))/2 >= sqrt(sigma (r-z)) at the optimal
ratio, and negative definiteness of the 2x2 block needs a^2 < sigma, i.e. r - z < 1
at every z in the box: flip at r* = 1 - rho for the optimised lens, and the same
first-order flip for the classical lens (whose a = sqrt(sigma)(1+r-z)/2 gives
(1+r-z)/2 < 1, again r < 1 - rho). Identity still never passes (its a >=
(sigma + r - z)/2 > sqrt(sigma) for all r >= 0 at sigma = 10). So the registered
prediction becomes: r_cls(rho) ~= r_opt(rho) ~= 1 - rho, identity empty, no pass at
r > 1 anywhere, and the honesty band of P3 now reads: certified flip at 1 - rho
against chaos onset ~24.06.

**Amended CAL-2:** r=0.4, classical lens, local box rho=0.3 must pass (derived
margin: vertex worst 2x2 block [[-10, 2.69],[2.69, -1]], lambda_max ~= -0.26 < 0).
Gate rerun before part A; failure aborts again.

**Part B unchanged:** the sync certificate's sup is correctly taken over the global
trap box at r=28 (the region that contains the trajectories); c* as frozen.

## AMENDMENT 2 — registered 2026-10-18, before part A readings

Resolution only, no new quantity: the frozen r sweep (0.5 to 30.5 step 0.5) cannot
resolve the amended flip prediction r* = 1 - rho. The local-region sweep therefore
runs on r in 0.05 to 1.25 step 0.05 (25 values) in addition to the frozen 61 values;
the global trap box keeps the frozen 61 alone. lambda_1 is measured on the frozen 61
(chaos-onset scale); the local flip comparison uses the derived prediction, not
lambda_1, which is not meaningful at that resolution.

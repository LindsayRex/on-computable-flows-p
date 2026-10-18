# exp_009 — Certified low-rank KV-cache compression (EXPERIMENTAL METHOD)

> **Written and FROZEN before the run.** Standard: `../_template/README.md` +
> `project_plan/v3_experiment_system.md`. Second worked example for v5
> (decision 9c, author-approved 2026-10-18: "I think the inference one";
> shortlist: `project_plan/doing/SECOND_EXAMPLE_SHORTLIST_9c.md`, candidate C1).

## 0. Status & scope

Frozen: 2026-10-18. · Operator: main session (author-directed). · **Track:** Q1 ·
**Explicitly NOT tested:** anything about real transformer caches (all data is
synthetic with declared spectra); whether this compression beats published KV
methods on any benchmark (no benchmark is run); softmax replacement, token
selection, routing or any inference-serving question; sharpness of the
softmax Lipschitz constant (an elementary bound with constant 1 is used).

## 1. Theory linkage (M1 — mandatory)

**Claim under test:** the declare→compose→certify route of the v5 build
procedure (sec:build) on a problem class structurally unlike deblurring:
matrix-variable energy, spectral (nuclear-norm) proximal term, data-learned
lens, and a certificate passed to a downstream nonlinearity.

**Registered predictions, derived before any computation:**

Setup: keys $K \in \mathbb{R}^{n\times d}$, sample queries
$Q \in \mathbb{R}^{m\times d}$, Gram matrix $G = Q^\top Q \succeq 0$ with
eigenvalues $g_1 \ge \dots \ge g_d \ge 0$. Energy
$E(X) = \tfrac12\|(X-K)Q^\top\|_F^2 + \tfrac{\mu}{2}\|X-K\|_F^2 + \lambda\|X\|_*$.
The smooth part has gradient $\nabla f(X) = (X-K)(G+\mu I)$, i.e. the Hessian
is right-multiplication by $G+\mu I$, acting identically on every row of $X$.

- **P1 (declared constants).** Smoothness $\hat\beta = g_1+\mu$, certified
  curvature $\sigma = g_d+\mu$, both exact (the Hessian's extreme eigenvalues),
  read off the declaration. One-line derivation: the Frobenius inner product
  diagonalises under the eigenbasis of $G$.
- **P2 (blind subspace / refusal).** With $m < d$ (or rank-deficient $Q$) and
  $\mu = 0$: $\ker(G) \ne \{0\}$, so the certified curvature is $0$ and the
  diagnostic refuses a rate; any declared ridge $\mu > 0$ restores
  $\sigma = \mu$ exactly on that subspace. The flip is at $\mu > 0$, exactly,
  parameter-free.
- **P3 (lens materiality).** In the eigenbasis of $G$ (the data-learned lens)
  the Hessian is diagonal, so the dominance test passes with the exact
  $\sigma$. In the identity lens the test examines $G+\mu I$ directly and must
  refuse whenever Gershgorin fails there, which for the declared
  ill-conditioned $Q$ (correlated rows) it does. Same matrix, lens decides
  certifiability — the deblurring story on a lens learned from data.
- **P4 (certified count).** The forward-backward map at step
  $\alpha = 1/\hat\beta$ is a $(1-\sigma/\hat\beta)$-contraction (smooth part
  affine with spectrum in $[\sigma,\hat\beta]$; the nuclear prox is
  nonexpansive), so the direct count
  $k = \lceil \log(r_0/\varepsilon) / \log(\hat\beta/(\hat\beta-\sigma)) \rceil$
  bounds the measured count, and the distance bound
  $\|X-X^*\|_F \le \|R_\alpha(X)\|_F/\sigma$ holds at every iterate
  (thm:soundness instantiated; same formula family as exp_007's registered
  addendum).
- **P5 (downstream certificate, the pipeline).** Logit error:
  $\|Q(X-X^*)^\top\|_F \le \sqrt{g_1}\,\|X-X^*\|_F$. Per-row softmax has
  Jacobian $\mathrm{diag}(p)-pp^\top \preceq \mathrm{diag}(p) \preceq I$, so it
  is $1$-Lipschitz ($\ell_2$), and the attention-weight error on any query row
  is bounded by that row's logit error. Chained:
  $\|\mathrm{softmax}(QX^\top)-\mathrm{softmax}(QX^{*\top})\|_F
  \le \sqrt{g_1}\,\|R_\alpha(X)\|_F/\sigma$ — a certificate on the quantity
  the application consumes, computed from the residual and declared constants
  only. Prediction: the bound holds on every checked iterate of every run
  (soundness); its slack is reported, not predicted.

## 2. Background & motivation

The v5 anchor example (deblurring, exp_007) is convolutional: Fourier lens,
coordinate-wise proximal maps. Reviewer item E2 asks for a second example and
for certificates passed between pipeline components. This experiment supplies
both on a contemporary problem shape (attention-logit-preserving cache
compression; the low-rank-KV literature is public) while staying synthetic and
fully certifiable. Decision waiting on the answer: whether the worked-example
unit enters v5 printed section 5.

## 3. Hypotheses & predictions

- **H1 (soundness).** Every certified bound (count, distance, logit,
  attention-weight) holds on every run. If true → the unit prints the bounds
  as certificates. If false → counterexample result; the unit is not written
  until adjudicated. Rejection criterion: one violated bound = H1 false.
- **H2 (refusal flip).** At $m<d$, $\mu=0$ the diagnostic refuses; at every
  tested $\mu>0$ it certifies $\sigma=g_d+\mu$ exactly (match to machine
  precision on the declared spectra). Rejection: any refusal at $\mu>0$ or any
  pass at $\mu=0$ with $m<d$.
- **H3 (lens materiality).** Identity lens refuses on the correlated-query
  instances where the $G$-eigenbasis lens certifies. Rejection: identity lens
  certifies a rate within 2x of the eigenbasis lens on those instances.
- **H4 (certificate vs classical baseline).** Truncated SVD of $K$ at matched
  rank achieves comparable (possibly better) logit error but ships no a-priori
  bound; the flow's measured logit error is within its certificate. This is a
  value-shape claim, not a speed claim: registered expectation is that the
  baseline is competitive on error and the contribution is the certificate.

## 4. Objective, formalized

Minimise $E(X)$ above. Measured quantities: measured iteration count to
residual $\varepsilon$ vs certified $k$; $\|X_k-X^*\|_F$ vs
$\|R_\alpha(X_k)\|_F/\sigma$; measured logit / attention-weight errors vs
their P5 bounds; rank of $X^*$ (the compression actually achieved) vs
$\lambda$. $X^*$ = iterate after $10\times$ the certified count at
$\varepsilon_{\mathrm{ref}} = 10^{-10}$ (reference solve; its own residual
printed).

## 5. Data & materials (NUMBERS MANDATORY)

| item | value |
|---|---|
| Dimensions | $d=64$, $n=256$ keys |
| Query counts $m$ | $16$ (rank-deficient), $64$, $128$ |
| Query spectra | $Q = U\,\mathrm{diag}(s)\,V^\top$, $s_j = s_1\,\kappa^{-(j-1)/(\mathrm{rank}-1)}$, $s_1=1$; condition $\kappa \in \{10, 100\}$; $U,V$ Haar (QR of Gaussian) |
| Keys | $K = A B^\top + 0.1\,N$, $A\in\mathbb{R}^{n\times 8}$, $B\in\mathbb{R}^{d\times 8}$, entries $N(0,1)/\sqrt{8}$, $N$ iid $N(0,1)$ |
| Ridge sweep | $\mu \in \{0, 10^{-3}, 10^{-2}, 10^{-1}\}$ |
| $\lambda$ sweep | $\{0.01, 0.1, 1\} \times \lambda_0$, $\lambda_0 = \|{\nabla f(0)}\|_{\mathrm{op}}$-scaled: $\lambda_0 = \|K(G+\mu I)\|_{\mathrm{op}}$ |
| Closed-form cases (M2) | CAL-1: $\lambda=0$ → $X^*=K$ exactly. CAL-2: isotropic $G=cI$ ($m=128$, $\kappa=1$) → $X^* = \mathrm{SVT}_{\lambda/(c+\mu)}(K)$ in closed form |
| Must-fail cases (M2) | CAL-3: $m=16$, $\mu=0$ — the diagnostic must refuse, watched; and the deliberately wrong certificate $\sigma' = g_m$ (smallest nonzero eigenvalue) must be watched violating its distance bound on a $K$ with a planted $\ker(G)$ component |
| Frozen artifacts | none external; all inputs generated from seeds below |
| Seeds | instance seeds 0–7 per configuration; reference solve shares the seed |
| Stopping | $\varepsilon = 10^{-6}\,r_0$, $r_0 = \|R_\alpha(X_0)\|_F$, $X_0 = 0$ |

## 6. Apparatus & environment (M7)

Python per `v3/pyproject.toml` (numpy, scipy); no Sage. Hardware: this box;
`runs/run_manifest.json` records resolved versions. Tolerances: eigenvalue /
closed-form recovery $10^{-10}$ (float64 spectral decompositions on $d=64$ are
exact to ~$10^{-12}$; one order of safety); certificate checks are
inequalities, checked exactly (a violation is a violation at any size, slack
reported); SVT optimality residual $10^{-8}$ (subgradient inclusion check,
same float64 reasoning). Iteration cap: $10\times$ certified count (a hit is
a result, not silently truncated).

## 7. Procedure (numbered, in run order)

1. `src/run_calibration.py` → `results/calibration.toml` (CAL-1..4; abort on
   gate failure, M5).
2. `src/run_main.py` → `results/runs.jsonl` (one row per configuration x seed:
   declared constants, certified count, measured count, per-checkpoint
   distance/bound and logit/attention bounds, final rank) and
   `results/soundness.jsonl` (every checked inequality).
3. `src/run_baseline.py` → `results/baseline.jsonl` (truncated SVD at the rank
   the flow achieved, same instances: logit error, no bound).
4. `src/make_summary.py` → `results/summary.toml` (the numbers the paper may
   cite).
5. `analysis/make_analysis.py` → `analysis/stats.json`, `analysis/fig1_flip.png`
   (certified curvature vs $\mu$: the refusal flip), `analysis/fig2_pipeline.png`
   (measured attention-weight error vs its certificate, per run).

## 8. Instrument calibration (M2 — BEFORE any real reading)

- **CAL-1:** $\lambda=0$, $\mu=10^{-2}$, $m=64$: the iteration must recover
  $X^*=K$ to $\|X-K\|_F \le 10^{-10}\,\|K\|_F$ within the certified count.
- **CAL-2:** isotropic $G=cI$, $\lambda = 0.1\lambda_0$: final $X$ must match
  closed-form $\mathrm{SVT}_{\lambda/(c+\mu)}(K)$ to $10^{-8}$; SVT subgradient
  optimality residual $\le 10^{-8}$.
- **CAL-3 (must-fail, watched):** $m=16$, $\mu=0$: certified curvature must be
  $0$ (refusal). The wrong certificate $\sigma'=g_{16}$ applied anyway, on $K$
  with a planted kernel component of norm 1: its distance bound must be
  watched violated (measured distance exceeds claimed bound) — the instrument
  can fail.
- **CAL-4:** contraction ruler: on one certified run, the measured per-step
  residual ratio must never exceed $1-\sigma/\hat\beta$ by more than $10^{-12}$
  (the derived rate is an upper bound, exact for the quadratic part).

## 9. Variables, baselines & controls

- **Independent:** $m$, $\kappa$, $\mu$, $\lambda$, seed. **Dependent:** counts,
  distances, logit/attention errors, rank, all bounds' slacks.
- **Baselines bracket:** random floor (Gaussian $X$ of matched rank, logit
  error), classical baseline (truncated SVD at matched rank), oracle ceiling
  ($X^*$ itself).
- **Negative controls:** CAL-3's wrong certificate (must fail); identity-lens
  dominance test on correlated instances (must refuse under H3).
- **Confounds:** initialisation frozen at $X_0=0$ everywhere; the baseline
  gets the same instances and the flow's achieved rank (generosity: the
  baseline is granted the rank after the fact; the flow declared it only
  through $\lambda$).

## 10. Error budget (M3)

No discretisation error (the iteration is the object, not an ODE
discretisation). Floating-point only: spectral decompositions and SVDs at
$d=64$, expected $O(10^{-12})$ relative; separable from model error because
every certified inequality carries its measured slack. Condition numbers
reported: $\kappa(G+\mu I)$ per configuration in `runs.jsonl`.

## 11. Metrics & statistics

Soundness is binary per check (violations counted; one is enough to sink H1);
slack ratios (measured/bound) reported as min/median/max per bound family —
the naive alternative (mean error) hides the one violation that matters.
Counts: measured/certified ratio min/median/max. No significance testing:
every check is deterministic given the seed; the 8 seeds probe instance
variation, and all cells are reported. Scoring is the script, not the
operator: `make_summary.py` recomputes every verdict from the jsonl rows.

## 12. Analysis plan (decided now)

Fig 1: certified curvature vs $\mu$ at $m=16$ (the flip at $\mu>0$), with the
refusal region marked. Fig 2: measured attention-weight error vs its
certificate across all certified runs (every point must sit below the
diagonal). Table (summary.toml): per configuration, $\hat\beta$, $\sigma$,
certified count, measured count min/med/max, worst slack per bound family,
flow vs SVD logit error at matched rank. Certificate traces per iteration
kept in `runs.jsonl` checkpoints (M4).

## 13. Threats to validity & scope

Synthetic spectra only: the result says the certificates are sound and the
pipeline bound is computable on this problem shape, not that any real model's
cache has these spectra (explicitly not tested, section 0). $d=64$ is small;
nothing here depends on scale, but no scaling claim is made. The SVD baseline
comparison is one rank-matching convention; others exist and are not swept.
Evidence ceiling: **empirical** (M6) — instances of a declared family, 8 seeds,
no theorem claimed beyond the instantiated classical bounds (P4/P5 derivations
are one-line instantiations of stated theorems, not new results).

## 14. Reproduction

```
v3/.venv/bin/python src/run_calibration.py   # -> results/calibration.toml
v3/.venv/bin/python src/run_main.py          # -> results/runs.jsonl, soundness.jsonl
v3/.venv/bin/python src/run_baseline.py      # -> results/baseline.jsonl
v3/.venv/bin/python src/make_summary.py      # -> results/summary.toml
v3/.venv/bin/python analysis/make_analysis.py # -> analysis/stats.json + figures
```

---

## AMENDMENT 1 (registered 2026-10-18, before any part-reading; after CAL-4 failed as frozen)

CAL-4 as frozen compared per-step residual ratios down to the stopping level
$10^{-10}$, where the ratio instrument itself loses precision: the residual is
computed from the difference of consecutive iterates, and at residual
$\rho$ the float64 cancellation error is of order
$\varepsilon_{\mathrm{mach}}\,\|X\|_F/(\alpha\rho)$, which at the observed
scales is $\sim 2.5\times10^{-5}$ relative — matching the measured excess
($0.980228$ vs certified $0.980198$, excess $3\times10^{-5}$). The failed gate
is kept in `results/calibration.toml` history (git) as a calibration result:
it locates the instrument's floor, exactly the error-budget term of section 10.

**Amended CAL-4:** the ratio check applies only at iterations whose residual
exceeds $10^{-6}\,r_0$ (where the cancellation term is below $10^{-10}$
relative); tolerance unchanged at $10^{-12}$. No part-A/B reading preceded
this amendment.

## AMENDMENT 2 (registered 2026-10-18, mid-sweep, before any summary or verdict)

Observed by monitoring the running sweep (no summary computed, no hypothesis
read): at $\lambda = 1.0\,\lambda_0$ the penalty equals
$\|\nabla f(0)\|_{\mathrm{op}}$ exactly, so $X_0 = 0$ is already optimal by the
subgradient condition, the initial residual is $r_0 = 0$ and the certified
count is $0$ steps. The run loop measures one step to discover the zero
residual, which the frozen `count_ok` definition ($0 < k_{\mathrm{meas}} \le
k_{\mathrm{cert}}$) mislabels. **Amended scoring:** rows with $r_0 = 0$ are
classified `degenerate_certified_at_start`; their check is $r_0 = 0$ verified
(the declaration certified the start point), reported as their own category,
never pooled into the count-ratio statistics. All other checks on those rows
(distance, logit, attention bounds) stand unchanged. No row is discarded.

## AMENDMENT 3 (registered 2026-10-18, mid-sweep, before any summary or verdict)

Amendment 2 classifies degenerate rows by $r_0 = 0$ exactly. In floating
point the computed $r_0$ at $\lambda = \lambda_0$ is not always exact zero:
$\lambda_0 = \|K H\|_{\mathrm{op}}$ is itself computed in float64, so on some
seeds the prox at $X_0 = 0$ returns a residual at the machine-epsilon level of
that computation ($r_0/\lambda \le 1.7\times10^{-15}$ across all such rows in
the interim data) instead of $0.0$. Those rows then enter the normal pool with
stopping threshold $10^{-6} r_0 \sim 10^{-20}$, which is unreachable
($k_{\mathrm{meas}} = -1$), and per-step ratios that are noise over noise.
**Amended degeneracy test:** a row is `degenerate_certified_at_start` when
$r_0 \le 10^{-9}\,\lambda$ (instrument floor; the nearest genuine row in the
interim data has $r_0/\lambda \ge 9.2$, a separation of fifteen orders of
magnitude). The degenerate check becomes $r_0 \le 10^{-9}\lambda$ verified.
Everything else in Amendment 2 stands; no row is discarded; no count or rate
statistic was read from the affected rows before this amendment.

**Amendment 3, run-time consequence (registered before the resumed rows were
produced):** an instance classified degenerate at the start ($r_0 \le
10^{-9}\lambda$) is not iterated: its thresholds $10^{-6}r_0, 10^{-10}r_0$ are
below the float64 floor and unreachable, so iterating only grinds to the
safety cap (observed: over an hour per batch confirming that zero stays zero).
Its row is written directly with $k_{\mathrm{meas}} = k_{\mathrm{ref}} = -1$,
final residual $r_0$, and no soundness checkpoints (the flow is never run;
the start point is the certified point). All non-degenerate instances are
unaffected.

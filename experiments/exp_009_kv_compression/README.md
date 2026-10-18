# v3 experiment template

Inherited from the author's engineering experiment standard
(`gfd_inference/external/gfd_context_synth/design/v2.0/_experiments/_template/`),
upgraded for mathematical work per `project_plan/v3_experiment_system.md`
(M1–M8). A number in a chat is not an experiment; an experiment is a
reproducible chain of artifacts a stranger could re-run.

## How to use

1. **Copy the whole folder** to `../exp_NNN_<slug>/`; register the track in
   `../INDEX.md` at creation time.
2. **Fill in order:** `experiment/exp_method.md` FIRST and **FREEZE it**
   (hypotheses, derived predictions, rejection criteria, data with sizes,
   calibration, controls, statistics — all before the run, never moved
   after). Then `src/`, run → `runs/`, `results/`, `analysis/`, `report/`,
   and `experiment/scorecard.md` LAST.
3. **Tick the done-checklist** before calling it banked.

## Folders

| Folder | Required artifact | Exists so that… |
|---|---|---|
| `experiment/` | `exp_method.md` frozen before the run | gates and analysis can't move after seeing results |
| `experiment/` | `scorecard.md` filled last | "did you show it?" has a scored answer, not a vibe |
| `src/` | the harness (SageMath scripts) | the measurement is code, re-runnable |
| `runs/` | `run_manifest.json`: commit, seeds, env, reproduce commands | a stranger regenerates the numbers cold |
| `results/` | frozen inputs + raw per-item numbers + **certificate traces** (M4). **Format rule (author, 2026-07-23):** bulk experimental data (traces, sweeps, per-item measurement tables) = **Lance datasets** (compressed, columnar, no JSON shard exhaust); small configuration and gate records a human opens in an editor (calibration verdicts, instance summaries, stats) = JSON | claims trace to per-iteration data, not an average |
| `analysis/` | `make_analysis.py` + `stats.json` + figures | numbers carry uncertainty and the picture |
| `report/` | `REPORT.md` (technical, figures embedded) + `one_pager.md` (four perspectives, M8) | legible to referee and cold reader |

## Invariants (every experiment, non-negotiable)

Inherited: brief frozen first · every hypothesis has if-true AND if-false
predictions, each driving a decision · pre-registered rejection criteria ·
baselines bracket (random floor + dumb/classical + oracle ceiling) · a
negative control that CAN fail and is **watched failing** before real data ·
CIs + paired tests, all cells reported · cost beside quality · dials swept
to collapse, never to the best point · no self-scoring · not-proven declared
up front.

Mathematical (M1–M8, defined in `project_plan/v3_experiment_system.md`):

- **M1** the brief names the claim (Q1–Q5) / theorem / TC entry whose
  registered prediction it tests, and derives the prediction (slope, not
  direction).
- **M2** instruments calibrate on **closed-form problems** (declared
  spectrum, known minimiser, known rate) and must-fail counterexamples
  (e.g. `diag(1,−5)`) before touching unknowns. Lessons banked from
  exp_003: a rate instrument needs a LOW-κ calibration case (κ≈5 —
  competing rate formulas agree within 5% above κ≈40, so a high-κ gate
  cannot tell them apart); trace fits need an FP-floor guard
  (fit only where grad_norm > 10⁻¹²·g₀); a registered rate prediction
  must NAME THE STEP RULE it is derived for (1/L → 1−1/κ; optimal
  2/(L+γ) → (κ−1)/(κ+1)).
- **M3** error budget separated: model / discretisation / floating-point;
  condition numbers reported at every linear solve or eigenproblem.
- **M4** per-iteration certificate traces (descent, residual, η, γ,
  invariant drift) are primary artifacts in `results/`.
- **M5** a structured failure emits a counterexample entry (minimal
  reproduction, what it violates) → report + `../INDEX.md` ledger +
  `theorem_candidates.md` pointer where relevant.
- **M6** verdicts carry a rung: empirical / conditional / counterexample.
- **M7** manifest pins SageMath version, package set, ALL seeds (symbolic =
  seedless, stated); tolerances declared in the brief with one-line
  justifications.
- **M8** the one-pager reads four ways: business, CS, mathematics, physics.
  A strained perspective is itself reportable.

## Done-checklist

- [ ] `exp_method.md` frozen BEFORE the run — all 14 headings filled (or one line why n/a)
- [ ] M1: claim/TC named; predictions derived with slopes; rejection criteria pre-registered
- [ ] §4 data quantified (problem sizes, spectra, seeds) — an unquantified setup voids the method
- [ ] M2: calibration on closed-form truth PASSED and must-fail case WATCHED failing, before any real reading
- [ ] baselines bracket: floor + dumb/classical + ceiling in every table
- [ ] `runs/run_manifest.json`: git sha, SageMath + package versions, seeds, tolerances, reproduce commands
- [ ] `results/`: frozen inputs + raw per-item numbers + certificate traces (M4)
- [ ] M3: error sources attributed or "not separable here" stated; condition numbers reported
- [ ] `analysis/`: `make_analysis.py` + `stats.json` (CIs + paired tests) + `*.png`
- [ ] `report/REPORT.md`: every figure embedded with a read-this annotation
- [ ] `report/one_pager.md`: four perspectives (M8)
- [ ] `scorecard.md`: scored; which claim is significant AND which is not, stated
- [ ] M6: verdict rung declared in `../INDEX.md`
- [ ] M5: any structured failure logged as a counterexample entry

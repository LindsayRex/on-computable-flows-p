# exp_010 — scorecard (filled LAST, 2026-11-02, after the readings)

Numbers are from the second full run (2026-11-02, after the harness repairs demanded by the dossier's stage-2 audit: exact-leaf majorants in the bound, assassination P1-01 and P2-06; a guard that flags products flushed to zero and non-finite values, P1-02; tiers deciding only under their own guard, P2-02). Every count of the first run was reproduced exactly; only the wall-clock figures differ.

Evidence calculus inherited from the engineering standard:
`C_D^exp = φ_method · φ_repro · φ_discriminant · φ_determinism`
(each φ ∈ {0, 0.5, 1}; the product is the score — one hard zero zeroes the
delivery).

| φ | gate | outcome | evidence |
|---|---|---|---|
| φ_method | brief frozen before run; predictions derived (M1); rejection criteria pre-registered; nothing moved after | 1 | brief frozen and committed (sha256 `b59436c8...`, commit e7a4b55) before `--calibrate`; seven predictions with derivations and failure readings; nothing in the brief moved after the run. The post-hoc checks below are labelled post hoc in `analysis/stats.json` and `results/summary.toml` (`[post_hoc]`). |
| φ_repro | manifest complete (M7); a stranger could re-run cold; artifacts frozen with shas | 1 | `runs/run_manifest.json` (git sha, brief sha256, Python, numpy 2.4.6, scipy 1.17.1, PyWavelets 1.8.0, mpmath 1.3.0, seeds, K, thread setting, commands, times); `§14` commands; `exp_007`'s constructors imported by path, so the data are exp_007's. |
| φ_discriminant | calibration passed AND must-fail watched failing (M2); baselines bracket; control that can fail present | 1 | CAL-1..5 passed (`results/calibration.json`, 200/200 containments); CAL-2 watched must-fail failed as required (102/200 with e/1000); P5 mutant produced 22 false accepts (watched must-fail, failed as required); baselines bracket: rule (a) floor, rule (b) classical, tier 2 at every step ceiling. |
| φ_determinism | seeds pinned / symbolic stated; tolerances pre-declared; error budget attributed (M3) | 1 | seeds 0–3 pinned, `rng(42)` for calibration; CAL-5 bitwise determinism passed; no tolerance in the certificate; the error budget is the subject and is attributed by construction (§10). |

**C_D^exp = 1**

## Registered predictions, scored mechanically (`analysis/make_analysis.py`)

| P | registered | outcome | reading |
|---|---|---|---|
| P1 | rule (c) makes zero false accepts (accept while the true energy rose), every step, every run | **FAILED** (22 of 1044 accepts, all on the smooth arm, all in branch 3 at tier 2) | The registered derivation over-claimed. Proposition 2 gives `E(z⁺) ≤ hi < B_k` and `B_{k+1} < B_k`; it does not compare `E(z⁺)` with `E(z_k)`. The registered derivation was a non sequitur. Post hoc, the certified statement held at all 1280 steps: 0 containment failures, 0 accepts with `hi ≥ B_k`, 0 accepts whose rigorous true energy was not below `B_k` (this concerns Proposition 2's clauses (i), (iii) and the accept-step inequality; `B` is not nonincreasing across classifier-mode rejects, where the protocol re-initialises it). The 22 rises are at most 2.9e-14 absolute (5.2e-13 of E), below the float64 tier's own resolution, and all occur after a reject re-initialised `B` from the looser tier-1 enclosure (classifier-mode carry, §4). Filed as M5: a counterexample to the registered reading of P1, not to Propositions 1 or 2. |
| P2 | plain float rule (a) makes ≥ 1 false accept in K steps on the smooth arm, some seed | passed (6, 1, 6, 3 false accepts on seeds 0–3; also 42–57 false rejects per run on both arms) | the band produces both kinds of error for the plain test |
| P3 | rule (b)'s false accepts equal rule (a)'s step for step | **FAILED** on the ℓ1 arm (19/14/18/36 against 10/7/9/15); equal on the smooth arm | The registered derivation missed that (b) accepts an apparent rise whenever the interval enclosure of the EXACT update lies below the float previous energy. 46 such accepts, every one a true rise of the STORED float32 point by 6.3e-11 to 9.7e-9: holes 2 and 3 of the source design observed, which is stronger evidence against the one-sided design than the registered equality would have been. (b)'s false accepts are a superset of (a)'s in every run. |
| P4 | `k_band ∈ [20, 120]` on the smooth arm, branch 1 throughout before it | passed (64, 70, 66, 67) | measured `e/(u₃₂E)` is 6.8e3 to 6.9e3 on the smooth arm and 4.3e3 on the ℓ1 arm, i.e. `C = e/(d u₃₂ E) ≈ 17–27`, above the brief's guess of 2–8; the onset still fell in the registered window |
| P5 | mutant bound e/1000 must produce a false accept (watched) | passed (22 false accepts over the four mutant runs) | the test has power against a wrong bound |
| P6 | tier 1 ≤ 5× float32 evaluation; tier 2 ≤ 10⁴× | passed (1.79×; 346×) | in the band tier 1 decided 86/97, 83/91, 86/95, 85/94 steps on the smooth arm and every band step on the ℓ1 arm; tier 2 fired on 8–11 steps per smooth run and never on the ℓ1 arm; the rule's wall time over 160 steps was 0.3 s (ℓ1) and 1.7–2.3 s (smooth) against 0.15 s for the plain float evaluation and 50 s for tier 2 at every step |
| P7 | live rule reaches the float32 fixed point or the cap with zero branch-2 rejects, smooth arm | **FAILED** in its stopping clause, passed in its branch-2 clause | zero certified rises in every live run (both arms); seeds 1 and 2 reached the bitwise float32 fixed point (141 and 146 steps, 7 and 9 halvings); seeds 0 and 3 exhausted the ten halvings at undecided steps (139 and 154 steps), as did every ℓ1 run (53–59 steps). An undecided step at 113 bits is a true energy change below about 1e-15 of E; the brief did not register this stopping state. |

## Claims

- **Significant (empirical, this run, these seeds):** the repaired two-sided margin rule issued, at every one of
  1 280 classifier steps, exactly what Proposition 2 says: an accepted point's rigorous enclosure lies strictly
  below the carried bound, so the bound drops strictly at every accepted step (0 violations; across the
  classifier-mode rejects the bound is re-initialised by the measurement protocol, which the proposition does not cover). It made 0 false rejects on every run
  where the plain float test made 42–57 and the one-sided design made 2–25. Rigour cost about 2× (ℓ1 arm) to
  15× (smooth arm) the plain float evaluation over 160 steps, against 346× per step for interval arithmetic
  throughout, because the float64 tier decided almost every band step. The float32 margin decided every step
  before the band onset (steps 64–70 on the smooth arm, 44–49 on the ℓ1 arm) and no step after it.
- **Significant (empirical):** the plain float test and the one-sided design both accept steps whose true energy
  rose (P2; P3's failure), the one-sided design more often on the ℓ1 arm, by enclosing the exact update rather than
  the stored float point.
- **NOT shown:** descent of the energies themselves in the band. The rule certifies `E(z_{k+1}) < B_k`, not
  `E(z_{k+1}) < E(z_k)`; in 22 accepted steps the true energy rose by up to 2.9e-14 inside the bound's slack
  (P1 as registered FAILED; see the table). A stricter test against the lower endpoint `A_k` would certify true
  descent at the price of rejecting every step whose true decrease is below the enclosure width; not run (not in the
  frozen brief). Nothing about rates, accuracy, or the step map's float32 deviation (which produced true rises of
  order 1e-9 on the ℓ1 arm at 51 of 160 steps, all caught by the rule as band steps and none certified as rises).
- **Verdict rung (M6):** **empirical** for every count above; **conditional** for the certificate (Propositions 1
  and 2 of dossier B72-SND, stage recorded there).
- **Counterexamples emitted (M5):** (i) to the registered reading of P1 ("accept implies the true energy fell"):
  22 steps, listed in `analysis/stats.json` under `predictions.P1` and `post_hoc.P1_failures_c`; (ii) to the
  registered P3 (equality of (b) and (a)): 46 steps, `post_hoc.P3_failures_b_only`. Neither touches Propositions
  1 or 2; both are corrections to what the brief said the rules would do.

## Declared limits

As §13: one energy, one dimension, one signal family; the a priori bound is specific to the direct evaluation order
(the FFT step map is not certified); mpmath's interval arithmetic is assumed correct (CAL-4 checks one exact case);
four seeds. Confirmed still true after the run. Added after the run: the classifier-mode carry (re-initialising `B`
from a tier-1 enclosure of a rejected point so that the fixed trajectory can continue) is a measurement protocol,
not part of the rule; the live mode carries `B` only through accepts.

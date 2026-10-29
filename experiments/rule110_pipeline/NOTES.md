# Rule 110 as a pipeline of certified flows: claims ledger

## Provenance
Written by Claude at the author's direction, 2026-10-19 ("I think we should do an additional
stronger rule 110 construction. I don't really care for the page length anymore. What I care
about is communicating the idea clearly."). This is the strong form of card #49, the build that
triage item T2 kept available as morning-package item 9a. It strengthens, and does not replace,
experiments/rule110_flow (the weak construction stays as the paper's first Rule 110 unit).

## What this is
An executable witness for the strong per-step theorem: one step of Rule 110 computed by a
pipeline of three certified flows in which NO product of the data is ever evaluated outside a
flow. The old construction's stated boundary was that the target t(x) = c + r - cr - lcr is a
closed-form polynomial evaluated when the energy is declared; the flow then reproduces a number
computed outside the dynamics. Here the declared data vectors and the gradient oracles are
affine in the data (the declared energy is quadratic in it), and the two multiplications are
performed by the grammar's projective primitive, because for binary a, b

    a*b = clamp(a + b - 1),    clamp = prox of the indicator of [0,1]^n (a convex set).

Note the typing upgrade over the old unit: the old read-out threshold (projection onto {0,1}^n)
is NOT the projective primitive because that indicator is not convex; the box [0,1]^n IS convex,
so the clamp here is a bona fide projective primitive, properly typed, inside the dynamics.

Three stages per automaton step (P: pair products c*r; Q: triple products l*(c*r); Y: the affine
assembly y = Sx - p - q), each a forward-backward flow with beta = sigma = 1, each stopped on its
own certificate (certified distance < 1/2) and read out by the computability section's rounding
(the minimiser of every stage is a binary vector, so the rounding is exact). The rounded report
is the next stage's declared data. Rounding between stages is why no error accumulates across
stages or rows: the pipeline computes exactly, for every row length and every number of steps.

## The single summed energy (construction B; dossier statements R8-R12)
The registered programme target ps:rule110-stitched asked for a single composed energy whose
fixed point IS the next row. Taken literally that is false for the summed energies of this form:
an active clamp leaves a residual, later terms backreact onto earlier blocks, and the joint
minimiser is not the cascade point and not the next row on rows with a bad cell (neighbourhood
(0,0,1) or (0,1,0)). Verified in exact arithmetic (KKT for the convex QP, Fractions module):

- n = 1, x = (0): joint minimiser (0,0,0), min E = 1 > 0 (y-block still correct here);
- n = 5, x = (0,0,1,1,1): joint minimiser p* = (0,1/2,1,1,0), q* = (0,0,0,1,0),
  y* = (0,1/2,1,0,1), min E = 3/4, and max_i |y*_i - t_i| = 1/2 EXACTLY. Cell 2 of the
  minimiser sits at distance exactly 1/2 from both binary values, so the threshold-1/2
  read-out has margin 0 there and cannot be issued.
- The cascade point is not even block-stationary in general: at n = 3, x = (0,1,0), the exact
  block-p resolve moves p from (0,0,0) to (1/3,1/3,0).

What IS true (dossier theorem R12, battery entry [single_energy_readout]): the minimiser's
y-values at unit weights lie in {0, 1/2, 1}, with 1/2 exactly at the bad cells, so the
threshold-1/4 read-out recovers the next row with margin 1/4, and a residual certificate
licenses it: declared pair beta-hat = 18/5, sigma-hat = 3/25, forward-backward at
alpha = 5/18, accept when ||R_alpha||^2 < (sigma-hat/4)^2, then certified distance < 1/4.
So the single summed energy is a SECOND valid construction of the step: one declaration, one
read-out per step at threshold 1/4, against the pipeline's three stages with margin-1/2
hand-offs. For weights w1 > w2 the plain threshold-1/2 read-out also works, with margin
(w1-w2)/(2(w1+w2)); for w1 <= w2 it fails on every row with a bad cell (negative controls in
the battery).

The joint energy is sigma-strongly convex with sigma = lambda_min of [[3,0,1],[0,2,1],[1,1,1]]
(per cell; the Hessian is this 3x3 tensored with the identity), the smallest root of
l^3 - 6 l^2 + 9 l - 1, approx 0.120615. Nothing is wrong with the stitching theorem; what is
false is only the literal reading of the registered target (the minimiser itself is never the
next row on rows with a bad cell, for every positive weighting).

## What the battery shows (summary.toml is the artifact; deterministic, seed 110)
- Exhaustive: every row of every length 1..12 (8190 rows), one pipeline step equals the
  reference step, with one inner iteration per stage at alpha = 1.
- Trajectory: 512 steps on a random length-256 ring agree with the reference at every step, at
  alpha = 1 (1 iteration/stage) and alpha = 0.4 (at most 7/6/7 iterations for stages P/Q/Y).
- Certificate audit: at alpha = 0.4 the worst observed per-stage counts (7, 6, 7) EQUAL the
  counts predicted from the declared numbers alone (q = 0.6, start residual, eps = 0.49); the
  certificate is checked, never trusted.
- Minimiser witnesses verified by exact-arithmetic KKT as above.
- Construction B ([single_energy_readout]): the threshold-1/4 read-out equals the reference on
  all 8190 rows of lengths 1..12 (IEEE double; worst accepted index 69 against the a-priori
  bound 185 from the declared numbers), on all 510 rows of lengths 1..8 re-run in EXACT rational
  arithmetic (Fractions; soundness and the 29/30 residual contraction checked exactly, zero
  violations), and on a 512-step length-256 trajectory (IEEE double; worst accepted index 108 against the
  bound 231). Negative controls: threshold 1/2 at unit weights hits the tie (margin 0); weights
  (1,2,1) put the bad cell at 1/3, which threshold 1/2 misreads; weights (2,1,1) read the row
  with margin 1/6.

## What this is NOT (claims ladder)
- NOT the theorem. The strong per-step statement goes through the proof pipeline (drafted,
  assassinated, adjudicated, Lean tier recorded) before the manuscript states it as one.
  This file is the empirical witness that the construction is real and the statement shape
  is right, plus the exact minimiser witnesses.
- NOT a universality proof. Rule 110's universality is Cook's theorem, cited, never re-proved.
- NOT a performance claim. Three certified stages per automaton step is more work than one
  table lookup, reported as such; the point is that the computation, multiplications included,
  runs inside the grammar under certificates.
- The alpha = 1 collapse to one iteration per stage is this energy family's perfect
  conditioning (beta = sigma per stage), reported as such, same as the old unit.
- The harness between stages moves certified, rounded reports and re-declares the next stage's
  energy; it computes no product of data entries, and its one nonlinear operation is the
  comparison with a threshold. The row-to-row stepping is the same re-declaration, stated
  plainly in the unit.

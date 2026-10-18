# Rule 110 as a flow: claims ledger

## Provenance
Written by Claude at the author's direction, 2026-10-17 ("write your own rule 110 program then
in experiments"), after the search of On-Computable-Flows, gfd_cpu (all of HEAD) and
flow_research (main, dev, dev5) found the author's original Windows-machine implementation
committed nowhere (research_log/LOG.md, 2026-10-17 late entries). This replaces the import that
card 28 was waiting for.

## What this is
An executable witness for the per-step theorem (card 49): one step of Wolfram's Rule 110,
computed not by table lookup but by a flow in the paper's grammar.

- The Rule 110 update is the polynomial t = c + r - cr - lcr on {0,1} neighbourhoods
  (checked against the truth table on all 8 neighbourhoods, in code).
- The declared energy is E(y) = 1/2 ||y - t(x)||^2: one smooth term, beta = 1, sigma = 1.
- The dynamics is the dissipative primitive (explicit Euler on the gradient flow) at the
  constructed step alpha = 1/beta-hat = 1, or any alpha in (0,1].
- The certificate is the paper's: residual = gradient norm, distance <= residual/sigma
  (soundness, regime A), stopping rule residual <= eps, rate q = 1 - alpha*sigma.
- The read-out is the projective primitive: threshold at 1/2, EXACT whenever the certified
  distance is below 1/2, because the minimiser t(x) is a {0,1} row.
- The lens: the Hessian is the identity, dominance ratio 0 in the identity lens; every
  orthonormal lens leaves it the identity. The mandatory-lens declaration is trivial here,
  and the notes say so rather than dressing it up.

## What the battery shows (summary.toml is the artifact; deterministic, seed 110)
- Exhaustive: for every row of every length 1..12 (8190 rows), one flow step equals the
  reference step. Per-step exactness is not sampled at these lengths, it is checked completely.
- Trajectory: 512 steps on a random length-256 ring agree with the reference at every step,
  at alpha = 1 (one inner iteration per step: the energy is perfectly conditioned) and at
  alpha = 0.4 (eight inner iterations per step).
- Certificate audit: at alpha = 0.4 the observed inner-iteration count (8) meets the count
  predicted from the declared numbers alone (8); the certificate is checked, never trusted.

## What this is NOT (claims ladder)
- NOT the theorem. Card 49's per-step statement (for all row lengths, or on the periodic
  background) goes through the proof pipeline: drafted, assassinated, adjudicated, Lean tier
  recorded. This file is the empirical witness that the construction is real and the statement
  shape is right.
- NOT a universality proof. Rule 110's universality is Cook's theorem and is cited, never
  re-proved (CLAUDE.md writing rule 4; V5_PLAN).
- NOT a performance claim. Nothing here says a flow computes Rule 110 fast; the point is
  expressiveness with certificates, the "no missing power" demonstration (V5_PLAN 1b).
- The alpha = 1 case collapses to one exact inner iteration because this energy has beta =
  sigma: that is a statement about this energy's perfect conditioning, honestly reported,
  not hidden behind a smaller step.

## Status of the original (the author, 2026-10-17)
There is no separate Windows implementation. The author merged everything from the Windows
machine into flow_research on the morning of 2026-10-17; what was there (006_maxSat/d-cpu,
imported as experiments/d-cpu) is all of it, and it contains no Rule 110 code (searched). The
V4_FIX_NOTES line of 2026-10-11 about uncommitted Windows code is obsolete. This file is THE
Rule 110 implementation for the paper. Nothing in the manuscript cites its numbers yet.

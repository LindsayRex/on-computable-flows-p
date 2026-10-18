# exp_008 — Constructed chaos: Lorenz-like fields against the diagnostic (one-pager, four readings — M8)

![headline](../analysis/fig1_ramp.png)

**Business.** The diagnostic's sales pitch is "measure before you spend". This run
bought the missing half of that pitch: evidence from a problem *built to be
unsolvable* by these methods. Every certificate the diagnostic issued on the chaotic
family held (0 violations in 82 + 72 checks), and where it could not certify, it
refused rather than guessed. The decision it unlocks: the chaos step (roadmap card
#4) can be designed as a one-sided instrument with honest wording, and a "dynamic
null" unit is now a concrete candidate for v5.

**Computer science.** Two baselines bracket the instrument. The dumb baseline
(divergence test) endorses the chaotic field at r = 28 — watched doing so. The
oracle (measured Lyapunov exponent) needs the run the certificate is not allowed to
see. Between them, the contraction test in a declared lens: pass/refuse per region
and lens, grid-certified with an exact vertex cross-check and a refinement sweep that
flipped nothing. One instrument bug (transient leaking into a Benettin window,
printing exactly 4/3 of truth) was caught from the run's own output, fixed, rerun,
and kept in history.

**Mathematics.** Identity-lens blindness is parameter-free: at sigma = 10 the
symmetric part's off-diagonal (sigma + r − z)/2 exceeds sqrt(sigma) for every r, so
no identity certificate exists even where the origin is globally stable — and none
was measured (0/257 rows). Diagonal lenses certify locally with the derived flip
r* = 1 − rho (measured 0.85/0.65/0.45 for rho = 0.1/0.3/0.5). The calibration failure
is itself a theorem-shaped fact: global asymptotic stability (the classical r < 1
Lyapunov function) does not imply contraction over the trap region (sup +21.76 at
r = 0.5). And no lens passed at r > 1, where coexisting equilibria make contraction
impossible: the forced-honesty ceiling, 20+ r-units before chaos actually starts.

**Physics.** The lattice is quadratic smoothing made literal: eight chaotic cells,
Laplacian coupling. The certificate computed before any run (c* = 28.7 from one sup
and one graph eigenvalue) guaranteed synchronisation, and every run obeyed it; the
measured threshold was 13.6 times cheaper, the usual price of a worst-case guarantee.
At certified coupling the ring beats its transverse differences flat in milliseconds
of model time, while the synchronised motion itself remains a full-strength Lorenz
attractor (lambda_1 = 0.9051 vs 0.9096 single-cell): the smoothing tamed exactly the
directions it couples and had no opinion about its blind subspace — which is what
the grammar says a quadratic term does.

**Verdict:** `empirical` — on a constructed chaotic family the diagnostic certifies
only what it can prove, refuses early and honestly, and its blind-subspace
bookkeeping is physically real.

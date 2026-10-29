#!/usr/bin/env python3
"""Rule 110 as a pipeline of certified flows (the strong construction of card #49).

Written at the author's direction (2026-10-19: build the stronger Rule 110 construction;
clarity over page length). See NOTES.md for the claims ledger.

The construction, in the paper's grammar. Row x in {0,1}^n on a ring. The Rule 110 update is
    t_i = c + r - c*r - l*c*r,   (l, c, r) = (x_{i-1}, x_i, x_{i+1}).
The old construction (experiments/rule110_flow) evaluates t(x) when the energy is declared; the
flow then reproduces a number computed outside the dynamics. Here no product is ever evaluated
outside a flow: the declared data vectors and the gradient oracles are affine in the data (the
declared energy is quadratic in it), and the two multiplications are
performed by the projective primitive (the proximal map of the convex box [0,1]^n), because for
binary a, b
    a*b = clamp(a + b - 1),   clamp = projection onto [0,1].

One automaton step = three certified stages, each a flow in the grammar, handing off through
certified read-outs (the rounding of the computability section, margin 1/2):

  stage P   E_P(p) = 1/2 ||p - (Sx - 1)||^2 + box,   (Sx)_i = x_i + x_{i+1}
            forward-backward (dissipative + projective), beta = sigma = 1;
            fixed point p* = clamp(Sx - 1) = (x_i x_{i+1}): the pair products c*r.
  stage Q   E_Q(q) = 1/2 ||q - (Tx + p^ - 1)||^2 + box,   (Tx)_i = x_{i-1},
            p^ = the certified, rounded output of stage P (data for this declaration);
            fixed point q* = clamp(Tx + p^ - 1) = (x_{i-1} x_i x_{i+1}): the triple products.
  stage Y   E_Y(y) = 1/2 ||y - (Sx - p^ - q^)||^2   (dissipative only);
            fixed point y* = Sx - p^ - q^ = t(x), a binary row; threshold read-out.

  certificate (every stage): composite residual ||R_alpha||, distance <= ||R_alpha||/sigma at
  alpha = 1/beta-hat (soundness); stage output accepted and ROUNDED only when the certified
  distance is < 1/2; the rounding is exact because each stage's minimiser is a binary vector.
  Rounding between stages is why no error accumulates across stages or rows.

The single summed energy (construction B; dossier statements R8-R12): the summed energy
    E(p,q,y) = 1/2||p-(Sx-1)||^2 + 1/2||q-(Tx+p-1)||^2 + 1/2||y-(Sx-p-q)||^2 + box(p) + box(q)
is sigma_J-strongly convex (sigma_J = lambda_min of [[3,0,1],[0,2,1],[1,1,1]], the root of
l^3 - 6l^2 + 9l - 1 in (3/25, 121/1000)). Its unique minimiser is NOT the cascade point and is
NOT the next row on rows with a bad cell (neighbourhood (0,0,1) or (0,1,0)): an active clamp
leaves a residual that backreacts onto earlier blocks, and the bad-cell y-value is exactly 1/2
at unit weights.  So the threshold-1/2 read-out cannot be issued there (margin 0), and the
literal reading of the registered target (the minimiser IS the next row) is false.  What IS
true: the threshold-1/4 read-out of the minimiser equals the next row with margin 1/4, and a
residual certificate (declared pair beta-hat = 18/5, sigma-hat = 3/25, forward-backward at
alpha = 5/18, accept when ||R_alpha||^2 < (sigma-hat/4)^2) licenses it.  Witnesses, verified in
EXACT arithmetic (KKT for the convex QP, Fractions):
  (i)  n = 1, x = (0): minimiser (p,q,y) = (0,0,0), min E = 1 > 0 (here y* = t(x) still);
  (ii) n = 5, x = (0,0,1,1,1): minimiser p* = (0,1/2,1,1,0), q* = (0,0,0,1,0),
       y* = (0,1/2,1,0,1), min E = 3/4, and ||y* - t(x)||_inf = 1/2 EXACTLY: cell 2 sits at
       distance exactly 1/2 from both binary values (threshold-1/2 margin 0; the threshold-1/4
       read-out recovers the row with margin 1/4).

Battery (all deterministic; artifact: summary.toml):
  A. exhaustive: every row of every length n = 1..12 (8190 rows), one pipeline step == reference,
     at alpha = 1 (each stage: one iteration);
  B. trajectory: n = 256 random row (seed 110), 512 steps, pipeline == reference at every step,
     at alpha = 1 and alpha = 0.4;
  C. certificate audit at alpha = 0.4: per-stage observed iteration counts equal the counts
     predicted from the declared numbers alone (rate q = 0.6, start residual, eps = sigma/2);
  D. witnesses (i) and (ii) verified by exact-arithmetic KKT;
  E. the cascade point is not even a sweep-stationary point of the joint energy in general:
     at n = 3, x = (0,1,0) the joint gradient at the cascade point pulls block p off its value;
  F. single-energy read-out (construction B, dossier R12): forward-backward on the summed energy
     at alpha = 5/18 from z0 = 0, accepted when ||R_alpha||^2 < (sigma-hat/4)^2, y-block read at
     threshold 1/4 (ties up):
     (a) exhaustive lengths 1..12 (IEEE double): read-out == reference on all 8190 rows; largest
         accepted index vs the a-priori bound from rho_0^2 <= 21 n (185 at n = 12);
     (b) at every accepted point, soundness ||z - z_min|| <= ||R_alpha(z)||/sigma-hat against
         the exact minimiser of the dossier's R9 table, and residual contraction
         rho_{k+1} <= (29/30) rho_k at every iterate: violations = 0;
     (c) the same run in EXACT rational arithmetic (Fractions) for lengths 1..8 (510 rows);
     (d) trajectory n = 256 (seed 110), 512 steps (IEEE double): per-step read-out == reference;
         largest accepted index vs the bound 231;
     (e) the exact minimiser table at unit weights: y-values in {0, 1/2, 1}; min over cell types
         of |y - 1/4| = 1/4 and of |y - 1/2| = 0;
     (f) negative controls: threshold 1/2 at unit weights on x = (0,0,1,1,1) has margin 0 (the
         tie); weights (1,2,1) put the bad-cell value at 1/3, which threshold 1/2 reads as 0,
         not the row's 1; weights (2,1,1) at threshold 1/2 have margin 1/6.
"""
from __future__ import annotations

import time
from fractions import Fraction as Fr

import numpy as np

RULE = 110
SEED = 110


# ----------------------------------------------------------------------------- reference
def reference_step(x: list[int]) -> list[int]:
    """Rule 110 by table lookup (the ground truth)."""
    n = len(x)
    table = {(1, 1, 1): 0, (1, 1, 0): 1, (1, 0, 1): 1, (1, 0, 0): 0,
             (0, 1, 1): 1, (0, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): 0}
    return [table[(x[(i - 1) % n], x[i], x[(i + 1) % n])] for i in range(n)]


# ----------------------------------------------------------------------------- the pipeline
def _affine_targets(x: np.ndarray) -> tuple[np.ndarray, np.ndarray]:
    """The two affine data maps of the declarations: (Sx)_i = x_i + x_{i+1}, (Tx)_i = x_{i-1}."""
    S = x + np.roll(x, -1)
    T = np.roll(x, 1)
    return S, T


def _stage_fb(target: np.ndarray, alpha: float, box: bool, start: np.ndarray,
              eps: float) -> tuple[np.ndarray, int]:
    """One stage: forward-backward on E(v) = 1/2||v - target||^2 (+ box), beta = sigma = 1.

    Residual at v: ||R_alpha(v)|| with R_alpha(v) = (v - prox(v - alpha grad f(v)))/alpha
    (for the pure smooth stage prox = identity, R = grad). Stops when residual <= eps;
    the certified distance is then residual/sigma <= eps."""
    v = start.astype(float).copy()
    count = 0
    while True:
        grad = v - target
        step = v - alpha * grad
        nxt = np.clip(step, 0.0, 1.0) if box else step
        residual = np.linalg.norm((v - nxt) / alpha)
        if residual <= eps:
            return v, count
        v = nxt
        count += 1


def pipeline_step(x: list[int], alpha: float, eps: float) -> tuple[list[int], tuple[int, int, int]]:
    """One automaton step as three certified stages with rounded hand-offs."""
    xv = np.array(x, float)
    S, T = _affine_targets(xv)
    # stage P: products c*r, performed by the projective primitive
    p_run, cP = _stage_fb(S - 1.0, alpha, True, np.zeros_like(xv), eps)
    p_hat = (p_run > 0.5).astype(float)          # certified read-out, margin 1/2
    # stage Q: products l*(c*r), data = x and the rounded stage-P report
    q_run, cQ = _stage_fb(T + p_hat - 1.0, alpha, True, np.zeros_like(xv), eps)
    q_hat = (q_run > 0.5).astype(float)
    # stage Y: affine assembly, dissipative only
    y_run, cY = _stage_fb(S - p_hat - q_hat, alpha, False, xv.copy(), eps)
    y_hat = (y_run > 0.5).astype(int)
    return y_hat.tolist(), (cP, cQ, cY)


# ----------------------------------------------------------------------------- battery A
def battery_exhaustive(max_n: int = 12) -> tuple[int, int]:
    total = ok = 0
    for n in range(1, max_n + 1):
        for code in range(2 ** n):
            x = [(code >> i) & 1 for i in range(n)]
            y, counts = pipeline_step(x, alpha=1.0, eps=0.49)
            total += 1
            ok += int(y == reference_step(x) and max(counts) <= 1)
    return total, ok


# ----------------------------------------------------------------------------- battery B/C
def battery_trajectory(n: int, steps: int, alpha: float, eps: float):
    rng = np.random.default_rng(SEED)
    x = rng.integers(0, 2, n).tolist()
    ref = list(x)
    max_counts = (0, 0, 0)
    for k in range(steps):
        y, counts = pipeline_step(x, alpha, eps)
        ref = reference_step(ref)
        x = y
        if x != ref:
            return False, max_counts, k
        max_counts = tuple(max(a, b) for a, b in zip(max_counts, counts))
    return True, max_counts, steps


def predicted_count(r0: float, eps: float, q: float) -> int:
    """Smallest k with r0 q^k <= eps, from the declared numbers alone."""
    import math
    if r0 <= eps:
        return 0
    return math.ceil(math.log(r0 / eps) / math.log(1.0 / q))


def battery_audit(n: int, alpha: float, eps: float):
    """Worst-case per-stage count vs the count predicted from declared numbers.

    The residual of the affine iteration contracts by exactly q = 1 - alpha per iteration
    (the projection is firmly nonexpansive and the target's prox-fixed point is interior-
    or-face-consistent; observed counts must never exceed the prediction from the worst
    start residual)."""
    rng = np.random.default_rng(SEED)
    x = rng.integers(0, 2, n).tolist()
    q = 1.0 - alpha
    worst = {"P": (0, 0), "Q": (0, 0), "Y": (0, 0)}  # (observed, predicted)
    for k in range(64):
        xv = np.array(x, float)
        S, T = _affine_targets(xv)
        # observed counts
        y, (cP, cQ, cY) = pipeline_step(x, alpha, eps)
        # predicted from declared numbers: start residual at the stage's start point
        p_hat = np.clip(S - 1.0, 0, 1)
        q_hat = np.clip(T + p_hat - 1.0, 0, 1)
        for key, start, target in (("P", np.zeros(len(x)), S - 1.0),
                                   ("Q", np.zeros(len(x)), T + p_hat - 1.0),
                                   ("Y", xv, S - p_hat - q_hat)):
            box = key != "Y"
            v = start.astype(float)
            nxt = np.clip(v - alpha * (v - target), 0, 1) if box else v - alpha * (v - target)
            r0 = float(np.linalg.norm((v - nxt) / alpha))
            pred = predicted_count(r0, eps, q)
            obs = {"P": cP, "Q": cQ, "Y": cY}[key]
            if obs > worst[key][0]:
                worst[key] = (obs, pred)
        x = y
    return worst


# ----------------------------------------------------------------------------- battery D (exact KKT)
def joint_kkt_verify(x: list[int], p: list[Fr], q: list[Fr], y: list[Fr],
                     w1: Fr = Fr(1), w2: Fr = Fr(1), w3: Fr = Fr(1)) -> tuple[bool, Fr]:
    """Exact KKT check that (p,q,y) minimises the weighted joint convex QP
    E = w1/2||p-(S-1)||^2 + w2/2||q-(T+p-1)||^2 + w3/2||y-(S-p-q)||^2 + box(p) + box(q)
    (unit weights by default). Returns (is_global_minimiser, E)."""
    n = len(x)
    S = [Fr(x[i] + x[(i + 1) % n]) for i in range(n)]
    T = [Fr(x[(i - 1) % n]) for i in range(n)]
    r1 = [p[i] - (S[i] - 1) for i in range(n)]
    r2 = [q[i] - (T[i] + p[i] - 1) for i in range(n)]
    r3 = [y[i] - (S[i] - p[i] - q[i]) for i in range(n)]
    gp = [w1 * r1[i] - w2 * r2[i] + w3 * r3[i] for i in range(n)]
    gq = [w2 * r2[i] + w3 * r3[i] for i in range(n)]
    gy = [w3 * r3[i] for i in range(n)]
    ok = True
    for i in range(n):
        for (v, g) in ((p[i], gp[i]), (q[i], gq[i])):
            if not (Fr(0) <= v <= Fr(1)):
                ok = False
            elif v == 0:
                ok = ok and g >= 0
            elif v == 1:
                ok = ok and g <= 0
            else:
                ok = ok and g == 0
        ok = ok and gy[i] == 0
    E = sum(w1 * r1[i] ** 2 + w2 * r2[i] ** 2 + w3 * r3[i] ** 2 for i in range(n)) / 2
    return ok, E


def battery_refutation():
    out = {}
    # witness (i): n = 1, x = (0)
    ok1, E1 = joint_kkt_verify([0], [Fr(0)], [Fr(0)], [Fr(0)])
    out["w1_kkt"] = ok1
    out["w1_minE"] = E1
    out["w1_y_equals_t"] = ([Fr(0)] == [Fr(v) for v in reference_step([0])])
    # witness (ii): n = 5, x = (0,0,1,1,1)
    x = [0, 0, 1, 1, 1]
    p = [Fr(0), Fr(1, 2), Fr(1), Fr(1), Fr(0)]
    q = [Fr(0), Fr(0), Fr(0), Fr(1), Fr(0)]
    y = [Fr(0), Fr(1, 2), Fr(1), Fr(0), Fr(1)]
    ok2, E2 = joint_kkt_verify(x, p, q, y)
    t = reference_step(x)
    gap = max(abs(y[i] - t[i]) for i in range(5))
    out["w2_kkt"] = ok2
    out["w2_minE"] = E2
    out["w2_inf_gap"] = gap
    # battery E: cascade point not sweep-stationary at n = 3, x = (0,1,0)
    x3 = [0, 1, 0]
    n = 3
    S = [Fr(x3[i] + x3[(i + 1) % n]) for i in range(n)]
    T = [Fr(x3[(i - 1) % n]) for i in range(n)]
    pc = [max(Fr(0), min(Fr(1), S[i] - 1)) for i in range(n)]
    qc = [max(Fr(0), min(Fr(1), T[i] + pc[i] - 1)) for i in range(n)]
    yc = [S[i] - pc[i] - qc[i] for i in range(n)]
    # block-p exact solve given (qc, yc): argmin over box of the joint E in p
    p_new = [max(Fr(0), min(Fr(1), (2 * S[i] - T[i] - yc[i]) / 3)) for i in range(n)]
    out["cascade_moves"] = (p_new != pc)
    out["cascade_p"] = pc
    out["cascade_p_resolve"] = p_new
    return out


# ----------------------------------------------------------------------------- battery F
# Construction B (dossier R8-R12): the single summed energy at unit weights, declared pair
# (beta-hat, sigma-hat) = (18/5, 3/25), forward-backward at alpha = 5/18, accept when
# ||R_alpha||^2 < (sigma-hat/4)^2, y-block read out at threshold 1/4 (ties up).
import math

ALPHA_J = 5.0 / 18.0
SIGMA_HAT = 3.0 / 25.0
GAMMA_J = 29.0 / 30.0   # 1 - sigma-hat/beta-hat


def _cell_types(x: list[int]) -> list[tuple[int, int]]:
    """Per cell i: (l, s) with l = x_{i-1}, s = x_i + x_{i+1}."""
    n = len(x)
    return [(x[(i - 1) % n], x[i] + x[(i + 1) % n]) for i in range(n)]


def joint_minimiser(x: list[int], w1=1, w2=1):
    """The exact minimiser of the summed energy, per the dossier's R9 table (Fractions).
    Returns (p, q, y) as lists of Fractions. theta = w1/(w1+w2); w3 does not enter."""
    th = Fr(w1, w1 + w2)
    table = {
        (1, 0): (Fr(0), Fr(0), Fr(0)),
        (1, 1): (Fr(0), Fr(0), Fr(1)),
        (1, 2): (Fr(1), Fr(1), Fr(0)),
        (0, 0): (max(Fr(0), 1 - 2 * th), Fr(0), -max(Fr(0), 1 - 2 * th)),
        (0, 1): (1 - th, Fr(0), th),
        (0, 2): (Fr(1), Fr(0), Fr(1)),
    }
    cells = [table[ls] for ls in _cell_types(x)]
    return ([c[0] for c in cells], [c[1] for c in cells], [c[2] for c in cells])


def _joint_grad(S, T, p, q, y):
    """Gradient of the smooth part at unit weights: om1 = p-(S-1), om2 = q-(T+p-1),
    om3 = y-(S-p-q); g_p = om1-om2+om3, g_q = om2+om3, g_y = om3. Works for arrays and lists."""
    om1 = [p[i] - (S[i] - 1) for i in range(len(p))]
    om2 = [q[i] - (T[i] + p[i] - 1) for i in range(len(p))]
    om3 = [y[i] - (S[i] - p[i] - q[i]) for i in range(len(p))]
    gp = [om1[i] - om2[i] + om3[i] for i in range(len(p))]
    gq = [om2[i] + om3[i] for i in range(len(p))]
    return gp, gq, om3


def single_energy_run(x: list[int], exact: bool):
    """Forward-backward on the summed energy from z0 = 0; returns
    (accepted z, count, rho at acceptance, contraction violations, soundness ok, readout)."""
    n = len(x)
    if exact:
        alpha, acc2, gam2 = Fr(5, 18), (Fr(3, 25) / 4) ** 2, Fr(29, 30) ** 2
        S = [Fr(x[i] + x[(i + 1) % n]) for i in range(n)]
        T = [Fr(x[(i - 1) % n]) for i in range(n)]
        p = [Fr(0)] * n; q = [Fr(0)] * n; y = [Fr(0)] * n
        clampf = lambda v: max(Fr(0), min(Fr(1), v))
    else:
        alpha, acc2, gam2 = ALPHA_J, (SIGMA_HAT / 4) ** 2, GAMMA_J ** 2 * (1 + 1e-12)
        S = [float(x[i] + x[(i + 1) % n]) for i in range(n)]
        T = [float(x[(i - 1) % n]) for i in range(n)]
        p = [0.0] * n; q = [0.0] * n; y = [0.0] * n
        clampf = lambda v: 0.0 if v < 0 else (1.0 if v > 1 else v)
    count = 0
    rho2_prev = None
    violations = 0
    while True:
        gp, gq, gy = _joint_grad(S, T, p, q, y)
        pn = [clampf(p[i] - alpha * gp[i]) for i in range(n)]
        qn = [clampf(q[i] - alpha * gq[i]) for i in range(n)]
        yn = [y[i] - alpha * gy[i] for i in range(n)]
        rho2 = sum(((p[i] - pn[i]) / alpha) ** 2 + ((q[i] - qn[i]) / alpha) ** 2
                   + ((y[i] - yn[i]) / alpha) ** 2 for i in range(n))
        if rho2_prev is not None and rho2 > gam2 * rho2_prev:
            violations += 1
        rho2_prev = rho2
        if rho2 < acc2:
            break
        p, q, y = pn, qn, yn
        count += 1
    # soundness against the exact minimiser (R9 table): ||z - z_min||^2 * sigma-hat^2 <= rho^2
    pm, qm, ym = joint_minimiser(x)
    if exact:
        d2 = sum((p[i] - pm[i]) ** 2 + (q[i] - qm[i]) ** 2 + (y[i] - ym[i]) ** 2
                 for i in range(n))
        sound = d2 * (Fr(3, 25) ** 2) <= rho2
    else:
        d2 = sum((p[i] - float(pm[i])) ** 2 + (q[i] - float(qm[i])) ** 2
                 + (y[i] - float(ym[i])) ** 2 for i in range(n))
        sound = d2 * SIGMA_HAT ** 2 <= rho2 * (1 + 1e-9)
    readout = [1 if y[i] >= (Fr(1, 4) if exact else 0.25) else 0 for i in range(n)]
    return count, violations, sound, readout


def single_energy_bound(n: int) -> int:
    """A-priori acceptance bound from the declared numbers: least k with
    gamma^k rho_0 < sigma-hat/4, rho_0^2 <= 21 n."""
    rho0 = math.sqrt(21.0 * n)
    return max(0, math.floor(math.log(4.0 * rho0 / SIGMA_HAT) / math.log(1.0 / GAMMA_J)) + 1)


def battery_single_energy():
    out = {}
    # (a)+(b) exhaustive, IEEE double; violation counters are MEASURED, then asserted zero
    worst_count = 0
    rows_double = 0
    viol_total = 0
    sound_fail = 0
    for n in range(1, 13):
        for code in range(2 ** n):
            x = [(code >> i) & 1 for i in range(n)]
            count, viol, sound, readout = single_energy_run(x, exact=False)
            viol_total += viol
            sound_fail += int(not sound)
            assert readout == reference_step(x), (n, code)
            assert count <= single_energy_bound(n), (n, code, count)
            worst_count = max(worst_count, count)
            rows_double += 1
    out["rows_double"] = rows_double
    out["exhaustive_worst_count"] = worst_count
    out["bound_n12"] = single_energy_bound(12)
    # (c) exact rational, lengths 1..8
    worst_exact = 0
    rows_exact = 0
    for n in range(1, 9):
        for code in range(2 ** n):
            x = [(code >> i) & 1 for i in range(n)]
            count, viol, sound, readout = single_energy_run(x, exact=True)
            viol_total += viol
            sound_fail += int(not sound)
            assert readout == reference_step(x), (n, code)
            worst_exact = max(worst_exact, count)
            rows_exact += 1
    out["exact_rows"] = rows_exact
    out["exact_worst_count"] = worst_exact
    # (d) trajectory, IEEE double
    rng = np.random.default_rng(SEED)
    x = rng.integers(0, 2, 256).tolist()
    ref = list(x)
    worst_traj = 0
    for _ in range(512):
        count, viol, sound, readout = single_energy_run(x, exact=False)
        ref = reference_step(ref)
        viol_total += viol
        sound_fail += int(not sound)
        assert readout == ref
        worst_traj = max(worst_traj, count)
        x = readout
    out["traj_worst_count"] = worst_traj
    out["bound_n256"] = single_energy_bound(256)
    out["contraction_violations"] = viol_total
    out["soundness_violations"] = sound_fail
    assert viol_total == 0 and sound_fail == 0
    # (e) minimiser table y-values at unit weights, one per cell type (l,s). Every type occurs
    # in the row x_e below, so the table is guarded by an exact KKT solve, not hand-typed alone:
    # cells of x_e = (0,0,1,1,1,0,1,0) realise all six (l,s) types on the ring of 8.
    x_e = [0, 0, 1, 1, 1, 0, 1, 0]
    assert set(_cell_types(x_e)) == {(1, 0), (1, 1), (1, 2), (0, 0), (0, 1), (0, 2)}
    pe, qe, ye = joint_minimiser(x_e)
    ok_e, _ = joint_kkt_verify(x_e, pe, qe, ye)
    out["table_kkt"] = ok_e
    table_y = ye
    out["table_y_values"] = sorted(set(table_y))
    out["min_margin_quarter"] = min(abs(v - Fr(1, 4)) for v in table_y)
    out["min_margin_half"] = min(abs(v - Fr(1, 2)) for v in table_y)
    # (f) negative controls; each weighted table output is guarded by an exact weighted KKT solve
    x5 = [0, 0, 1, 1, 1]
    t5 = reference_step(x5)
    p_u, q_u, y_unit = joint_minimiser(x5, 1, 1)
    ok_u, _ = joint_kkt_verify(x5, p_u, q_u, y_unit)
    out["control_unit_kkt"] = ok_u
    out["control_unit_margin_half"] = min(abs(v - Fr(1, 2)) for v in y_unit)
    p_12, q_12, y_12 = joint_minimiser(x5, 1, 2)
    ok_12, _ = joint_kkt_verify(x5, p_12, q_12, y_12, Fr(1), Fr(2), Fr(1))
    out["control_w12_kkt"] = ok_12
    bad = [i for i, (l, s) in enumerate(_cell_types(x5)) if l == 0 and s == 1][0]
    out["control_w12_badcell"] = y_12[bad]
    out["control_w12_read_vs_t"] = (1 if y_12[bad] >= Fr(1, 2) else 0, t5[bad])
    p_21, q_21, y_21 = joint_minimiser(x5, 2, 1)
    ok_21, _ = joint_kkt_verify(x5, p_21, q_21, y_21, Fr(2), Fr(1), Fr(1))
    out["control_w21_kkt"] = ok_21
    read_21 = [1 if v >= Fr(1, 2) else 0 for v in y_21]
    out["control_w21_margin_half"] = min(abs(v - Fr(1, 2)) for v in y_21)
    out["control_w21_reads_row"] = (read_21 == t5)
    return out


# ----------------------------------------------------------------------------- main
def main():
    t0 = time.time()
    lines = []

    total, ok = battery_exhaustive(12)
    assert ok == total, (ok, total)
    print(f"A. exhaustive lengths 1..12: {ok}/{total} pipeline steps exact (alpha=1, 1 it/stage)")

    agree1, mc1, s1 = battery_trajectory(256, 512, alpha=1.0, eps=0.49)
    assert agree1, s1
    print(f"B. trajectory n=256, 512 steps, alpha=1.0: agrees at every step; max its/stage {mc1}")

    agree04, mc04, s04 = battery_trajectory(256, 512, alpha=0.4, eps=0.49)
    assert agree04, s04
    print(f"B. trajectory n=256, 512 steps, alpha=0.4: agrees at every step; max its/stage {mc04}")

    worst = battery_audit(256, alpha=0.4, eps=0.49)
    for k, (obs, pred) in worst.items():
        assert obs <= pred, (k, obs, pred)
    print(f"C. certificate audit alpha=0.4 (q=0.6, eps=0.49): per-stage observed/predicted "
          + ", ".join(f"{k}: {o}/{pr}" for k, (o, pr) in worst.items()))

    ref = battery_refutation()
    assert ref["w1_kkt"] and ref["w1_minE"] == 1 and ref["w1_y_equals_t"]
    assert ref["w2_kkt"] and ref["w2_minE"] == Fr(3, 4) and ref["w2_inf_gap"] == Fr(1, 2)
    assert ref["cascade_moves"]
    print(f"D. minimiser witnesses (exact KKT): n=1 minE={ref['w1_minE']}; n=5 minE={ref['w2_minE']}, "
          f"||y*-t||_inf={ref['w2_inf_gap']} exactly")
    print(f"E. cascade point not sweep-stationary at n=3, x=(0,1,0): block p moves "
          f"{[str(v) for v in ref['cascade_p']]} -> {[str(v) for v in ref['cascade_p_resolve']]}")

    se = battery_single_energy()
    assert se["table_kkt"] and se["table_y_values"] == [Fr(0), Fr(1, 2), Fr(1)]
    assert se["min_margin_quarter"] == Fr(1, 4) and se["min_margin_half"] == Fr(0)
    assert se["control_unit_kkt"] and se["control_unit_margin_half"] == Fr(0)
    assert se["control_w12_kkt"] and se["control_w12_badcell"] == Fr(1, 3)
    assert se["control_w12_read_vs_t"] == (0, 1)
    assert se["control_w21_kkt"] and se["control_w21_margin_half"] == Fr(1, 6)
    assert se["control_w21_reads_row"]
    print(f"F. single energy (construction B): exhaustive 1..12 (IEEE double, "
          f"{se['rows_double']} rows), worst count {se['exhaustive_worst_count']} <= bound "
          f"{se['bound_n12']}; exact-rational runs {se['exact_rows']} rows (lengths 1..8, "
          f"Fractions), worst count {se['exact_worst_count']}; trajectory 512 steps n=256 "
          f"(IEEE double), worst count {se['traj_worst_count']} <= bound {se['bound_n256']}; "
          f"contraction/soundness violations {se['contraction_violations']}/"
          f"{se['soundness_violations']}; table (exact KKT) margins 1/4 at threshold 1/4, 0 at "
          f"threshold 1/2; controls (exact KKT): unit margin 0, w=(1,2,1) bad cell 1/3 reads 0 "
          f"vs row 1, w=(2,1,1) margin 1/6 reads the row")

    elapsed = time.time() - t0
    with open("summary.toml", "w") as f:
        f.write(f"""# Rule 110 pipeline battery artifact (deterministic; seed {SEED} where random)
elapsed_seconds = {elapsed:.2f}
rule = {RULE}

construction = "three certified stages per automaton step; the declared data vectors and gradient oracles are affine in the data (the declared energy is quadratic in it); products performed by the projective primitive (prox of the convex box); certified read-out (margin 1/2) between stages"
exhaustive_rows = {total}
exhaustive_result = "pipeline == reference for every row, lengths 1..12, one iteration per stage at alpha = 1 (IEEE double)"

[trajectory_alpha_1.0]
n = 256
steps = 512
agrees_with_reference = true
arithmetic = "IEEE double"
max_iters_per_stage = [{mc1[0]}, {mc1[1]}, {mc1[2]}]

[trajectory_alpha_0.4]
n = 256
steps = 512
agrees_with_reference = true
arithmetic = "IEEE double"
max_iters_per_stage = [{mc04[0]}, {mc04[1]}, {mc04[2]}]

[certificate_audit]
alpha = 0.4
rate_q = 0.6
eps = 0.49
observed_vs_predicted_P = [{worst['P'][0]}, {worst['P'][1]}]
observed_vs_predicted_Q = [{worst['Q'][0]}, {worst['Q'][1]}]
observed_vs_predicted_Y = [{worst['Y'][0]}, {worst['Y'][1]}]

[joint_energy_minimiser]
verified = "exact-arithmetic KKT (Fractions)"
witness_1 = "n = 1, x = (0): joint minimiser (0,0,0), min E = 1 > 0"
witness_2 = "n = 5, x = (0,0,1,1,1): p* = (0,1/2,1,1,0), q* = (0,0,0,1,0), y* = (0,1/2,1,0,1), min E = 3/4, max |y*_i - t_i| = 1/2 exactly: the joint minimiser is not the next row, the threshold-1/2 read-out has margin 0 there and cannot be issued, and the threshold-1/4 read-out is issued from a residual certificate (see single_energy_readout)"
cascade_not_stationary = "n = 3, x = (0,1,0): exact block-p resolve moves p from (0,0,0) to (1/3,1/3,0)"
sigma_joint = "lambda_min of [[3,0,1],[0,2,1],[1,1,1]], the smallest root of l^3 - 6 l^2 + 9 l - 1 (approx 0.120615)"

[single_energy_readout]
declaration = "one smooth term (the summed energy's quadratic), declared pair beta_hat = 18/5, sigma_hat = 3/25; prox = clamp on p and q, identity on y; forward-backward at alpha = 5/18 from z0 = 0; accepted when ||R_alpha||^2 < (sigma_hat/4)^2; y-block read at threshold 1/4, ties up"
exhaustive_rows = {se['rows_double']}
exhaustive_result = "read-out == reference for every row, lengths 1..12 (IEEE double)"
exhaustive_worst_count = {se['exhaustive_worst_count']}
bound_from_declared_n12 = {se['bound_n12']}
exact_rational_rows = {se['exact_rows']}
exact_rational_result = "read-out == reference, soundness and contraction checked exactly, lengths 1..8 (Fractions)"
exact_rational_worst_count = {se['exact_worst_count']}
soundness_violations = {se['soundness_violations']}
contraction_violations = {se['contraction_violations']}
[single_energy_readout.trajectory]
n = 256
steps = 512
agrees_with_reference = true
arithmetic = "IEEE double"
worst_count = {se['traj_worst_count']}
bound_from_declared_n256 = {se['bound_n256']}
[single_energy_readout.minimiser_table]
verified = "exact KKT on the ring of 8 realising all six cell types, x = (0,0,1,1,1,0,1,0)"
y_values = "0, 1/2, 1"
min_margin_threshold_quarter = "1/4"
min_margin_threshold_half = "0"
[single_energy_readout.negative_controls]
verified = "exact weighted KKT at each control weighting"
unit_weights_threshold_half = "x = (0,0,1,1,1): margin 0 (the tie at the bad cell)"
weights_1_2_1 = "bad-cell minimiser value 1/3; threshold 1/2 reads 0, the row has 1"
weights_2_1_1 = "threshold 1/2 margin 1/6; reads the row"
""")
    print(f"summary.toml written; elapsed {elapsed:.2f}s")


if __name__ == "__main__":
    main()

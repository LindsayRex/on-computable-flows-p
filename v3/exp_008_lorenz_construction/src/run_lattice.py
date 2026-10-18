#!/usr/bin/env python3
"""exp_008 part B: ring of N=8 Lorenz cells at r=28, diffusive coupling c in all
three coordinates. Brief section 1 (P5) and section 4; c* read from part A's
ramp.jsonl (optimised lens, global trap box, r=28).

Integrator: Strang splitting, exact exponential for the linear coupling (circulant
Laplacian, eigendecomposition) + RK4 for the local Lorenz part; stable at any c.

Emits results/lattice.jsonl and prints the headline values for summary.
"""
import json
import math
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import exp008_lib as lib

HERE = pathlib.Path(__file__).resolve().parent.parent
RES = HERE / "results"
N, R_PARAM = 8, 28.0
H = 1e-3

# ring Laplacian and its eigendecomposition
L = 2 * np.eye(N) - np.roll(np.eye(N), 1, 0) - np.roll(np.eye(N), -1, 0)
evals, Q = np.linalg.eigh(L)
LAM2 = float(np.sort(evals)[1])  # = 2 - sqrt(2) for N=8

# c* from part A artifact (never recomputed here: one source)
row28 = None
for line in (RES / "ramp.jsonl").open():
    row = json.loads(line)
    if row["region"] == "global_trap" and row["lens"] == "optimised" and abs(row["r"] - R_PARAM) < 1e-9:
        row28 = row
if row28 is None:
    sys.exit("no optimised global_trap row at r=28 in ramp.jsonl")
SUP_MU = row28["sup_vertex"]  # exact sup over the box (affine entries, convex max)
C_STAR = SUP_MU / LAM2
print(f"lambda2 = {LAM2:.6f}  sup mu_P (r=28, optimised lens, global box) = {SUP_MU:.4f}")
print(f"c* = {C_STAR:.4f}")


def coupling_half(c):
    e = Q @ np.diag(np.exp(-c * evals * H / 2)) @ Q.T
    return e


def integrate(c, seeds, t_end=200.0, t_sync_from=50.0, track_tangent=False,
              t_tan_trans=50.0):
    """States (S, N, 3) for S seeds. Returns per-seed sync error (max pair
    distance, running max over t >= t_sync_from) and, if track_tangent, the
    full-lattice lambda_1 per seed."""
    S = len(seeds)
    base = np.array([1.0, 1.0, 20.0])
    for _ in range(int(50.0 / H)):
        base = lib.rk4_step(base, R_PARAM, H)
    states = np.empty((S, N, 3))
    for i, sd in enumerate(seeds):
        rng = np.random.default_rng(sd)
        states[i] = base + rng.uniform(-1.0, 1.0, (N, 3))
    E = coupling_half(c)
    v = None
    if track_tangent:
        v = np.zeros((S, N, 3))
        v[..., 0, 0] = 1.0
        logsum = np.zeros(S)
    sync_err = np.zeros(S)
    n_steps = int(t_end / H)
    for step in range(n_steps):
        t = (step + 1) * H
        states = np.einsum("ij,sjk->sik", E, states)
        if track_tangent:
            v = np.einsum("ij,sjk->sik", E, v)
            states, v = lib.rk4_pair_step(states, v, R_PARAM, H)
            v = np.einsum("ij,sjk->sik", E, v)
        else:
            states = lib.rk4_step(states, R_PARAM, H)
        states = np.einsum("ij,sjk->sik", E, states)
        if track_tangent:
            # renormalise every step; accumulate only inside the measurement
            # window, otherwise the transient's growth leaks into the average
            # (instrument bug caught in the first run: printed 4/3 of truth).
            nrm = np.sqrt((v ** 2).sum(axis=(1, 2), keepdims=True))
            v = v / nrm
            if t > t_tan_trans:
                logsum += np.log(nrm[:, 0, 0])
        if t >= t_sync_from:
            spread = states.max(axis=1) - states.min(axis=1)  # (S, 3)
            d = np.sqrt((spread ** 2).sum(-1))  # upper proxy >= max pair dist
            sync_err = np.maximum(sync_err, d)
    out = {"sync_err": sync_err}
    if track_tangent:
        out["lambda1"] = logsum / (t_end - t_tan_trans)
    return out


rows = []
# fixed c grid, all 8 seeds (soundness at 1.1 c* is covered by the 2 c* cell;
# the brief's explicit soundness cell c = 1.1 c* is run as its own entry)
grid = [0.25, 0.5, 1.0, 1.1, 1.2, 2.0, 4.0, 8.0, 16.0]
for mult in grid:
    c = mult * C_STAR
    res = integrate(c, seeds=range(8), track_tangent=(mult == 1.2))
    row = {"c_over_cstar": mult, "c": c,
           "sync_err_per_seed": [float(x) for x in res["sync_err"]],
           "synced_all": bool((res["sync_err"] < 1e-6).all())}
    if mult == 1.2:
        row["lambda1_sync_per_seed"] = [float(x) for x in res["lambda1"]]
        row["lambda1_sync_mean"] = float(res["lambda1"].mean())
    rows.append(row)
    print(f"c/c* = {mult:<5} sync_err max over seeds = {res['sync_err'].max():.3e} "
          + (f" lambda1_sync = {row['lambda1_sync_mean']:.4f}" if mult == 1.2 else ""))

# bisection for c_sync (seed 0), tolerance 1e-2 absolute
lo_c, hi_c = 0.0, C_STAR
while hi_c - lo_c > 1e-2:
    mid = 0.5 * (lo_c + hi_c)
    err = integrate(mid, seeds=[0])["sync_err"][0]
    if err < 1e-6:
        hi_c = mid
    else:
        lo_c = mid
c_sync = hi_c
rows.append({"c_sync_seed0": c_sync, "c_star": C_STAR, "lambda2": LAM2,
             "sup_mu": SUP_MU, "ratio_cstar_over_csync": C_STAR / c_sync})
print(f"c_sync (seed 0, bisection to 1e-2) = {c_sync:.4f}  "
      f"c*/c_sync = {C_STAR / c_sync:.1f}")

lib.write_jsonl(RES / "lattice.jsonl", rows)

#!/usr/bin/env python3
"""exp_008 part A: the r ramp. Brief sections 4-7 as amended (amendments 1, 2).

Emits results/ramp.jsonl (one row per r x region x lens), results/lambda1.jsonl
(one row per frozen-sweep r), results/soundness.jsonl (one row per passing
(r, region, lens) x trajectory pair). Amended CAL-2 gate runs first and aborts
on failure.
"""
import json
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import exp008_lib as lib

HERE = pathlib.Path(__file__).resolve().parent.parent
RES = HERE / "results"
RES.mkdir(exist_ok=True)

P_CLS = np.array([1.0 / lib.SIGMA, 1.0, 1.0])
P_ID = np.array([1.0, 1.0, 1.0])
RHOS = [0.1, 0.3, 0.5]
R_FROZEN = [0.5 + 0.5 * i for i in range(61)]          # 0.5 .. 30.5
R_FINE = [round(0.05 * i, 2) for i in range(1, 26)]    # 0.05 .. 1.25

# --- Amended CAL-2 gate (amendment 1): r=0.4, classical lens, rho=0.3 box.
lo, hi = lib.ball_box([0, 0, 0], 0.3)
g, v = lib.sup_mu(lo, hi, 0.4, P_CLS, n_grid=41)
print(f"amended CAL-2: r=0.4 rho=0.3 classical: grid sup {g:.6f}, vertex sup {v:.6f}")
if g >= 0:
    print("ABORT: amended CAL-2 failed.")
    sys.exit(1)

# --- regions: name -> function r -> (lo, hi)
regions = {f"local_rho{rho}": (lambda rho: (lambda r: lib.ball_box([0, 0, 0], rho)))(rho)
           for rho in RHOS}
regions["global_trap"] = lambda r: lib.trap_box(r)
region_rs = {name: (R_FINE + R_FROZEN if name.startswith("local") else R_FROZEN)
             for name in regions}

rows = []
for name, box_of in regions.items():
    for r in region_rs[name]:
        lo, hi = box_of(r)
        row_base = {"r": r, "region": name,
                    "box_lo": [float(x) for x in lo], "box_hi": [float(x) for x in hi]}
        # identity and classical lenses
        for lens_name, p in (("identity", P_ID), ("classical", P_CLS)):
            g, v = lib.sup_mu(lo, hi, r, p, n_grid=41)
            rows.append({**row_base, "lens": lens_name, "p": list(map(float, p)),
                         "sup_grid": g, "sup_vertex": v, "s": -g, "pass": bool(g < 0)})
        # optimised diagonal lens (vertex-exact objective, grid reading reported)
        p_opt, v_opt = lib.optimise_lens(lo, hi, r, P_CLS)
        g_opt, _ = lib.sup_mu(lo, hi, r, p_opt, n_grid=41)
        rows.append({**row_base, "lens": "optimised", "p": list(map(float, p_opt)),
                     "sup_grid": g_opt, "sup_vertex": v_opt, "s": -g_opt,
                     "pass": bool(g_opt < 0)})
    print(f"region {name}: done ({len(region_rs[name])} r values)")

# refinement check (brief section 10): 81^3 at every passing row; flip -> recorded.
n_flip = 0
for row in rows:
    if row["pass"]:
        lo, hi = np.array(row["box_lo"]), np.array(row["box_hi"])
        g81, _ = lib.sup_mu(lo, hi, row["r"], row["p"], n_grid=81)
        row["sup_grid_81"] = g81
        row["refinement_flip"] = bool(g81 >= 0)
        n_flip += row["refinement_flip"]
print(f"refinement check: {n_flip} verdict flips at 81^3")

lib.write_jsonl(RES / "ramp.jsonl", rows)

# --- lambda_1 on the frozen sweep (8 seeds).
print("Benettin lambda1 over frozen sweep ...")
lam = lib.lyap1(R_FROZEN, n_seeds=8)
lam_rows = [{"r": r, "lambda1_mean": float(lam[i].mean()),
             "lambda1_min": float(lam[i].min()), "lambda1_max": float(lam[i].max())}
            for i, r in enumerate(R_FROZEN)]
lib.write_jsonl(RES / "lambda1.jsonl", lam_rows)

# --- soundness spot-check (P4): passing rows, 8 random pairs, T=20, h=1e-3.
sound_rows, viol = [], 0
T, h = 20.0, 1e-3
for row in rows:
    if not row["pass"]:
        continue
    lo, hi = np.array(row["box_lo"]), np.array(row["box_hi"])
    centre, half = (lo + hi) / 2, (hi - lo) / 2
    s = row["s"]
    d = np.sqrt(np.array(row["p"]))
    rng = np.random.default_rng(0)
    a = centre + rng.uniform(-0.5, 0.5, (8, 3)) * half
    b = centre + rng.uniform(-0.5, 0.5, (8, 3)) * half
    d0 = np.linalg.norm((a - b) * d, axis=1)
    inside = np.ones(8, dtype=bool)
    worst = np.zeros(8)
    t = 0.0
    while t < T:
        a = lib.rk4_step(a, row["r"], h)
        b = lib.rk4_step(b, row["r"], h)
        t += h
        now_in = (np.all(a >= lo, 1) & np.all(a <= hi, 1)
                  & np.all(b >= lo, 1) & np.all(b <= hi, 1))
        inside &= now_in
        dist = np.linalg.norm((a - b) * d, axis=1)
        ratio = dist / (d0 * np.exp(-s * t))
        worst = np.where(inside, np.maximum(worst, ratio), worst)
    n_viol = int((worst > 1.01).sum())
    viol += n_viol
    sound_rows.append({"r": row["r"], "region": row["region"], "lens": row["lens"],
                       "s": s, "worst_ratio_vs_bound": float(worst.max()),
                       "pairs_stayed_inside": int(inside.sum()),
                       "violations": n_viol})
lib.write_jsonl(RES / "soundness.jsonl", sound_rows)

n_pass = sum(r["pass"] for r in rows)
print(f"rows: {len(rows)}  passing: {n_pass}  soundness rows: {len(sound_rows)}  "
      f"violations: {viol}")

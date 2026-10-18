#!/usr/bin/env python3
"""exp_007 analysis — reads ../results/, checks the frozen predictions
mechanically, writes analysis/stats.json, results/summary.toml and figures.
Thresholds are those frozen in experiment/exp_method.md §1."""
import json
import math
from pathlib import Path

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt  # noqa: E402

HERE = Path(__file__).resolve().parent.parent
R = HERE / "results"
A = HERE / "analysis"
C1, C2, C3, C4 = "#2a78d6", "#eb6834", "#1baf7a", "#eda100"
INK, MUTED = "#222222", "#888888"
EPS_REL = 1e-6


def load(name):
    return [json.loads(l) for l in (R / name).read_text().splitlines() if l.strip()]


runs = load("runs.jsonl")
decls = load("declarations.jsonl")
secant = load("arm_b_secant.jsonl")
traces = np.load(R / "traces.npz")


def dec(d, s, w2, trunc=True):
    return next(r for r in decls if r["d"] == d and r["s"] == s
                and r["w2"] == w2 and r["truncated"] == trunc)


def mmm(v):
    v = list(v)
    return [min(v), float(np.median(v)), max(v)]


stats = {}
C = [r for r in runs if r["arm"] in ("C", "C_G", "C_dscale")]

# ---- P1 soundness ----
viol = []
for r in C:
    for n in ("canonical", "band"):
        kc = r["k_cert"][n]
        if kc is None or r["k_meas"] > kc or r["censored"]:
            viol.append((r["arm"], r["s"], r["w2"], r["lam"], r["seed"], n, "count"))
        b = r["dist_bound"][n]
        if b is None or r["dist"] > b + r["ref_slack"]:
            viol.append((r["arm"], r["s"], r["w2"], r["lam"], r["seed"], n, "dist"))
stats["P1"] = {"n_runs": len(C), "n_checks": 4 * len(C), "violations": viol,
               "max_dist_over_bound_band": max(r["dist"] / r["dist_bound"]["band"] for r in C),
               "max_kmeas_over_kcert_band": max(r["k_meas"] / r["k_cert"]["band"] for r in C),
               "pass": not viol}

# ---- P2 tightness: per config (seed-median) ----
table1, p2_fail = [], []
for s in (1.0, 2.0, 4.0):
    for w2 in (0.01, 0.1, 1.0, 10.0):
        dc = dec(256, s, w2)
        for lam in (0.0, 0.01):
            rs = [r for r in runs if r["arm"] == "C" and r["s"] == s and r["w2"] == w2
                  and r["lam"] == lam]
            km = mmm(r["k_meas"] for r in rs)
            kf = mmm(r["k_fista"] for r in rs)
            row = {"s": s, "w2": w2, "lam": lam, "jc": dc["jc"], "nu1": dc["nu1"],
                   "beta_hat": dc["beta_hat"], "lam_min": dc["lam_min"],
                   "kappa_true": dc["kappa_true"], "k_meas": km, "k_fista": kf,
                   "k_oracle": rs[0]["k_oracle"]}
            for n in ("canonical", "band"):
                v = dc["decl"][n]
                beta, sig = dc["beta_hat"], v["sigma_E"]
                kc = rs[0]["k_cert"][n]
                L = math.log((2 * beta / sig - 1) / EPS_REL) / math.log(1 / EPS_REL)
                pred = dc["lam_min"] / sig * L
                ratio = kc / km[1]
                ok = pred / 3 <= ratio <= 3 * pred
                row[n] = {"nu2": v["nu2"], "delta_w": v["delta_w"], "sigma_E": sig,
                          "kappa_cert": v["kappa_cert"], "k_cert": kc,
                          "ratio_cert_meas": ratio, "pred_ratio": pred,
                          "ratio_over_pred": ratio / pred, "P2_within_3x": ok,
                          "delta_le_lammin": v["delta_w"] <= dc["lam_min"] * (1 + 1e-12),
                          "total_cert_flops": kc * rs[0]["flops"]["step"]}
                if not ok:
                    p2_fail.append((s, w2, lam, n, round(ratio / pred, 3)))
            row["total_meas_flops_median"] = km[1] * rs[0]["flops"]["step"]
            table1.append(row)
stats["table1"] = table1
stats["P2"] = {"all_delta_le_lammin": all(t[n]["delta_le_lammin"] for t in table1
                                          for n in ("canonical", "band")),
               "within_3x_count": sum(t[n]["P2_within_3x"] for t in table1
                                      for n in ("canonical", "band")),
               "cells": 2 * len(table1), "fails": p2_fail,
               "ratio_over_pred_range": [min(t[n]["ratio_over_pred"] for t in table1 for n in ("canonical", "band")),
                                         max(t[n]["ratio_over_pred"] for t in table1 for n in ("canonical", "band"))]}

# ---- P3 arm B ----
B = [r for r in runs if r["arm"] == "B"]
stats["P3"] = {
    "sigma_E_all_zero": all(r["sigma_E"] == 0.0 for r in B),
    "dimK1": {str(s): dec(256, s, 0.0)["dimK1"] for s in (1.0, 2.0, 4.0)},
    "lam_min_KtK_max": max(r["lam_min_KtK"] for r in B),
    "slopes": [{"s": x["s"], "lam": x["lam"], "slope": x["slope_top_decade"],
                "bound_holds": x["bound_holds"]} for x in secant],
    "slope_range": [min(x["slope_top_decade"] for x in secant),
                    max(x["slope_top_decade"] for x in secant)],
    "k_meas": {f"s{s}_lam{l}": mmm(r["k_meas"] for r in B if r["s"] == s and r["lam"] == l)
               for s in (1.0, 2.0, 4.0) for l in (0.001, 0.01, 0.1)},
    "censored": sum(r["censored"] for r in B),
    "k_cert_S2_min": min(r["k_cert_S2"] for r in B),
}
stats["P3"]["pass"] = bool(stats["P3"]["sigma_E_all_zero"]
                           and stats["P3"]["lam_min_KtK_max"] <= 1e-12
                           and all(abs(x["slope_top_decade"] + 1) <= 0.05 and x["bound_holds"]
                                   for x in secant))

# ---- P4 arm A ----
Aa = [r for r in runs if r["arm"] == "A"]
AG = [r for r in runs if r["arm"] == "A_G"]
stats["P4"] = {
    "energy_invariance_rel_max": max(r["energy_invariance_rel"] for r in Aa),
    "k_meas_le_range_pred": all(r["k_meas"] <= r["k_pred_range"] for r in Aa),
    "per_s": {str(s): {"k_meas": mmm(r["k_meas"] for r in Aa if r["s"] == s),
                       "k_pred_range": [r["k_pred_range"] for r in Aa if r["s"] == s][0],
                       "k_fista": mmm(r["k_fista"] for r in Aa if r["s"] == s),
                       "k_cert_S2": mmm(r["k_cert_S2"] for r in Aa if r["s"] == s),
                       "rel_err_true": mmm(r["rel_err_true"] for r in Aa if r["s"] == s),
                       "lost_high_band_rel": [r["norm_PK1_xtrue_rel"] for r in Aa if r["s"] == s][0],
                       "PK1_xret_max": max(r["norm_PK1_xret"] for r in Aa if r["s"] == s)}
              for s in (1.0, 2.0, 4.0)},
    "untruncated_gaussian_A_G": {"censored": sum(r["censored"] for r in AG), "n": len(AG),
                                 "lam_min_KtK": AG[0]["lam_min_KtK"]},
}
stats["P4"]["pass"] = bool(stats["P4"]["energy_invariance_rel_max"] <= 1e-12
                           and stats["P4"]["k_meas_le_range_pred"])

# ---- P5 FISTA ----
hi = [t for t in table1 if t["kappa_true"] >= 100]
stats["P5"] = {"configs_kappa_ge_100": [(t["s"], t["w2"], t["lam"], t["kappa_true"],
                                         t["k_meas"][1], t["k_fista"][1]) for t in hi],
               "fista_wins_all_hi": all(t["k_fista"][1] < t["k_meas"][1] for t in hi),
               "fista_wins_overall": sum(t["k_fista"][1] < t["k_meas"][1] for t in table1),
               "cells": len(table1)}
stats["P5"]["pass"] = bool(hi) and stats["P5"]["fista_wins_all_hi"]

# ---- P6 cheap to check ----
c6 = []
for r in [r for r in runs if r["arm"] == "C" and r["seed"] == 0]:
    fr = r["flops"]["cert_eval"] / (r["k_meas"] * r["flops"]["step"])
    wr = r["wall_cert"] / r["wall_solve_fb"]
    c6.append({"s": r["s"], "w2": r["w2"], "lam": r["lam"], "k_meas": r["k_meas"],
               "step_flops": r["flops"]["step"], "cert_flops": r["flops"]["cert_eval"],
               "solve_flops": r["k_meas"] * r["flops"]["step"], "flop_ratio": fr,
               "wall_cert_s": r["wall_cert"], "wall_solve_s": r["wall_solve_fb"],
               "wall_ratio": wr, "wall_over_flop": wr / fr})
big = [c for c in c6 if c["k_meas"] >= 100]
stats["P6"] = {"cells": c6, "n_kmeas_ge_100": len(big),
               "flop_ratio_max_kge100": max(c["flop_ratio"] for c in big),
               "wall_over_flop_range": [min(c["wall_over_flop"] for c in c6),
                                        max(c["wall_over_flop"] for c in c6)],
               "pass_flop": all(c["flop_ratio"] <= 1e-2 for c in big),
               "pass_wall_3x": all(1 / 3 <= c["wall_over_flop"] <= 3 for c in c6)}

# ---- P7 d-scaling ----
ds = sorted([r for r in runs if r["arm"] == "C_dscale"], key=lambda r: r["d"])
kc_can = [r["k_cert"]["canonical"] for r in ds]
kc_band = [r["k_cert"]["band"] for r in ds]
km = [r["k_meas"] for r in ds]
var = lambda v: (max(v) - min(v)) / min(v)  # noqa: E731
stats["P7"] = {"d": [r["d"] for r in ds], "k_cert_canonical": kc_can, "k_cert_band": kc_band,
               "k_meas": km, "k_fista": [r["k_fista"] for r in ds],
               "jc": [r["jc"] for r in ds],
               "canonical_ratio_1024_256": kc_can[-1] / kc_can[0],
               "band_variation": var(kc_band), "meas_variation": var(km)}
stats["P7"]["pass_canonical"] = 12 <= stats["P7"]["canonical_ratio_1024_256"] <= 20
stats["P7"]["pass_band"] = stats["P7"]["band_variation"] <= 0.10
stats["P7"]["pass_meas"] = stats["P7"]["meas_variation"] <= 0.10

# ---- P8 weight dial ----
p8 = []
grid = [0.01, 0.1, 1.0, 10.0]
for s in (1.0, 2.0, 4.0):
    dc0 = dec(256, s, 0.1)
    wstar = dc0["nu1"] / dc0["decl"]["band"]["nu2"]
    kcs = [next(t for t in table1 if t["s"] == s and t["w2"] == w and t["lam"] == 0.0)["band"]["k_cert"]
           for w in grid]
    kms = [next(t for t in table1 if t["s"] == s and t["w2"] == w and t["lam"] == 0.0)["k_meas"][1]
           for w in grid]
    am = grid[int(np.argmin(kcs))]
    inside = grid[0] <= wstar <= grid[-1]
    if inside:
        lo = max(w for w in grid if w <= wstar)
        hi_ = min(w for w in grid if w >= wstar)
        ok = am in (lo, hi_)
    else:
        ok = None  # w* outside the swept grid: registered criterion not testable
    p8.append({"s": s, "w_star": wstar, "w_star_in_grid": inside, "k_cert_band": kcs,
               "k_meas": kms, "argmin_k_cert": am, "argmin_k_meas": grid[int(np.argmin(kms))],
               "pass": ok})
stats["P8"] = p8

# ---- variant G ----
G = [r for r in runs if r["arm"] == "C_G"]
dG = dec(256, 2.0, 0.1, False)
stats["variant_G"] = {"invariant_data": dG["invariant_data"], "valid_data": dG["valid_data"],
                      "lam_min": dG["lam_min"], "delta_band": dG["decl"]["band"]["delta_w"],
                      "k_cert_band": G[0]["k_cert"]["band"], "k_meas": mmm(r["k_meas"] for r in G),
                      "k_fista": mmm(r["k_fista"] for r in G)}

(A / "stats.json").write_text(json.dumps(stats, indent=1, default=float))

# ---- summary.toml (headline numbers) ----
hl = next(t for t in table1 if t["s"] == 2.0 and t["w2"] == 0.1 and t["lam"] == 0.0)
hl1 = next(t for t in table1 if t["s"] == 2.0 and t["w2"] == 0.1 and t["lam"] == 0.01)
c6h = next(c for c in c6 if c["s"] == 2.0 and c["w2"] == 0.1 and c["lam"] == 0.0)


def tv(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, str):
        return json.dumps(v)
    if isinstance(v, (list, tuple)):
        return "[" + ", ".join(tv(x) for x in v) + "]"
    if isinstance(v, float):
        return repr(float(v))
    return str(v)


S = [("meta", {"experiment": "exp_007_deconvolution", "brief": "experiment/exp_method.md",
               "brief_sha256": "893b440a298350b4ab38066e67596c01d80753400f333771ea404a75346cdea9",
               "d": 256, "eps_rel": EPS_REL, "seeds": "0-7",
               "blur": "band-limited Gaussian, exact zero above cutoff (tau=1e-2)"}),
     ("headline_s2_w0p1_smooth", {
         "jc": hl["jc"], "nu1": hl["nu1"], "beta_hat": hl["beta_hat"], "lam_min_true": hl["lam_min"],
         "sigma_cert_canonical": hl["canonical"]["sigma_E"], "sigma_cert_band": hl["band"]["sigma_E"],
         "k_cert_canonical": hl["canonical"]["k_cert"], "k_cert_band": hl["band"]["k_cert"],
         "k_oracle_true_lammin": hl["k_oracle"],
         "k_meas_fb_min_med_max": hl["k_meas"], "k_meas_fista_min_med_max": hl["k_fista"],
         "step_flops": c6h["step_flops"], "cert_eval_flops": c6h["cert_flops"],
         "certified_total_flops_band": hl["band"]["total_cert_flops"],
         "measured_total_flops_median": hl["total_meas_flops_median"],
         "cert_over_solve_flops": c6h["flop_ratio"],
         "wall_cert_s": c6h["wall_cert_s"], "wall_solve_s": c6h["wall_solve_s"]}),
     ("headline_s2_w0p1_l1", {
         "k_cert_band": hl1["band"]["k_cert"], "k_meas_fb_min_med_max": hl1["k_meas"],
         "k_meas_fista_min_med_max": hl1["k_fista"]}),
     ("gates", {"calibration_passed": json.loads((R / "calibration.json").read_text())["passed"],
                "P1_soundness_pass": stats["P1"]["pass"], "P1_checks": stats["P1"]["n_checks"],
                "P1_max_dist_over_bound_band": stats["P1"]["max_dist_over_bound_band"],
                "P1_max_kmeas_over_kcert_band": stats["P1"]["max_kmeas_over_kcert_band"],
                "P2_delta_le_lammin_all": stats["P2"]["all_delta_le_lammin"],
                "P2_within_3x": f'{stats["P2"]["within_3x_count"]}/{stats["P2"]["cells"]}',
                "P2_ratio_over_pred_range": stats["P2"]["ratio_over_pred_range"],
                "P3_armB_pass": stats["P3"]["pass"], "P3_slope_range": stats["P3"]["slope_range"],
                "P4_armA_pass": stats["P4"]["pass"],
                "P4_energy_invariance_rel_max": stats["P4"]["energy_invariance_rel_max"],
                "P5_fista_wins_when_kappa_ge_100": stats["P5"]["pass"],
                "P5_fista_wins_cells": f'{stats["P5"]["fista_wins_overall"]}/{stats["P5"]["cells"]}',
                "P6_flop_ratio_pass": stats["P6"]["pass_flop"],
                "P6_wall_within_3x_pass": stats["P6"]["pass_wall_3x"],
                "P6_wall_over_flop_range": stats["P6"]["wall_over_flop_range"],
                "P7_canonical_ratio_1024_256": stats["P7"]["canonical_ratio_1024_256"],
                "P7_pass_canonical": stats["P7"]["pass_canonical"],
                "P7_band_variation": stats["P7"]["band_variation"],
                "P7_pass_band": stats["P7"]["pass_band"],
                "P7_meas_variation": stats["P7"]["meas_variation"],
                "P7_pass_meas": stats["P7"]["pass_meas"],
                "P8_pass_by_s": [("untestable" if x["pass"] is None else x["pass"]) for x in p8]})]
lines = ["# exp_007 summary — generated by analysis/make_analysis.py from results/*.jsonl",
         "# numbers for the paper come from here or from analysis/stats.json"]
for sec, kv in S:
    lines.append(f"\n[{sec}]")
    for k, v in kv.items():
        lines.append(f"{k} = {tv(v)}")
(R / "summary.toml").write_text("\n".join(lines) + "\n")

# ---- figures ----
plt.rcParams.update({"font.size": 9, "axes.edgecolor": MUTED, "axes.labelcolor": INK,
                     "xtick.color": MUTED, "ytick.color": MUTED, "axes.spines.top": False,
                     "axes.spines.right": False})
# fig1: residual traces + certified envelopes
fig, axs = plt.subplots(1, 2, figsize=(10, 3.8), sharey=True)
for ax, lam in zip(axs, (0.0, 0.01)):
    fb = traces[f"C_s2.0_w0.1_lam{lam}_fb"]
    fi = traces[f"C_s2.0_w0.1_lam{lam}_fista"]
    r0 = fb[0]
    t = next(x for x in table1 if x["s"] == 2.0 and x["w2"] == 0.1 and x["lam"] == lam)
    beta = t["beta_hat"]
    kk = np.arange(0, 4000)
    for sig, col, lab in ((t["band"]["sigma_E"], C2, "certified envelope (band-split declaration)"),
                          (t["canonical"]["sigma_E"], C4, "certified envelope (canonical declaration)"),
                          (t["lam_min"], MUTED, "envelope at true λ_min (oracle)")):
        q = 1 - sig / beta
        ax.plot(kk, (1 + q) / (1 - q) * q ** kk, color=col, lw=1.5, ls="--", label=lab)
    ax.plot(np.arange(len(fb)), fb / r0, color=C1, lw=2, label="forward–backward (measured)")
    ax.plot(np.arange(len(fi)), fi / r0, color=C3, lw=2, label="FISTA (measured, uncertified)")
    ax.axhline(EPS_REL, color=INK, lw=0.8)
    ax.text(3950, EPS_REL * 1.6, "ε", ha="right", color=INK)
    ax.set_yscale("log"); ax.set_ylim(1e-8, 1e6); ax.set_xlim(0, 4000)
    ax.set_xlabel("iteration k")
    ax.set_title(f"s = 2, w₂ = 0.1, λ = {lam}", color=INK)
axs[0].set_ylabel("‖R_α(x_k)‖ / ‖R_α(x_0)‖")
axs[1].legend(frameon=False, fontsize=7.5, loc="center right", bbox_to_anchor=(1.0, 0.62))
fig.tight_layout(); fig.savefig(A / "fig1_traces.png", dpi=150); plt.close(fig)

# fig2: certified vs measured counts
fig, ax = plt.subplots(figsize=(5.2, 4.4))
for n, col, lab in (("band", C2, "band-split declaration"), ("canonical", C4, "canonical declaration")):
    xs = [t["k_meas"][1] for t in table1]
    ys = [t[n]["k_cert"] for t in table1]
    ax.scatter(xs, ys, s=30, color=col, edgecolor="white", lw=1, label=lab, zorder=3)
ax.scatter([t["k_meas"][1] for t in table1], [t["k_oracle"] for t in table1], s=30,
           color=MUTED, edgecolor="white", lw=1, label="count at true λ_min (oracle)", zorder=3)
lim = [10, 3e7]
ax.plot(lim, lim, color=INK, lw=0.8); ax.text(2e4, 1.1e4, "certified = measured", color=INK, fontsize=7, rotation=33)
ax.set_xscale("log"); ax.set_yscale("log"); ax.set_xlim(10, 1e5); ax.set_ylim(10, 3e7)
ax.set_xlabel("measured iterations (forward–backward, median of 8 seeds)")
ax.set_ylabel("certified iterations (computed before the run)")
ax.legend(frameon=False, fontsize=7.5, loc="upper left")
ax.set_title("Every point above the line: the certified count held", color=INK, fontsize=9)
fig.tight_layout(); fig.savefig(A / "fig2_cert_vs_meas.png", dpi=150); plt.close(fig)

# fig3: arm B secant modulus
fig, ax = plt.subplots(figsize=(5.2, 3.8))
cols = {0.001: C1, 0.01: C2, 0.1: C3}
for x in secant:
    if x["s"] != 2.0:
        continue
    t = np.array(x["t"]); sv = np.array(x["sigma_sec"])
    m = sv > 0
    ax.plot(t[m], sv[m], color=cols[x["lam"]], lw=2, marker="o", ms=4, label=f"λ = {x['lam']}")
    ax.plot(t, x["bound"], color=cols[x["lam"]], lw=1, ls="--")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel("distance t along a kernel direction of the blur")
ax.set_ylabel("largest σ consistent with E on [x−tz, x+tz]")
ax.set_title("Arm B (data + ℓ1): curvature bound → 0 like 1/t for every λ", color=INK, fontsize=9)
ax.legend(frameon=False, fontsize=8)
fig.tight_layout(); fig.savefig(A / "fig3_armB_secant.png", dpi=150); plt.close(fig)

print(json.dumps({k: stats[k].get("pass") if isinstance(stats[k], dict) else None
                  for k in ("P1", "P3", "P4", "P5")}, indent=1))
print((R / "summary.toml").read_text())

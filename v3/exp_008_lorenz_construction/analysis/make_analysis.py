#!/usr/bin/env python3
"""exp_008 figures (brief section 12), rendered from the results files only."""
import json
import pathlib

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = pathlib.Path(__file__).resolve().parent.parent
RES = HERE / "results"
OUT = HERE / "analysis"


def load(name):
    return [json.loads(l) for l in (RES / name).open()]


ramp = load("ramp.jsonl")
lam = sorted(load("lambda1.jsonl"), key=lambda r: r["r"])
latt = load("lattice.jsonl")

# Figure 1: certified rate s(r) per lens on the rho=0.3 local box (fine sweep),
# lambda1(r) on the frozen sweep, shared r axis (two panels).
fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(7, 6), sharex=False)
styles = {"identity": ("0.6", "s"), "classical": ("0.35", "o"), "optimised": ("0.0", "^")}
for lens, (col, mk) in styles.items():
    sel = sorted([r for r in ramp if r["region"] == "local_rho0.3" and r["lens"] == lens
                  and r["r"] <= 1.3], key=lambda r: r["r"])
    ax1.plot([r["r"] for r in sel], [r["s"] for r in sel], marker=mk, ms=3.5,
             color=col, lw=1, label=f"{lens} lens")
ax1.axhline(0, color="k", lw=0.6)
ax1.axvline(0.7, color="k", lw=0.6, ls=":")
ax1.set_ylim(-5.5, 1.0)
ax1.annotate("derived flip $1-\\rho=0.7$", (0.71, -5.2), fontsize=8, va="bottom")
ax1.set_xlabel("$r$")
ax1.set_ylabel("certified rate $s$ (local box $\\rho=0.3$)")
ax1.legend(fontsize=8, loc="center left")

ax2.plot([r["r"] for r in lam], [r["lambda1_mean"] for r in lam], "k.-", lw=0.8, ms=3)
ax2.fill_between([r["r"] for r in lam], [r["lambda1_min"] for r in lam],
                 [r["lambda1_max"] for r in lam], color="0.8")
ax2.axhline(0, color="k", lw=0.6)
ax2.axvline(1.0, color="k", lw=0.6, ls=":")
ax2.axvline(24.06, color="k", lw=0.6, ls="--")
ax2.set_ylim(-1.1, 1.1)
ax2.annotate("certified region\nends ($r\\leq 1-\\rho$)", (1.5, 0.75), fontsize=8)
ax2.annotate("chaos onset\n$\\approx 24.06$", (24.6, -0.9), fontsize=8)
ax2.set_xlabel("$r$")
ax2.set_ylabel("measured $\\lambda_1$ (8 seeds)")
fig.tight_layout()
fig.savefig(OUT / "fig1_ramp.pdf")
fig.savefig(OUT / "fig1_ramp.png", dpi=140)

# Figure 2: lattice sync error vs c/c*.
fig2, ax = plt.subplots(figsize=(6, 4))
grid = [r for r in latt if "c_over_cstar" in r]
x = [r["c_over_cstar"] for r in grid]
y = [max(r["sync_err_per_seed"]) for r in grid]
ax.loglog(x, y, "ko-", lw=1, ms=4)
ax.axhline(1e-6, color="k", lw=0.6, ls=":")
ax.axvline(1.0, color="k", lw=0.8, ls="--")
tail = latt[-1]
ax.axvline(tail["c_sync_seed0"] / tail["c_star"], color="0.5", lw=0.8, ls="--")
ax.annotate("$c^*$ (certified)", (1.0, ax.get_ylim()[0] * 2), fontsize=8, rotation=90,
            ha="right")
ax.annotate("$c_{sync}$ (measured)", (tail["c_sync_seed0"] / tail["c_star"],
            ax.get_ylim()[0] * 2), fontsize=8, rotation=90, ha="right", color="0.4")
lam_sync = next((r["lambda1_sync_mean"] for r in grid if "lambda1_sync_mean" in r), None)
ax.set_title(f"ring N=8, r=28: worst-seed sync error; "
             f"$\\lambda_1$ on sync manifold at $1.2c^*$ = {lam_sync:.3f}", fontsize=9)
ax.set_xlabel("$c/c^*$")
ax.set_ylabel("sync error (worst seed, running max $t\\in[50,200]$)")
fig2.tight_layout()
fig2.savefig(OUT / "fig2_lattice.pdf")
fig2.savefig(OUT / "fig2_lattice.png", dpi=140)
print("wrote fig1_ramp.{pdf,png}, fig2_lattice.{pdf,png}")

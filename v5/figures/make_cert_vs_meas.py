#!/usr/bin/env python3
"""Witness script for fig:cert-vs-meas (review triage E4 + M6, 2026-10-18).

Reads v3/exp_007_deconvolution/results/direct_count.jsonl (the registered addendum of
2026-10-18, which re-certified every run's count by the direct-contraction formula;
writing-rule 5: numbers come from run artifacts only, and this figure is a rendering of
that artifact) and draws the addendum's certified iteration count against the measured
count for every uncensored arm C run, one point per (configuration, seed, declaration).

Run from the repo root with the pinned environment:
    v3/.venv/bin/python v5/figures/make_cert_vs_meas.py
Output: v5/figures/cert_vs_meas.pdf (committed; the build does not regenerate it).
It also prints the slack statistics quoted in the accompanying empirical observation.
"""
import json
import pathlib
import statistics

import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = pathlib.Path(__file__).resolve().parents[2]
RUNS = ROOT / "v3/exp_007_deconvolution/results/direct_count.jsonl"
OUT = pathlib.Path(__file__).resolve().parent / "cert_vs_meas.pdf"

rows = [json.loads(line) for line in RUNS.open()]
arm_c = [r for r in rows if r["arm"] == "C"]  # the addendum file holds uncensored rows only
assert arm_c, "no arm C rows found"

series = {
    "band": {"marker": "o", "color": "0.15", "label": "band declaration"},
    "canonical": {"marker": "^", "color": "0.55", "label": "canonical declaration"},
}

fig, ax = plt.subplots(figsize=(4.6, 3.4))
stats = {}
for decl, style in series.items():
    xs = [r["k_meas"] for r in arm_c if r["declaration"] == decl]
    ys = [r["k_direct"] for r in arm_c if r["declaration"] == decl]
    ratios = sorted(y / x for x, y in zip(xs, ys))
    stats[decl] = (len(xs), sum(y < x for x, y in zip(xs, ys)),
                   ratios[0], statistics.median(ratios), ratios[-1])
    ax.loglog(xs, ys, linestyle="none", marker=style["marker"], markersize=3.5,
              markerfacecolor="none", markeredgecolor=style["color"],
              label=style["label"], alpha=0.8)

lo = min(r["k_meas"] for r in arm_c)
hi = max(r["k_direct"] for r in arm_c)
ax.loglog([lo, hi], [lo, hi], color="0.3", linewidth=0.8, linestyle="--",
          label="certified = measured")
ax.set_xlabel("measured iterations to $\\Vert R_\\alpha(x)\\Vert \\leq \\varepsilon$")
ax.set_ylabel("certified iteration count")
ax.legend(frameon=False, fontsize=8, loc="lower right")
ax.tick_params(labelsize=8)
fig.tight_layout()
fig.savefig(OUT)

for decl, (n, viol, rmin, rmed, rmax) in stats.items():
    print(f"{decl}: n={n} violations={viol} slack min/median/max = "
          f"{rmin:.1f} / {rmed:.1f} / {rmax:.1f}")
print(f"wrote {OUT}")

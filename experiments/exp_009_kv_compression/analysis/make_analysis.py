#!/usr/bin/env python3
"""Figures of the analysis plan (brief section 12): fig1 the refusal flip,
fig2 measured attention error vs its certificate. Also stats.json."""
import json
import pathlib
import statistics as st

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = pathlib.Path(__file__).resolve().parent
RES = HERE.parent / "results"
runs = [json.loads(l) for l in (RES / "runs.jsonl").open()]
snd = [json.loads(l) for l in (RES / "soundness.jsonl").open()]

# fig 1: certified curvature vs mu at m=16 (kappa=10, lfrac=0.1), refusal marked
flip = {}
for r in runs:
    if r["m"] == 16 and r["kappa"] == 10 and r["lfrac"] == 0.1:
        flip.setdefault(r["mu"], []).append(r.get("sigma", 0.0))
mus = sorted(flip)
sig = [st.median(flip[m]) for m in mus]
fig, ax = plt.subplots(figsize=(5.2, 3.4))
pos = [m for m in mus if m > 0]
ax.plot(pos, [st.median(flip[m]) for m in pos], "o-", color="k",
        label=r"certified $\sigma = g_d + \mu$ (here $g_d=0$)")
ax.plot(pos, pos, ":", color="0.6", label=r"derived $\sigma = \mu$")
if 0.0 in flip:
    ax.scatter([min(pos) * 0.3], [min(pos) * 0.3], marker="x", s=70, color="crimson")
    ax.annotate("$\\mu=0$: refused\n(certified curvature 0)",
                xy=(min(pos) * 0.3, min(pos) * 0.3), xytext=(min(pos) * 0.5, max(pos) * 0.3),
                fontsize=8, color="crimson")
ax.set_xscale("log"); ax.set_yscale("log")
ax.set_xlabel(r"declared ridge $\mu$"); ax.set_ylabel(r"certified curvature $\sigma$")
ax.legend(fontsize=8, loc="upper left")
fig.tight_layout()
fig.savefig(HERE / "fig1_flip.png", dpi=150)

# fig 2: measured attention-weight error vs its certificate (every point below diagonal)
x = [s["attn_slack"] for s in snd]
b = [1.0] * len(x)
fig2, ax2 = plt.subplots(figsize=(5.2, 3.4))
attn = [s for s in snd]
bounds = [s["attn_slack"] for s in attn]
ax2.hist(bounds, bins=40, color="0.4")
ax2.axvline(1.0, color="crimson", linestyle="--", label="certificate (slack = 1)")
ax2.set_xlabel("measured attention error / certified bound")
ax2.set_ylabel("checkpoints")
ax2.legend(fontsize=8)
fig2.tight_layout()
fig2.savefig(HERE / "fig2_pipeline.png", dpi=150)

stats = dict(
    soundness_rows=len(snd),
    attn_slack_max=max(bounds),
    attn_slack_median=st.median(bounds),
    dist_slack_max=max(s["dist_slack"] for s in snd),
    violations=sum(1 for s in snd if not (s["dist_ok"] and s["logit_ok"] and s["attn_ok"])),
)
(HERE / "stats.json").write_text(json.dumps(stats, indent=1))
print(stats)
print("wrote figures + stats.json")

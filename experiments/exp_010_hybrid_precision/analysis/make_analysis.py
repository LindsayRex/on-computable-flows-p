#!/usr/bin/env python3
"""exp_010 analysis: results/*.jsonl -> analysis/stats.json, results/summary.toml, two figures.
Scores the registered predictions P1-P7 of experiment/exp_method.md (frozen) mechanically."""
import hashlib
import json
import statistics
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
import numpy as np

HERE = Path(__file__).resolve().parent.parent
R, A = HERE / "results", HERE / "analysis"
U32 = 2.0 ** -24
PAL = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100"]        # categorical slots 1-4, fixed order


def rows(name):
    p = R / name
    return [json.loads(l) for l in p.read_text().splitlines() if l.strip()] if p.exists() else []


steps = rows("steps.jsonl")
mutant = rows("mutant.jsonl")
live = rows("live.jsonl")
cal = json.loads((R / "calibration.json").read_text())
live_summary = json.loads((R / "summary_live.json").read_text()) if (R / "summary_live.json").exists() else {}
manifest = json.loads((HERE / "runs" / "run_manifest.json").read_text())

stats = {"meta": {"experiment": "exp_010_hybrid_precision",
                  "brief_sha256": hashlib.sha256((HERE / "experiment" / "exp_method.md").read_bytes()).hexdigest(),
                  "git_sha": {k: v["git_sha"] for k, v in manifest.items()}},
         "calibration": cal, "table1": {}, "table2": {}, "table3": live_summary, "predictions": {}}


def key(r):
    return f"{r['arm']}/seed{r['seed']}"


def false_accept(dec, tr):
    return dec == "accept" and tr == "rose"


def false_reject(dec, tr):
    return dec in ("reject", "reject_undecided") and tr == "fell"


runs = sorted({key(r) for r in steps})
for rk in runs:
    rs = [r for r in steps if key(r) == rk]
    n = len(rs)
    br = {b: sum(r["branch"] == b for r in rs) for b in (1, 2, 3)}
    tiers3 = {t: sum(r["branch"] == 3 and r["tier_c"] == t for r in rs) for t in (1, 2)}
    kband = next((r["k"] for r in rs if r["branch"] != 1), None)
    before_ok = all(r["branch"] == 1 for r in rs if kband is None or r["k"] < kband)
    t1 = dict(steps=n, k_band=kband, branch1_before_k_band=before_ok, branch_counts=br,
              branch3_tier_counts=tiers3, rigorous_share=br[3] / n,
              ties=sum(r["truth"] == "tie" for r in rs),
              truth_tiers={t: sum(r["tier_truth"] == t for r in rs) for t in (1, 2, 3)},
              guard_violations=sum(not r["guard"] for r in rs),
              fixed_point_steps=sum(r["fixed"] for r in rs))
    for rule in ("a", "b", "c"):
        d = f"dec_{rule}"
        t1[f"false_accepts_{rule}"] = sum(false_accept(r[d], r["truth"]) for r in rs)
        t1[f"false_rejects_{rule}"] = sum(false_reject(r[d], r["truth"]) for r in rs)
        t1[f"false_accept_steps_{rule}"] = [r["k"] for r in rs if false_accept(r[d], r["truth"])]
    t1["b_not_evaluated"] = sum(r["dec_b"] == "not_evaluated" for r in rs)
    t1["c_rejects_undecided"] = sum(r["dec_c"] == "reject_undecided" for r in rs)
    t1["c_stop_fixed"] = sum(r["dec_c"] == "stop_fixed" for r in rs)
    t1["max_e_over_uE"] = max(r["e32"] / (U32 * r["E32"]) for r in rs)
    t1["wall_s"] = dict(step=sum(r["t_step"] for r in rs), rule_c=sum(r["t_c"] for r in rs), rule_b=sum(r["t_b"] for r in rs))
    stats["table1"][rk] = t1

# table 2: cost per evaluation and the three regimes
t2 = dict(t_eval32_s=cal["t_eval32_s"], t_tier1_s=cal["t_eval64_s"], t_tier2_s=cal["t_iv113_s"],
          t_b72_rerun_s=cal["t_b72_rerun_s"], t_step32_s=cal["t_step32_s"],
          tier1_over_eval32=cal["P6_tier1_over_eval32"], tier2_over_eval32=cal["P6_tier2_over_eval32"])
for rk, t in stats["table1"].items():
    n = t["steps"]
    t2[rk] = dict(floor_rule_a_s=n * cal["t_eval32_s"],
                  repaired_rule_c_s=t["wall_s"]["rule_c"],
                  ceiling_tier2_every_step_s=n * cal["t_iv113_s"])
stats["table2"] = t2

# predictions
smooth = [rk for rk in runs if rk.startswith("C-smooth")]
P = stats["predictions"]
P["P1"] = dict(pass_=all(stats["table1"][rk]["false_accepts_c"] == 0 for rk in runs),
               false_accepts_c={rk: stats["table1"][rk]["false_accepts_c"] for rk in runs})
P["P2"] = dict(pass_=any(stats["table1"][rk]["false_accepts_a"] >= 1 for rk in smooth),
               false_accepts_a={rk: stats["table1"][rk]["false_accepts_a"] for rk in runs})
P["P3"] = dict(pass_=all(stats["table1"][rk]["false_accept_steps_b"] == stats["table1"][rk]["false_accept_steps_a"] for rk in runs))
P["P4"] = dict(pass_=all(stats["table1"][rk]["k_band"] is not None and 20 <= stats["table1"][rk]["k_band"] <= 120
                         and stats["table1"][rk]["branch1_before_k_band"] for rk in smooth),
               k_band={rk: stats["table1"][rk]["k_band"] for rk in runs},
               max_e_over_uE={rk: stats["table1"][rk]["max_e_over_uE"] for rk in runs})
mut_fa = sum(false_accept(r["dec_c"], r["truth"]) for r in mutant)
P["P5"] = dict(pass_=mut_fa >= 1, mutant_false_accepts_c=mut_fa, mutant_steps=len(mutant),
               mutant_false_accept_steps=[(r["seed"], r["k"]) for r in mutant if false_accept(r["dec_c"], r["truth"])][:20])
P["P6"] = dict(pass_=cal["P6_tier1_over_eval32"] <= 5 and cal["P6_tier2_over_eval32"] <= 1e4,
               tier1_over_eval32=cal["P6_tier1_over_eval32"], tier2_over_eval32=cal["P6_tier2_over_eval32"],
               rigorous_share={rk: stats["table1"][rk]["rigorous_share"] for rk in runs})
P["P7"] = dict(pass_=all(v["branch_counts"]["2"] == 0 and v["status"] in ("fixed_point", "cap")
                         for k, v in live_summary.items() if k.startswith("C-smooth")) if live_summary else None,
               live={k: dict(status=v["status"], steps=v["steps"], branch2=v["branch_counts"]["2"], halvings=v["halvings"])
                     for k, v in live_summary.items()})
# P7 split into its two clauses (the registered form conjoins them)
P["P7"]["branch2_clause_pass"] = all(v["branch_counts"]["2"] == 0 for k, v in live_summary.items() if k.startswith("C-smooth")) if live_summary else None
P["P7"]["stopping_clause_pass"] = all(v["status"] in ("fixed_point", "cap") for k, v in live_summary.items() if k.startswith("C-smooth")) if live_summary else None
stats["all_registered_pass"] = all(P[p]["pass_"] for p in P if P[p]["pass_"] is not None)

# POST HOC (not registered in the frozen brief; added after the readings, labelled as such):
# the invariant that Proposition 2 actually certifies, checked at every classifier step against the
# rigorous truth enclosures, and the anatomy of the registered-prediction failures.
ph = {"label": "post hoc, added 2026-11-02 after the readings; not a registered prediction"}
ph["containment_failures"] = sum(not (r["lo_c"] <= r["enc_new_lo"] and r["enc_new_hi"] <= r["hi_c"]) for r in steps)
acc = [r for r in steps if r["dec_c"] == "accept"]
ph["accepts_c"] = len(acc)
ph["accepts_with_hi_not_below_B"] = sum(not (r["hi_c"] < r["B"]) for r in acc)
ph["accepts_with_true_energy_not_below_B"] = sum(not (r["enc_new_hi"] < r["B"]) for r in acc)
ph["invariant_held_every_step"] = (ph["containment_failures"] == 0 and ph["accepts_with_hi_not_below_B"] == 0
                                   and ph["accepts_with_true_energy_not_below_B"] == 0)
fa_c = [r for r in steps if r["dec_c"] == "accept" and r["truth"] == "rose"]
ph["P1_failures_c"] = dict(count=len(fa_c), all_branch3=all(r["branch"] == 3 for r in fa_c),
                           tiers={t: sum(r["tier_c"] == t for r in fa_c) for t in (0, 1, 2)},
                           max_true_rise=max((r["enc_new_lo"] - r["enc_prev_hi"] for r in fa_c), default=0.0),
                           max_true_rise_over_E=max((r["enc_new_lo"] - r["enc_prev_hi"]) / r["E32"] for r in fa_c) if fa_c else 0.0,
                           min_e32=min((r["e32"] for r in fa_c), default=0.0),
                           reading="every such accept has E(z+) < B_k (the certified statement); the rise is relative to E(z_k), "
                                   "which Proposition 2 does not compare; the registered P1 derivation over-claimed")
fa_b_only = [r for r in steps if r["dec_b"] == "accept" and r["dec_a"] != "accept" and r["truth"] == "rose"]
ph["P3_failures_b_only"] = dict(count=len(fa_b_only), per_run={rk: sum(key(r) == rk for r in fa_b_only) for rk in runs},
                                min_true_rise=min((r["enc_new_lo"] - r["enc_prev_hi"] for r in fa_b_only), default=0.0),
                                max_true_rise=max((r["enc_new_lo"] - r["enc_prev_hi"] for r in fa_b_only), default=0.0),
                                reading="rule (b) accepted an apparent rise because the enclosure of the EXACT update lay below the "
                                        "float previous energy while the STORED float32 point rose: holes 2 and 3 of the source design")
ph["false_rejects"] = {rk: dict(a=stats["table1"][rk]["false_rejects_a"], b=stats["table1"][rk]["false_rejects_b"],
                                c=stats["table1"][rk]["false_rejects_c"]) for rk in runs}
ph["true_rises_per_run"] = {rk: sum(r["truth"] == "rose" for r in steps if key(r) == rk) for rk in runs}
stats["post_hoc"] = ph
(A / "stats.json").write_text(json.dumps(stats, indent=1, default=str))

# summary.toml (numbers for the paper)
def toml_val(v):
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (int, float)):
        return repr(v)
    if isinstance(v, (list, tuple)):
        return "[" + ", ".join(toml_val(x) for x in v) + "]"
    return json.dumps(str(v))

L = ["# exp_010 summary, generated by analysis/make_analysis.py from results/*.jsonl",
     "# numbers for the paper come from here or from analysis/stats.json", "", "[meta]",
     f'experiment = "exp_010_hybrid_precision"', f'brief = "experiment/exp_method.md"',
     f'brief_sha256 = "{stats["meta"]["brief_sha256"]}"', "d = 256", 'seeds = "0-3"', f"K_classify = {manifest.get('--classify', {}).get('K_classify', 160)}", ""]
L += ["[calibration]"] + [f"{k} = {toml_val(v)}" for k, v in cal.items()] + [""]
for rk, t in stats["table1"].items():
    L += [f'[classifier."{rk}"]']
    for k in ("steps", "k_band", "rigorous_share", "ties", "guard_violations", "fixed_point_steps",
              "false_accepts_a", "false_accepts_b", "false_accepts_c", "false_rejects_a", "false_rejects_b", "false_rejects_c",
              "b_not_evaluated", "c_rejects_undecided", "c_stop_fixed", "max_e_over_uE"):
        if t[k] is not None:
            L.append(f"{k} = {toml_val(t[k])}")
    L += [f"branch1 = {t['branch_counts'][1]}", f"branch2 = {t['branch_counts'][2]}", f"branch3 = {t['branch_counts'][3]}",
          f"branch3_tier1 = {t['branch3_tier_counts'][1]}", f"branch3_tier2 = {t['branch3_tier_counts'][2]}",
          f"wall_rule_c_s = {t['wall_s']['rule_c']!r}", f"wall_rule_b_s = {t['wall_s']['rule_b']!r}", ""]
L += ["[cost]"] + [f"{k} = {toml_val(v)}" for k, v in t2.items() if not isinstance(v, dict)] + [""]
for rk, v in live_summary.items():
    L += [f'[live."{rk}"]', f"steps = {v['steps']}", f'status = "{v["status"]}"', f"halvings = {v['halvings']}",
          f"branch1 = {v['branch_counts']['1']}", f"branch2 = {v['branch_counts']['2']}", f"branch3 = {v['branch_counts']['3']}",
          f"final_alpha = {v['final_alpha']!r}", f"final_B = {v['final_B']!r}", ""]
L += ["[post_hoc]", f'label = {toml_val(ph["label"])}', f"containment_failures = {ph['containment_failures']}",
      f"accepts_c = {ph['accepts_c']}", f"accepts_with_hi_not_below_B = {ph['accepts_with_hi_not_below_B']}",
      f"accepts_with_true_energy_not_below_B = {ph['accepts_with_true_energy_not_below_B']}",
      f"invariant_held_every_step = {toml_val(ph['invariant_held_every_step'])}",
      f"P1_failures_c = {ph['P1_failures_c']['count']}", f"P1_failures_all_branch3 = {toml_val(ph['P1_failures_c']['all_branch3'])}",
      f"P1_failures_max_true_rise = {ph['P1_failures_c']['max_true_rise']!r}",
      f"P1_failures_max_true_rise_over_E = {ph['P1_failures_c']['max_true_rise_over_E']!r}",
      f"P1_failures_min_e32 = {ph['P1_failures_c']['min_e32']!r}",
      f"P3_failures_b_only = {ph['P3_failures_b_only']['count']}",
      f"P3_failures_b_only_min_true_rise = {ph['P3_failures_b_only']['min_true_rise']!r}",
      f"P3_failures_b_only_max_true_rise = {ph['P3_failures_b_only']['max_true_rise']!r}", ""]
L += ["[gates]", f"calibration_passed = {toml_val(cal['all_pass'])}"]
L += [f"{p}_pass = {toml_val(P[p]['pass_'])}" for p in P if P[p]["pass_"] is not None]
L += [f"P5_mutant_false_accepts = {mut_fa}", f"P7_branch2_clause_pass = {toml_val(P['P7']['branch2_clause_pass'])}",
      f"P7_stopping_clause_pass = {toml_val(P['P7']['stopping_clause_pass'])}",
      f"all_registered_pass = {toml_val(stats['all_registered_pass'])}", ""]
(R / "summary.toml").write_text("\n".join(L))

# figures (smooth arm, seed 0)
plt.rcParams.update({"font.size": 9, "axes.spines.top": False, "axes.spines.right": False,
                     "axes.grid": True, "grid.color": "#e6e6e3", "grid.linewidth": 0.6, "axes.edgecolor": "#9a9a95"})
rs = [r for r in steps if key(r) == "C-smooth/seed0"]
if rs:
    k = np.array([r["k"] for r in rs])
    ratio = np.array([r["e32"] / (U32 * r["E32"]) for r in rs])
    dec = np.array([r["enc_prev_lo"] - r["enc_new_hi"] for r in rs])          # certified lower bound on the true decrease
    dec_u = np.array([d / (U32 * r["E32"]) for d, r in zip(dec, rs)])
    kb = stats["table1"]["C-smooth/seed0"]["k_band"]
    fig, ax = plt.subplots(figsize=(6.4, 3.4))
    ax.plot(k, ratio, color=PAL[0], lw=2, label="a priori bound e over u E (float32)")
    pos = dec_u > 0
    ax.plot(k[pos], dec_u[pos], color=PAL[1], lw=2, label="certified true one-step decrease over u E")
    ax.set_yscale("log")
    if kb:
        ax.axvline(kb, color="#9a9a95", lw=1, ls="--")
        ax.text(kb + 1, ax.get_ylim()[1] * 0.5, f"band onset k = {kb}", color="#55554f")
    ax.set_xlabel("step k")
    ax.set_ylabel("ratio to u E (log)")
    ax.set_title("Smooth arm, seed 0: where the float32 margin stops deciding")
    ax.legend(frameon=False, loc="lower left")
    fig.tight_layout()
    fig.savefig(A / "fig1_margin_vs_decrease.png", dpi=160)
    plt.close(fig)

    fig, ax = plt.subplots(figsize=(7.0, 2.6))
    truth_v = np.array([{"fell": 1, "rose": -1, "tie": 0}[r["truth"]] for r in rs])
    for row, (lab, col) in enumerate((("rule (a) plain float", "dec_a"), ("rule (b) B72 as written", "dec_b"),
                                      ("rule (c) repaired", "dec_c"))):
        acc = np.array([r[col] == "accept" for r in rs])
        wrong = acc & (truth_v < 0)
        ax.scatter(k[acc & ~wrong], np.full((acc & ~wrong).sum(), row), s=9, color=PAL[2], marker="s")
        ax.scatter(k[~acc], np.full((~acc).sum(), row), s=9, color="#b9b9b4", marker="s")
        ax.scatter(k[wrong], np.full(wrong.sum(), row), s=22, color=PAL[1], marker="s")
    ax.set_yticks([0, 1, 2], ["rule (a) plain float", "rule (b) B72 as written", "rule (c) repaired"])
    ax.set_xlabel("step k")
    ax.set_title("Decisions, smooth arm, seed 0: accept (aqua), reject (grey), accept of a true rise (orange)", fontsize=8.5)
    ax.grid(False)
    fig.tight_layout()
    fig.savefig(A / "fig2_decisions.png", dpi=160)
    plt.close(fig)

print(json.dumps({p: P[p]["pass_"] for p in P}, indent=1))
print("all registered pass:", stats["all_registered_pass"])

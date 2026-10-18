#!/usr/bin/env python3
"""exp_007 addendum: direct-contraction certified count.

Registered BEFORE computation in experiment/addendum_direct_count_2026-10-18.md.
Reads results/runs.jsonl (never modified), writes results/direct_count.jsonl and
results/direct_count_summary.toml. Formula, scope and checks C1-C3 are the
addendum's; nothing here departs from them.
"""
import json
import math
import pathlib
import statistics

HERE = pathlib.Path(__file__).resolve().parent.parent
RUNS = HERE / "results/runs.jsonl"
OUT_ROWS = HERE / "results/direct_count.jsonl"
OUT_SUMMARY = HERE / "results/direct_count_summary.toml"


def k_direct(beta_hat, sigma, r0, eps):
    if r0 <= eps:
        return 0
    if sigma >= beta_hat:
        return 1
    return max(0, math.ceil(math.log(r0 / eps)
                            / math.log(beta_hat / (beta_hat - sigma))))


rows = [json.loads(line) for line in RUNS.open()]
out, c1_fail, c2_fail = [], 0, 0
slack = {}
for r in rows:
    if not isinstance(r.get("k_cert"), dict) or r.get("censored"):
        continue
    for decl, k_reg in r["k_cert"].items():
        sigma = r["sigma_E"][decl]
        if sigma <= 0:
            continue
        kd = k_direct(r["beta_hat"], sigma, r["r0"], r["eps"])
        c1 = r["k_meas"] <= kd
        c2 = kd <= k_reg
        c1_fail += not c1
        c2_fail += not c2
        slack.setdefault(decl, []).append(kd / r["k_meas"])
        out.append({"arm": r["arm"], "w2": r["w2"], "lam": r["lam"], "s": r["s"],
                    "seed": r["seed"], "declaration": decl, "sigma": sigma,
                    "k_meas": r["k_meas"], "k_cert_registered": k_reg,
                    "k_direct": kd, "C1_meas_le_direct": c1,
                    "C2_direct_le_registered": c2})

with OUT_ROWS.open("w") as f:
    for row in out:
        f.write(json.dumps(row) + "\n")

# C3: headline recompute from summary.toml declared numbers.
import re
summary_text = (HERE / "results/summary.toml").read_text()
block = summary_text.split("[headline_s2_w0p1_smooth]")[1].split("[")[0]
num = lambda k: float(re.search(rf"^{k} = ([-\d.e+]+)", block, re.M).group(1))
beta_hat = num("beta_hat")
head = {d: k_direct(beta_hat, num(f"sigma_cert_{d}"), 1e6, 1.0)
        for d in ("band", "canonical")}

lines = ["[totals]",
         f"rows_in_scope = {len(out)}",
         f"C1_failures = {c1_fail}",
         f"C2_failures = {c2_fail}",
         "",
         "[headline_s2_w0p1_smooth_direct]",
         f"beta_hat = {beta_hat}",
         f"k_direct_band = {head['band']}",
         f"k_direct_canonical = {head['canonical']}",
         ""]
for decl, ratios in sorted(slack.items()):
    rs = sorted(ratios)
    lines += [f"[slack_direct_over_measured.{decl}]",
              f"n = {len(rs)}",
              f"min = {rs[0]:.3f}",
              f"median = {statistics.median(rs):.3f}",
              f"max = {rs[-1]:.3f}",
              ""]
OUT_SUMMARY.write_text("\n".join(lines))

print(f"rows in scope: {len(out)}  C1 failures: {c1_fail}  C2 failures: {c2_fail}")
print(f"headline direct counts: band {head['band']}  canonical {head['canonical']}")
for decl, ratios in sorted(slack.items()):
    rs = sorted(ratios)
    print(f"{decl}: slack min/median/max = {rs[0]:.1f} / "
          f"{statistics.median(rs):.1f} / {rs[-1]:.1f}")

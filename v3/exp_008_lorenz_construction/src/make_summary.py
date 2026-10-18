#!/usr/bin/env python3
"""exp_008 summary: totals and headline numbers from the results files only."""
import json
import pathlib

HERE = pathlib.Path(__file__).resolve().parent.parent
RES = HERE / "results"


def load(name):
    return [json.loads(l) for l in (RES / name).open()]


ramp = load("ramp.jsonl")
lam = load("lambda1.jsonl")
sound = load("soundness.jsonl")
latt = load("lattice.jsonl")

lines = ["[part_a]"]
# pass counts and flip points per (region, lens)
combos = sorted({(r["region"], r["lens"]) for r in ramp})
for region, lens in combos:
    sel = sorted([r for r in ramp if r["region"] == region and r["lens"] == lens],
                 key=lambda r: r["r"])
    passing = [r["r"] for r in sel if r["pass"]]
    key = f"{region}.{lens}".replace(".", "_")
    if passing:
        lines.append(f'{key} = {{ n_pass = {len(passing)}, r_first = {min(passing)}, '
                     f'r_flip = {max(passing)} }}')
    else:
        lines.append(f'{key} = {{ n_pass = 0 }}')

n_flip = sum(1 for r in ramp if r.get("refinement_flip"))
lines += [f"refinement_flips = {n_flip}",
          f"rows_total = {len(ramp)}",
          f"passes_at_r_gt_1 = {sum(1 for r in ramp if r['pass'] and r['r'] > 1)}"]

# lambda1 zero crossing on the frozen sweep
lam_sorted = sorted(lam, key=lambda r: r["r"])
cross = next((row["r"] for row in lam_sorted if row["lambda1_mean"] > 0.01), None)
lines.append(f"lambda1_first_positive_r = {cross}")
lines.append(f"lambda1_at_28 = {next(r['lambda1_mean'] for r in lam_sorted if abs(r['r']-28)<1e-9):.4f}")

lines += ["", "[part_a_soundness]",
          f"checks = {len(sound)}",
          f"violations = {sum(r['violations'] for r in sound)}",
          f"worst_ratio_vs_bound = {max((r['worst_ratio_vs_bound'] for r in sound), default=0):.4f}"]

lines += ["", "[part_b]"]
tail = latt[-1]
lines += [f"sup_mu_r28 = {tail['sup_mu']:.4f}",
          f"lambda2 = {tail['lambda2']:.6f}",
          f"c_star = {tail['c_star']:.4f}",
          f"c_sync_seed0 = {tail['c_sync_seed0']:.4f}",
          f"ratio_cstar_over_csync = {tail['ratio_cstar_over_csync']:.1f}"]
for row in latt[:-1]:
    key = str(row["c_over_cstar"]).replace(".", "p")
    extra = ""
    if "lambda1_sync_mean" in row:
        extra = f", lambda1_sync_mean = {row['lambda1_sync_mean']:.4f}"
    lines.append(f'grid_c_{key} = {{ synced_all = {str(row["synced_all"]).lower()}, '
                 f'sync_err_max = {max(row["sync_err_per_seed"]):.3e}{extra} }}')

soundness_cells = [r for r in latt[:-1] if r["c_over_cstar"] >= 1.1]
lines.append(f"sync_failures_at_c_ge_1p1_cstar = "
             f"{sum(0 if r['synced_all'] else 1 for r in soundness_cells)}")

(RES / "summary.toml").write_text("\n".join(lines) + "\n")
print("\n".join(lines))

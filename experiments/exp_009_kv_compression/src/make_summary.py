#!/usr/bin/env python3
"""Recomputes every verdict from the jsonl rows (the script scores, not the
operator; brief section 11) and writes results/summary.toml — the only numbers
the paper may cite."""
import json
import pathlib
import statistics as st

RES = pathlib.Path(__file__).resolve().parent.parent / "results"
runs = [json.loads(l) for l in (RES / "runs.jsonl").open()]
snd = [json.loads(l) for l in (RES / "soundness.jsonl").open()]
base = [json.loads(l) for l in (RES / "baseline.jsonl").open()]

certified_all = [r for r in runs if r["verdict"] == "certified"]
refused = [r for r in runs if r["verdict"] == "refused"]
# AMENDMENT 2 + 3: rows with r0 at the instrument floor (lambda at the
# subgradient threshold, X0 already optimal; float r0 <= 1e-9 lambda) are
# their own category, never pooled into count ratios.
degenerate = [r for r in certified_all if r["r0"] <= 1e-9 * r["lam"]]
cert = [r for r in certified_all if r["r0"] > 1e-9 * r["lam"]]

count_ok = [r for r in cert if r["count_ok"]]
ratios = [r["k_meas"] / r["k_cert"] for r in cert]
rate_ok = [r for r in cert if r["worst_ratio"] <= r["rate_cert"] + 1e-12]
# AMENDMENT 3: the degenerate check is that the flow stayed at the certified
# start point (final residual also at the instrument floor), not k_cert == 0.
degen_ok = [r for r in degenerate if r["res_final"] <= 1e-9 * r["lam"]]

families = {
    "dist": ("dist_ok", "dist_slack"),
    "logit": ("logit_ok", "logit_slack"),
    "attn_vs_bound": ("attn_ok", "attn_slack"),
}
L = []
L.append("[headline]")
L.append(f"runs_certified = {len(cert)}")
L.append(f"runs_refused = {len(refused)}")
L.append(f"runs_degenerate_certified_at_start = {len(degenerate)}")
L.append(f"degenerate_r0_zero_verified = {len(degen_ok)}")
L.append(f"count_checks_held = {len(count_ok)}")
L.append(f"count_checks_total = {len(cert)}")
L.append(f"count_ratio_min = {min(ratios):.4f}")
L.append(f"count_ratio_median = {st.median(ratios):.4f}")
L.append(f"count_ratio_max = {max(ratios):.4f}")
L.append(f"rate_checks_held = {len(rate_ok)}")
L.append(f"soundness_rows = {len(snd)}")
for fam, (okk, slk) in families.items():
    oks = [s[okk] for s in snd]
    sl = [s[slk] for s in snd]
    L.append(f"{fam}_violations = {len(oks) - sum(oks)}")
    L.append(f"{fam}_worst_slack = {max(sl):.6f}")
L.append(f"attn_le_logit_violations = {sum(1 for s in snd if not s['attn_le_logit'])}")

# P3 / H3 lens materiality: identity-lens dominance vs eigenbasis, per instance
lens = [json.loads(l) for l in (RES / "lens.jsonl").open()]
eigc = [r for r in lens if r["eig_certifies"]]
idpass = [r for r in eigc if r["id_pass"]]
L.append("")
L.append("[lens_materiality]")
L.append(f"cells_total = {len(lens)}")
L.append(f"eigenbasis_certifies = {len(eigc)}")
L.append(f"identity_also_certifies = {len(idpass)}")
L.append(f"h3_rejection_rows = {sum(1 for r in idpass if r['id_sigma'] >= 0.5 * r['eig_sigma'])}")

# the refusal flip at m=16: certified curvature vs mu
L.append("")
L.append("[flip_m16]")
flip = {}
for r in runs:
    if r["m"] == 16 and r["kappa"] == 10 and r["lfrac"] == 0.1:
        flip.setdefault(r["mu"], []).append(r.get("sigma", 0.0))
for mu in sorted(flip):
    tag = str(mu).replace(".", "p").replace("-", "m")
    L.append(f'sigma_at_mu_{tag} = {st.median(flip[mu]):.6g}')

# baseline comparison per (m, kappa): median flow vs svd vs random logit error
L.append("")
L.append("[baseline_logit_median]")
groups = {}
for b in base:
    groups.setdefault((b["m"], b["kappa"]), []).append(b)
for (m, kp), g in sorted(groups.items()):
    fl = st.median([x["flow_logit"] for x in g])
    sv = st.median([x["svd_logit"] for x in g])
    rd = st.median([x["rand_logit"] for x in g])
    L.append(f"m{m}_kappa{kp} = {{ flow = {fl:.4f}, svd = {sv:.4f}, random = {rd:.4f} }}")

(RES / "summary.toml").write_text("\n".join(L) + "\n")
print("\n".join(L[:20]))
print("wrote", RES / "summary.toml")

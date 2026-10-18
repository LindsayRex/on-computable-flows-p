#!/usr/bin/env python3
"""Resume of the main sweep after a process interruption (the host editor was
closed at 2026-10-18 ~16:20 with 496/576 rows on disk). Identical computation
to run_main.py for the batches absent from results/runs.jsonl, appended in
place; seeding is deterministic per (seed, m, kappa), so every resumed row is
what the uninterrupted run would have written. Verified before resuming: no
partial batches (every present batch has all 8 seeds), both jsonl files parse
to the last line, no stray soundness rows from unfinished batches."""
import json
import pathlib
import sys
import time

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from exp009_lib import (D, attention_err, certified_count, constants, fb_batch,
                        gram_spectrum, logit_err, make_keys, make_query, svt)

RES = pathlib.Path(__file__).resolve().parent.parent / "results"
SEEDS = list(range(8))
MS = [16, 64, 128]
KAPPAS = [10, 100]
MUS = [0.0, 1e-3, 1e-2, 1e-1]
LFRACS = [0.01, 0.1, 1.0]

done = {(r["m"], r["kappa"], r["mu"], r["lfrac"])
        for r in map(json.loads, (RES / "runs.jsonl").open())}

runs_f = (RES / "runs.jsonl").open("a")
snd_f = (RES / "soundness.jsonl").open("a")
t_all = time.time()

for m in MS:
    for kappa in KAPPAS:
        if all((m, kappa, mu, lf) in done for mu in MUS for lf in LFRACS):
            continue
        Ks = np.stack([make_keys(s) for s in SEEDS])
        Qs = [make_query(s, m, kappa) for s in SEEDS]
        spect = [gram_spectrum(Q) for Q in Qs]
        for mu in MUS:
            if all((m, kappa, mu, lf) in done for lf in LFRACS):
                continue
            Hs = np.stack([G + mu * np.eye(D) for G, _, _ in spect])
            betas = np.array([constants(ev, mu)[0] for _, ev, _ in spect])
            sigmas = np.array([constants(ev, mu)[1] for _, ev, _ in spect])
            lam0 = np.array([np.linalg.norm(Ks[i] @ Hs[i], ord=2)
                             for i in range(len(SEEDS))])
            for lfrac in LFRACS:
                if (m, kappa, mu, lfrac) in done:
                    continue
                tag = dict(m=m, kappa=kappa, mu=mu, lfrac=lfrac)
                if sigmas.min() <= 0:
                    for i, s in enumerate(SEEDS):
                        runs_f.write(json.dumps(dict(
                            tag, seed=s, verdict="refused",
                            beta=betas[i], sigma=0.0,
                            note="certified curvature 0: ker(G) nonempty, no ridge")) + "\n")
                    continue
                lam = lfrac * lam0
                alpha = 1.0 / betas
                P0, _ = svt((alpha[:, None, None] * np.einsum(
                    "bnd,bde->bne", Ks, Hs)), (alpha * lam)[:, None])
                r0 = np.linalg.norm(P0.reshape(len(SEEDS), -1), axis=1) / alpha
                # AMENDMENT 3 run-time consequence: degenerate instances
                # (r0 at the instrument floor) are not iterated; their
                # thresholds are below the float64 floor and unreachable.
                deg = r0 <= 1e-9 * lam
                live = np.flatnonzero(~deg)
                eps = 1e-6 * r0
                eps_ref = 1e-10 * r0
                kcert = np.array([certified_count(r0[i], eps[i], betas[i], sigmas[i])
                                  for i in range(len(SEEDS))])
                t0 = time.time()
                g1 = np.array([ev[-1] for _, ev, _ in spect])
                for i in np.flatnonzero(deg):
                    s = SEEDS[i]
                    runs_f.write(json.dumps(dict(
                        tag, seed=s, verdict="certified",
                        beta=float(betas[i]), sigma=float(sigmas[i]),
                        cond=float(betas[i] / sigmas[i]), r0=float(r0[i]),
                        lam=float(lam[i]), k_cert=int(kcert[i]),
                        k_meas=-1, count_ok=False, k_ref=-1,
                        res_final=float(r0[i]), worst_ratio=0.0,
                        rate_cert=float(1 - sigmas[i] / betas[i]),
                        rank=0, model_logit_err=logit_err(Qs[i], np.zeros_like(Ks[i]), Ks[i]),
                        n_checkpoints=0)) + "\n")
                if len(live) == 0:
                    runs_f.flush()
                    print(f"m={m} kappa={kappa} mu={mu} lfrac={lfrac}: "
                          f"all degenerate, 0 iters", flush=True)
                    continue
                cap = int(10 * kcert[live].max())
                Xref, crossing, snaps, res_fin, worst, kend = fb_batch(
                    Ks[live], Hs[live], alpha[live], lam[live],
                    {"eps": eps[live], "ref": eps_ref[live]}, cap,
                    ratio_floor=1e-6 * r0[live])
                for j, i in enumerate(live):
                    s = SEEDS[i]
                    checks = []
                    for (kk, rr, XX) in snaps:
                        if rr[j] <= eps_ref[i]:
                            continue
                        dist = float(np.linalg.norm(XX[j] - Xref[j]))
                        bound = float((rr[j] + res_fin[j]) / sigmas[i])
                        le = logit_err(Qs[i], XX[j], Xref[j])
                        lb = float(np.sqrt(g1[i]) * bound)
                        ae = attention_err(Qs[i], XX[j], Xref[j])
                        checks.append(dict(k=int(kk), res=float(rr[j]), dist=dist,
                                           bound=bound, logit=le, logit_bound=lb,
                                           attn=ae))
                        snd_f.write(json.dumps(dict(
                            tag, seed=s, k=int(kk),
                            dist_ok=bool(dist <= bound), dist_slack=dist / bound,
                            logit_ok=bool(le <= lb), logit_slack=le / lb if lb else 0.0,
                            attn_ok=bool(ae <= lb), attn_slack=ae / lb if lb else 0.0,
                            attn_le_logit=bool(ae <= le + 1e-12))) + "\n")
                    sv = np.linalg.svd(Xref[j], compute_uv=False)
                    rank = int((sv > 1e-8 * sv[0]).sum()) if sv[0] > 0 else 0
                    model_logit = logit_err(Qs[i], Xref[j], Ks[i])
                    runs_f.write(json.dumps(dict(
                        tag, seed=s, verdict="certified",
                        beta=float(betas[i]), sigma=float(sigmas[i]),
                        cond=float(betas[i] / sigmas[i]), r0=float(r0[i]),
                        lam=float(lam[i]), k_cert=int(kcert[i]),
                        k_meas=int(crossing["eps"][j]),
                        count_ok=bool(0 < crossing["eps"][j] <= kcert[i]),
                        k_ref=int(crossing["ref"][j]), res_final=float(res_fin[j]),
                        worst_ratio=float(worst[j]),
                        rate_cert=float(1 - sigmas[i] / betas[i]),
                        rank=rank, model_logit_err=model_logit,
                        n_checkpoints=len(checks))) + "\n")
                runs_f.flush(); snd_f.flush()
                print(f"m={m} kappa={kappa} mu={mu} lfrac={lfrac}: "
                      f"kcert max {kcert.max()}, ran {kend} iters, "
                      f"{time.time()-t0:.1f}s", flush=True)
print(f"total {time.time()-t_all:.0f}s")
runs_f.close(); snd_f.close()

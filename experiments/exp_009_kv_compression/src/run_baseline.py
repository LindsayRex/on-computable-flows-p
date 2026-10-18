#!/usr/bin/env python3
"""Baselines bracket (brief section 9): truncated SVD of K at the rank the flow
achieved (classical baseline, granted the rank after the fact), and a random
rank-matched floor. Oracle ceiling is the reference iterate itself (model_logit_err
in runs.jsonl). Emits results/baseline.jsonl."""
import json
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from exp009_lib import logit_err, make_keys, make_query

RES = pathlib.Path(__file__).resolve().parent.parent / "results"
rows = [json.loads(l) for l in (RES / "runs.jsonl").open()]
out = (RES / "baseline.jsonl").open("w")
rng = np.random.default_rng(314159)

for r in rows:
    if r["verdict"] != "certified":
        continue
    K = make_keys(r["seed"])
    Q = make_query(r["seed"], r["m"], r["kappa"])
    rank = max(r["rank"], 1)
    U, s, Vt = np.linalg.svd(K, full_matrices=False)
    Ksvd = (U[:, :rank] * s[:rank]) @ Vt[:rank]
    A = rng.standard_normal((K.shape[0], rank))
    B = rng.standard_normal((K.shape[1], rank))
    Krand = A @ B.T
    Krand *= np.linalg.norm(Ksvd) / np.linalg.norm(Krand)
    out.write(json.dumps(dict(
        m=r["m"], kappa=r["kappa"], mu=r["mu"], lfrac=r["lfrac"], seed=r["seed"],
        rank=rank, flow_logit=r["model_logit_err"],
        svd_logit=logit_err(Q, Ksvd, K),
        rand_logit=logit_err(Q, Krand, K))) + "\n")
out.close()
print("wrote", RES / "baseline.jsonl")

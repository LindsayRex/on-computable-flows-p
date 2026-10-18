#!/usr/bin/env python3
"""P3 / H3 (lens materiality, brief section 4): the same Hessian G + mu I is
put to the dominance test in two lenses. In the G-eigenbasis it is diagonal
and the test returns the exact sigma = g_d + mu. In the identity lens the
test is Gershgorin row dominance on G + mu I directly and is entitled to
refuse. H3 rejection criterion (frozen): identity lens certifies a rate
within 2x of the eigenbasis lens on the instances where both certify.
Emits results/lens.jsonl, one row per (m, kappa, mu, seed)."""
import json
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from exp009_lib import D, constants, dominance_identity, gram_spectrum, make_query

RES = pathlib.Path(__file__).resolve().parent.parent / "results"
SEEDS = list(range(8))
MS = [16, 64, 128]
KAPPAS = [10, 100]
MUS = [0.0, 1e-3, 1e-2, 1e-1]

out = (RES / "lens.jsonl").open("w")
for m in MS:
    for kappa in KAPPAS:
        for s in SEEDS:
            G, evals, V = gram_spectrum(make_query(s, m, kappa))
            for mu in MUS:
                _, sigma = constants(evals, mu)
                ok, margin = dominance_identity(G + mu * np.eye(D))
                out.write(json.dumps(dict(
                    m=m, kappa=kappa, mu=mu, seed=s,
                    eig_sigma=float(sigma), eig_certifies=bool(sigma > 0),
                    id_pass=ok, id_margin=margin,
                    id_sigma=float(margin) if ok else 0.0)) + "\n")
out.close()
print("wrote", RES / "lens.jsonl")

#!/usr/bin/env python3
"""CAL-1..4 of the frozen brief. Aborts (nonzero exit) on any gate failure; a
failure is itself a result (M5)."""
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from exp009_lib import (D, attention_err, certified_count, constants,
                        dominance_identity, fb_batch, gram_spectrum, logit_err,
                        make_keys, make_query, svt)

OUT = pathlib.Path(__file__).resolve().parent.parent / "results/calibration.toml"
lines, failures = [], []


def gate(name, ok, detail):
    lines.append(f'{name} = {{ pass = {str(bool(ok)).lower()}, detail = "{detail}" }}')
    print(("PASS " if ok else "FAIL ") + name + ": " + detail)
    if not ok:
        failures.append(name)


def run_one(K, Q, mu, lam, eps_names, cap, ratio_floor=None):
    G, evals, V = gram_spectrum(Q)
    beta, sigma = constants(evals, mu)
    H = (G + mu * np.eye(D))[None]
    alpha = np.array([1.0 / beta])
    X, crossing, snaps, res, worst, k = fb_batch(
        K[None], H, alpha, np.array([lam]), eps_names, cap, ratio_floor=ratio_floor)
    return X[0], crossing, res[0], worst[0], k, beta, sigma


# CAL-1: lambda=0, mu=1e-2, m=64 -> X* = K exactly, within the certified count.
K = make_keys(0)
Q = make_query(0, 64, 10)
G, evals, V = gram_spectrum(Q)
beta, sigma = constants(evals, 1e-2)
r0 = float(np.linalg.norm(K @ (G + 1e-2 * np.eye(D))))  # residual at X0 = 0
eps = 1e-10 * np.linalg.norm(K) * sigma  # distance 1e-10||K|| via bound res/sigma
kcert = certified_count(r0, eps, beta, sigma)
X, crossing, res, worst, k, _, _ = run_one(K, Q, 1e-2, 0.0, {"stop": eps}, 3 * kcert)
derr = np.linalg.norm(X - K) / np.linalg.norm(K)
gate("CAL1", derr <= 1e-10 and 0 < crossing["stop"][0] <= kcert,
     f"rel err {derr:.2e} (<=1e-10), measured {crossing['stop'][0]} <= certified {kcert}")

# CAL-2: isotropic G = I (kappa=1, m=128): X* = SVT_{lam/(1+mu)}(K) closed form.
Q = make_query(1, 128, 1)
G, evals, V = gram_spectrum(Q)
iso = float(np.abs(evals - evals[0]).max())
mu = 1e-2
lam0 = float(np.linalg.norm(K @ (G + mu * np.eye(D)), ord=2))
lam = 0.1 * lam0
beta, sigma = constants(evals, mu)
Xstar, _ = svt(K[None], np.array([[lam / (evals[0] + mu)]]))
Xstar = Xstar[0]
r0 = float(np.linalg.norm(K @ (G + mu * np.eye(D))))
eps = 1e-12 * r0
X, crossing, res, worst, k, _, _ = run_one(K, Q, mu, lam, {"stop": eps}, 20000)
cerr = np.linalg.norm(X - Xstar) / np.linalg.norm(Xstar)
# SVT optimality: subgradient inclusion for the isotropic problem,
# (1+mu)(K - Xstar) must lie in lam * subdiff ||Xstar||_* : check via SVD parts.
U, s, Vt = np.linalg.svd(Xstar, full_matrices=False)
pos = s > 1e-12
grad_term = (evals[0] + mu) * (K - Xstar)
sub = U[:, pos].T @ grad_term @ Vt[pos].T
subres = float(np.abs(np.diag(sub) - lam).max()) / lam
gate("CAL2", iso <= 1e-12 and cerr <= 1e-8 and subres <= 1e-8,
     f"isotropy {iso:.1e}, closed-form rel err {cerr:.2e} (<=1e-8), subgrad res {subres:.2e}")

# CAL-3 (must-fail, watched): m=16, mu=0 -> refusal; wrong certificate
# sigma' = g_16 (smallest NONZERO eigenvalue) violates its distance bound on a
# K with a planted unit kernel component. lambda = 0 so the minimiser set is
# K + ker(G) rows; the bound is claimed against the specific minimiser K.
Q = make_query(2, 16, 10)
G, evals, V = gram_spectrum(Q)
kerdim = int((evals == 0).sum())
refused = evals[0] == 0.0
kernel_vec = V[:, 0]                      # eigenvalue 0 direction
Kp = make_keys(2)
Kp = Kp - np.outer((Kp @ kernel_vec), kernel_vec)  # remove, then plant norm-1
Kp = Kp + np.outer(np.ones(Kp.shape[0]) / np.sqrt(Kp.shape[0]), kernel_vec)
sigma_wrong = float(evals[evals > 0][0])
beta = float(evals[-1])
r0 = float(np.linalg.norm(Kp @ G))
eps = 1e-8 * r0
X, crossing, res, worst, k, _, _ = run_one(Kp, Q, 0.0, 0.0, {"stop": eps}, 200000)
dist = float(np.linalg.norm(X - Kp))
claimed = res / sigma_wrong
violated = dist > claimed
gate("CAL3", refused and kerdim == D - 16 and violated,
     f"refusal sigma=0 (kerdim {kerdim}), wrong-certificate bound {claimed:.2e} "
     f"< measured distance {dist:.4f}: watched violated")

# CAL-4 (AMENDMENT 1): contraction ruler on the CAL-1 run: per-step residual
# ratio never exceeds 1 - sigma/beta by more than 1e-12, read only above the
# instrument's cancellation floor 1e-6 r0.
G, evals, V = gram_spectrum(make_query(0, 64, 10))
beta, sigma = constants(evals, 1e-2)
rate = 1 - sigma / beta
r0 = float(np.linalg.norm(K @ (G + 1e-2 * np.eye(D))))
X, crossing, res, worst, k, b2, s2 = run_one(K, make_query(0, 64, 10), 1e-2, 0.0,
                                             {"stop": 1e-10}, 50000,
                                             ratio_floor=np.array([1e-6 * r0]))
gate("CAL4", worst <= rate + 1e-12,
     f"worst measured ratio above the floor {worst:.12f} <= certified rate {rate:.12f} + 1e-12")

OUT.parent.mkdir(exist_ok=True)
OUT.write_text("[gates]\n" + "\n".join(lines) + "\n")
print("wrote", OUT)
if failures:
    sys.exit("CALIBRATION FAILED: " + ", ".join(failures))

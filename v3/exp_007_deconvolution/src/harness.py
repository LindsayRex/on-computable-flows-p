#!/usr/bin/env python3
"""exp_007 harness — deconvolution: certified vs measured iteration count.

Brief (frozen before the run): ../experiment/exp_method.md.
  --calibrate  -> results/calibration.json   (gates CAL-1..CAL-5)
  --run        -> results/declarations.jsonl, runs.jsonl, arm_b_secant.jsonl,
                  traces.npz
Every certified number is computed from per-term declarations BEFORE the
iteration it certifies is run (declarations.jsonl is written first).
"""
import os

for _v in ("OMP_NUM_THREADS", "OPENBLAS_NUM_THREADS", "MKL_NUM_THREADS",
           "NUMEXPR_NUM_THREADS"):
    os.environ.setdefault(_v, "4")

import argparse  # noqa: E402
import json  # noqa: E402
import math  # noqa: E402
import sys  # noqa: E402
import time  # noqa: E402
from pathlib import Path  # noqa: E402

import numpy as np  # noqa: E402
import pywt  # noqa: E402

HERE = Path(__file__).resolve().parent.parent
RESULTS = HERE / "results"

# ---------------- frozen parameters (brief §5, §6) ----------------
D_MAIN = 256
TAU = 1e-2
S_GRID = [1.0, 2.0, 4.0]
W2_GRID = [0.01, 0.1, 1.0, 10.0]
LAM_B = [0.001, 0.01, 0.1]
LAM_C = 0.01
D_SCALE = [256, 512, 1024]
SEEDS = list(range(8))
EPS_REL = 1e-6
CAP = 300_000
REF_TOL = 1e-12
REF_CAP = 3_000_000
WAVELET = "db4"


# ---------------- problem construction ----------------
def omega(d):
    m = np.minimum(np.arange(d), d - np.arange(d))
    return 2 * np.pi * m / d, m


def blur_multiplier(d, s, truncated=True):
    """Full-length (d) real even multiplier k_hat_j and cutoff index j_c."""
    w, m = omega(d)
    full = np.exp(-0.5 * s * s * w * w)
    kept = np.exp(-s * s * w * w) >= TAU
    jc = int(m[kept].max())
    khat = np.where(kept, full, 0.0) if truncated else full
    return khat, jc, kept


def diff_multiplier(d):
    return 4.0 * np.sin(np.pi * np.arange(d) / d) ** 2


def x_true(d):
    t = np.arange(d) / d
    x = 0.3 * np.sin(2 * np.pi * 3 * t)
    x += np.where((t >= 0.10) & (t < 0.30), 1.0, 0.0)
    x += np.where((t >= 0.45) & (t < 0.50), -0.5, 0.0)
    x += np.where((t >= 0.60) & (t < 0.85), 0.8, 0.0)
    return x


def circ_apply(mult, x):
    """Apply the real even circulant with full-length multiplier mult."""
    d = len(x)
    return np.fft.irfft(mult[: d // 2 + 1] * np.fft.rfft(x), n=d)


def wavelet_matrix(d):
    lev = pywt.dwt_max_level(d, pywt.Wavelet(WAVELET).dec_len)
    cols = []
    for i in range(d):
        e = np.zeros(d)
        e[i] = 1.0
        c = pywt.wavedec(e, WAVELET, mode="periodization", level=lev)
        cols.append(np.concatenate(c))
    return np.array(cols).T, lev  # W[:, i] = coefficients of e_i


def make_data(d, s, seed, truncated=True):
    khat, jc, kept = blur_multiplier(d, s, truncated)
    xt = x_true(d)
    kx = circ_apply(khat, xt)
    sig = 0.01 * np.linalg.norm(kx) / math.sqrt(d)
    y = kx + np.random.default_rng(seed).normal(0.0, sig, d)
    return khat, jc, kept, xt, y


# ---------------- declarations and the Gram certificate ----------------
def fourier_basis(d, ms):
    """Orthonormal real basis of span of Fourier modes with |freq| in ms."""
    i = np.arange(d)
    cols = []
    for m in sorted(set(int(v) for v in ms)):
        if m == 0:
            cols.append(np.ones(d) / math.sqrt(d))
        elif 2 * m == d:
            cols.append((-1.0) ** i / math.sqrt(d))
        else:
            cols.append(math.sqrt(2.0 / d) * np.cos(2 * np.pi * m * i / d))
            cols.append(math.sqrt(2.0 / d) * np.sin(2 * np.pi * m * i / d))
    return np.array(cols).T if cols else np.zeros((d, 0))


def gram_delta(bases, a):
    """Transversality defect Delta_w = sum a_i - lmax(A^1/2 G A^1/2)."""
    B = np.concatenate(bases, axis=1)
    if B.shape[1] == 0:
        return float(sum(a))
    sq = np.concatenate([np.full(b.shape[1], math.sqrt(ai))
                         for b, ai in zip(bases, a)])
    M = (B * sq).T @ (B * sq)
    return float(sum(a) - np.linalg.eigvalsh(M)[-1])


def valid_fourier(mult, kernel_modes_mask, nu, tol=1e-12):
    """(K, nu) valid for 1/2 x^T H x, H Fourier-diagonal, K a union of modes:
    H - nu P_{K^perp} >= 0  iff  mult_j - nu*[j not in K] >= -tol."""
    return bool(np.min(mult - nu * (~kernel_modes_mask)) >= -tol)


def declarations(d, s, w2, truncated=True):
    """Per-term declarations and every certified number, from declared data."""
    khat, jc, kept = blur_multiplier(d, s, truncated)
    _, m = omega(d)
    dhat = diff_multiplier(d)
    k1_mask = ~kept                       # K1 = high band (= ker K if truncated)
    nu1 = float(np.min(khat[kept] ** 2))
    beta1 = float(np.max(khat ** 2))
    B1 = fourier_basis(d, np.unique(m[k1_mask]))
    out = {"d": d, "s": s, "w2": w2, "truncated": truncated, "jc": jc,
           "dimK1": int(B1.shape[1]), "nu1": nu1, "beta1": beta1,
           "valid_data": valid_fourier(khat ** 2, k1_mask, nu1),
           "invariant_data": bool(np.all(khat[k1_mask] == 0.0))}
    if w2 == 0:
        out["beta_hat"] = beta1
        out["sigma_E"] = {"data_only": max(0.0, gram_delta([B1], [nu1]))}
        return out
    beta_hat = beta1 + 4.0 * w2
    lam_min = float(np.min(khat ** 2 + w2 * dhat))
    out.update(beta_hat=beta_hat, lam_min=lam_min, kappa_true=beta_hat / lam_min)
    decl = {}
    # canonical: K2 = constants, nu2 = 4 sin^2(pi/d)
    nu2c = float(dhat[1])
    k2c = (m == 0)
    # band-split: K2 = low band |j| <= jc, nu2' = 4 sin^2(pi (jc+1)/d)
    nu2b = float(4.0 * math.sin(math.pi * (jc + 1) / d) ** 2)
    k2b = (m <= jc)
    for name, nu2, k2 in (("canonical", nu2c, k2c), ("band", nu2b, k2b)):
        B2 = fourier_basis(d, np.unique(m[k2]))
        a = [1.0 * nu1, w2 * nu2]
        delta = gram_delta([B1, B2], a)
        sigma = max(0.0, delta)          # sigma_hat_S = 0 (both sigma_i = 0)
        decl[name] = {
            "nu2": nu2, "dimK2": int(B2.shape[1]),
            "valid_D": valid_fourier(dhat, k2, nu2),
            "valid_D_inflated_fails": not valid_fourier(dhat, k2, 1.01 * nu2),
            "delta_w": delta, "closed_form_min": min(a), "sigma_E": sigma,
            "kappa_cert": beta_hat / sigma if sigma > 0 else math.inf,
        }
    out["decl"] = decl
    return out


def k_cert_A(beta, sigma, r0, eps):
    """(S5)(A) certified count (thm:soundness, cor:fb-stop(c))."""
    if r0 <= eps:
        return 0
    if sigma >= beta:
        return 1
    return max(0, math.ceil(math.log((2 * beta / sigma - 1) * r0 / eps)
                            / math.log(beta / (beta - sigma))))


def k_cert_S2(beta, E0, Elow, eps):
    """(S2) count with declared E_low, x0 in dom g (k0 = 0)."""
    return math.floor(2 * beta * (E0 - Elow) / eps ** 2)


# ---------------- the energy and the iterations ----------------
class Problem:
    def __init__(self, khat, dhat, y, w2, lam, W=None):
        self.d = len(y)
        self.h = khat ** 2 + w2 * dhat          # smooth Hessian multiplier
        self.b = circ_apply(khat, y)            # K^T y
        self.khat, self.dhat, self.y, self.w2, self.lam, self.W = (
            khat, dhat, y, w2, lam, W)

    def grad(self, x):
        return circ_apply(self.h, x) - self.b

    def prox(self, v, alpha):
        if self.lam == 0:
            return v
        c = self.W @ v
        c = np.sign(c) * np.maximum(np.abs(c) - alpha * self.lam, 0.0)
        return self.W.T @ c

    def energy(self, x):
        r = circ_apply(self.khat, x) - self.y
        dx = x - np.roll(x, 1)
        e = 0.5 * r @ r + self.w2 * 0.5 * dx @ dx
        if self.lam:
            e += self.lam * np.abs(self.W @ x).sum()
        return float(e)

    def T(self, x, alpha):
        return self.prox(x - alpha * self.grad(x), alpha)

    def residual(self, x, alpha):
        return (x - self.T(x, alpha)) / alpha


def run_fb(P, alpha, eps, cap, trace=False):
    x = np.zeros(P.d)
    tr = []
    for k in range(cap + 1):
        xn = P.T(x, alpha)
        r = float(np.linalg.norm(x - xn) / alpha)
        if trace:
            tr.append(r)
        if r <= eps:
            return x, k, False, tr
        x = xn
    return x, cap, True, tr


def run_fista(P, alpha, eps, cap, trace=False):
    x = np.zeros(P.d)
    tr = []
    r = float(np.linalg.norm(P.residual(x, alpha)))
    if trace:
        tr.append(r)
    if r <= eps:
        return x, 0, False, tr
    yk, t, xprev = x.copy(), 1.0, x.copy()
    for k in range(1, cap + 1):
        xk = P.T(yk, alpha)
        tn = 0.5 * (1 + math.sqrt(1 + 4 * t * t))
        yk = xk + ((t - 1) / tn) * (xk - xprev)
        xprev, t = xk, tn
        r = float(np.linalg.norm(P.residual(xk, alpha)))  # monitor, not charged
        if trace:
            tr.append(r)
        if r <= eps:
            return xk, k, False, tr
    return xprev, cap, True, tr


# ---------------- declared flop model (brief §6) ----------------
def flops(d, n_smooth, lam):
    fft = 2.5 * d * math.log2(d)
    g_data = 2 * fft + (d + 2) + d
    g_D = 2 * fft + (d + 2)
    grads = g_data + (g_D if n_smooth == 2 else 0)
    upd = (2 * n_smooth + 1) * d
    prox = 0 if lam == 0 else 2 * (2 * d * d - d) + 4 * d + 2 * d + 1
    step = grads + upd + prox
    return {"step": step, "cert_eval": step + 2 * d, "fista_step": step + 4 * d}


def time_it(fn, reps):
    ts = []
    for _ in range(reps):
        t0 = time.perf_counter()
        fn()
        ts.append(time.perf_counter() - t0)
    return float(np.median(ts))


# ---------------- calibration ----------------
def calibrate():
    RESULTS.mkdir(exist_ok=True)
    g = {}
    rng = np.random.default_rng(42)
    # CAL-1 flat spectrum, random non-orthogonal kernels, d=64
    d = 64
    Q1, _ = np.linalg.qr(rng.standard_normal((d, 10)))
    Q2, _ = np.linalg.qr(rng.standard_normal((d, 10)))
    nu, w = [0.7, 1.9], [1.0, 0.4]
    H = sum(wi * ni * (np.eye(d) - Q @ Q.T) for wi, ni, Q in zip(w, nu, (Q1, Q2)))
    dl = gram_delta([Q1, Q2], [w[0] * nu[0], w[1] * nu[1]])
    lm = float(np.linalg.eigvalsh(H)[0])
    four = declarations(256, 2.0, 0.1)
    errs = [abs(v["delta_w"] - v["closed_form_min"]) for v in four["decl"].values()]
    g["CAL-1_flat_spectrum_exact"] = {"delta_w": dl, "lam_min": lm,
                                      "fourier_gram_vs_min_maxerr": max(errs),
                                      "pass": abs(dl - lm) <= 1e-10 and max(errs) <= 1e-12}
    # CAL-2 must fail: kernel overlap (data term also kills DC)
    khat, jc, kept = blur_multiplier(256, 2.0)
    _, m = omega(256)
    k1 = (~kept) | (m == 0)
    B1 = fourier_basis(256, np.unique(m[k1]))
    B2 = fourier_basis(256, [0])
    nu1 = float(np.min(khat[kept & (m != 0)] ** 2))
    dov = gram_delta([B1, B2], [nu1, 0.1 * float(diff_multiplier(256)[1])])
    g["CAL-2_overlap_refused"] = {"delta_w": dov, "pass": dov <= 1e-12}
    # CAL-3 validity checker (true pass, inflated fail) on every main config
    ok = True
    for s in S_GRID:
        for w2 in W2_GRID:
            dc = declarations(D_MAIN, s, w2)
            kh, _, kp = blur_multiplier(D_MAIN, s)
            ok &= dc["valid_data"] and not valid_fourier(kh ** 2, ~kp, 1.01 * dc["nu1"])
            for v in dc["decl"].values():
                ok &= v["valid_D"] and v["valid_D_inflated_fails"]
    g["CAL-3_validity_checker"] = {"pass": bool(ok)}
    # CAL-4 count/distance on closed-form diagonal quadratic; must-fail H_Delta
    spec = np.geomspace(1e-2, 1.0, 64)
    bvec = rng.standard_normal(64)
    xs = bvec / spec
    beta, sig = 1.0, 1e-2
    x = np.zeros(64)
    r0 = float(np.linalg.norm(spec * x - bvec))
    eps = 1e-6 * r0
    kc = k_cert_A(beta, sig, r0, eps)
    k = 0
    while np.linalg.norm(spec * x - bvec) > eps:
        x = x - (spec * x - bvec) / beta
        k += 1
    dist_ok = np.linalg.norm(x - xs) <= eps / sig
    xw = rng.standard_normal(8)
    viol = np.linalg.norm(xw) > np.linalg.norm(xw) / 1.5   # R(x)=x for f=1/2|x|^2
    g["CAL-4_count_distance_and_HDelta"] = {
        "k_meas": k, "k_cert": kc, "dist_ok": bool(dist_ok),
        "HDelta_witness_violates": bool(viol),
        "pass": bool(k <= kc and dist_ok and viol)}
    # CAL-5 operators
    W, lev = wavelet_matrix(256)
    orth = float(np.max(np.abs(W.T @ W - np.eye(256))))
    C = np.array([circ_apply(khat, e) for e in np.eye(256)]).T
    xr = rng.standard_normal(256)
    gerr = float(np.linalg.norm(C.T @ (C @ xr) - circ_apply(khat ** 2, xr))
                 / np.linalg.norm(C.T @ (C @ xr)))
    Dm = np.eye(256) - np.roll(np.eye(256), 1, axis=0)
    derr = float(np.linalg.norm(Dm.T @ Dm @ xr - circ_apply(diff_multiplier(256), xr))
                 / np.linalg.norm(Dm.T @ Dm @ xr))
    g["CAL-5_operators"] = {"wavelet_level": lev, "orth_maxerr": orth,
                            "grad_relerr_K": gerr, "grad_relerr_D": derr,
                            "pass": orth <= 1e-12 and gerr <= 1e-12 and derr <= 1e-12}
    for v in g.values():
        v["pass"] = bool(v["pass"])
    rep = {"gates": g, "passed": all(v["pass"] for v in g.values())}
    (RESULTS / "calibration.json").write_text(json.dumps(rep, indent=2))
    print(json.dumps({k: v["pass"] for k, v in g.items()}, indent=2))
    print("CALIBRATION", "PASSED" if rep["passed"] else "FAILED")
    return rep["passed"]


# ---------------- main run ----------------
def main_run():
    cal = json.loads((RESULTS / "calibration.json").read_text())
    if not cal.get("passed"):
        print("REFUSING TO RUN: calibration not passed", file=sys.stderr)
        return False
    Wcache = {}

    def W_of(d):
        if d not in Wcache:
            Wcache[d] = wavelet_matrix(d)[0]
        return Wcache[d]

    # 1. declarations first (certified numbers before any iteration)
    decls = []
    for s in S_GRID:
        decls.append(declarations(D_MAIN, s, 0.0))
        for w2 in W2_GRID:
            decls.append(declarations(D_MAIN, s, w2))
    decls.append(declarations(D_MAIN, 2.0, 0.0, truncated=False))
    decls.append(declarations(D_MAIN, 2.0, 0.1, truncated=False))
    for d in D_SCALE:
        if d != D_MAIN:
            decls.append(declarations(d, 2.0, 0.1))
    with open(RESULTS / "declarations.jsonl", "w") as f:
        for r in decls:
            f.write(json.dumps(r) + "\n")

    def dec(d, s, w2, trunc=True):
        return next(r for r in decls if r["d"] == d and r["s"] == s
                    and r["w2"] == w2 and r["truncated"] == trunc)

    rows, secant, traces = [], [], {}
    t_start = time.time()

    def one(arm, d, s, w2, lam, seed, trunc=True, fista=False, trace=False):
        khat, jc, kept, xt, y = make_data(d, s, seed, trunc)
        P = Problem(khat, diff_multiplier(d), y, w2, lam, W_of(d) if lam else None)
        dc = dec(d, s, w2, trunc)
        beta = dc["beta_hat"]
        alpha = 1.0 / beta
        x0 = np.zeros(d)
        r0 = float(np.linalg.norm(P.residual(x0, alpha)))
        eps = EPS_REL * r0
        E0 = P.energy(x0)
        nS = 2 if w2 > 0 else 1
        fl = flops(d, nS, lam)
        row = {"arm": arm, "d": d, "s": s, "w2": w2, "lam": lam, "seed": seed,
               "truncated": trunc, "jc": jc, "beta_hat": beta, "r0": r0,
               "eps": eps, "E0": E0, "flops": fl}
        # certified counts: computed before the run
        if w2 > 0:
            row["k_cert"] = {n: (k_cert_A(beta, v["sigma_E"], r0, eps)
                                 if v["sigma_E"] > 0 else None)
                             for n, v in dc["decl"].items()}
            row["sigma_E"] = {n: v["sigma_E"] for n, v in dc["decl"].items()}
            row["k_oracle"] = k_cert_A(beta, dc["lam_min"], r0, eps)
            row["lam_min"] = dc["lam_min"]
        else:
            row["sigma_E"] = dc["sigma_E"]["data_only"]
            row["k_cert_S2"] = k_cert_S2(beta, E0, 0.0, eps)
            row["k_pred_range"] = k_cert_A(beta, dc["nu1"], r0, eps)
        t0 = time.perf_counter()
        x, k, cens, tr = run_fb(P, alpha, eps, CAP, trace)
        row["wall_solve_fb"] = time.perf_counter() - t0
        row.update(k_meas=k, censored=cens)
        row["E_ret"] = P.energy(x)
        row["rel_err_true"] = float(np.linalg.norm(x - xt) / np.linalg.norm(xt))
        if trace:
            traces[f"{arm}_s{s}_w{w2}_lam{lam}_fb"] = np.array(tr)
        # reference x*
        if w2 > 0:
            if lam == 0:
                xh = np.fft.rfft(P.b) / P.h[: d // 2 + 1]
                xstar = np.fft.irfft(xh, n=d)
                ref_slack = 0.0
            else:
                xstar, kr, cr, _ = run_fb(P, alpha, REF_TOL * r0, REF_CAP)
                rr = float(np.linalg.norm(P.residual(xstar, alpha)))
                ref_slack = rr / dc["decl"]["band"]["sigma_E"]
                row.update(ref_iters=kr, ref_censored=cr, ref_resid=rr)
            dist = float(np.linalg.norm(x - xstar))
            row["dist"] = dist
            row["ref_slack"] = ref_slack
            row["dist_bound"] = {n: (eps / v["sigma_E"] if v["sigma_E"] > 0 else None)
                                 for n, v in dc["decl"].items()}
            row["xstar_rel_err_true"] = float(np.linalg.norm(xstar - xt)
                                              / np.linalg.norm(xt))
        else:
            # arm A/B: non-uniqueness probe along K1, lost high band
            B1 = fourier_basis(d, np.unique(omega(d)[1][~kept]))
            Pk = B1 @ B1.T
            row["norm_PK1_xtrue_rel"] = float(np.linalg.norm(Pk @ xt) / np.linalg.norm(xt))
            row["norm_PK1_xret"] = float(np.linalg.norm(Pk @ x))
            if lam == 0 and trunc:
                z = B1 @ np.random.default_rng(1000 + seed).standard_normal(B1.shape[1])
                z *= np.linalg.norm(x) / np.linalg.norm(z)
                row["energy_invariance_rel"] = abs(P.energy(x + z) - P.energy(x)) / abs(P.energy(x))
            row["lam_min_KtK"] = float(np.min(khat ** 2))
        if fista:
            t0 = time.perf_counter()
            xf, kf, cf, trf = run_fista(P, alpha, eps, CAP, trace)
            row["wall_solve_fista"] = time.perf_counter() - t0
            row.update(k_fista=kf, fista_censored=cf)
            if w2 > 0:
                row["dist_fista"] = float(np.linalg.norm(xf - xstar))
            if trace:
                traces[f"{arm}_s{s}_w{w2}_lam{lam}_fista"] = np.array(trf)
        if seed == 0:
            row["wall_step"] = time_it(lambda: P.T(x, alpha), 300)
            row["wall_cert"] = time_it(lambda: np.linalg.norm(P.residual(x, alpha)), 300)
        # arm B secant modulus along the highest-frequency (kernel) mode
        if arm == "B" and seed == 0:
            z = (-1.0) ** np.arange(d) / math.sqrt(d)
            Ex = P.energy(x)
            ts = np.logspace(-3, 3, 25)
            sec = [(P.energy(x + t * z) + P.energy(x - t * z) - 2 * Ex) / t ** 2
                   for t in ts]
            bound = [2 * lam * np.abs(P.W @ z).sum() / t for t in ts]
            top = ts >= 1e2
            slope = float(np.polyfit(np.log10(ts[top]), np.log10(np.array(sec)[top]), 1)[0])
            secant.append({"s": s, "lam": lam, "t": ts.tolist(), "sigma_sec": sec,
                           "bound": bound, "slope_top_decade": slope,
                           "bound_holds": bool(all(a <= b * (1 + 1e-9) + 1e-15
                                                   for a, b in zip(sec, bound)))})
        rows.append(row)
        print(f"[{time.time()-t_start:7.1f}s] {arm} d={d} s={s} w2={w2} lam={lam} "
              f"seed={seed} k_meas={k}{' CENSORED' if cens else ''}"
              + (f" k_fista={row.get('k_fista')}" if fista else "")
              + (f" k_cert={row.get('k_cert')}" if w2 > 0 else ""), flush=True)

    for s in S_GRID:
        for seed in SEEDS:
            one("A", D_MAIN, s, 0.0, 0.0, seed, fista=True)
            for lam in LAM_B:
                one("B", D_MAIN, s, 0.0, lam, seed)
            for w2 in W2_GRID:
                for lam in (0.0, LAM_C):
                    one("C", D_MAIN, s, w2, lam, seed, fista=True,
                        trace=(seed == 0 and s == 2.0 and w2 == 0.1))
    for seed in SEEDS:
        one("A_G", D_MAIN, 2.0, 0.0, 0.0, seed, trunc=False)
        one("C_G", D_MAIN, 2.0, 0.1, 0.0, seed, trunc=False, fista=True)
    for d in D_SCALE:
        one("C_dscale", d, 2.0, 0.1, 0.0, 0, fista=True)

    with open(RESULTS / "runs.jsonl", "w") as f:
        for r in rows:
            f.write(json.dumps(r) + "\n")
    with open(RESULTS / "arm_b_secant.jsonl", "w") as f:
        for r in secant:
            f.write(json.dumps(r) + "\n")
    np.savez_compressed(RESULTS / "traces.npz", **traces)
    print(f"done: {len(rows)} runs in {time.time()-t_start:.1f}s")
    return True


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--run", action="store_true")
    a = ap.parse_args()
    ok = True
    if a.calibrate:
        ok = calibrate()
    if a.run and ok:
        ok = main_run()
    sys.exit(0 if ok else 1)

#!/usr/bin/env python3
"""exp_010 harness: hybrid precision, a certificate for the float32 run of the deconvolution
example. Brief: ../experiment/exp_method.md (frozen). Modes: --calibrate, --classify, --live.

Precision model (brief section 4): every product is rounded once, sums in any order; the a priori
bound e composes Jeannerod-Rump 2013 Props 3.1 and 4.1 with the one-operation bound |fl(t) - t| <= u |fl(t)|
(dossier B72-SND Lemma A; final constant 2u E_hat). Tier 1 = the same evaluation in float64 with its bound;
tier 2 = mpmath intervals. Repaired after the stage-2 audit (exact-leaf majorants, guard, tier gating).
"""
import json
import math
import os
import subprocess
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np
import mpmath
from mpmath import iv

HERE = Path(__file__).resolve().parent.parent
import importlib.util  # noqa: E402
_spec = importlib.util.spec_from_file_location("exp007_harness", HERE.parent / "exp_007_deconvolution" / "src" / "harness.py")
H7 = importlib.util.module_from_spec(_spec)   # the exp_007 problem constructors, loaded by path (name clash with this file)
_spec.loader.exec_module(H7)

R = HERE / "results"
RUNS = HERE / "runs"
D = 256
S_BLUR = 2
W2 = 0.1
LAM_L1 = 0.01
SEEDS = [0, 1, 2, 3]
K_CLASS = 160
K_LIVE = 400
B_RERUN_CAP = 40
U32 = 2.0 ** -24
U64 = 2.0 ** -53
INFL = 1.0 + 2.0 ** -40          # dominates the float64 rounding of the bound itself (brief section 4)
UNDERFLOW_GUARD = 2.0 ** -100        # float32 tier (normal range begins at 2^-126)
UNDERFLOW_GUARD_64 = 2.0 ** -900     # float64 tier (normal range begins at 2^-1022)
T_REPEATS = 20


# ---------------- declared data (stored float32) ----------------
class Data:
    def __init__(self, seed, lam):
        khat, jc, kept, xt, y = H7.make_data(D, S_BLUR, seed)
        kappa = np.fft.irfft(khat[: D // 2 + 1], n=D)           # circulant first column, float64
        self.kappa = kappa.astype(np.float32)
        self.y = y.astype(np.float32)
        self.w2 = np.float32(W2)
        self.lam = np.float32(lam)
        W, lev = H7.wavelet_matrix(D)
        self.W = W.astype(np.float32) if lam > 0 else None
        idx = (np.arange(D)[:, None] - np.arange(D)[None, :]) % D
        self.K = self.kappa[idx]                                  # K_ij = kappa[(i-j) mod d], float32
        # float32 step data (FFT form of the SAME declared K)
        self.khat32 = np.fft.rfft(self.kappa)                     # complex64
        self.dhat32 = (4.0 * np.sin(np.pi * np.arange(D // 2 + 1) / D) ** 2).astype(np.float32)
        self.h32 = (self.khat32 * np.conj(self.khat32)).real.astype(np.float32) + self.w2 * self.dhat32
        self.b32 = np.fft.irfft(np.conj(self.khat32) * np.fft.rfft(self.y), n=D).astype(np.float32)
        beta = (1.0 + 4.0 * W2) * (1.0 + 2.0 ** -20)
        self.alpha = np.float32(1.0 / beta)
        self._iv_cache = {}

    # interval copies of the data at a given precision (exact: every float32 is representable)
    def iv_data(self, prec):
        if prec in self._iv_cache:
            return self._iv_cache[prec]
        iv.prec = prec
        Kiv = [[iv.mpf(float(v)) for v in row] for row in self.K]
        yiv = [iv.mpf(float(v)) for v in self.y]
        Wiv = [[iv.mpf(float(v)) for v in row] for row in self.W] if self.W is not None else None
        out = (Kiv, yiv, Wiv, iv.mpf(float(self.w2)), iv.mpf(float(self.lam)))
        self._iv_cache[prec] = out
        return out


# ---------------- the float32 step (exp_007's forward-backward step, in float32) ----------------
def step32(data, z, alpha):
    g = np.fft.irfft(data.h32 * np.fft.rfft(z), n=D).astype(np.float32) - data.b32
    v = (z - alpha * g).astype(np.float32)
    if data.W is None:
        return v
    c = (data.W @ v).astype(np.float32)
    t = np.float32(alpha * data.lam)
    c = np.sign(c) * np.maximum(np.abs(c) - t, np.float32(0))
    return (data.W.T @ c).astype(np.float32)


# ---------------- direct evaluation with the a priori bound (Proposition 1) ----------------
def direct_eval(data, x, dt, bound_scale=1.0):
    """Returns (E_hat as float, e as float, guard_ok). dt = np.float32 or np.float64."""
    u = U32 if dt is np.float32 else U64          # Lemma A of the dossier: |fl(t) - t| <= u |fl(t)| for one operation
    K = data.K.astype(dt)
    y = data.y.astype(dt)
    w2 = dt(data.w2)
    lam = dt(data.lam)
    xx = x.astype(dt)
    d = len(xx)
    P = (K * xx[None, :]).astype(dt)              # each product rounded once
    s = P.sum(axis=1, dtype=dt)
    r = (s - y).astype(dt)
    r2 = (r * r).astype(dt)
    Dh = r2.sum(dtype=dt)
    v = (xx - np.roll(xx, 1)).astype(dt)
    v2 = (v * v).astype(dt)
    Sh = v2.sum(dtype=dt)
    half = dt(0.5)
    tS = (w2 * Sh).astype(dt)
    gmin = UNDERFLOW_GUARD if dt is np.float32 else UNDERFLOW_GUARD_64
    guard_ok = True

    def _prod_guard(prod, a, b):
        # H-NU: no product underflows. A product that flushed to zero from nonzero factors, or any nonzero
        # product below the guard, violates it (computed zeros are NOT skipped: assassination P1-02).
        flushed = (prod == 0) & (a != 0) & (b != 0)
        nz = np.abs(prod[prod != 0])
        return not flushed.any() and not (nz.size and nz.min() < gmin)

    guard_ok &= _prod_guard(P, K, xx[None, :] * np.ones_like(K))
    if lam > 0:
        W = data.W.astype(dt)
        Q = (W * xx[None, :]).astype(dt)
        c = Q.sum(axis=1, dtype=dt)
        ca = np.abs(c)
        Ah = ca.sum(dtype=dt)
        tA = (lam * Ah).astype(dt)
        guard_ok &= _prod_guard(Q, W, xx[None, :] * np.ones_like(W))
    else:
        ca = None
        tA = dt(0)
    E_hat = ((half * Dh + half * tS).astype(dt) + tA).astype(dt)
    guard_ok &= _prod_guard(r2, r, r) and _prod_guard(v2, v, v)
    guard_ok &= _prod_guard(np.array([tS]), np.array([w2]), np.array([Sh]))
    if lam > 0:
        guard_ok &= _prod_guard(np.array([tA]), np.array([lam]), np.array([Ah]))
    if not (np.isfinite(E_hat) and np.all(np.isfinite(P)) and np.all(np.isfinite(r2))):   # H-NO: no overflow
        guard_ok = False
    # the bound, in float64 from nonnegative terms
    # sum_j |K_ij x_j| (EXACT products in the formula) <= sum_j |fl(K_ij x_j)| / (1 - u), since |fl(p)| >= (1-u)|p|
    Pa = np.abs(P.astype(np.float64)).sum(axis=1) / (1.0 - u)
    ra = np.abs(r.astype(np.float64))
    e_i = d * u * Pa + u * ra
    E_D = d * u * float((ra * ra).sum()) / (1.0 - U64) + float((e_i * (2 * ra + e_i)).sum())   # ra*ra in float64: exact for float32 r, else majorised
    va = np.abs(v.astype(np.float64))
    E_S = d * u * float((va * va).sum()) / (1.0 - U64) + float((u * va * (2 * va + u * va)).sum())
    e = 0.5 * E_D + 0.5 * (float(w2) * E_S + u * abs(float(tS)))
    if lam > 0:
        Qa = np.abs(Q.astype(np.float64)).sum(axis=1) / (1.0 - u)      # same majorant for sum_j |W_ij x_j|
        f_i = d * u * Qa
        E_A = (d - 1) * u * float(ca.astype(np.float64).sum()) + float(f_i.sum())
        e += float(lam) * E_A + u * abs(float(tA))
    e += 2 * u * float(E_hat)                      # Route B of the dossier: 2u E_hat, no correction factor
    e = (e * INFL) * bound_scale                   # Proposition 1(b): e_used >= e (weight count 3d+13 <= 8191, d <= 2726)
    return float(E_hat), float(e), guard_ok


OUT = 2.0 ** -51


def outward(Eh, e):
    """Proposition 1(c): outward-rounded float64 endpoints of [Eh - e, Eh + e]."""
    hi = (Eh + e) * (1.0 + OUT)
    lo = Eh - e
    lo = 0.0 if lo <= 0.0 else lo * (1.0 - OUT)
    return lo, hi


def encl_direct(data, x, dt, bound_scale=1.0):
    Eh, e, ok = direct_eval(data, x, dt, bound_scale)
    lo, hi = outward(Eh, e)
    return lo, hi, ok


# ---------------- tier 2: interval evaluation (mpmath) ----------------
def _outward(a_lo, a_hi):
    lo = float(mpmath.mpf(a_lo))
    hi = float(mpmath.mpf(a_hi))
    lo = float(np.nextafter(lo, -np.inf))
    hi = float(np.nextafter(hi, np.inf))
    return lo, hi


def iv_energy_vec(data, xs, prec):
    """Energy of an interval vector xs (list of iv.mpf) as an interval; data exact."""
    Kiv, yiv, Wiv, w2iv, lamiv = data.iv_data(prec)
    iv.prec = prec
    d = len(xs)
    r = [iv.fsum(Kiv[i][j] * xs[j] for j in range(d)) - yiv[i] for i in range(d)]
    E = iv.fsum(ri * ri for ri in r) / 2
    v = [xs[i] - xs[i - 1] for i in range(d)]
    E += w2iv * iv.fsum(vi * vi for vi in v) / 2
    if Wiv is not None:
        c = [iv.fsum(Wiv[i][j] * xs[j] for j in range(d)) for i in range(d)]
        E += lamiv * iv.fsum(abs(ci) for ci in c)
    return E


def encl_iv(data, x32, prec=113):
    iv.prec = prec
    xs = [iv.mpf(float(t)) for t in x32]
    E = iv_energy_vec(data, xs, prec)
    return _outward(E.a, E.b)


def iv_soft(c, t):
    """Soft threshold of an interval, monotone so endpoints map to endpoints."""
    def st(a):
        a = mpmath.mpf(a)
        if a > t:
            return a - t
        if a < -t:
            return a + t
        return mpmath.mpf(0)
    lo, hi = st(c.a), st(c.b)
    return iv.mpf([lo, hi])


def b72_rerun_encl(data, z32, alpha, prec=113):
    """B72 as written: enclosure of the energy of the EXACT update T_alpha(z) from the float point z."""
    Kiv, yiv, Wiv, w2iv, lamiv = data.iv_data(prec)
    iv.prec = prec
    d = len(z32)
    zs = [iv.mpf(float(t)) for t in z32]
    a = iv.mpf(float(alpha))
    r = [iv.fsum(Kiv[i][j] * zs[j] for j in range(d)) - yiv[i] for i in range(d)]
    g = [iv.fsum(Kiv[i][j] * r[i] for i in range(d)) for j in range(d)]     # K^T r
    for i in range(d):
        g[i] = g[i] + w2iv * (2 * zs[i] - zs[i - 1] - zs[(i + 1) % d])
    v = [zs[i] - a * g[i] for i in range(d)]
    if Wiv is None:
        xs = v
    else:
        t = mpmath.mpf(float(alpha)) * mpmath.mpf(float(data.lam))
        c = [iv_soft(iv.fsum(Wiv[i][j] * v[j] for j in range(d)), t) for i in range(d)]
        xs = [iv.fsum(Wiv[i][j] * c[i] for i in range(d)) for j in range(d)]   # W^T c
    E = iv_energy_vec(data, xs, prec)
    return _outward(E.a, E.b)


# ---------------- ground truth ----------------
def truth(data, z, znew):
    """'rose' | 'fell' | 'tie', the tier that decided, and the enclosures."""
    lo0, hi0, ok0 = encl_direct(data, z, np.float64)
    lo1, hi1, ok1 = encl_direct(data, znew, np.float64)
    tier = 1
    if ok0 and ok1 and (hi1 < lo0 or lo1 > hi0):
        return ("fell" if hi1 < lo0 else "rose"), tier, (lo0, hi0, lo1, hi1)
    for prec in (113, 200):
        tier += 1
        lo0, hi0 = encl_iv(data, z, prec)
        lo1, hi1 = encl_iv(data, znew, prec)
        if hi1 < lo0 or lo1 > hi0:
            return ("fell" if hi1 < lo0 else "rose"), tier, (lo0, hi0, lo1, hi1)
    return "tie", tier, (lo0, hi0, lo1, hi1)


# ---------------- the repaired rule (Proposition 2), one decision ----------------
def rule_c(data, z, znew, B, bound_scale=1.0):
    """Returns dict(decision, branch, tier, lo, hi) for the proposed point znew against bound B."""
    Eh, e, ok = direct_eval(data, znew, np.float32, bound_scale)
    lo, hi = outward(Eh, e)
    if ok and hi < B:
        return dict(decision="accept", branch=1, tier=0, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    if ok and lo > B:
        return dict(decision="reject", branch=2, tier=0, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    lo, hi, ok1 = encl_direct(data, znew, np.float64)      # tier 1 decides only under its own guard
    if ok1 and hi < B:
        return dict(decision="accept", branch=3, tier=1, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    if ok1 and lo > B:
        return dict(decision="reject", branch=3, tier=1, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    lo, hi = encl_iv(data, znew, 113)
    if hi < B:
        return dict(decision="accept", branch=3, tier=2, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    if lo > B:
        return dict(decision="reject", branch=3, tier=2, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    if np.array_equal(z, znew):
        return dict(decision="stop_fixed", branch=3, tier=2, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)
    return dict(decision="reject_undecided", branch=3, tier=2, lo=lo, hi=hi, E32=Eh, e32=e, guard=ok)


# ---------------- modes ----------------
def arms():
    return [("C-smooth", 0.0), ("C-l1", LAM_L1)]


def classify(mutant=False):
    rows = []
    for arm, lam in arms():
        if mutant and lam > 0:
            continue
        for seed in SEEDS:
            data = Data(seed, lam)
            z = np.zeros(D, dtype=np.float32)
            E32_prev, _, _ = direct_eval(data, z, np.float32)
            lo0, hi0, _ = encl_direct(data, z, np.float64)
            B = hi0
            n_rerun = 0
            for k in range(K_CLASS):
                t0 = time.perf_counter()
                znew = step32(data, z, data.alpha)
                t_step = time.perf_counter() - t0
                t0 = time.perf_counter()
                rc = rule_c(data, z, znew, B, bound_scale=(1e-3 if mutant else 1.0))
                t_c = time.perf_counter() - t0
                dec_a = "accept" if rc["E32"] < E32_prev else "reject"
                dec_b, t_b = None, 0.0
                if not mutant:
                    if dec_a == "accept":
                        dec_b = "accept"
                    elif n_rerun < B_RERUN_CAP:
                        t0 = time.perf_counter()
                        lo_b, hi_b = b72_rerun_encl(data, z, data.alpha)
                        t_b = time.perf_counter() - t0
                        dec_b = "accept" if hi_b < E32_prev else "reject"
                        n_rerun += 1
                    else:
                        dec_b = "not_evaluated"
                tr, tier_t, encs = truth(data, z, znew)
                rows.append(dict(
                    arm=arm, seed=seed, k=k + 1, mutant=mutant,
                    dec_a=dec_a, dec_b=dec_b, dec_c=rc["decision"], branch=rc["branch"], tier_c=rc["tier"],
                    truth=tr, tier_truth=tier_t, E32=rc["E32"], e32=rc["e32"], B=B, lo_c=rc["lo"], hi_c=rc["hi"],
                    enc_prev_lo=encs[0], enc_prev_hi=encs[1], enc_new_lo=encs[2], enc_new_hi=encs[3],
                    guard=rc["guard"], t_step=t_step, t_c=t_c, t_b=t_b,
                    fixed=bool(np.array_equal(z, znew))))
                # carry
                if rc["decision"] == "accept":
                    B = rc["hi"]
                else:
                    lo1, hi1, _ = encl_direct(data, znew, np.float64)
                    B = hi1
                E32_prev = rc["E32"]
                z = znew
            print(f"classify {arm} seed {seed} done ({'mutant' if mutant else 'main'})", flush=True)
    name = "mutant.jsonl" if mutant else "steps.jsonl"
    (R / name).write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    return rows


def live():
    rows = []
    summ = {}
    for arm, lam in arms():
        for seed in SEEDS:
            data = Data(seed, lam)
            z = np.zeros(D, dtype=np.float32)
            lo0, hi0, _ = encl_direct(data, z, np.float64)
            B = hi0
            alpha = data.alpha
            halvings = 0
            status = "cap"
            counts = {1: 0, 2: 0, 3: 0}
            k = 0
            while k < K_LIVE:
                znew = step32(data, z, alpha)
                rc = rule_c(data, z, znew, B)
                counts[rc["branch"]] += 1
                rows.append(dict(arm=arm, seed=seed, k=k + 1, alpha=float(alpha), decision=rc["decision"],
                                 branch=rc["branch"], tier=rc["tier"], B=B, lo=rc["lo"], hi=rc["hi"],
                                 E32=rc["E32"], e32=rc["e32"]))
                if rc["decision"] == "accept":
                    z, B = znew, rc["hi"]
                    k += 1
                    continue
                if rc["decision"] == "stop_fixed":
                    status = "fixed_point"
                    break
                # reject (branch 2, tier-decided rise, or undecided): halve and retry
                halvings += 1
                if halvings > 10:
                    status = "step_exhausted"
                    break
                alpha = np.float32(alpha / 2)
            summ[f"{arm}/seed{seed}"] = dict(steps=k, status=status, halvings=halvings, branch_counts=counts,
                                             final_alpha=float(alpha), final_B=B)
            print(f"live {arm} seed {seed}: {status} at k={k}, halvings={halvings}, branches={counts}", flush=True)
    (R / "live.jsonl").write_text("\n".join(json.dumps(r) for r in rows) + "\n")
    (R / "summary_live.json").write_text(json.dumps(summ, indent=1))
    return summ


def calibrate():
    out = {}
    data = Data(0, LAM_L1)
    rng = np.random.default_rng(42)
    pts = []
    for scale, n in ((1.0, 67), (1e-3, 67), (1e3, 66)):           # 200 points, three scales
        for _ in range(n):
            pts.append((rng.standard_normal(D) * scale).astype(np.float32))
    assert len(pts) == 200
    c1 = c2 = c3a = c3b = 0
    for x in pts:
        lo2, hi2 = encl_iv(data, x, 113)
        lo32, hi32, _ = encl_direct(data, x, np.float32)
        lo64, hi64, _ = encl_direct(data, x, np.float64)
        c1 += int(lo32 <= lo2 and hi2 <= hi32)
        lom, him, _ = encl_direct(data, x, np.float32, bound_scale=1e-3)
        c2 += int(not (lom <= lo2 and hi2 <= him))
        c3a += int(lo64 <= lo2 and hi2 <= hi64)
        c3b += int((hi64 - lo64) < (hi32 - lo32))
    out["CAL1_float32_contains_tier2"] = f"{c1}/200"
    out["CAL1_pass"] = c1 == 200
    out["CAL2_mutant_fails_count"] = c2
    out["CAL2_pass_watched_failure"] = c2 >= 1
    out["CAL3_tier1_contains_tier2"] = f"{c3a}/200"
    out["CAL3_tier1_narrower"] = f"{c3b}/200"
    out["CAL3_pass"] = (c3a == 200 and c3b == 200)
    # CAL-4: x = 0, exact rational value from the float32 y
    exact = sum(Fraction(float(v)) ** 2 for v in data.y) / 2
    x0 = np.zeros(D, dtype=np.float32)
    lo2, hi2 = encl_iv(data, x0, 113)
    lo32, hi32, _ = encl_direct(data, x0, np.float32)
    out["CAL4_exact_in_tier2"] = bool(Fraction(lo2) <= exact <= Fraction(hi2))
    out["CAL4_exact_in_float32"] = bool(Fraction(lo32) <= exact <= Fraction(hi32))
    out["CAL4_pass"] = out["CAL4_exact_in_tier2"] and out["CAL4_exact_in_float32"]
    # CAL-5: determinism
    x = pts[0]
    a1 = direct_eval(data, x, np.float32)
    a2 = direct_eval(data, x, np.float32)
    s1 = step32(data, x, data.alpha)
    s2 = step32(data, x, data.alpha)
    out["CAL5_pass"] = (a1 == a2 and np.array_equal(s1, s2))
    # timings (P6)
    def med(fn, reps=T_REPEATS):
        ts = []
        for _ in range(reps):
            t0 = time.perf_counter()
            fn()
            ts.append(time.perf_counter() - t0)
        return float(np.median(ts))
    out["t_eval32_s"] = med(lambda: direct_eval(data, x, np.float32))
    out["t_eval64_s"] = med(lambda: direct_eval(data, x, np.float64))
    out["t_iv113_s"] = med(lambda: encl_iv(data, x, 113))
    out["t_b72_rerun_s"] = med(lambda: b72_rerun_encl(data, x, data.alpha))
    out["t_step32_s"] = med(lambda: step32(data, x, data.alpha))
    out["P6_tier1_over_eval32"] = out["t_eval64_s"] / out["t_eval32_s"]
    out["P6_tier2_over_eval32"] = out["t_iv113_s"] / out["t_eval32_s"]
    out["all_pass"] = all(out[k] for k in out if k.endswith("_pass") or k == "CAL2_pass_watched_failure")
    (R / "calibration.json").write_text(json.dumps(out, indent=1))
    print(json.dumps(out, indent=1))
    if not out["all_pass"]:
        sys.exit("calibration FAILED")


def manifest(cmd):
    sha = subprocess.run(["git", "rev-parse", "HEAD"], capture_output=True, text=True, cwd=HERE).stdout.strip()
    brief = (HERE / "experiment" / "exp_method.md").read_bytes()
    import hashlib
    import pywt, scipy
    m = dict(experiment="exp_010_hybrid_precision", git_sha=sha,
             brief_sha256=hashlib.sha256(brief).hexdigest(),
             python=sys.version.split()[0], numpy=np.__version__, scipy=scipy.__version__,
             pywt=pywt.__version__, mpmath=mpmath.__version__,
             seeds=SEEDS, K_classify=K_CLASS, K_live=K_LIVE, b72_rerun_cap=B_RERUN_CAP,
             threads=os.environ.get("OMP_NUM_THREADS"), command=cmd, at=time.strftime("%Y-%m-%d %H:%M:%S"))
    p = RUNS / "run_manifest.json"
    old = json.loads(p.read_text()) if p.exists() else {}
    old[cmd] = m
    p.write_text(json.dumps(old, indent=1))


if __name__ == "__main__":
    R.mkdir(exist_ok=True)
    RUNS.mkdir(exist_ok=True)
    mode = sys.argv[1] if len(sys.argv) > 1 else "--calibrate"
    t0 = time.perf_counter()
    if mode == "--calibrate":
        calibrate()
    elif mode == "--classify":
        classify(mutant=False)
        classify(mutant=True)
    elif mode == "--live":
        live()
    else:
        sys.exit(f"unknown mode {mode}")
    manifest(mode)
    print(f"{mode} finished in {time.perf_counter() - t0:.1f} s")

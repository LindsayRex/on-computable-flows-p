#!/usr/bin/env python3
"""exp_008 calibration gates (brief section 8). Runs BEFORE any real reading;
any failed gate aborts the experiment and the failure is itself a result (M5)."""
import pathlib
import sys

import numpy as np

sys.path.insert(0, str(pathlib.Path(__file__).parent))
import exp008_lib as lib

HERE = pathlib.Path(__file__).resolve().parent.parent
OUT = HERE / "results/calibration.toml"
OUT.parent.mkdir(exist_ok=True)

lines, failures = ["[calibration]"], []


def gate(name, ok, detail):
    lines.append(f'{name} = {{ pass = {str(bool(ok)).lower()}, detail = "{detail}" }}')
    print(("PASS " if ok else "FAIL ") + name + ": " + detail)
    if not ok:
        failures.append(name)


# CAL-1: closed-form mu on linear fields.
mu_good = float(np.linalg.eigvalsh(np.diag([-1.0, -5.0]))[-1])
mu_bad = float(np.linalg.eigvalsh(np.diag([+1.0, -5.0]))[-1])
gate("CAL1_closed_form", abs(mu_good + 1.0) < 1e-9 and mu_bad > 0,
     f"mu(diag(-1,-5)) = {mu_good:.12f} (want -1 exactly); "
     f"mu(diag(+1,-5)) = {mu_bad:.12f} must refuse (>0)")

# CAL-2: Lorenz r=0.5, classical lens diag(1/sigma,1,1), grid sup over B(0.5).
lo, hi = lib.trap_box(0.5)
p_cls = [1.0 / lib.SIGMA, 1.0, 1.0]
sup_g, sup_v = lib.sup_mu(lo, hi, 0.5, p_cls, n_grid=41)
gate("CAL2_classical_pass_r0p5", sup_g < 0,
     f"grid sup mu = {sup_g:.6f}, exact vertex sup = {sup_v:.6f} over trap box "
     f"[{lo[0]:.2f},{hi[0]:.2f}]x[{lo[1]:.2f},{hi[1]:.2f}]x[{lo[2]:.2f},{hi[2]:.2f}]; "
     f"brief demanded s>0 here")

# CAL-3: Lyapunov ruler. Lorenz r=28 vs literature 0.906; harmonic oscillator = 0.
lam28 = lib.lyap1([28.0], n_seeds=8)
lam28_mean = float(lam28.mean())


def lyap_harmonic(t_meas=500.0, h=1e-3):
    state = np.array([1.0, 0.0])
    v = np.array([1.0, 0.0])
    A = np.array([[0.0, 1.0], [-1.0, 0.0]])
    logsum = 0.0
    for _ in range(int(t_meas / h)):
        def step(u):
            k1 = A @ u
            k2 = A @ (u + 0.5 * h * k1)
            k3 = A @ (u + 0.5 * h * k2)
            k4 = A @ (u + h * k3)
            return u + (h / 6) * (k1 + 2 * k2 + 2 * k3 + k4)
        state, v = step(state), step(v)
        n = np.linalg.norm(v)
        v /= n
        logsum += np.log(n)
    return logsum / t_meas


lam_ho = float(lyap_harmonic())
gate("CAL3_lyapunov_ruler", abs(lam28_mean - 0.906) < 0.03 and abs(lam_ho) < 1e-3,
     f"lambda1(r=28) mean over 8 seeds = {lam28_mean:.4f} "
     f"(min {float(lam28.min()):.4f}, max {float(lam28.max()):.4f}; want 0.906 +- 0.03); "
     f"harmonic oscillator lambda1 = {lam_ho:.2e} (want |.| < 1e-3)")

# CAL-4: dumb baseline watched failing: divergence negative at r=28 yet chaotic.
trace = -(lib.SIGMA + 1.0 + lib.B)
gate("CAL4_divergence_watched_failing", trace < 0 and lam28_mean > 0.5,
     f"trace J = {trace:.4f} < 0 at ALL r (divergence test endorses the field) "
     f"while measured lambda1(r=28) = {lam28_mean:.4f} > 0: wrong instrument, watched")

lines.append("")
lines.append(f'all_gates_pass = {str(not failures).lower()}')
lines.append(f'failed = {failures!r}'.replace("'", '"'))
OUT.write_text("\n".join(lines) + "\n")
print(f"\nwrote {OUT}")
if failures:
    print("ABORT per brief section 8: failed gates are a result, not a reading.")
    sys.exit(1)

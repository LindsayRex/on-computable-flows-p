#!/usr/bin/env python3
"""Rule 110 as a flow (card #28 replacement; witness for the per-step theorem, card #49).

Written at the author's direction (2026-10-17) after the search of all three repos found the
original Windows-machine implementation uncommitted anywhere. See NOTES.md for the claims ledger.

The construction, in the paper's grammar:

  Row x in {0,1}^n on a ring (periodic boundary). The Rule 110 update of cell i is the polynomial
      t_i = c + r - c*r - l*c*r,     (l, c, r) = (x_{i-1}, x_i, x_{i+1}),
  which on {0,1} inputs equals OR(c, r) - AND(l, c, r): exactly Wolfram's rule 110 truth table.

  One step is computed by a flow, not by table lookup:
      declared energy   E(y) = 1/2 * ||y - t(x)||^2        (one smooth term)
      declaration       beta = 1 (gradient 1-Lipschitz), sigma = 1 (1-strongly convex)
      dynamics          dissipative primitive: y <- y - alpha * grad E(y),  grad E(y) = y - t(x)
      step              alpha = 1/beta-hat = 1 (the constructed iteration), or any alpha in (0,1]
      certificate       residual ||grad E(y)|| = ||y - t||; distance ||y - y*|| <= residual/sigma
                        (soundness theorem, regime A); rate q = 1 - alpha*sigma
      stopping rule     residual <= eps
      read-out          projective primitive: threshold at 1/2 (projection of y onto {0,1}^n,
                        exact whenever the certified distance is < 1/2, since y* = t in {0,1}^n)
      lens              the Hessian is the identity: dominance ratio eta = 0 in the identity lens,
                        and any orthonormal lens leaves it the identity (trivially diagonal).

  Per-step exactness, the shape of theorem #49: run the flow to certified distance < 1/2 and
  threshold; the result equals the Rule 110 row, for every row and every length.

Battery (all deterministic; artifact: summary.toml):
  A. exhaustive: every row of every length n = 1..12 (8190 rows), one flow step == reference;
  B. trajectory: n = 256 random row (seed 110), 512 steps, flow == reference at every step,
     at alpha = 1 and alpha = 0.4;
  C. certificate audit: observed iteration counts at alpha = 0.4 never exceed the count predicted
     from the declared numbers (rate q = 0.6, start residual, eps).
"""
from __future__ import annotations

import time

import numpy as np

RULE = 110
WOLFRAM_TABLE = {  # (l, c, r) -> next bit, read off the binary expansion of 110 = 0b01101110
    (1, 1, 1): 0, (1, 1, 0): 1, (1, 0, 1): 1, (1, 0, 0): 0,
    (0, 1, 1): 1, (0, 1, 0): 1, (0, 0, 1): 1, (0, 0, 0): 0,
}


def reference_step(x: np.ndarray) -> np.ndarray:
    """Ground truth: table lookup, periodic boundary."""
    l, c, r = np.roll(x, 1), x, np.roll(x, -1)
    idx = (l << 2) | (c << 1) | r
    lut = np.array([(RULE >> k) & 1 for k in range(8)], dtype=np.int64)
    return lut[idx]


def target(x: np.ndarray) -> np.ndarray:
    """The Rule 110 polynomial t = c + r - c r - l c r (equals the table on {0,1})."""
    l, c, r = np.roll(x, 1), x, np.roll(x, -1)
    return (c + r - c * r - l * c * r).astype(np.float64)


def flow_step(x: np.ndarray, alpha: float = 1.0, eps: float = 0.25):
    """One Rule 110 step by the constructed iteration on E(y) = 1/2 ||y - t(x)||^2.

    Returns (next row, certificate dict). The certificate is checked, not trusted:
    residual and distance bound come from the declared numbers (beta = sigma = 1).
    """
    assert 0.0 < alpha <= 1.0
    t = target(x)
    y = x.astype(np.float64)          # start from the current row
    sigma = 1.0                       # declared curvature of the one term
    iters = 0
    while True:
        grad = y - t                  # grad E(y)
        residual = float(np.linalg.norm(grad))
        if residual <= eps:
            break
        y = y - alpha * grad          # dissipative primitive, explicit Euler
        iters += 1
        if iters > 10_000:            # the certificate says this cannot happen; fail loudly
            raise RuntimeError("flow did not meet its certificate")
    distance_bound = residual / sigma  # soundness: ||y - y*|| <= residual / sigma
    out = (y > 0.5).astype(np.int64)   # projective read-out, exact when distance_bound < 1/2
    cert = {"iters": iters, "residual": residual, "distance_bound": distance_bound,
            "exact_readout": distance_bound < 0.5, "alpha": alpha, "rate_q": 1.0 - alpha * sigma}
    return out, cert


def predicted_count(res0: float, eps: float, q: float) -> int:
    """Iterations to drive the residual from res0 to eps at linear rate q (declared numbers)."""
    if res0 <= eps:
        return 0
    if q == 0.0:
        return 1
    return int(np.ceil(np.log(eps / res0) / np.log(q)))


def battery() -> dict:
    results: dict = {}

    # A. truth table, stated explicitly, against the polynomial on all 8 neighbourhoods
    poly = {(l, c, r): int(round(c + r - c * r - l * c * r)) for (l, c, r) in WOLFRAM_TABLE}
    assert poly == WOLFRAM_TABLE, "polynomial does not reproduce the Rule 110 table"
    results["truth_table_polynomial"] = "exact on all 8 neighbourhoods"

    # A'. exhaustive per-step equality for every row of every length 1..12
    total = 0
    for n in range(1, 13):
        for bits in range(2 ** n):
            x = np.array([(bits >> k) & 1 for k in range(n)], dtype=np.int64)
            out, cert = flow_step(x)
            assert cert["exact_readout"]
            assert np.array_equal(out, reference_step(x)), (n, bits)
            total += 1
    results["exhaustive_rows"] = total
    results["exhaustive_result"] = "flow == reference for every row, lengths 1..12"

    # B. long trajectory at two step sizes
    rng = np.random.default_rng(110)
    for alpha in (1.0, 0.4):
        x = rng.integers(0, 2, size=256).astype(np.int64)
        ref = x.copy()
        max_iters = 0
        for _ in range(512):
            x, cert = flow_step(x, alpha=alpha)
            ref = reference_step(ref)
            assert cert["exact_readout"]
            assert np.array_equal(x, ref)
            max_iters = max(max_iters, cert["iters"])
        results[f"trajectory_alpha_{alpha}"] = {
            "n": 256, "steps": 512, "agrees_with_reference": True, "max_iters_per_step": max_iters}

    # C. certificate audit at alpha = 0.4: observed count <= predicted from declared numbers
    x = rng.integers(0, 2, size=256).astype(np.int64)
    t = target(x)
    res0 = float(np.linalg.norm(x.astype(np.float64) - t))
    pred = predicted_count(res0, eps=0.25, q=0.6)
    _, cert = flow_step(x, alpha=0.4)
    assert cert["iters"] <= pred, (cert["iters"], pred)
    results["certificate_audit"] = {"start_residual": round(res0, 4), "predicted_count": pred,
                                    "observed_count": cert["iters"], "rate_q": 0.6, "eps": 0.25}
    return results


def main() -> None:
    t0 = time.time()
    results = battery()
    elapsed = time.time() - t0
    lines = ["# Rule 110 flow battery artifact (deterministic; seed 110 where random)",
             f"elapsed_seconds = {elapsed:.2f}", 'rule = 110', ""]
    for k, v in results.items():
        if isinstance(v, dict):
            lines.append(f"[{k}]")
            lines += [f"{kk} = {repr(vv).lower() if isinstance(vv, bool) else vv}" for kk, vv in v.items()]
            lines.append("")
        else:
            lines.append(f'{k} = "{v}"' if isinstance(v, str) else f"{k} = {v}")
    with open(__file__.rsplit("/", 1)[0] + "/summary.toml", "w") as f:
        f.write("\n".join(lines) + "\n")
    print("\n".join(lines))
    print("ALL CHECKS PASSED")


if __name__ == "__main__":
    main()

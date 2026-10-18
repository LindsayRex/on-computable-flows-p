"""exp_008 shared library. Brief: experiment/exp_method.md (FROZEN 2026-10-18).

Lorenz field F = (sigma(y-x), rx - y - xz, xy - bz), sigma=10, b=8/3.
Diagnostic quantity: mu_P(J(x)) = lambda_max of sym(D J D^-1), D = diag(sqrt(p)).
Certificate over a region: s = -sup mu_P; pass iff s > 0.
"""
import json
import math
import numpy as np

SIGMA, B = 10.0, 8.0 / 3.0


def f(state, r):
    """Lorenz field; state (..., 3)."""
    x, y, z = state[..., 0], state[..., 1], state[..., 2]
    return np.stack([SIGMA * (y - x), r * x - y - x * z, x * y - B * z], axis=-1)


def jv(state, v, r):
    """J(state) @ v, both (..., 3)."""
    x, y, z = state[..., 0], state[..., 1], state[..., 2]
    vx, vy, vz = v[..., 0], v[..., 1], v[..., 2]
    return np.stack([SIGMA * (vy - vx),
                     (r - z) * vx - vy - x * vz,
                     y * vx + x * vy - B * vz], axis=-1)


def jacobian(points, r):
    """J at points (..., 3) -> (..., 3, 3)."""
    x, y, z = points[..., 0], points[..., 1], points[..., 2]
    zero = np.zeros_like(x)
    one = np.ones_like(x)
    return np.stack([
        np.stack([-SIGMA * one, SIGMA * one, zero], axis=-1),
        np.stack([r - z, -one, -x], axis=-1),
        np.stack([y, x, -B * one], axis=-1)], axis=-2)


def mu_P(points, r, p):
    """mu_P(J) at each point; p = diagonal metric (3,)."""
    d = np.sqrt(np.asarray(p, dtype=float))
    J = jacobian(points, r)
    M = d[:, None] * J / d[None, :]
    S = 0.5 * (M + np.swapaxes(M, -1, -2))
    return np.linalg.eigvalsh(S)[..., -1]


def trap_box(r, inflate=1.5):
    """Bounding box of the trapping ellipsoid
    sigma x^2 + y^2 + b (z-(r+sigma)/2)^2 <= b (r+sigma)^2/4 (brief section 4),
    inflated about its centre. Returns (lo, hi) arrays (3,)."""
    c = (r + SIGMA) / 2.0
    ax = math.sqrt(B / (4.0 * SIGMA)) * (r + SIGMA)
    ay = math.sqrt(B) / 2.0 * (r + SIGMA)
    az = c
    half = inflate * np.array([ax, ay, az])
    centre = np.array([0.0, 0.0, c])
    return centre - half, centre + half


def ball_box(centre, rho):
    """Axis box circumscribing the ball of radius rho (sup over it upper-bounds
    the ball sup, so a pass over the box certifies the ball)."""
    c = np.asarray(centre, dtype=float)
    h = rho * np.ones(3)
    return c - h, c + h


def grid_points(lo, hi, n):
    axes = [np.linspace(lo[i], hi[i], n) for i in range(3)]
    g = np.stack(np.meshgrid(*axes, indexing="ij"), axis=-1)
    return g.reshape(-1, 3)


def vertices(lo, hi):
    out = []
    for i in range(8):
        out.append([hi[k] if (i >> k) & 1 else lo[k] for k in range(3)])
    return np.array(out)


def sup_mu(lo, hi, r, p, n_grid=41):
    """(grid sup, vertex sup). Entries of J are affine in the state and
    lambda_max of the symmetric part is convex, so the vertex sup is the exact
    sup over the box; the grid sup is the brief's registered reading."""
    g = float(mu_P(grid_points(lo, hi, n_grid), r, p).max())
    v = float(mu_P(vertices(lo, hi), r, p).max())
    return g, v


def optimise_lens(lo, hi, r, p0):
    """Nelder-Mead on log(p1,p3) with p2=1 (scale invariance), minimising the
    exact vertex sup. Returns (p, vertex sup at p)."""
    from scipy.optimize import minimize
    vtx = vertices(lo, hi)

    def obj(q):
        p = np.array([math.exp(q[0]), 1.0, math.exp(q[1])])
        return float(mu_P(vtx, r, p).max())

    q0 = np.array([math.log(p0[0] / p0[1]), math.log(p0[2] / p0[1])])
    res = minimize(obj, q0, method="Nelder-Mead",
                   options={"xatol": 1e-4, "fatol": 1e-9, "maxiter": 400})
    p = np.array([math.exp(res.x[0]), 1.0, math.exp(res.x[1])])
    return p, float(res.fun)


def rk4_step(state, r, h):
    k1 = f(state, r)
    k2 = f(state + 0.5 * h * k1, r)
    k3 = f(state + 0.5 * h * k2, r)
    k4 = f(state + h * k3, r)
    return state + (h / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4)


def rk4_pair_step(state, v, r, h):
    """Joint RK4 on (state, tangent)."""
    k1, l1 = f(state, r), jv(state, v, r)
    s2, v2 = state + 0.5 * h * k1, v + 0.5 * h * l1
    k2, l2 = f(s2, r), jv(s2, v2, r)
    s3, v3 = state + 0.5 * h * k2, v + 0.5 * h * l2
    k3, l3 = f(s3, r), jv(s3, v3, r)
    s4, v4 = state + h * k3, v + h * l3
    k4, l4 = f(s4, r), jv(s4, v4, r)
    return (state + (h / 6.0) * (k1 + 2 * k2 + 2 * k3 + k4),
            v + (h / 6.0) * (l1 + 2 * l2 + 2 * l3 + l4))


def lyap1(rs, n_seeds=8, h=1e-3, t_trans=50.0, t_meas=500.0):
    """Benettin largest Lyapunov exponent, vectorised over r values and seeds.
    Returns (len(rs), n_seeds)."""
    rs = np.asarray(rs, dtype=float)
    R, K = len(rs), n_seeds
    r_b = rs[:, None]  # broadcasts against (R, K) state components
    states = np.empty((R, K, 3))
    for k in range(K):
        rng = np.random.default_rng(k)
        states[:, k, :] = rng.uniform(-1, 1, size=(R, 3)) + [0.0, 0.0, 10.0]
    for _ in range(int(round(t_trans / h))):
        states = rk4_step(states, r_b, h)
    v = np.zeros((R, K, 3))
    v[..., 0] = 1.0
    logsum = np.zeros((R, K))
    n = int(round(t_meas / h))
    for _ in range(n):
        states, v = rk4_pair_step(states, v, r_b, h)
        nrm = np.linalg.norm(v, axis=-1, keepdims=True)
        v = v / nrm
        logsum += np.log(nrm[..., 0])
    return logsum / t_meas


def write_jsonl(path, rows):
    with open(path, "w") as fh:
        for row in rows:
            fh.write(json.dumps(row) + "\n")

"""exp_009 library: instances, declared constants, forward-backward with nuclear prox,
certificates. Everything derives from the frozen brief (experiment/exp_method.md)."""
import numpy as np

D, N = 64, 256


def make_query(seed, m, kappa, d=D):
    """Q = U diag(s) V^T, s geometric from 1 down to 1/kappa over rank = min(m, d)."""
    rng = np.random.default_rng(seed)
    r = min(m, d)
    s = np.ones(r) if (kappa == 1 or r == 1) else np.exp(
        -np.log(kappa) * np.arange(r) / (r - 1))
    U = np.linalg.qr(rng.standard_normal((m, r)))[0]
    V = np.linalg.qr(rng.standard_normal((d, r)))[0]
    return U * s @ V.T


def make_keys(seed, n=N, d=D, rank=8, noise=0.1):
    rng = np.random.default_rng(10_000 + seed)
    A = rng.standard_normal((n, rank)) / np.sqrt(rank)
    B = rng.standard_normal((d, rank))
    return A @ B.T + noise * rng.standard_normal((n, d))


def gram_spectrum(Q, d=D):
    """Eigenvalues (ascending) and eigenbasis of G = Q^T Q, full d x d."""
    G = Q.T @ Q
    evals, evecs = np.linalg.eigh(G)
    evals = np.clip(evals, 0.0, None)
    # numerically zero eigenvalues below machine-scale threshold are exact zeros
    tol = evals[-1] * d * np.finfo(float).eps
    evals[evals < tol] = 0.0
    return G, evals, evecs


def constants(evals, mu):
    """Declared beta-hat and certified curvature sigma (P1)."""
    return evals[-1] + mu, evals[0] + mu


def dominance_identity(H):
    """The dominance test in the identity lens on H: every diagonal entry must
    exceed the sum of absolute off-diagonals in its row (P3)."""
    diag = np.diag(H)
    off = np.abs(H).sum(axis=1) - np.abs(diag)
    margins = diag - off
    return bool((margins > 0).all()), float(margins.min())


def svt(X, t):
    """Singular-value thresholding: prox of t * nuclear norm. X: (..., n, d)."""
    U, s, Vt = np.linalg.svd(X, full_matrices=False)
    s = np.clip(s - t, 0.0, None)
    return (U * s[..., None, :]) @ Vt, s


def certified_count(r0, eps, beta, sigma):
    """Direct count (P4): first k with (1 - sigma/beta)^k r0 <= eps."""
    if sigma <= 0 or r0 <= eps:
        return None if sigma <= 0 else 0
    return int(np.ceil(np.log(r0 / eps) / np.log(beta / (beta - sigma))))


def fb_batch(K, H, alpha, lam, eps_stop, cap, n_checkpoints=20, ratio_floor=None):
    """Forward-backward X+ = SVT_{alpha lam}(X - alpha (X-K) H) on a batch.
    K: (b, n, d), H: (b, d, d). Runs until residual <= eps_stop (per instance)
    or cap. Returns final X, per-instance iteration-of-first-crossing for each
    threshold in eps_stop (dict name->value), checkpoint rows, residual ratios.
    """
    b = K.shape[0]
    X = np.zeros_like(K)
    crossing = {nm: np.full(b, -1, dtype=int) for nm in eps_stop}
    # per-instance finest threshold across the named stopping levels
    finest = np.min(np.stack([np.broadcast_to(v, (b,)) for v in eps_stop.values()]), axis=0)
    res = np.full(b, np.inf)
    snapshots = []            # (k, res.copy(), X.copy())
    every = max(1, cap // n_checkpoints)
    worst_ratio = np.zeros(b)
    prev_res = None
    k = 0
    while (res > finest).any() and k < cap:
        grad = np.einsum("bnd,bde->bne", X - K, H)
        Xn, _ = svt(X - alpha[:, None, None] * grad, (alpha * lam)[:, None])
        res = np.linalg.norm((X - Xn).reshape(b, -1), axis=1) / alpha
        k += 1
        if prev_res is not None:
            # AMENDMENT 1: the ratio instrument is read only above its
            # cancellation floor (ratio_floor, typically 1e-6 r0).
            ok = prev_res > (0.0 if ratio_floor is None else ratio_floor)
            worst_ratio[ok] = np.maximum(worst_ratio[ok], (res / prev_res)[ok])
        prev_res = res.copy()
        for nm, ev in eps_stop.items():
            hit = (res <= ev) & (crossing[nm] < 0)
            crossing[nm][hit] = k
        if k % every == 0:
            snapshots.append((k, res.copy(), Xn.copy()))
        X = Xn
    return X, crossing, snapshots, res, worst_ratio, k


def logit_err(Q, X, Xref):
    d = (X - Xref) @ Q.T
    return float(np.linalg.norm(d))


def softmax(L):
    L = L - L.max(axis=-1, keepdims=True)
    E = np.exp(L)
    return E / E.sum(axis=-1, keepdims=True)


def attention_err(Q, X, Xref):
    """Frobenius error of softmax(Q X^T) vs softmax(Q Xref^T) (P5)."""
    A, B = softmax(Q @ X.T), softmax(Q @ Xref.T)
    return float(np.linalg.norm(A - B))

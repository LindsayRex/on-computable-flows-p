# exp_007 addendum — direct-contraction certified count (REGISTERED BEFORE COMPUTATION)

> **FROZEN before the computation, 2026-10-18.** Author approval: this session
> ("But option two, man. Just do it. Run it. We're here to get us right."), logged in
> research_log/LOG.md. Trigger: external reviewer A item A5.5 (triage M6,
> project_plan/done/v6_campaign/REVIEW_TRIAGE_2026-10-18.md). The original brief and all existing
> results files are untouched; this addendum adds a tighter certified-count formula over
> the SAME raw runs and re-runs the soundness checks against it. No new dynamics is run:
> the certificate is a pre-run formula of declared numbers, and the measured counts it is
> checked against are already in the artifact.

## 1. The registered formula

For a declaration with certified smoothness beta-hat and certified curvature sigma > 0,
initial residual r0 = ||R_alpha(x0)|| and target eps:

    k_direct(beta_hat, sigma, r0, eps) =
        0                                   if r0 <= eps
        1                                   if sigma >= beta_hat
        ceil( log(r0/eps) / log(beta_hat/(beta_hat - sigma)) )   otherwise

One-line derivation (classical chain, manuscript Known result cl:fb(b)): the constructed
map T is a q-contraction with q = 1 - sigma/beta-hat (gradient step contracts by q, the
proximal map is nonexpansive). With x_{k+1} = T x_k and R_alpha(x) = (x - Tx)/alpha:
||x_{k+1} - T x_{k+1}|| = ||T x_k - T x_{k+1}|| <= q ||x_k - T x_k||, so
||R_alpha(x_k)|| <= q^k r0, and k_direct is the smallest k with q^k r0 <= eps. This sheds
the factor (2 beta-hat/sigma - 1) that the original registered formula k_cert_A pays for
the detour through ||x_k - x*||.

## 2. Scope

Every uncensored row of results/runs.jsonl whose k_cert field is a per-declaration dict
(arm C), for every declaration with sigma_E[declaration] > 0. The same r0 and eps as the
row (eps = 1e-6 * r0 throughout the artifact, so log(r0/eps) = log(1e6) exactly).

## 3. Pre-registered checks (all must hold; any failure is reported, never hidden)

- C1 (soundness): k_meas <= k_direct on every row and declaration in scope.
- C2 (tightening, never loosening): k_direct <= the row's registered k_cert on every row
  and declaration in scope.
- C3 (headline): recompute the two headline counts from the summary.toml declared numbers
  [headline_s2_w0p1_smooth] (beta_hat = 1.4, sigma_cert_band, sigma_cert_canonical,
  r0/eps = 1e6) and record them; these replace 2316 / 570862 in the manuscript if and only
  if C1 and C2 hold with zero failures.

## 4. Outputs

- results/direct_count.jsonl — one row per (run row, declaration): arm, w2, lam, s, seed,
  declaration, sigma, k_meas, k_cert_registered, k_direct, checks C1/C2 booleans.
- results/direct_count_summary.toml — totals of C1/C2, headline C3 values, slack
  statistics (k_direct / k_meas min/median/max per declaration).
- Script: src/direct_count_addendum.py (committed with this addendum).

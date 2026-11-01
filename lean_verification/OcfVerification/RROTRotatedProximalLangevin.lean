/-
R-ROT (the Gibbs certificate of the proximal Langevin word in two more orders, by rotation) — the abstract metric
form of Theorem A, from named hypotheses.

Source of truth: project_plan/doing/proof_audits/R_ROT_rotated_proximal_langevin/01_derivation.md, section 5
(adjudicated stage 3, 2026-11-02; rulings and the Lean-ready specification in 03_adjudication.md, section 3).
Dossier sha16 (first 16 hex of sha256sum of 01_derivation.md) at formalisation time: d765304879904781.

DEFINITIONAL MAP (dossier symbol — Lean name). `M` is the space of laws of finite second moment with the Wasserstein
distance of order 2 (a `MetricSpace`, Bullo Thm 6.12; abstract here). Letters act on laws in map notation:
* gradient letter D, noise letter N, proximal letter P — `AD AN AP : M → M`; the base word dnp (gradient, noise,
  proximal, in this order) applied to ν is `AP (AN (AD ν))`; npd is `AD (AP (AN ν))`; pdn is `AN (AD (AP ν))`;
* Gibbs law π_T, invariant law π_dnp of dnp, point-mass start δ_{x_0} — `piT`, `pidnp`, `nu0`;
  π_npd = π_dnp Q_D — `AD pidnp`; π_pdn = π_dnp Q_{N∘D} = π_npd Q_N — `AN (AD pidnp)` (definitional, no separate name);
* parameters m, L, h, T, M_g, r_*, d — `m L h T Mg rstar : ℝ`, `d : ℕ` (M_g is the Lipschitz attribute of the non-smooth
  term in the EUCLIDEAN norm; r_* is the landed start number of the conditional certificate);
* ρ = 1 − m h (contraction factor of D at zero declared curvature) — written `1 - m * h`; √(1 − m h) — `sigma m h`;
* B_* = (h/m)(M_g² + 2 L d T) — `Bstar m L h T Mg d`; √B_* — `b0 m L h T Mg d`;
* Υ_D = h (L √(T d/m) + M_g) — `DD m L h T Mg d`; Υ_N = √(2 T h d) — `DN T h d`;
  Υ_ND = √(Υ_D² + Υ_N²) — `DND m L h T Mg d`;
* flo_dnp = √B_*, flo_npd = ρ √B_* + Υ_D, flo_pdn = ρ √B_* + Υ_ND — `floDNP`, `floNPD`, `floPDN`.

NAMED HYPOTHESES (each a landed, classical or audited statement; none is proved in this file, none is a global axiom):
* `hm : 0 < m`, `hmL : m ≤ L`, `hh : 0 < h`, `hhL : h * L ≤ 1`, `hT : 0 < T`, `hMg : 0 ≤ Mg`, `hd : 0 < d`;
* `hDlip`: D is (1 − m h)-Lipschitz in W2 (landed `cl:r0-contraction`, Ryu–Yin Sec. 13.3 Prop. 2);
* `hNlip`: N is nonexpansive in W2 (same-ξ coupling); `hPlip`: P is nonexpansive in W2 (landed prox contraction);
* `hfix`: π_dnp is invariant for dnp;
* `hcert0`: the landed conditional certificate from a point, part (i), in square-root form, AT THE ONE START `nu0` only:
  W2(δ_{x_0} Q_dnp^K, π_T) ≤ √(1 − m h)^K W2(δ_{x_0}, π_T) + √B_*. No general-start hypothesis appears anywhere;
* `hDD`: W2(π_T Q_D, π_T) ≤ Υ_D (dossier Lemma on displacements, (i); proof idea: coupling, Minkowski, the cited bound
  ‖∇F(x*)‖ ≤ M_g of Beck/Bauschke–Combettes, the Gibbs second moment);
* `hDND`: W2(π_T Q_{N∘D}, π_T) ≤ Υ_ND (same lemma, (ii); Pythagorean combination with independent noise);
* `hr`: W2(δ_{x_0}, π_T) ≤ r_*.
Not hypotheses of this file: the noise displacement for every law, the proximal displacement, any general-start
certificate (they belong to the withdrawn second route of the dossier, kept in its supplement only).

COVERAGE (dossier item — Lean name), all in `r_rot` (one theorem, five groups of conjuncts), no sorry:
* Theorem A (i), the rotated invariant laws and uniqueness: `r_rot` group 1 (the Lipschitz factors 1 − m h, 1, 1 have
  product below one; uniqueness exactly as `huniq` in `OCF.RORD.r_ord_reversed`).
* The contraction to the own fixed point (lemma behind Route 1): group 2.
* Floors (Theorem A (ii) and the floor lemma for dnp), from `hcert0` at `nu0`, `hfix`, the contraction of dnp and K → ∞,
  and `OCF.RORD.rotation_w2_bound`: group 3, together with `DND ≤ DD + DN`, `DD ≤ floNPD`, `DD ≤ floPDN`, `0 < DD`
  (`flo_npd`, `flo_pdn` are at least Υ_D > 0).
* Theorem A (iii), the K-step bound through the own fixed point, and the triangle inequality for the start term: group 4.
* Theorem A (iv), the counts, as real arithmetic (`OCF.RSP.pow_mul_le_of_log`): group 5.
* Non-vacuity: `r_rot_model_hyps`, `r_rot_model` (M = ℝ, D x = (1 − m h) x, N = P = id, everything 0, m = L).
`OCF.RSP.step_mul_le` is not needed: `hhL : h * L ≤ 1` and `m ≤ L` give `m * h ≤ 1` directly.

NOT FORMALISED: the identification of M with the laws of finite second moment under W2; the law-level hypotheses
`hDlip`, `hNlip`, `hPlip`, `hfix`, `hcert0`, `hDD`, `hDND`, `hr` (landed results and the displacement lemma, all PROSE-ONLY with
full assassination in the dossier); the second-moment bound of the Gibbs law behind Υ_D and r_* (the lemma under the
author's pending call, `% AUTHOR'S CALL (HMOM)`); the proximal and Fermat facts of convex analysis; the other branch of the
start term, D̄_0/(h m), from the landed own-law certificate (it enters only as a hypothesis `dist nu0 (π_ω) ≤ S`); Theorem A
(v) evaluability; Part B, the refusal for the three orders dpn, ndp, pnd; the Euclidean-norm convention for M_g; sharpness
(the corner g = 0, m = L, h = 1/L is not formalised); any start other than a point mass.

Status tier: STATEMENT-FORMALISED (the conclusions are proved in the file from the named hypotheses on an abstract
metric space of laws, no sorry; the law-level hypotheses are not proved here), the same label `r_ord_reversed` carries in
`RORDOrderEffects.lean`. STATUS: COMPLETE.
-/
import Mathlib
import OcfVerification.RORDOrderEffects
import OcfVerification.RSPProximalLangevin

open OCF.RSP OCF.RORD

namespace OCF.RROT

/-! ## The real constants (explicit expressions) -/

/-- `√(1 − m h)`. -/
noncomputable def sigma (m h : ℝ) : ℝ := Real.sqrt (1 - m * h)

/-- `B_* = (h/m)(M_g² + 2 L d T)`, the squared floor of the landed conditional certificate. -/
noncomputable def Bstar (m L h T Mg : ℝ) (d : ℕ) : ℝ := h / m * (Mg ^ 2 + 2 * L * d * T)

/-- `√B_*`. -/
noncomputable def b0 (m L h T Mg : ℝ) (d : ℕ) : ℝ := Real.sqrt (Bstar m L h T Mg d)

/-- `Υ_D = h (L √(T d/m) + M_g)`: displacement bound of the gradient letter on the Gibbs law. -/
noncomputable def DD (m L h T Mg : ℝ) (d : ℕ) : ℝ := h * (L * Real.sqrt (T * d / m) + Mg)

/-- `Υ_N = √(2 T h d)`: displacement bound of the noise letter. -/
noncomputable def DN (T h : ℝ) (d : ℕ) : ℝ := Real.sqrt (2 * T * h * d)

/-- `Υ_ND = √(Υ_D² + Υ_N²)`: noise after gradient, on the Gibbs law. -/
noncomputable def DND (m L h T Mg : ℝ) (d : ℕ) : ℝ :=
  Real.sqrt (DD m L h T Mg d ^ 2 + DN T h d ^ 2)

/-- `flo_dnp = √B_*`. -/
noncomputable def floDNP (m L h T Mg : ℝ) (d : ℕ) : ℝ := b0 m L h T Mg d

/-- `flo_npd = ρ √B_* + Υ_D`. -/
noncomputable def floNPD (m L h T Mg : ℝ) (d : ℕ) : ℝ := (1 - m * h) * b0 m L h T Mg d + DD m L h T Mg d

/-- `flo_pdn = ρ √B_* + Υ_ND`. -/
noncomputable def floPDN (m L h T Mg : ℝ) (d : ℕ) : ℝ := (1 - m * h) * b0 m L h T Mg d + DND m L h T Mg d

/-! ## Helper lemmas on an abstract metric space -/

section helpers
variable {M : Type*} [MetricSpace M]

/-- A `c`-Lipschitz self-map iterated `K` times is `c ^ K`-Lipschitz. -/
lemma iter_lip (f : M → M) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x y, dist (f x) (f y) ≤ c * dist x y)
    (K : ℕ) (x y : M) : dist (f^[K] x) (f^[K] y) ≤ c ^ K * dist x y := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    calc dist (f (f^[K] x)) (f (f^[K] y)) ≤ c * dist (f^[K] x) (f^[K] y) := hf _ _
      _ ≤ c * (c ^ K * dist x y) := mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (K + 1) * dist x y := by ring

/-- Uniqueness of the fixed point of a `c`-Lipschitz map, `c < 1`. -/
lemma fixed_unique (f : M → M) {c : ℝ} (hc : c < 1) (hf : ∀ x y, dist (f x) (f y) ≤ c * dist x y)
    {p : M} (hp : f p = p) {x : M} (hx : f x = x) : x = p := by
  have h1 : dist x p ≤ c * dist x p := by
    calc dist x p = dist (f x) (f p) := by rw [hx, hp]
      _ ≤ c * dist x p := hf _ _
  have h2 : dist x p ≤ 0 := by nlinarith [dist_nonneg (x := x) (y := p)]
  exact dist_le_zero.1 h2

/-- The K-step bound through the own fixed point `fp` of `f`, with `dist fp piT ≤ flo`. -/
lemma kstep_bound (f : M → M) {c : ℝ} (hc : 0 ≤ c) (hf : ∀ x y, dist (f x) (f y) ≤ c * dist x y)
    {fp piT nu : M} (hfp : f fp = fp) {flo S : ℝ} (hfl : dist fp piT ≤ flo) (hS : dist nu fp ≤ S)
    (K : ℕ) : dist (f^[K] nu) piT ≤ c ^ K * S + flo := by
  have h1 : dist (f^[K] nu) fp ≤ c ^ K * dist nu fp := by
    have := iter_lip f hc hf K nu fp
    rwa [Function.iterate_fixed hfp K] at this
  have h2 : c ^ K * dist nu fp ≤ c ^ K * S :=
    mul_le_mul_of_nonneg_left hS (pow_nonneg hc K)
  calc dist (f^[K] nu) piT ≤ dist (f^[K] nu) fp + dist fp piT := dist_triangle _ _ _
    _ ≤ c ^ K * S + flo := by linarith

/-- The count: `q ^ K * S ≤ eps - flo` once `K ≥ ⌈log (S / (eps - flo)) / (h m)⌉₊`, with `q = 1 - m h`. -/
lemma count_arith {m h S eps flo : ℝ} (hm : 0 < m) (hh : 0 < h) (hq : 0 ≤ 1 - m * h) (hS : 0 ≤ S)
    (hfe : flo < eps) (K : ℕ) (hK : ⌈Real.log (S / (eps - flo)) / (h * m)⌉₊ ≤ K) :
    (1 - m * h) ^ K * S ≤ eps - flo := by
  have hk := Nat.ceil_le.1 hK
  have hhm : 0 < h * m := mul_pos hh hm
  have hk2 : Real.log (S / (eps - flo)) ≤ K * (1 - (1 - m * h)) := by
    rw [div_le_iff₀ hhm] at hk
    linarith
  exact pow_mul_le_of_log K hq hS (by linarith) hk2

end helpers

/-! ## The theorem -/

section main
variable {M : Type*} [MetricSpace M]

/-- **Theorem A (abstract metric form), R-ROT.** From the named hypotheses (see the file header; each is a landed,
classical or audited law-level statement, none proved here) the conclusions, in order:

1. Rotated invariant laws. (a) npd: `AD pidnp` is invariant for `x ↦ AD (AP (AN x))` and is its only fixed point;
   (b) pdn: `AN (AD pidnp)` is invariant for `x ↦ AN (AD (AP x))` and is its only fixed point (π_pdn = π_npd Q_N is
   definitional: `AN (AD pidnp) = AN (AD pidnp)`); (c) dnp: `pidnp` is its only fixed point.
2. Contraction to the own fixed point, factor `(1 - m h) ^ K`, for both rotated words and every start.
3. Floors: `W2(pidnp, piT) ≤ floDNP`, `W2(AD pidnp, piT) ≤ floNPD`, `W2(AN (AD pidnp), piT) ≤ floPDN`, and the real
   facts `DND ≤ DD + DN`, `DD ≤ floNPD`, `DD ≤ floPDN`, `0 < DD`.
4. Route 1: for every `S` with `dist nu0 (π_ω) ≤ S`, `dist (Q_ω^K nu0) piT ≤ (1 - m h)^K S + flo_ω` (ω = npd, pdn);
   and `dist nu0 (π_ω) ≤ rstar + flo_ω`, so `S := rstar + flo_ω` is admissible.
5. Counts: for `0 < S`, `flo_ω < eps`, `K ≥ ⌈log (S / (eps - flo_ω)) / (h m)⌉₊`: `(1 - m h)^K S ≤ eps - flo_ω`, and
   when `dist nu0 (π_ω) ≤ S` the K-step distance is at most `eps`.

NOT formalised here: the law-level instantiation of the hypotheses (the metric space `M` is abstract). -/
theorem r_rot (AD AN AP : M → M) (piT pidnp nu0 : M) {m L h T Mg rstar : ℝ} {d : ℕ}
    (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hhL : h * L ≤ 1) (hT : 0 < T) (hMg : 0 ≤ Mg)
    (hd : 0 < d)
    (hDlip : ∀ x y, dist (AD x) (AD y) ≤ (1 - m * h) * dist x y)
    (hNlip : ∀ x y, dist (AN x) (AN y) ≤ dist x y)
    (hPlip : ∀ x y, dist (AP x) (AP y) ≤ dist x y)
    (hfix : AP (AN (AD pidnp)) = pidnp)
    (hcert0 : ∀ K : ℕ, dist ((AP ∘ AN ∘ AD)^[K] nu0) piT ≤
      sigma m h ^ K * dist nu0 piT + b0 m L h T Mg d)
    (hDD : dist (AD piT) piT ≤ DD m L h T Mg d)
    (hDND : dist (AN (AD piT)) piT ≤ DND m L h T Mg d)
    (hr : dist nu0 piT ≤ rstar) :
    -- 1. rotated invariant laws
    (((AD (AP (AN (AD pidnp))) = AD pidnp ∧ ∀ x, AD (AP (AN x)) = x → x = AD pidnp) ∧
      (AN (AD (AP (AN (AD pidnp)))) = AN (AD pidnp) ∧ ∀ x, AN (AD (AP x)) = x → x = AN (AD pidnp)) ∧
      (∀ x, AP (AN (AD x)) = x → x = pidnp)) ∧
    -- 2. contraction to the own fixed point
    ((∀ (x : M) (K : ℕ), dist ((AD ∘ AP ∘ AN)^[K] x) (AD pidnp) ≤
        (1 - m * h) ^ K * dist x (AD pidnp)) ∧
      (∀ (x : M) (K : ℕ), dist ((AN ∘ AD ∘ AP)^[K] x) (AN (AD pidnp)) ≤
        (1 - m * h) ^ K * dist x (AN (AD pidnp)))) ∧
    -- 3. floors
    (dist pidnp piT ≤ floDNP m L h T Mg d ∧
      dist (AD pidnp) piT ≤ floNPD m L h T Mg d ∧
      dist (AN (AD pidnp)) piT ≤ floPDN m L h T Mg d ∧
      DND m L h T Mg d ≤ DD m L h T Mg d + DN T h d ∧
      DD m L h T Mg d ≤ floNPD m L h T Mg d ∧
      DD m L h T Mg d ≤ floPDN m L h T Mg d ∧
      0 < DD m L h T Mg d) ∧
    -- 4. Route 1
    ((∀ S : ℝ, dist nu0 (AD pidnp) ≤ S → ∀ K : ℕ,
        dist ((AD ∘ AP ∘ AN)^[K] nu0) piT ≤ (1 - m * h) ^ K * S + floNPD m L h T Mg d) ∧
      (∀ S : ℝ, dist nu0 (AN (AD pidnp)) ≤ S → ∀ K : ℕ,
        dist ((AN ∘ AD ∘ AP)^[K] nu0) piT ≤ (1 - m * h) ^ K * S + floPDN m L h T Mg d) ∧
      dist nu0 (AD pidnp) ≤ rstar + floNPD m L h T Mg d ∧
      dist nu0 (AN (AD pidnp)) ≤ rstar + floPDN m L h T Mg d)) ∧
    -- 5. counts
    ((∀ (S eps : ℝ) (K : ℕ), 0 < S → floNPD m L h T Mg d < eps →
        ⌈Real.log (S / (eps - floNPD m L h T Mg d)) / (h * m)⌉₊ ≤ K →
        (1 - m * h) ^ K * S ≤ eps - floNPD m L h T Mg d ∧
        (dist nu0 (AD pidnp) ≤ S → dist ((AD ∘ AP ∘ AN)^[K] nu0) piT ≤ eps)) ∧
      (∀ (S eps : ℝ) (K : ℕ), 0 < S → floPDN m L h T Mg d < eps →
        ⌈Real.log (S / (eps - floPDN m L h T Mg d)) / (h * m)⌉₊ ≤ K →
        (1 - m * h) ^ K * S ≤ eps - floPDN m L h T Mg d ∧
        (dist nu0 (AN (AD pidnp)) ≤ S → dist ((AN ∘ AD ∘ AP)^[K] nu0) piT ≤ eps))) := by
  -- numerical facts
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hmh : m * h ≤ 1 := by nlinarith
  have hmh0 : 0 < m * h := mul_pos hm hh
  have hq0 : 0 ≤ 1 - m * h := by linarith
  have hq1 : 1 - m * h < 1 := by linarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hDDnn : 0 ≤ DD m L h T Mg d := by
    unfold DD; have := Real.sqrt_nonneg (T * d / m); positivity
  have hDDpos : 0 < DD m L h T Mg d := by
    unfold DD
    have : 0 < Real.sqrt (T * d / m) := Real.sqrt_pos.2 (by positivity)
    have : 0 < L * Real.sqrt (T * d / m) := by positivity
    positivity
  have hDNnn : 0 ≤ DN T h d := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b0 m L h T Mg d := Real.sqrt_nonneg _
  have hσ0 : 0 ≤ sigma m h := Real.sqrt_nonneg _
  have hσ1 : sigma m h < 1 := by
    unfold sigma; rw [Real.sqrt_lt' one_pos]; linarith
  -- Lipschitz bounds of the three words
  have hdnp : ∀ x y, dist (AP (AN (AD x))) (AP (AN (AD y))) ≤ (1 - m * h) * dist x y := fun x y =>
    ((hPlip _ _).trans (hNlip _ _)).trans (hDlip x y)
  have hnpd : ∀ x y, dist (AD (AP (AN x))) (AD (AP (AN y))) ≤ (1 - m * h) * dist x y := fun x y =>
    (hDlip _ _).trans (mul_le_mul_of_nonneg_left ((hPlip _ _).trans (hNlip _ _)) hq0)
  have hpdn : ∀ x y, dist (AN (AD (AP x))) (AN (AD (AP y))) ≤ (1 - m * h) * dist x y := fun x y =>
    (hNlip _ _).trans ((hDlip _ _).trans (mul_le_mul_of_nonneg_left (hPlip _ _) hq0))
  have hND : ∀ x y, dist ((AN ∘ AD) x) ((AN ∘ AD) y) ≤ (1 - m * h) * dist x y := fun x y =>
    (hNlip _ _).trans (hDlip x y)
  -- fixed points
  have hfixnpd : AD (AP (AN (AD pidnp))) = AD pidnp := congrArg AD hfix
  have hfixpdn : AN (AD (AP (AN (AD pidnp)))) = AN (AD pidnp) := congrArg (fun z => AN (AD z)) hfix
  -- floor of dnp
  have hfl : dist pidnp piT ≤ b0 m L h T Mg d := by
    have hK : ∀ K : ℕ, dist pidnp piT ≤
        (1 - m * h) ^ K * dist nu0 pidnp + (sigma m h ^ K * dist nu0 piT + b0 m L h T Mg d) := by
      intro K
      have h1 : dist ((AP ∘ AN ∘ AD)^[K] nu0) pidnp ≤ (1 - m * h) ^ K * dist nu0 pidnp := by
        have := iter_lip (fun x => AP (AN (AD x))) hq0 hdnp K nu0 pidnp
        rwa [Function.iterate_fixed (f := fun x => AP (AN (AD x))) (x := pidnp) hfix K] at this
      have h2 := hcert0 K
      have h3 : dist pidnp piT ≤ dist pidnp ((AP ∘ AN ∘ AD)^[K] nu0) +
          dist ((AP ∘ AN ∘ AD)^[K] nu0) piT := dist_triangle _ _ _
      rw [dist_comm pidnp ((AP ∘ AN ∘ AD)^[K] nu0)] at h3
      linarith
    have hlim : Filter.Tendsto
        (fun K : ℕ => (1 - m * h) ^ K * dist nu0 pidnp +
          (sigma m h ^ K * dist nu0 piT + b0 m L h T Mg d)) Filter.atTop
        (nhds (0 * dist nu0 pidnp + (0 * dist nu0 piT + b0 m L h T Mg d))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _).add
        (((tendsto_pow_atTop_nhds_zero_of_lt_one hσ0 hσ1).mul_const _).add_const _)
    rw [zero_mul, zero_mul, zero_add, zero_add] at hlim
    exact ge_of_tendsto' hlim hK
  -- floors of the rotated laws
  have hfl2 : dist (AD pidnp) piT ≤ floNPD m L h T Mg d := by
    have := rotation_w2_bound AD hDlip pidnp piT
    unfold floNPD
    nlinarith
  have hDND_le : DND m L h T Mg d ≤ DD m L h T Mg d + DN T h d := by
    unfold DND
    rw [Real.sqrt_le_iff]
    exact ⟨by linarith, by nlinarith⟩
  have hDD_le_DND : DD m L h T Mg d ≤ DND m L h T Mg d := by
    unfold DND
    exact (le_abs_self _).trans (Real.abs_le_sqrt (by nlinarith [sq_nonneg (DN T h d)]))
  have hfl3 : dist (AN (AD pidnp)) piT ≤ floPDN m L h T Mg d := by
    have := rotation_w2_bound (AN ∘ AD) hND pidnp piT
    have h1 : dist ((AN ∘ AD) piT) piT ≤ DND m L h T Mg d := hDND
    unfold floPDN
    have h2 : dist ((AN ∘ AD) pidnp) piT ≤ (1 - m * h) * dist pidnp piT + DND m L h T Mg d := by
      linarith
    have h3 : (1 - m * h) * dist pidnp piT ≤ (1 - m * h) * b0 m L h T Mg d :=
      mul_le_mul_of_nonneg_left hfl hq0
    exact h2.trans (by linarith)
  have hqb : 0 ≤ (1 - m * h) * b0 m L h T Mg d := mul_nonneg hq0 hb0
  have hDD_flo2 : DD m L h T Mg d ≤ floNPD m L h T Mg d := by unfold floNPD; linarith
  have hDD_flo3 : DD m L h T Mg d ≤ floPDN m L h T Mg d := by unfold floPDN; linarith
  -- distances of the start to the rotated laws
  have hs2 : dist nu0 (AD pidnp) ≤ rstar + floNPD m L h T Mg d := by
    calc dist nu0 (AD pidnp) ≤ dist nu0 piT + dist piT (AD pidnp) := dist_triangle _ _ _
      _ ≤ rstar + floNPD m L h T Mg d := by rw [dist_comm piT]; linarith
  have hs3 : dist nu0 (AN (AD pidnp)) ≤ rstar + floPDN m L h T Mg d := by
    calc dist nu0 (AN (AD pidnp)) ≤ dist nu0 piT + dist piT (AN (AD pidnp)) := dist_triangle _ _ _
      _ ≤ rstar + floPDN m L h T Mg d := by rw [dist_comm piT]; linarith
  -- K-step bounds
  have hk2 : ∀ S : ℝ, dist nu0 (AD pidnp) ≤ S → ∀ K : ℕ,
      dist ((AD ∘ AP ∘ AN)^[K] nu0) piT ≤ (1 - m * h) ^ K * S + floNPD m L h T Mg d :=
    fun S hS K => kstep_bound (fun x => AD (AP (AN x))) hq0 hnpd hfixnpd hfl2 hS K
  have hk3 : ∀ S : ℝ, dist nu0 (AN (AD pidnp)) ≤ S → ∀ K : ℕ,
      dist ((AN ∘ AD ∘ AP)^[K] nu0) piT ≤ (1 - m * h) ^ K * S + floPDN m L h T Mg d :=
    fun S hS K => kstep_bound (fun x => AN (AD (AP x))) hq0 hpdn hfixpdn hfl3 hS K
  refine ⟨⟨⟨⟨hfixnpd, fun x hx => fixed_unique (fun x => AD (AP (AN x))) hq1 hnpd hfixnpd hx⟩,
      ⟨hfixpdn, fun x hx => fixed_unique (fun x => AN (AD (AP x))) hq1 hpdn hfixpdn hx⟩,
      fun x hx => fixed_unique (fun x => AP (AN (AD x))) hq1 hdnp hfix hx⟩,
    ⟨fun x K => by
        have := iter_lip (fun x => AD (AP (AN x))) hq0 hnpd K x (AD pidnp)
        rwa [Function.iterate_fixed (f := fun x => AD (AP (AN x))) (x := AD pidnp) hfixnpd K] at this,
      fun x K => by
        have := iter_lip (fun x => AN (AD (AP x))) hq0 hpdn K x (AN (AD pidnp))
        rwa [Function.iterate_fixed (f := fun x => AN (AD (AP x))) (x := AN (AD pidnp)) hfixpdn K]
          at this⟩,
    ⟨hfl, hfl2, hfl3, hDND_le, hDD_flo2, hDD_flo3, hDDpos⟩,
    ⟨hk2, hk3, hs2, hs3⟩⟩, ?_, ?_⟩
  · intro S eps K hS hfe hK
    have hc := count_arith hm hh hq0 hS.le hfe K hK
    exact ⟨hc, fun hS' => by linarith [hk2 S hS' K]⟩
  · intro S eps K hS hfe hK
    have hc := count_arith hm hh hq0 hS.le hfe K hK
    exact ⟨hc, fun hS' => by linarith [hk3 S hS' K]⟩

end main

/-! ## Non-vacuity: M = ℝ, D x = (1 − m h) x, N = P = id, piT = pidnp = nu0 = 0, rstar = 0, m = L -/

section model

/-- All eight law-level hypotheses hold in the model `M = ℝ`, `AD x = (1 − m h) x`, `AN = AP = id`,
`piT = pidnp = nu0 = 0`, `rstar = 0`, with `m = L`, `0 < m`, `0 < h`, `h * m ≤ 1`, `0 < T`, `0 ≤ Mg`, `0 < d`. -/
theorem r_rot_model_hyps {m h T Mg : ℝ} {d : ℕ} (hm : 0 < m) (hh : 0 < h) (hhm : h * m ≤ 1)
    (hT : 0 < T) (hMg : 0 ≤ Mg) (hd : 0 < d) :
    (∀ x y : ℝ, dist ((fun x : ℝ => (1 - m * h) * x) x) ((fun x : ℝ => (1 - m * h) * x) y) ≤
        (1 - m * h) * dist x y) ∧
    (∀ x y : ℝ, dist ((id : ℝ → ℝ) x) (id y) ≤ dist x y) ∧
    ((id : ℝ → ℝ) ((id : ℝ → ℝ) ((fun x : ℝ => (1 - m * h) * x) 0)) = 0) ∧
    (∀ K : ℕ, dist (((id : ℝ → ℝ) ∘ (id : ℝ → ℝ) ∘ (fun x : ℝ => (1 - m * h) * x))^[K] 0) 0 ≤
      sigma m h ^ K * dist (0 : ℝ) 0 + b0 m m h T Mg d) ∧
    dist ((fun x : ℝ => (1 - m * h) * x) 0) (0 : ℝ) ≤ DD m m h T Mg d ∧
    dist ((id : ℝ → ℝ) ((fun x : ℝ => (1 - m * h) * x) 0)) (0 : ℝ) ≤ DND m m h T Mg d ∧
    dist (0 : ℝ) 0 ≤ 0 := by
  have hq0 : 0 ≤ 1 - m * h := by nlinarith
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hDDnn : 0 ≤ DD m m h T Mg d := by
    unfold DD; have := Real.sqrt_nonneg (T * d / m); positivity
  refine ⟨fun x y => ?_, fun x y => le_rfl, by simp, fun K => ?_, ?_, ?_, ?_⟩
  · simp only [Real.dist_eq]
    rw [← mul_sub, abs_mul, abs_of_nonneg hq0]
  · have h0 : ∀ K : ℕ, ((id : ℝ → ℝ) ∘ (id : ℝ → ℝ) ∘ (fun x : ℝ => (1 - m * h) * x))^[K] 0 = 0 := by
      intro K
      exact Function.iterate_fixed (f := (id : ℝ → ℝ) ∘ (id : ℝ → ℝ) ∘ (fun x : ℝ => (1 - m * h) * x))
        (x := 0) (by simp) K
    rw [h0 K]
    simp only [dist_self, mul_zero, zero_add]
    exact Real.sqrt_nonneg _
  · simp only [mul_zero, dist_self]; exact hDDnn
  · simp only [mul_zero, dist_self, id]
    exact Real.sqrt_nonneg _
  · simp

/-- The theorem `r_rot` applied in the model, at `m = L = 1`, `h = 1`, `T = 1`, `Mg = 0`, `d = 1`: the
statement is satisfiable (hypotheses consistent) and its conclusion is instantiated. -/
theorem r_rot_model :
    ((1 : ℝ) - 1 * 1) ^ 0 * 0 + floNPD 1 1 1 1 0 1 = floNPD 1 1 1 1 0 1 ∧
    dist (0 : ℝ) 0 ≤ 0 + floNPD 1 1 1 1 0 1 := by
  have hm : (0:ℝ) < 1 := one_pos
  have hh : (0:ℝ) < 1 := one_pos
  have hd : 0 < (1 : ℕ) := one_pos
  have key := r_rot (M := ℝ) (fun x : ℝ => (1 - 1 * 1) * x) id id 0 0 0 (m := 1) (L := 1) (h := 1)
    (T := 1) (Mg := 0) (rstar := 0) (d := 1) hm le_rfl hh (by norm_num) one_pos le_rfl hd
    (r_rot_model_hyps (m := 1) (h := 1) (T := 1) (Mg := 0) (d := 1) hm hh (by norm_num) one_pos
      le_rfl hd).1
    (fun x y => le_rfl) (fun x y => le_rfl) (by simp)
    (r_rot_model_hyps (m := 1) (h := 1) (T := 1) (Mg := 0) (d := 1) hm hh (by norm_num) one_pos
      le_rfl hd).2.2.2.1
    (r_rot_model_hyps (m := 1) (h := 1) (T := 1) (Mg := 0) (d := 1) hm hh (by norm_num) one_pos
      le_rfl hd).2.2.2.2.1
    (r_rot_model_hyps (m := 1) (h := 1) (T := 1) (Mg := 0) (d := 1) hm hh (by norm_num) one_pos
      le_rfl hd).2.2.2.2.2.1
    (by simp)
  refine ⟨by simp, ?_⟩
  simpa using key.1.2.2.2.2.2.1
end model

/-! ## Axiom audit -/

#print axioms OCF.RROT.iter_lip
#print axioms OCF.RROT.fixed_unique
#print axioms OCF.RROT.kstep_bound
#print axioms OCF.RROT.count_arith
#print axioms OCF.RROT.r_rot
#print axioms OCF.RROT.r_rot_model_hyps
#print axioms OCF.RROT.r_rot_model

end OCF.RROT

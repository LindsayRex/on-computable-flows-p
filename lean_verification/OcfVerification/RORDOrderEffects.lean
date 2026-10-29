/-
R-ORD (order effects in an ordered noisy word) — the Lean targets the adjudicator marked FORMALISED in
the stage-3 tier table, plus the reversed-word corollary as a hypothesis-relative derivation.

Source of truth: project_plan/doing/proof_audits/R_ORD_order_effects/01_derivation.md (adjudicated stage 3,
2026-10-30; rulings in 03_adjudication.md, "Surviving statements and tiers"; repaired by the D rulings, section 1b).
Sections used: 2 (r-ord-coincide), 3 (r-ord-rotation), 4 (r-ord-undetermined), 5 (r-ord-row), 7 (r-ord-reversed).
Dossier sha16 (first 16 hex of sha256sum of 01_derivation.md): 9a471d7941d562a7 (main session 2026-10-30: the corollary statement now lists the six hypotheses this file names, no statement changed; previously 58fec7a01e0d19ec, drift-checked 2026-10-30 against the
D-repaired text; the file was first formalised against 248c9b1dd81878bb). Drift check result: every statement below matches
the repaired text; the only change is the added contrast `instance_c` (the {1,1,2} spectrum of part (v)).

DEFINITIONAL MAP (dossier symbol — Lean name). Reused from `OCF.RSP` (RSPProximalLangevin.lean), NOT redefined:
the six orders `Ord6` (.DNP .DPN .NDP .NPD .PDN .PND = dnp, dpn, ndp, npd, pdn, pnd, application order),
a = 1 − h κ, u = 1/(1 + h sg), ρ = a u (`rho κ h sg`), c_ω (`cOf κ sg h ω`), v_ω (`statVar T h κ sg ω`, the unique
fixed point `statVar_fixed`), Gibbs variance T/(κ + sg) (`gibbsVar T κ sg`), the class `InClass κ sg h T`
(κ > 0, 0 < h, h κ ≤ 1, sg ≥ 0, T > 0), `exact_iff`. Reused from `OCF.R0` (R0StackingLimits.lean): the one-dimensional
Gaussian W2 hypothesis `W2Gaussian gauss W2` (|σ₁ − σ₂|), `uF η = (1 − η/2)^(−1/2)`, `statND`, `statDN`, `floors_key`.
New here:
* C_ω = c_ω (1 + h sg) — `Cw κ sg h ω`; E = 2 + h (sg − κ) — `Ew κ sg h`; C_ω, E as polynomials in η = h κ at slope
  s = sg/κ — `Cpoly s η ω`, `Epoly s η` (`Cw_eq_poly`); criterion (C₁ + C₂)² − 2E — `coincPoly s η ω₁ ω₂`
  (and `coincPolyP : ℝ[X]`); the four pairs {dpn, pdn} × {ndp, npd} — `slicePair`.
* floor(ω) = W2(π_ω, π_T), laws N(0, v) DEFINED by their variances (as R0 `r0_order`) — `flr gauss W2 T h κ sg ω`.
* disp_ω(θ) = W2(θ Q_ω, θ) at θ = π_T: the variance map ρ² v + c_ω² 2Th — `pushVar`, `dispG`.
* Words as kernels: Q_W acts on laws by `Q ∘ₘ ν`; "U then V" is `Q_V ∘ₖ Q_U`; a word as a list — `wordK`.
* (M, dist) for (P_2, W2): an abstract (pseudo)metric space; the action of a word on laws is a map `A : M → M`;
  disp = `dist (A θ) θ`; λ-Lipschitz = `∀ x y, dist (A x) (A y) ≤ λ * dist x y`.
* Records F = ½ xᵀHx are represented by the SPECTRUM `μ : Fin d → ℝ` of H in an eigenbasis (the laws of all three
  words are products of one-dimensional centred Gaussians with commuting covariances): `Spec m L μ` (m ≤ μ_i ≤ L),
  declared numbers (m, L, h) — `Adm m L h` (0 < m ≤ L, 0 < h ≤ 2/(m+L)); per-direction squared floors
  `pND T μ h = (T/μ)(w − 1)²`, `pDN T μ h = (T/μ)(1 − |1 − η| w)²` with w = uF (h μ), η = h μ;
  f_ND, f_DN — `fND`, `fDN`; the spectrum {m, L × k} (d = k + 1) — `specK m L k`; H = m I, H = L I are
  `fun _ => m`, `fun _ => L`.

NAMED HYPOTHESES (classical inputs; never global axioms):
* `hW2 : W2Gaussian gauss W2` — Bullo, Contraction Theory for Dynamical Systems v1.3, Ex. 6.11 (iii), (iv), p. 229
  (VERIFIED in the dossier): W2(N(0, σ₁²), N(0, σ₂²)) = |σ₁ − σ₂|, σ ≥ 0 (σ = 0 the Dirac mass). Same hypothesis as R0.
* `hW : W2GaussianDiag gaussD W2` — Bullo Ex. 6.11 (iv), (6.44), p. 229: centred Gaussians with commuting (here diagonal,
  in the eigenbasis) covariances, W2 = ‖Σ₁^{1/2} − Σ₂^{1/2}‖_F = √Σ (a_i − b_i)². Non-vacuity: `w2GaussianDiag_model`.
* The AR(1) / independent-Gaussian-sum rule enters only as the DEFINITION of the stationary and pushed-forward
  laws by their variances (`statVar`, `pushVar`), as in R0 and RSP (fixed point: `statVar_fixed`).
* r_ord_reversed: the six hypotheses stated in its docstring (the landed Langevin certificate `thm:stochastic-word` (a),
  the W2-Lipschitz constants of the letters, the Gibbs displacement of D, the noise displacement); each is a landed or
  classical statement. The metric space `M` of laws is abstract.

COVERAGE (dossier item — Lean name):
* r-ord-coincide, all FORMALISED (statement + proof, no sorry):
  (i) `sqrt_statVar` (τ_ω = τ_T · C_ω √(2/E)), `flr_eq` (floor = τ_T |C_ω √(2/E) − 1|), `exact_iff_Cw` (exact iff 2C² = E);
  (ii) `flr_eq_iff` (distinct standard deviations: equal floors iff (C₁ + C₂)² = 2E; T does not occur);
  (iii) `Cw_eq_poly` (the polynomials), `coincPoly_zero_iff_Ioc` (holds for every η ∈ (0, 1] iff s = 1 and the pair is in
  {dpn, pdn} × {ndp, npd}; also over all real η: `coincPoly_zero_iff`), `coincide_finite` (any other pair of distinct
  orders, s ≥ 0: at most 4 roots in (0, 1]), `floors_coincide_finite` (THE dossier's count: the set of η = hκ ∈ (0, 1] at which
  the laws differ and the floors coincide has at most 4 points, fixed κ, T > 0, sg = s κ; points where the laws are equal are
  not counted, as in the repaired text; "laws differ" is stated as the standard deviations differing), `slice_identity` (sg = κ: for the four pairs the laws differ and
  the floors are equal for every admissible h and T);
  (iv) `law_coincide_iff` (the exact list of coincidences of laws, `LawCond`: dpn = pdn, ndp = npd always; sg = 0: dnp with
  dpn, pdn and pnd with ndp, npd; h = (sg − κ)/(κ sg) with sg > κ: dnp with pnd; h κ = 1: pnd, ndp, npd);
  (v) `disp_formula` (disp_ω(π_T) = |√(ρ²τ_T² + c²2Th) − τ_T|), `order_pushVar`, `order_displacements` (instance
  (κ, sg, T, h) = (1, 1/2, 1, 1/4): the six displacements take four distinct values; exact images of the Gibbs variance
  56/81, 43/54, 14/27, 499/864). The decimal values 0.014983, ... are not stated (the exact algebraic forms are).
* r-ord-rotation, FORMALISED in abstract form (the dossier's remark that a word with no Lipschitz letter has λ = 1, the empty
  product, is a convention of the word package (H-W); the abstract `rotation_w2_bound` takes an arbitrary λ and needs no
  λ < 1, so it covers that case and the remark is not a separate Lean statement): (i) `rotation_invariant` (kernels on a measurable space, `Measure.comp_assoc`),
  `rotation_eq` (with the unique-invariant-law hypothesis supplied by lem:r0-product), `rotation_map` (deterministic maps and
  `Measure.map`); (ii) `rotation_w2_bound` (abstract metric space); (iii) `rotation_cyclic` (rotation of a word given as a list of
  letter kernels, `wordK`). The law-level instances (Gaussian orbits, the remark on orbits) are NOT formalised.
* r-ord-undetermined, FORMALISED relative to `hW` and to the spectrum model: (i) `fND_eq`, `fDN_eq`, `diag_reduction`;
  (ii) `ranking_le` (h L ≤ √5 − 1 gives f_ND ≤ f_DN for every spectrum in [m, L], every d), `ranking_eq_iff` (d ≥ 1: equality iff H = L I and h L = √5 − 1);
  (iii) `ranking_opposite` (h L > √5 − 1: f_ND < f_DN at H = m I and f_ND > f_DN at H = L I), `sign_fixed_iff` (the five numbers fix the
  sign weakly iff h L ≤ √5 − 1), `top_step_iff`, `exists_step_iff` (an admissible h with h L > √5 − 1 exists iff L/m > φ = (1 + √5)/2),
  `thr_iff` (interval form); (iv)(a) `instance_a` (d = 2, diag(1, 3), h = 1/2: f_ND² = T(8/3 − 4/√3), f_DN² = T(1 − 1/√3)², f_ND > f_DN;
  and H = I₂ with the same five numbers has f_ND < f_DN), (b) `instance_b` (d = 3, diag(1, 2, 2), h = 2/3: difference of squares
  T(4 − 4√3/3 − 2√6/3) > 0), (c) `multiplicity_iff` (h = 2/(m+L), spectrum {m, L × k}: some k gives f_ND > f_DN iff L/m > φ; for L/m ≤ φ none, by
  `ranking_le`), `least_k_L2` (m = 1, L = 2: k = 0, 1 give f_ND ≤ f_DN; k = 2 is `instance_b`); (v) `attained_sign_d2` (d = 2, pair (1, 3) attained,
  h = 1/2: the sign is determined, f_ND > f_DN), `instance_c` (the {1,1,2} contrast at (m, L, h, d) = (1, 2, 2/3, 3): pair attained,
  f_ND² − f_DN² = T (2 d_m + d_L) = T (4 − 4√6/3 − 2√3/3) < 0, so f_ND < f_DN, opposite to `instance_b`; the decimals −0.4207,
  −0.2997, 0.1786 are not stated). The hypotheses of the repaired proposition are met: m > 0 and 0 < m ≤ L (`Adm`), T > 0
  (`hT`), H symmetric (as its real spectrum `μ`, see below), d ≥ 1 where an equality or strict sign is claimed (`hd`).
  NOT formalised: (vi) the numerical root r* (the repaired (vi) is a witness-checked remark); the least k for L = 1.8, 1.7, 1.62 (numerical witness values);
  the reduction of a symmetric matrix H to its spectrum (rotation to an eigenbasis and orthogonal invariance of W2): records are
  taken as spectra, i.e. the statements hold for "every record up to rotation".
* r-ord-row FORMALISED (a dossier tool with no consumer in the unit; the finite-K use remark was cut from the dossier, the lemma
  itself kept): `row_recursion` (e_{k+1} ≤ λ e_k + δ, 0 ≤ λ < 1 gives e_K ≤ λ^K e_0 + (1 − λ^K)/(1 − λ) δ), `r_ord_row`
  (the metric-space form with δ = dist (Q y) y, and the weaker term δ/(1 − λ)).
* r-ord-reversed (e) (HYPOTHESES THE DOSSIER MUST ADD, found at the 2026-10-30 drift check: `r_ord_reversed` takes `hNlip` (the noise
  letter is nonexpansive in W2), used ONLY for the uniqueness clause of (i) (the unique-fixed-point step, the landed `lem:r0-product`
  mechanism: the contraction factor of D ∘ N is q times the Lipschitz constant 1 of N). The dossier's corollary statement lists no
  such hypothesis. The dossier's tier line also names only three hypotheses (floor(N∘D) ≤ bias, D q-Lipschitz, Gibbs displacement);
  the Lean takes the K-step certificate `hcert` in place of the floor bound alone, `hnoise` (W2(ν Q_N, ν) ≤ √(2Thd), proof step 4
  of the dossier) and `hND` (π_ND is invariant for N ∘ D) as well): `reversed_iterate` (nu Q'^K = ((nu Q_N) Q_{N∘D}^{K−1}) Q_D), `r_ord_reversed` — (i) π' = A_D π_ND is the unique invariant
  law of D ∘ N; (ii) floor(N∘D) ≤ bias and floor(D∘N) ≤ q bias + h L √(T d/m); (iii) the K-step clause for K ≥ 1 — all proved from the
  six named hypotheses on an abstract metric space of laws; the instantiation at (P_2(ℝ^d), W2) and clause (iv) are NOT formalised.
* NOT formalised (PROSE-ONLY in the dossier): r-ord-consistency, r-ord-two, the table r-ord-refuse, the section-10 notes.

Status tier: FORMALISED (statement + proof, no sorry) for r-ord-coincide, r-ord-rotation (abstract), r-ord-undetermined
(relative to `hW`, spectrum model, r* excluded), r-ord-row; STATEMENT-FORMALISED in the dossier's sense for r-ord-reversed (proof of the
conclusions from the named hypotheses is complete, no sorry). STATUS: COMPLETE.
-/
import Mathlib
import OcfVerification.R0StackingLimits
import OcfVerification.RSPProximalLangevin

open OCF.RSP OCF.R0

namespace OCF.RORD

/-! ## Part A: the coincidence criterion (r-ord-coincide) -/

/-- `C_ω := c_ω (1 + h sg)`. -/
noncomputable def Cw (κ sg h : ℝ) (ω : Ord6) : ℝ := cOf κ sg h ω * (1 + h * sg)

/-- `E := 2 + h (sg − κ)`. -/
noncomputable def Ew (κ sg h : ℝ) : ℝ := 2 + h * (sg - κ)

lemma one_add_pos {κ sg h T : ℝ} (H : InClass κ sg h T) : 0 < 1 + h * sg := by
  have := H.hh; have := H.hsg; positivity

lemma cOf_nonneg {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) : 0 ≤ cOf κ sg h ω := by
  have hA := one_add_pos H
  have h1 : 0 ≤ 1 - h * κ := by nlinarith [H.hhκ]
  cases ω <;> simp only [cOf, rho]
  · positivity
  · exact zero_le_one
  · apply div_nonneg <;> nlinarith
  · apply div_nonneg <;> nlinarith
  · exact zero_le_one
  · exact h1

lemma Cw_nonneg {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) : 0 ≤ Cw κ sg h ω :=
  mul_nonneg (cOf_nonneg H ω) (one_add_pos H).le

lemma Ew_pos {κ sg h T : ℝ} (H : InClass κ sg h T) : 0 < Ew κ sg h := by
  have := H.hhκ; have := H.hh; have := H.hsg; unfold Ew; nlinarith

lemma statVar_eq {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) :
    statVar T h κ sg ω = gibbsVar T κ sg * (2 * Cw κ sg h ω ^ 2 / Ew κ sg h) := by
  have hA := one_add_pos H
  have hks : 0 < κ + sg := by have := H.hκ; have := H.hsg; linarith
  have hW := Ew_pos H
  have hh0 : h ≠ 0 := H.hh.ne'
  have hW' : 2 + h * (sg - κ) ≠ 0 := hW.ne'
  unfold statVar gibbsVar Cw Ew
  rw [one_sub_rho_sq hA.ne']
  field_simp


section floors
variable {Law : Type*} (gauss : ℝ → Law) (W2 : Law → Law → ℝ)

/-- The floor `W2(π_ω, π_T)` of order `ω`: the stationary law of `ω` is `N(0, statVar)` and the
target is `N(0, gibbsVar)` (laws DEFINED by their variances, as in R0 `r0_order`). -/
noncomputable def flr (T h κ sg : ℝ) (ω : Ord6) : ℝ :=
  W2 (gauss (Real.sqrt (statVar T h κ sg ω))) (gauss (Real.sqrt (gibbsVar T κ sg)))

lemma gibbsVar_pos {κ sg h T : ℝ} (H : InClass κ sg h T) : 0 < gibbsVar T κ sg := by
  have := H.hκ; have := H.hsg; have := H.hT; unfold gibbsVar; positivity

/-- (i), standard deviations: `τ_ω = τ_T · C_ω √(2/E)`. -/
theorem sqrt_statVar {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) :
    Real.sqrt (statVar T h κ sg ω) =
      Real.sqrt (gibbsVar T κ sg) * (Cw κ sg h ω * Real.sqrt (2 / Ew κ sg h)) := by
  have hC := Cw_nonneg H ω
  have hE := Ew_pos H
  rw [statVar_eq H ω, Real.sqrt_mul (gibbsVar_pos H).le,
    show 2 * Cw κ sg h ω ^ 2 / Ew κ sg h = Cw κ sg h ω ^ 2 * (2 / Ew κ sg h) by ring,
    Real.sqrt_mul (by positivity), Real.sqrt_sq hC]

/-- (i), floor: `floor_ω = τ_T |C_ω √(2/E) − 1|`. -/
theorem flr_eq (hW2 : W2Gaussian gauss W2) {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) :
    flr gauss W2 T h κ sg ω =
      Real.sqrt (gibbsVar T κ sg) * |Cw κ sg h ω * Real.sqrt (2 / Ew κ sg h) - 1| := by
  have hτ : 0 < Real.sqrt (gibbsVar T κ sg) := Real.sqrt_pos.2 (gibbsVar_pos H)
  unfold flr
  rw [hW2 _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), sqrt_statVar H ω,
    show Real.sqrt (gibbsVar T κ sg) * (Cw κ sg h ω * Real.sqrt (2 / Ew κ sg h)) -
      Real.sqrt (gibbsVar T κ sg) =
      Real.sqrt (gibbsVar T κ sg) * (Cw κ sg h ω * Real.sqrt (2 / Ew κ sg h) - 1) by ring,
    abs_mul, abs_of_pos hτ]

/-- (i), exactness: `v_ω = v_T` iff `2 C_ω² = E` (the landed `exact_iff`, in the `C_ω`, `E` form). -/
theorem exact_iff_Cw {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) :
    statVar T h κ sg ω = gibbsVar T κ sg ↔ 2 * Cw κ sg h ω ^ 2 = Ew κ sg h := by
  have hE := Ew_pos H
  have hg := (gibbsVar_pos H).ne'
  rw [statVar_eq H ω]
  constructor
  · intro e
    have e1 := mul_left_cancel₀ hg (e.trans (mul_one _).symm)
    rwa [div_eq_one_iff_eq hE.ne'] at e1
  · intro e; rw [e, div_self hE.ne', mul_one]

/-- (ii): for two orders with different standard deviations, equal floors iff `(C₁ + C₂)² = 2E`.
`T` does not occur. -/
theorem flr_eq_iff (hW2 : W2Gaussian gauss W2) {κ sg h T : ℝ} (H : InClass κ sg h T)
    {ω₁ ω₂ : Ord6}
    (hne : Real.sqrt (statVar T h κ sg ω₁) ≠ Real.sqrt (statVar T h κ sg ω₂)) :
    flr gauss W2 T h κ sg ω₁ = flr gauss W2 T h κ sg ω₂ ↔
      (Cw κ sg h ω₁ + Cw κ sg h ω₂) ^ 2 = 2 * Ew κ sg h := by
  have hτ : 0 < Real.sqrt (gibbsVar T κ sg) := Real.sqrt_pos.2 (gibbsVar_pos H)
  have hE := Ew_pos H
  have hC1 := Cw_nonneg H ω₁
  have hC2 := Cw_nonneg H ω₂
  set r := Real.sqrt (2 / Ew κ sg h) with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 2 / Ew κ sg h := Real.sq_sqrt (by positivity)
  set x := Cw κ sg h ω₁ * r
  set y := Cw κ sg h ω₂ * r
  have hxy : x ≠ y := by
    intro e
    apply hne
    rw [sqrt_statVar H ω₁, sqrt_statVar H ω₂]
    exact congrArg _ e
  rw [flr_eq gauss W2 hW2 H, flr_eq gauss W2 hW2 H, mul_right_inj' hτ.ne']
  have key : |x - 1| = |y - 1| ↔ x + y = 2 := by
    constructor
    · intro e
      rcases abs_eq_abs.1 e with e | e
      · exact absurd (by linarith) hxy
      · linarith
    · intro e; rw [abs_eq_abs]; right; linarith
  rw [key]
  have hsum : x + y = (Cw κ sg h ω₁ + Cw κ sg h ω₂) * r := by ring
  rw [hsum]
  constructor
  · intro e
    have e2 : ((Cw κ sg h ω₁ + Cw κ sg h ω₂) * r) ^ 2 = 4 := by rw [e]; norm_num
    rw [mul_pow, hr2] at e2
    field_simp at e2
    linarith
  · intro e
    have e2 : ((Cw κ sg h ω₁ + Cw κ sg h ω₂) * r) ^ 2 = 2 ^ 2 := by
      rw [mul_pow, hr2, e]; field_simp
    exact (pow_left_inj₀ (by positivity) (by norm_num) (by norm_num)).1 e2

end floors

/-! ### The polynomial form (iii) and the slice identity -/

/-- The pairs `{dpn, pdn} × {ndp, npd}` (either order). -/
def slicePair (ω₁ ω₂ : Ord6) : Prop :=
  ((ω₁ = .DPN ∨ ω₁ = .PDN) ∧ (ω₂ = .NDP ∨ ω₂ = .NPD)) ∨
  ((ω₂ = .DPN ∨ ω₂ = .PDN) ∧ (ω₁ = .NDP ∨ ω₁ = .NPD))

/-- `C_ω` as a polynomial in `η = h κ` at slope `s = sg/κ`:
`1 + sη` (dpn, pdn), `1` (dnp), `(1 − η)(1 + sη)` (pnd), `1 − η` (ndp, npd). -/
def Cpoly (s η : ℝ) : Ord6 → ℝ
  | .DPN => 1 + s * η
  | .PDN => 1 + s * η
  | .DNP => 1
  | .PND => (1 - η) * (1 + s * η)
  | .NDP => 1 - η
  | .NPD => 1 - η

/-- `E = 2 + (s − 1) η`. -/
def Epoly (s η : ℝ) : ℝ := 2 + (s - 1) * η

/-- The criterion polynomial `(C₁ + C₂)² − 2E`. -/
def coincPoly (s η : ℝ) (ω₁ ω₂ : Ord6) : ℝ := (Cpoly s η ω₁ + Cpoly s η ω₂) ^ 2 - 2 * Epoly s η

theorem Cw_eq_poly {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) :
    Cw κ sg h ω = Cpoly (sg / κ) (h * κ) ω ∧ Ew κ sg h = Epoly (sg / κ) (h * κ) := by
  have hA := (one_add_pos H).ne'
  have hκ := H.hκ.ne'
  constructor
  · cases ω <;> simp only [Cw, cOf, rho, Cpoly] <;> field_simp
  · unfold Ew Epoly; field_simp

theorem coincPoly_zero_iff {s : ℝ} (hs : 0 ≤ s) {ω₁ ω₂ : Ord6} (hne : ω₁ ≠ ω₂) :
    (∀ η, coincPoly s η ω₁ ω₂ = 0) ↔ s = 1 ∧ slicePair ω₁ ω₂ := by
  constructor
  · intro H
    have h1 := H 1
    have h2 := H 2
    have h3 := H 3
    cases ω₁ <;> cases ω₂ <;> simp only [coincPoly, Cpoly, Epoly, slicePair] at h1 h2 h3 ⊢ <;>
      first
      | exact absurd rfl hne
      | (exfalso; nlinarith)
      | (refine ⟨by nlinarith, by simp⟩)
  · rintro ⟨rfl, hp⟩ η
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;>
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;>
      simp only [coincPoly, Cpoly, Epoly] <;> ring

open Polynomial in
/-- `C_ω` as an element of `ℝ[X]` (variable `η`). -/
noncomputable def CpolyP (s : ℝ) : Ord6 → ℝ[X]
  | .DPN => 1 + C s * X
  | .PDN => 1 + C s * X
  | .DNP => 1
  | .PND => (1 - X) * (1 + C s * X)
  | .NDP => 1 - X
  | .NPD => 1 - X

open Polynomial in
noncomputable def coincPolyP (s : ℝ) (ω₁ ω₂ : Ord6) : ℝ[X] :=
  (CpolyP s ω₁ + CpolyP s ω₂) ^ 2 - 2 * (2 + C (s - 1) * X)

open Polynomial in
lemma eval_coincPolyP (s η : ℝ) (ω₁ ω₂ : Ord6) :
    (coincPolyP s ω₁ ω₂).eval η = coincPoly s η ω₁ ω₂ := by
  have : ∀ ω, (CpolyP s ω).eval η = Cpoly s η ω := by
    intro ω; cases ω <;> simp [CpolyP, Cpoly]
  simp [coincPolyP, coincPoly, Epoly, this]

open Polynomial in
lemma natDegree_CpolyP_le (s : ℝ) (ω : Ord6) : (CpolyP s ω).natDegree ≤ 2 := by
  cases ω <;> simp only [CpolyP] <;> compute_degree <;> norm_num

open Polynomial in
lemma natDegree_coincPolyP_le (s : ℝ) (ω₁ ω₂ : Ord6) : (coincPolyP s ω₁ ω₂).natDegree ≤ 4 := by
  unfold coincPolyP
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · refine (natDegree_pow_le).trans ?_
    have := (natDegree_add_le (CpolyP s ω₁) (CpolyP s ω₂)).trans
      (max_le (natDegree_CpolyP_le s ω₁) (natDegree_CpolyP_le s ω₂))
    omega
  · (compute_degree; norm_num)

/-- (iii), first half, exactly as in the dossier: the criterion holds for every step `η ∈ (0, 1]`
iff `s = 1` and the pair is one of `{dpn, pdn} × {ndp, npd}`. -/
theorem coincPoly_zero_iff_Ioc {s : ℝ} (hs : 0 ≤ s) {ω₁ ω₂ : Ord6} (hne : ω₁ ≠ ω₂) :
    (∀ η, 0 < η → η ≤ 1 → coincPoly s η ω₁ ω₂ = 0) ↔ s = 1 ∧ slicePair ω₁ ω₂ := by
  rw [← coincPoly_zero_iff hs hne]
  constructor
  · intro H
    have hP : coincPolyP s ω₁ ω₂ = 0 := by
      apply Polynomial.eq_zero_of_infinite_isRoot
      apply Set.Infinite.mono _ (Set.Ioc_infinite (zero_lt_one' ℝ))
      intro η hη
      simp only [Set.mem_setOf_eq, Polynomial.IsRoot.def, eval_coincPolyP]
      exact H η hη.1 hη.2
    intro η
    rw [← eval_coincPolyP, hP]; simp
  · intro H η _ _; exact H η

/-- (iii), second half: off the exceptional slice the criterion polynomial is a nonzero polynomial
of degree at most 4, so it has at most 4 roots in `(0, 1]`. -/
theorem coincide_finite {s : ℝ} (hs : 0 ≤ s) {ω₁ ω₂ : Ord6} (hne : ω₁ ≠ ω₂)
    (hnot : ¬ (s = 1 ∧ slicePair ω₁ ω₂)) :
    {η : ℝ | 0 < η ∧ η ≤ 1 ∧ coincPoly s η ω₁ ω₂ = 0}.Finite ∧
      {η : ℝ | 0 < η ∧ η ≤ 1 ∧ coincPoly s η ω₁ ω₂ = 0}.ncard ≤ 4 := by
  classical
  have hP : coincPolyP s ω₁ ω₂ ≠ 0 := by
    intro h0
    apply hnot
    apply (coincPoly_zero_iff hs hne).1
    intro η
    rw [← eval_coincPolyP, h0]; simp
  have hsub : {η : ℝ | 0 < η ∧ η ≤ 1 ∧ coincPoly s η ω₁ ω₂ = 0} ⊆
      ↑(coincPolyP s ω₁ ω₂).roots.toFinset := by
    rintro η ⟨_, _, h⟩
    simp only [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hP,
      Polynomial.IsRoot.def, eval_coincPolyP]
    exact h
  have hfin : {η : ℝ | 0 < η ∧ η ≤ 1 ∧ coincPoly s η ω₁ ω₂ = 0}.Finite :=
    (Finset.finite_toSet _).subset hsub
  refine ⟨hfin, ?_⟩
  calc _ ≤ (↑(coincPolyP s ω₁ ω₂).roots.toFinset : Set ℝ).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = (coincPolyP s ω₁ ω₂).roots.toFinset.card := Set.ncard_coe_finset _
    _ ≤ Multiset.card (coincPolyP s ω₁ ω₂).roots := Multiset.toFinset_card_le _
    _ ≤ (coincPolyP s ω₁ ω₂).natDegree := Polynomial.card_roots' _
    _ ≤ 4 := natDegree_coincPolyP_le s ω₁ ω₂

/-- The slice identity (iii): on `sg = κ`, for the four pairs `{dpn, pdn} × {ndp, npd}` the laws
differ and the floors are equal, for every admissible step and every temperature. -/
theorem slice_identity (hW2 : W2Gaussian gauss W2) {κ h T : ℝ} (H : InClass κ κ h T)
    {ω₁ ω₂ : Ord6} (hp : slicePair ω₁ ω₂) :
    Real.sqrt (statVar T h κ κ ω₁) ≠ Real.sqrt (statVar T h κ κ ω₂) ∧
      flr gauss W2 T h κ κ ω₁ = flr gauss W2 T h κ κ ω₂ := by
  have hκ := H.hκ; have hh := H.hh
  have key : ∀ a b : Ord6, ((a = .DPN ∨ a = .PDN) ∧ (b = .NDP ∨ b = .NPD)) →
      Cw κ κ h a = 1 + h * κ ∧ Cw κ κ h b = 1 - h * κ := by
    intro a b ⟨ha, hb⟩
    have hA : 1 + h * κ ≠ 0 := (one_add_pos H).ne'
    refine ⟨?_, ?_⟩
    · rcases ha with rfl | rfl <;> simp [Cw, cOf]
    · rcases hb with rfl | rfl <;> simp [Cw, cOf, rho] <;> field_simp
  have main : ∀ a b : Ord6, ((a = .DPN ∨ a = .PDN) ∧ (b = .NDP ∨ b = .NPD)) →
      Real.sqrt (statVar T h κ κ a) ≠ Real.sqrt (statVar T h κ κ b) ∧
      flr gauss W2 T h κ κ a = flr gauss W2 T h κ κ b := by
    intro a b hab
    obtain ⟨ha, hb⟩ := key a b hab
    have hE : Ew κ κ h = 2 := by unfold Ew; ring
    have hne : Real.sqrt (statVar T h κ κ a) ≠ Real.sqrt (statVar T h κ κ b) := by
      rw [sqrt_statVar H a, sqrt_statVar H b, ha, hb, hE]
      have hτ := Real.sqrt_pos.2 (gibbsVar_pos H)
      intro e
      have e1 := mul_left_cancel₀ hτ.ne' e
      have hr : 0 < Real.sqrt (2 / 2 : ℝ) := by norm_num
      have e2 := mul_right_cancel₀ hr.ne' e1
      nlinarith
    refine ⟨hne, (flr_eq_iff gauss W2 hW2 H hne).2 ?_⟩
    rw [ha, hb, hE]; ring
  rcases hp with hp | hp
  · exact main _ _ hp
  · obtain ⟨h1, h2⟩ := main _ _ hp
    exact ⟨h1.symm, h2.symm⟩

/-- (iii) for floors: for fixed `κ, T > 0`, slope `s ≥ 0` (so `sg = s κ`) and an off-slice pair of
different orders, the steps `η = h κ ∈ (0, 1]` at which the laws differ and the floors coincide
number at most 4. -/
theorem floors_coincide_finite (hW2 : W2Gaussian gauss W2) {κ T s : ℝ} (hκ : 0 < κ) (hT : 0 < T)
    (hs : 0 ≤ s) {ω₁ ω₂ : Ord6} (hne : ω₁ ≠ ω₂) (hnot : ¬ (s = 1 ∧ slicePair ω₁ ω₂)) :
    {η : ℝ | 0 < η ∧ η ≤ 1 ∧
      Real.sqrt (statVar T (η / κ) κ (s * κ) ω₁) ≠ Real.sqrt (statVar T (η / κ) κ (s * κ) ω₂) ∧
      flr gauss W2 T (η / κ) κ (s * κ) ω₁ = flr gauss W2 T (η / κ) κ (s * κ) ω₂}.Finite ∧
    {η : ℝ | 0 < η ∧ η ≤ 1 ∧
      Real.sqrt (statVar T (η / κ) κ (s * κ) ω₁) ≠ Real.sqrt (statVar T (η / κ) κ (s * κ) ω₂) ∧
      flr gauss W2 T (η / κ) κ (s * κ) ω₁ = flr gauss W2 T (η / κ) κ (s * κ) ω₂}.ncard ≤ 4 := by
  obtain ⟨hf, hc⟩ := coincide_finite hs hne hnot
  have hsub : {η : ℝ | 0 < η ∧ η ≤ 1 ∧
      Real.sqrt (statVar T (η / κ) κ (s * κ) ω₁) ≠ Real.sqrt (statVar T (η / κ) κ (s * κ) ω₂) ∧
      flr gauss W2 T (η / κ) κ (s * κ) ω₁ = flr gauss W2 T (η / κ) κ (s * κ) ω₂} ⊆
      {η : ℝ | 0 < η ∧ η ≤ 1 ∧ coincPoly s η ω₁ ω₂ = 0} := by
    rintro η ⟨h0, h1, hne', heq⟩
    refine ⟨h0, h1, ?_⟩
    have H : InClass κ (s * κ) (η / κ) T :=
      ⟨hκ, by positivity, by rw [div_mul_cancel₀ _ hκ.ne']; exact h1, by positivity, hT⟩
    have e := (flr_eq_iff gauss W2 hW2 H hne').1 heq
    have p1 := Cw_eq_poly H ω₁
    have p2 := Cw_eq_poly H ω₂
    have hη : η / κ * κ = η := div_mul_cancel₀ _ hκ.ne'
    have hsκ : s * κ / κ = s := mul_div_cancel_right₀ _ hκ.ne'
    rw [p1.1, p2.1, p1.2, hη, hsκ] at e
    unfold coincPoly
    linarith [e]
  exact ⟨hf.subset hsub, (Set.ncard_le_ncard hsub hf).trans hc⟩

/-! ### (iv): exactly when two orders have the same law -/

/-- The exact list of coincidences of laws (dossier (iv)): dpn = pdn and ndp = npd always; at
`sg = 0` also dnp with dpn, pdn and pnd with ndp, npd; at `h = (sg − κ)/(κ sg)` (needs `sg > κ`)
dnp with pnd; at `h κ = 1` pnd, ndp, npd (the Dirac mass at 0). A pair of equal orders is
trivially a coincidence. -/
def LawCond (κ sg h : ℝ) : Ord6 → Ord6 → Prop
  | .DNP, .DNP => True
  | .DPN, .DPN => True
  | .NDP, .NDP => True
  | .NPD, .NPD => True
  | .PDN, .PDN => True
  | .PND, .PND => True
  | .DPN, .PDN => True
  | .PDN, .DPN => True
  | .NDP, .NPD => True
  | .NPD, .NDP => True
  | .DNP, .DPN => sg = 0
  | .DPN, .DNP => sg = 0
  | .DNP, .PDN => sg = 0
  | .PDN, .DNP => sg = 0
  | .PND, .NDP => sg = 0 ∨ h * κ = 1
  | .NDP, .PND => sg = 0 ∨ h * κ = 1
  | .PND, .NPD => sg = 0 ∨ h * κ = 1
  | .NPD, .PND => sg = 0 ∨ h * κ = 1
  | .DNP, .PND => κ < sg ∧ h = (sg - κ) / (κ * sg)
  | .PND, .DNP => κ < sg ∧ h = (sg - κ) / (κ * sg)
  | _, _ => False

lemma statVar_eq_iff_cOf {κ sg h T : ℝ} (H : InClass κ sg h T) (ω₁ ω₂ : Ord6) :
    statVar T h κ sg ω₁ = statVar T h κ sg ω₂ ↔ cOf κ sg h ω₁ = cOf κ sg h ω₂ := by
  have hρ := H.rho_sq_lt
  have hpos : 0 < 2 * T * h / (1 - rho κ h sg ^ 2) := by
    have := H.hT; have := H.hh
    exact div_pos (by positivity) (by linarith)
  have e : ∀ ω, statVar T h κ sg ω = cOf κ sg h ω ^ 2 * (2 * T * h / (1 - rho κ h sg ^ 2)) := by
    intro ω; unfold statVar; ring
  rw [e ω₁, e ω₂]
  constructor
  · intro h1
    have h2 := mul_right_cancel₀ hpos.ne' h1
    exact (pow_left_inj₀ (cOf_nonneg H ω₁) (cOf_nonneg H ω₂) (by norm_num)).1 h2
  · intro h1; rw [h1]

/-- (iv): the laws of two orders coincide exactly in the listed cases. -/
theorem law_coincide_iff {κ sg h T : ℝ} (H : InClass κ sg h T) (ω₁ ω₂ : Ord6) :
    statVar T h κ sg ω₁ = statVar T h κ sg ω₂ ↔ LawCond κ sg h ω₁ ω₂ := by
  rw [statVar_eq_iff_cOf H]
  have hκ := H.hκ; have hh := H.hh; have hk1 := H.hhκ; have hsg := H.hsg
  have hA : 0 < 1 + h * sg := one_add_pos H
  have hhk : 0 < h * κ := mul_pos hh hκ
  have hρ1 : rho κ h sg < 1 := by
    have := (r_sp_factor_arith (m := κ) (L := κ) hκ le_rfl hh (by
      rw [le_div_iff₀ (by linarith)]; nlinarith) hsg)
    exact this.2.1
  -- the basic comparisons
  have u1 : 1 / (1 + h * sg) = 1 ↔ sg = 0 := by
    rw [div_eq_one_iff_eq hA.ne']
    constructor
    · intro e
      have : h * sg = 0 := by linarith
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 hh.ne'
      · exact h0
    · intro e; rw [e]; ring
  have ua : 1 / (1 + h * sg) = 1 - h * κ ↔ κ < sg ∧ h = (sg - κ) / (κ * sg) := by
    rw [div_eq_iff hA.ne']
    constructor
    · intro e
      have e1 : sg - κ = h * κ * sg := by
        have : h * (sg - κ - h * κ * sg) = 0 := by nlinarith
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 hh.ne'
        · linarith
      have hs0 : sg ≠ 0 := by
        intro e0; rw [e0] at e1; nlinarith
      have hsp : 0 < sg := lt_of_le_of_ne hsg (Ne.symm hs0)
      refine ⟨?_, ?_⟩
      · nlinarith
      · rw [eq_div_iff (by positivity)]; linarith
    · rintro ⟨hlt, e⟩
      have hs0 : 0 < sg := by linarith
      rw [e]; field_simp; ring
  have ar : 1 - h * κ = rho κ h sg ↔ sg = 0 ∨ h * κ = 1 := by
    unfold rho
    rw [eq_div_iff hA.ne']
    constructor
    · intro e
      have : (1 - h * κ) * (h * sg) = 0 := by linear_combination e
      rcases mul_eq_zero.1 this with h0 | h0
      · right; linarith
      · left
        rcases mul_eq_zero.1 h0 with h1 | h1
        · exact absurd h1 hh.ne'
        · exact h1
    · rintro (e | e)
      · rw [e]; ring
      · linear_combination (-(h * sg)) * e
  have n1 : (1 : ℝ) ≠ 1 - h * κ := by intro e; linarith
  have n2 : (1 : ℝ) ≠ rho κ h sg := by intro e; linarith
  have n3 : 1 / (1 + h * sg) ≠ rho κ h sg := by
    intro e
    unfold rho at e
    rw [div_left_inj' hA.ne'] at e
    linarith
  cases ω₁ <;> cases ω₂ <;> simp only [cOf, LawCond]
  all_goals first
    | exact Iff.rfl
    | exact iff_of_true rfl trivial
    | exact iff_of_false n1 not_false
    | exact iff_of_false n1.symm not_false
    | exact iff_of_false n2 not_false
    | exact iff_of_false n2.symm not_false
    | exact iff_of_false n3 not_false
    | exact iff_of_false n3.symm not_false
    | exact u1
    | exact eq_comm.trans u1
    | exact ua
    | exact eq_comm.trans ua
    | exact ar
    | exact eq_comm.trans ar

/-! ### (v): the displacement of the Gibbs law under one step -/

/-- The variance map of one application of order `ω` on `F = κ x²/2`, `g = sg x²/2`:
a centred Gaussian of variance `v` goes to one of variance `ρ² v + c_ω² 2 T h`
(`word_lin`: `x ↦ ρ x + c_ω z`, `z ~ N(0, 2 T h)`; the independent-sum rule for Gaussians is
CLASSICAL and enters, as in R0, by defining the image law through its variance). -/
noncomputable def pushVar (T h κ sg : ℝ) (ω : Ord6) (v : ℝ) : ℝ :=
  rho κ h sg ^ 2 * v + cOf κ sg h ω ^ 2 * (2 * T * h)

/-- `disp_ω(π_T) = W2(π_T Q_ω, π_T)`. -/
noncomputable def dispG {Law : Type*} (gauss : ℝ → Law) (W2 : Law → Law → ℝ)
    (T h κ sg : ℝ) (ω : Ord6) : ℝ :=
  W2 (gauss (Real.sqrt (pushVar T h κ sg ω (gibbsVar T κ sg)))) (gauss (Real.sqrt (gibbsVar T κ sg)))

theorem disp_formula {Law : Type*} (gauss : ℝ → Law) (W2 : Law → Law → ℝ)
    (hW2 : W2Gaussian gauss W2) (T h κ sg : ℝ) (ω : Ord6) :
    dispG gauss W2 T h κ sg ω =
      |Real.sqrt (rho κ h sg ^ 2 * gibbsVar T κ sg + cOf κ sg h ω ^ 2 * (2 * T * h)) -
        Real.sqrt (gibbsVar T κ sg)| := by
  unfold dispG pushVar
  exact hW2 _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

/-- If `a ≠ b` and `(4 t − a − b)² ≠ 4 a b` then `|√a − √t| ≠ |√b − √t|` (`a, b, t ≥ 0`). -/
lemma abs_sqrt_ne {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht : 0 ≤ t) (hab : a ≠ b)
    (hq : (4 * t - a - b) ^ 2 ≠ 4 * a * b) :
    |Real.sqrt a - Real.sqrt t| ≠ |Real.sqrt b - Real.sqrt t| := by
  intro e
  have hx := Real.sq_sqrt ha
  have hy := Real.sq_sqrt hb
  have hz := Real.sq_sqrt ht
  rcases abs_eq_abs.1 e with e | e
  · apply hab
    have : Real.sqrt a = Real.sqrt b := by linarith
    rw [← hx, ← hy, this]
  · apply hq
    have e2 : 2 * (Real.sqrt a * Real.sqrt b) = 4 * t - a - b := by
      have : (Real.sqrt a + Real.sqrt b) ^ 2 = (2 * Real.sqrt t) ^ 2 := by
        have : Real.sqrt a + Real.sqrt b = 2 * Real.sqrt t := by linarith
        rw [this]
      nlinarith
    have : (4 * t - a - b) ^ 2 = 4 * (Real.sqrt a * Real.sqrt b) ^ 2 := by rw [← e2]; ring
    rw [this, mul_pow, hx, hy]; ring

/-- The printed instance `(κ, sg, T, h) = (1, 1/2, 1, 1/4)` of `rem:r-sp-order`: the images of the Gibbs
variance `2/3` under the six orders are `56/81` (dnp), `43/54` (dpn, pdn), `14/27` (ndp, npd),
`499/864` (pnd). -/
theorem order_pushVar :
    pushVar 1 (1/4) 1 (1/2) .DNP (gibbsVar 1 1 (1/2)) = 56/81 ∧
    pushVar 1 (1/4) 1 (1/2) .DPN (gibbsVar 1 1 (1/2)) = 43/54 ∧
    pushVar 1 (1/4) 1 (1/2) .PDN (gibbsVar 1 1 (1/2)) = 43/54 ∧
    pushVar 1 (1/4) 1 (1/2) .NDP (gibbsVar 1 1 (1/2)) = 14/27 ∧
    pushVar 1 (1/4) 1 (1/2) .NPD (gibbsVar 1 1 (1/2)) = 14/27 ∧
    pushVar 1 (1/4) 1 (1/2) .PND (gibbsVar 1 1 (1/2)) = 499/864 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [pushVar, gibbsVar, cOf, rho]

/-- (v), the instance: the six displacements `|√v_ω − τ_T|` take exactly four distinct values
(dpn = pdn, ndp = npd). -/
theorem order_displacements {Law : Type*} (gauss : ℝ → Law) (W2 : Law → Law → ℝ)
    (hW2 : W2Gaussian gauss W2) :
    let D := dispG gauss W2 1 (1/4) 1 (1/2)
    D .DPN = D .PDN ∧ D .NDP = D .NPD ∧
    D .DNP ≠ D .DPN ∧ D .DNP ≠ D .NDP ∧ D .DNP ≠ D .PND ∧
    D .DPN ≠ D .NDP ∧ D .DPN ≠ D .PND ∧ D .NDP ≠ D .PND := by
  intro D
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := order_pushVar
  have hg : gibbsVar 1 1 (1/2) = 2/3 := by norm_num [gibbsVar]
  have f : ∀ ω, D ω = |Real.sqrt (pushVar 1 (1/4) 1 (1/2) ω (gibbsVar 1 1 (1/2))) -
      Real.sqrt (2/3)| := by
    intro ω
    show dispG gauss W2 1 (1/4) 1 (1/2) ω = _
    unfold dispG
    rw [hW2 _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), hg]
  have t : (0:ℝ) ≤ 2/3 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [f, f, a2, a3]
  · rw [f, f, a4, a5]
  · rw [f, f, a1, a2]; exact abs_sqrt_ne (by norm_num) (by norm_num) t (by norm_num) (by norm_num)
  · rw [f, f, a1, a4]; exact abs_sqrt_ne (by norm_num) (by norm_num) t (by norm_num) (by norm_num)
  · rw [f, f, a1, a6]; exact abs_sqrt_ne (by norm_num) (by norm_num) t (by norm_num) (by norm_num)
  · rw [f, f, a2, a4]; exact abs_sqrt_ne (by norm_num) (by norm_num) t (by norm_num) (by norm_num)
  · rw [f, f, a2, a6]; exact abs_sqrt_ne (by norm_num) (by norm_num) t (by norm_num) (by norm_num)
  · rw [f, f, a4, a6]; exact abs_sqrt_ne (by norm_num) (by norm_num) t (by norm_num) (by norm_num)

/-! ## Part B: the rotation identity (r-ord-rotation), abstract form -/

section rotation
open MeasureTheory ProbabilityTheory

variable {α : Type*} [MeasurableSpace α]

/-- r-ord-rotation (i), kernel form. A kernel `Q` acts on a law `ν` by `Q ∘ₘ ν` (= `ν Q`); the word
"U then V" has kernel `Q_V ∘ₖ Q_U`. If `π` is invariant for "U then V", then `π Q_U` is invariant
for "V then U". [ELEMENTARY: associativity of the action of kernels on laws, Pavliotis (2.16);
no locator held for the rotation itself.] -/
theorem rotation_invariant (QU QV : Kernel α α) {π : Measure α}
    (h : (QV ∘ₖ QU) ∘ₘ π = π) : (QU ∘ₖ QV) ∘ₘ (QU ∘ₘ π) = QU ∘ₘ π := by
  calc (QU ∘ₖ QV) ∘ₘ (QU ∘ₘ π) = QU ∘ₘ (QV ∘ₘ (QU ∘ₘ π)) := Measure.comp_assoc.symm
    _ = QU ∘ₘ ((QV ∘ₖ QU) ∘ₘ π) := congrArg (fun m => QU ∘ₘ m) Measure.comp_assoc
    _ = QU ∘ₘ π := by rw [h]

/-- r-ord-rotation (i), with the identification: if "V then U" has a unique invariant law `πVU`
(the landed `lem:r0-product` supplies uniqueness when the product bound is `< 1`), then
`πVU = π_UV Q_U`. -/
theorem rotation_eq (QU QV : Kernel α α) {π πVU : Measure α}
    (h : (QV ∘ₖ QU) ∘ₘ π = π) (huniq : ∀ ν : Measure α, (QU ∘ₖ QV) ∘ₘ ν = ν → ν = πVU) :
    πVU = QU ∘ₘ π :=
  (huniq _ (rotation_invariant QU QV h)).symm

/-- The kernel of a word given as a list of letter kernels, first letter applied first. -/
noncomputable def wordK : List (Kernel α α) → Kernel α α
  | [] => Kernel.id
  | k :: l => wordK l ∘ₖ k

lemma wordK_append (l₁ l₂ : List (Kernel α α)) : wordK (l₁ ++ l₂) = wordK l₂ ∘ₖ wordK l₁ := by
  induction l₁ with
  | nil => simp [wordK, Kernel.comp_id]
  | cons k l ih => simp [wordK, ih, Kernel.comp_assoc]

/-- r-ord-rotation (iii): for a word `w_1 ⋯ w_n` (a list of letter kernels) and `0 ≤ k ≤ n`
(here any `k`; `take`/`drop` saturate), the cyclically rotated word `w_{k+1} ⋯ w_n w_1 ⋯ w_k` has the
invariant law `π Q_{w_1 ⋯ w_k}` whenever `π` is invariant for `w_1 ⋯ w_n`. -/
theorem rotation_cyclic (l : List (Kernel α α)) (k : ℕ) {π : Measure α}
    (h : wordK l ∘ₘ π = π) :
    wordK (l.drop k ++ l.take k) ∘ₘ (wordK (l.take k) ∘ₘ π) = wordK (l.take k) ∘ₘ π := by
  have hl : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  rw [hl, wordK_append] at h
  rw [wordK_append]
  exact rotation_invariant _ _ h

/-- The same for deterministic maps and push-forward: if `π` is invariant under "f then g"
(`g ∘ f`), then `f_* π` is invariant under "g then f" (`f ∘ g`). -/
theorem rotation_map {f g : α → α} (hf : Measurable f) (hg : Measurable g) {π : Measure α}
    (h : π.map (g ∘ f) = π) : (π.map f).map (f ∘ g) = π.map f := by
  rw [Measure.map_map (hf.comp hg) hf, show (f ∘ g) ∘ f = f ∘ (g ∘ f) from rfl,
    ← Measure.map_map hf (hg.comp hf), h]

end rotation

/-- r-ord-rotation (ii), abstract metric form. `M` plays the role of `(P_2, W2)` (a metric space,
Bullo Thm 6.12), `A` the action of the word `U` on laws, `lam` its Lipschitz constant (the landed
`lem:r0-product`), `disp = dist (A θ) θ`. Then `dist (A p) θ ≤ lam · dist p θ + disp_U(θ)`; with
`p = π_UV` and `A p = π_VU` (rotation_invariant/rotation_eq) this is the dossier's (ii). -/
theorem rotation_w2_bound {M : Type*} [PseudoMetricSpace M] (A : M → M) {lam : ℝ}
    (hA : ∀ x y, dist (A x) (A y) ≤ lam * dist x y) (p θ : M) :
    dist (A p) θ ≤ lam * dist p θ + dist (A θ) θ :=
  (dist_triangle (A p) (A θ) θ).trans (by linarith [hA p θ])

/-! ## Part D: the finite-K clause (r-ord-row) -/

/-- The recursion `e_{k+1} ≤ λ e_k + δ` gives `e_K ≤ λ^K e_0 + (1 − λ^K)/(1 − λ) δ`
(`0 ≤ λ < 1`). -/
theorem row_recursion {e : ℕ → ℝ} {lam δ : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1)
    (hrec : ∀ k, e (k + 1) ≤ lam * e k + δ) (K : ℕ) :
    e K ≤ lam ^ K * e 0 + (1 - lam ^ K) / (1 - lam) * δ := by
  have h1 : 1 - lam ≠ 0 := by linarith
  induction K with
  | zero => simp
  | succ K ih =>
    have := hrec K
    have h2 : lam * e K ≤ lam * (lam ^ K * e 0 + (1 - lam ^ K) / (1 - lam) * δ) :=
      mul_le_mul_of_nonneg_left ih hlam
    have h3 : lam * (lam ^ K * e 0 + (1 - lam ^ K) / (1 - lam) * δ) + δ =
        lam ^ (K + 1) * e 0 + (1 - lam ^ (K + 1)) / (1 - lam) * δ := by
      field_simp; ring
    linarith

/-- r-ord-row: for a `lam`-Lipschitz action `Q` of the word `W` on the metric space `M` of laws,
`0 ≤ lam < 1`, a target `y` and a start `ν`, with `disp = dist (Q y) y`:
`dist (Q^K ν) y ≤ lam^K dist ν y + (1 − lam^K)/(1 − lam) disp ≤ lam^K dist ν y + disp/(1 − lam)`. -/
theorem r_ord_row {M : Type*} [PseudoMetricSpace M] (Q : M → M) {lam : ℝ} (hlam : 0 ≤ lam)
    (hlam1 : lam < 1) (hQ : ∀ x y, dist (Q x) (Q y) ≤ lam * dist x y) (ν y : M) (K : ℕ) :
    dist (Q^[K] ν) y ≤ lam ^ K * dist ν y + (1 - lam ^ K) / (1 - lam) * dist (Q y) y ∧
    lam ^ K * dist ν y + (1 - lam ^ K) / (1 - lam) * dist (Q y) y ≤
      lam ^ K * dist ν y + dist (Q y) y / (1 - lam) := by
  have hrec : ∀ k, dist (Q^[k + 1] ν) y ≤ lam * dist (Q^[k] ν) y + dist (Q y) y := by
    intro k
    rw [Function.iterate_succ_apply']
    exact (dist_triangle (Q (Q^[k] ν)) (Q y) y).trans (by linarith [hQ (Q^[k] ν) y])
  have hd := dist_nonneg (x := Q y) (y := y)
  have h1 : 0 < 1 - lam := by linarith
  refine ⟨row_recursion (e := fun k => dist (Q^[k] ν) y) hlam hlam1 hrec K, ?_⟩
  have hpk : 0 ≤ lam ^ K := pow_nonneg hlam K
  have : (1 - lam ^ K) / (1 - lam) * dist (Q y) y ≤ dist (Q y) y / (1 - lam) := by
    rw [div_mul_eq_mul_div]
    exact div_le_div_of_nonneg_right (by nlinarith) h1.le
  linarith

/-! ## Part E: the reversed word (r-ord-reversed), from named hypotheses -/

section reversed
variable {M : Type*} [MetricSpace M]

omit [MetricSpace M] in
/-- Step 4 of r-ord-reversed: `(D ∘ N)^{K+1} ν = D ((N ∘ D)^K (N ν))`, with `AD`, `AN` the actions of
the letters D and N on laws (composition notation: `AD ∘ AN` is "noise first, then gradient step"). -/
lemma reversed_iterate (AD AN : M → M) (ν : M) (K : ℕ) :
    (AD ∘ AN)^[K + 1] ν = AD ((AN ∘ AD)^[K] (AN ν)) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply' (AN ∘ AD)]
    rfl

/-- **Corollary r-ord-reversed**, in the form "named hypotheses give the conclusions".
`M` is `(P_2(ℝ^d), W2)` (a metric space, Bullo Thm 6.12; `MetricSpace` is used for uniqueness of the fixed point), `AD`, `AN` the actions of the gradient
step and the noise letter on laws, `πT` the Gibbs law, `πND` the invariant law of `N ∘ D`,
`π' = AD πND` the law of `D ∘ N` (rotation identity). Hypotheses (each a landed or classical
statement, not proved here):
* `hND`: `πND` is invariant for `N ∘ D`;
* `hcert`: `thm:stochastic-word` (a): `W2(ν Q_{N∘D}^K, π_T) ≤ q^K W2(ν, π_T) + bias(h)`, `q = 1 − m h`
  (`OCF.S1.bias T d m L h = 1.82 (L/m) √(T h d)`);
* `hDlip`: `D` is `q`-Lipschitz in W2 (`cl:r0-contraction` (c), Ryu–Yin Sec. 13.3 Prop. 2);
* `hNlip`: the noise letter is nonexpansive in W2 (same-`ξ` coupling);
* `hGibbs`: `W2(π_T Q_D, π_T) ≤ h L √(T d/m)` (coupling and `cl:gibbs-moment`);
* `hnoise`: `W2(ν Q_N, ν) ≤ √(2 T h d)` (the coupling `(X, X + √(2Th) ξ)`).
Conclusions: (i) `π'` is the (unique) invariant law of `D ∘ N`; (ii) the floor bound
`floor(D∘N) ≤ q bias(h) + h L √(T d/m)` (and `floor(N∘D) ≤ bias(h)`); (iii) the `K`-step clause.
NOT formalised: the law-level instantiation of the hypotheses and (iv). -/
theorem r_ord_reversed (AD AN : M → M) (πT πND : M) {m L h T : ℝ} {d : ℕ}
    (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hhL : h ≤ 2 / (m + L))
    (hND : AN (AD πND) = πND)
    (hcert : ∀ (ν : M) (K : ℕ),
      dist ((AN ∘ AD)^[K] ν) πT ≤ (1 - m * h) ^ K * dist ν πT + OCF.S1.bias T d m L h)
    (hDlip : ∀ x y, dist (AD x) (AD y) ≤ (1 - m * h) * dist x y)
    (hNlip : ∀ x y, dist (AN x) (AN y) ≤ dist x y)
    (hGibbs : dist (AD πT) πT ≤ h * L * Real.sqrt (T * d / m))
    (hnoise : ∀ ν, dist (AN ν) ν ≤ Real.sqrt (2 * T * h * d)) :
    (AD (AN (AD πND)) = AD πND ∧ ∀ x, AD (AN x) = x → x = AD πND) ∧
    dist πND πT ≤ OCF.S1.bias T d m L h ∧
    dist (AD πND) πT ≤ (1 - m * h) * dist πND πT + dist (AD πT) πT ∧
    dist (AD πND) πT ≤ (1 - m * h) * OCF.S1.bias T d m L h + h * L * Real.sqrt (T * d / m) ∧
    ∀ (ν : M) (K : ℕ), 1 ≤ K →
      dist ((AD ∘ AN)^[K] ν) πT ≤ (1 - m * h) ^ K * (dist ν πT + Real.sqrt (2 * T * h * d)) +
        (1 - m * h) * OCF.S1.bias T d m L h + h * L * Real.sqrt (T * d / m) := by
  have hs := step_mul_le hm hmL hhL
  have hq0 : 0 ≤ 1 - m * h := by nlinarith
  have hq1 : 1 - m * h < 1 := by nlinarith
  set q := 1 - m * h with hq
  set B := OCF.S1.bias T d m L h with hB
  set G := h * L * Real.sqrt (T * d / m) with hG
  -- (i)
  have hfix : AD (AN (AD πND)) = AD πND := congrArg AD hND
  have huniq : ∀ x, AD (AN x) = x → x = AD πND := by
    intro x hx
    have h1 : dist x (AD πND) ≤ q * dist x (AD πND) := by
      calc dist x (AD πND) = dist (AD (AN x)) (AD (AN (AD πND))) := by rw [hx, hfix]
        _ ≤ q * dist (AN x) (AN (AD πND)) := hDlip _ _
        _ ≤ q * dist x (AD πND) := mul_le_mul_of_nonneg_left (hNlip _ _) hq0
    have h2 : dist x (AD πND) ≤ 0 := by nlinarith [dist_nonneg (x := x) (y := AD πND)]
    exact dist_le_zero.1 h2
  -- floor of N ∘ D
  have hfl : dist πND πT ≤ B := by
    have hK : ∀ K : ℕ, dist πND πT ≤ q ^ K * dist πND πT + B := by
      intro K
      have := hcert πND K
      rwa [Function.iterate_fixed (f := AN ∘ AD) (x := πND) hND K] at this
    have hlim : Filter.Tendsto (fun K : ℕ => q ^ K * dist πND πT + B) Filter.atTop
        (nhds (0 * dist πND πT + B)) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _).add_const _
    rw [zero_mul, zero_add] at hlim
    exact ge_of_tendsto' hlim hK
  have hii : dist (AD πND) πT ≤ q * dist πND πT + dist (AD πT) πT := by
    have := rotation_w2_bound AD hDlip πND πT
    exact this
  refine ⟨⟨hfix, huniq⟩, hfl, hii, ?_, ?_⟩
  · calc dist (AD πND) πT ≤ q * dist πND πT + dist (AD πT) πT := hii
      _ ≤ q * B + G := by nlinarith
  · intro ν K hK
    obtain ⟨K', rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    rw [reversed_iterate AD AN ν K']
    set X := (AN ∘ AD)^[K'] (AN ν) with hX
    have h1 : dist (AD X) πT ≤ q * dist X πT + dist (AD πT) πT := rotation_w2_bound AD hDlip X πT
    have h2 : dist X πT ≤ q ^ K' * dist (AN ν) πT + B := hcert (AN ν) K'
    have h3 : dist (AN ν) πT ≤ dist ν πT + Real.sqrt (2 * T * h * d) := by
      calc dist (AN ν) πT ≤ dist (AN ν) ν + dist ν πT := dist_triangle _ _ _
        _ ≤ _ := by linarith [hnoise ν]
    have hpk : 0 ≤ q ^ K' := pow_nonneg hq0 K'
    have h4 : q ^ K' * dist (AN ν) πT ≤ q ^ K' * (dist ν πT + Real.sqrt (2 * T * h * d)) :=
      mul_le_mul_of_nonneg_left h3 hpk
    have h5 : q * dist X πT ≤ q * (q ^ K' * (dist ν πT + Real.sqrt (2 * T * h * d)) + B) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0
    calc dist (AD X) πT ≤ q * dist X πT + dist (AD πT) πT := h1
      _ ≤ q * (q ^ K' * (dist ν πT + Real.sqrt (2 * T * h * d)) + B) + G := by linarith
      _ = q ^ (K' + 1) * (dist ν πT + Real.sqrt (2 * T * h * d)) + q * B + G := by ring

end reversed

/-! ## Part C: the declared numbers do not rank the two orders (r-ord-undetermined) -/

section ranking

/-- Per-direction squared floors in units `T/μ` (eigenvalue `μ`, `η = h μ`, `w = uF η`):
`(T/μ)(w − 1)²` for `N ∘ D` and `(T/μ)(1 − |1 − η| w)²` for `D ∘ N`. -/
noncomputable def pND (T μ h : ℝ) : ℝ := T / μ * (uF (h * μ) - 1) ^ 2
noncomputable def pDN (T μ h : ℝ) : ℝ := T / μ * (1 - |1 - h * μ| * uF (h * μ)) ^ 2

lemma uF_gt_one {η : ℝ} (h0 : 0 < η) (h2 : η < 2) : 1 < uF η := by
  have hu := uF_pos h2
  have hu2 := uF_sq h2
  by_contra hcon
  push Not at hcon
  have h1 : uF η ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 2 - η)]

/-- Per direction, the three-way comparison at the threshold `η = √5 − 1`
(the squared form of `floors_key`). -/
lemma dir_cmp {η : ℝ} (h0 : 0 < η) (h2 : η < 2) :
    (η < Real.sqrt 5 - 1 → (uF η - 1) ^ 2 < (1 - |1 - η| * uF η) ^ 2) ∧
    (η = Real.sqrt 5 - 1 → (uF η - 1) ^ 2 = (1 - |1 - η| * uF η) ^ 2) ∧
    (Real.sqrt 5 - 1 < η → (1 - |1 - η| * uF η) ^ 2 < (uF η - 1) ^ 2) := by
  have hu := uF_pos h2
  have hu1 := uF_gt_one h0 h2
  obtain ⟨k1, k2, k3⟩ := floors_key h0 h2 hu (uF_sq h2)
  have e : (1 - |1 - η| * uF η) ^ 2 = |(|1 - η|) * uF η - 1| ^ 2 := by rw [sq_abs]; ring
  have ha : 0 ≤ uF η - 1 := by linarith
  rw [e]
  refine ⟨fun h => pow_lt_pow_left₀ (k1 h) ha (by norm_num), fun h => ?_,
    fun h => pow_lt_pow_left₀ (k3 h) (abs_nonneg _) (by norm_num)⟩
  rw [← k2 h]

variable {Law : Type*} {d : ℕ}

/-- The Gaussian `W2` formula for centred Gaussians with DIAGONAL covariances in the eigenbasis
(commuting covariances; HYPOTHESIS, [CLASSICAL] Bullo, Contraction Theory for Dynamical Systems v1.3,
Ex. 6.11 (iv), (6.44), p. 229, VERIFIED): `W2(N(0, diag a²), N(0, diag b²)) = ‖a − b‖₂` for
standard-deviation vectors `a, b ≥ 0` (`‖Σ₁^{1/2} − Σ₂^{1/2}‖_F`). `gaussD a` is the centred
Gaussian with covariance `diag(a_i²)`. -/
def W2GaussianDiag (gaussD : (Fin d → ℝ) → Law) (W2 : Law → Law → ℝ) : Prop :=
  ∀ a b : Fin d → ℝ, (∀ i, 0 ≤ a i) → (∀ i, 0 ≤ b i) →
    W2 (gaussD a) (gaussD b) = Real.sqrt (∑ i, (a i - b i) ^ 2)

/-- Non-vacuity: `Law = (Fin d → ℝ)` (a law is its standard-deviation vector), `gaussD = id`, `W2` the
Euclidean distance. -/
theorem w2GaussianDiag_model :
    W2GaussianDiag (d := d) (Law := Fin d → ℝ) id (fun a b => Real.sqrt (∑ i, (a i - b i) ^ 2)) :=
  fun _ _ _ _ => rfl

/-- The floors `f_ND = W2(π_{N∘D}, π_T)` and `f_DN = W2(π_{D∘N}, π_T)` of the record `F = ½ xᵀHx`
with spectrum `μ`, written in an eigenbasis of `H` (laws DEFINED by their variances, per direction the
stationary variances `statND`, `statDN` of R0; the target is `N(0, T H⁻¹)`). -/
noncomputable def fND (gaussD : (Fin d → ℝ) → Law) (W2 : Law → Law → ℝ) (T h : ℝ) (μ : Fin d → ℝ) : ℝ :=
  W2 (gaussD (fun i => Real.sqrt (statND T (μ i) h))) (gaussD (fun i => Real.sqrt (T / μ i)))
noncomputable def fDN (gaussD : (Fin d → ℝ) → Law) (W2 : Law → Law → ℝ) (T h : ℝ) (μ : Fin d → ℝ) : ℝ :=
  W2 (gaussD (fun i => Real.sqrt (statDN T (μ i) h))) (gaussD (fun i => Real.sqrt (T / μ i)))

variable {gaussD : (Fin d → ℝ) → Law} {W2 : Law → Law → ℝ}

lemma pND_nonneg {T μ h : ℝ} (hT : 0 < T) (hμ : 0 < μ) : 0 ≤ pND T μ h := by
  unfold pND; positivity

lemma pDN_nonneg {T μ h : ℝ} (hT : 0 < T) (hμ : 0 < μ) : 0 ≤ pDN T μ h := by
  unfold pDN; positivity

/-- `f_ND = √(Σ (T/μ_i)(w_i − 1)²)`, `f_DN = √(Σ (T/μ_i)(1 − |1 − η_i| w_i)²)`. -/
theorem fND_eq (hW : W2GaussianDiag gaussD W2) {T h : ℝ} (hT : 0 < T) {μ : Fin d → ℝ}
    (hμ : ∀ i, 0 < μ i) : fND gaussD W2 T h μ = Real.sqrt (∑ i, pND T (μ i) h) := by
  have hs : ∀ i, 0 ≤ Real.sqrt (T / μ i) := fun i => Real.sqrt_nonneg _
  have hs2 : ∀ i, Real.sqrt (T / μ i) ^ 2 = T / μ i := fun i =>
    Real.sq_sqrt (div_pos hT (hμ i)).le
  unfold fND
  rw [hW _ _ (fun i => Real.sqrt_nonneg _) hs]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sqrt_statND hT (hμ i), pND]
  linear_combination (uF (h * μ i) - 1) ^ 2 * hs2 i

theorem fDN_eq (hW : W2GaussianDiag gaussD W2) {T h : ℝ} (hT : 0 < T) {μ : Fin d → ℝ}
    (hμ : ∀ i, 0 < μ i) : fDN gaussD W2 T h μ = Real.sqrt (∑ i, pDN T (μ i) h) := by
  have hs : ∀ i, 0 ≤ Real.sqrt (T / μ i) := fun i => Real.sqrt_nonneg _
  have hs2 : ∀ i, Real.sqrt (T / μ i) ^ 2 = T / μ i := fun i =>
    Real.sq_sqrt (div_pos hT (hμ i)).le
  unfold fDN
  rw [hW _ _ (fun i => Real.sqrt_nonneg _) hs]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [sqrt_statDN hT (hμ i), pDN]
  linear_combination (|1 - h * μ i| * uF (h * μ i) - 1) ^ 2 * hs2 i

/-- (i) Diagonal reduction: `f_ND² = Σ (T/μ_i)(w_i − 1)²`, `f_DN² = Σ (T/μ_i)(1 − |1 − η_i| w_i)²`. -/
theorem diag_reduction (hW : W2GaussianDiag gaussD W2) {T h : ℝ} (hT : 0 < T) {μ : Fin d → ℝ}
    (hμ : ∀ i, 0 < μ i) :
    fND gaussD W2 T h μ ^ 2 = ∑ i, pND T (μ i) h ∧
    fDN gaussD W2 T h μ ^ 2 = ∑ i, pDN T (μ i) h := by
  rw [fND_eq hW hT hμ, fDN_eq hW hT hμ,
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pND_nonneg hT (hμ i))),
    Real.sq_sqrt (Finset.sum_nonneg (fun i _ => pDN_nonneg hT (hμ i)))]
  exact ⟨rfl, rfl⟩

/-- The declared numbers: a computed pair `0 < m ≤ L` and a step `0 < h ≤ 2/(m+L)`. -/
structure Adm (m L h : ℝ) : Prop where
  hm : 0 < m
  hmL : m ≤ L
  hh : 0 < h
  hhL : h ≤ 2 / (m + L)

lemma Adm.mul_le {m L h : ℝ} (A : Adm m L h) : h * (m + L) ≤ 2 := step_mul_le A.hm A.hmL A.hhL

lemma Adm.hm_le_one {m L h : ℝ} (A : Adm m L h) : h * m ≤ 1 := by
  have := A.mul_le; have := A.hh; have := A.hmL; nlinarith

lemma Adm.hL_lt_two {m L h : ℝ} (A : Adm m L h) : h * L < 2 := by
  have := A.mul_le; have := A.hh; have := A.hm; nlinarith

lemma sqrt5_gt_two : 2 < Real.sqrt 5 := by
  rw [Real.lt_sqrt (by norm_num)]; norm_num

/-- Spectrum of a record with computed pair `(m, L)`. -/
def Spec (m L : ℝ) (μ : Fin d → ℝ) : Prop := ∀ i, m ≤ μ i ∧ μ i ≤ L

lemma Spec.eta {m L h : ℝ} {μ : Fin d → ℝ} (A : Adm m L h) (S : Spec m L μ) (i : Fin d) :
    0 < h * μ i ∧ h * μ i ≤ h * L ∧ h * μ i < 2 := by
  have h1 := (S i).1; have h2 := (S i).2
  have := A.hm; have := A.hh; have := A.hL_lt_two
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

lemma Spec.pos {m L h : ℝ} {μ : Fin d → ℝ} (A : Adm m L h) (S : Spec m L μ) (i : Fin d) :
    0 < μ i := lt_of_lt_of_le A.hm (S i).1

/-- (ii) No reversal below the threshold: if `h L ≤ √5 − 1` then `f_ND ≤ f_DN` for every record
with spectrum in `[m, L]`, in every dimension. -/
theorem ranking_le (hW : W2GaussianDiag gaussD W2) {m L h T : ℝ} (A : Adm m L h) (hT : 0 < T)
    {μ : Fin d → ℝ} (S : Spec m L μ) (hL : h * L ≤ Real.sqrt 5 - 1) :
    fND gaussD W2 T h μ ≤ fDN gaussD W2 T h μ := by
  rw [fND_eq hW hT (S.pos A), fDN_eq hW hT (S.pos A)]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  obtain ⟨e0, e1, e2⟩ := S.eta A i
  have hc := dir_cmp e0 e2
  unfold pND pDN
  have hTm : 0 ≤ T / μ i := (div_pos hT (S.pos A i)).le
  apply mul_le_mul_of_nonneg_left _ hTm
  rcases lt_or_eq_of_le (e1.trans hL) with h' | h'
  · exact (hc.1 h').le
  · exact (hc.2.1 h').le

/-- (ii), equality case: for `d ≥ 1` and `h L ≤ √5 − 1`, `f_ND = f_DN` iff `H = L I` and
`h L = √5 − 1`. -/
theorem ranking_eq_iff (hW : W2GaussianDiag gaussD W2) {m L h T : ℝ} (A : Adm m L h) (hT : 0 < T)
    (hd : 0 < d) {μ : Fin d → ℝ} (S : Spec m L μ) (hL : h * L ≤ Real.sqrt 5 - 1) :
    fND gaussD W2 T h μ = fDN gaussD W2 T h μ ↔ (∀ i, μ i = L) ∧ h * L = Real.sqrt 5 - 1 := by
  rw [fND_eq hW hT (S.pos A), fDN_eq hW hT (S.pos A)]
  have hnn1 : 0 ≤ ∑ i, pND T (μ i) h := Finset.sum_nonneg (fun i _ => pND_nonneg hT (S.pos A i))
  have hnn2 : 0 ≤ ∑ i, pDN T (μ i) h := Finset.sum_nonneg (fun i _ => pDN_nonneg hT (S.pos A i))
  rw [Real.sqrt_inj hnn1 hnn2]
  have hle : ∀ i ∈ Finset.univ, pND T (μ i) h ≤ pDN T (μ i) h := by
    intro i _
    obtain ⟨e0, e1, e2⟩ := S.eta A i
    have hc := dir_cmp e0 e2
    unfold pND pDN
    have hTm : 0 ≤ T / μ i := (div_pos hT (S.pos A i)).le
    apply mul_le_mul_of_nonneg_left _ hTm
    rcases lt_or_eq_of_le (e1.trans hL) with h' | h'
    · exact (hc.1 h').le
    · exact (hc.2.1 h').le
  rw [Finset.sum_eq_sum_iff_of_le hle]
  -- per direction: equal iff h μ_i = √5 - 1
  have hdir : ∀ i, pND T (μ i) h = pDN T (μ i) h ↔ h * μ i = Real.sqrt 5 - 1 := by
    intro i
    obtain ⟨e0, e1, e2⟩ := S.eta A i
    have hc := dir_cmp e0 e2
    have hTm : 0 < T / μ i := div_pos hT (S.pos A i)
    unfold pND pDN
    constructor
    · intro e
      have e' := mul_left_cancel₀ hTm.ne' e
      rcases lt_trichotomy (h * μ i) (Real.sqrt 5 - 1) with h' | h' | h'
      · exact absurd e' (hc.1 h').ne
      · exact h'
      · exact absurd e' (hc.2.2 h').ne'
    · intro e; rw [hc.2.1 e]
  constructor
  · intro H
    have H0 := (hdir ⟨0, hd⟩).1 (H ⟨0, hd⟩ (Finset.mem_univ _))
    have hLe : h * L = Real.sqrt 5 - 1 := by
      have := (S.eta A ⟨0, hd⟩).2.1
      linarith
    refine ⟨fun i => ?_, hLe⟩
    have := (hdir i).1 (H i (Finset.mem_univ _))
    have hh := A.hh
    have : h * μ i = h * L := by linarith
    exact mul_left_cancel₀ hh.ne' this
  · rintro ⟨hLL, hLe⟩ i _
    rw [hdir]
    rw [hLL i]; exact hLe

/-- (iii) Opposite signs above the threshold: if `h L > √5 − 1` (and `d ≥ 1`), `f_ND < f_DN` at
`H = m I` and `f_ND > f_DN` at `H = L I`. -/
theorem ranking_opposite (hW : W2GaussianDiag gaussD W2) {m L h T : ℝ} (A : Adm m L h)
    (hT : 0 < T) (hd : 0 < d) (hL : Real.sqrt 5 - 1 < h * L) :
    fND gaussD W2 T h (fun _ : Fin d => m) < fDN gaussD W2 T h (fun _ : Fin d => m) ∧
    fDN gaussD W2 T h (fun _ : Fin d => L) < fND gaussD W2 T h (fun _ : Fin d => L) := by
  have hmpos : ∀ _ : Fin d, 0 < m := fun _ => A.hm
  have hLpos : ∀ _ : Fin d, 0 < L := fun _ => lt_of_lt_of_le A.hm A.hmL
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  have h5 := sqrt5_gt_two
  constructor
  · rw [fND_eq hW hT hmpos, fDN_eq hW hT hmpos]
    apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => pND_nonneg hT A.hm))
    apply Finset.sum_lt_sum_of_nonempty hne
    intro i _
    have e0 : 0 < h * m := mul_pos A.hh A.hm
    have e1 := A.hm_le_one
    have hc := dir_cmp e0 (by linarith)
    unfold pND pDN
    exact mul_lt_mul_of_pos_left (hc.1 (by linarith)) (div_pos hT A.hm)
  · rw [fND_eq hW hT hLpos, fDN_eq hW hT hLpos]
    apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => pDN_nonneg hT (hLpos i)))
    apply Finset.sum_lt_sum_of_nonempty hne
    intro i _
    have hL0 : 0 < L := hLpos i
    have e0 : 0 < h * L := mul_pos A.hh hL0
    have hc := dir_cmp e0 A.hL_lt_two
    unfold pND pDN
    exact mul_lt_mul_of_pos_left (hc.2.2 hL) (div_pos hT hL0)

/-- The five declared numbers `(m, L, h, T, d)` fix the sign of `f_ND − f_DN` over all records with
spectrum in `[m, L]` (weakly, in one direction or the other) iff `h L ≤ √5 − 1`. -/
theorem sign_fixed_iff (hW : W2GaussianDiag gaussD W2) {m L h T : ℝ} (A : Adm m L h)
    (hT : 0 < T) (hd : 0 < d) :
    ((∀ μ : Fin d → ℝ, Spec m L μ → fND gaussD W2 T h μ ≤ fDN gaussD W2 T h μ) ∨
     (∀ μ : Fin d → ℝ, Spec m L μ → fDN gaussD W2 T h μ ≤ fND gaussD W2 T h μ)) ↔
      h * L ≤ Real.sqrt 5 - 1 := by
  constructor
  · intro H
    by_contra hcon
    push Not at hcon
    obtain ⟨o1, o2⟩ := ranking_opposite hW A hT hd hcon
    have Sm : Spec m L (fun _ : Fin d => m) := fun _ => ⟨le_rfl, A.hmL⟩
    have SL : Spec m L (fun _ : Fin d => L) := fun _ => ⟨A.hmL, le_rfl⟩
    rcases H with H | H
    · exact absurd (H _ SL) (not_le.2 o2)
    · exact absurd (H _ Sm) (not_le.2 o1)
  · intro hL
    exact Or.inl (fun μ S => ranking_le hW A hT S hL)

/-- At the largest admissible step `h = 2/(m+L)`: `h L > √5 − 1` iff `L/m > φ`. -/
lemma top_step_iff {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    Real.sqrt 5 - 1 < 2 / (m + L) * L ↔ (1 + Real.sqrt 5) / 2 < L / m := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hs : 0 < m + L := by linarith
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have h52 := sqrt5_gt_two
  rw [div_mul_eq_mul_div, lt_div_iff₀ hs, lt_div_iff₀ hm]
  constructor
  · intro H; nlinarith
  · intro H; nlinarith

/-- (iii), the threshold: an admissible step with `h L > √5 − 1` exists iff `L/m > φ = (1+√5)/2`;
equivalently the interval `((√5 − 1)/L, 2/(m+L)]` is nonempty. -/
theorem exists_step_iff {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    (∃ h : ℝ, Adm m L h ∧ Real.sqrt 5 - 1 < h * L) ↔ (1 + Real.sqrt 5) / 2 < L / m := by
  have hs : 0 < m + L := by linarith
  rw [← top_step_iff hm hmL]
  constructor
  · rintro ⟨h, A, H⟩
    refine lt_of_lt_of_le H ?_
    exact mul_le_mul_of_nonneg_right A.hhL (by linarith)
  · intro H
    exact ⟨2 / (m + L), ⟨hm, hmL, by positivity, le_rfl⟩, H⟩

/-- (iii), same threshold, interval form: `h L > √5 − 1 ⟺ (√5 − 1)/L < h`. -/
theorem thr_iff {L h : ℝ} (hL : 0 < L) : Real.sqrt 5 - 1 < h * L ↔ (Real.sqrt 5 - 1) / L < h := by
  rw [div_lt_iff₀ hL]

lemma uF_eq {η u : ℝ} (h2 : η < 2) (hu : 0 < u) (e : u ^ 2 * (2 - η) = 2) : uF η = u := by
  have h1 := uF_sq h2
  have h3 := uF_pos h2
  have h4 : 0 < 2 - η := by linarith
  have : uF η ^ 2 = u ^ 2 := by
    have := h1.trans e.symm
    exact mul_right_cancel₀ h4.ne' this
  exact (pow_left_inj₀ h3.le hu.le (by norm_num)).1 this

/-- `x ↦ (the first coordinate m, then k copies of L)`: the spectrum `{m, L × k}` (`d = k + 1`). -/
def specK (m L : ℝ) (k : ℕ) : Fin (k + 1) → ℝ := Fin.cons m (fun _ : Fin k => L)

lemma sum_specK (m L : ℝ) (k : ℕ) (g : ℝ → ℝ) : ∑ i, g (specK m L k i) = g m + k * g L := by
  rw [Fin.sum_univ_succ]
  simp [specK]

lemma specK_spec {m L : ℝ} (hmL : m ≤ L) (k : ℕ) : Spec m L (specK m L k) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [specK, hmL]
  · simp [specK, hmL]

lemma specK_pos {m L : ℝ} (hm : 0 < m) (hmL : m ≤ L) (k : ℕ) : ∀ i, 0 < specK m L k i :=
  fun i => lt_of_lt_of_le hm (specK_spec hmL k i).1

/-- The per-direction gap `p_ND − p_DN`. -/
noncomputable def gapD (T μ h : ℝ) : ℝ := pND T μ h - pDN T μ h

lemma gapD_neg {m L h T : ℝ} (A : Adm m L h) (hT : 0 < T) : gapD T m h < 0 := by
  have e0 : 0 < h * m := mul_pos A.hh A.hm
  have e1 := A.hm_le_one
  have h5 := sqrt5_gt_two
  have hc := dir_cmp e0 (by linarith)
  unfold gapD pND pDN
  have := mul_lt_mul_of_pos_left (hc.1 (by linarith)) (div_pos hT A.hm)
  linarith

lemma gapD_pos {m L h T : ℝ} (A : Adm m L h) (hT : 0 < T) (hL : Real.sqrt 5 - 1 < h * L) :
    0 < gapD T L h := by
  have hL0 : 0 < L := lt_of_lt_of_le A.hm A.hmL
  have e0 : 0 < h * L := mul_pos A.hh hL0
  have hc := dir_cmp e0 A.hL_lt_two
  unfold gapD pND pDN
  have := mul_lt_mul_of_pos_left (hc.2.2 hL) (div_pos hT hL0)
  linarith

/-- (iv)(c): at the largest step `h = 2/(m+L)` and spectrum `{m, L × k}` (`d = k + 1`), some `k` gives
`f_ND > f_DN` iff `L/m > φ`. For `L/m ≤ φ` no `k` (and by `ranking_le` no spectrum) does.
Here the dimension varies, so the laws and `W2` form a family indexed by `d`. -/
theorem multiplicity_iff {Law' : ℕ → Type*} {gaussD' : ∀ d, (Fin d → ℝ) → Law' d}
    {W2' : ∀ d, Law' d → Law' d → ℝ} (hW : ∀ d, W2GaussianDiag (gaussD' d) (W2' d))
    {m L T : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hT : 0 < T) :
    (∃ k : ℕ, fDN (gaussD' (k + 1)) (W2' (k + 1)) T (2 / (m + L)) (specK m L k) <
        fND (gaussD' (k + 1)) (W2' (k + 1)) T (2 / (m + L)) (specK m L k)) ↔
      (1 + Real.sqrt 5) / 2 < L / m := by
  have hs : 0 < m + L := by linarith
  have A : Adm m L (2 / (m + L)) := ⟨hm, hmL, by positivity, le_rfl⟩
  set h := 2 / (m + L) with hh
  rw [← top_step_iff hm hmL, ← hh]
  constructor
  · rintro ⟨k, hk⟩
    by_contra hcon
    push Not at hcon
    exact absurd (ranking_le (hW (k + 1)) A hT (specK_spec hmL k) hcon) (not_le.2 hk)
  · intro hL
    have gm := gapD_neg A hT
    have gL := gapD_pos A hT hL
    obtain ⟨k, hk⟩ := exists_nat_gt (-(gapD T m h) / gapD T L h)
    refine ⟨k, ?_⟩
    rw [fND_eq (hW (k + 1)) hT (specK_pos hm hmL k), fDN_eq (hW (k + 1)) hT (specK_pos hm hmL k)]
    have hnn : 0 ≤ ∑ i, pDN T (specK m L k i) h :=
      Finset.sum_nonneg (fun i _ => pDN_nonneg hT (specK_pos hm hmL k i))
    apply Real.sqrt_lt_sqrt hnn
    rw [sum_specK m L k (fun μ => pND T μ h), sum_specK m L k (fun μ => pDN T μ h)]
    have : -(gapD T m h) < k * gapD T L h := by
      rwa [div_lt_iff₀ gL] at hk
    unfold gapD at this
    nlinarith

lemma uF_half : uF (1 / 2) = 2 * Real.sqrt 3 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  exact uF_eq (by norm_num) (by positivity) (by nlinarith)

lemma uF_three_half : uF (3 / 2) = 2 := uF_eq (by norm_num) (by norm_num) (by norm_num)

lemma uF_two_thirds : uF (2 / 3) = Real.sqrt (3 / 2) := by
  have h3 : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.2 (by norm_num)
  exact uF_eq (by norm_num) h3p (by rw [h3]; norm_num)

lemma uF_four_thirds : uF (4 / 3) = Real.sqrt 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  exact uF_eq (by norm_num) h3p (by rw [h3]; norm_num)

lemma inv_sqrt_three : 1 / Real.sqrt 3 = Real.sqrt 3 / 3 := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  field_simp
  nlinarith

lemma four_div_sqrt_three : 4 / Real.sqrt 3 = 4 * Real.sqrt 3 / 3 := by
  rw [div_eq_mul_one_div, inv_sqrt_three]; ring

lemma sqrt_six : Real.sqrt 6 = 2 * Real.sqrt (3 / 2) := by
  rw [show (6 : ℝ) = 2 ^ 2 * (3 / 2) by norm_num, Real.sqrt_mul (by norm_num), Real.sqrt_sq (by norm_num)]

lemma pND_a1 (T : ℝ) : pND T 1 (1 / 2) = T * (2 * Real.sqrt 3 / 3 - 1) ^ 2 := by
  unfold pND; norm_num [uF_half]

lemma pND_a3 (T : ℝ) : pND T 3 (1 / 2) = T / 3 := by
  unfold pND; norm_num [uF_three_half]

lemma pDN_a1 (T : ℝ) : pDN T 1 (1 / 2) = T * (1 - Real.sqrt 3 / 3) ^ 2 := by
  unfold pDN
  have : |1 - 1 / 2 * (1:ℝ)| = 1 / 2 := by norm_num [abs_of_pos]
  rw [this, mul_one, uF_half]; ring

lemma pDN_a3 (T : ℝ) : pDN T 3 (1 / 2) = 0 := by
  unfold pDN
  have : |1 - 1 / 2 * (3:ℝ)| = 1 / 2 := by norm_num [abs_of_neg]
  rw [this, show (1 / 2 * 3 : ℝ) = 3 / 2 by norm_num, uF_three_half]; norm_num

/-- (iv)(a): `d = 2`, `H = diag(1, 3)`, `(m, L) = (1, 3)` (both attained), `h = 1/2 = 2/(m+L)`:
`f_ND² = T(8/3 − 4/√3)`, `f_DN² = T(1 − 1/√3)²`, `f_ND > f_DN`; while `H = I₂` with the same five numbers
(`m = 1`, `L = 3`, `h = 1/2`, `T`, `d = 2`; a loose pair) has `f_ND < f_DN`. -/
theorem instance_a {gaussD : (Fin (1 + 1) → ℝ) → Law} {W2 : Law → Law → ℝ}
    (hW : W2GaussianDiag gaussD W2) {T : ℝ} (hT : 0 < T) :
    Adm 1 3 (1 / 2) ∧ (1 / 2 : ℝ) = 2 / (1 + 3) ∧ Spec 1 3 (specK 1 3 1) ∧
    (specK 1 3 1 0 = 1 ∧ specK 1 3 1 1 = 3) ∧
    fND gaussD W2 T (1 / 2) (specK 1 3 1) ^ 2 = T * (8 / 3 - 4 / Real.sqrt 3) ∧
    fDN gaussD W2 T (1 / 2) (specK 1 3 1) ^ 2 = T * (1 - 1 / Real.sqrt 3) ^ 2 ∧
    fDN gaussD W2 T (1 / 2) (specK 1 3 1) < fND gaussD W2 T (1 / 2) (specK 1 3 1) ∧
    Spec 1 3 (fun _ : Fin (1 + 1) => (1 : ℝ)) ∧
    fND gaussD W2 T (1 / 2) (fun _ : Fin (1 + 1) => (1 : ℝ)) <
      fDN gaussD W2 T (1 / 2) (fun _ : Fin (1 + 1) => (1 : ℝ)) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h3lt : Real.sqrt 3 < 2 := by nlinarith
  have A : Adm 1 3 (1 / 2) := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hpos := specK_pos (m := 1) (L := 3) (by norm_num) (by norm_num) 1
  have sND : ∑ i, pND T (specK 1 3 1 i) (1 / 2) = T * (8 / 3 - 4 / Real.sqrt 3) := by
    rw [sum_specK 1 3 1 (fun μ => pND T μ (1 / 2)), pND_a1, pND_a3, four_div_sqrt_three]
    push_cast
    linear_combination (4 * T / 9) * h3
  have sDN : ∑ i, pDN T (specK 1 3 1 i) (1 / 2) = T * (1 - 1 / Real.sqrt 3) ^ 2 := by
    rw [sum_specK 1 3 1 (fun μ => pDN T μ (1 / 2)), pDN_a1, pDN_a3, inv_sqrt_three]
    push_cast; ring
  refine ⟨A, by norm_num, specK_spec (by norm_num) 1, ⟨by simp [specK], by simp [specK]⟩, ?_, ?_, ?_,
    fun _ => ⟨le_rfl, by norm_num⟩, ?_⟩
  · rw [(diag_reduction hW hT hpos).1, sND]
  · rw [(diag_reduction hW hT hpos).2, sDN]
  · rw [fND_eq hW hT hpos, fDN_eq hW hT hpos]
    apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => pDN_nonneg hT (hpos i)))
    rw [sND, sDN, inv_sqrt_three, four_div_sqrt_three]
    have key : T * (8 / 3 - 4 * Real.sqrt 3 / 3) - T * (1 - Real.sqrt 3 / 3) ^ 2 =
        T * (4 / 3 - 2 * Real.sqrt 3 / 3) := by linear_combination (-T / 9) * h3
    nlinarith [mul_pos hT (by linarith : 0 < 4 / 3 - 2 * Real.sqrt 3 / 3)]
  · have := (ranking_opposite hW A hT (by norm_num : 0 < 1 + 1) (by
      have h5 := sqrt5_gt_two
      have : Real.sqrt 5 < 5 / 2 := by nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 5 by norm_num)]
      linarith)).1
    exact this

lemma pND_b1 (T : ℝ) : pND T 1 (2 / 3) = T * (Real.sqrt (3 / 2) - 1) ^ 2 := by
  unfold pND; norm_num [uF_two_thirds]

lemma pND_b2 (T : ℝ) : pND T 2 (2 / 3) = T / 2 * (Real.sqrt 3 - 1) ^ 2 := by
  unfold pND
  rw [show (2 / 3 * 2 : ℝ) = 4 / 3 by norm_num, uF_four_thirds]

lemma pDN_b1 (T : ℝ) : pDN T 1 (2 / 3) = T * (1 - Real.sqrt (3 / 2) / 3) ^ 2 := by
  unfold pDN
  have : |1 - 2 / 3 * (1:ℝ)| = 1 / 3 := by norm_num [abs_of_pos]
  rw [this, mul_one, uF_two_thirds]; ring

lemma pDN_b2 (T : ℝ) : pDN T 2 (2 / 3) = T / 2 * (1 - Real.sqrt 3 / 3) ^ 2 := by
  unfold pDN
  have : |1 - 2 / 3 * (2:ℝ)| = 1 / 3 := by norm_num [abs_of_neg]
  rw [this, show (2 / 3 * 2 : ℝ) = 4 / 3 by norm_num, uF_four_thirds]; ring

lemma gap_b1 (T : ℝ) : gapD T 1 (2 / 3) = T * (4 / 3 - 4 * Real.sqrt (3 / 2) / 3) := by
  have h : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  unfold gapD; rw [pND_b1, pDN_b1]
  linear_combination (8 * T / 9) * h

lemma gap_b2 (T : ℝ) : gapD T 2 (2 / 3) = T * (4 / 3 - 2 * Real.sqrt 3 / 3) := by
  have h : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  unfold gapD; rw [pND_b2, pDN_b2]
  linear_combination (4 * T / 9) * h

/-- (iv)(b): `d = 3`, `H = diag(1, 2, 2)`, `(m, L) = (1, 2)` (both attained, `L/m = 2`), `h = 2/3 = 2/(m+L)`:
`f_ND² − f_DN² = T(4 − 4√3/3 − 2√6/3) > 0`, so `f_ND > f_DN`. -/
theorem instance_b {gaussD : (Fin (2 + 1) → ℝ) → Law} {W2 : Law → Law → ℝ}
    (hW : W2GaussianDiag gaussD W2) {T : ℝ} (hT : 0 < T) :
    Adm 1 2 (2 / 3) ∧ (2 / 3 : ℝ) = 2 / (1 + 2) ∧ Spec 1 2 (specK 1 2 2) ∧
    (specK 1 2 2 0 = 1 ∧ specK 1 2 2 1 = 2 ∧ specK 1 2 2 2 = 2) ∧
    fND gaussD W2 T (2 / 3) (specK 1 2 2) ^ 2 =
      T * ((Real.sqrt (3 / 2) - 1) ^ 2 + (Real.sqrt 3 - 1) ^ 2) ∧
    fDN gaussD W2 T (2 / 3) (specK 1 2 2) ^ 2 =
      T * ((1 - Real.sqrt (3 / 2) / 3) ^ 2 + (1 - Real.sqrt 3 / 3) ^ 2) ∧
    fND gaussD W2 T (2 / 3) (specK 1 2 2) ^ 2 - fDN gaussD W2 T (2 / 3) (specK 1 2 2) ^ 2 =
      T * (4 - 4 * Real.sqrt 3 / 3 - 2 * Real.sqrt 6 / 3) ∧
    0 < T * (4 - 4 * Real.sqrt 3 / 3 - 2 * Real.sqrt 6 / 3) ∧
    fDN gaussD W2 T (2 / 3) (specK 1 2 2) < fND gaussD W2 T (2 / 3) (specK 1 2 2) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h32 : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h32p : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.2 (by norm_num)
  have A : Adm 1 2 (2 / 3) := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hpos := specK_pos (m := 1) (L := 2) (by norm_num) (by norm_num) 2
  have sND : ∑ i, pND T (specK 1 2 2 i) (2 / 3) =
      T * ((Real.sqrt (3 / 2) - 1) ^ 2 + (Real.sqrt 3 - 1) ^ 2) := by
    rw [sum_specK 1 2 2 (fun μ => pND T μ (2 / 3)), pND_b1, pND_b2]; push_cast; ring
  have sDN : ∑ i, pDN T (specK 1 2 2 i) (2 / 3) =
      T * ((1 - Real.sqrt (3 / 2) / 3) ^ 2 + (1 - Real.sqrt 3 / 3) ^ 2) := by
    rw [sum_specK 1 2 2 (fun μ => pDN T μ (2 / 3)), pDN_b1, pDN_b2]; push_cast; ring
  have hdiff : T * ((Real.sqrt (3 / 2) - 1) ^ 2 + (Real.sqrt 3 - 1) ^ 2) -
      T * ((1 - Real.sqrt (3 / 2) / 3) ^ 2 + (1 - Real.sqrt 3 / 3) ^ 2) =
      T * (4 - 4 * Real.sqrt 3 / 3 - 2 * Real.sqrt 6 / 3) := by
    rw [sqrt_six]
    linear_combination (8 * T / 9) * h32 + (8 * T / 9) * h3
  have hpospoly : 0 < 4 - 4 * Real.sqrt 3 / 3 - 2 * Real.sqrt 6 / 3 := by
    rw [sqrt_six]
    have hst : (Real.sqrt 3 * Real.sqrt (3 / 2)) ^ 2 = 9 / 2 := by rw [mul_pow, h3, h32]; norm_num
    have hstp : 0 < Real.sqrt 3 * Real.sqrt (3 / 2) := mul_pos h3p h32p
    have hlt : Real.sqrt 3 * Real.sqrt (3 / 2) < 9 / 4 := by nlinarith
    have hsum : Real.sqrt 3 + Real.sqrt (3 / 2) < 3 := by nlinarith
    linarith
  refine ⟨A, by norm_num, specK_spec (by norm_num) 2,
    ⟨by simp [specK], by simp [specK], rfl⟩, ?_, ?_, ?_, mul_pos hT hpospoly, ?_⟩
  · rw [(diag_reduction hW hT hpos).1, sND]
  · rw [(diag_reduction hW hT hpos).2, sDN]
  · rw [(diag_reduction hW hT hpos).1, (diag_reduction hW hT hpos).2, sND, sDN, hdiff]
  · rw [fND_eq hW hT hpos, fDN_eq hW hT hpos]
    apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => pDN_nonneg hT (hpos i)))
    rw [sND, sDN]
    nlinarith [mul_pos hT hpospoly]

/-- (v), the contrast spectrum `{1, 1, 2}` at `(m, L, h, d) = (1, 2, 2/3, 3)` (both `1` and `2` occur, so the
pair is attained, as for `{1, 2, 2}` of `instance_b`): `f_ND² − f_DN² = T (2 d_m + d_L)
= T (4 − 4√6/3 − 2√3/3) < 0`, so `f_ND < f_DN`, the opposite sign to `instance_b`. Here `d_m = 4/3 − 4√(3/2)/3`
and `d_L = 4/3 − 2√3/3` are the per-direction values in units `T/μ` (`gap_b1`, `gap_b2`; `√6 = 2√(3/2)`). -/
theorem instance_c {gaussD : (Fin 3 → ℝ) → Law} {W2 : Law → Law → ℝ}
    (hW : W2GaussianDiag gaussD W2) {T : ℝ} (hT : 0 < T) :
    Adm 1 2 (2 / 3) ∧ Spec 1 2 (![1, 1, 2] : Fin 3 → ℝ) ∧
    (∃ i, (![1, 1, 2] : Fin 3 → ℝ) i = 1) ∧ (∃ i, (![1, 1, 2] : Fin 3 → ℝ) i = 2) ∧
    fND gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) ^ 2 -
      fDN gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) ^ 2 =
      T * (2 * (4 / 3 - 4 * Real.sqrt (3 / 2) / 3) + (4 / 3 - 2 * Real.sqrt 3 / 3)) ∧
    T * (2 * (4 / 3 - 4 * Real.sqrt (3 / 2) / 3) + (4 / 3 - 2 * Real.sqrt 3 / 3)) =
      T * (4 - 4 * Real.sqrt 6 / 3 - 2 * Real.sqrt 3 / 3) ∧
    T * (4 - 4 * Real.sqrt 6 / 3 - 2 * Real.sqrt 3 / 3) < 0 ∧
    fND gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) <
      fDN gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) := by
  have A : Adm 1 2 (2 / 3) := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hpos : ∀ i, 0 < (![1, 1, 2] : Fin 3 → ℝ) i := by
    intro i; fin_cases i <;> norm_num
  have hs6 : Real.sqrt 6 = 2 * Real.sqrt (3 / 2) := sqrt_six
  have h6 : (2.4 : ℝ) < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h3 : (1.7 : ℝ) < Real.sqrt 3 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hneg : 4 - 4 * Real.sqrt 6 / 3 - 2 * Real.sqrt 3 / 3 < 0 := by linarith
  have gsum : ∀ g : ℝ → ℝ, ∑ i, g ((![1, 1, 2] : Fin 3 → ℝ) i) = g 1 + g 1 + g 2 := by
    intro g; rw [Fin.sum_univ_three]; simp
  have hdiff : fND gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) ^ 2 -
      fDN gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) ^ 2 =
      T * (2 * (4 / 3 - 4 * Real.sqrt (3 / 2) / 3) + (4 / 3 - 2 * Real.sqrt 3 / 3)) := by
    rw [(diag_reduction hW hT hpos).1, (diag_reduction hW hT hpos).2,
      gsum (fun μ => pND T μ (2 / 3)), gsum (fun μ => pDN T μ (2 / 3))]
    have g1 := gap_b1 T
    have g2 := gap_b2 T
    unfold gapD at g1 g2
    linear_combination 2 * g1 + g2
  have hcl : T * (2 * (4 / 3 - 4 * Real.sqrt (3 / 2) / 3) + (4 / 3 - 2 * Real.sqrt 3 / 3)) =
      T * (4 - 4 * Real.sqrt 6 / 3 - 2 * Real.sqrt 3 / 3) := by
    rw [hs6]; ring
  refine ⟨A, fun i => by fin_cases i <;> norm_num, ⟨0, rfl⟩, ⟨2, rfl⟩, hdiff, hcl,
    mul_neg_of_pos_of_neg hT hneg, ?_⟩
  rw [fND_eq hW hT hpos, fDN_eq hW hT hpos]
  apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => pND_nonneg hT (hpos i)))
  have := (diag_reduction (h := 2 / 3) hW hT hpos)
  have e1 : fND gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) ^ 2 = ∑ i, pND T ((![1, 1, 2] : Fin 3 → ℝ) i) (2 / 3) := this.1
  have e2 : fDN gaussD W2 T (2 / 3) (![1, 1, 2] : Fin 3 → ℝ) ^ 2 = ∑ i, pDN T ((![1, 1, 2] : Fin 3 → ℝ) i) (2 / 3) := this.2
  have := mul_neg_of_pos_of_neg hT hneg
  linarith

/-- (iv)(c), the instance `m = 1`, `L = 2`, `h = 2/3`: the least `k` with `f_ND > f_DN` is `k = 2`
(`k = 0` and `k = 1` give `f_ND ≤ f_DN`; `k = 2` is `instance_b`). The other listed least `k`
(`L = 1.8: 4`, `1.7: 8`, `1.62: 325`) are numerical (witness) values and are not formalised. -/
theorem least_k_L2 {Law' : ℕ → Type*} {gaussD' : ∀ d, (Fin d → ℝ) → Law' d}
    {W2' : ∀ d, Law' d → Law' d → ℝ} (hW : ∀ d, W2GaussianDiag (gaussD' d) (W2' d))
    {T : ℝ} (hT : 0 < T) (k : ℕ) (hk : k ≤ 1) :
    fND (gaussD' (k + 1)) (W2' (k + 1)) T (2 / 3) (specK 1 2 k) ≤
      fDN (gaussD' (k + 1)) (W2' (k + 1)) T (2 / 3) (specK 1 2 k) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h32 : Real.sqrt (3 / 2) ^ 2 = 3 / 2 := Real.sq_sqrt (by norm_num)
  have h3p : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h32p : 0 < Real.sqrt (3 / 2) := Real.sqrt_pos.2 (by norm_num)
  have hpos := specK_pos (m := 1) (L := 2) (by norm_num) (by norm_num) k
  rw [fND_eq (hW (k + 1)) hT hpos, fDN_eq (hW (k + 1)) hT hpos]
  apply Real.sqrt_le_sqrt
  rw [sum_specK 1 2 k (fun μ => pND T μ (2 / 3)), sum_specK 1 2 k (fun μ => pDN T μ (2 / 3))]
  have g1 := gap_b1 T
  have g2 := gap_b2 T
  unfold gapD at g1 g2
  have s1 : Real.sqrt 3 > 1.7 := by
    rw [gt_iff_lt, Real.lt_sqrt (by norm_num)]; norm_num
  have s2 : Real.sqrt (3 / 2) > 1.2 := by
    rw [gt_iff_lt, Real.lt_sqrt (by norm_num)]; norm_num
  interval_cases k
  · simp only [Nat.cast_zero, zero_mul, add_zero]
    nlinarith [mul_pos hT (by linarith : 0 < 4 * Real.sqrt (3 / 2) / 3 - 4 / 3)]
  · simp only [Nat.cast_one, one_mul]
    nlinarith [mul_pos hT (by linarith : 0 < 4 * Real.sqrt (3 / 2) / 3 + 2 * Real.sqrt 3 / 3 - 8 / 3)]

/-- (v) of r-ord-undetermined: among records of dimension `d = 2` that attain the pair `(m, L) = (1, 3)`
(both `1` and `3` occur in the spectrum), at `h = 1/2`, the sign is determined: `f_ND > f_DN`
(all such records are rotations of `diag(1, 3)`; the opposite sign in `instance_a` comes from the
record `H = I₂`, whose pair is loose). -/
theorem attained_sign_d2 {gaussD : (Fin (1 + 1) → ℝ) → Law} {W2 : Law → Law → ℝ}
    (hW : W2GaussianDiag gaussD W2) {T : ℝ} (hT : 0 < T) {μ : Fin (1 + 1) → ℝ}
    (S : Spec 1 3 μ) (h1 : ∃ i, μ i = 1) (h3 : ∃ i, μ i = 3) :
    fDN gaussD W2 T (1 / 2) μ < fND gaussD W2 T (1 / 2) μ := by
  have A : Adm 1 3 (1 / 2) := ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  have hpos := S.pos A
  have key : (μ 0 = 1 ∧ μ 1 = 3) ∨ (μ 0 = 3 ∧ μ 1 = 1) := by
    obtain ⟨i, hi⟩ := h1
    obtain ⟨j, hj⟩ := h3
    fin_cases i <;> fin_cases j <;> simp_all
  have hT3 := (instance_a hW hT)
  have hmain := hT3.2.2.2.2.2.2.1
  rcases key with ⟨a, b⟩ | ⟨a, b⟩
  · have : μ = specK 1 3 1 := by
      funext i; fin_cases i <;> simp [specK, a, b]
    rw [this]; exact hmain
  · have : ∀ g : ℝ → ℝ, ∑ i, g (μ i) = ∑ i, g (specK 1 3 1 i) := by
      intro g
      rw [Fin.sum_univ_two, Fin.sum_univ_two]
      simp [specK, a, b, add_comm]
    rw [fND_eq hW hT hpos, fDN_eq hW hT hpos]
    apply Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun i _ => pDN_nonneg hT (hpos i)))
    have e1 := this (fun x => pND T x (1 / 2))
    have e2 := this (fun x => pDN T x (1 / 2))
    rw [e1, e2]
    have hp1 := specK_pos (m := 1) (L := 3) (by norm_num) (by norm_num) 1
    have := hmain
    rw [fND_eq hW hT hp1, fDN_eq hW hT hp1] at this
    exact Real.sqrt_lt_sqrt_iff (Finset.sum_nonneg (fun i _ => pDN_nonneg hT (hp1 i))) |>.1 this

end ranking

/-! ## Axiom audit -/

#print axioms OCF.RORD.Cw_eq_poly
#print axioms OCF.RORD.statVar_eq
#print axioms OCF.RORD.sqrt_statVar
#print axioms OCF.RORD.flr_eq
#print axioms OCF.RORD.exact_iff_Cw
#print axioms OCF.RORD.flr_eq_iff
#print axioms OCF.RORD.coincPoly_zero_iff
#print axioms OCF.RORD.coincPoly_zero_iff_Ioc
#print axioms OCF.RORD.coincide_finite
#print axioms OCF.RORD.slice_identity
#print axioms OCF.RORD.floors_coincide_finite
#print axioms OCF.RORD.law_coincide_iff
#print axioms OCF.RORD.disp_formula
#print axioms OCF.RORD.order_pushVar
#print axioms OCF.RORD.order_displacements
#print axioms OCF.RORD.rotation_invariant
#print axioms OCF.RORD.rotation_eq
#print axioms OCF.RORD.rotation_cyclic
#print axioms OCF.RORD.rotation_map
#print axioms OCF.RORD.rotation_w2_bound
#print axioms OCF.RORD.row_recursion
#print axioms OCF.RORD.r_ord_row
#print axioms OCF.RORD.reversed_iterate
#print axioms OCF.RORD.r_ord_reversed
#print axioms OCF.RORD.w2GaussianDiag_model
#print axioms OCF.RORD.diag_reduction
#print axioms OCF.RORD.ranking_le
#print axioms OCF.RORD.ranking_eq_iff
#print axioms OCF.RORD.ranking_opposite
#print axioms OCF.RORD.sign_fixed_iff
#print axioms OCF.RORD.top_step_iff
#print axioms OCF.RORD.exists_step_iff
#print axioms OCF.RORD.thr_iff
#print axioms OCF.RORD.multiplicity_iff
#print axioms OCF.RORD.instance_a
#print axioms OCF.RORD.instance_b
#print axioms OCF.RORD.least_k_L2
#print axioms OCF.RORD.attained_sign_d2
#print axioms OCF.RORD.instance_c

end OCF.RORD

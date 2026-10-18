/-
C3 (Local scope of the conditioning certificate) — facts F1–F3, Lemma 1 (curvature floor,
quadratic-form version), Lemma 2 (strong convexity and strong monotonicity on balls), Lemma 3
(ray estimates), Proposition 4 (uniqueness, minimality, location), Proposition 5 (capture),
Theorem 6 (a)–(c) (local conditioning certificate), Corollary 7 (i)–(iv) and its r = ∞ case
(the spine's constants), and Proposition 8 (a)–(f) plus the case M = 0 (sharpness, d = 1).

Source of truth: project_plan/done/proof_audits/C3_local_conditioning/01_derivation.md (stage-1 dossier
revised at stage 3; sha16 95ed6bc3a8aae604 at the start and at the end of formalisation; file not
edited), 03_adjudication.md (tractability call: algebraic sharpness core and Lemma 1 cheap;
Lemma 3 and Proposition 5 medium), and the stage-4 draft 04_landing_draft.tex
(Lemma lem:c3-ray, Theorem thm:c3-local).

DEFINITIONAL MAP:
* ℝᵈ (d ≥ 1) — any finite-dimensional nontrivial real inner product space X
  (`InnerProductSpace ℝ X`, `CompleteSpace X`, `ProperSpace X`, `Nontrivial X`); Lemmas 1–3,
  Proposition 4 and the strong convexity statements need only `CompleteSpace X`. ℝᵈ is
  `EuclideanSpace ℝ (Fin d)` with `NeZero d` (instance check at the end of the file).
* ∇E — Mathlib's `gradient E`; ∇²E — `hess E x := fderiv ℝ (gradient E) x : X →L[ℝ] X`;
  ‖·‖ on operators is the operator norm (the spectral norm on ℝᵈ). Symmetry of ∇²E is
  derived from C² (`hess_symm`, via `ContDiffAt.isSymmSndFDerivAt`), not assumed.
* (H1) E ∈ C² — `ContDiff ℝ 2 E`.
* (H2) γ := λ_min(∇²E(x̄)) > 0 — encoded in Rayleigh form `γ‖u‖² ≤ ⟪∇²E(x̄)u, u⟫ ∀u`, γ > 0,
  i.e. γ ≤ λ_min (B&V p. 647). This is the only consequence of γ = λ_min any proof uses, so
  every theorem is stated under a weaker hypothesis and applies verbatim with γ = λ_min. No
  eigenvalue API is used anywhere (as the adjudicator recommended for Lemma 1).
* (H3) R ∈ (0, ∞], M ≥ 0, ‖∇²E(x) − ∇²E(x̄)‖ ≤ M‖x − x̄‖ on B(x̄, R) — `R : ℝ≥0∞`, `0 < R`,
  ball membership `ENNReal.ofReal ‖x − x̄‖ < R` (R = ⊤ is R = ∞, B(x̄, ∞) = X).
  Structure `Hyp E x̄ γ M R` bundles (H1)–(H3).
* [0, γ/M] with γ/0 = ∞ — `Dom γ M = {s | 0 ≤ s ∧ M s ≤ γ}`; 0 ≤ t ≤ γ²/(2M) —
  `0 ≤ t ∧ 2Mt ≤ γ²` (`F3Hyp`, with γ > 0, M ≥ 0); both read correctly when M = 0.
* φ, s₋, κ, q_ρ — `phi γ M s`, `sMinus γ M t` (the dossier's closed formula; = t/γ when M = 0,
  `sMinus_M_zero`), `kappa γ M ρ`, `qfac γ M ρ α = 1 − ακ(ρ)`.
* r₀ = min{R, γ/M} (γ/0 = ∞) — `r0 R γ M : ℝ≥0∞`; U = B(x̄, r₀) — `U x̄ R γ M`;
  "‖g‖ < φ(r₀), with φ(∞) := +∞" — `ExistCond R γ M ‖g‖ := r0 = ⊤ ∨ ‖g‖ < φ(r0.toReal)`.
* β_ρ = max_{B̄(x̄,ρ)} ‖∇²E‖ — `beta E x̄ ρ := sSup` of the image, proved attained
  (`Hyp.beta_attained`); α ≤ 1/β_ρ ⇔ α‖∇²E(z)‖ ≤ 1 on B̄(x̄, ρ) (`Hyp.step_le_inv_beta_iff`).
* T_α = Id − α∇E — `step E α`. (H4)+(H5) of Proposition 5 — structure `Capture E x̄ γ M R ρ α`.
* "E is κ-strongly convex on C" (B&C Def. 10.7, (10.2), for E + ι_C) — Mathlib
  `StrongConvexOn C κ E` (the same inequality on the convex set C).
* "Stationary point" — `gradient E x = 0`; "unique minimiser over U" — `IsMinOn E U x*` and
  every `IsMinOn E U y` with y ∈ U has y = x*.
* Proposition 8 (d = 1): `Hyp1D e e' e'' γ M R` = (H1)–(H3) for e : ℝ → ℝ at x̄ = 0 written with
  derivatives; `Hyp1D.toHyp` proves it is exactly `Hyp e 0 γ M R` on X = ℝ (with
  `gradient e = e'`, `hess e x u = e''(x) u`). Family: `famD1 ζ γ M x = −ζ + γx − (M/2)x|x|`
  (= e′), `famD2 γ M x = γ − M|x|` (= e″), `famE = ∫₀ˣ famD1`. Steep drop (8.1): `sdD1`,
  `sdD2` (`sdD2_eq` is the dossier's two-piece formula), `sdE = ∫₀ˣ sdD1`.

STATEMENTS FORMALISED (all proved, no sorry):
* F1 `hasDerivAt_phi`, `phi_strictMonoOn`, `phi_le_max`, `phi_vertex`; F2 `half_le_phi`;
  F3 `sMinus_nonneg`, `sMinus_mem_Dom`, `phi_sMinus`, `eq_sMinus_of_phi_eq` (unique root in
  [0, γ/M]), `phi_eq_iff_roots`, `sMinus_eq_smaller_root`, `larger_root_ge` (≥ γ/M, equality iff
  t = γ²/(2M)), `sMinus_M_zero`, `phi_le_iff`, `sMinus_lt_iff`, `sMinus_le_two_div`;
  monotonicity of s₋: `sMinus_strictMonoOn`.
* S6.2 `psi_le`, `psi_bound`.
* Corollary 7 constants: `M_mul_min_le`, `kappa_ge_half`, `kappa_min_eq_half`,
  `phi_ge_three_quarters`, `cor7_iii_constants`, `cor7_iv_constants`.
* S0.1 `hessVar_closed`; Lemma 1 `curvature_floor`, `curvature_floor_ball` (any continuous
  operator field), `Hyp.floor_pt`, `Hyp.floor_ball`.
* Lemma 2 `Hyp.lemma2` ((a) via `Hyp.convexOn_sub_sq` + `strongConvexOn_iff_convex`; (b)
  `Hyp.strongMono`, which holds for every finite ρ ≤ R).
* Lemma 3 (a) `Hyp.ray_lower`; (b) `Hyp.ray_step` (and the pointwise form `Hyp.ray_step'`).
  The vector-valued integral Ā of S3.4–S3.7 is replaced by scalar monotonicity along the segment
  (`sub_le_sub_of_hasDerivAt_le`, `seg_bound`) and the symmetric-form bound
  `inner_le_of_form_bounds` (0 ≤ ⟨Bu,u⟩ ≤ c‖u‖² ⇒ ⟨Bh,w⟩ ≤ c‖h‖‖w‖) — the quadratic-form
  route of Decision 4, applied pointwise in t.
* Proposition 4 `Hyp.stationary_unique`, `Hyp.stationary_isMinOn`, `Hyp.isMinOn_unique`,
  `Hyp.location` (with `Hyp.phi_le_of_stationary`).
* S5.0/S6.1/Cor. 7 β facts `Hyp.beta_attained`, `Hyp.gamma_le_beta`, `Hyp.beta_mono`,
  `Hyp.beta_eq_sSup_ball` (β_r = β_B).
* Proposition 5 (a) `Capture.mapsTo`, `Capture.mapsTo_ball`; (b) `Capture.lipschitz`,
  `Capture.qfac_nonneg`, `Capture.qfac_lt_one`; (c) `Capture.existsUnique_stationary` (Banach
  via `ContractingWith.exists_fixedPoint'` on the closed ball), `Capture.iterate_bounds`
  (stay in ball, q^k rate, 2ρq^k, a-posteriori q/(1−q)), `Capture.tendsto_iterate`;
  (d) `Capture.location`.
* Theorem 6 (a) `thm6_a`, (b) `thm6_b`, (c) `thm6_c`; (d) is Proposition 8 below.
* Corollary 7 `cor7_radius` (r = min{R, γ/(2M)} finite is admissible), `cor7_i`, `cor7_ii`,
  `cor7_iii`, `cor7_iv`, `cor7_infinite` (r = ∞). (i)–(iv) are proved for every finite r > 0
  with r ≤ R and Mr ≤ γ/2, which includes the dossier's r.
* Proposition 8 (d = 1): S8.1 `fam_hyp`, `fam_facts`; (a) `prop8_a_attained`,
  `prop8_a_sharp_convex`, `prop8_a_sharp_mono`; (b) `prop8_b` (both cases: S8.3 family,
  S8.3b steep drop `sd_hyp`); (c) `prop8_c`; (d) `prop8_d` (with `fam_beta`: β_ρ = γ);
  (e) `prop8_e` (Lipschitz constant is exactly q_ρ, as an `IsLeast`); (f) `prop8_f`,
  `prop8_f_ratio`; case M = 0 `prop8_M_zero`.

NOT COVERED (remain audited prose): Examples 9.1–9.4; Remarks 1.4, 2.4 (its arithmetic is
`kappa_ge_half`/`kappa_min_eq_half`), 3.8, 4.6, 10.1–10.6; the lift of Proposition 8 from d = 1 to
d ≥ 2 (E(x) = e(x₁) + (γ/2)Σ_{i≥2} x_i²); the B&C citation route of S2.1–S2.2 and S5.2–S5.4
(replaced, not formalised: the statements are proved by first-order arguments instead).

Status tier: FORMALISED (statement + proof, no sorry) for F1–F3, S6.2, Lemmas 1–3,
Propositions 4–5, Theorem 6 (a)–(c), Corollary 7 (i)–(iv) and r = ∞, and Proposition 8
(a)–(f) and M = 0 in dimension d = 1. `#print axioms`: propext, Classical.choice, Quot.sound only.
-/
import Mathlib

namespace OCF.C3
open Set Filter Topology Metric
open scoped ENNReal NNReal

/-! ## Part A. The scalar functions φ, s₋, κ (facts F1–F3) -/

/-- φ(s) = γs − (M/2)s². -/
noncomputable def phi (γ M s : ℝ) : ℝ := γ * s - M / 2 * s ^ 2

/-- s₋(t) = 2t / (γ + √(γ² − 2Mt)). For M = 0 this is t/γ (`sMinus_M_zero`). -/
noncomputable def sMinus (γ M t : ℝ) : ℝ := 2 * t / (γ + Real.sqrt (γ ^ 2 - 2 * M * t))

/-- κ(ρ) = γ − Mρ, the curvature floor. -/
def kappa (γ M ρ : ℝ) : ℝ := γ - M * ρ

section Algebra
variable {γ M : ℝ}

/-- F1: φ′(s) = γ − Ms. -/
theorem hasDerivAt_phi (s : ℝ) : HasDerivAt (phi γ M) (γ - M * s) s := by
  have h1 : HasDerivAt (fun x : ℝ => γ * x) γ s := by
    simpa using (hasDerivAt_id s).const_mul γ
  have h2 : HasDerivAt (fun x : ℝ => M / 2 * x ^ 2) (M / 2 * (2 * s)) s := by
    simpa using (hasDerivAt_pow 2 s).const_mul (M / 2)
  have h3 : HasDerivAt (fun x => γ * x - M / 2 * x ^ 2) (γ - M / 2 * (2 * s)) s := h1.sub h2
  rw [show γ - M * s = γ - M / 2 * (2 * s) by ring]
  exact h3

/-- The interval [0, γ/M] (with γ/0 = +∞), encoded as `0 ≤ s ∧ M * s ≤ γ`. -/
def Dom (γ M : ℝ) : Set ℝ := {s | 0 ≤ s ∧ M * s ≤ γ}

lemma phi_sub (a b : ℝ) : phi γ M b - phi γ M a = (b - a) * (γ - M * (a + b) / 2) := by
  simp only [phi]; ring

/-- F1: φ is strictly increasing on [0, γ/M] (on [0, ∞) when M = 0). -/
theorem phi_strictMonoOn (hγ : 0 < γ) (hM : 0 ≤ M) : StrictMonoOn (phi γ M) (Dom γ M) := by
  intro a ha b hb hab
  rw [← sub_pos, phi_sub]
  apply mul_pos (by linarith)
  rcases hM.lt_or_eq with hM | hM
  · have : M * a < M * b := mul_lt_mul_of_pos_left hab hM
    linarith [ha.2, hb.2]
  · subst hM; simp; linarith

/-- F1: for M > 0 the maximum of φ is γ²/(2M), attained at γ/M. -/
theorem phi_le_max (hM : 0 < M) (s : ℝ) : phi γ M s ≤ γ ^ 2 / (2 * M) := by
  have : γ ^ 2 / (2 * M) - phi γ M s = M / 2 * (s - γ / M) ^ 2 := by
    simp only [phi]; field_simp; ring
  nlinarith [sq_nonneg (s - γ / M)]

theorem phi_vertex (hM : 0 < M) : phi γ M (γ / M) = γ ^ 2 / (2 * M) := by
  simp only [phi]; field_simp; ring

/-- F2: φ(s) ≥ γs/2 on [0, γ/M]. -/
theorem half_le_phi {s : ℝ} (hs : 0 ≤ s) (hMs : M * s ≤ γ) : γ * s / 2 ≤ phi γ M s := by
  simp only [phi]; nlinarith [mul_nonneg hs (sub_nonneg.2 hMs)]

section F3
variable {t : ℝ}

/-- Standing hypotheses of F3: 0 ≤ t ≤ γ²/(2M), encoded as `2 M t ≤ γ²`. -/
structure F3Hyp (γ M t : ℝ) : Prop where
  hγ : 0 < γ
  hM : 0 ≤ M
  ht : 0 ≤ t
  htM : 2 * M * t ≤ γ ^ 2

namespace F3Hyp
variable (h : F3Hyp γ M t)
include h

lemma disc_nonneg : 0 ≤ γ ^ 2 - 2 * M * t := by linarith [h.htM]
lemma sqrt_le : Real.sqrt (γ ^ 2 - 2 * M * t) ≤ γ := by
  rw [Real.sqrt_le_left h.hγ.le]; nlinarith [h.hM, h.ht]
lemma denom_pos : 0 < γ + Real.sqrt (γ ^ 2 - 2 * M * t) := by
  have := Real.sqrt_nonneg (γ ^ 2 - 2 * M * t); linarith [h.hγ]
lemma sq_sqrt' : Real.sqrt (γ ^ 2 - 2 * M * t) ^ 2 = γ ^ 2 - 2 * M * t :=
  Real.sq_sqrt h.disc_nonneg

/-- M · s₋(t) = γ − √(γ² − 2Mt) (valid also for M = 0). -/
lemma M_mul_sMinus : M * sMinus γ M t = γ - Real.sqrt (γ ^ 2 - 2 * M * t) := by
  have hd := h.denom_pos
  have hs := h.sq_sqrt'
  simp only [sMinus]
  rw [mul_div_assoc', div_eq_iff hd.ne']
  linear_combination hs

lemma sMinus_mul_denom : sMinus γ M t * (γ + Real.sqrt (γ ^ 2 - 2 * M * t)) = 2 * t := by
  simp only [sMinus]; exact div_mul_cancel₀ _ h.denom_pos.ne'

end F3Hyp

/-- F3: s₋(t) ≥ 0. -/
theorem sMinus_nonneg (h : F3Hyp γ M t) : 0 ≤ sMinus γ M t :=
  div_nonneg (by linarith [h.ht]) h.denom_pos.le

/-- F3: s₋(t) ∈ [0, γ/M]. -/
theorem sMinus_mem_Dom (h : F3Hyp γ M t) : sMinus γ M t ∈ Dom γ M :=
  ⟨sMinus_nonneg h, by rw [h.M_mul_sMinus]; linarith [Real.sqrt_nonneg (γ ^ 2 - 2 * M * t)]⟩

/-- F3: φ(s₋(t)) = t. -/
theorem phi_sMinus (h : F3Hyp γ M t) : phi γ M (sMinus γ M t) = t := by
  have h1 := h.M_mul_sMinus
  have h2 := h.sMinus_mul_denom
  have : phi γ M (sMinus γ M t) = sMinus γ M t * (γ - M * sMinus γ M t / 2) := by
    simp only [phi]; ring
  rw [this, h1]; linarith [h2]

/-- F3: s₋(t) is the unique solution of φ(s) = t in [0, γ/M]. -/
theorem eq_sMinus_of_phi_eq (h : F3Hyp γ M t) {s : ℝ} (hs : s ∈ Dom γ M)
    (hφ : phi γ M s = t) : s = sMinus γ M t :=
  (phi_strictMonoOn h.hγ h.hM).injOn hs (sMinus_mem_Dom h) (by rw [hφ, phi_sMinus h])

/-- F3 (M > 0): φ(s) = t iff s is one of the two roots (γ ∓ √(γ² − 2Mt))/M. -/
theorem phi_eq_iff_roots (h : F3Hyp γ M t) (hM : 0 < M) (s : ℝ) :
    phi γ M s = t ↔ s = (γ - Real.sqrt (γ ^ 2 - 2 * M * t)) / M ∨
      s = (γ + Real.sqrt (γ ^ 2 - 2 * M * t)) / M := by
  have hs := h.sq_sqrt'
  have key : phi γ M s = t ↔ (M * s - γ) ^ 2 = Real.sqrt (γ ^ 2 - 2 * M * t) ^ 2 := by
    rw [hs]; simp only [phi]
    constructor
    · intro e; nlinarith [e]
    · intro e
      have : 2 * M * (γ * s - M / 2 * s ^ 2) = 2 * M * t := by nlinarith [e]
      have h2M : (2 * M) ≠ 0 := by positivity
      exact mul_left_cancel₀ h2M this
  rw [key, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro (e | e)
    · right; field_simp; linarith
    · left; field_simp; linarith
  · rintro (e | e)
    · right; rw [e]; field_simp; ring
    · left; rw [e]; field_simp; ring

/-- F3 (M > 0): the smaller root equals s₋(t). -/
theorem sMinus_eq_smaller_root (h : F3Hyp γ M t) (hM : 0 < M) :
    sMinus γ M t = (γ - Real.sqrt (γ ^ 2 - 2 * M * t)) / M := by
  rw [eq_div_iff hM.ne', mul_comm, h.M_mul_sMinus]

/-- F3 (M > 0): the larger root is ≥ γ/M, with equality iff t = γ²/(2M). -/
theorem larger_root_ge (h : F3Hyp γ M t) (hM : 0 < M) :
    γ / M ≤ (γ + Real.sqrt (γ ^ 2 - 2 * M * t)) / M ∧
    ((γ + Real.sqrt (γ ^ 2 - 2 * M * t)) / M = γ / M ↔ t = γ ^ 2 / (2 * M)) := by
  refine ⟨div_le_div_of_nonneg_right (by linarith [Real.sqrt_nonneg (γ ^ 2 - 2 * M * t)]) hM.le,
    ?_⟩
  rw [div_left_inj' hM.ne', add_eq_left, Real.sqrt_eq_zero h.disc_nonneg]
  constructor
  · intro e; field_simp; linarith
  · intro e; rw [e]; field_simp; ring

/-- F3 (M = 0): s₋(t) = t/γ. -/
theorem sMinus_M_zero (hγ : 0 < γ) (t : ℝ) : sMinus γ 0 t = t / γ := by
  simp only [sMinus]
  rw [show γ ^ 2 - 2 * 0 * t = γ ^ 2 by ring, Real.sqrt_sq hγ.le]
  field_simp; ring

/-- F3 consequence: for s ∈ [0, γ/M], φ(s) ≤ t ⇔ s ≤ s₋(t). -/
theorem phi_le_iff (h : F3Hyp γ M t) {s : ℝ} (hs : s ∈ Dom γ M) :
    phi γ M s ≤ t ↔ s ≤ sMinus γ M t := by
  conv_lhs => rw [← phi_sMinus h]
  exact (phi_strictMonoOn h.hγ h.hM).le_iff_le hs (sMinus_mem_Dom h)

/-- F3 consequence: for s′ ∈ [0, γ/M], s₋(t) < s′ ⇔ t < φ(s′). -/
theorem sMinus_lt_iff (h : F3Hyp γ M t) {s' : ℝ} (hs : s' ∈ Dom γ M) :
    sMinus γ M t < s' ↔ t < phi γ M s' := by
  conv_rhs => rw [← phi_sMinus h]
  exact ((phi_strictMonoOn h.hγ h.hM).lt_iff_lt (sMinus_mem_Dom h) hs).symm

/-- F3 consequence (via F2): s₋(t) ≤ 2t/γ. -/
theorem sMinus_le_two_div (h : F3Hyp γ M t) : sMinus γ M t ≤ 2 * t / γ := by
  have h1 := half_le_phi (sMinus_mem_Dom h).1 (sMinus_mem_Dom h).2
  rw [phi_sMinus h] at h1
  rw [le_div_iff₀ h.hγ]; linarith

end F3

/-- Monotonicity of s₋: strictly increasing on [0, γ²/(2M)]. -/
theorem sMinus_strictMonoOn (hγ : 0 < γ) (hM : 0 ≤ M) :
    StrictMonoOn (sMinus γ M) {t | 0 ≤ t ∧ 2 * M * t ≤ γ ^ 2} := by
  intro a ha b hb hab
  have hA : F3Hyp γ M a := ⟨hγ, hM, ha.1, ha.2⟩
  have hB : F3Hyp γ M b := ⟨hγ, hM, hb.1, hb.2⟩
  rw [← (phi_strictMonoOn hγ hM).lt_iff_lt (sMinus_mem_Dom hA) (sMinus_mem_Dom hB),
    phi_sMinus hA, phi_sMinus hB]
  exact hab

/-! ## Part B. The scalar monotonicity step S6.2 -/

/-- S6.2: ψ(s) := s − αφ(s) is nondecreasing on [0, ρ] when αγ ≤ 1. -/
theorem psi_le (hM : 0 ≤ M) {α s ρ : ℝ} (hα : 0 ≤ α) (hαγ : α * γ ≤ 1)
    (hs : 0 ≤ s) (hsρ : s ≤ ρ) : s - α * phi γ M s ≤ ρ - α * phi γ M ρ := by
  have e : (ρ - α * phi γ M ρ) - (s - α * phi γ M s) =
      (ρ - s) * ((1 - α * γ) + α * M * (ρ + s) / 2) := by simp only [phi]; ring
  have : 0 ≤ (ρ - s) * ((1 - α * γ) + α * M * (ρ + s) / 2) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ α * M * (ρ + s) := mul_nonneg (mul_nonneg hα hM) (by linarith)
    linarith
  linarith

/-- S6.2, conclusion: s − αφ(s) + α‖g‖ ≤ ρ − α(φ(ρ) − ‖g‖); hence ≤ ρ if ‖g‖ ≤ φ(ρ), and
< ρ if ‖g‖ < φ(ρ) and α > 0. -/
theorem psi_bound (hM : 0 ≤ M) {α s ρ G : ℝ} (hα : 0 ≤ α) (hαγ : α * γ ≤ 1)
    (hs : 0 ≤ s) (hsρ : s ≤ ρ) :
    s - α * phi γ M s + α * G ≤ ρ - α * (phi γ M ρ - G) := by
  have := psi_le hM hα hαγ hs hsρ; linarith

/-! ## Part C. Constant arithmetic of Corollary 7 -/

/-- Cor. 7 radius r = min{R, γ/(2M)} (M > 0, R finite) satisfies M r ≤ γ/2. -/
theorem M_mul_min_le (hM : 0 < M) (R : ℝ) : M * min R (γ / (2 * M)) ≤ γ / 2 := by
  calc M * min R (γ / (2 * M)) ≤ M * (γ / (2 * M)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) hM.le
    _ = γ / 2 := by field_simp

/-- Cor. 7(i) / Remark 2.4: M r ≤ γ/2 ⇒ κ(r) ≥ γ/2. -/
theorem kappa_ge_half {r : ℝ} (hr : M * r ≤ γ / 2) : γ / 2 ≤ kappa γ M r := by
  simp only [kappa]; linarith

/-- Remark 2.4: if M > 0 and R ≥ γ/(2M) then κ(r) = γ/2 exactly. -/
theorem kappa_min_eq_half (hM : 0 < M) {R : ℝ} (hR : γ / (2 * M) ≤ R) :
    kappa γ M (min R (γ / (2 * M))) = γ / 2 := by
  rw [min_eq_right hR]; simp only [kappa]; field_simp; ring

/-- Cor. 7(iii): M r ≤ γ/2, r ≥ 0 ⇒ φ(r) ≥ (3/4)γr ≥ γr/4. -/
theorem phi_ge_three_quarters (hγ : 0 < γ) {r : ℝ} (hr0 : 0 ≤ r) (hr : M * r ≤ γ / 2) :
    3 / 4 * γ * r ≤ phi γ M r ∧ γ * r / 4 ≤ 3 / 4 * γ * r := by
  constructor
  · simp only [phi]; nlinarith [mul_nonneg hr0 (by linarith : 0 ≤ γ / 2 - M * r)]
  · nlinarith [mul_nonneg hγ.le hr0]

/-- Cor. 7(iii), the constants: if 0 < r, Mr ≤ γ/2, 0 ≤ t < φ(r), then s₋(t) < r; for every
ρ ∈ [s₋(t), r]: ρ ∈ [0, γ/M) (so (H4) holds once ρ > 0), t ≤ φ(ρ), κ(ρ) ≥ γ/2, and the
contraction factor 1 − ακ(ρ) ≤ 1 − αγ/2 for α ≥ 0. -/
theorem cor7_iii_constants (hγ : 0 < γ) (hM : 0 ≤ M) {r t : ℝ} (hr0 : 0 < r)
    (hr : M * r ≤ γ / 2) (ht : 0 ≤ t) (htr : t < phi γ M r) :
    F3Hyp γ M t ∧ sMinus γ M t < r ∧
    ∀ ρ, sMinus γ M t ≤ ρ → ρ ≤ r →
      M * ρ < γ ∧ t ≤ phi γ M ρ ∧ γ / 2 ≤ kappa γ M ρ ∧
      ∀ α, 0 ≤ α → 1 - α * kappa γ M ρ ≤ 1 - α * γ / 2 := by
  have hrD : r ∈ Dom γ M := ⟨hr0.le, by linarith⟩
  have hF : F3Hyp γ M t := by
    refine ⟨hγ, hM, ht, ?_⟩
    rcases hM.lt_or_eq with hM' | hM'
    · have := phi_le_max (γ := γ) hM' r
      have : 2 * M * t ≤ 2 * M * (γ ^ 2 / (2 * M)) := by nlinarith
      rwa [show 2 * M * (γ ^ 2 / (2 * M)) = γ ^ 2 by field_simp] at this
    · subst hM'; simp; positivity
  refine ⟨hF, (sMinus_lt_iff hF hrD).2 htr, fun ρ h1 h2 => ?_⟩
  have hρ0 : 0 ≤ ρ := le_trans (sMinus_nonneg hF) h1
  have hMρ : M * ρ ≤ M * r := mul_le_mul_of_nonneg_left h2 hM
  have hρD : ρ ∈ Dom γ M := ⟨hρ0, by linarith⟩
  refine ⟨by linarith, ?_, by simp only [kappa]; linarith, fun α hα => ?_⟩
  · rw [← phi_sMinus hF]; exact (phi_strictMonoOn hγ hM).monotoneOn (sMinus_mem_Dom hF) hρD h1
  · have : γ / 2 ≤ kappa γ M ρ := by simp only [kappa]; linarith
    nlinarith

/-- Cor. 7(iv), the constants: under the spine's ‖g‖ < γr/4 (0 < r, Mr ≤ γ/2):
s₋(t) ≤ 2t/γ < r/2 < r, φ(r/2) ≥ 7γr/16 > γr/4 > t, κ(r/2) ≥ (3/4)γ, and the factor
1 − ακ(r/2) ≤ 1 − (3/4)αγ for α ≥ 0. -/
theorem cor7_iv_constants (hγ : 0 < γ) (hM : 0 ≤ M) {r t : ℝ} (hr0 : 0 < r)
    (hr : M * r ≤ γ / 2) (ht : 0 ≤ t) (htr : t < γ * r / 4) :
    F3Hyp γ M t ∧ sMinus γ M t ≤ 2 * t / γ ∧ 2 * t / γ < r / 2 ∧ r / 2 < r ∧
    7 * γ * r / 16 ≤ phi γ M (r / 2) ∧ γ * r / 4 < 7 * γ * r / 16 ∧ t < phi γ M (r / 2) ∧
    M * (r / 2) < γ ∧ 3 / 4 * γ ≤ kappa γ M (r / 2) ∧
    ∀ α, 0 ≤ α → 1 - α * kappa γ M (r / 2) ≤ 1 - 3 / 4 * α * γ := by
  have hF : F3Hyp γ M t := by
    refine ⟨hγ, hM, ht, ?_⟩
    have : M * t ≤ M * (γ * r / 4) := mul_le_mul_of_nonneg_left htr.le hM
    nlinarith [mul_le_mul_of_nonneg_left hr hγ.le]
  have h7 : 7 * γ * r / 16 ≤ phi γ M (r / 2) := by
    simp only [phi]; nlinarith [mul_le_mul_of_nonneg_left hr hr0.le]
  have hgr : γ * r / 4 < 7 * γ * r / 16 := by nlinarith [mul_pos hγ hr0]
  refine ⟨hF, sMinus_le_two_div hF, ?_, by linarith, h7, hgr, by linarith, by linarith,
    by simp only [kappa]; linarith, fun α hα => ?_⟩
  · rw [div_lt_iff₀ hγ]; nlinarith
  · have : 3 / 4 * γ ≤ kappa γ M (r / 2) := by simp only [kappa]; linarith
    nlinarith

end Algebra

/-! ## Part D. Lemma 1 (curvature floor), quadratic-form version -/

section Core
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- S0.1: (H3) on the open ball extends to the closed ball, for a continuous Hessian field. -/
theorem hessVar_closed {H : X → X →L[ℝ] X} (hH : Continuous H) {xbar : X} {R : ℝ≥0∞} {M : ℝ}
    (hR : 0 < R)
    (hvar : ∀ x, ENNReal.ofReal ‖x - xbar‖ < R → ‖H x - H xbar‖ ≤ M * ‖x - xbar‖)
    {x : X} (hx : ENNReal.ofReal ‖x - xbar‖ ≤ R) : ‖H x - H xbar‖ ≤ M * ‖x - xbar‖ := by
  rcases eq_or_ne R ⊤ with rfl | hRt
  · exact hvar x ENNReal.ofReal_lt_top
  have hR' : 0 < R.toReal := ENNReal.toReal_pos hR.ne' hRt
  have hsub : ball xbar R.toReal ⊆ {x | ‖H x - H xbar‖ ≤ M * ‖x - xbar‖} := by
    intro y hy
    rw [mem_ball, dist_eq_norm] at hy
    exact hvar y ((ENNReal.ofReal_lt_iff_lt_toReal (norm_nonneg _) hRt).2 hy)
  have hcl : IsClosed {x | ‖H x - H xbar‖ ≤ M * ‖x - xbar‖} :=
    isClosed_le ((hH.sub continuous_const).norm)
      (continuous_const.mul ((continuous_id.sub continuous_const).norm))
  have := closure_minimal hsub hcl
  rw [closure_ball xbar hR'.ne'] at this
  apply this
  rw [mem_closedBall, dist_eq_norm]
  exact (ENNReal.ofReal_le_iff_le_toReal hRt).1 hx

/-- **Lemma 1 (curvature floor), quadratic-form form.** If the form of H(x̄) is bounded below
by γ (i.e. γ ≤ λ_min(H(x̄)) by Rayleigh), (H3) holds on B(x̄, R) and H is continuous, then for
every x with ‖x − x̄‖ ≤ R: ⟨H(x)u, u⟩ ≥ (γ − M‖x − x̄‖)‖u‖² for all u. -/
theorem curvature_floor {H : X → X →L[ℝ] X} (hH : Continuous H) {xbar : X} {R : ℝ≥0∞}
    {γ M : ℝ} (hR : 0 < R)
    (hγ : ∀ u, γ * ‖u‖ ^ 2 ≤ ⟪H xbar u, u⟫)
    (hvar : ∀ x, ENNReal.ofReal ‖x - xbar‖ < R → ‖H x - H xbar‖ ≤ M * ‖x - xbar‖)
    {x : X} (hx : ENNReal.ofReal ‖x - xbar‖ ≤ R) (u : X) :
    (γ - M * ‖x - xbar‖) * ‖u‖ ^ 2 ≤ ⟪H x u, u⟫ := by
  have h1 := hessVar_closed hH hR hvar hx
  have h2 : |⟪(H x - H xbar) u, u⟫| ≤ ‖H x - H xbar‖ * ‖u‖ ^ 2 := by
    calc |⟪(H x - H xbar) u, u⟫| ≤ ‖(H x - H xbar) u‖ * ‖u‖ := abs_real_inner_le_norm _ _
      _ ≤ (‖H x - H xbar‖ * ‖u‖) * ‖u‖ := by
          gcongr; exact (H x - H xbar).le_opNorm u
      _ = _ := by ring
  have h3 : ⟪H x u, u⟫ = ⟪H xbar u, u⟫ + ⟪(H x - H xbar) u, u⟫ := by
    simp [inner_sub_left]
  have h4 := neg_abs_le ⟪(H x - H xbar) u, u⟫
  have h5 : ‖H x - H xbar‖ * ‖u‖ ^ 2 ≤ M * ‖x - xbar‖ * ‖u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
  rw [h3]; nlinarith [hγ u]

/-- Lemma 1, second sentence: for finite ρ ≤ R, the form of H(z) is ≥ κ(ρ)‖u‖² on B̄(x̄, ρ). -/
theorem curvature_floor_ball {H : X → X →L[ℝ] X} (hH : Continuous H) {xbar : X} {R : ℝ≥0∞}
    {γ M ρ : ℝ} (hR : 0 < R) (hM : 0 ≤ M)
    (hγ : ∀ u, γ * ‖u‖ ^ 2 ≤ ⟪H xbar u, u⟫)
    (hvar : ∀ x, ENNReal.ofReal ‖x - xbar‖ < R → ‖H x - H xbar‖ ≤ M * ‖x - xbar‖)
    (hρR : ENNReal.ofReal ρ ≤ R) {z : X} (hz : z ∈ closedBall xbar ρ) (u : X) :
    kappa γ M ρ * ‖u‖ ^ 2 ≤ ⟪H z u, u⟫ := by
  rw [mem_closedBall, dist_eq_norm] at hz
  have hzR : ENNReal.ofReal ‖z - xbar‖ ≤ R := le_trans (ENNReal.ofReal_le_ofReal hz) hρR
  have := curvature_floor hH hR hγ hvar hzR u
  have : kappa γ M ρ * ‖u‖ ^ 2 ≤ (γ - M * ‖z - xbar‖) * ‖u‖ ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    simp only [kappa]; nlinarith
  linarith

/-! ## Part E. The C² setting: Hessian field, segment estimates, Lemma 3 -/

/-- Integration along [0, 1] by monotonicity: F′ ≤ K′ on [0,1] ⇒ F 1 − F 0 ≤ K 1 − K 0. -/
lemma sub_le_sub_of_hasDerivAt_le {F K F' K' : ℝ → ℝ}
    (hF : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt F (F' t) t)
    (hK : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt K (K' t) t)
    (h : ∀ t ∈ Icc (0:ℝ) 1, F' t ≤ K' t) : F 1 - F 0 ≤ K 1 - K 0 := by
  have hm : MonotoneOn (fun t => K t - F t) (Icc 0 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    · intro t ht; exact ((hK t ht).sub (hF t ht)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact ((hK t (Ioo_subset_Icc_self ht)).sub
        (hF t (Ioo_subset_Icc_self ht))).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have hd : HasDerivAt (fun t => K t - F t) (K' t - F' t) t :=
        (hK t (Ioo_subset_Icc_self ht)).sub (hF t (Ioo_subset_Icc_self ht))
      rw [hd.deriv]
      linarith [h t (Ioo_subset_Icc_self ht)]
  have := hm (left_mem_Icc.2 zero_le_one) (right_mem_Icc.2 zero_le_one) zero_le_one
  simp only at this; linarith

/-- A symmetric operator B with 0 ≤ ⟨Bu,u⟩ ≤ c‖u‖² satisfies ⟨Bh, w⟩ ≤ c‖h‖‖w‖ (this is the
quadratic-form replacement for ‖B‖ ≤ c; no eigenvalues). -/
lemma inner_le_of_form_bounds (B : X →L[ℝ] X) (hsym : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫) {c : ℝ}
    (hpos : ∀ u, 0 ≤ ⟪B u, u⟫) (hup : ∀ u, ⟪B u, u⟫ ≤ c * ‖u‖ ^ 2) (h w : X) :
    ⟪B h, w⟫ ≤ c * ‖h‖ * ‖w‖ := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  have hnh : 0 < ‖h‖ := norm_pos_iff.2 hh
  have hnw : 0 < ‖w‖ := norm_pos_iff.2 hw
  have key := hpos (‖w‖ • h - ‖h‖ • w)
  have hs := hsym w h
  rw [real_inner_comm (B h) w] at hs
  have e : ⟪B (‖w‖ • h - ‖h‖ • w), ‖w‖ • h - ‖h‖ • w⟫ = ‖w‖ ^ 2 * ⟪B h, h⟫
      - 2 * (‖w‖ * ‖h‖) * ⟪B h, w⟫ + ‖h‖ ^ 2 * ⟪B w, w⟫ := by
    simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    rw [hs]; ring
  rw [e] at key
  have h1 := mul_le_mul_of_nonneg_left (hup h) (sq_nonneg ‖w‖)
  have h2 := mul_le_mul_of_nonneg_left (hup w) (sq_nonneg ‖h‖)
  have h3 : 2 * (‖w‖ * ‖h‖) * ⟪B h, w⟫ ≤ 2 * (‖w‖ * ‖h‖) * (c * ‖h‖ * ‖w‖) := by nlinarith
  exact le_of_mul_le_mul_left h3 (by positivity)

lemma hasDerivAt_line (p d : X) (t : ℝ) : HasDerivAt (fun t : ℝ => p + t • d) d t := by
  simpa using ((hasDerivAt_id t).smul_const d).const_add p

lemma hasDerivAt_inner_left (w : X) {f : ℝ → X} {f' : X} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => ⟪w, f s⟫) ⟪w, f'⟫ t := by
  have := (innerSL ℝ w).hasFDerivAt.comp_hasDerivAt t hf
  simp only [Function.comp_def, innerSL_apply_apply] at this
  exact this

lemma hasDerivAt_quad (a b t : ℝ) : HasDerivAt (fun t : ℝ => a * t + b * t ^ 2) (a + 2 * b * t) t := by
  have h1 : HasDerivAt (fun x : ℝ => a * x) a t := by
    simpa using (hasDerivAt_id t).const_mul a
  have h2 : HasDerivAt (fun x : ℝ => b * x ^ 2) (b * (2 * t)) t := by
    simpa using (hasDerivAt_pow 2 t).const_mul b
  have h3 : HasDerivAt (fun x => a * x + b * x ^ 2) (a + b * (2 * t)) t := h1.add h2
  rw [show a + 2 * b * t = a + b * (2 * t) by ring]
  exact h3

variable [CompleteSpace X]

/-- The Hessian field ∇²E := D(∇E) (an operator X →L X; on ℝᵈ its operator norm is the spectral
norm). -/
noncomputable def hess (E : X → ℝ) (x : X) : X →L[ℝ] X := fderiv ℝ (gradient E) x

section Smooth
variable {E : X → ℝ} (hE : ContDiff ℝ 2 E)
include hE

lemma contDiff_gradient : ContDiff ℝ 1 (gradient E) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ E) := hE.fderiv_right (by norm_num)
  have hg : gradient E = (InnerProductSpace.toDual ℝ X).symm ∘ fderiv ℝ E := rfl
  rw [hg]
  exact (InnerProductSpace.toDual ℝ X).symm.contDiff.comp h1

lemma hasFDerivAt_gradient (x : X) : HasFDerivAt (gradient E) (hess E x) x :=
  ((contDiff_gradient hE).differentiable one_ne_zero x).hasFDerivAt

lemma continuous_hess : Continuous (hess E) :=
  (contDiff_gradient hE).continuous_fderiv one_ne_zero

/-- The Hessian is symmetric (Schwarz), from C². -/
lemma hess_symm (x u v : X) : ⟪hess E x u, v⟫ = ⟪u, hess E x v⟫ := by
  have hD : HasFDerivAt (fderiv ℝ E) (fderiv ℝ (fderiv ℝ E) x) x :=
    ((hE.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt
  have key : ∀ a b : X, ⟪b, hess E x a⟫ = fderiv ℝ (fderiv ℝ E) x a b := by
    intro a b
    have hfun : (fun y => ⟪b, gradient E y⟫) = fun y => fderiv ℝ E y b := by
      funext y; rw [real_inner_comm, inner_gradient_left]
    have d1 : HasFDerivAt (fun y => ⟪b, gradient E y⟫) ((innerSL ℝ b).comp (hess E x)) x :=
      (innerSL ℝ b).hasFDerivAt.comp x (hasFDerivAt_gradient hE x)
    have d2 : HasFDerivAt (fun y => fderiv ℝ E y b)
        ((ContinuousLinearMap.apply ℝ ℝ b).comp (fderiv ℝ (fderiv ℝ E) x)) x :=
      (ContinuousLinearMap.apply ℝ ℝ b).hasFDerivAt.comp x hD
    rw [← hfun] at d2
    have := congrArg (fun L : X →L[ℝ] ℝ => L a) (d1.unique d2)
    simpa using this
  have hs : IsSymmSndFDerivAt ℝ E x := hE.contDiffAt.isSymmSndFDerivAt (by simp)
  rw [real_inner_comm, key, key]
  exact hs u v

lemma hasDerivAt_grad_line (p d : X) (t : ℝ) :
    HasDerivAt (fun t : ℝ => gradient E (p + t • d)) (hess E (p + t • d) d) t :=
  (hasFDerivAt_gradient hE _).comp_hasDerivAt t (hasDerivAt_line p d t)

lemma hasDerivAt_E_line (p d : X) (t : ℝ) :
    HasDerivAt (fun t : ℝ => E (p + t • d)) ⟪gradient E (p + t • d), d⟫ t := by
  have h := ((hE.differentiable two_ne_zero) (p + t • d)).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_line p d t)
  rwa [← inner_gradient_left] at h

/-- **Segment estimate** (replaces the vector-valued integral Ā of S3.4–S3.7 by scalar
monotonicity). If along p + t d, t ∈ [0,1], the operator B_t := I − α∇²E(p + t d) satisfies
0 ≤ ⟨B_t u, u⟩ ≤ (a + b t)‖u‖², then ‖d − α(∇E(p + d) − ∇E(p))‖ ≤ (a + b/2)‖d‖. -/
theorem seg_bound {p d : X} {α a b : ℝ}
    (hB : ∀ t ∈ Icc (0:ℝ) 1, ∀ u, α * ⟪hess E (p + t • d) u, u⟫ ≤ ‖u‖ ^ 2 ∧
       ‖u‖ ^ 2 - α * ⟪hess E (p + t • d) u, u⟫ ≤ (a + b * t) * ‖u‖ ^ 2) :
    ‖d - α • (gradient E (p + d) - gradient E p)‖ ≤ (a + b / 2) * ‖d‖ := by
  set w := d - α • (gradient E (p + d) - gradient E p) with hw
  have hpt : ∀ t ∈ Icc (0:ℝ) 1,
      ⟪w, d - α • hess E (p + t • d) d⟫ ≤ (a + b * t) * ‖d‖ * ‖w‖ := by
    intro t ht
    let B : X →L[ℝ] X := ContinuousLinearMap.id ℝ X - α • hess E (p + t • d)
    have hBu : ∀ u, ⟪B u, u⟫ = ‖u‖ ^ 2 - α * ⟪hess E (p + t • d) u, u⟫ := by
      intro u
      simp [B, inner_sub_left, real_inner_smul_left]
    have hsym : ∀ u v, ⟪B u, v⟫ = ⟪u, B v⟫ := by
      intro u v
      simp only [B, sub_apply, ContinuousLinearMap.id_apply, smul_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
        real_inner_smul_right, hess_symm hE]
    have := inner_le_of_form_bounds B hsym
      (fun u => by rw [hBu]; linarith [(hB t ht u).1]) (fun u => by rw [hBu]; exact (hB t ht u).2)
      d w
    rw [real_inner_comm]
    simpa [B] using this
  have hF : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt
      (fun t : ℝ => ⟪w, t • d - α • (gradient E (p + t • d) - gradient E p)⟫)
      ⟪w, d - α • hess E (p + t • d) d⟫ t := by
    intro t _
    have ha : HasDerivAt (fun t : ℝ => t • d) d t := by
      simpa only [id, one_smul] using (hasDerivAt_id t).smul_const d
    have hb := ((hasDerivAt_grad_line hE p d t).sub_const (gradient E p)).const_smul α
    exact hasDerivAt_inner_left w (ha.sub hb)
  have hK : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => (a * t + b / 2 * t ^ 2) * ‖d‖ * ‖w‖)
      ((a + b * t) * ‖d‖ * ‖w‖) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => a * t + b / 2 * t ^ 2) (a + b * t) t := by
      have := hasDerivAt_quad a (b / 2) t
      rwa [show a + 2 * (b / 2) * t = a + b * t by ring] at this
    exact (h1.mul_const _).mul_const _
  have main := sub_le_sub_of_hasDerivAt_le hF hK hpt
  simp only [one_smul, zero_smul, add_zero, sub_self, smul_zero,
    inner_zero_right, sub_zero, one_pow, mul_one, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at main
  rw [← hw, real_inner_self_eq_norm_sq] at main
  -- main : ‖w‖^2 ≤ (a + b/2) * ‖d‖ * ‖w‖
  rcases (norm_nonneg w).lt_or_eq with hpos | hzero
  · have : ‖w‖ * ‖w‖ ≤ ((a + b / 2) * ‖d‖) * ‖w‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]
    rcases eq_or_ne d 0 with hd | hd
    · simp [hd]
    have hnd : 0 < ‖d‖ ^ 2 := by positivity
    have h0 := hB 0 (left_mem_Icc.2 zero_le_one) d
    have h1 := hB 1 (right_mem_Icc.2 zero_le_one) d
    have ha : 0 ≤ a := by
      have : 0 ≤ (a + b * 0) * ‖d‖ ^ 2 := by linarith [h0.1, h0.2]
      simpa using nonneg_of_mul_nonneg_left this hnd
    have hab : 0 ≤ a + b := by
      have : 0 ≤ (a + b * 1) * ‖d‖ ^ 2 := by linarith [h1.1, h1.2]
      simpa using nonneg_of_mul_nonneg_left this hnd
    have : 0 ≤ a + b / 2 := by linarith
    positivity

end Smooth

/-! ### The standing hypotheses (H1)–(H3) -/

/-- (H1) E ∈ C²; (H2) γ > 0 with ⟨∇²E(x̄)u, u⟩ ≥ γ‖u‖² (Rayleigh form of γ ≤ λ_min(∇²E(x̄));
the dossier's γ = λ_min satisfies it); (H3) R ∈ (0, ∞], M ≥ 0 and
‖∇²E(x) − ∇²E(x̄)‖ ≤ M‖x − x̄‖ on B(x̄, R) (R = ⊤ is R = ∞, B(x̄, ∞) = X). -/
structure Hyp (E : X → ℝ) (xbar : X) (γ M : ℝ) (R : ℝ≥0∞) : Prop where
  smooth : ContDiff ℝ 2 E
  hγ : 0 < γ
  floor : ∀ u, γ * ‖u‖ ^ 2 ≤ ⟪hess E xbar u, u⟫
  hR : 0 < R
  hM : 0 ≤ M
  var : ∀ x, ENNReal.ofReal ‖x - xbar‖ < R → ‖hess E x - hess E xbar‖ ≤ M * ‖x - xbar‖

namespace Hyp
variable {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞} (h : Hyp E xbar γ M R)
include h

/-- Lemma 1 for the Hessian of E. -/
theorem floor_pt {x : X} (hx : ENNReal.ofReal ‖x - xbar‖ ≤ R) (u : X) :
    (γ - M * ‖x - xbar‖) * ‖u‖ ^ 2 ≤ ⟪hess E x u, u⟫ :=
  curvature_floor (continuous_hess h.smooth) h.hR h.floor h.var hx u

theorem floor_ball {ρ : ℝ} (hρR : ENNReal.ofReal ρ ≤ R) {z : X} (hz : z ∈ closedBall xbar ρ)
    (u : X) : kappa γ M ρ * ‖u‖ ^ 2 ≤ ⟪hess E z u, u⟫ :=
  curvature_floor_ball (continuous_hess h.smooth) h.hR h.hM h.floor h.var hρR hz u

/-- **Lemma 2(b)** (strong monotonicity on the closed ball; no positivity of κ needed for the
inequality itself): for finite ρ ≤ R, ⟨∇E x − ∇E y, x − y⟩ ≥ κ(ρ)‖x − y‖² on B̄(x̄, ρ). -/
theorem strongMono {ρ : ℝ} (hρR : ENNReal.ofReal ρ ≤ R) {x y : X}
    (hx : x ∈ closedBall xbar ρ) (hy : y ∈ closedBall xbar ρ) :
    kappa γ M ρ * ‖x - y‖ ^ 2 ≤ ⟪gradient E x - gradient E y, x - y⟫ := by
  set d := x - y
  have hF : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => ⟪d, gradient E (y + t • d)⟫)
      ⟪d, hess E (y + t • d) d⟫ t := by
    intro t _
    exact hasDerivAt_inner_left d (hasDerivAt_grad_line h.smooth y d t)
  have hK : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => kappa γ M ρ * ‖d‖ ^ 2 * t)
      (kappa γ M ρ * ‖d‖ ^ 2) t := fun t _ => by simpa using (hasDerivAt_id t).const_mul _
  have hle : ∀ t ∈ Icc (0:ℝ) 1, kappa γ M ρ * ‖d‖ ^ 2 ≤ ⟪d, hess E (y + t • d) d⟫ := by
    intro t ht
    rw [real_inner_comm]
    exact h.floor_ball hρR ((convex_closedBall xbar ρ).add_smul_sub_mem hy hx ht) d
  have := sub_le_sub_of_hasDerivAt_le hK hF hle
  simp only [one_smul, zero_smul, add_zero, mul_one, mul_zero, sub_zero] at this
  rw [show y + d = x by simp [d]] at this
  rw [real_inner_comm d, inner_sub_right]
  linarith

/-- **Lemma 3(a)** (ray estimate): for ‖x − x̄‖ = s ≤ R (s finite),
⟨∇E(x) − ∇E(x̄), x − x̄⟩ ≥ s·φ(s) = (γ − Ms/2)s². -/
theorem ray_lower {x : X} (hx : ENNReal.ofReal ‖x - xbar‖ ≤ R) :
    ‖x - xbar‖ * phi γ M ‖x - xbar‖ ≤ ⟪gradient E x - gradient E xbar, x - xbar⟫ := by
  set d := x - xbar
  set s := ‖d‖
  have hF : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => ⟪d, gradient E (xbar + t • d)⟫)
      ⟪d, hess E (xbar + t • d) d⟫ t := by
    intro t _
    exact hasDerivAt_inner_left d (hasDerivAt_grad_line h.smooth xbar d t)
  have hK : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => (γ * t - M * s / 2 * t ^ 2) * s ^ 2)
      ((γ - M * s * t) * s ^ 2) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => γ * t - M * s / 2 * t ^ 2) (γ - M * s * t) t := by
      have := hasDerivAt_quad γ (-(M * s / 2)) t
      rw [show γ + 2 * -(M * s / 2) * t = γ - M * s * t by ring] at this
      convert this using 2; ring
    exact h1.mul_const _
  have hle : ∀ t ∈ Icc (0:ℝ) 1, (γ - M * s * t) * s ^ 2 ≤ ⟪d, hess E (xbar + t • d) d⟫ := by
    intro t ht
    have hn : ‖xbar + t • d - xbar‖ = t * s := by
      simp [norm_smul, abs_of_nonneg ht.1, s]
    have hz : ENNReal.ofReal ‖xbar + t • d - xbar‖ ≤ R := by
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hx
      rw [hn]; exact mul_le_of_le_one_left (norm_nonneg _) ht.2
    have := h.floor_pt hz d
    rw [hn] at this
    rw [real_inner_comm]
    linarith [show M * s * t = M * (t * s) by ring]
  have := sub_le_sub_of_hasDerivAt_le hK hF hle
  simp only [one_smul, zero_smul, add_zero, mul_one, mul_zero, sub_zero, one_pow, zero_mul,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at this
  rw [show xbar + d = x by simp [d]] at this
  rw [real_inner_comm d, inner_sub_right]
  have e : s * phi γ M s = (γ - M * s / 2) * s ^ 2 := by simp only [phi]; ring
  rw [e]; linarith

/-- **Lemma 3(b)** (ray step estimate), with the step condition in its pointwise form
α‖∇²E(z)‖ ≤ 1 on B̄(x̄, ρ) (equivalent to α ≤ 1/β_ρ, see `step_le_inv_beta_iff`):
‖T_α x − x̄‖ ≤ s − αφ(s) + α‖∇E(x̄)‖ for s = ‖x − x̄‖ ≤ ρ ≤ R, ρ finite. -/
theorem ray_step' {x : X} {ρ α : ℝ} (hsρ : ‖x - xbar‖ ≤ ρ) (hρR : ENNReal.ofReal ρ ≤ R)
    (hα : 0 ≤ α) (hstep : ∀ z ∈ closedBall xbar ρ, α * ‖hess E z‖ ≤ 1) :
    ‖(x - α • gradient E x) - xbar‖ ≤
      ‖x - xbar‖ - α * phi γ M ‖x - xbar‖ + α * ‖gradient E xbar‖ := by
  set d := x - xbar with hd
  set s := ‖d‖
  have hseg := seg_bound h.smooth (p := xbar) (d := d) (α := α) (a := 1 - α * γ) (b := α * M * s)
    (by
      intro t ht u
      have hn : ‖xbar + t • d - xbar‖ = t * s := by
        simp [norm_smul, abs_of_nonneg ht.1, s]
      have hzb : xbar + t • d ∈ closedBall xbar ρ := by
        rw [mem_closedBall, dist_eq_norm, hn]
        exact le_trans (mul_le_of_le_one_left (norm_nonneg _) ht.2) hsρ
      have hz : ENNReal.ofReal ‖xbar + t • d - xbar‖ ≤ R := by
        refine le_trans (ENNReal.ofReal_le_ofReal ?_) hρR
        rw [mem_closedBall, dist_eq_norm] at hzb; exact hzb
      have hfl := h.floor_pt hz u
      rw [hn] at hfl
      have hup : ⟪hess E (xbar + t • d) u, u⟫ ≤ ‖hess E (xbar + t • d)‖ * ‖u‖ ^ 2 := by
        calc _ ≤ ‖hess E (xbar + t • d) u‖ * ‖u‖ := real_inner_le_norm _ _
          _ ≤ (‖hess E (xbar + t • d)‖ * ‖u‖) * ‖u‖ := by
            gcongr; exact (hess E _).le_opNorm u
          _ = _ := by ring
      have hs1 := hstep _ hzb
      constructor
      · have := mul_le_mul_of_nonneg_left hup hα
        nlinarith [sq_nonneg ‖u‖]
      · have := mul_le_mul_of_nonneg_left hfl hα
        nlinarith)
  rw [show xbar + d = x by simp [d]] at hseg
  have e : (x - α • gradient E x) - xbar =
      (d - α • (gradient E x - gradient E xbar)) - α • gradient E xbar := by
    simp only [d, smul_sub]; abel
  rw [e]
  calc ‖(d - α • (gradient E x - gradient E xbar)) - α • gradient E xbar‖
      ≤ ‖d - α • (gradient E x - gradient E xbar)‖ + ‖α • gradient E xbar‖ := norm_sub_le _ _
    _ ≤ (1 - α * γ + α * M * s / 2) * s + α * ‖gradient E xbar‖ := by
        rw [norm_smul, Real.norm_of_nonneg hα]; linarith
    _ = s - α * phi γ M s + α * ‖gradient E xbar‖ := by simp only [phi]; ring

end Hyp

/-! ## Part F. β_ρ, the uniqueness ball U = B(x̄, r₀), and Proposition 4 -/

/-- β_ρ := max over B̄(x̄, ρ) of ‖∇²E‖ (as a supremum; attained, see `Hyp.beta_attained`). -/
noncomputable def beta (E : X → ℝ) (xbar : X) (ρ : ℝ) : ℝ :=
  sSup ((fun z => ‖hess E z‖) '' closedBall xbar ρ)

/-- r₀ := min{R, γ/M} in [0, ∞], with γ/0 = ∞ (for γ > 0). -/
noncomputable def r0 (R : ℝ≥0∞) (γ M : ℝ) : ℝ≥0∞ := min R (ENNReal.ofReal γ / ENNReal.ofReal M)

/-- U := B(x̄, r₀). -/
def U (xbar : X) (R : ℝ≥0∞) (γ M : ℝ) : Set X := {x | ENNReal.ofReal ‖x - xbar‖ < r0 R γ M}

/-- The existence condition ‖g‖ < φ(r₀), with φ(∞) := +∞ (r₀ = ∞ iff M = 0 and R = ∞). -/
def ExistCond (R : ℝ≥0∞) (γ M t : ℝ) : Prop := r0 R γ M = ⊤ ∨ t < phi γ M (r0 R γ M).toReal

lemma ofReal_lt_r0_iff {R : ℝ≥0∞} {γ M s : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (_hs : 0 ≤ s) :
    ENNReal.ofReal s < r0 R γ M ↔ ENNReal.ofReal s < R ∧ M * s < γ := by
  unfold r0
  rw [lt_min_iff]
  apply and_congr_right
  intro _
  rcases hM.lt_or_eq with hM' | hM'
  · rw [← ENNReal.ofReal_div_of_pos hM', ENNReal.ofReal_lt_ofReal_iff (div_pos hγ hM'),
      lt_div_iff₀ hM', mul_comm]
  · subst hM'
    simp only [ENNReal.ofReal_zero, zero_mul, hγ, iff_true]
    rw [ENNReal.div_zero (by simp [hγ])]
    exact ENNReal.ofReal_lt_top
omit [InnerProductSpace ℝ X] [CompleteSpace X] in

lemma isOpen_U (xbar : X) (R : ℝ≥0∞) (γ M : ℝ) : IsOpen (U xbar R γ M) :=
  isOpen_lt (ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const).norm)
    continuous_const

lemma existCond_spec {R : ℝ≥0∞} {γ M t : ℝ} (hγ : 0 < γ) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hc : ExistCond R γ M t) :
    F3Hyp γ M t ∧ ENNReal.ofReal (sMinus γ M t) < r0 R γ M := by
  rcases hc with htop | hlt
  · have h2 : ENNReal.ofReal γ / ENNReal.ofReal M = ⊤ := (min_eq_top.1 htop).2
    have hM0 : M = 0 := by
      rcases ENNReal.div_eq_top.1 h2 with ⟨_, h⟩ | ⟨h, _⟩
      · exact le_antisymm (ENNReal.ofReal_eq_zero.1 h) hM
      · exact absurd h ENNReal.ofReal_ne_top
    subst hM0
    exact ⟨⟨hγ, le_rfl, ht, by simp; positivity⟩, by rw [htop]; exact ENNReal.ofReal_lt_top⟩
  · have hne : r0 R γ M ≠ ⊤ := by
      intro h; rw [h] at hlt; simp [phi] at hlt; linarith
    set r := (r0 R γ M).toReal with hr
    have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
    have hrD : r ∈ Dom γ M := by
      refine ⟨hr0, ?_⟩
      rcases hM.lt_or_eq with hM' | hM'
      · have : r0 R γ M ≤ ENNReal.ofReal (γ / M) := by
          rw [ENNReal.ofReal_div_of_pos hM']; exact min_le_right _ _
        have := ENNReal.toReal_le_of_le_ofReal (div_pos hγ hM').le this
        rw [← hr] at this
        rw [le_div_iff₀ hM'] at this; linarith
      · subst hM'; simp; exact hγ.le
    have hF : F3Hyp γ M t := by
      refine ⟨hγ, hM, ht, ?_⟩
      rcases hM.lt_or_eq with hM' | hM'
      · have := phi_le_max (γ := γ) hM' r
        have h3 : 2 * M * t ≤ 2 * M * (γ ^ 2 / (2 * M)) := by nlinarith
        rwa [show 2 * M * (γ ^ 2 / (2 * M)) = γ ^ 2 by field_simp] at h3
      · subst hM'; simp; positivity
    refine ⟨hF, ?_⟩
    have hs := (sMinus_lt_iff hF hrD).2 hlt
    rw [← ENNReal.ofReal_toReal hne, ← hr]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt (sMinus_nonneg hF) hs)).2 hs

namespace Hyp
variable {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞} (h : Hyp E xbar γ M R)
include h

lemma mem_U_iff {x : X} : x ∈ U xbar R γ M ↔
    ENNReal.ofReal ‖x - xbar‖ < R ∧ M * ‖x - xbar‖ < γ :=
  ofReal_lt_r0_iff h.hγ h.hM (norm_nonneg _)

/-- Two points of U lie in a common closed ball B̄(x̄, ρ) with ρ < R, Mρ < γ. -/
lemma common_ball {x y : X} (hx : x ∈ U xbar R γ M) (hy : y ∈ U xbar R γ M) :
    ∃ ρ, 0 ≤ ρ ∧ ENNReal.ofReal ρ ≤ R ∧ M * ρ < γ ∧ x ∈ closedBall xbar ρ ∧
      y ∈ closedBall xbar ρ := by
  rw [h.mem_U_iff] at hx hy
  rcases le_total ‖x - xbar‖ ‖y - xbar‖ with hle | hle
  · exact ⟨‖y - xbar‖, norm_nonneg _, hy.1.le, hy.2,
      by rw [mem_closedBall, dist_eq_norm]; exact hle,
      by rw [mem_closedBall, dist_eq_norm]⟩
  · exact ⟨‖x - xbar‖, norm_nonneg _, hx.1.le, hx.2,
      by rw [mem_closedBall, dist_eq_norm], by rw [mem_closedBall, dist_eq_norm]; exact hle⟩

/-- **Proposition 4, "at most one"**: E has at most one stationary point in U. -/
theorem stationary_unique {x y : X} (hx : x ∈ U xbar R γ M) (hy : y ∈ U xbar R γ M)
    (gx : gradient E x = 0) (gy : gradient E y = 0) : x = y := by
  obtain ⟨ρ, -, hρR, hMρ, hxb, hyb⟩ := h.common_ball hx hy
  have := h.strongMono hρR hxb hyb
  rw [gx, gy, sub_self, inner_zero_left] at this
  have hk : 0 < kappa γ M ρ := by simp only [kappa]; linarith
  have : ‖x - y‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖x - y‖ = 0 := by nlinarith [norm_nonneg (x - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Proposition 4(i), minimality**: a stationary point x* ∈ U minimises E over U. -/
theorem stationary_isMinOn {xs : X} (hxs : xs ∈ U xbar R γ M) (gxs : gradient E xs = 0) :
    IsMinOn E (U xbar R γ M) xs := by
  intro y hy
  obtain ⟨ρ, -, hρR, hMρ, hxb, hyb⟩ := h.common_ball hxs hy
  set d := y - xs
  have hF : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun t : ℝ => E (xs + t • d))
      ⟪gradient E (xs + t • d), d⟫ t := fun t _ => hasDerivAt_E_line h.smooth xs d t
  have hK : ∀ t ∈ Icc (0:ℝ) 1, HasDerivAt (fun _ : ℝ => (0:ℝ)) 0 t :=
    fun t _ => hasDerivAt_const t 0
  have hle : ∀ t ∈ Icc (0:ℝ) 1, (0:ℝ) ≤ ⟪gradient E (xs + t • d), d⟫ := by
    intro t ht
    have hz := (convex_closedBall xbar ρ).add_smul_sub_mem hxb hyb ht
    have hm := h.strongMono hρR hz hxb
    rw [gxs, sub_zero, show xs + t • d - xs = t • d by abel, inner_smul_right] at hm
    have hk : 0 ≤ kappa γ M ρ := by simp only [kappa]; linarith
    rcases ht.1.lt_or_eq with htp | ht0
    · have : 0 ≤ t * ⟪gradient E (xs + t • d), d⟫ :=
        le_trans (mul_nonneg hk (sq_nonneg _)) hm
      exact nonneg_of_mul_nonneg_right (by linarith) htp |> fun h' => by
        nlinarith [mul_nonneg htp.le h']
    · subst ht0; simp [gxs]
  have := sub_le_sub_of_hasDerivAt_le hK hF hle
  simp only [one_smul, zero_smul, add_zero, sub_self] at this
  rw [show xs + d = y by simp [d]] at this
  show E xs ≤ E y
  linarith

/-- **Proposition 4(i), uniqueness of the minimiser**: any minimiser of E over the open set U
is stationary, hence equals x*. -/
theorem isMinOn_unique {xs y : X} (hxs : xs ∈ U xbar R γ M) (gxs : gradient E xs = 0)
    (hy : y ∈ U xbar R γ M) (hmin : IsMinOn E (U xbar R γ M) y) : y = xs := by
  have hloc : IsLocalMin E y := hmin.isLocalMin ((isOpen_U xbar R γ M).mem_nhds hy)
  have : gradient E y = 0 := by simp [gradient, hloc.fderiv_eq_zero]
  exact h.stationary_unique hy hxs this gxs

/-- Location of a stationary point with ‖x − x̄‖ ≤ R: φ(‖x − x̄‖) ≤ ‖∇E(x̄)‖ (S5.5 / S6.7). -/
theorem phi_le_of_stationary {x : X} (hx : ENNReal.ofReal ‖x - xbar‖ ≤ R)
    (gx : gradient E x = 0) : phi γ M ‖x - xbar‖ ≤ ‖gradient E xbar‖ := by
  have h1 := h.ray_lower hx
  rw [gx, zero_sub, inner_neg_left] at h1
  have h2 : -⟪gradient E xbar, x - xbar⟫ ≤ ‖gradient E xbar‖ * ‖x - xbar‖ := by
    have := real_inner_le_norm (-gradient E xbar) (x - xbar)
    rw [inner_neg_left, norm_neg] at this; exact this
  rcases (norm_nonneg (x - xbar)).lt_or_eq with hp | h0
  · have : ‖x - xbar‖ * phi γ M ‖x - xbar‖ ≤ ‖x - xbar‖ * ‖gradient E xbar‖ := by linarith
    exact le_of_mul_le_mul_left this hp
  · rw [← h0]; simp [phi]

/-- **Proposition 4(ii)**: for a stationary x* ∈ U: φ(‖x* − x̄‖) ≤ ‖g‖, ‖x* − x̄‖ ≤ 2‖g‖/γ, and
‖x* − x̄‖ ≤ s₋(‖g‖) whenever ‖g‖ ≤ γ²/(2M) (encoded 2M‖g‖ ≤ γ²). -/
theorem location {xs : X} (hxs : xs ∈ U xbar R γ M) (gxs : gradient E xs = 0) :
    phi γ M ‖xs - xbar‖ ≤ ‖gradient E xbar‖ ∧ ‖xs - xbar‖ ≤ 2 * ‖gradient E xbar‖ / γ ∧
    (2 * M * ‖gradient E xbar‖ ≤ γ ^ 2 → ‖xs - xbar‖ ≤ sMinus γ M ‖gradient E xbar‖) := by
  have hU := h.mem_U_iff.1 hxs
  have hφ := h.phi_le_of_stationary hU.1.le gxs
  have hD : ‖xs - xbar‖ ∈ Dom γ M := ⟨norm_nonneg _, hU.2.le⟩
  refine ⟨hφ, ?_, fun hg => ?_⟩
  · have := half_le_phi hD.1 hD.2
    rw [le_div_iff₀ h.hγ]; linarith
  · exact (phi_le_iff ⟨h.hγ, h.hM, norm_nonneg _, hg⟩ hD).1 hφ

end Hyp

namespace Hyp
variable {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞} (h : Hyp E xbar γ M R)
include h

/-- E − (κ(ρ)/2)‖·‖² is convex on every convex S ⊆ B̄(x̄, ρ), ρ ≤ R finite (first-order
criterion along segments, from Lemma 2(b)). -/
theorem convexOn_sub_sq {ρ : ℝ} (hρR : ENNReal.ofReal ρ ≤ R) {S : Set X} (hS : Convex ℝ S)
    (hSB : S ⊆ closedBall xbar ρ) :
    ConvexOn ℝ S (fun x => E x - kappa γ M ρ / 2 * ‖x‖ ^ 2) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  set d := x - y with hd
  set κ := kappa γ M ρ
  let φ : ℝ → ℝ := fun t => E (y + t • d) - κ / 2 * ‖y + t • d‖ ^ 2
  let φ' : ℝ → ℝ := fun t => ⟪gradient E (y + t • d), d⟫ - κ * ⟪y + t • d, d⟫
  have hφ : ∀ t, HasDerivAt φ (φ' t) t := by
    intro t
    have h1 := hasDerivAt_E_line h.smooth y d t
    have h2 := (hasDerivAt_line y d t).norm_sq
    have h3 := h1.sub (h2.const_mul (κ / 2))
    have e : φ' t = ⟪gradient E (y + t • d), d⟫ - κ / 2 * (2 * ⟪y + t • d, d⟫) := by
      simp only [φ']; ring
    rw [e]; exact h3
  have hmono : MonotoneOn φ' (Icc 0 1) := by
    intro s hs t ht hst
    rcases hst.lt_or_eq with hlt | heq
    · have hzs := hS.add_smul_sub_mem hy hx hs
      have hzt := hS.add_smul_sub_mem hy hx ht
      have hm := h.strongMono hρR (hSB hzt) (hSB hzs)
      have e : y + t • d - (y + s • d) = (t - s) • d := by rw [sub_smul]; abel
      rw [e, inner_smul_right, norm_smul, Real.norm_of_nonneg (by linarith), inner_sub_left] at hm
      have hd2 : ⟪y + t • d, d⟫ - ⟪y + s • d, d⟫ = (t - s) * ‖d‖ ^ 2 := by
        rw [← inner_sub_left, e, real_inner_smul_left, real_inner_self_eq_norm_sq]
      have hts : 0 < t - s := by linarith
      have h4 : (t - s) * (κ * ((t - s) * ‖d‖ ^ 2)) ≤ (t - s) *
          (⟪gradient E (y + t • d), d⟫ - ⟪gradient E (y + s • d), d⟫) := by nlinarith
      have h5 := le_of_mul_le_mul_left h4 hts
      have h6 : κ * (⟪y + t • d, d⟫ - ⟪y + s • d, d⟫) = κ * ((t - s) * ‖d‖ ^ 2) := by rw [hd2]
      simp only [φ']
      linarith
    · rw [heq]
  have hconv : ConvexOn ℝ (Icc (0:ℝ) 1) φ := by
    apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
    · exact fun t _ => (hφ t).continuousAt.continuousWithinAt
    · exact fun t _ => (hφ t).differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro s hs t ht hst
      rw [(hφ s).deriv, (hφ t).deriv]
      exact hmono (Ioo_subset_Icc_self hs) (Ioo_subset_Icc_self ht) hst
  have := hconv.2 (right_mem_Icc.2 zero_le_one) (left_mem_Icc.2 zero_le_one) ha hb hab
  simp only [φ, smul_eq_mul, mul_one, mul_zero, one_smul, zero_smul, add_zero] at this
  have e1 : y + a • d = a • x + b • y := by
    rw [show b = 1 - a by linarith, hd]; simp only [smul_sub, sub_smul, one_smul]; abel
  have e2 : y + d = x := by simp [d]
  rw [e1, e2] at this
  simpa [smul_eq_mul] using this

/-- **Lemma 2(a)**: for ρ ∈ (0, ∞), ρ ≤ R, Mρ < γ: κ(ρ) > 0 and E is κ(ρ)-strongly convex on the
open ball B(x̄, ρ) (Mathlib's `StrongConvexOn`, which is B&C (10.2) for E + ι_{B(x̄,ρ)}). -/
theorem strongConvexOn_ball {ρ : ℝ} (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ ≤ R)
    (hMρ : M * ρ < γ) :
    0 < kappa γ M ρ ∧ StrongConvexOn (ball xbar ρ) (kappa γ M ρ) E := by
  have _ := hρ
  exact ⟨by simp only [kappa]; linarith, strongConvexOn_iff_convex.2
    (h.convexOn_sub_sq hρR (convex_ball _ _) ball_subset_closedBall)⟩

/-- **Lemma 2** as stated: (a) strong convexity on B(x̄, ρ) and (b) κ(ρ)-strong monotonicity of
∇E on B̄(x̄, ρ), for ρ ∈ (0, ∞), ρ ≤ R, Mρ < γ. -/
theorem lemma2 {ρ : ℝ} (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ ≤ R) (hMρ : M * ρ < γ) :
    0 < kappa γ M ρ ∧ StrongConvexOn (ball xbar ρ) (kappa γ M ρ) E ∧
    ∀ x ∈ closedBall xbar ρ, ∀ y ∈ closedBall xbar ρ,
      kappa γ M ρ * ‖x - y‖ ^ 2 ≤ ⟪gradient E x - gradient E y, x - y⟫ :=
  ⟨(h.strongConvexOn_ball hρ hρR hMρ).1, (h.strongConvexOn_ball hρ hρR hMρ).2,
    fun _ hx _ hy => h.strongMono hρR hx hy⟩

end Hyp

/-! ## Part G. β_ρ facts (finite dimension), Proposition 5 (capture) -/

section Proper
variable [ProperSpace X]

namespace Hyp
variable {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞} (h : Hyp E xbar γ M R)
include h

lemma beta_bdd (ρ : ℝ) : BddAbove ((fun z => ‖hess E z‖) '' closedBall xbar ρ) :=
  ((isCompact_closedBall xbar ρ).image (continuous_hess h.smooth).norm).bddAbove

lemma norm_hess_le_beta {ρ : ℝ} {z : X} (hz : z ∈ closedBall xbar ρ) :
    ‖hess E z‖ ≤ beta E xbar ρ :=
  le_csSup (h.beta_bdd ρ) (mem_image_of_mem _ hz)

/-- β_ρ is a maximum: attained on B̄(x̄, ρ) (Weierstrass + Heine–Borel, S5.0). -/
lemma beta_attained {ρ : ℝ} (hρ : 0 ≤ ρ) : ∃ z ∈ closedBall xbar ρ, ‖hess E z‖ = beta E xbar ρ := by
  have hc := (isCompact_closedBall xbar ρ).image (continuous_hess h.smooth).norm
  have hne : ((fun z => ‖hess E z‖) '' closedBall xbar ρ).Nonempty :=
    (nonempty_closedBall.2 hρ).image _
  obtain ⟨z, hz, e⟩ := hc.sSup_mem hne
  exact ⟨z, hz, e⟩

lemma beta_mono {ρ₁ ρ₂ : ℝ} (hρ₁ : 0 ≤ ρ₁) (h12 : ρ₁ ≤ ρ₂) :
    beta E xbar ρ₁ ≤ beta E xbar ρ₂ :=
  csSup_le_csSup (h.beta_bdd ρ₂) ((nonempty_closedBall.2 hρ₁).image _)
    (image_mono (closedBall_subset_closedBall h12))

/-- β_r over the closed ball equals the spine's β_B := sup over the open ball (Cor. 7). -/
lemma beta_eq_sSup_ball {r : ℝ} (hr : 0 < r) :
    beta E xbar r = sSup ((fun z => ‖hess E z‖) '' ball xbar r) := by
  have hbdd : BddAbove ((fun z => ‖hess E z‖) '' ball xbar r) :=
    (h.beta_bdd r).mono (image_mono ball_subset_closedBall)
  have hne : ((fun z => ‖hess E z‖) '' ball xbar r).Nonempty :=
    (nonempty_ball.2 hr).image _
  apply le_antisymm
  · apply csSup_le ((nonempty_closedBall.2 hr.le).image _)
    rintro _ ⟨z, hz, rfl⟩
    have hsub : ball xbar r ⊆ {z | ‖hess E z‖ ≤ sSup ((fun z => ‖hess E z‖) '' ball xbar r)} :=
      fun y hy => le_csSup hbdd (mem_image_of_mem _ hy)
    have hcl : IsClosed {z | ‖hess E z‖ ≤ sSup ((fun z => ‖hess E z‖) '' ball xbar r)} :=
      isClosed_le (continuous_hess h.smooth).norm continuous_const
    have := closure_minimal hsub hcl
    rw [closure_ball xbar hr.ne'] at this
    exact this hz
  · exact csSup_le_csSup (h.beta_bdd r) hne (image_mono ball_subset_closedBall)

variable [Nontrivial X]

omit [ProperSpace X] in
/-- γ ≤ ‖∇²E(x̄)‖ (from the Rayleigh lower bound; d ≥ 1). -/
lemma gamma_le_norm_hess : γ ≤ ‖hess E xbar‖ := by
  obtain ⟨u, hu⟩ := exists_ne (0 : X)
  have hnu : 0 < ‖u‖ ^ 2 := by positivity
  have h1 := h.floor u
  have h2 : ⟪hess E xbar u, u⟫ ≤ ‖hess E xbar‖ * ‖u‖ ^ 2 := by
    calc _ ≤ ‖hess E xbar u‖ * ‖u‖ := real_inner_le_norm _ _
      _ ≤ (‖hess E xbar‖ * ‖u‖) * ‖u‖ := by gcongr; exact (hess E xbar).le_opNorm u
      _ = _ := by ring
  exact le_of_mul_le_mul_right (by linarith) hnu

/-- S6.1: β_ρ ≥ γ > 0. -/
lemma gamma_le_beta {ρ : ℝ} (hρ : 0 ≤ ρ) : γ ≤ beta E xbar ρ :=
  le_trans h.gamma_le_norm_hess (h.norm_hess_le_beta (mem_closedBall_self hρ))

/-- α ≤ 1/β_ρ ⇔ α‖∇²E(z)‖ ≤ 1 on B̄(x̄, ρ) (for α > 0). -/
lemma step_le_inv_beta_iff {ρ α : ℝ} (hρ : 0 ≤ ρ) (hα : 0 < α) :
    α ≤ 1 / beta E xbar ρ ↔ ∀ z ∈ closedBall xbar ρ, α * ‖hess E z‖ ≤ 1 := by
  have hβ : 0 < beta E xbar ρ := lt_of_lt_of_le h.hγ (h.gamma_le_beta hρ)
  rw [le_one_div hα hβ]
  constructor
  · intro hb z hz
    have := le_trans (h.norm_hess_le_beta hz) hb
    rw [le_div_iff₀ hα] at this; linarith
  · intro hz
    apply csSup_le ((nonempty_closedBall.2 hρ).image _)
    rintro _ ⟨z, hzb, rfl⟩
    rw [le_div_iff₀ hα]; linarith [hz z hzb]

/-- **Lemma 3(b)** as stated: for x with s = ‖x − x̄‖ ≤ ρ ≤ R, ρ finite, and α ∈ (0, 1/β_ρ]:
‖T_α x − x̄‖ ≤ s − αφ(s) + α‖∇E(x̄)‖. -/
theorem ray_step {x : X} {ρ α : ℝ} (hsρ : ‖x - xbar‖ ≤ ρ) (hρR : ENNReal.ofReal ρ ≤ R)
    (hα : 0 < α) (hαβ : α ≤ 1 / beta E xbar ρ) :
    ‖(x - α • gradient E x) - xbar‖ ≤
      ‖x - xbar‖ - α * phi γ M ‖x - xbar‖ + α * ‖gradient E xbar‖ :=
  h.ray_step' hsρ hρR hα.le
    ((h.step_le_inv_beta_iff (le_trans (norm_nonneg _) hsρ) hα).1 hαβ)

end Hyp

/-- (H4) + (H5) of Proposition 5: ρ ∈ (0, ∞), ρ ≤ R, Mρ < γ, ‖g‖ ≤ φ(ρ); α ∈ (0, 1/β_ρ]. -/
structure Capture (E : X → ℝ) (xbar : X) (γ M : ℝ) (R : ℝ≥0∞) (ρ α : ℝ) : Prop where
  hyp : Hyp E xbar γ M R
  hρ : 0 < ρ
  hρR : ENNReal.ofReal ρ ≤ R
  hMρ : M * ρ < γ
  hg : ‖gradient E xbar‖ ≤ phi γ M ρ
  hα : 0 < α
  hαβ : α ≤ 1 / beta E xbar ρ

/-- The gradient step T_α = Id − α∇E. -/
noncomputable def step (E : X → ℝ) (α : ℝ) (x : X) : X := x - α • gradient E x

/-- q_ρ = 1 − ακ(ρ). -/
def qfac (γ M ρ α : ℝ) : ℝ := 1 - α * kappa γ M ρ
omit [ProperSpace X] in

lemma step_fixed_iff {E : X → ℝ} {α : ℝ} (hα : α ≠ 0) (x : X) :
    step E α x = x ↔ gradient E x = 0 := by
  simp [step, sub_eq_self, hα]

namespace Capture
variable [Nontrivial X] {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞} {ρ α : ℝ}
variable (c : Capture E xbar γ M R ρ α)
include c

lemma stepOK : ∀ z ∈ closedBall xbar ρ, α * ‖hess E z‖ ≤ 1 :=
  (c.hyp.step_le_inv_beta_iff c.hρ.le c.hα).1 c.hαβ

lemma alpha_gamma_le : α * γ ≤ 1 := by
  have := c.stepOK xbar (mem_closedBall_self c.hρ.le)
  nlinarith [c.hyp.gamma_le_norm_hess, c.hα]

/-- **Proposition 5(a)**: T_α maps B̄(x̄, ρ) into itself; into the open ball B(x̄, ρ) if
‖g‖ < φ(ρ). -/
theorem mapsTo : MapsTo (step E α) (closedBall xbar ρ) (closedBall xbar ρ) := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx ⊢
  have h1 := c.hyp.ray_step' hx c.hρR c.hα.le c.stepOK
  have h2 := psi_bound (G := ‖gradient E xbar‖) c.hyp.hM c.hα.le c.alpha_gamma_le
    (norm_nonneg _) hx
  have h3 : 0 ≤ α * (phi γ M ρ - ‖gradient E xbar‖) := mul_nonneg c.hα.le (by linarith [c.hg])
  simp only [step]; linarith

theorem mapsTo_ball (hlt : ‖gradient E xbar‖ < phi γ M ρ) :
    MapsTo (step E α) (closedBall xbar ρ) (ball xbar ρ) := by
  intro x hx
  rw [mem_closedBall, dist_eq_norm] at hx
  rw [mem_ball, dist_eq_norm]
  have h1 := c.hyp.ray_step' hx c.hρR c.hα.le c.stepOK
  have h2 := psi_bound (G := ‖gradient E xbar‖) c.hyp.hM c.hα.le c.alpha_gamma_le
    (norm_nonneg _) hx
  have h3 : 0 < α * (phi γ M ρ - ‖gradient E xbar‖) := mul_pos c.hα (by linarith)
  simp only [step]; linarith

/-- **Proposition 5(b)**: ‖T_α x − T_α y‖ ≤ q_ρ‖x − y‖ on B̄(x̄, ρ), and 0 ≤ q_ρ < 1. -/
theorem lipschitz {x y : X} (hx : x ∈ closedBall xbar ρ) (hy : y ∈ closedBall xbar ρ) :
    ‖step E α x - step E α y‖ ≤ qfac γ M ρ α * ‖x - y‖ := by
  have hseg := seg_bound c.hyp.smooth (p := y) (d := x - y) (α := α) (a := qfac γ M ρ α) (b := 0)
    (by
      intro t ht u
      have hz := (convex_closedBall xbar ρ).add_smul_sub_mem hy hx ht
      have hfl := c.hyp.floor_ball c.hρR hz u
      have hup : ⟪hess E (y + t • (x - y)) u, u⟫ ≤ ‖hess E (y + t • (x - y))‖ * ‖u‖ ^ 2 := by
        calc _ ≤ ‖hess E (y + t • (x - y)) u‖ * ‖u‖ := real_inner_le_norm _ _
          _ ≤ (‖hess E (y + t • (x - y))‖ * ‖u‖) * ‖u‖ := by
            gcongr; exact (hess E _).le_opNorm u
          _ = _ := by ring
      have hs1 := c.stepOK _ hz
      constructor
      · have := mul_le_mul_of_nonneg_left hup c.hα.le
        nlinarith [sq_nonneg ‖u‖]
      · have := mul_le_mul_of_nonneg_left hfl c.hα.le
        simp only [qfac]; nlinarith)
  rw [show y + (x - y) = x by abel] at hseg
  have e : step E α x - step E α y = (x - y) - α • (gradient E x - gradient E y) := by
    simp only [step, smul_sub]; abel
  rw [e]; simpa using hseg

theorem qfac_nonneg : 0 ≤ qfac γ M ρ α := by
  have := c.alpha_gamma_le
  have : α * kappa γ M ρ ≤ α * γ := by
    apply mul_le_mul_of_nonneg_left _ c.hα.le
    simp only [kappa]; nlinarith [c.hyp.hM, c.hρ]
  simp only [qfac]; linarith
omit [ProperSpace X] [Nontrivial X] in

theorem qfac_lt_one : qfac γ M ρ α < 1 := by
  have : 0 < α * kappa γ M ρ := mul_pos c.hα (by simp only [kappa]; linarith [c.hMρ])
  simp only [qfac]; linarith

/-- **Proposition 5(c), existence and uniqueness**: exactly one stationary point in B̄(x̄, ρ). -/
theorem existsUnique_stationary : ∃! xs, xs ∈ closedBall xbar ρ ∧ gradient E xs = 0 := by
  set K : ℝ≥0 := ⟨qfac γ M ρ α, c.qfac_nonneg⟩
  have hsf := c.mapsTo
  have hK : ContractingWith K (hsf.restrict (step E α) (closedBall xbar ρ) (closedBall xbar ρ)) := by
    refine ⟨?_, LipschitzWith.of_dist_le_mul fun a b => ?_⟩
    · show (⟨qfac γ M ρ α, c.qfac_nonneg⟩ : ℝ≥0) < 1
      exact_mod_cast c.qfac_lt_one
    · rw [Subtype.dist_eq, Subtype.dist_eq, MapsTo.val_restrict_apply, MapsTo.val_restrict_apply,
        dist_eq_norm, dist_eq_norm]
      exact c.lipschitz a.2 b.2
  obtain ⟨y, hy, hfix, -⟩ := hK.exists_fixedPoint' isClosed_closedBall.isComplete hsf
    (mem_closedBall_self c.hρ.le) (edist_ne_top _ _)
  refine ⟨y, ⟨hy, (step_fixed_iff c.hα.ne' y).1 hfix⟩, ?_⟩
  rintro z ⟨hz, gz⟩
  have hl := c.lipschitz hz hy
  have hfz : step E α z = z := (step_fixed_iff c.hα.ne' z).2 gz
  have hfy : step E α y = y := hfix
  rw [hfz, hfy] at hl
  have hq := c.qfac_lt_one
  have : ‖z - y‖ = 0 := by nlinarith [norm_nonneg (z - y)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Proposition 5(c), convergence**: iterates stay in the ball and
‖x^k − x*‖ ≤ q^k‖x⁰ − x*‖ ≤ 2ρq^k; a-posteriori ‖x^k − x*‖ ≤ q/(1−q)‖x^k − x^{k−1}‖;
x^k → x*. -/
theorem iterate_bounds {xs x0 : X} (hxs : xs ∈ closedBall xbar ρ) (gxs : gradient E xs = 0)
    (hx0 : x0 ∈ closedBall xbar ρ) (k : ℕ) :
    (step E α)^[k] x0 ∈ closedBall xbar ρ ∧
    ‖(step E α)^[k] x0 - xs‖ ≤ qfac γ M ρ α ^ k * ‖x0 - xs‖ ∧
    qfac γ M ρ α ^ k * ‖x0 - xs‖ ≤ 2 * ρ * qfac γ M ρ α ^ k ∧
    ‖(step E α)^[k + 1] x0 - xs‖ ≤ qfac γ M ρ α / (1 - qfac γ M ρ α) *
      ‖(step E α)^[k + 1] x0 - (step E α)^[k] x0‖ := by
  have hfix : step E α xs = xs := (step_fixed_iff c.hα.ne' xs).2 gxs
  have hmem : ∀ n, (step E α)^[n] x0 ∈ closedBall xbar ρ := fun n => c.mapsTo.iterate n hx0
  have hq0 := c.qfac_nonneg
  have hq1 := c.qfac_lt_one
  have hrate : ∀ n, ‖(step E α)^[n] x0 - xs‖ ≤ qfac γ M ρ α ^ n * ‖x0 - xs‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      calc ‖step E α ((step E α)^[n] x0) - xs‖
          = ‖step E α ((step E α)^[n] x0) - step E α xs‖ := by rw [hfix]
        _ ≤ qfac γ M ρ α * ‖(step E α)^[n] x0 - xs‖ := c.lipschitz (hmem n) hxs
        _ ≤ qfac γ M ρ α * (qfac γ M ρ α ^ n * ‖x0 - xs‖) := by gcongr
        _ = _ := by ring
  refine ⟨hmem k, hrate k, ?_, ?_⟩
  · have : ‖x0 - xs‖ ≤ 2 * ρ := by
      rw [mem_closedBall, dist_eq_norm] at hx0 hxs
      calc ‖x0 - xs‖ = ‖(x0 - xbar) - (xs - xbar)‖ := by congr 1; abel
        _ ≤ ‖x0 - xbar‖ + ‖xs - xbar‖ := norm_sub_le _ _
        _ ≤ 2 * ρ := by linarith
    have := mul_le_mul_of_nonneg_left this (pow_nonneg hq0 k)
    linarith
  · set a := (step E α)^[k] x0
    have hk1 : (step E α)^[k + 1] x0 = step E α a := Function.iterate_succ_apply' _ _ _
    rw [hk1]
    have l1 := c.lipschitz (hmem k) hxs
    rw [hfix] at l1
    change ‖step E α a - xs‖ ≤ qfac γ M ρ α * ‖a - xs‖ at l1
    have l2 : ‖a - xs‖ ≤ ‖a - step E α a‖ + ‖step E α a - xs‖ := by
      calc ‖a - xs‖ = ‖(a - step E α a) + (step E α a - xs)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    rw [norm_sub_rev a (step E α a)] at l2
    have key : ‖step E α a - xs‖ * (1 - qfac γ M ρ α) ≤
        qfac γ M ρ α * ‖step E α a - a‖ := by
      nlinarith [mul_le_mul_of_nonneg_left l2 hq0]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]; linarith [key]

theorem tendsto_iterate {xs x0 : X} (hxs : xs ∈ closedBall xbar ρ) (gxs : gradient E xs = 0)
    (hx0 : x0 ∈ closedBall xbar ρ) :
    Tendsto (fun k => (step E α)^[k] x0) atTop (𝓝 xs) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hq := tendsto_pow_atTop_nhds_zero_of_lt_one c.qfac_nonneg c.qfac_lt_one
  have : Tendsto (fun k => qfac γ M ρ α ^ k * ‖x0 - xs‖) atTop (𝓝 0) := by
    simpa using hq.mul_const ‖x0 - xs‖
  exact squeeze_zero (fun _ => norm_nonneg _)
    (fun k => (c.iterate_bounds hxs gxs hx0 k).2.1) this

omit [ProperSpace X] [Nontrivial X] in
/-- **Proposition 5(d)**: the stationary point satisfies ‖x* − x̄‖ ≤ s₋(‖g‖) ≤ 2‖g‖/γ; if moreover
‖g‖ < φ(r₀), then x* ∈ U. -/
theorem location {xs : X} (hxs : xs ∈ closedBall xbar ρ) (gxs : gradient E xs = 0) :
    F3Hyp γ M ‖gradient E xbar‖ ∧
    ‖xs - xbar‖ ≤ sMinus γ M ‖gradient E xbar‖ ∧
    sMinus γ M ‖gradient E xbar‖ ≤ 2 * ‖gradient E xbar‖ / γ ∧
    (ExistCond R γ M ‖gradient E xbar‖ → xs ∈ U xbar R γ M) := by
  have h := c.hyp
  rw [mem_closedBall, dist_eq_norm] at hxs
  have hsR : ENNReal.ofReal ‖xs - xbar‖ ≤ R := le_trans (ENNReal.ofReal_le_ofReal hxs) c.hρR
  have hφ := h.phi_le_of_stationary hsR gxs
  have hD : ‖xs - xbar‖ ∈ Dom γ M :=
    ⟨norm_nonneg _, by nlinarith [mul_le_mul_of_nonneg_left hxs h.hM, c.hMρ]⟩
  have hF : F3Hyp γ M ‖gradient E xbar‖ := by
    refine ⟨h.hγ, h.hM, norm_nonneg _, ?_⟩
    rcases h.hM.lt_or_eq with hM' | hM'
    · have := phi_le_max (γ := γ) hM' ρ
      have h3 : 2 * M * ‖gradient E xbar‖ ≤ 2 * M * (γ ^ 2 / (2 * M)) := by nlinarith [c.hg]
      rwa [show 2 * M * (γ ^ 2 / (2 * M)) = γ ^ 2 by field_simp] at h3
    · subst hM'; simp; positivity
  have hs := (phi_le_iff hF hD).1 hφ
  refine ⟨hF, hs, sMinus_le_two_div hF, fun hc => ?_⟩
  have h2 := (existCond_spec h.hγ h.hM (norm_nonneg _) hc).2
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hs) h2

end Capture

/-! ## Part H. Theorem 6 (local conditioning certificate) and Corollary 7 -/

section Thm6
variable [Nontrivial X] {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞}

omit [ProperSpace X] [Nontrivial X] in
/-- (H4)+(H5) from the Theorem 6(c) choice of ρ (S7.3). -/
lemma capture_of (h : Hyp E xbar γ M R) (hF : F3Hyp γ M ‖gradient E xbar‖) {ρ α : ℝ}
    (hρ : 0 < ρ) (hsρ : sMinus γ M ‖gradient E xbar‖ ≤ ρ)
    (hρU : ENNReal.ofReal ρ < r0 R γ M) (hα : 0 < α) (hαβ : α ≤ 1 / beta E xbar ρ) :
    Capture E xbar γ M R ρ α := by
  have hU := (ofReal_lt_r0_iff h.hγ h.hM hρ.le).1 hρU
  have hρD : ρ ∈ Dom γ M := ⟨hρ.le, hU.2.le⟩
  refine ⟨h, hρ, hU.1.le, hU.2, ?_, hα, hαβ⟩
  rw [← phi_sMinus hF]
  exact (phi_strictMonoOn h.hγ h.hM).monotoneOn (sMinus_mem_Dom hF) hρD hsρ

omit [ProperSpace X] [Nontrivial X] in
/-- **Theorem 6(a)**: for ρ ∈ (0, ∞) with ρ ≤ R and Mρ < γ, E is κ(ρ)-strongly convex on
B(x̄, ρ) and ∇E is κ(ρ)-strongly monotone on B̄(x̄, ρ). -/
theorem thm6_a (h : Hyp E xbar γ M R) {ρ : ℝ} (hρ : 0 < ρ) (hρR : ENNReal.ofReal ρ ≤ R)
    (hMρ : M * ρ < γ) :
    0 < kappa γ M ρ ∧ StrongConvexOn (ball xbar ρ) (kappa γ M ρ) E ∧
    ∀ x ∈ closedBall xbar ρ, ∀ y ∈ closedBall xbar ρ,
      kappa γ M ρ * ‖x - y‖ ^ 2 ≤ ⟪gradient E x - gradient E y, x - y⟫ :=
  h.lemma2 hρ hρR hMρ

omit [ProperSpace X] [Nontrivial X] in
/-- **Theorem 6(b)**: at most one stationary point in U = B(x̄, r₀); any stationary x* ∈ U is the
unique minimiser of E over U and ‖x* − x̄‖ ≤ 2‖g‖/γ. -/
theorem thm6_b (h : Hyp E xbar γ M R) :
    (∀ x ∈ U xbar R γ M, ∀ y ∈ U xbar R γ M, gradient E x = 0 → gradient E y = 0 → x = y) ∧
    ∀ xs ∈ U xbar R γ M, gradient E xs = 0 →
      IsMinOn E (U xbar R γ M) xs ∧ (∀ y ∈ U xbar R γ M, IsMinOn E (U xbar R γ M) y → y = xs) ∧
      ‖xs - xbar‖ ≤ 2 * ‖gradient E xbar‖ / γ :=
  ⟨fun _ hx _ hy gx gy => h.stationary_unique hx hy gx gy,
   fun _ hxs gxs => ⟨h.stationary_isMinOn hxs gxs, fun _ hy hmin => h.isMinOn_unique hxs gxs hy hmin,
     (h.location hxs gxs).2.1⟩⟩

/-- **Theorem 6(c)** (existence and capture): if ‖g‖ < φ(r₀) (no condition if r₀ = ∞), E has a
stationary point x* ∈ U with ‖x* − x̄‖ ≤ s₋(‖g‖); for every ρ ∈ [s₋(‖g‖), r₀), ρ > 0, and every
α ∈ (0, 1/β_ρ], T_α maps B̄(x̄, ρ) into itself, is q_ρ-Lipschitz there with 0 ≤ q_ρ < 1, and its
iterates from any x⁰ ∈ B̄(x̄, ρ) converge to x* with ‖x^k − x*‖ ≤ q_ρ^k‖x⁰ − x*‖. -/
theorem thm6_c (h : Hyp E xbar γ M R) (hc : ExistCond R γ M ‖gradient E xbar‖) :
    ∃ xs ∈ U xbar R γ M, gradient E xs = 0 ∧ ‖xs - xbar‖ ≤ sMinus γ M ‖gradient E xbar‖ ∧
    ∀ ρ α : ℝ, 0 < ρ → sMinus γ M ‖gradient E xbar‖ ≤ ρ → ENNReal.ofReal ρ < r0 R γ M →
      0 < α → α ≤ 1 / beta E xbar ρ →
      MapsTo (step E α) (closedBall xbar ρ) (closedBall xbar ρ) ∧
      (∀ x ∈ closedBall xbar ρ, ∀ y ∈ closedBall xbar ρ,
        ‖step E α x - step E α y‖ ≤ qfac γ M ρ α * ‖x - y‖) ∧
      0 ≤ qfac γ M ρ α ∧ qfac γ M ρ α < 1 ∧
      ∀ x0 ∈ closedBall xbar ρ, Tendsto (fun k => (step E α)^[k] x0) atTop (𝓝 xs) ∧
        ∀ k : ℕ, ‖(step E α)^[k] x0 - xs‖ ≤ qfac γ M ρ α ^ k * ‖x0 - xs‖ := by
  obtain ⟨hF, hsU⟩ := existCond_spec h.hγ h.hM (norm_nonneg _) hc
  set t := ‖gradient E xbar‖
  have hs0 := sMinus_nonneg hF
  -- a radius ρ₀ ∈ [s₋, r₀), ρ₀ > 0
  obtain ⟨ρ₀, hρ₀, hsρ₀, hρ₀U⟩ : ∃ ρ₀, 0 < ρ₀ ∧ sMinus γ M t ≤ ρ₀ ∧
      ENNReal.ofReal ρ₀ < r0 R γ M := by
    rcases eq_or_ne (r0 R γ M) ⊤ with htop | hne
    · exact ⟨sMinus γ M t + 1, by linarith, by linarith, by rw [htop]; exact ENNReal.ofReal_lt_top⟩
    · have hlt := (ENNReal.ofReal_lt_iff_lt_toReal hs0 hne).1 hsU
      refine ⟨(sMinus γ M t + (r0 R γ M).toReal) / 2, by linarith, by linarith, ?_⟩
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by linarith) hne).2 (by linarith)
  have hβ₀ : 0 < beta E xbar ρ₀ := lt_of_lt_of_le h.hγ (h.gamma_le_beta hρ₀.le)
  have c₀ := capture_of h hF hρ₀ hsρ₀ hρ₀U (one_div_pos.2 hβ₀) le_rfl
  obtain ⟨xs, ⟨hxsb, gxs⟩, -⟩ := c₀.existsUnique_stationary
  obtain ⟨-, hloc, -, hU⟩ := c₀.location hxsb gxs
  have hxsU := hU hc
  refine ⟨xs, hxsU, gxs, hloc, fun ρ α hρ hsρ hρU hα hαβ => ?_⟩
  have c := capture_of h hF hρ hsρ hρU hα hαβ
  obtain ⟨xs', ⟨hxsb', gxs'⟩, -⟩ := c.existsUnique_stationary
  have hxsU' := (c.location hxsb' gxs').2.2.2 hc
  have heq : xs' = xs := h.stationary_unique hxsU' hxsU gxs' gxs
  subst heq
  exact ⟨c.mapsTo, fun x hx y hy => c.lipschitz hx hy, c.qfac_nonneg, c.qfac_lt_one,
    fun x0 hx0 => ⟨c.tendsto_iterate hxsb' gxs' hx0,
      fun k => (c.iterate_bounds hxsb' gxs' hx0 k).2.1⟩⟩

end Thm6

section Cor7
variable [Nontrivial X] {E : X → ℝ} {xbar : X} {γ M : ℝ} {R : ℝ≥0∞}

/-- Corollary 7's radius r := min{R, γ/(2M)} (γ/0 := ∞), when finite, is a real r > 0 with
r ≤ R and Mr ≤ γ/2. -/
lemma cor7_radius (hγ : 0 < γ) (hM : 0 ≤ M) (hR : 0 < R)
    (hfin : min R (ENNReal.ofReal γ / ENNReal.ofReal (2 * M)) ≠ ⊤) :
    let r := (min R (ENNReal.ofReal γ / ENNReal.ofReal (2 * M))).toReal
    0 < r ∧ ENNReal.ofReal r ≤ R ∧ M * r ≤ γ / 2 := by
  intro r
  have hpos : 0 < min R (ENNReal.ofReal γ / ENNReal.ofReal (2 * M)) := by
    refine lt_min hR (ENNReal.div_pos (by simp [hγ]) ENNReal.ofReal_ne_top)
  refine ⟨ENNReal.toReal_pos hpos.ne' hfin, ?_, ?_⟩
  · rw [ENNReal.ofReal_toReal hfin]; exact min_le_left _ _
  · rcases hM.lt_or_eq with hM' | hM'
    · have h1 : min R (ENNReal.ofReal γ / ENNReal.ofReal (2 * M)) ≤ ENNReal.ofReal (γ / (2 * M)) := by
        rw [ENNReal.ofReal_div_of_pos (by linarith)]; exact min_le_right _ _
      have h2 := ENNReal.toReal_le_of_le_ofReal (div_pos hγ (by linarith)).le h1
      have h3 : M * r ≤ M * (γ / (2 * M)) := mul_le_mul_of_nonneg_left h2 hM
      rwa [show M * (γ / (2 * M)) = γ / 2 by field_simp] at h3
    · subst hM'; simp; linarith

omit [ProperSpace X] [Nontrivial X] in
/-- Corollary 7, case r = ∞ (M = 0, R = ∞): E is γ-strongly convex on all of X, and U = X (so
Theorem 6(b) gives at most one stationary point and the unique minimiser on X). -/
theorem cor7_infinite (h : Hyp E xbar γ 0 ⊤) :
    StrongConvexOn univ γ E ∧ U xbar ⊤ γ 0 = univ := by
  refine ⟨strongConvexOn_iff_convex.2 ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩, ?_⟩
  · set ρ := max ‖x - xbar‖ ‖y - xbar‖
    have hx : x ∈ closedBall xbar ρ := by
      rw [mem_closedBall, dist_eq_norm]; exact le_max_left _ _
    have hy : y ∈ closedBall xbar ρ := by
      rw [mem_closedBall, dist_eq_norm]; exact le_max_right _ _
    have := (h.convexOn_sub_sq (ρ := ρ) le_top (convex_closedBall xbar ρ) subset_rfl).2 hx hy
      ha hb hab
    simpa [kappa] using this
  · ext x
    simp only [U, mem_setOf_eq, mem_univ, iff_true]
    rw [ofReal_lt_r0_iff h.hγ le_rfl (norm_nonneg _)]
    exact ⟨ENNReal.ofReal_lt_top, by simp [h.hγ]⟩


variable (h : Hyp E xbar γ M R) {r : ℝ} (hr0 : 0 < r) (hrR : ENNReal.ofReal r ≤ R)
  (hMr : M * r ≤ γ / 2)
include h hr0 hrR hMr
omit [ProperSpace X] [Nontrivial X] in

lemma ball_subset_U : ball xbar r ⊆ U xbar R γ M := by
  intro x hx
  rw [mem_ball, dist_eq_norm] at hx
  rw [h.mem_U_iff]
  refine ⟨lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff hr0).2 hx) hrR, ?_⟩
  have := mul_le_mul_of_nonneg_left hx.le h.hM
  linarith [h.hγ]

omit [ProperSpace X] [Nontrivial X] in
/-- **Corollary 7(i)**: E is (γ/2)-strongly convex on B(x̄, r), and ∇E is (γ/2)-strongly monotone
on B̄(x̄, r). -/
theorem cor7_i : StrongConvexOn (ball xbar r) (γ / 2) E ∧
    ∀ x ∈ closedBall xbar r, ∀ y ∈ closedBall xbar r,
      γ / 2 * ‖x - y‖ ^ 2 ≤ ⟪gradient E x - gradient E y, x - y⟫ := by
  have hk := kappa_ge_half hMr
  have hMr' : M * r < γ := by linarith [h.hγ]
  obtain ⟨-, hsc, hmono⟩ := h.lemma2 hr0 hrR hMr'
  refine ⟨hsc.mono hk, fun x hx y hy => ?_⟩
  have := hmono x hx y hy
  nlinarith [sq_nonneg ‖x - y‖]

omit [ProperSpace X] [Nontrivial X] in
/-- **Corollary 7(ii)**: at most one stationary point in B(x̄, r); such a point is the unique
minimiser of E over B(x̄, r). -/
theorem cor7_ii :
    (∀ x ∈ ball xbar r, ∀ y ∈ ball xbar r, gradient E x = 0 → gradient E y = 0 → x = y) ∧
    ∀ xs ∈ ball xbar r, gradient E xs = 0 →
      IsMinOn E (ball xbar r) xs ∧ ∀ y ∈ ball xbar r, IsMinOn E (ball xbar r) y → y = xs := by
  have hsub := ball_subset_U h hr0 hrR hMr
  refine ⟨fun x hx y hy gx gy => h.stationary_unique (hsub hx) (hsub hy) gx gy,
    fun xs hxs gxs => ⟨(h.stationary_isMinOn (hsub hxs) gxs).on_subset hsub, fun y hy hmin => ?_⟩⟩
  have hloc : IsLocalMin E y := hmin.isLocalMin (isOpen_ball.mem_nhds hy)
  have : gradient E y = 0 := by simp [gradient, hloc.fderiv_eq_zero]
  exact h.stationary_unique (hsub hy) (hsub hxs) this gxs

/-- **Corollary 7(iii)**: for finite r and ‖g‖ < φ(r): a stationary x* ∈ B(x̄, r) exists with
‖x* − x̄‖ ≤ s₋(‖g‖) < r; for every ρ ∈ [s₋(‖g‖), r], ρ > 0, and α ∈ (0, 1/β_ρ], T_α maps B̄(x̄, ρ)
into itself, contracts there with factor 1 − α(γ − Mρ) ≤ 1 − αγ/2, and its unique fixed point in
B̄(x̄, ρ) is x*. -/
theorem cor7_iii (hg : ‖gradient E xbar‖ < phi γ M r) :
    ∃ xs ∈ ball xbar r, gradient E xs = 0 ∧ ‖xs - xbar‖ ≤ sMinus γ M ‖gradient E xbar‖ ∧
    sMinus γ M ‖gradient E xbar‖ < r ∧
    ∀ ρ α : ℝ, 0 < ρ → sMinus γ M ‖gradient E xbar‖ ≤ ρ → ρ ≤ r → 0 < α →
      α ≤ 1 / beta E xbar ρ →
      MapsTo (step E α) (closedBall xbar ρ) (closedBall xbar ρ) ∧
      (∀ x ∈ closedBall xbar ρ, ∀ y ∈ closedBall xbar ρ,
        ‖step E α x - step E α y‖ ≤ qfac γ M ρ α * ‖x - y‖) ∧
      qfac γ M ρ α < 1 ∧ qfac γ M ρ α ≤ 1 - α * γ / 2 ∧
      ∀ z ∈ closedBall xbar ρ, step E α z = z ↔ z = xs := by
  obtain ⟨hF, hsr, hρs⟩ := cor7_iii_constants h.hγ h.hM hr0 hMr (norm_nonneg _) hg
  have cap : ∀ ρ α : ℝ, 0 < ρ → sMinus γ M ‖gradient E xbar‖ ≤ ρ → ρ ≤ r → 0 < α →
      α ≤ 1 / beta E xbar ρ → Capture E xbar γ M R ρ α := by
    intro ρ α hρ h1 h2 hα hαβ
    obtain ⟨hMρ, hgρ, -, -⟩ := hρs ρ h1 h2
    exact ⟨h, hρ, le_trans (ENNReal.ofReal_le_ofReal h2) hrR, hMρ, hgρ, hα, hαβ⟩
  have hβr : 0 < beta E xbar r := lt_of_lt_of_le h.hγ (h.gamma_le_beta hr0.le)
  have c₀ := cap r (1 / beta E xbar r) hr0 hsr.le le_rfl (one_div_pos.2 hβr) le_rfl
  obtain ⟨xs, ⟨hxsb, gxs⟩, -⟩ := c₀.existsUnique_stationary
  have hloc := (c₀.location hxsb gxs).2.1
  have hxsr : xs ∈ ball xbar r := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hsub := ball_subset_U h hr0 hrR hMr
  refine ⟨xs, hxsr, gxs, hloc, hsr, fun ρ α hρ h1 h2 hα hαβ => ?_⟩
  have c := cap ρ α hρ h1 h2 hα hαβ
  obtain ⟨-, -, -, hfac⟩ := hρs ρ h1 h2
  refine ⟨c.mapsTo, fun x hx y hy => c.lipschitz hx hy, c.qfac_lt_one,
    by have := hfac α hα.le; simp only [qfac]; linarith, fun z hz => ?_⟩
  rw [step_fixed_iff hα.ne']
  constructor
  · intro gz
    have hzr : z ∈ ball xbar r := by
      have := (c.location hz gz).2.1
      rw [mem_ball, dist_eq_norm]; linarith
    exact h.stationary_unique (hsub hzr) (hsub hxsr) gz gxs
  · rintro rfl; exact gxs

/-- **Corollary 7(iv)**: under the spine's ‖g‖ < γr/4 (r finite), the closed half-radius ball
B̄(x̄, r/2) ⊂ B(x̄, r) is invariant under T_α for every α ∈ (0, 1/β_r], and T_α contracts there with
factor q_{r/2} ≤ 1 − (3/4)αγ. -/
theorem cor7_iv (hg : ‖gradient E xbar‖ < γ * r / 4) {α : ℝ} (hα : 0 < α)
    (hαβ : α ≤ 1 / beta E xbar r) :
    closedBall xbar (r / 2) ⊆ ball xbar r ∧
    MapsTo (step E α) (closedBall xbar (r / 2)) (closedBall xbar (r / 2)) ∧
    (∀ x ∈ closedBall xbar (r / 2), ∀ y ∈ closedBall xbar (r / 2),
      ‖step E α x - step E α y‖ ≤ qfac γ M (r / 2) α * ‖x - y‖) ∧
    qfac γ M (r / 2) α ≤ 1 - 3 / 4 * α * γ := by
  obtain ⟨hF, -, -, hr2, -, -, hgφ, hMρ, -, hfac⟩ :=
    cor7_iv_constants h.hγ h.hM hr0 hMr (norm_nonneg _) hg
  have hβ2 : 0 < beta E xbar (r / 2) := lt_of_lt_of_le h.hγ (h.gamma_le_beta (by linarith))
  have hβr : 0 < beta E xbar r := lt_of_lt_of_le h.hγ (h.gamma_le_beta hr0.le)
  have hαβ2 : α ≤ 1 / beta E xbar (r / 2) :=
    le_trans hαβ (one_div_le_one_div_of_le hβ2 (h.beta_mono (by linarith) (by linarith)))
  have c : Capture E xbar γ M R (r / 2) α :=
    ⟨h, by linarith, le_trans (ENNReal.ofReal_le_ofReal (by linarith)) hrR, hMρ, hgφ.le, hα,
      hαβ2⟩
  exact ⟨closedBall_subset_ball hr2, c.mapsTo, fun x hx y hy => c.lipschitz hx hy,
    by have := hfac α hα.le; simp only [qfac]; linarith⟩

end Cor7
end Proper
end Core

/-! ## Part I. Proposition 8 (sharpness): the one-dimensional extremal family -/

section Sharp

/-- Derivative of a function defined by two smooth pieces glued at c with matching values and
matching derivatives. -/
lemma hasDerivAt_ite_le {c : ℝ} {p q p' q' : ℝ → ℝ} (hp : ∀ x, HasDerivAt p (p' x) x)
    (hq : ∀ x, HasDerivAt q (q' x) x) (hc : p c = q c) (hc' : p' c = q' c) (x : ℝ) :
    HasDerivAt (fun y => if y ≤ c then p y else q y) (if x ≤ c then p' x else q' x) x := by
  rcases lt_trichotomy x c with hlt | heq | hgt
  · rw [if_pos hlt.le]
    apply (hp x).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlt] with y hy
    rw [if_pos (le_of_lt hy)]
  · subst heq
    rw [if_pos le_rfl]
    have h1 : HasDerivWithinAt (fun y => if y ≤ x then p y else q y) (p' x) (Iic x) x :=
      (hp x).hasDerivWithinAt.congr (fun y hy => if_pos hy) (if_pos le_rfl)
    have h2 : HasDerivWithinAt (fun y => if y ≤ x then p y else q y) (p' x) (Ici x) x := by
      rw [hc']
      refine (hq x).hasDerivWithinAt.congr (fun y hy => ?_) (by rw [if_pos le_rfl, hc])
      by_cases hyx : y ≤ x
      · have : y = x := le_antisymm hyx hy
        rw [if_pos hyx, this, hc]
      · rw [if_neg hyx]
    have := h1.union h2
    rwa [Iic_union_Ici, hasDerivWithinAt_univ] at this
  · rw [if_neg (not_le.2 hgt)]
    apply (hq x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hgt] with y hy
    rw [if_neg (not_le.2 hy)]

/-- (H1)–(H3) for a function e : ℝ → ℝ at x̄ = 0, written with e′, e″: e has derivative e′,
e′ has derivative e″, e″ is continuous (so e ∈ C²), e″(0) = γ (in d = 1, λ_min = e″(0)), and
|e″(x) − e″(0)| ≤ M|x| for |x| < R. -/
structure Hyp1D (e e' e'' : ℝ → ℝ) (γ M : ℝ) (R : ℝ≥0∞) : Prop where
  d1 : ∀ x, HasDerivAt e (e' x) x
  d2 : ∀ x, HasDerivAt e' (e'' x) x
  cont : Continuous e''
  at0 : e'' 0 = γ
  var : ∀ x, ENNReal.ofReal |x| < R → |e'' x - e'' 0| ≤ M * |x|

namespace Hyp1D
variable {e e' e'' : ℝ → ℝ} {γ M : ℝ} {R : ℝ≥0∞} (h : Hyp1D e e' e'' γ M R)
include h

lemma gradient_eq (x : ℝ) : gradient e x = e' x := by
  rw [gradient_eq_deriv', (h.d1 x).deriv]

lemma gradient_fun : gradient e = e' := funext h.gradient_eq

lemma hess_apply (x u : ℝ) : hess e x u = e'' x * u := by
  simp only [hess, h.gradient_fun, (h.d2 x).hasFDerivAt.fderiv]
  simp [mul_comm]

lemma norm_hess_sub (x y : ℝ) : ‖hess e x - hess e y‖ = |e'' x - e'' y| := by
  have : hess e x - hess e y = (e'' x - e'' y) • ContinuousLinearMap.id ℝ ℝ := by
    ext; simp [h.hess_apply]
  rw [this, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

lemma norm_hess (x : ℝ) : ‖hess e x‖ = |e'' x| := by
  have : hess e x = e'' x • ContinuousLinearMap.id ℝ ℝ := by
    ext; simp [h.hess_apply]
  rw [this, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

/-- **Bridge**: the one-dimensional hypotheses are exactly the general (H1)–(H3) on X = ℝ. -/
theorem toHyp (hγ : 0 < γ) (hM : 0 ≤ M) (hR : 0 < R) : Hyp e 0 γ M R := by
  have hde : deriv e = e' := funext fun x => (h.d1 x).deriv
  have hde' : deriv e' = e'' := funext fun x => (h.d2 x).deriv
  refine ⟨?_, hγ, ?_, hR, hM, ?_⟩
  · show ContDiff ℝ (1 + 1) e
    rw [contDiff_succ_iff_deriv]
    refine ⟨fun x => (h.d1 x).differentiableAt, by simp, ?_⟩
    rw [hde, contDiff_one_iff_deriv, hde']
    exact ⟨fun x => (h.d2 x).differentiableAt, h.cont⟩
  · intro u
    rw [h.hess_apply, Real.inner_apply, h.at0, Real.norm_eq_abs, sq_abs]; ring_nf; rfl
  · intro x hx
    rw [h.norm_hess_sub, sub_zero, Real.norm_eq_abs]
    exact h.var x (by simpa [sub_zero, Real.norm_eq_abs] using hx)

end Hyp1D

/-- The extremal family of Proposition 8: e′(x) = −ζ + γx − (M/2)x|x|. -/
noncomputable def famD1 (ζ γ M x : ℝ) : ℝ := -ζ + γ * x - M / 2 * x * |x|

/-- e″(x) = γ − M|x|. -/
def famD2 (γ M x : ℝ) : ℝ := γ - M * |x|

/-- e(x) = ∫₀ˣ e′ (so e(0) = 0). -/
noncomputable def famE (ζ γ M x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, famD1 ζ γ M t

section Family
variable {ζ γ M : ℝ}

lemma famD1_cont : Continuous (famD1 ζ γ M) := by
  unfold famD1; fun_prop

lemma famD1_eq_ite : famD1 ζ γ M = fun y =>
    if y ≤ 0 then -ζ + (γ * y + M / 2 * y ^ 2) else -ζ + (γ * y + -(M / 2) * y ^ 2) := by
  funext y
  split_ifs with hy
  · rw [famD1, abs_of_nonpos hy]; ring
  · rw [famD1, abs_of_pos (not_le.1 hy)]; ring

lemma famD1_hasDerivAt (x : ℝ) : HasDerivAt (famD1 ζ γ M) (famD2 γ M x) x := by
  rw [famD1_eq_ite]
  have := hasDerivAt_ite_le (c := 0)
    (p := fun y => -ζ + (γ * y + M / 2 * y ^ 2)) (q := fun y => -ζ + (γ * y + -(M / 2) * y ^ 2))
    (p' := fun y => γ + 2 * (M / 2) * y) (q' := fun y => γ + 2 * (-(M / 2)) * y)
    (fun x => (hasDerivAt_quad γ (M / 2) x).const_add (-ζ))
    (fun x => (hasDerivAt_quad γ (-(M / 2)) x).const_add (-ζ)) (by simp) (by simp) x
  convert this using 1
  split_ifs with hx
  · rw [famD2, abs_of_nonpos hx]; ring
  · rw [famD2, abs_of_pos (not_le.1 hx)]; ring

/-- S8.1: (H1)–(H3) hold for the family with this γ, M and every R (equality in (H3)). -/
theorem fam_hyp (hM : 0 ≤ M) (R : ℝ≥0∞) :
    Hyp1D (famE ζ γ M) (famD1 ζ γ M) (famD2 γ M) γ M R where
  d1 x := (famD1_cont.integral_hasStrictDerivAt 0 x).hasDerivAt
  d2 x := famD1_hasDerivAt x
  cont := by unfold famD2; fun_prop
  at0 := by simp [famD2]
  var x _ := by simp [famD2, abs_mul, abs_of_nonneg hM]

/-- S8.1: equality in (H3), g = ∇E(0) = −ζ (‖g‖ = ζ), and φ(s) = e′(s) + ζ for s ≥ 0. -/
theorem fam_facts (hM : 0 ≤ M) (hζ : 0 ≤ ζ) :
    (∀ x, |famD2 γ M x - famD2 γ M 0| = M * |x|) ∧ famD1 ζ γ M 0 = -ζ ∧
    |famD1 ζ γ M 0| = ζ ∧ ∀ s, 0 ≤ s → phi γ M s = famD1 ζ γ M s + ζ := by
  refine ⟨fun x => by simp [famD2, abs_mul, abs_of_nonneg hM], by simp [famD1],
    by simp [famD1, abs_of_nonneg hζ], fun s hs => ?_⟩
  simp only [phi, famD1, abs_of_nonneg hs]; ring

/-- r₀ for M > 0: finite, positive, in [0, γ/M]; and U = {|x| < r₀}. -/
lemma r0_spec (hγ : 0 < γ) (hM : 0 < M) {R : ℝ≥0∞} (hR : 0 < R) :
    r0 R γ M ≠ ⊤ ∧ 0 < (r0 R γ M).toReal ∧ M * (r0 R γ M).toReal ≤ γ ∧
    ∀ x : ℝ, x ∈ U (0:ℝ) R γ M ↔ |x| < (r0 R γ M).toReal := by
  have hle : r0 R γ M ≤ ENNReal.ofReal (γ / M) := by
    unfold r0; rw [ENNReal.ofReal_div_of_pos hM]; exact min_le_right _ _
  have hne : r0 R γ M ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  have hpos : 0 < r0 R γ M := by
    unfold r0
    exact lt_min hR (ENNReal.div_pos (by simp [hγ]) ENNReal.ofReal_ne_top)
  refine ⟨hne, ENNReal.toReal_pos hpos.ne' hne, ?_, fun x => ?_⟩
  · have := ENNReal.toReal_le_of_le_ofReal (div_pos hγ hM).le hle
    rw [le_div_iff₀ hM] at this; linarith
  · simp only [U, mem_setOf_eq, sub_zero, Real.norm_eq_abs]
    exact ENNReal.ofReal_lt_iff_lt_toReal (abs_nonneg x) hne

/-- **Proposition 8(c)** (existence threshold): if ζ ≥ φ(r₀) then e′ has no zero in U. -/
theorem prop8_c (hγ : 0 < γ) (hM : 0 < M) {R : ℝ≥0∞} (hR : 0 < R)
    (hζ : phi γ M (r0 R γ M).toReal ≤ ζ) : ∀ x ∈ U (0:ℝ) R γ M, famD1 ζ γ M x ≠ 0 := by
  obtain ⟨-, hr0, hMr, hU⟩ := r0_spec hγ hM hR
  set r := (r0 R γ M).toReal
  have hφr : 0 < phi γ M r := by
    have := half_le_phi hr0.le hMr; nlinarith
  intro x hx
  have hxr := (hU x).1 hx
  rcases le_or_gt x 0 with hx0 | hx0
  · have hxr' : -r < x := by rw [abs_of_nonpos hx0] at hxr; linarith
    have : famD1 ζ γ M x = -ζ + x * (γ + M / 2 * x) := by
      rw [famD1, abs_of_nonpos hx0]; ring
    rw [this]
    have h1 : 0 < γ + M / 2 * x := by nlinarith
    have : x * (γ + M / 2 * x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hx0 h1.le
    linarith
  · have hxr' : x < r := by rwa [abs_of_pos hx0] at hxr
    have hmono := phi_strictMonoOn hγ hM.le ⟨hx0.le, by nlinarith⟩ ⟨hr0.le, hMr⟩ hxr'
    have : famD1 ζ γ M x = phi γ M x - ζ := by
      rw [famD1, abs_of_pos hx0, phi]; ring
    rw [this]; linarith

/-- The step map of the family, T(x) = x − α e′(x); at α = 1/γ it is ζ/γ + (M/(2γ))x|x|. -/
lemma fam_step (hγ : 0 < γ) (hM : 0 ≤ M) (x : ℝ) :
    step (famE ζ γ M) (1 / γ) x = ζ / γ + M / (2 * γ) * (x * |x|) := by
  rw [step, (fam_hyp (ζ := ζ) (γ := γ) hM ⊤).gradient_eq, smul_eq_mul, famD1]
  field_simp; ring

/-- On B̄(0, ρ), Mρ < γ: β_ρ = γ (S8.5). -/
theorem fam_beta (hγ : 0 < γ) (hM : 0 ≤ M) {ρ : ℝ} (hρ : 0 ≤ ρ) (hMρ : M * ρ < γ) :
    beta (famE ζ γ M) 0 ρ = γ := by
  have h := fam_hyp (ζ := ζ) (γ := γ) hM ⊤
  apply IsGreatest.csSup_eq
  refine ⟨⟨0, mem_closedBall_self hρ, by simp [h.norm_hess, famD2, abs_of_pos hγ]⟩, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs] at hz
  simp only [h.norm_hess, famD2]
  have : M * |z| ≤ M * ρ := mul_le_mul_of_nonneg_left hz hM
  rw [abs_le]; constructor <;> nlinarith [abs_nonneg z, mul_nonneg hM (abs_nonneg z)]

/-- **Proposition 8(d)** (invariance threshold): for 0 < ρ with Mρ < γ (in particular
0 < ρ < r₀) and α = 1/β_ρ = 1/γ, T_α maps B̄(0, ρ) into itself iff ζ ≤ φ(ρ). -/
theorem prop8_d (hγ : 0 < γ) (hM : 0 ≤ M) (hζ : 0 ≤ ζ) {ρ : ℝ} (hρ : 0 < ρ)
    (hMρ : M * ρ < γ) :
    1 / beta (famE ζ γ M) 0 ρ = 1 / γ ∧
    (MapsTo (step (famE ζ γ M) (1 / γ)) (closedBall 0 ρ) (closedBall 0 ρ) ↔ ζ ≤ phi γ M ρ) := by
  refine ⟨by rw [fam_beta hγ hM hρ.le hMρ], ?_⟩
  have hc : ∀ x, x ∈ closedBall (0:ℝ) ρ ↔ |x| ≤ ρ := fun x => by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  constructor
  · intro hm
    have := hm ((hc ρ).2 (by rw [abs_of_pos hρ]))
    rw [hc, fam_step hγ hM, abs_of_pos hρ, abs_le] at this
    have h2 := mul_le_mul_of_nonneg_right this.2 hγ.le
    have e1 : (ζ / γ + M / (2 * γ) * (ρ * ρ)) * γ = ζ + M / 2 * ρ ^ 2 := by field_simp
    rw [e1] at h2
    simp only [phi]; nlinarith
  · intro hle x hx
    rw [hc] at hx ⊢
    rw [fam_step hγ hM]
    have hxx : abs (x * |x|) ≤ ρ ^ 2 := by
      rw [abs_mul, abs_abs]; nlinarith [abs_nonneg x]
    have hk : 0 ≤ M / (2 * γ) := by positivity
    have h1 := mul_le_mul_of_nonneg_left (abs_le.1 hxx).2 hk
    have h2 := mul_le_mul_of_nonneg_left (neg_le_of_abs_le hxx) hk
    have e1 : ζ / γ + M / (2 * γ) * ρ ^ 2 ≤ ρ := by
      rw [div_add' _ _ _ hγ.ne', div_le_iff₀ hγ]
      have : M / (2 * γ) * ρ ^ 2 * γ = M / 2 * ρ ^ 2 := by field_simp
      simp only [phi] at hle; nlinarith
    have e2 : -ρ ≤ ζ / γ - M / (2 * γ) * ρ ^ 2 := by
      have : M / (2 * γ) * ρ ^ 2 ≤ ρ := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
      have : 0 ≤ ζ / γ := div_nonneg hζ hγ.le
      linarith
    rw [abs_le]; constructor <;> nlinarith

/-- |x|x| − y|y|| ≤ 2ρ|x − y| on [−ρ, ρ]. -/
lemma abs_mul_abs_sub_le {x y ρ : ℝ} (hx : |x| ≤ ρ) (hy : |y| ≤ ρ) :
    abs (x * |x| - y * |y|) ≤ 2 * ρ * |x - y| := by
  rcases le_total 0 x with hx0 | hx0 <;> rcases le_total 0 y with hy0 | hy0
  · rw [abs_of_nonneg hx0, abs_of_nonneg hy0] at *
    rw [show x * x - y * y = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (by linarith : 0 ≤ x + y)]
    nlinarith [abs_nonneg (x - y)]
  · rw [abs_of_nonneg hx0, abs_of_nonpos hy0] at *
    rw [abs_of_nonneg (by nlinarith : 0 ≤ x * x - y * -y), abs_of_nonneg (by linarith : 0 ≤ x - y)]
    nlinarith
  · rw [abs_of_nonpos hx0, abs_of_nonneg hy0] at *
    rw [abs_of_nonpos (by nlinarith : x * -x - y * y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    nlinarith
  · rw [abs_of_nonpos hx0, abs_of_nonpos hy0] at *
    rw [show x * -x - y * -y = (y - x) * (y + x) by ring, abs_mul,
      abs_of_nonpos (by linarith : y + x ≤ 0), abs_sub_comm]
    nlinarith [abs_nonneg (x - y)]

/-- **Proposition 8(e)** (contraction factor): with α = 1/γ, the Lipschitz constant of T_α on
B̄(0, ρ) (0 < ρ, Mρ < γ) is exactly q_ρ = 1 − α(γ − Mρ): it is the least L ≥ 0 with
|Tx − Ty| ≤ L|x − y| there. -/
theorem prop8_e (hγ : 0 < γ) (hM : 0 ≤ M) {ρ : ℝ} (hρ : 0 < ρ) :
    IsLeast {L | 0 ≤ L ∧ ∀ x ∈ closedBall (0:ℝ) ρ, ∀ y ∈ closedBall (0:ℝ) ρ,
      |step (famE ζ γ M) (1 / γ) x - step (famE ζ γ M) (1 / γ) y| ≤ L * |x - y|}
      (qfac γ M ρ (1 / γ)) := by
  have hq : qfac γ M ρ (1 / γ) = M * ρ / γ := by
    simp only [qfac, kappa]; field_simp; ring
  have hc : ∀ x, x ∈ closedBall (0:ℝ) ρ ↔ |x| ≤ ρ := fun x => by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  have hT : ∀ x y, step (famE ζ γ M) (1 / γ) x - step (famE ζ γ M) (1 / γ) y =
      M / (2 * γ) * (x * |x| - y * |y|) := fun x y => by
    rw [fam_step hγ hM, fam_step hγ hM]; ring
  rw [hq]
  refine ⟨⟨by positivity, fun x hx y hy => ?_⟩, ?_⟩
  · rw [hc] at hx hy
    rw [hT, abs_mul, abs_of_nonneg (by positivity : 0 ≤ M / (2 * γ))]
    have := abs_mul_abs_sub_le hx hy
    calc M / (2 * γ) * abs (x * |x| - y * |y|) ≤ M / (2 * γ) * (2 * ρ * |x - y|) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = M * ρ / γ * |x - y| := by field_simp
  · rintro L ⟨hL0, hL⟩
    by_contra hlt
    push Not at hlt
    -- x = ρ, y = ρ − η with η small
    have hMpos : 0 < M := by
      rcases hM.lt_or_eq with h | h
      · exact h
      · subst h; simp at hlt; linarith
    set η := min ρ ((M * ρ / γ - L) * γ / M) with hη
    have hη0 : 0 < η := lt_min hρ (by
      apply div_pos (mul_pos (by linarith) hγ) hMpos)
    have hηρ : η ≤ ρ := min_le_left _ _
    have hη2 : η ≤ (M * ρ / γ - L) * γ / M := min_le_right _ _
    have hx : ρ ∈ closedBall (0:ℝ) ρ := (hc ρ).2 (by rw [abs_of_pos hρ])
    have hy : ρ - η ∈ closedBall (0:ℝ) ρ := (hc _).2 (by rw [abs_le]; constructor <;> linarith)
    have := hL ρ hx (ρ - η) hy
    rw [hT, abs_of_pos hρ, abs_of_nonneg (by linarith : 0 ≤ ρ - η),
      show ρ - (ρ - η) = η by ring, abs_of_pos hη0] at this
    have e : M / (2 * γ) * (ρ * ρ - (ρ - η) * (ρ - η)) = M * ρ / γ * η - M / (2 * γ) * η ^ 2 := by
      ring
    have e2 : M * ρ / γ * η - M / (2 * γ) * η ^ 2 = M / (2 * γ) * η * (2 * ρ - η) := by ring
    rw [e, e2, abs_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hη0.le) (by linarith)),
      ← e2] at this
    -- M ρ/γ η − (M/(2γ)) η² ≤ L η  ⇒  Mρ/γ − L ≤ (M/(2γ)) η ≤ (Mρ/γ − L)/2
    have h1 : M * ρ / γ - L ≤ M / (2 * γ) * η := by
      have := le_of_mul_le_mul_right (a := η) (by nlinarith) hη0
      nlinarith
    have h2 : M / (2 * γ) * η ≤ (M * ρ / γ - L) / 2 := by
      calc M / (2 * γ) * η ≤ M / (2 * γ) * ((M * ρ / γ - L) * γ / M) :=
            mul_le_mul_of_nonneg_left hη2 (by positivity)
        _ = (M * ρ / γ - L) / 2 := by field_simp
    linarith

/-- **Proposition 8(f)** (location attained): if 0 ≤ ζ < φ(r₀) (M > 0), the unique stationary
point of the family in U is x* = s₋(ζ), so ‖x* − x̄‖ = s₋(‖g‖). -/
theorem prop8_f (hγ : 0 < γ) (hM : 0 < M) {R : ℝ≥0∞} (hR : 0 < R) (hζ : 0 ≤ ζ)
    (hc : ζ < phi γ M (r0 R γ M).toReal) :
    sMinus γ M ζ ∈ U (0:ℝ) R γ M ∧ famD1 ζ γ M (sMinus γ M ζ) = 0 ∧
    (∀ x ∈ U (0:ℝ) R γ M, famD1 ζ γ M x = 0 → x = sMinus γ M ζ) ∧
    |sMinus γ M ζ - 0| = sMinus γ M ζ := by
  obtain ⟨hne, hr0, hMr, hU⟩ := r0_spec hγ hM hR
  obtain ⟨hF, hsU⟩ := existCond_spec (R := R) hγ hM.le hζ (Or.inr hc)
  have hs0 := sMinus_nonneg hF
  have hzero : famD1 ζ γ M (sMinus γ M ζ) = 0 := by
    have := phi_sMinus hF
    rw [famD1, abs_of_nonneg hs0]; simp only [phi] at this; linarith
  have hsU' : sMinus γ M ζ ∈ U (0:ℝ) R γ M := by
    simp only [U, mem_setOf_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hs0]; exact hsU
  refine ⟨hsU', hzero, fun x hx hx0 => ?_, by rw [sub_zero, abs_of_nonneg hs0]⟩
  have h := ((fam_hyp (ζ := ζ) (γ := γ) hM.le R).toHyp hγ hM.le hR)
  have g1 : gradient (famE ζ γ M) x = 0 := by
    rw [(fam_hyp (ζ := ζ) (γ := γ) hM.le R).gradient_eq]; exact hx0
  have g2 : gradient (famE ζ γ M) (sMinus γ M ζ) = 0 := by
    rw [(fam_hyp (ζ := ζ) (γ := γ) hM.le R).gradient_eq]; exact hzero
  exact h.stationary_unique hx hsU' g1 g2

/-- Proposition 8(f), second clause: s₋(ζ)/(2ζ/γ) = γ/(γ + √(γ² − 2Mζ)) → 1 as ζ ↑ γ²/(2M);
so 2‖g‖/γ cannot be improved by a constant factor. -/
theorem prop8_f_ratio (hγ : 0 < γ) (hM : 0 < M) :
    (∀ t, 0 < t → 2 * M * t ≤ γ ^ 2 →
      sMinus γ M t / (2 * t / γ) = γ / (γ + Real.sqrt (γ ^ 2 - 2 * M * t))) ∧
    Tendsto (fun t => sMinus γ M t / (2 * t / γ)) (𝓝[<] (γ ^ 2 / (2 * M))) (𝓝 1) := by
  have hform : ∀ t, 0 < t → sMinus γ M t / (2 * t / γ) =
      γ / (γ + Real.sqrt (γ ^ 2 - 2 * M * t)) := by
    intro t ht
    have hd : 0 < γ + Real.sqrt (γ ^ 2 - 2 * M * t) := by
      have := Real.sqrt_nonneg (γ ^ 2 - 2 * M * t); linarith
    simp only [sMinus]; field_simp
  refine ⟨fun t ht _ => hform t ht, ?_⟩
  have hcont : ContinuousAt (fun t => γ / (γ + Real.sqrt (γ ^ 2 - 2 * M * t)))
      (γ ^ 2 / (2 * M)) := by
    apply ContinuousAt.div continuousAt_const (by fun_prop)
    have := Real.sqrt_nonneg (γ ^ 2 - 2 * M * (γ ^ 2 / (2 * M))); linarith
  have hval : γ / (γ + Real.sqrt (γ ^ 2 - 2 * M * (γ ^ 2 / (2 * M)))) = 1 := by
    rw [show γ ^ 2 - 2 * M * (γ ^ 2 / (2 * M)) = 0 by field_simp; ring, Real.sqrt_zero,
      add_zero, div_self hγ.ne']
  have h1 := hcont.tendsto
  rw [hval] at h1
  have hpos : (0:ℝ) < γ ^ 2 / (2 * M) := by positivity
  refine (h1.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hpos] with t ht
  exact (hform t ht.1).symm

/-- Case M = 0 (S8.7): e′(x) = γx − ζ has its zero at ζ/γ = s₋(ζ), and a zero lies in
B(0, R) iff ζ < γR = φ(R) (so (c) and (f) are sharp for M = 0 and finite R too). -/
theorem prop8_M_zero (hγ : 0 < γ) (hζ : 0 ≤ ζ) {R : ℝ} (hR : 0 < R) :
    famD1 ζ γ 0 (ζ / γ) = 0 ∧ sMinus γ 0 ζ = ζ / γ ∧
    ((∃ x, |x| < R ∧ famD1 ζ γ 0 x = 0) ↔ ζ < phi γ 0 R) := by
  have _ := hR
  have hz : ∀ x, famD1 ζ γ 0 x = 0 ↔ x = ζ / γ := by
    intro x; simp only [famD1]; constructor
    · intro h; field_simp; linarith
    · rintro rfl; field_simp; ring
  refine ⟨(hz _).2 rfl, sMinus_M_zero hγ ζ, ?_⟩
  simp only [phi, zero_div, zero_mul, sub_zero]
  constructor
  · rintro ⟨x, hx, h0⟩
    rw [(hz x).1 h0, abs_of_nonneg (div_nonneg hζ hγ.le), div_lt_iff₀ hγ] at hx; linarith
  · intro h
    refine ⟨ζ / γ, ?_, (hz _).2 rfl⟩
    rw [abs_of_nonneg (div_nonneg hζ hγ.le), div_lt_iff₀ hγ]; linarith


lemma fam_inner (hγ : 0 < γ) (hM : 0 ≤ M) (x y : ℝ) :
    inner ℝ (gradient (famE ζ γ M) x - gradient (famE ζ γ M) y) (x - y) =
      (famD1 ζ γ M x - famD1 ζ γ M y) * (x - y) := by
  have _ := hγ
  rw [(fam_hyp (ζ := ζ) (γ := γ) hM ⊤).gradient_eq, (fam_hyp (ζ := ζ) (γ := γ) hM ⊤).gradient_eq,
    Real.inner_apply, mul_comm]

/-- **Proposition 8(a), attained**: for 0 < ρ with Mρ < γ, E is (γ − Mρ)-strongly convex on
B(0, ρ) and e′ is (γ − Mρ)-strongly monotone on B̄(0, ρ). -/
theorem prop8_a_attained (hγ : 0 < γ) (hM : 0 ≤ M) {ρ : ℝ} (hρ : 0 < ρ) (hMρ : M * ρ < γ) :
    StrongConvexOn (ball (0:ℝ) ρ) (kappa γ M ρ) (famE ζ γ M) ∧
    ∀ x ∈ closedBall (0:ℝ) ρ, ∀ y ∈ closedBall (0:ℝ) ρ,
      kappa γ M ρ * (x - y) ^ 2 ≤ (famD1 ζ γ M x - famD1 ζ γ M y) * (x - y) := by
  have h := (fam_hyp (ζ := ζ) (γ := γ) hM ⊤).toHyp hγ hM (by simp)
  obtain ⟨-, hsc, hmono⟩ := h.lemma2 hρ le_top hMρ
  refine ⟨hsc, fun x hx y hy => ?_⟩
  have := hmono x hx y hy
  rwa [fam_inner hγ hM, Real.norm_eq_abs, sq_abs] at this

/-- **Proposition 8(a), sharp (monotonicity form)**: if e′ is κ-strongly monotone on B̄(0, ρ)
then κ ≤ γ − Mρ. -/
theorem prop8_a_sharp_mono (hM : 0 < M) {ρ : ℝ} (hρ : 0 < ρ) {κ : ℝ}
    (hκ : ∀ x ∈ closedBall (0:ℝ) ρ, ∀ y ∈ closedBall (0:ℝ) ρ,
      κ * (x - y) ^ 2 ≤ (famD1 ζ γ M x - famD1 ζ γ M y) * (x - y)) :
    κ ≤ kappa γ M ρ := by
  by_contra hlt
  push Not at hlt
  set ε := min ρ ((κ - kappa γ M ρ) / M)
  have hε0 : 0 < ε := lt_min hρ (div_pos (by linarith) hM)
  have hερ : ε ≤ ρ := min_le_left _ _
  have hε2 : M * ε ≤ κ - kappa γ M ρ := by
    have := mul_le_mul_of_nonneg_left (min_le_right ρ ((κ - kappa γ M ρ) / M)) hM.le
    rwa [mul_div_cancel₀ _ hM.ne'] at this
  have hc : ∀ x, x ∈ closedBall (0:ℝ) ρ ↔ |x| ≤ ρ := fun x => by
    rw [mem_closedBall, dist_zero_right, Real.norm_eq_abs]
  have := hκ ρ ((hc ρ).2 (by rw [abs_of_pos hρ])) (ρ - ε)
    ((hc _).2 (by rw [abs_le]; constructor <;> linarith))
  rw [famD1, famD1, abs_of_pos hρ, abs_of_nonneg (by linarith : 0 ≤ ρ - ε),
    show ρ - (ρ - ε) = ε by ring] at this
  have e : (-ζ + γ * ρ - M / 2 * ρ * ρ - (-ζ + γ * (ρ - ε) - M / 2 * (ρ - ε) * (ρ - ε))) * ε =
      ε ^ 2 * (kappa γ M ρ + M * ε / 2) := by simp only [kappa]; ring
  rw [e] at this
  have h5 : κ * ε ^ 2 ≤ (kappa γ M ρ + M * ε / 2) * ε ^ 2 := by linarith
  have h6 := le_of_mul_le_mul_right h5 (by positivity)
  linarith

/-- **Proposition 8(a), sharp (strong convexity)**: if E is κ-strongly convex on B(0, ρ) then
κ ≤ γ − Mρ. Together with `prop8_a_attained`, γ − Mρ is the largest such κ. -/
theorem prop8_a_sharp_convex (hM : 0 < M) {ρ : ℝ} (hρ : 0 < ρ) {κ : ℝ}
    (hκ : StrongConvexOn (ball (0:ℝ) ρ) κ (famE ζ γ M)) : κ ≤ kappa γ M ρ := by
  have hc := strongConvexOn_iff_convex.1 hκ
  set g : ℝ → ℝ := fun x => famE ζ γ M x - κ / 2 * ‖x‖ ^ 2
  have hg : ∀ x, HasDerivAt g (famD1 ζ γ M x - κ * x) x := by
    intro x
    have h1 := (fam_hyp (ζ := ζ) (γ := γ) hM.le ⊤).d1 x
    have h2 : HasDerivAt (fun x : ℝ => ‖x‖ ^ 2) (2 * x) x := by
      have := (hasDerivAt_id x).norm_sq
      simpa [Real.inner_apply] using this
    have h3 := h1.sub (h2.const_mul (κ / 2))
    rw [show famD1 ζ γ M x - κ * x = famD1 ζ γ M x - κ / 2 * (2 * x) by ring]
    exact h3
  have hmono := hc.monotoneOn_deriv (fun x _ => (hg x).differentiableAt)
  by_contra hlt
  push Not at hlt
  set ε := min ρ ((κ - kappa γ M ρ) / M)
  have hε0 : 0 < ε := lt_min hρ (div_pos (by linarith) hM)
  have hερ : ε ≤ ρ := min_le_left _ _
  have hε2 : M * ε ≤ κ - kappa γ M ρ := by
    have := mul_le_mul_of_nonneg_left (min_le_right ρ ((κ - kappa γ M ρ) / M)) hM.le
    rwa [mul_div_cancel₀ _ hM.ne'] at this
  have hb : ∀ x, x ∈ ball (0:ℝ) ρ ↔ |x| < ρ := fun x => by
    rw [mem_ball, dist_zero_right, Real.norm_eq_abs]
  have hy : ρ - ε ∈ ball (0:ℝ) ρ := (hb _).2 (by rw [abs_lt]; constructor <;> linarith)
  have hx : ρ - ε / 2 ∈ ball (0:ℝ) ρ := (hb _).2 (by rw [abs_lt]; constructor <;> linarith)
  have := hmono hy hx (by linarith)
  rw [(hg _).deriv, (hg _).deriv, famD1, famD1, abs_of_nonneg (by linarith : 0 ≤ ρ - ε),
    abs_of_nonneg (by linarith : 0 ≤ ρ - ε / 2)] at this
  have e : (-ζ + γ * (ρ - ε / 2) - M / 2 * (ρ - ε / 2) * (ρ - ε / 2) - κ * (ρ - ε / 2)) -
      (-ζ + γ * (ρ - ε) - M / 2 * (ρ - ε) * (ρ - ε) - κ * (ρ - ε)) =
      ε / 2 * (kappa γ M ρ + 3 * M * ε / 4 - κ) := by simp only [kappa]; ring
  have h4 : 0 ≤ ε / 2 * (kappa γ M ρ + 3 * M * ε / 4 - κ) := by linarith
  have h5 : 0 ≤ kappa γ M ρ + 3 * M * ε / 4 - κ := by
    by_contra hneg
    push Not at hneg
    have := mul_neg_of_pos_of_neg (by linarith : 0 < ε / 2) hneg
    linarith
  linarith

/-! ### Proposition 8(b): the steep-drop modification e_K (S8.3b) -/

/-- Right half of e_K′ (x ≥ 0), as polynomial pieces glued at R. -/
noncomputable def sdP (γ M R K x : ℝ) : ℝ :=
  if x ≤ R then 0 + (γ * x + -(M / 2) * x ^ 2)
  else (phi γ M R - (γ - M * R) * R - K / 2 * R ^ 2) +
    (((γ - M * R) + K * R) * x + -(K / 2) * x ^ 2)

noncomputable def sdP' (γ M R K x : ℝ) : ℝ :=
  if x ≤ R then γ + 2 * (-(M / 2)) * x else ((γ - M * R) + K * R) + 2 * (-(K / 2)) * x

/-- e_K′(x) = −ζ + (odd extension of sdP). -/
noncomputable def sdD1 (ζ γ M R K x : ℝ) : ℝ :=
  -ζ + (if x ≤ 0 then -sdP γ M R K (-x) else sdP γ M R K x)

/-- e_K″(x) = γ − M|x| for |x| ≤ R and a − K(|x| − R) for |x| > R (a = γ − MR). -/
noncomputable def sdD2 (γ M R K x : ℝ) : ℝ := sdP' γ M R K |x|

noncomputable def sdE (ζ γ M R K x : ℝ) : ℝ := ∫ t in (0:ℝ)..x, sdD1 ζ γ M R K t

section SteepDrop
variable {R K : ℝ}

lemma sdD2_eq (x : ℝ) : sdD2 γ M R K x =
    if |x| ≤ R then γ - M * |x| else (γ - M * R) - K * (|x| - R) := by
  simp only [sdD2, sdP']; split_ifs <;> ring

lemma sdP_left {x : ℝ} (hx : x ≤ R) : sdP γ M R K x = phi γ M x := by
  simp only [sdP, if_pos hx, phi]; ring

lemma sdP_right {x : ℝ} (hx : R < x) : sdP γ M R K x =
    phi γ M R + (γ - M * R) * (x - R) - K / 2 * (x - R) ^ 2 := by
  simp only [sdP, if_neg (not_le.2 hx)]; ring

lemma sdP_hasDerivAt (x : ℝ) : HasDerivAt (sdP γ M R K) (sdP' γ M R K x) x :=
  hasDerivAt_ite_le (c := R)
    (fun x => (hasDerivAt_quad γ (-(M / 2)) x).const_add 0)
    (fun x => (hasDerivAt_quad ((γ - M * R) + K * R) (-(K / 2)) x).const_add _)
    (by simp only [phi]; ring) (by ring) x

lemma sdD1_hasDerivAt (hR : 0 ≤ R) (x : ℝ) :
    HasDerivAt (sdD1 ζ γ M R K) (sdD2 γ M R K x) x := by
  have hodd : ∀ x, HasDerivAt (fun y => -sdP γ M R K (-y)) (sdP' γ M R K (-x)) x := by
    intro x
    have := ((sdP_hasDerivAt (γ := γ) (M := M) (R := R) (K := K) (-x)).comp x
      (hasDerivAt_neg x)).neg
    rw [show sdP' γ M R K (-x) = -(sdP' γ M R K (-x) * -1) by ring]
    exact this
  have h0 : sdP γ M R K 0 = 0 := by rw [sdP_left hR]; simp [phi]
  have := hasDerivAt_ite_le (c := 0) hodd (sdP_hasDerivAt (γ := γ) (M := M) (R := R) (K := K))
    (by simp [h0]) (by simp) x
  have h2 : (if x ≤ 0 then sdP' γ M R K (-x) else sdP' γ M R K x) = sdD2 γ M R K x := by
    simp only [sdD2]; split_ifs with hx
    · rw [abs_of_nonpos hx]
    · rw [abs_of_pos (not_le.1 hx)]
  rw [← h2]
  exact this.const_add (-ζ)

lemma sdD2_cont : Continuous (sdD2 γ M R K) := by
  have : Continuous (sdP' γ M R K) := by
    unfold sdP'
    exact Continuous.if_le (by fun_prop) (by fun_prop) continuous_id continuous_const
      (fun x hx => by rw [hx]; ring)
  exact this.comp continuous_abs

/-- S8.3b: e_K satisfies (H1)–(H3) with this γ, M and R (finite, 0 < R). -/
theorem sd_hyp (hR : 0 < R) (hM : 0 ≤ M) :
    Hyp1D (sdE ζ γ M R K) (sdD1 ζ γ M R K) (sdD2 γ M R K) γ M (ENNReal.ofReal R) := by
  have hd := sdD1_hasDerivAt (ζ := ζ) (γ := γ) (M := M) (K := K) hR.le
  have hc : Continuous (sdD1 ζ γ M R K) :=
    continuous_iff_continuousAt.2 fun x => (hd x).continuousAt
  refine ⟨fun x => (hc.integral_hasStrictDerivAt 0 x).hasDerivAt, hd, sdD2_cont, ?_, ?_⟩
  · rw [sdD2_eq, if_pos (by simp [hR.le])]; simp
  · intro x hx
    have hxR : |x| < R := (ENNReal.ofReal_lt_ofReal_iff hR).1 hx
    rw [sdD2_eq, sdD2_eq, if_pos hxR.le, if_pos (by simp [hR.le])]
    simp [abs_mul, abs_of_nonneg hM]

end SteepDrop

/-- **Proposition 8(b)** (uniqueness radius): for every R ∈ (0, ∞] and ε > 0 there is E
satisfying (H1)–(H3) with these γ, M > 0, R, having two distinct stationary points in
B(0, r₀ + ε). So r₀ = min{R, γ/M} cannot be enlarged. -/
theorem prop8_b (hγ : 0 < γ) (hM : 0 < M) {R : ℝ≥0∞} (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    ∃ e e' e'' : ℝ → ℝ, Hyp1D e e' e'' γ M R ∧ ∃ x₁ x₂ : ℝ, x₁ ≠ x₂ ∧ e' x₁ = 0 ∧ e' x₂ = 0 ∧
      |x₁| < (r0 R γ M).toReal + ε ∧ |x₂| < (r0 R γ M).toReal + ε := by
  have hr0eq : r0 R γ M = min R (ENNReal.ofReal (γ / M)) := by
    unfold r0; rw [ENNReal.ofReal_div_of_pos hM]
  rcases le_or_gt (ENNReal.ofReal (γ / M)) R with hle | hlt
  · -- S8.3: r₀ = γ/M, the family itself
    have hr : (r0 R γ M).toReal = γ / M := by
      rw [hr0eq, min_eq_right hle, ENNReal.toReal_ofReal (div_pos hγ hM).le]
    set δ := min (γ ^ 2 / (4 * M)) (M * ε ^ 2 / 4) with hδ
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδ1 : δ ≤ γ ^ 2 / (4 * M) := min_le_left _ _
    have hδ2 : δ ≤ M * ε ^ 2 / 4 := min_le_right _ _
    set ζ' := γ ^ 2 / (2 * M) - δ
    have hζ' : 0 ≤ ζ' := by
      have : γ ^ 2 / (4 * M) ≤ γ ^ 2 / (2 * M) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
      linarith
    have hD : γ ^ 2 - 2 * M * ζ' = 2 * M * δ := by simp only [ζ']; field_simp; ring
    have hF : F3Hyp γ M ζ' := ⟨hγ, hM.le, hζ', by nlinarith⟩
    set S := Real.sqrt (2 * M * δ)
    have hS0 : 0 < S := Real.sqrt_pos.2 (by positivity)
    have hSγ : S ≤ γ := by
      rw [Real.sqrt_le_left hγ.le]
      have : 2 * M * δ ≤ 2 * M * (γ ^ 2 / (4 * M)) := by nlinarith
      rw [show 2 * M * (γ ^ 2 / (4 * M)) = γ ^ 2 / 2 by field_simp; ring] at this
      nlinarith
    have hSε : S < M * ε := by
      rw [show M * ε = Real.sqrt ((M * ε) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
      apply Real.sqrt_lt_sqrt (by positivity)
      nlinarith
    have roots := phi_eq_iff_roots hF hM
    rw [hD] at roots
    have hz : ∀ s, 0 ≤ s → phi γ M s = ζ' → famD1 ζ' γ M s = 0 := by
      intro s hs he
      have := (fam_facts (ζ := ζ') (γ := γ) hM.le hζ').2.2.2 s hs
      linarith
    have hm0 : 0 ≤ (γ - S) / M := div_nonneg (by linarith) hM.le
    have hp0 : 0 ≤ (γ + S) / M := div_nonneg (by linarith) hM.le
    refine ⟨famE ζ' γ M, famD1 ζ' γ M, famD2 γ M, fam_hyp hM.le R, (γ - S) / M, (γ + S) / M,
      ?_, hz _ hm0 ((roots _).2 (Or.inl rfl)), hz _ hp0 ((roots _).2 (Or.inr rfl)), ?_, ?_⟩
    · intro h
      rw [div_left_inj' hM.ne'] at h; linarith
    · rw [hr, abs_of_nonneg hm0]
      have : (γ - S) / M ≤ γ / M := div_le_div_of_nonneg_right (by linarith) hM.le
      linarith
    · rw [hr, abs_of_nonneg hp0, add_div]
      have : S / M < ε := by rw [div_lt_iff₀ hM]; linarith
      linarith
  · -- S8.3b: r₀ = R < γ/M, the steep-drop function
    have hRne : R ≠ ⊤ := ne_top_of_lt hlt
    set R' := R.toReal
    have hR'pos : 0 < R' := ENNReal.toReal_pos hR.ne' hRne
    have hRR' : R = ENNReal.ofReal R' := (ENNReal.ofReal_toReal hRne).symm
    have hr : (r0 R γ M).toReal = R' := by rw [hr0eq, min_eq_left hlt.le]
    have hR'γ : R' < γ / M := by
      have := (ENNReal.toReal_lt_toReal hRne ENNReal.ofReal_ne_top).2 hlt
      rwa [ENNReal.toReal_ofReal (div_pos hγ hM).le] at this
    have hMR : M * R' < γ := by rwa [lt_div_iff₀ hM, mul_comm] at hR'γ
    set a := γ - M * R'
    have ha : 0 ≤ a := by simp only [a]; linarith
    have hφR : 0 < phi γ M R' := by
      have := half_le_phi hR'pos.le hMR.le; nlinarith
    set ε' := ε / 2
    have hε' : 0 < ε' := by positivity
    set K := 4 * a / ε' + 1
    have hK : 0 < K := by positivity
    have hKε : 4 * a ≤ K * ε' := by
      simp only [K]; rw [add_mul, div_mul_cancel₀ _ hε'.ne']; linarith
    set δ := min (K * ε' ^ 2 / 8) (phi γ M R' / 2)
    have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
    have hδ1 : δ ≤ K * ε' ^ 2 / 8 := min_le_left _ _
    have hδ2 : δ ≤ phi γ M R' / 2 := min_le_right _ _
    set ζ' := phi γ M R' - δ
    have hζ'0 : 0 < ζ' := by simp only [ζ']; linarith
    have hR'D : R' ∈ Dom γ M := ⟨hR'pos.le, hMR.le⟩
    have hF : F3Hyp γ M ζ' := by
      refine ⟨hγ, hM.le, hζ'0.le, ?_⟩
      have := phi_le_max (γ := γ) hM R'
      have h3 : 2 * M * ζ' ≤ 2 * M * (γ ^ 2 / (2 * M)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity); simp only [ζ']; linarith
      rwa [show 2 * M * (γ ^ 2 / (2 * M)) = γ ^ 2 by field_simp] at h3
    -- first stationary point: s₋(ζ') ∈ (0, R')
    have hx1R : sMinus γ M ζ' < R' := (sMinus_lt_iff hF hR'D).2 (by simp only [ζ']; linarith)
    have hx1pos : 0 < sMinus γ M ζ' := by
      simp only [sMinus]; exact div_pos (by linarith) hF.denom_pos
    have hz1 : sdD1 ζ' γ M R' K (sMinus γ M ζ') = 0 := by
      rw [sdD1, if_neg (not_le.2 hx1pos), sdP_left hx1R.le, phi_sMinus hF]; ring
    -- second stationary point: R' + u*
    set S := Real.sqrt (a ^ 2 + 2 * K * δ)
    have hS2 : S ^ 2 = a ^ 2 + 2 * K * δ := Real.sq_sqrt (by positivity)
    have hS0 : 0 ≤ S := Real.sqrt_nonneg _
    set u := (a + S) / K
    have hu0 : 0 < u := by
      apply div_pos _ hK
      have : 0 < S := Real.sqrt_pos.2 (by positivity)
      linarith
    have huε : u ≤ ε' := by
      rw [div_le_iff₀ hK]
      have hSle : S ≤ K * ε' - a := by
        rw [show K * ε' - a = Real.sqrt ((K * ε' - a) ^ 2) by
          rw [Real.sqrt_sq (by linarith)]]
        apply Real.sqrt_le_sqrt
        nlinarith [mul_le_mul_of_nonneg_left hKε (by positivity : 0 ≤ K * ε')]
      linarith
    have hz2 : sdD1 ζ' γ M R' K (R' + u) = 0 := by
      rw [sdD1, if_neg (by linarith), sdP_right (by linarith), show R' + u - R' = u by ring]
      have : K / 2 * u ^ 2 = a * u + δ := by
        simp only [u]; field_simp; nlinarith [hS2]
      simp only [ζ', a] at this ⊢; linarith
    refine ⟨sdE ζ' γ M R' K, sdD1 ζ' γ M R' K, sdD2 γ M R' K, ?_, sMinus γ M ζ', R' + u, ?_, hz1,
      hz2, ?_, ?_⟩
    · rw [hRR']; exact sd_hyp hR'pos hM.le
    · intro h; linarith
    · rw [hr, abs_of_pos hx1pos]; linarith
    · rw [hr, abs_of_pos (by linarith)]; simp only [ε'] at huε; linarith

end Family

end Sharp

/-- ℝᵈ with d ≥ 1 (`EuclideanSpace ℝ (Fin d)`, operator norm = spectral norm) is an instance of
the setting of Parts G–H. -/
example (d : ℕ) [NeZero d] :
    ProperSpace (EuclideanSpace ℝ (Fin d)) ∧ Nontrivial (EuclideanSpace ℝ (Fin d)) ∧
      CompleteSpace (EuclideanSpace ℝ (Fin d)) :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end OCF.C3

/-
D1 (Rate as a function of the regularisation weight) — Lemma D1.1(a)–(c); Proposition
D1.4(b) (exact bias identity, two-sided displacement bounds, data-fit identity); Proposition
D1.5(a) (the declared affine ratio is monotone); Example ex:cond-weight(i) (the witness family
H = diag(1, s, t), Q = diag(1, 0, 0)); and the continuity and quasiconvexity clauses of
Theorem D1.2(a). This is the cheap slice recommended by DECISION 4 of the stage-3
adjudication, plus the moderate witness family and quasiconvexity items.

Source of truth: project_plan/done/proof_audits/D1_rate_vs_weight/01_derivation.md (stage-1 dossier
revised at stage 3 and its re-audit addendum; sha16 c89880119334ba37 at the start and at the
end of formalisation; file not edited), 03_adjudication.md (DECISION 4 and the addendum), and
the stage-4 draft 04_landing_draft.tex (Theorem thm:cond-weight, Example ex:cond-weight,
Proposition prop:weight-bias). Lemma D1.1(d), Theorem D1.2(a) trichotomy and (b)–(d),
Corollary D1.3, Proposition D1.4(a) and (c), Proposition D1.5(o) and (b), Remark D1.6 and
Observation D1.7 are not attempted here (PROSE-ONLY by ruling).

DEFINITIONAL MAP:
* 𝕊^d (d ≥ 1) — `Matrix (Fin d) (Fin d) ℝ` with `IsHermitian`; H, Q ⪰ 0 — `PosSemidef`;
  ≻ 0 — `PosDef`; ker — `OCF.matKer` (T1KernelTransversality); ker H ∩ ker Q = {0} —
  `OCF.matKer H ⊓ OCF.matKer Q = ⊥`; "nonsingular" — `H.det ≠ 0`.
* λ_min — PSpectralGlue's `lamMin`; λ_max — T1GramBound's `OCF.lambdaMax`.
* H_θ = H + θQ — `H + θ • Q`; μ(θ) = λ_min(H_θ) — D0's `phi hH hQ hd θ` (reused, so Lemma
  D1.1(b)'s μ-half is D0's `lemma_D01_i_iv`); β(θ) = λ_max(H_θ) — `beta H Q θ`.
* Θ — `Theta H` ([0, ∞) if H ≻ 0, (0, ∞) otherwise); cond(θ) = β(θ)/μ(θ) — `cond`;
  set of minimisers of a function f on S — `minSet S f` = {θ ∈ S | ∀ θ' ∈ S, f θ ≤ f θ'}.
* ‖·‖ (Euclidean) — `l2 v = √(vᵀv)`; `l2_eq_norm_toLp` identifies it with the norm of
  `EuclideanSpace ℝ (Fin d)` (the default norm on `Fin d → ℝ` is the sup norm).
* f = ½xᵀHx − bᵀx, r = ½xᵀQx − hᵀx — `quadF H b`, `quadF Q h`; E_θ = f + θr —
  `energy H Q b h θ`; ∇r(x) = Qx − h — `gradQ Q h x` (the dossier's formula; `fderiv_quadF`
  proves it is the gradient: the Fréchet derivative in direction v is ⟨Qx − h, v⟩);
  x*₀ ∈ argmin f — `∀ y, quadF H b x₀ ≤ quadF H b y`; x*_θ — `(H + θ • Q)⁻¹ *ᵥ (b + θ • h)`,
  proved to be the unique minimiser of E_θ.
* σ̂(θ)/β̂(θ) = (σ_f + θσ_r)/(β_f + θβ_r) — `declRatio`; the certified factor 1 − σ̂/β̂ —
  `declFactor`; "no interior optimum unless constant" — `IsMinOn`/`IsMaxOn` on (0, ∞) at
  θ₀ > 0 forces constancy on (0, ∞).
* Witness family — `Hw s t = diagonal ![1, s, t]`, `Qw = diagonal ![1, 0, 0]`.
* Quasiconvexity — Mathlib's `QuasiconvexOn ℝ (Theta H) cond`.

THEOREMS:
* Lemma D1.1(a): `lemma_D11_a` (bundle: ker H ∩ ker Q = {0} ⇒ H_θ ≻ 0 and μ(θ) > 0 for θ > 0;
  H ≻ 0 ⟺ det H ≠ 0 ⟺ ker H = {0}; ker H ∩ ker Q ≠ {0} ⇒ μ ≡ 0 on [0, ∞); the converse
  `posDef_ray_iff`: H_θ ≻ 0 for every θ > 0 ⟺ ker H ∩ ker Q = {0}).
* Lemma D1.1(b): `lemma_D11_b` (μ concave, non-decreasing on [0, ∞) — from D0; β convex,
  non-decreasing on [0, ∞); μ, β continuous on ℝ). Pieces `beta_convexOn_univ`,
  `beta_monotone`, `phi_continuous`, `beta_continuous`.
* Lemma D1.1(c): `lemma_D11_c` (the four Weyl/Rayleigh bounds, θ ≥ 0).
* Proposition D1.4(b): `prop_D14b` (H_θ invertible; x*_θ = H_θ⁻¹(b + θh) is the unique
  minimiser of E_θ; x*_θ − x*₀ = −θH_θ⁻¹∇r(x*₀); θ‖∇r(x*₀)‖/β(θ) ≤ ‖x*_θ − x*₀‖ ≤
  θ‖∇r(x*₀)‖/μ(θ), the bounds differing by the factor cond(θ); f(x*_θ) − f(x*₀) =
  ½ΔᵀHΔ ≥ 0). Gradient check `fderiv_quadF`.
* Proposition D1.5(a): `prop_D15a_identity` (the difference identity), `prop_D15a_monotone`
  (non-increasing if σ_r/β_r ≥ σ_f/β_f, non-decreasing otherwise; strict unless equal;
  constant if equal), `prop_D15a_no_interior_optimum`, `prop_D15a_kernel` (σ_r = 0:
  non-decreasing; σ_f = σ_r = 0: ≡ 1).
* Theorem D1.2(a), continuity and quasiconvexity: `cond_continuousOn`, `cond_quasiconvexOn`;
  with `phi_pos_on_Theta` (cond well defined on Θ) and `one_le_cond`.
* Example ex:cond-weight(i): `witness_hyps` (H ⪰ 0, H ≻ 0, Q ⪰ 0, Q ≠ 0, kernel case,
  ker H ∩ ker Q = {0}), `witness_cond` (cond = max{1 + θ, t}/min{1 + θ, s}),
  `witness_minSet` (Θ = [0, ∞), minimiser set [s − 1, t − 1], minimum t/s),
  `witness_every_shape` (every [a, b] with 0 ≤ a ≤ b is a minimiser set),
  `witness_four_shapes` ({0}, [0, 1], {1}, [1, 2]).

HYPOTHESES DROPPED (theorems proved under fewer hypotheses than stated, i.e. stronger):
Q ≠ 0 is never used in Lemma D1.1(a)–(c) or Proposition D1.4(b). Lemma D1.1(b)–(c) need only
H symmetric (not H ⪰ 0). Proposition D1.5(a) is pure algebra: it uses only β_f, β_r > 0
(not σ_f, σ_r ≥ 0, nor the validity of the declarations), except that the kernel-case reading
uses σ_f ≥ 0. No hypothesis was strengthened.

PROOF ROUTE: as the dossier — Rayleigh quotients throughout (S1.1–S1.7); β convex as a
supremum of affine functions, proved directly. Continuity via Mathlib's
`ConvexOn.continuousOn`/`ConcaveOn.continuousOn` (in place of Bauschke–Combettes Cor. 8.40).
Proposition D1.4(b): first-order condition by a discriminant argument
(`gradQ_eq_zero_of_isMin`), uniqueness by the exact quadratic expansion (`quadF_add`); the
lower bound ‖H_θΔ‖ ≤ β‖Δ‖ by Cauchy–Schwarz for the form of H_θ (`mulVec_dot_le_lambdaMax_sq`)
instead of the Lipschitz route of S4.4 (the same inequality). Quasiconvexity: the sublevel set
{cond ≤ r} ∩ Θ equals {β − rμ ≤ 0} ∩ Θ, convex for r ≥ 0 and empty for r < 0 (the content of
Boyd–Vandenberghe Ex. 3.38).

Status tier: FORMALISED (statement + proof, no sorry) for Lemma D1.1(a)–(c), Proposition
D1.4(b), Proposition D1.5(a), the continuity and quasiconvexity clauses of Theorem D1.2(a),
and the witness family of Example ex:cond-weight(i).
-/
import Mathlib
import OcfVerification.D0RegulariserEffect

open Matrix BigOperators Filter Topology

namespace OCF.D1

open OCF.P (lamMin)
open OCF.D0 (phi isHermitian_ray quad_ray phi_le exists_phi_eq phi_zero lamMin_le_quad
  lamMin_mul_le exists_unit_lamMin exists_unit_eigvec_lamMin exists_unit_lambdaMax
  lamMin_le_lambdaMax quad_nonneg phi_ge_weyl phi_concaveOn phi_concaveOn_univ phi_monotone
  phi_monotoneOn lemma_D01_i_iv lamMin_congr dot_mulVec_comm dot_sq_le)

/-! ## §0 Basic facts about PSD matrices and the Euclidean norm -/

section Basic

variable {n : ℕ}

lemma dot_self_nonneg (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simpa using dotProduct_self_star_nonneg v

lemma dot_self_pos {v : Fin n → ℝ} (hv : v ≠ 0) : 0 < v ⬝ᵥ v :=
  lt_of_le_of_ne (dot_self_nonneg v) (fun h => hv (dotProduct_self_eq_zero.mp h.symm))

/-- The Euclidean norm ‖v‖ = √(vᵀv) on ℝⁿ (the default norm on `Fin n → ℝ` is the sup norm,
so the Euclidean norm is written out; `l2_eq_norm_toLp` identifies it with the norm of
`EuclideanSpace ℝ (Fin n)`). -/
noncomputable def l2 (v : Fin n → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

lemma l2_eq_norm_toLp (v : Fin n → ℝ) :
    l2 v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [l2, EuclideanSpace.norm_eq]
  congr 1
  simp [dotProduct, sq]

lemma l2_nonneg (v : Fin n → ℝ) : 0 ≤ l2 v := Real.sqrt_nonneg _

lemma l2_sq (v : Fin n → ℝ) : l2 v ^ 2 = v ⬝ᵥ v := Real.sq_sqrt (dot_self_nonneg v)

/-- Cauchy–Schwarz: |uᵀv| ≤ ‖u‖‖v‖. -/
lemma abs_dot_le (u v : Fin n → ℝ) : |u ⬝ᵥ v| ≤ l2 u * l2 v := by
  rw [l2, l2, ← Real.sqrt_mul (dot_self_nonneg u)]
  exact Real.abs_le_sqrt (by rw [sq]; nlinarith [dot_sq_le u v])

lemma quad_nonneg_of_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ A *ᵥ x := by
  simpa using hA.dotProduct_mulVec_nonneg x

lemma mulVec_eq_zero_of_quad {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) {x : Fin n → ℝ}
    (h : x ⬝ᵥ A *ᵥ x = 0) : A *ᵥ x = 0 := by
  have := (hA.dotProduct_mulVec_zero_iff x).mp (by simpa using h)
  exact this

/-- For A ⪰ 0: A ≻ 0 iff ker A = {0}. -/
lemma posDef_iff_ker_eq_bot {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) :
    A.PosDef ↔ OCF.matKer A = ⊥ := by
  constructor
  · intro hpd
    rw [Submodule.eq_bot_iff]
    intro x hx
    by_contra hx0
    have hAx : A *ᵥ x = 0 := by simpa [mulVecLin_apply] using hx
    have := hpd.dotProduct_mulVec_pos hx0
    rw [hAx, dotProduct_zero] at this
    exact lt_irrefl _ this
  · intro hK
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hA.1 fun x hx0 => ?_
    rw [star_trivial]
    refine lt_of_le_of_ne (quad_nonneg_of_psd hA x) (Ne.symm fun h => hx0 ?_)
    have hAx := mulVec_eq_zero_of_quad hA h
    have hmem : x ∈ OCF.matKer A := by simpa [mulVecLin_apply] using hAx
    rw [hK, Submodule.mem_bot] at hmem
    exact hmem

/-- For A ⪰ 0: ker A = {0} iff A is nonsingular. -/
lemma ker_eq_bot_iff_det_ne_zero {A : Matrix (Fin n) (Fin n) ℝ} :
    OCF.matKer A = ⊥ ↔ A.det ≠ 0 := by
  rw [Ne, ← Matrix.exists_mulVec_eq_zero_iff, Submodule.eq_bot_iff]
  constructor
  · rintro h ⟨v, hv0, hv⟩
    exact hv0 (h v (by simpa [mulVecLin_apply] using hv))
  · intro h x hx
    by_contra hx0
    exact h ⟨x, hx0, by simpa [mulVecLin_apply] using hx⟩

/-- For a symmetric A: A ≻ 0 iff λ_min(A) > 0. -/
lemma posDef_iff_lamMin_pos {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n) :
    A.PosDef ↔ 0 < lamMin hA hn := by
  constructor
  · intro hpd
    obtain ⟨x, hx, hxA⟩ := exists_unit_lamMin hA hn
    have hx0 : x ≠ 0 := by rintro rfl; simp at hx
    have := hpd.dotProduct_mulVec_pos hx0
    rw [star_trivial, hxA] at this
    exact this
  · intro hpos
    refine Matrix.PosDef.of_dotProduct_mulVec_pos hA fun x hx0 => ?_
    rw [star_trivial]
    have := lamMin_mul_le hA hn x
    have := dot_self_pos hx0
    nlinarith

lemma lamMin_nonneg_of_psd {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef) (hn : 0 < n) :
    0 ≤ lamMin hA.1 hn := by
  obtain ⟨x, -, hxA⟩ := exists_unit_lamMin hA.1 hn
  rw [← hxA]; exact quad_nonneg_of_psd hA x

/-- For A ⪰ 0: ‖Av‖² ≤ λ_max(A)²‖v‖² (via Cauchy–Schwarz for the form of A). -/
lemma mulVec_dot_le_lambdaMax_sq {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (v : Fin n → ℝ) : (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ OCF.lambdaMax A ^ 2 * (v ⬝ᵥ v) := by
  set w := A *ᵥ v with hw
  set β := OCF.lambdaMax A
  have hβ0 : 0 ≤ β := OCF.lambdaMax_nonneg hA
  have hsym : w ⬝ᵥ A *ᵥ v = v ⬝ᵥ A *ᵥ w := dot_mulVec_comm hA.1 w v
  have hdisc := discrim_le_zero (a := v ⬝ᵥ A *ᵥ v) (b := 2 * (w ⬝ᵥ A *ᵥ v))
    (c := w ⬝ᵥ A *ᵥ w) (fun t => by
      have h := quad_nonneg_of_psd hA (w + t • v)
      simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
        smul_dotProduct, smul_eq_mul] at h
      rw [← hsym] at h
      nlinarith)
  unfold discrim at hdisc
  have hwv : w ⬝ᵥ A *ᵥ v = w ⬝ᵥ w := by rw [← hw]
  rw [hwv] at hdisc
  have h1 := OCF.dotProduct_mulVec_le_lambdaMax hA.1 v
  have h2 := OCF.dotProduct_mulVec_le_lambdaMax hA.1 w
  have h3 := quad_nonneg_of_psd hA v
  have h4 := quad_nonneg_of_psd hA w
  have hww := dot_self_nonneg w
  have hvv := dot_self_nonneg v
  have hprod : (v ⬝ᵥ A *ᵥ v) * (w ⬝ᵥ A *ᵥ w) ≤ (β * (v ⬝ᵥ v)) * (β * (w ⬝ᵥ w)) :=
    mul_le_mul h1 h2 h4 (by positivity)
  rcases hww.lt_or_eq with hpos | hzero
  · have : (w ⬝ᵥ w) * (w ⬝ᵥ w) ≤ (β ^ 2 * (v ⬝ᵥ v)) * (w ⬝ᵥ w) := by nlinarith
    exact le_of_mul_le_mul_right this hpos
  · rw [← hzero]; positivity

end Basic

/-! ## Lemma D1.1 — both ends of the spectrum along the ray -/

section Ray

variable {d : ℕ} {H Q : Matrix (Fin d) (Fin d) ℝ}

/-- β(θ) := λ_max(H + θQ). (μ(θ) := λ_min(H + θQ) is D0's `phi`.) -/
noncomputable def beta (H Q : Matrix (Fin d) (Fin d) ℝ) (θ : ℝ) : ℝ :=
  OCF.lambdaMax (H + θ • Q)

lemma quad_le_beta (hH : H.IsHermitian) (hQ : Q.IsHermitian) (θ : ℝ) {x : Fin d → ℝ}
    (hx : x ⬝ᵥ x = 1) : x ⬝ᵥ H *ᵥ x + θ * (x ⬝ᵥ Q *ᵥ x) ≤ beta H Q θ := by
  have h := OCF.dotProduct_mulVec_le_lambdaMax (isHermitian_ray hH hQ θ) x
  rw [hx, mul_one, quad_ray] at h
  exact h

lemma exists_beta_eq (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) (θ : ℝ) :
    ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ beta H Q θ = x ⬝ᵥ H *ᵥ x + θ * (x ⬝ᵥ Q *ᵥ x) := by
  obtain ⟨x, hx, hxA⟩ := exists_unit_lambdaMax (isHermitian_ray hH hQ θ) hd
  exact ⟨x, hx, by rw [beta, ← hxA, quad_ray]⟩

lemma beta_zero : beta H Q 0 = OCF.lambdaMax H := by simp [beta]

/-- β is convex on all of ℝ (S1.4: a supremum of affine functions). -/
theorem beta_convexOn_univ (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) :
    ConvexOn ℝ Set.univ (beta H Q) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  obtain ⟨x, hx, hβ⟩ := exists_beta_eq hH hQ hd (a • s + b • t)
  have h1 := quad_le_beta hH hQ s hx
  have h2 := quad_le_beta hH hQ t hx
  simp only [smul_eq_mul] at hβ ⊢
  have e : a * (x ⬝ᵥ H *ᵥ x + s * (x ⬝ᵥ Q *ᵥ x)) + b * (x ⬝ᵥ H *ᵥ x + t * (x ⬝ᵥ Q *ᵥ x))
      = (a + b) * (x ⬝ᵥ H *ᵥ x) + (a * s + b * t) * (x ⬝ᵥ Q *ᵥ x) := by ring
  rw [hab, one_mul] at e
  rw [hβ, ← e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- β is non-decreasing (S1.5), on all of ℝ since Q ⪰ 0. -/
theorem beta_monotone (hH : H.IsHermitian) (hQpsd : Q.PosSemidef) (hd : 0 < d) :
    Monotone (beta H Q) := by
  intro s t hst
  obtain ⟨x, hx, hβ⟩ := exists_beta_eq hH hQpsd.1 hd s
  have h1 := quad_le_beta hH hQpsd.1 t hx
  have := quad_nonneg_of_psd hQpsd x
  rw [hβ]; nlinarith

theorem phi_continuous (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) :
    Continuous (phi hH hQ hd) := by
  rw [← continuousOn_univ]
  exact (phi_concaveOn_univ hH hQ hd).continuousOn isOpen_univ

theorem beta_continuous (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) :
    Continuous (beta H Q) := by
  rw [← continuousOn_univ]
  exact (beta_convexOn_univ hH hQ hd).continuousOn isOpen_univ

/-- For H, Q ⪰ 0 and θ > 0: ker(H + θQ) = ker H ∩ ker Q. -/
lemma ker_ray (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) {θ : ℝ} (hθ : 0 < θ) :
    OCF.matKer (H + θ • Q) = OCF.matKer H ⊓ OCF.matKer Q := by
  ext x
  simp only [Submodule.mem_inf, LinearMap.mem_ker, mulVecLin_apply]
  constructor
  · intro hx
    have hq : x ⬝ᵥ (H + θ • Q) *ᵥ x = 0 := by rw [hx, dotProduct_zero]
    rw [quad_ray] at hq
    have h1 := quad_nonneg_of_psd hHpsd x
    have h2 := quad_nonneg_of_psd hQpsd x
    have hH0 : x ⬝ᵥ H *ᵥ x = 0 := by nlinarith
    have hQ0 : x ⬝ᵥ Q *ᵥ x = 0 := by
      have : θ * (x ⬝ᵥ Q *ᵥ x) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hθ.ne'
    exact ⟨mulVec_eq_zero_of_quad hHpsd hH0, mulVec_eq_zero_of_quad hQpsd hQ0⟩
  · rintro ⟨h1, h2⟩
    rw [add_mulVec, smul_mulVec, h1, h2, smul_zero, add_zero]

lemma psd_ray (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) {θ : ℝ} (hθ : 0 ≤ θ) :
    (H + θ • Q).PosSemidef :=
  hHpsd.add (hQpsd.smul hθ)

/-- **Lemma D1.1(a)**, the equivalence: H + θQ ≻ 0 for every θ > 0 iff ker H ∩ ker Q = {0}. -/
theorem posDef_ray_iff (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) :
    (∀ θ : ℝ, 0 < θ → (H + θ • Q).PosDef) ↔ OCF.matKer H ⊓ OCF.matKer Q = ⊥ := by
  constructor
  · intro h
    have := (posDef_iff_ker_eq_bot (psd_ray hHpsd hQpsd zero_le_one)).mp (h 1 one_pos)
    rwa [ker_ray hHpsd hQpsd one_pos] at this
  · intro hK θ hθ
    rw [posDef_iff_ker_eq_bot (psd_ray hHpsd hQpsd hθ.le), ker_ray hHpsd hQpsd hθ]
    exact hK

/-- **Lemma D1.1(a)** in full. For H, Q ⪰ 0 (d ≥ 1):
* if ker H ∩ ker Q = {0}, then H + θQ ≻ 0, equivalently μ(θ) > 0, for every θ > 0;
* H₀ = H is ≻ 0 iff H is nonsingular (iff ker H = {0});
* if ker H ∩ ker Q ≠ {0}, then μ(θ) = 0 for every θ ≥ 0;
* and (necessity) H + θQ ≻ 0 for all θ > 0 forces ker H ∩ ker Q = {0}. -/
theorem lemma_D11_a (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) (hd : 0 < d) :
    (OCF.matKer H ⊓ OCF.matKer Q = ⊥ →
      ∀ θ : ℝ, 0 < θ → (H + θ • Q).PosDef ∧ 0 < phi hHpsd.1 hQpsd.1 hd θ) ∧
    (H.PosDef ↔ H.det ≠ 0) ∧ (H.PosDef ↔ OCF.matKer H = ⊥) ∧
    (OCF.matKer H ⊓ OCF.matKer Q ≠ ⊥ → ∀ θ : ℝ, 0 ≤ θ → phi hHpsd.1 hQpsd.1 hd θ = 0) ∧
    ((∀ θ : ℝ, 0 < θ → (H + θ • Q).PosDef) ↔ OCF.matKer H ⊓ OCF.matKer Q = ⊥) := by
  refine ⟨fun hK θ hθ => ?_, ?_, posDef_iff_ker_eq_bot hHpsd, fun hK θ hθ => ?_,
    posDef_ray_iff hHpsd hQpsd⟩
  · have hpd := (posDef_ray_iff hHpsd hQpsd).mpr hK θ hθ
    exact ⟨hpd, (posDef_iff_lamMin_pos (isHermitian_ray hHpsd.1 hQpsd.1 θ) hd).mp hpd⟩
  · rw [posDef_iff_ker_eq_bot hHpsd, ker_eq_bot_iff_det_ne_zero]
  · apply le_antisymm
    · obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
      rw [Submodule.mem_inf] at hv
      have hHv : H *ᵥ v = 0 := by simpa [mulVecLin_apply] using hv.1
      have hQv : Q *ᵥ v = 0 := by simpa [mulVecLin_apply] using hv.2
      have h := lamMin_mul_le (isHermitian_ray hHpsd.1 hQpsd.1 θ) hd v
      rw [add_mulVec, smul_mulVec, hHv, hQv, smul_zero, add_zero, dotProduct_zero] at h
      have := dot_self_pos hv0
      change phi hHpsd.1 hQpsd.1 hd θ * (v ⬝ᵥ v) ≤ 0 at h
      nlinarith
    · have := lamMin_nonneg_of_psd (psd_ray hHpsd hQpsd hθ) hd
      exact this

/-- **Lemma D1.1(b)**: μ is concave and non-decreasing on [0, ∞) (D0 Lemma D0.1(i)–(ii),
reused); β is convex and non-decreasing on [0, ∞); μ and β are continuous on ℝ. -/
theorem lemma_D11_b (hH : H.IsHermitian) (hQpsd : Q.PosSemidef) (hd : 0 < d) :
    ConcaveOn ℝ (Set.Ici 0) (phi hH hQpsd.1 hd) ∧ MonotoneOn (phi hH hQpsd.1 hd) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (beta H Q) ∧ MonotoneOn (beta H Q) (Set.Ici 0) ∧
    Continuous (phi hH hQpsd.1 hd) ∧ Continuous (beta H Q) :=
  ⟨(lemma_D01_i_iv hH hQpsd.1 hd hQpsd).1, (lemma_D01_i_iv hH hQpsd.1 hd hQpsd).2.1,
    (beta_convexOn_univ hH hQpsd.1 hd).subset (Set.subset_univ _) (convex_Ici 0),
    (beta_monotone hH hQpsd hd).monotoneOn _, phi_continuous hH hQpsd.1 hd,
    beta_continuous hH hQpsd.1 hd⟩

/-- **Lemma D1.1(c)**: for every θ ≥ 0,
λ_min(H) + θλ_min(Q) ≤ μ(θ) ≤ λ_max(H) + θλ_min(Q) and
max{λ_max(H), λ_min(H) + θλ_max(Q)} ≤ β(θ) ≤ λ_max(H) + θλ_max(Q). -/
theorem lemma_D11_c (hH : H.IsHermitian) (hQpsd : Q.PosSemidef) (hd : 0 < d) {θ : ℝ}
    (hθ : 0 ≤ θ) :
    lamMin hH hd + θ * lamMin hQpsd.1 hd ≤ phi hH hQpsd.1 hd θ ∧
    phi hH hQpsd.1 hd θ ≤ OCF.lambdaMax H + θ * lamMin hQpsd.1 hd ∧
    max (OCF.lambdaMax H) (lamMin hH hd + θ * OCF.lambdaMax Q) ≤ beta H Q θ ∧
    beta H Q θ ≤ OCF.lambdaMax H + θ * OCF.lambdaMax Q := by
  have hQ := hQpsd.1
  refine ⟨?_, ?_, max_le ?_ ?_, ?_⟩
  · have := phi_ge_weyl hH hQ hd hθ
    rwa [phi_zero] at this
  · obtain ⟨u, hu, hQu⟩ := exists_unit_lamMin hQ hd
    have h1 := phi_le hH hQ hd θ hu
    have h2 := OCF.dotProduct_mulVec_le_lambdaMax hH u
    rw [hu, mul_one] at h2
    rw [hQu] at h1
    linarith
  · rw [← beta_zero (Q := Q)]; exact beta_monotone hH hQpsd hd hθ
  · obtain ⟨v, hv, hQv⟩ := exists_unit_lambdaMax hQ hd
    have h1 := quad_le_beta hH hQ θ hv
    have h2 := lamMin_le_quad hd hH hv
    rw [hQv] at h1
    linarith
  · obtain ⟨x, hx, hβ⟩ := exists_beta_eq hH hQ hd θ
    have h1 := OCF.dotProduct_mulVec_le_lambdaMax hH x
    have h2 := OCF.dotProduct_mulVec_le_lambdaMax hQ x
    rw [hx, mul_one] at h1 h2
    rw [hβ]; nlinarith

end Ray

/-! ## Proposition D1.4(b) — the minimiser moves (quadratic case) -/

section Bias

variable {d : ℕ}

/-- The convex quadratic x ↦ ½xᵀAx − cᵀx (H_D1c: f = `quadF H b`, r = `quadF Q h`). -/
noncomputable def quadF (A : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) (x : Fin d → ℝ) : ℝ :=
  1 / 2 * (x ⬝ᵥ A *ᵥ x) - c ⬝ᵥ x

/-- ∇r(x) = Qx − h, the dossier's formula (H_D1c); `hasGradientAt_quadF` checks that it is the
gradient of `quadF Q h` for the Euclidean inner product. -/
def gradQ (A : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  A *ᵥ x - c

/-- E_θ := f + θ r. -/
noncomputable def energy (H Q : Matrix (Fin d) (Fin d) ℝ) (b h : Fin d → ℝ) (θ : ℝ)
    (x : Fin d → ℝ) : ℝ :=
  quadF H b x + θ * quadF Q h x

/-- Exact expansion of a quadratic with symmetric A around x. -/
lemma quadF_add {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (c x ξ : Fin d → ℝ) :
    quadF A c (x + ξ) = quadF A c x + gradQ A c x ⬝ᵥ ξ + 1 / 2 * (ξ ⬝ᵥ A *ᵥ ξ) := by
  have hs : ξ ⬝ᵥ A *ᵥ x = x ⬝ᵥ A *ᵥ ξ := dot_mulVec_comm hA ξ x
  simp only [quadF, gradQ, mulVec_add, dotProduct_add, add_dotProduct, sub_dotProduct]
  rw [hs, dotProduct_comm (A *ᵥ x) ξ, dotProduct_comm c ξ, dotProduct_mulVec x A ξ,
    ← mulVec_transpose, OCF.D0.transpose_eq_of_isHermitian hA, dotProduct_comm (A *ᵥ x) ξ]
  ring

lemma differentiable_quadF (A : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    Differentiable ℝ (quadF A c) := by
  unfold quadF
  simp only [dotProduct, mulVec]
  fun_prop

/-- `gradQ A c x` is the gradient of `quadF A c` at x (A symmetric): the Fréchet derivative
of the quadratic in direction v is ⟨Ax − c, v⟩. -/
theorem fderiv_quadF {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (c x v : Fin d → ℝ) :
    fderiv ℝ (quadF A c) x v = gradQ A c x ⬝ᵥ v := by
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => quadF A c (x + t • v)) (fderiv ℝ (quadF A c) x v) 0 := by
    have := (differentiable_quadF A c (x + (0 : ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hline
    rw [zero_smul, add_zero] at this
    exact this
  have h2 : HasDerivAt (fun t : ℝ => quadF A c (x + t • v)) (gradQ A c x ⬝ᵥ v) 0 := by
    have e : (fun t : ℝ => quadF A c (x + t • v)) = fun t =>
        quadF A c x + t * (gradQ A c x ⬝ᵥ v) + t ^ 2 * (1 / 2 * (v ⬝ᵥ A *ᵥ v)) := by
      funext t
      rw [quadF_add hA]
      simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul]
      ring
    rw [e]
    have := (((hasDerivAt_id (0 : ℝ)).mul_const (gradQ A c x ⬝ᵥ v)).const_add (quadF A c x)).add
      ((hasDerivAt_pow 2 (0 : ℝ)).mul_const (1 / 2 * (v ⬝ᵥ A *ᵥ v)))
    exact this.congr_deriv (by simp)
  exact h1.unique h2

lemma energy_eq_quadF(H Q : Matrix (Fin d) (Fin d) ℝ) (b h : Fin d → ℝ) (θ : ℝ)
    (x : Fin d → ℝ) : energy H Q b h θ x = quadF (H + θ • Q) (b + θ • h) x := by
  simp only [energy, quadF, quad_ray, add_dotProduct, smul_dotProduct, smul_eq_mul]
  ring

/-- First-order condition for a global minimiser of a quadratic with A ⪰ 0: Ax₀ = c. -/
lemma gradQ_eq_zero_of_isMin {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef) {c x₀ : Fin d → ℝ}
    (hmin : ∀ y, quadF A c x₀ ≤ quadF A c y) : gradQ A c x₀ = 0 := by
  set g := gradQ A c x₀
  have hdisc := discrim_le_zero (a := 1 / 2 * (g ⬝ᵥ A *ᵥ g)) (b := g ⬝ᵥ g) (c := 0)
    (fun t => by
      have h := hmin (x₀ + t • g)
      rw [quadF_add hA.1] at h
      simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h
      nlinarith)
  unfold discrim at hdisc
  have : g ⬝ᵥ g = 0 := by nlinarith
  exact dotProduct_self_eq_zero.mp this

lemma isUnit_det_of_posDef {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosDef) : IsUnit A.det :=
  isUnit_iff_ne_zero.mpr hA.det_pos.ne'

/-- **Proposition D1.4(b)** (H_D1a–H_D1d). Let H, Q ⪰ 0 with ker H ∩ ker Q = {0} (d ≥ 1),
f = ½xᵀHx − bᵀx, r = ½xᵀQx − hᵀx, E_θ = f + θr, x*₀ a (global) minimiser of f, θ > 0, and
x*_θ := (H + θQ)⁻¹(b + θh). Then:
* H + θQ is invertible, x*_θ minimises E_θ, and it is the only minimiser;
* x*_θ − x*₀ = −θ(H + θQ)⁻¹∇r(x*₀);
* θ‖∇r(x*₀)‖/β(θ) ≤ ‖x*_θ − x*₀‖ ≤ θ‖∇r(x*₀)‖/μ(θ), and the two bounds differ by the factor
  cond(θ) = β(θ)/μ(θ);
* f(x*_θ) − f(x*₀) = ½(x*_θ − x*₀)ᵀH(x*_θ − x*₀) ≥ 0. -/
theorem prop_D14b {H Q : Matrix (Fin d) (Fin d) ℝ} (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef)
    (hd : 0 < d) (hK : OCF.matKer H ⊓ OCF.matKer Q = ⊥) (b h x₀ : Fin d → ℝ)
    (hx₀ : ∀ y, quadF H b x₀ ≤ quadF H b y) {θ : ℝ} (hθ : 0 < θ) :
    let xθ := (H + θ • Q)⁻¹ *ᵥ (b + θ • h)
    IsUnit (H + θ • Q).det ∧
    (∀ y, energy H Q b h θ xθ ≤ energy H Q b h θ y) ∧
    (∀ y, (∀ z, energy H Q b h θ y ≤ energy H Q b h θ z) → y = xθ) ∧
    xθ - x₀ = -θ • ((H + θ • Q)⁻¹ *ᵥ gradQ Q h x₀) ∧
    θ * l2 (gradQ Q h x₀) / beta H Q θ ≤ l2 (xθ - x₀) ∧
    l2 (xθ - x₀) ≤ θ * l2 (gradQ Q h x₀) / phi hHpsd.1 hQpsd.1 hd θ ∧
    θ * l2 (gradQ Q h x₀) / phi hHpsd.1 hQpsd.1 hd θ =
      (beta H Q θ / phi hHpsd.1 hQpsd.1 hd θ) * (θ * l2 (gradQ Q h x₀) / beta H Q θ) ∧
    quadF H b xθ - quadF H b x₀ = 1 / 2 * ((xθ - x₀) ⬝ᵥ H *ᵥ (xθ - x₀)) ∧
    0 ≤ quadF H b xθ - quadF H b x₀ := by
  intro xθ
  set Hθ := H + θ • Q with hHθ
  have hpd : Hθ.PosDef := (posDef_ray_iff hHpsd hQpsd).mpr hK θ hθ
  have hHθ_herm : Hθ.IsHermitian := isHermitian_ray hHpsd.1 hQpsd.1 θ
  have hu : IsUnit Hθ.det := isUnit_det_of_posDef hpd
  have hμ : 0 < phi hHpsd.1 hQpsd.1 hd θ :=
    (posDef_iff_lamMin_pos hHθ_herm hd).mp hpd
  have hβμ : phi hHpsd.1 hQpsd.1 hd θ ≤ beta H Q θ := lamMin_le_lambdaMax hHθ_herm hd
  have hβ : 0 < beta H Q θ := lt_of_lt_of_le hμ hβμ
  -- stationarity of x*_θ and of x*₀
  have hstat : Hθ *ᵥ xθ = b + θ • h := by
    show Hθ *ᵥ (Hθ⁻¹ *ᵥ (b + θ • h)) = b + θ • h
    rw [mulVec_mulVec, mul_nonsing_inv _ hu, one_mulVec]
  have hgradθ : gradQ Hθ (b + θ • h) xθ = 0 := by simp [gradQ, hstat]
  have hHx₀ : H *ᵥ x₀ = b := by
    have := gradQ_eq_zero_of_isMin hHpsd hx₀
    simpa [gradQ, sub_eq_zero] using this
  -- the displacement equation H_θ Δ = −θ∇r(x*₀)
  set g := gradQ Q h x₀ with hg
  set Δ := xθ - x₀ with hΔ
  have hdisp : Hθ *ᵥ Δ = -θ • g := by
    rw [hΔ, mulVec_sub, hstat, hHθ, add_mulVec, smul_mulVec, hHx₀, hg, gradQ, smul_sub]
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hident : Δ = -θ • (Hθ⁻¹ *ᵥ g) := by
    have : Hθ⁻¹ *ᵥ (Hθ *ᵥ Δ) = Δ := by
      rw [mulVec_mulVec, nonsing_inv_mul _ hu, one_mulVec]
    rw [← this, hdisp, mulVec_smul]
  -- minimality and uniqueness through the exact expansion
  have hexp : ∀ y, energy H Q b h θ y = energy H Q b h θ xθ + 1 / 2 * ((y - xθ) ⬝ᵥ Hθ *ᵥ (y - xθ)) := by
    intro y
    rw [energy_eq_quadF, energy_eq_quadF]
    have := quadF_add hHθ_herm (b + θ • h) xθ (y - xθ)
    rw [add_sub_cancel, hgradθ, zero_dotProduct, add_zero] at this
    exact this
  have hmin : ∀ y, energy H Q b h θ xθ ≤ energy H Q b h θ y := by
    intro y
    rw [hexp y]
    have := quad_nonneg_of_psd hpd.posSemidef (y - xθ)
    linarith
  -- the bounds
  have hμΔ : phi hHpsd.1 hQpsd.1 hd θ * (Δ ⬝ᵥ Δ) ≤ Δ ⬝ᵥ Hθ *ᵥ Δ :=
    lamMin_mul_le hHθ_herm hd Δ
  have hΔg : Δ ⬝ᵥ Hθ *ᵥ Δ = -θ * (Δ ⬝ᵥ g) := by
    rw [hdisp, dotProduct_smul, smul_eq_mul]
  have hcs := abs_dot_le Δ g
  have hlow := mulVec_dot_le_lambdaMax_sq hpd.posSemidef Δ
  rw [hdisp] at hlow
  simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul] at hlow
  have hl2Δ := l2_sq Δ
  have hl2g := l2_sq g
  have hΔ0 := l2_nonneg Δ
  have hg0 := l2_nonneg g
  refine ⟨hu, hmin, fun y hy => ?_, hident, ?_, ?_, ?_, ?_, ?_⟩
  · -- uniqueness
    have h1 := hy xθ
    rw [hexp y] at h1
    have h2 : (y - xθ) ⬝ᵥ Hθ *ᵥ (y - xθ) ≤ 0 := by linarith
    by_contra hne
    have := hpd.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)
    rw [star_trivial] at this
    linarith
  · -- lower bound: θ‖g‖ = ‖H_θΔ‖ ≤ β‖Δ‖
    rw [div_le_iff₀ hβ]
    have hsq : (θ * l2 g) ^ 2 ≤ (l2 Δ * beta H Q θ) ^ 2 := by
      have e0 : OCF.lambdaMax Hθ = beta H Q θ := rfl
      rw [e0] at hlow
      have e1 : (θ * l2 g) ^ 2 = θ ^ 2 * (g ⬝ᵥ g) := by rw [mul_pow, hl2g]
      have e2 : (l2 Δ * beta H Q θ) ^ 2 = beta H Q θ ^ 2 * (Δ ⬝ᵥ Δ) := by rw [mul_pow, hl2Δ]; ring
      have e3 : -θ * (-θ * (g ⬝ᵥ g)) = θ ^ 2 * (g ⬝ᵥ g) := by ring
      rw [e1, e2]; linarith
    exact (sq_le_sq₀ (by positivity) (by positivity)).mp hsq
  · -- upper bound: μ‖Δ‖² ≤ ΔᵀH_θΔ = −θΔᵀg ≤ θ‖Δ‖‖g‖
    rw [le_div_iff₀ hμ]
    have hkey : phi hHpsd.1 hQpsd.1 hd θ * (l2 Δ * l2 Δ) ≤ θ * l2 g * l2 Δ := by
      have : -θ * (Δ ⬝ᵥ g) ≤ θ * (l2 Δ * l2 g) := by
        have := neg_abs_le (Δ ⬝ᵥ g)
        nlinarith
      nlinarith
    rcases hΔ0.lt_or_eq with hpos | hz
    · nlinarith
    · rw [← hz]; simp only [zero_mul]; positivity
  · field_simp
  · -- data-fit identity
    have := quadF_add hHpsd.1 b x₀ Δ
    rw [hΔ, add_sub_cancel] at this
    have hg0' : gradQ H b x₀ = 0 := by simp [gradQ, hHx₀]
    rw [this, hg0', zero_dotProduct]
    ring
  · have := quadF_add hHpsd.1 b x₀ Δ
    rw [hΔ, add_sub_cancel] at this
    have hg0' : gradQ H b x₀ = 0 := by simp [gradQ, hHx₀]
    rw [this, hg0', zero_dotProduct]
    have := quad_nonneg_of_psd hHpsd (xθ - x₀)
    linarith

end Bias

/-! ## Proposition D1.5(a) — the declared affine ratio is monotone -/

section Declared

/-- σ̂(θ)/β̂(θ) = (σ_f + θσ_r)/(β_f + θβ_r). -/
noncomputable def declRatio (σf σr βf βr θ : ℝ) : ℝ := (σf + θ * σr) / (βf + θ * βr)

/-- The certified factor 1 − σ̂(θ)/β̂(θ). -/
noncomputable def declFactor (σf σr βf βr θ : ℝ) : ℝ := 1 - declRatio σf σr βf βr θ

variable {σf σr βf βr : ℝ}

/-- **Proposition D1.5(a)**, the identity: for 0 < θ < θ′ (β_f, β_r > 0),
σ̂(θ′)/β̂(θ′) − σ̂(θ)/β̂(θ) = (θ′ − θ)(σ_rβ_f − σ_fβ_r)/(β̂(θ)β̂(θ′)). -/
theorem prop_D15a_identity (hβf : 0 < βf) (hβr : 0 < βr) {θ θ' : ℝ} (hθ : 0 < θ)
    (_hθθ' : θ < θ') :
    declRatio σf σr βf βr θ' - declRatio σf σr βf βr θ =
      (θ' - θ) * (σr * βf - σf * βr) / ((βf + θ * βr) * (βf + θ' * βr)) := by
  have h1 : 0 < βf + θ * βr := by positivity
  have h2 : 0 < βf + θ' * βr := by nlinarith
  unfold declRatio
  field_simp
  ring

lemma declRatio_sub (hβf : 0 < βf) (hβr : 0 < βr) {θ θ' : ℝ} (hθ : 0 < θ) (hθθ' : θ < θ') :
    0 < (βf + θ * βr) * (βf + θ' * βr) ∧
    declRatio σf σr βf βr θ' - declRatio σf σr βf βr θ =
      (θ' - θ) * (σr * βf - σf * βr) / ((βf + θ * βr) * (βf + θ' * βr)) :=
  ⟨by have : 0 < βf + θ * βr := by positivity
      have : 0 < βf + θ' * βr := by nlinarith
      positivity, prop_D15a_identity hβf hβr hθ hθθ'⟩

/-- **Proposition D1.5(a)**, monotonicity. The certified factor 1 − σ̂/β̂ is non-increasing on
(0, ∞) if σ_r/β_r ≥ σ_f/β_f, and non-decreasing on (0, ∞) otherwise; strictly so unless
σ_r/β_r = σ_f/β_f, in which case it is constant. -/
theorem prop_D15a_monotone (hβf : 0 < βf) (hβr : 0 < βr) :
    (σf / βf ≤ σr / βr → AntitoneOn (declFactor σf σr βf βr) (Set.Ioi 0)) ∧
    (σr / βr < σf / βf → MonotoneOn (declFactor σf σr βf βr) (Set.Ioi 0)) ∧
    (σf / βf < σr / βr → StrictAntiOn (declFactor σf σr βf βr) (Set.Ioi 0)) ∧
    (σr / βr < σf / βf → StrictMonoOn (declFactor σf σr βf βr) (Set.Ioi 0)) ∧
    (σr / βr = σf / βf → ∀ θ ∈ Set.Ioi (0 : ℝ), ∀ θ' ∈ Set.Ioi (0 : ℝ),
      declFactor σf σr βf βr θ = declFactor σf σr βf βr θ') := by
  have key : ∀ θ θ' : ℝ, 0 < θ → θ < θ' →
      declFactor σf σr βf βr θ - declFactor σf σr βf βr θ' =
        (θ' - θ) * (σr * βf - σf * βr) / ((βf + θ * βr) * (βf + θ' * βr)) := by
    intro θ θ' hθ hθθ'
    have := prop_D15a_identity (σf := σf) (σr := σr) hβf hβr hθ hθθ'
    unfold declFactor; linarith
  have hden : ∀ θ θ' : ℝ, 0 < θ → θ < θ' → 0 < (βf + θ * βr) * (βf + θ' * βr) :=
    fun θ θ' hθ hθθ' => (declRatio_sub (σf := σf) (σr := σr) hβf hβr hθ hθθ').1
  have hcross : (σf / βf ≤ σr / βr ↔ σf * βr ≤ σr * βf) := by
    rw [div_le_div_iff₀ hβf hβr]
  have hcross' : (σr / βr < σf / βf ↔ σr * βf < σf * βr) := by
    rw [div_lt_div_iff₀ hβr hβf]
  have hcross'' : (σf / βf < σr / βr ↔ σf * βr < σr * βf) := by
    rw [div_lt_div_iff₀ hβf hβr]
  -- sign of the difference factor(θ) − factor(θ') for θ < θ'
  have sgn : ∀ θ θ' : ℝ, 0 < θ → θ < θ' →
      (0 ≤ σr * βf - σf * βr → declFactor σf σr βf βr θ' ≤ declFactor σf σr βf βr θ) ∧
      (0 < σr * βf - σf * βr → declFactor σf σr βf βr θ' < declFactor σf σr βf βr θ) ∧
      (σr * βf - σf * βr < 0 → declFactor σf σr βf βr θ < declFactor σf σr βf βr θ') ∧
      (σr * βf - σf * βr = 0 → declFactor σf σr βf βr θ = declFactor σf σr βf βr θ') := by
    intro θ θ' hθ hθθ'
    have hk := key θ θ' hθ hθθ'
    have hd := hden θ θ' hθ hθθ'
    have hpos : 0 < θ' - θ := by linarith
    refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
    · have : 0 ≤ (θ' - θ) * (σr * βf - σf * βr) / ((βf + θ * βr) * (βf + θ' * βr)) := by
        positivity
      linarith
    · have : 0 < (θ' - θ) * (σr * βf - σf * βr) / ((βf + θ * βr) * (βf + θ' * βr)) := by
        positivity
      linarith
    · have : (θ' - θ) * (σr * βf - σf * βr) / ((βf + θ * βr) * (βf + θ' * βr)) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hpos h) hd
      linarith
    · rw [h, mul_zero, zero_div] at hk; linarith
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · intro θ hθ θ' hθ' hle
    rcases hle.lt_or_eq with hlt | heq
    · exact (sgn θ θ' hθ hlt).1 (by linarith [hcross.mp h])
    · rw [heq]
  · intro θ hθ θ' hθ' hle
    rcases hle.lt_or_eq with hlt | heq
    · exact ((sgn θ θ' hθ hlt).2.2.1 (by linarith [hcross'.mp h])).le
    · rw [heq]
  · intro θ hθ θ' _ hlt
    exact (sgn θ θ' hθ hlt).2.1 (by linarith [hcross''.mp h])
  · intro θ hθ θ' _ hlt
    exact (sgn θ θ' hθ hlt).2.2.1 (by linarith [hcross'.mp h])
  · have h0 : σr * βf - σf * βr = 0 := by
      rw [div_eq_div_iff hβr.ne' hβf.ne'] at h; linarith
    intro θ hθ θ' hθ'
    rcases lt_trichotomy θ θ' with hlt | heq | hgt
    · exact (sgn θ θ' hθ hlt).2.2.2 h0
    · rw [heq]
    · exact ((sgn θ' θ hθ' hgt).2.2.2 h0).symm

/-- **Proposition D1.5(a)**: no interior optimum unless constant. If the certified factor has a
minimiser or a maximiser over (0, ∞) at some θ₀ > 0, it is constant on (0, ∞). -/
theorem prop_D15a_no_interior_optimum (hβf : 0 < βf) (hβr : 0 < βr) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    (hopt : IsMinOn (declFactor σf σr βf βr) (Set.Ioi 0) θ₀ ∨
      IsMaxOn (declFactor σf σr βf βr) (Set.Ioi 0) θ₀) :
    ∀ θ ∈ Set.Ioi (0 : ℝ), ∀ θ' ∈ Set.Ioi (0 : ℝ),
      declFactor σf σr βf βr θ = declFactor σf σr βf βr θ' := by
  obtain ⟨-, -, hSA, hSM, hC⟩ := prop_D15a_monotone (σf := σf) (σr := σr) hβf hβr
  have h2 : (2 * θ₀) ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith
  have hlt : θ₀ < 2 * θ₀ := by linarith
  rcases lt_trichotomy (σr / βr) (σf / βf) with h | h | h
  · exfalso
    have hsm := hSM h
    rcases hopt with hmin | hmax
    · -- strictly increasing: θ₀/2 is strictly smaller
      have hh : θ₀ / 2 ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith
      have := hsm hh (Set.mem_Ioi.mpr hθ₀) (by linarith)
      have := hmin hh
      simp only [Set.mem_setOf_eq] at this
      linarith
    · have := hsm (Set.mem_Ioi.mpr hθ₀) h2 hlt
      have := hmax h2
      simp only [Set.mem_setOf_eq] at this
      linarith
  · exact hC h
  · exfalso
    have hsa := hSA h
    rcases hopt with hmin | hmax
    · have := hsa (Set.mem_Ioi.mpr hθ₀) h2 hlt
      have := hmin h2
      simp only [Set.mem_setOf_eq] at this
      linarith
    · have hh : θ₀ / 2 ∈ Set.Ioi (0 : ℝ) := by simp only [Set.mem_Ioi]; linarith
      have := hsa hh (Set.mem_Ioi.mpr hθ₀) (by linarith)
      have := hmax hh
      simp only [Set.mem_setOf_eq] at this
      linarith

/-- **Proposition D1.5(a)**, the kernel case of the declaration (σ_r = 0, σ_f ≥ 0): the certified
factor is non-decreasing on (0, ∞); if also σ_f = 0 it is ≡ 1 (void). -/
theorem prop_D15a_kernel (hβf : 0 < βf) (hβr : 0 < βr) (hσf : 0 ≤ σf) :
    MonotoneOn (declFactor σf 0 βf βr) (Set.Ioi 0) ∧
    ∀ θ, declFactor 0 0 βf βr θ = 1 := by
  refine ⟨?_, fun θ => by simp [declFactor, declRatio]⟩
  rcases hσf.lt_or_eq with hpos | hzero
  · exact (prop_D15a_monotone (σf := σf) (σr := 0) hβf hβr).2.1
      (by rw [zero_div]; exact div_pos hpos hβf)
  · subst hzero
    intro θ _ θ' _ _
    simp [declFactor, declRatio]

end Declared

/-! ## The condition number along the weight: definitions, continuity, quasiconvexity
(Theorem D1.2(a), the quasiconvexity and continuity clauses) -/

section Cond

variable {d : ℕ} {H Q : Matrix (Fin d) (Fin d) ℝ}

/-- Θ := [0, ∞) if H ≻ 0, and Θ := (0, ∞) otherwise. -/
noncomputable def Theta (H : Matrix (Fin d) (Fin d) ℝ) : Set ℝ := by
  classical exact if H.PosDef then Set.Ici 0 else Set.Ioi 0

/-- cond(θ) := β(θ)/μ(θ) (used on Θ). -/
noncomputable def cond (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) (θ : ℝ) : ℝ :=
  beta H Q θ / phi hH hQ hd θ

/-- The set of minimisers of cond on Θ. -/
def minSet (S : Set ℝ) (f : ℝ → ℝ) : Set ℝ := {θ ∈ S | ∀ θ' ∈ S, f θ ≤ f θ'}

lemma Theta_of_posDef (hpd : H.PosDef) : Theta H = Set.Ici 0 := by
  simp [Theta, hpd]

lemma Theta_of_not_posDef (hpd : ¬ H.PosDef) : Theta H = Set.Ioi 0 := by
  simp [Theta, hpd]

lemma Theta_subset_Ici : Theta H ⊆ Set.Ici 0 := by
  by_cases hpd : H.PosDef
  · rw [Theta_of_posDef hpd]
  · rw [Theta_of_not_posDef hpd]; exact Set.Ioi_subset_Ici_self

lemma convex_Theta : Convex ℝ (Theta H) := by
  by_cases hpd : H.PosDef
  · rw [Theta_of_posDef hpd]; exact convex_Ici 0
  · rw [Theta_of_not_posDef hpd]; exact convex_Ioi 0

/-- μ > 0 on Θ (Lemma D1.1(a); this is what makes cond well defined on Θ). -/
theorem phi_pos_on_Theta (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) (hd : 0 < d)
    (hK : OCF.matKer H ⊓ OCF.matKer Q = ⊥) {θ : ℝ} (hθ : θ ∈ Theta H) :
    0 < phi hHpsd.1 hQpsd.1 hd θ := by
  by_cases hpd : H.PosDef
  · rw [Theta_of_posDef hpd] at hθ
    rcases (Set.mem_Ici.mp hθ).lt_or_eq with hpos | hzero
    · exact ((lemma_D11_a hHpsd hQpsd hd).1 hK θ hpos).2
    · subst hzero
      rw [phi_zero]
      exact (posDef_iff_lamMin_pos hHpsd.1 hd).mp hpd
  · rw [Theta_of_not_posDef hpd] at hθ
    exact ((lemma_D11_a hHpsd hQpsd hd).1 hK θ hθ).2

/-- cond ≥ 1 on Θ. -/
theorem one_le_cond (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) (hd : 0 < d)
    (hK : OCF.matKer H ⊓ OCF.matKer Q = ⊥) {θ : ℝ} (hθ : θ ∈ Theta H) :
    1 ≤ cond hHpsd.1 hQpsd.1 hd θ := by
  have hμ := phi_pos_on_Theta hHpsd hQpsd hd hK hθ
  rw [cond, le_div_iff₀ hμ, one_mul]
  exact lamMin_le_lambdaMax (isHermitian_ray hHpsd.1 hQpsd.1 θ) hd

/-- **Theorem D1.2(a)**, continuity: cond is continuous on Θ. -/
theorem cond_continuousOn (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) (hd : 0 < d)
    (hK : OCF.matKer H ⊓ OCF.matKer Q = ⊥) :
    ContinuousOn (cond hHpsd.1 hQpsd.1 hd) (Theta H) :=
  (beta_continuous hHpsd.1 hQpsd.1 hd).continuousOn.div
    (phi_continuous hHpsd.1 hQpsd.1 hd).continuousOn
    fun _ hθ => (phi_pos_on_Theta hHpsd hQpsd hd hK hθ).ne'

/-- **Theorem D1.2(a)**, quasiconvexity: under H_D1a–H_D1b, cond is quasiconvex on Θ (β convex,
μ concave and positive on the interval Θ: Boyd–Vandenberghe Ex. 3.38). -/
theorem cond_quasiconvexOn (hHpsd : H.PosSemidef) (hQpsd : Q.PosSemidef) (hd : 0 < d)
    (hK : OCF.matKer H ⊓ OCF.matKer Q = ⊥) :
    QuasiconvexOn ℝ (Theta H) (cond hHpsd.1 hQpsd.1 hd) := by
  intro r
  set μ := phi hHpsd.1 hQpsd.1 hd
  set β := beta H Q
  have hset : {θ ∈ Theta H | cond hHpsd.1 hQpsd.1 hd θ ≤ r} =
      {θ ∈ Theta H | β θ - r * μ θ ≤ 0} := by
    ext θ
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hθ, h⟩
      refine ⟨hθ, ?_⟩
      have hμ := phi_pos_on_Theta hHpsd hQpsd hd hK hθ
      rw [cond, div_le_iff₀ hμ] at h
      linarith
    · rintro ⟨hθ, h⟩
      refine ⟨hθ, ?_⟩
      have hμ := phi_pos_on_Theta hHpsd hQpsd hd hK hθ
      rw [cond, div_le_iff₀ hμ]
      linarith
  rw [hset]
  rcases le_or_gt 0 r with hr | hr
  · have hβc : ConvexOn ℝ (Theta H) β :=
      (beta_convexOn_univ hHpsd.1 hQpsd.1 hd).subset (Set.subset_univ _) convex_Theta
    have hμc : ConcaveOn ℝ (Theta H) μ :=
      (phi_concaveOn_univ hHpsd.1 hQpsd.1 hd).subset (Set.subset_univ _) convex_Theta
    have hconv : ConvexOn ℝ (Theta H) (fun θ => β θ - r * μ θ) := by
      have := hβc.add ((hμc.smul hr).neg)
      refine this.congr fun θ _ => ?_
      simp [sub_eq_add_neg, smul_eq_mul]
    exact hconv.convex_le 0
  · convert convex_empty (𝕜 := ℝ) (E := ℝ)
    ext θ
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
    intro hθ
    have hμ := phi_pos_on_Theta hHpsd hQpsd hd hK hθ
    have hβμ : μ θ ≤ β θ := lamMin_le_lambdaMax (isHermitian_ray hHpsd.1 hQpsd.1 θ) hd
    nlinarith

end Cond

/-! ## Example ex:cond-weight(i) — the witness family H = diag(1, s, t), Q = diag(1, 0, 0) -/

section Witness

/-- λ_min of a diagonal matrix is its smallest diagonal entry. -/
lemma lamMin_diagonal {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) {m : ℝ} (hm : ∀ i, m ≤ a i)
    (hj : ∃ j, a j = m) :
    lamMin (isHermitian_diagonal a) hn = m := by
  obtain ⟨j, hj⟩ := hj
  apply le_antisymm
  · have h := lamMin_le_quad hn (isHermitian_diagonal a) (x := Pi.single j 1)
      (by simp [dotProduct_single])
    simpa [hj, mulVec_single, dotProduct_single] using h
  · obtain ⟨x, hx, hxA⟩ := exists_unit_lamMin (isHermitian_diagonal a) hn
    rw [← hxA]
    have e : x ⬝ᵥ diagonal a *ᵥ x = ∑ i, a i * (x i * x i) := by
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e1 : ∑ i, x i * x i = 1 := by rw [← hx]; rfl
    rw [e]
    calc m = ∑ i, m * (x i * x i) := by rw [← Finset.mul_sum, e1, mul_one]
      _ ≤ ∑ i, a i * (x i * x i) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hm i) (mul_self_nonneg _)

/-- λ_max of a diagonal matrix is its largest diagonal entry. -/
lemma lambdaMax_diagonal {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ) {M : ℝ} (hM : ∀ i, a i ≤ M)
    (hj : ∃ j, a j = M) :
    OCF.lambdaMax (diagonal a) = M := by
  obtain ⟨j, hj⟩ := hj
  apply le_antisymm
  · obtain ⟨x, hx, hxA⟩ := exists_unit_lambdaMax (isHermitian_diagonal a) hn
    rw [← hxA]
    have e : x ⬝ᵥ diagonal a *ᵥ x = ∑ i, a i * (x i * x i) := by
      simp only [dotProduct, mulVec_diagonal]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e1 : ∑ i, x i * x i = 1 := by rw [← hx]; rfl
    rw [e]
    calc ∑ i, a i * (x i * x i) ≤ ∑ i, M * (x i * x i) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hM i) (mul_self_nonneg _)
      _ = M := by rw [← Finset.mul_sum, e1, mul_one]
  · have h := OCF.dotProduct_mulVec_le_lambdaMax (isHermitian_diagonal a) (Pi.single j 1)
    simpa [hj, mulVec_single, dotProduct_single] using h

/-- H = diag(1, s, t). -/
noncomputable def Hw (s t : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, s, t]

/-- Q = diag(1, 0, 0). -/
noncomputable def Qw : Matrix (Fin 3) (Fin 3) ℝ := diagonal ![1, 0, 0]

lemma Hw_herm (s t : ℝ) : (Hw s t).IsHermitian := isHermitian_diagonal _
lemma Qw_herm : Qw.IsHermitian := isHermitian_diagonal _

lemma ray_w (s t θ : ℝ) : Hw s t + θ • Qw = diagonal ![1 + θ, s, t] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Hw, Qw, diagonal]

/-- The hypotheses of the kernel case with H ≻ 0, for 1 ≤ s ≤ t. -/
theorem witness_hyps {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    (Hw s t).PosSemidef ∧ Qw.PosSemidef ∧ Qw ≠ 0 ∧ (Hw s t).PosDef ∧
    OCF.matKer (Hw s t) ⊓ OCF.matKer Qw = ⊥ ∧ OCF.matKer Qw ≠ ⊥ := by
  have hpd : (Hw s t).PosDef := by
    rw [Hw, Matrix.posDef_diagonal_iff]
    intro i; fin_cases i <;> simp <;> linarith
  have hQ : Qw.PosSemidef := by
    rw [Qw, Matrix.posSemidef_diagonal_iff]
    intro i; fin_cases i <;> simp
  have hHpsd := hpd.posSemidef
  refine ⟨hHpsd, hQ, ?_, hpd, ?_, ?_⟩
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [Qw] at this
  · rw [(posDef_iff_ker_eq_bot hHpsd).mp hpd, bot_inf_eq]
  · intro h
    have hmem : (Pi.single 1 1 : Fin 3 → ℝ) ∈ OCF.matKer Qw := by
      show Qw *ᵥ Pi.single 1 1 = 0
      ext i; fin_cases i <;> simp [Qw, mulVec_single]
    rw [h, Submodule.mem_bot] at hmem
    have := congrFun hmem 1
    simp at this

/-- cond(θ) = max{1 + θ, t}/min{1 + θ, s} for θ ≥ 0, 1 ≤ s ≤ t. -/
theorem witness_cond {s t : ℝ} (_hs : 1 ≤ s) (hst : s ≤ t) {θ : ℝ} (_hθ : 0 ≤ θ) :
    cond (Hw_herm s t) Qw_herm (by norm_num) θ = max (1 + θ) t / min (1 + θ) s := by
  rw [cond, beta, phi, lamMin_congr (ray_w s t θ) _ (isHermitian_diagonal _), ray_w,
    lambdaMax_diagonal (by norm_num) _ (M := max (1 + θ) t), lamMin_diagonal (by norm_num) _
      (m := min (1 + θ) s)]
  · intro i; fin_cases i <;> simp
    right; linarith
  · rcases le_total (1 + θ) s with h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
  · intro i; fin_cases i <;> simp
    right; linarith
  · rcases le_total (1 + θ) t with h | h
    · exact ⟨2, by simp [h]⟩
    · exact ⟨0, by simp [h]⟩

/-- **Example ex:cond-weight(i)**: for H = diag(1, s, t), Q = diag(1, 0, 0), 1 ≤ s ≤ t, we have
Θ = [0, ∞), and the set of minimisers of cond on Θ is [s − 1, t − 1] (minimum value t/s). -/
theorem witness_minSet {s t : ℝ} (hs : 1 ≤ s) (hst : s ≤ t) :
    Theta (Hw s t) = Set.Ici 0 ∧
    minSet (Theta (Hw s t)) (cond (Hw_herm s t) Qw_herm (by norm_num)) = Set.Icc (s - 1) (t - 1) ∧
    ∀ θ ∈ Set.Icc (s - 1) (t - 1), cond (Hw_herm s t) Qw_herm (by norm_num) θ = t / s := by
  have hTh : Theta (Hw s t) = Set.Ici 0 := Theta_of_posDef (witness_hyps hs hst).2.2.2.1
  have hs0 : 0 < s := by linarith
  -- the closed form and its lower bound
  have hval : ∀ θ, 0 ≤ θ → t / s ≤ cond (Hw_herm s t) Qw_herm (by norm_num) θ ∧
      (cond (Hw_herm s t) Qw_herm (by norm_num) θ = t / s ↔ θ ∈ Set.Icc (s - 1) (t - 1)) := by
    intro θ hθ
    rw [witness_cond hs hst hθ, Set.mem_Icc]
    rcases le_total (1 + θ) s with h1 | h1
    · have hu : 0 < 1 + θ := by linarith
      rw [max_eq_right (by linarith), min_eq_left h1]
      refine ⟨div_le_div_of_nonneg_left (by linarith) hu h1, ?_⟩
      rw [div_eq_div_iff hu.ne' hs0.ne']
      constructor
      · intro h
        have : 1 + θ = s := by nlinarith
        constructor <;> linarith
      · rintro ⟨h2, -⟩
        have : 1 + θ = s := by linarith
        rw [this]
    · rw [min_eq_right h1]
      rcases le_total (1 + θ) t with h2 | h2
      · rw [max_eq_right h2]
        exact ⟨le_rfl, ⟨fun _ => ⟨by linarith, by linarith⟩, fun _ => rfl⟩⟩
      · rw [max_eq_left h2]
        refine ⟨div_le_div_of_nonneg_right h2 hs0.le, ?_⟩
        rw [div_left_inj' hs0.ne']
        constructor
        · intro h; constructor <;> linarith
        · rintro ⟨-, h3⟩; linarith
  refine ⟨hTh, ?_, fun θ hθ => ((hval θ (by linarith [hθ.1])).2).mpr hθ⟩
  rw [hTh]
  ext θ
  simp only [minSet, Set.mem_setOf_eq, Set.mem_Ici]
  constructor
  · rintro ⟨hθ, hmin⟩
    refine ((hval θ hθ).2).mp (le_antisymm ?_ (hval θ hθ).1)
    have hm := hmin (s - 1) (by linarith)
    have := ((hval (s - 1) (by linarith)).2).mpr ⟨le_rfl, by linarith⟩
    linarith
  · intro hθ
    have hθ0 : 0 ≤ θ := by linarith [hθ.1]
    refine ⟨hθ0, fun θ' hθ' => ?_⟩
    rw [((hval θ hθ0).2).mpr hθ]
    exact (hval θ' hθ').1

/-- Every shape: for every 0 ≤ a ≤ b, the witness with (s, t) = (a + 1, b + 1) has minimiser set
exactly [a, b]. In particular {0}, [0, 1], {1} and [1, 2] arise from (s, t) = (1, 1), (1, 2),
(2, 2), (2, 3); both alternatives of Theorem D1.2(c) for H ≻ 0 ("[0, a]" and "⊂ (0, ∞)") occur
both as a single point and as a non-degenerate interval. -/
theorem witness_every_shape {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    minSet (Theta (Hw (a + 1) (b + 1))) (cond (Hw_herm (a + 1) (b + 1)) Qw_herm (by norm_num)) =
      Set.Icc a b := by
  have := (witness_minSet (s := a + 1) (t := b + 1) (by linarith) (by linarith)).2.1
  simpa using this

theorem witness_four_shapes :
    minSet (Theta (Hw 1 1)) (cond (Hw_herm 1 1) Qw_herm (by norm_num)) = {0} ∧
    minSet (Theta (Hw 1 2)) (cond (Hw_herm 1 2) Qw_herm (by norm_num)) = Set.Icc 0 1 ∧
    minSet (Theta (Hw 2 2)) (cond (Hw_herm 2 2) Qw_herm (by norm_num)) = {1} ∧
    minSet (Theta (Hw 2 3)) (cond (Hw_herm 2 3) Qw_herm (by norm_num)) = Set.Icc 1 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [(witness_minSet (le_refl _) (le_refl _)).2.1]; norm_num
  · rw [(witness_minSet (le_refl _) (by norm_num)).2.1]; norm_num
  · rw [(witness_minSet (by norm_num) (le_refl _)).2.1]; norm_num
  · rw [(witness_minSet (by norm_num) (by norm_num)).2.1]; norm_num

end Witness

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only) -/

#print axioms posDef_ray_iff
#print axioms lemma_D11_a
#print axioms lemma_D11_b
#print axioms lemma_D11_c
#print axioms prop_D14b
#print axioms fderiv_quadF
#print axioms prop_D15a_identity
#print axioms prop_D15a_monotone
#print axioms prop_D15a_no_interior_optimum
#print axioms prop_D15a_kernel
#print axioms phi_pos_on_Theta
#print axioms one_le_cond
#print axioms cond_continuousOn
#print axioms cond_quasiconvexOn
#print axioms witness_hyps
#print axioms witness_cond
#print axioms witness_minSet
#print axioms witness_every_shape
#print axioms witness_four_shapes
#print axioms l2_eq_norm_toLp

end OCF.D1

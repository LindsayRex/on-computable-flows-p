/-
A56 (Proximal maps and spectral bookkeeping in frame coordinates) — the
linear-algebra parts named tractable in the adjudication (Decision 4).

Source of truth: project_plan/done/proof_audits/A56_prox_frame_bookkeeping/01_derivation.md
(adjudicated 2026-10-09; cleared for stage 3½ under the author's overnight
delegation, 03_adjudication.md "Formalisation tier call").

DEFINITIONAL MAP:
* HF — hypotheses `hc : 0 < c`, `hW : Wᵀ * W = c • 1` on `W : Matrix (Fin n) (Fin d) ℝ`
  (analysis operator of a tight frame, frame constant c). ℝᵏ is `Fin k → ℝ`.
* W⁺ := c⁻¹Wᵀ — `pushDown W c`.
* C := WHW⁺ — `conjOp W c H`; the lifted Hessian WHWᵀ — `OCF.B6.conj W H`.
* η (signed-diagonal convention, B6 adjudication Decision 1; A56 adjudication
  finding A-1) — reused verbatim from B6: `OCF.B6.domRatio`, test
  `OCF.B6.PassesDominance`. "η defined" = positive diagonal (HD).
* spec with algebraic multiplicity — the characteristic polynomial
  (Mathlib `Matrix.charpoly`, det(X·I − M)) and its root multiset.
* ‖·‖ on matrices — the ℓ²-operator norm (`Matrix.Norms.L2Operator`).
* A function on ℝⁿ with values in (−∞, +∞] — any codomain `β`
  (the statement is proved for an arbitrary codomain; `WithTop ℝ` is the
  dossier's case, `lift_characterisation_WithTop`).

COVERAGE:
* A56.2 matrix identities — `transpose_eq_smul_pushDown` (Wᵀ = cW⁺),
  `pushDown_transpose` ((W⁺)ᵀ = c⁻¹W), `pushDown_mul_self` (W⁺W = I),
  `transpose_mulVec_dual` (Wᵀ(c⁻¹Wx) = x, step 2.5),
  `projRan_symm_idem` (P_{ran W} = WW⁺ symmetric idempotent),
  `norm_scaled_frame` (‖c^{-1/2}W‖ = 1, for d ≥ 1), `norm_frame` (‖W‖ = √c).
* A56.5(a) — `lift_characterisation` (iff + uniqueness + g = φ∘(c⁻¹W)).
* A56.6(a) — `A56_6a` (symmetry, CW = WH, ran W invariant, the restriction
  C|_{ran W} conjugate to H via W : ℝᵈ ≃ ran W, vanishing on ker Wᵀ,
  ker Wᵀ = (ran W)^⊥, d ≤ n, charpoly C = X^{n−d}·charpoly H) and
  `A56_6a_roots` (root multiset = spec H ⊎ {0}^{n−d}).
* A56.6(b) — `A56_6b` (WHWᵀ = c·C, (WHWᵀ)W = W(cH),
  charpoly = X^{n−d}·charpoly(cH)).
* A56.6(d) — `A56_6d_scale` (η(ρA) = η(A), ρ > 0, with positivity of the
  diagonal and the test preserved), `A56_6d_frame` (η(WHWᵀ) = η(WHW⁺), same
  definedness condition wᵢᵀHwᵢ > 0), `A56_6d_failure` (the witness
  W = [I₂; 0], H = diag(1, 2): η undefined).
* A56.6(f) — `A56_6f` (n > d, positive diagonal ⇒ η(WHW⁺) ≥ 1, test fails)
  and `A56_6f_attained` (W = (1, 1)ᵀ, c = 2, H = (1): η = 1).
* Bonus, A56.6(e) — `A56_6e` (η(H) = 0, η(WHW⁺) = 1/3; the integer frame
  W = √2·R(π/4) with c = 2 gives the same matrix WHW⁺ as the c = 1 rotation).

PROSE-ONLY (no prox / Moreau theory in Mathlib): A56.1, every prox row of
A56.2, A56.3, A56.4, A56.5(b)–(d). Not targeted: A56.6(c) (Hessian
conversion, calculus).

Status tier: FORMALISED (partial: the linear-algebra parts listed above;
statement + proof, no sorry). Prox parts PROSE-ONLY.
-/
import Mathlib
import OcfVerification.B6Witnesses

open Matrix BigOperators Polynomial

namespace OCF.A56

open OCF.B6

variable {n d : ℕ}

/-- The ruled push-down W⁺ := c⁻¹Wᵀ. -/
noncomputable def pushDown (W : Matrix (Fin n) (Fin d) ℝ) (c : ℝ) : Matrix (Fin d) (Fin n) ℝ :=
  c⁻¹ • Wᵀ

/-- The conjugate operator C := W H W⁺. -/
noncomputable def conjOp (W : Matrix (Fin n) (Fin d) ℝ) (c : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  W * H * pushDown W c

/-! ### A56.2: the matrix identities -/

/-- Wᵀ = c·W⁺. -/
theorem transpose_eq_smul_pushDown (W : Matrix (Fin n) (Fin d) ℝ) {c : ℝ} (hc : c ≠ 0) :
    Wᵀ = c • pushDown W c := by
  rw [pushDown, smul_smul, mul_inv_cancel₀ hc, one_smul]

/-- (W⁺)ᵀ = c⁻¹W (the dual analysis operator of repair 2). -/
theorem pushDown_transpose (W : Matrix (Fin n) (Fin d) ℝ) (c : ℝ) :
    (pushDown W c)ᵀ = c⁻¹ • W := by
  rw [pushDown, transpose_smul, transpose_transpose]

/-- W⁺W = I_d. -/
theorem pushDown_mul_self {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : pushDown W c * W = 1 := by
  rw [pushDown, Matrix.smul_mul, hW, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- Step 2.5: Wᵀ(c⁻¹Wx) = x. -/
theorem transpose_mulVec_dual {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (x : Fin d → ℝ) :
    Wᵀ *ᵥ (c⁻¹ • (W *ᵥ x)) = x := by
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hW, Matrix.smul_mulVec,
    Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]

/-- P_{ran W} := WW⁺ is symmetric and idempotent. -/
theorem projRan_symm_idem {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    (W * pushDown W c)ᵀ = W * pushDown W c ∧
      (W * pushDown W c) * (W * pushDown W c) = W * pushDown W c := by
  refine ⟨?_, ?_⟩
  · rw [pushDown, transpose_mul, transpose_smul, transpose_transpose, Matrix.mul_smul, Matrix.smul_mul]
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc W, pushDown_mul_self hc hW, Matrix.mul_one]

section Norm
open scoped Matrix.Norms.L2Operator

/-- WᵀW = cI ⇒ ‖c^{-1/2}W‖ = 1 (ℓ²-operator norm), for d ≥ 1. -/
theorem norm_scaled_frame [NeZero d] {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    ‖(Real.sqrt c)⁻¹ • W‖ = 1 := by
  set L := (Real.sqrt c)⁻¹ • W
  have hLL : Lᴴ * L = 1 := by
    rw [conjTranspose_eq_transpose_of_trivial]
    simp only [L, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hW, smul_smul]
    rw [show (Real.sqrt c)⁻¹ * ((Real.sqrt c)⁻¹ * c) = 1 by
      rw [← mul_assoc, ← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne'], one_smul]
  have h1 : ‖(1 : Matrix (Fin d) (Fin d) ℝ)‖ = 1 := by
    rw [← diagonal_one, l2_opNorm_diagonal]
    exact norm_one
  have h := l2_opNorm_conjTranspose_mul_self L
  rw [hLL, h1] at h
  have h0 : 0 ≤ ‖L‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖L‖ - 1), sq_nonneg (‖L‖ + 1)]

/-- ‖W‖ = √c (ℓ²-operator norm), for d ≥ 1. -/
theorem norm_frame [NeZero d] {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    ‖W‖ = Real.sqrt c := by
  have h := norm_scaled_frame hc hW
  rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr hc)] at h
  have hs : Real.sqrt c ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  field_simp at h
  linarith

end Norm

/-! ### A56.5(a): lifts are exactly the ker Wᵀ-invariant functions -/

/-- **A56.5(a).** φ : ℝⁿ → β is a lift g∘Wᵀ iff φ(u + v) = φ(u) for all u and
all v ∈ ker Wᵀ; in that case g is unique and g = φ∘(c⁻¹W). -/
theorem lift_characterisation {β : Type*} {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (φ : (Fin n → ℝ) → β) :
    ((∃ g : (Fin d → ℝ) → β, ∀ u, φ u = g (Wᵀ *ᵥ u)) ↔
        ∀ u v, Wᵀ *ᵥ v = 0 → φ (u + v) = φ u) ∧
      ∀ g : (Fin d → ℝ) → β, (∀ u, φ u = g (Wᵀ *ᵥ u)) →
        g = fun x => φ (c⁻¹ • (W *ᵥ x)) := by
  have huniq : ∀ g : (Fin d → ℝ) → β, (∀ u, φ u = g (Wᵀ *ᵥ u)) →
      g = fun x => φ (c⁻¹ • (W *ᵥ x)) := by
    intro g hg; funext x; rw [hg, transpose_mulVec_dual hc hW]
  refine ⟨⟨?_, ?_⟩, huniq⟩
  · rintro ⟨g, hg⟩ u v hv
    rw [hg, hg, Matrix.mulVec_add, hv, add_zero]
  · intro hinv
    refine ⟨fun x => φ (c⁻¹ • (W *ᵥ x)), fun u => ?_⟩
    set p := c⁻¹ • (W *ᵥ (Wᵀ *ᵥ u))
    have hv : Wᵀ *ᵥ (u - p) = 0 := by
      rw [Matrix.mulVec_sub, transpose_mulVec_dual hc hW, sub_self]
    have := hinv p (u - p) hv
    rw [add_sub_cancel] at this
    exact this

/-- A56.5(a) at the dossier's codomain (−∞, +∞] = `WithTop ℝ`. -/
theorem lift_characterisation_WithTop {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (φ : (Fin n → ℝ) → WithTop ℝ) :
    ((∃ g : (Fin d → ℝ) → WithTop ℝ, ∀ u, φ u = g (Wᵀ *ᵥ u)) ↔
        ∀ u v, Wᵀ *ᵥ v = 0 → φ (u + v) = φ u) ∧
      ∀ g : (Fin d → ℝ) → WithTop ℝ, (∀ u, φ u = g (Wᵀ *ᵥ u)) →
        g = fun x => φ (c⁻¹ • (W *ᵥ x)) :=
  lift_characterisation hc hW φ

/-! ### A56.6(a), (b): spectral bookkeeping -/

lemma frame_injective {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    Function.Injective (fun x : Fin d → ℝ => W *ᵥ x) := by
  intro x y hxy
  have := congrArg (fun z => Wᵀ *ᵥ (c⁻¹ • z)) hxy
  simpa only [transpose_mulVec_dual hc hW] using this

lemma frame_d_le_n {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : d ≤ n := by
  have hinj : Function.Injective (Matrix.mulVecLin W) := frame_injective hc hW
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

/-- ker Wᵀ = (ran W)^⊥. -/
lemma ker_transpose_iff_orth (W : Matrix (Fin n) (Fin d) ℝ) (v : Fin n → ℝ) :
    Wᵀ *ᵥ v = 0 ↔ ∀ x : Fin d → ℝ, v ⬝ᵥ (W *ᵥ x) = 0 := by
  have key : ∀ x, v ⬝ᵥ (W *ᵥ x) = (Wᵀ *ᵥ v) ⬝ᵥ x := by
    intro x; rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  constructor
  · intro h x; rw [key, h, zero_dotProduct]
  · intro h
    have := h (Wᵀ *ᵥ v)
    rw [key] at this
    exact dotProduct_self_eq_zero.mp this

/-- The range of W as a submodule of ℝⁿ. -/
abbrev ranW (W : Matrix (Fin n) (Fin d) ℝ) : Submodule ℝ (Fin n → ℝ) :=
  LinearMap.range (Matrix.mulVecLin W)

lemma conjOp_mul_W {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (H : Matrix (Fin d) (Fin d) ℝ) :
    conjOp W c H * W = W * H := by
  rw [conjOp, Matrix.mul_assoc, pushDown_mul_self hc hW, Matrix.mul_one]

lemma conjOp_ranW_invariant {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (H : Matrix (Fin d) (Fin d) ℝ) :
    ∀ u ∈ ranW W, Matrix.mulVecLin (conjOp W c H) u ∈ ranW W := by
  rintro u ⟨x, rfl⟩
  refine ⟨H *ᵥ x, ?_⟩
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, conjOp_mul_W hc hW]

/-- C|_{ran W} as a linear endomorphism of ran W. -/
noncomputable def conjOpRestrict {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (H : Matrix (Fin d) (Fin d) ℝ) :
    ranW W →ₗ[ℝ] ranW W :=
  (Matrix.mulVecLin (conjOp W c H)).restrict (conjOp_ranW_invariant hc hW H)

/-- The isomorphism W : ℝᵈ ≃ ran W. -/
noncomputable def frameEquiv {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : (Fin d → ℝ) ≃ₗ[ℝ] ranW W :=
  LinearEquiv.ofInjective (Matrix.mulVecLin W) (frame_injective hc hW)

/-- **A56.6(a).** For HF and H symmetric, C := WHW⁺:
(i) C is symmetric and C = c⁻¹WHWᵀ; (ii) CW = WH, so ran W is C-invariant;
(iii) C|_{ran W} is similar to H via the isomorphism W : ℝᵈ ≃ ran W;
(iv) C vanishes on ker Wᵀ, and ker Wᵀ = (ran W)^⊥;
(v) d ≤ n and charpoly C = X^{n−d}·charpoly H (spec C = spec H ⊎ {0}^{n−d},
with algebraic multiplicity). -/
theorem A56_6a {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : Hᵀ = H) :
    (conjOp W c H)ᵀ = conjOp W c H ∧
    conjOp W c H = c⁻¹ • conj W H ∧
    conjOp W c H * W = W * H ∧
    (∀ u ∈ ranW W, conjOp W c H *ᵥ u ∈ ranW W) ∧
    (∀ x, (frameEquiv hc hW).symm (conjOpRestrict hc hW H (frameEquiv hc hW x)) = H *ᵥ x) ∧
    (∀ v, Wᵀ *ᵥ v = 0 → conjOp W c H *ᵥ v = 0) ∧
    (∀ v, Wᵀ *ᵥ v = 0 ↔ ∀ x, v ⬝ᵥ (W *ᵥ x) = 0) ∧
    d ≤ n ∧
    (conjOp W c H).charpoly = X ^ (n - d) * H.charpoly := by
  refine ⟨?_, ?_, conjOp_mul_W hc hW H, conjOp_ranW_invariant hc hW H, ?_, ?_,
    ker_transpose_iff_orth W, frame_d_le_n hc hW, ?_⟩
  · rw [conjOp, pushDown]
    simp [transpose_mul, hH, Matrix.mul_assoc]
  · rw [conjOp, pushDown, conj, Matrix.mul_smul]
  · intro x
    rw [LinearEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [conjOpRestrict, frameEquiv, LinearMap.coe_restrict_apply,
      LinearEquiv.ofInjective_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec,
      conjOp_mul_W hc hW]
  · intro v hv
    rw [conjOp, pushDown, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hv, smul_zero,
      Matrix.mulVec_zero]
  · have h := charpoly_mul_comm_of_le W (H * pushDown W c) (by simpa using frame_d_le_n hc hW)
    rw [Matrix.mul_assoc, pushDown_mul_self hc hW, Matrix.mul_one] at h
    simpa [conjOp, Matrix.mul_assoc] using h

/-- A56.6(a), root form: the eigenvalue multiset of C (roots of its
characteristic polynomial, with multiplicity) is {0}^{n−d} ⊎ spec H. -/
theorem A56_6a_roots {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : Hᵀ = H) :
    (conjOp W c H).charpoly.roots = Multiset.replicate (n - d) 0 + H.charpoly.roots := by
  rw [(A56_6a hc hW hH).2.2.2.2.2.2.2.2, Polynomial.roots_mul
    (mul_ne_zero (pow_ne_zero _ X_ne_zero) H.charpoly_monic.ne_zero), Polynomial.roots_X_pow, Multiset.nsmul_singleton]

/-- **A56.6(b).** The lifted Hessian WHWᵀ = c·C acts as cH on ran W
((WHWᵀ)W = W(cH)) and charpoly(WHWᵀ) = X^{n−d}·charpoly(cH), i.e.
spec(WHWᵀ) = spec(cH) ⊎ {0}^{n−d}. -/
theorem A56_6b {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (H : Matrix (Fin d) (Fin d) ℝ) :
    conj W H = c • conjOp W c H ∧
    conj W H * W = W * (c • H) ∧
    (conj W H).charpoly = X ^ (n - d) * (c • H).charpoly ∧
    (conj W H).charpoly.roots = Multiset.replicate (n - d) 0 + (c • H).charpoly.roots := by
  have hCW : conj W H * W = W * (c • H) := by
    rw [conj, Matrix.mul_assoc, hW, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_smul]
  have hchar : (conj W H).charpoly = X ^ (n - d) * (c • H).charpoly := by
    have h := charpoly_mul_comm_of_le W (H * Wᵀ) (by simpa using frame_d_le_n hc hW)
    rw [Matrix.mul_assoc, hW, Matrix.mul_smul, Matrix.mul_one] at h
    simpa [conj, Matrix.mul_assoc] using h
  refine ⟨?_, hCW, hchar, ?_⟩
  · rw [conjOp, pushDown, conj, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · rw [hchar, Polynomial.roots_mul
      (mul_ne_zero (pow_ne_zero _ X_ne_zero) (c • H).charpoly_monic.ne_zero),
      Polynomial.roots_X_pow, Multiset.nsmul_singleton]

/-! ### A56.6(d): scale invariance of the signed-diagonal η -/

/-- **A56.6(d), scale part.** For ρ > 0: η(ρA) = η(A); ρA has positive
diagonal iff A does (so η(ρA) is defined iff η(A) is); and the test agrees. -/
theorem A56_6d_scale {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    domRatio (ρ • A) = domRatio A ∧
    ((∀ i, 0 < (ρ • A) i i) ↔ ∀ i, 0 < A i i) ∧
    (PassesDominance (ρ • A) ↔ PassesDominance A) := by
  have hpos : (∀ i, 0 < (ρ • A) i i) ↔ ∀ i, 0 < A i i := by
    simp only [Matrix.smul_apply, smul_eq_mul]
    exact forall_congr' fun i => mul_pos_iff_of_pos_left hρ
  refine ⟨domRatio_smul hρ, hpos, ?_⟩
  unfold PassesDominance
  rw [domRatio_smul hρ, hpos]

/-- **A56.6(d), frame part.** η(WHWᵀ) = η(WHW⁺); both are defined under the same
condition, wᵢᵀHwᵢ > 0 for every row wᵢ of W (the diagonal entries are
(WHWᵀ)ᵢᵢ = wᵢᵀHwᵢ and (WHW⁺)ᵢᵢ = c⁻¹wᵢᵀHwᵢ). -/
theorem A56_6d_frame {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (H : Matrix (Fin d) (Fin d) ℝ) :
    domRatio (conj W H) = domRatio (conjOp W c H) ∧
    (∀ i, conj W H i i = W i ⬝ᵥ (H *ᵥ W i)) ∧
    (∀ i, conjOp W c H i i = c⁻¹ * (W i ⬝ᵥ (H *ᵥ W i))) ∧
    ((∀ i, 0 < conj W H i i) ↔ ∀ i, 0 < W i ⬝ᵥ (H *ᵥ W i)) ∧
    ((∀ i, 0 < conjOp W c H i i) ↔ ∀ i, 0 < W i ⬝ᵥ (H *ᵥ W i)) ∧
    (PassesDominance (conj W H) ↔ PassesDominance (conjOp W c H)) := by
  have hCC : conj W H = c • conjOp W c H := by
    rw [conjOp, pushDown, conj, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  have hdiag : ∀ i, conj W H i i = W i ⬝ᵥ (H *ᵥ W i) := by
    intro i
    simp only [conj, Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
      Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hdiag' : ∀ i, conjOp W c H i i = c⁻¹ * (W i ⬝ᵥ (H *ᵥ W i)) := by
    intro i
    rw [conjOp, pushDown, Matrix.mul_smul, Matrix.smul_apply, ← conj, hdiag, smul_eq_mul]
  have hs := A56_6d_scale (conjOp W c H) hc
  rw [← hCC] at hs
  refine ⟨hs.1, hdiag, hdiag', ?_, ?_, hs.2.2⟩
  · simp only [hdiag]
  · simp only [hdiag']
    exact forall_congr' fun i => mul_pos_iff_of_pos_left (inv_pos.mpr hc)

/-- The A56.6(d) failure witness: d = 2, n = 3, W = [I₂; 0] (c = 1),
H = diag(1, 2). WᵀW = I₂, and diag(WHW⁺) = (1, 2, 0), so η is undefined. -/
theorem A56_6d_failure :
    let W : Matrix (Fin 3) (Fin 2) ℝ := !![1, 0; 0, 1; 0, 0]
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]
    Wᵀ * W = (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    conjOp W 1 H 0 0 = 1 ∧ conjOp W 1 H 1 1 = 2 ∧ conjOp W 1 H 2 2 = 0 ∧
    ¬ (∀ i, 0 < conjOp W 1 H i i) ∧ ¬ PassesDominance (conjOp W 1 H) := by
  intro W H
  have h22 : conjOp W 1 H 2 2 = 0 := by
    simp [W, H, conjOp, pushDown, Matrix.mul_apply]
  refine ⟨?_, ?_, ?_, h22, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [W, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [W, H, conjOp, pushDown, Matrix.mul_apply, Fin.sum_univ_succ]
  · simp [W, H, conjOp, pushDown, Matrix.mul_apply, Fin.sum_univ_succ]
  · intro h; have := h 2; rw [h22] at this; exact lt_irrefl 0 this
  · intro h; have := h.1 2; rw [h22] at this; exact lt_irrefl 0 this

/-! ### A56.6(e) (bonus): η is not conjugation-invariant -/

/-- A56.6(e) witness. H = diag(1, 2), η(H) = 0; W = [[1, −1], [1, 1]] (c = 2,
i.e. √2 times the rotation by π/4, which gives the same WHW⁺) yields
WHW⁺ = [[3/2, −1/2], [−1/2, 3/2]] and η(WHW⁺) = 1/3. -/
theorem A56_6e :
    let W : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1; 1, 1]
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 2]
    Wᵀ * W = (2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) ∧
    domRatio H = 0 ∧
    conjOp W 2 H = !![3 / 2, -1 / 2; -1 / 2, 3 / 2] ∧
    domRatio (conjOp W 2 H) = 1 / 3 := by
  intro W H
  have hC : conjOp W 2 H = !![3 / 2, -1 / 2; -1 / 2, 3 / 2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [W, H, conjOp, pushDown, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  refine ⟨?_, ?_, hC, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [W, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  · rw [domRatio_two]; simp [H]
  · rw [hC, domRatio_two]; norm_num [abs_of_pos]

/-! ### A56.6(f): the floor η(WHW⁺) ≥ 1 for redundant frames -/

/-- **A56.6(f).** If n > d and η(WHW⁺) is defined (positive diagonal), then
η(WHW⁺) ≥ 1, so the dominance test never passes on ℝⁿ. (Symmetry of H is
not needed, and of HF only the shape d < n is used; HF is kept so the
statement reads exactly as the dossier's.) -/
theorem A56_6f {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (_hc : 0 < c)
    (_hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) (H : Matrix (Fin d) (Fin d) ℝ)
    (hnd : d < n) (hpos : ∀ i, 0 < conjOp W c H i i) :
    1 ≤ domRatio (conjOp W c H) ∧ ¬ PassesDominance (conjOp W c H) := by
  -- C is singular: it vanishes on ker Wᵀ ≠ {0}.
  have hker : LinearMap.ker (Matrix.mulVecLin Wᵀ) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa using hnd)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv
  have hsing : (conjOp W c H).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv0, ?_⟩
    rw [conjOp, pushDown, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, hv, smul_zero,
      Matrix.mulVec_zero]
  have hnp : ¬ PassesDominance (conjOp W c H) := by
    intro hp
    refine absurd hsing (det_ne_zero_of_sum_row_lt_diag (A := conjOp W c H) ?_)
    intro k
    have hk := passes_imp_row_lt hp k
    rw [Real.norm_eq_abs, abs_of_pos (hp.1 k)]
    simpa [gershRadius, Real.norm_eq_abs] using hk
  refine ⟨?_, hnp⟩
  by_contra hlt
  exact hnp ⟨hpos, lt_of_not_ge hlt⟩

/-- A56.6(f), equality instance: n = 2, d = 1, W = (1, 1)ᵀ (c = 2), H = (1):
WHW⁺ = ½[[1, 1], [1, 1]], positive diagonal, η = 1. -/
theorem A56_6f_attained :
    let W : Matrix (Fin 2) (Fin 1) ℝ := !![1; 1]
    let H : Matrix (Fin 1) (Fin 1) ℝ := !![1]
    Wᵀ * W = (2 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) ∧
    conjOp W 2 H = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] ∧
    (∀ i, 0 < conjOp W 2 H i i) ∧
    domRatio (conjOp W 2 H) = 1 := by
  intro W H
  have hC : conjOp W 2 H = !![1 / 2, 1 / 2; 1 / 2, 1 / 2] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [W, H, conjOp, pushDown, Matrix.mul_apply]
  refine ⟨?_, hC, ?_, ?_⟩
  · ext i j; fin_cases i; fin_cases j; simp [W, Matrix.mul_apply]; norm_num
  · rw [hC]; intro i; fin_cases i <;> norm_num
  · rw [hC, domRatio_two]; norm_num

end OCF.A56

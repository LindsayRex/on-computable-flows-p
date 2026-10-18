/-
T1 (Composite gap via kernel transversality) — part (b), the SHARP
weighted-defect bound λ_min(H) ≥ Δ_w, and the middle inequality
Δ_w ≥ (minᵢ aᵢ)·s of the same display.

Source of truth: project_plan/done/proof_audits/T1_composite_gap/01_derivation.md
(adjudicated 2026-07-27; Theorem T1(b), L3, L4, ST.3, ST.4) and the
B1p adjudication's commissioned Lean pass
(project_plan/done/proof_audits/B1p_uniform_composite_gap/03_adjudication.md,
author-approved 2026-10-09, decision 4). Landed statement:
sections/04_composition/02_composite_gap_kernel_transversality.tex,
Theorem `thm:composite-gap`(b) (per-term gap there written νᵢ; it is the
dossier's γᵢ, `restrictedGap` below).

This file formalises T1(b)'s full display

  λ_min(Σᵢ wᵢHᵢ) ≥ Δ_w = Σᵢ aᵢ − λ_max(A^{1/2} G A^{1/2})
                  ≥ (minᵢ aᵢ) · (n − λ_max(G)),          aᵢ = wᵢγᵢ,

reusing T1GramBound.lean (restrictedGap, lambdaMax, gramMatrix, L2's
quadratic-form minorant `gap_mul_residual_le_quadForm`, and the
Cauchy–Schwarz Gram transfer `sum_sq_dotProduct_le_lambdaMax`).

DEFINITIONAL MAP (additions to T1GramBound.lean's map):

* (D7) A := blockdiag(a₁I_{k₁}, …, a_nI_{k_n}) on the stacked index
  (sigma type) — `blockWeight a`, the diagonal matrix with entry a_{z.1}
  at the stacked column z = ⟨i, p⟩. A^{1/2} — `blockWeightSqrt a`, the
  diagonal matrix of √a_{z.1} (for aᵢ ≥ 0 this is the PSD square root
  of A; `blockWeightSqrt_mul_self` proves (A^{1/2})² = A).
* (D7) weighted Gram A^{1/2} G A^{1/2} — `weightedGram b a`, literally
  the matrix product `blockWeightSqrt a * gramMatrix b * blockWeightSqrt a`.
  Its λ_max is `lambdaMax (weightedGram b a)`, with (D7)'s k = 0
  convention automatic as in T1GramBound.lean.
* (D8) Δ_w — `deltaW b a := Σᵢ aᵢ − lambdaMax (weightedGram b a)`, i.e.
  the L4 form Δ_w = Σᵢaᵢ − λ_max(A^{1/2}GA^{1/2}) used in the theorem
  display (the L3 form Σaᵢ − λ_max(Σ aᵢP_{Kᵢ}) is its definitionally
  prior value; L4 proves them equal; this file states and proves the
  bound for the Gram form, which is the displayed certificate).
* s — `(n : ℝ) − lambdaMax (gramMatrix b)`, as in T1GramBound.lean.

PROOF ROUTE: (i) A^{1/2}GA^{1/2} is the Gram matrix of the scaled
columns √aᵢ·bᵢₚ (`weightedGram_eq_gramMatrix_scaled`); (ii) the existing
Cauchy–Schwarz Gram transfer applied to the scaled columns gives
Σᵢ aᵢ‖P_{Kᵢ}x‖² ≤ λ_max(A^{1/2}GA^{1/2})‖x‖² (the L4 inequality
direction consumed by ST.3); (iii) with L2 summed (S3.1):
Δ_w‖x‖² ≤ Σᵢ aᵢ(‖x‖² − ‖P_{Kᵢ}x‖²) ≤ xᵀHx (`flat_minorant_ge` is the
pure projector-geometry middle step, reused by B1pUniformGap.lean).
For ST.4 (Δ_w ≥ m·s) the needed direction of S4.2 — λ_max(XᵀX) ≤ any
upper Rayleigh bound of XXᵀ — is proved by pushing a top eigenvector c
of the Gram matrix forward to y = Xc (`lambdaMax_gramMatrix_le`); the
upper bound on XXᵀ is ST.4's freeze-the-smallest-coefficient split with
Bessel (‖P_{Kᵢ}y‖² ≤ ‖y‖²) on the first sum and L4 on the second.

Status tier: FORMALISED (statement + proof, no sorry).
-/
import Mathlib
import OcfVerification.T1GramBound

open Matrix BigOperators

namespace OCF

variable {d n : ℕ} {k : Fin n → ℕ}

/-! ### (D7) The block weight matrix A, its square root, the weighted Gram -/

/-- (D7) A = blockdiag(a₁I_{k₁}, …, a_nI_{k_n}) on the stacked index. -/
noncomputable def blockWeight (a : Fin n → ℝ) :
    Matrix ((i : Fin n) × Fin (k i)) ((i : Fin n) × Fin (k i)) ℝ :=
  Matrix.diagonal fun z => a z.1

/-- (D7) A^{1/2}: the diagonal matrix of √a_{z.1}. -/
noncomputable def blockWeightSqrt (a : Fin n → ℝ) :
    Matrix ((i : Fin n) × Fin (k i)) ((i : Fin n) × Fin (k i)) ℝ :=
  Matrix.diagonal fun z => Real.sqrt (a z.1)

/-- For nonnegative weights, `blockWeightSqrt` squares to `blockWeight`
(it is the PSD square root of A). -/
lemma blockWeightSqrt_mul_self {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i) :
    (blockWeightSqrt (k := k) a) * blockWeightSqrt a = blockWeight a := by
  rw [blockWeightSqrt, blockWeight, Matrix.diagonal_mul_diagonal]
  congr 1
  funext z
  exact Real.mul_self_sqrt (ha z.1)

/-- (D7) The weighted Gram matrix A^{1/2} G A^{1/2}. -/
noncomputable def weightedGram (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (a : Fin n → ℝ) :
    Matrix ((i : Fin n) × Fin (k i)) ((i : Fin n) × Fin (k i)) ℝ :=
  blockWeightSqrt a * gramMatrix b * blockWeightSqrt a

/-- (D8) The weighted joint defect Δ_w = Σᵢ aᵢ − λ_max(A^{1/2} G A^{1/2}). -/
noncomputable def deltaW (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (a : Fin n → ℝ) : ℝ :=
  ∑ i, a i - lambdaMax (weightedGram b a)

/-- A^{1/2} G A^{1/2} is the Gram matrix of the scaled columns √aᵢ·bᵢₚ
(S4.1: Σ aᵢ P_{Kᵢ} = (BA^{1/2})(BA^{1/2})ᵀ, Gram side). -/
lemma weightedGram_eq_gramMatrix_scaled
    (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) (a : Fin n → ℝ) :
    weightedGram b a = gramMatrix (fun i p => Real.sqrt (a i) • b i p) := by
  ext z w
  simp only [weightedGram, blockWeightSqrt, Matrix.diagonal_mul, Matrix.mul_diagonal,
    gramMatrix, Matrix.of_apply, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

/-- Σ over the stacked columns of ⟨√aᵢ bᵢₚ, x⟩² is Σᵢ aᵢ Σₚ⟨bᵢₚ, x⟩²
(= Σᵢ aᵢ‖P_{Kᵢ}x‖² under orthonormality). -/
lemma sum_sq_scaled_eq {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) (x : Fin d → ℝ) :
    ∑ z : (i : Fin n) × Fin (k i), ((Real.sqrt (a z.1) • b z.1 z.2) ⬝ᵥ x) ^ 2
      = ∑ i, a i * ∑ p, (b i p ⬝ᵥ x) ^ 2 := by
  rw [← Finset.univ_sigma_univ, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [smul_dotProduct, smul_eq_mul, mul_pow, Real.sq_sqrt (ha i)]

/-- **L4 for the weighted Gram (inequality direction consumed by ST.3).**
Σᵢ aᵢ Σₚ⟨bᵢₚ, x⟩² ≤ λ_max(A^{1/2}GA^{1/2})·‖x‖². -/
lemma weighted_sum_sq_le_lambdaMax {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) (x : Fin d → ℝ) :
    ∑ i, a i * ∑ p, (b i p ⬝ᵥ x) ^ 2 ≤ lambdaMax (weightedGram b a) * (x ⬝ᵥ x) := by
  rw [← sum_sq_scaled_eq ha b x, weightedGram_eq_gramMatrix_scaled]
  exact sum_sq_dotProduct_le_lambdaMax (fun i p => Real.sqrt (a i) • b i p) x

/-- **Flat minorant lower bound (L3 + L4, pure projector geometry).**
For any columns bᵢₚ and weights aᵢ ≥ 0,
Δ_w·‖x‖² ≤ Σᵢ aᵢ(‖x‖² − Σₚ⟨bᵢₚ, x⟩²); under orthonormal bases of Kᵢ the
right side is xᵀ(Σᵢ aᵢP_{Kᵢ^⊥})x. -/
lemma flat_minorant_ge {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) (x : Fin d → ℝ) :
    deltaW b a * (x ⬝ᵥ x) ≤ ∑ i, a i * (x ⬝ᵥ x - ∑ p, (b i p ⬝ᵥ x) ^ 2) := by
  have h := weighted_sum_sq_le_lambdaMax ha b x
  have hexp : ∑ i, a i * (x ⬝ᵥ x - ∑ p, (b i p ⬝ᵥ x) ^ 2)
      = (∑ i, a i) * (x ⬝ᵥ x) - ∑ i, a i * ∑ p, (b i p ⬝ᵥ x) ^ 2 := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hexp, deltaW]
  linarith

/-! ### T1(b), sharp form: λ_min(Σ wᵢHᵢ) ≥ Δ_w -/

/-- S1.1 (local copy; the part-(a) and Gram-bound files' versions are
`private`). -/
private lemma dotProduct_sum_smul_mulVec''
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (∑ i, w i • H i) *ᵥ x = ∑ i, w i * (x ⬝ᵥ H i *ᵥ x) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **T1(b), sharp bound (ST.3), Loewner form.** Under (H1)–(H4), with
orthonormal kernel bases stacked into G and aᵢ = wᵢγᵢ,
Σᵢ wᵢHᵢ − Δ_w·I is PSD, where Δ_w = Σᵢ aᵢ − λ_max(A^{1/2}GA^{1/2}). -/
theorem composite_gap_sharp_posSemidef
    (_hn : 0 < n) (_hd : 0 < d)
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (_hH4 : ∀ i, H i ≠ 0)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0)
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = matKer (H i)) :
    ((∑ i, w i • H i)
      - deltaW b (fun i => w i * restrictedGap (H i))
        • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  -- (H1), (H2)'s n ≥ 1, and (H4) are not consumed (see T1GramBound.lean's
  -- definitional map); they are kept so the hypotheses are the dossier's.
  set a : Fin n → ℝ := fun i => w i * restrictedGap (H i) with ha_def
  have ha : ∀ i, 0 ≤ a i := fun i =>
    mul_nonneg (hw i).le (restrictedGap_nonneg (hpsd i))
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · exact (isSelfAdjoint_sum _ fun i _ =>
        (hpsd i).1.smul (IsSelfAdjoint.all (w i))).sub
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  · intro x
    rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_sub, dotProduct_smul, smul_eq_mul, sub_nonneg,
      dotProduct_sum_smul_mulVec'']
    -- L2 per term, scaled by wᵢ (S3.1)
    have hL2 : ∀ i, a i * (x ⬝ᵥ x - ∑ p, (b i p ⬝ᵥ x) ^ 2)
        ≤ w i * (x ⬝ᵥ H i *ᵥ x) := by
      intro i
      have h := gap_mul_residual_le_quadForm (hpsd i) (hbo i) (hbs i) x
      calc a i * (x ⬝ᵥ x - ∑ p, (b i p ⬝ᵥ x) ^ 2)
          = w i * (restrictedGap (H i) * (x ⬝ᵥ x - ∑ p, (b i p ⬝ᵥ x) ^ 2)) := by
            simp only [ha_def]; ring
        _ ≤ w i * (x ⬝ᵥ H i *ᵥ x) := mul_le_mul_of_nonneg_left h (hw i).le
    exact (flat_minorant_ge ha b x).trans (Finset.sum_le_sum fun i _ => hL2 i)

/-- Spectral reading of a Loewner lower bound: if S − c·I is PSD then c
is at most every eigenvalue of the Hermitian S. -/
lemma le_eigenvalues_of_sub_posSemidef {S : Matrix (Fin d) (Fin d) ℝ}
    (hS : S.IsHermitian) {c : ℝ} (hpsd : (S - c • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef)
    (j : Fin d) : c ≤ hS.eigenvalues j := by
  have hmem : hS.eigenvalues j ∈ spectrum ℝ S := by
    rw [hS.spectrum_real_eq_range_eigenvalues]
    exact ⟨j, rfl⟩
  have hsub : hS.eigenvalues j - c
      ∈ spectrum ℝ (S - algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ) c) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hmem rfl
  rw [Algebra.algebraMap_eq_smul_one] at hsub
  have hnn := (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hpsd).2 hsub
  simpa [sub_nonneg] using hnn

/-- **T1(b), sharp bound, λ_min form:** the landed display
λ_min(Σᵢ wᵢHᵢ) ≥ Δ_w = Σᵢ wᵢγᵢ − λ_max(A^{1/2}GA^{1/2}), λ_min written as
the minimum (`⨅`) of the eigenvalues. -/
theorem composite_gap_sharp_le_iInf_eigenvalues
    (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (hH4 : ∀ i, H i ≠ 0)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0)
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = matKer (H i))
    (hS : (∑ i, w i • H i).IsHermitian) :
    deltaW b (fun i => w i * restrictedGap (H i)) ≤ ⨅ j, hS.eigenvalues j := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact le_ciInf fun j => le_eigenvalues_of_sub_posSemidef hS
    (composite_gap_sharp_posSemidef hn hd H w hw hpsd hH4 b hbo hbs) j

/-! ### ST.4: Δ_w ≥ (minᵢ aᵢ)·s -/

/-- Bessel for an orthonormal family: Σₚ⟨bₚ, x⟩² ≤ ‖x‖² (S5.1's
classical input; P_K ⪯ I). -/
lemma sum_sq_dotProduct_le_self {κ : ℕ} {b : Fin κ → (Fin d → ℝ)}
    (hbo : ∀ p q, b p ⬝ᵥ b q = if p = q then 1 else 0) (x : Fin d → ℝ) :
    ∑ p, (b p ⬝ᵥ x) ^ 2 ≤ x ⬝ᵥ x := by
  set u : Fin d → ℝ := ∑ p, (b p ⬝ᵥ x) • b p with hu
  have hbu : ∀ p, b p ⬝ᵥ u = b p ⬝ᵥ x := by
    intro p
    rw [hu, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, hbo]
    simp [mul_ite, Finset.sum_ite_eq]
  have hxu : x ⬝ᵥ u = ∑ p, (b p ⬝ᵥ x) ^ 2 := by
    rw [hu, dotProduct_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x (b p), sq]
  have hux : u ⬝ᵥ x = ∑ p, (b p ⬝ᵥ x) ^ 2 := by
    rw [hu, sum_dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_dotProduct, smul_eq_mul, sq]
  have huu : u ⬝ᵥ u = ∑ p, (b p ⬝ᵥ x) ^ 2 := by
    conv_lhs => rw [hu, sum_dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_dotProduct, smul_eq_mul, hbu p, sq]
  have h0 : 0 ≤ (x - u) ⬝ᵥ (x - u) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hxu, hux, huu] at h0
  linarith

/-- **S4.2, the direction ST.4 needs.** If the quadratic form of XXᵀ
(y ↦ Σ_z⟨b_z, y⟩²) is bounded by C‖y‖² with C ≥ 0, then λ_max of the
Gram matrix XᵀX is at most C. Proof: push a top eigenvector c of the
Gram matrix forward to y = Σ_z c_z b_z. -/
lemma lambdaMax_gramMatrix_le (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    {C : ℝ} (hC : 0 ≤ C)
    (hq : ∀ y : Fin d → ℝ,
      ∑ z : (i : Fin n) × Fin (k i), (b z.1 z.2 ⬝ᵥ y) ^ 2 ≤ C * (y ⬝ᵥ y)) :
    lambdaMax (gramMatrix b) ≤ C := by
  have hG := gramMatrix_isHermitian b
  rw [show lambdaMax (gramMatrix b) = ⨆ j, hG.eigenvalues j from dif_pos hG]
  rcases isEmpty_or_nonempty ((i : Fin n) × Fin (k i)) with hE | hE
  · rw [Real.iSup_of_isEmpty]; exact hC
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := hG.eigenvalues)
  rw [← hj]
  set μ : ℝ := hG.eigenvalues j with hμ
  set c : ((i : Fin n) × Fin (k i)) → ℝ := ⇑(hG.eigenvectorBasis j) with hc
  have hGc : gramMatrix b *ᵥ c = μ • c := hG.mulVec_eigenvectorBasis j
  have hcc : c ⬝ᵥ c = 1 := by
    have h1 := hG.eigenvectorBasis.orthonormal.1 j
    have h2 : ‖hG.eigenvectorBasis j‖ ^ 2 = c ⬝ᵥ c := by
      rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct,
        star_trivial]
    rw [← h2, h1, one_pow]
  set y : Fin d → ℝ := ∑ z, c z • b z.1 z.2 with hy
  -- ⟨b_w, y⟩ = (G c)_w = μ c_w
  have hby : ∀ w : (i : Fin n) × Fin (k i), b w.1 w.2 ⬝ᵥ y = μ * c w := by
    intro w
    have h := congrFun hGc w
    simp only [Pi.smul_apply, smul_eq_mul] at h
    have hrow : (gramMatrix b *ᵥ c) w = ∑ z, (b w.1 w.2 ⬝ᵥ b z.1 z.2) * c z := rfl
    rw [← h, hrow, hy, dotProduct_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [dotProduct_smul, smul_eq_mul, mul_comm]
  have hyy : y ⬝ᵥ y = μ := by
    rw [hy, ← dotProduct_gramMatrix_mulVec, hGc, dotProduct_smul, hcc, smul_eq_mul,
      mul_one]
  have hsum : ∑ z : (i : Fin n) × Fin (k i), (b z.1 z.2 ⬝ᵥ y) ^ 2 = μ * μ := by
    simp only [hby]
    have : ∑ z : (i : Fin n) × Fin (k i), (μ * c z) ^ 2 = μ * μ * (c ⬝ᵥ c) := by
      rw [dotProduct, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [this, hcc, mul_one]
  have h := hq y
  rw [hsum, hyy] at h
  rcases le_or_gt μ 0 with hμ0 | hμ0
  · exact hμ0.trans hC
  · nlinarith

/-- **ST.4 (T1(b)'s middle inequality).** For orthonormal kernel bases
and weights aᵢ ≥ 0 (n ≥ 1): Δ_w ≥ (minᵢ aᵢ)·(n − λ_max(G)).
Pure projector geometry (no Hᵢ involved, as in L4). -/
theorem deltaW_ge_min_mul_defect (hn : 0 < n)
    {a : Fin n → ℝ} (ha : ∀ i, 0 ≤ a i)
    (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0) :
    (⨅ i, a i) * ((n : ℝ) - lambdaMax (gramMatrix b)) ≤ deltaW b a := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  set m : ℝ := ⨅ i, a i with hm
  set g : ℝ := lambdaMax (gramMatrix b) with hg
  have hm0 : 0 ≤ m := le_ciInf ha
  have hmle : ∀ i, m ≤ a i := fun i => ciInf_le (Set.finite_range _).bddBelow i
  have hg0 : 0 ≤ g := lambdaMax_nonneg (gramMatrix_posSemidef b)
  set C : ℝ := ∑ i, (a i - m) + m * g with hC
  have hC0 : 0 ≤ C :=
    add_nonneg (Finset.sum_nonneg fun i _ => sub_nonneg.mpr (hmle i)) (mul_nonneg hm0 hg0)
  -- XXᵀ ⪯ C·I (ST.4's split, Bessel on the first sum, L4 on the second)
  have hq : ∀ y : Fin d → ℝ, ∑ z : (i : Fin n) × Fin (k i),
      ((Real.sqrt (a z.1) • b z.1 z.2) ⬝ᵥ y) ^ 2 ≤ C * (y ⬝ᵥ y) := by
    intro y
    rw [sum_sq_scaled_eq ha b y]
    set t : Fin n → ℝ := fun i => ∑ p, (b i p ⬝ᵥ y) ^ 2 with ht
    have hL4 : ∑ i, t i ≤ g * (y ⬝ᵥ y) := by
      have h := sum_sq_dotProduct_le_lambdaMax b y
      rwa [← Finset.univ_sigma_univ, Finset.sum_sigma] at h
    have hB : ∀ i, (a i - m) * t i ≤ (a i - m) * (y ⬝ᵥ y) := fun i =>
      mul_le_mul_of_nonneg_left (sum_sq_dotProduct_le_self (hbo i) y)
        (sub_nonneg.mpr (hmle i))
    calc ∑ i, a i * t i = ∑ i, (a i - m) * t i + m * ∑ i, t i := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => by ring
      _ ≤ ∑ i, (a i - m) * (y ⬝ᵥ y) + m * (g * (y ⬝ᵥ y)) :=
          add_le_add (Finset.sum_le_sum fun i _ => hB i)
            (mul_le_mul_of_nonneg_left hL4 hm0)
      _ = C * (y ⬝ᵥ y) := by rw [hC, ← Finset.sum_mul]; ring
  have hlam : lambdaMax (weightedGram b a) ≤ C := by
    rw [weightedGram_eq_gramMatrix_scaled]
    exact lambdaMax_gramMatrix_le _ hC0 hq
  have hsumm : ∑ i, (a i - m) = ∑ i, a i - (n : ℝ) * m := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
  rw [deltaW]
  rw [hC, hsumm] at hlam
  linarith

/-- **T1(b), the full display:** λ_min(Σᵢ wᵢHᵢ) ≥ Δ_w ≥ (minᵢ wᵢγᵢ)·s,
s = n − λ_max(G), λ_min written as `⨅` of the eigenvalues. -/
theorem composite_gap_display
    (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (hH4 : ∀ i, H i ≠ 0)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0)
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = matKer (H i))
    (hS : (∑ i, w i • H i).IsHermitian) :
    deltaW b (fun i => w i * restrictedGap (H i)) ≤ ⨅ j, hS.eigenvalues j ∧
    (⨅ i, w i * restrictedGap (H i)) * ((n : ℝ) - lambdaMax (gramMatrix b))
      ≤ deltaW b (fun i => w i * restrictedGap (H i)) :=
  ⟨composite_gap_sharp_le_iInf_eigenvalues hn hd H w hw hpsd hH4 b hbo hbs hS,
    deltaW_ge_min_mul_defect hn
      (fun i => mul_nonneg (hw i).le (restrictedGap_nonneg (hpsd i))) b hbo⟩

end OCF

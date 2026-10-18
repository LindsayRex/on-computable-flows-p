/-
T1 (Composite gap via kernel transversality) — part (a), the PD dichotomy.

Source of truth: project_plan/done/proof_audits/T1_composite_gap/01_derivation.md
(adjudicated 2026-07-27). This file formalises T1(a):

  For PSD symmetric H_i with positive weights w_i, the composed matrix
  H = Σ w_i H_i is positive definite iff the kernels intersect trivially.

Status tier: FORMALISED (statement + proof, both directions, no sorry).
T1(b) (quantitative Gram-defect bound) is deferred — statement
formalisation only, later.

Pipeline note: a compiled proof of (a) supersedes the stage-2 validity
audit for the steps it covers (L1 and the (a)-direction of the theorem
assembly); statement-intent review remains human.
-/
import Mathlib

open Matrix BigOperators

namespace OCF

variable {d n : ℕ}

/-- The kernel of a matrix as a submodule, via its linear map. -/
abbrev matKer (A : Matrix (Fin d) (Fin d) ℝ) : Submodule ℝ (Fin d → ℝ) :=
  LinearMap.ker A.mulVecLin

/-- Quadratic form of the weighted sum expands to the weighted sum of
per-term quadratic forms (S1.1 of the dossier). -/
private lemma dotProduct_sum_smul_mulVec
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (∑ i, w i • H i) *ᵥ x = ∑ i, w i * (x ⬝ᵥ H i *ᵥ x) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **T1(a), forward direction.** If the weighted sum of PSD matrices is
positive definite, the kernels intersect trivially. -/
theorem kernels_trivial_of_posDef
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hpd : (∑ i, w i • H i).PosDef) :
    (⨅ i, matKer (H i)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  by_contra hxne
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, mulVecLin_apply] at hx
  have hzero : (∑ i, w i • H i) *ᵥ x = 0 := by
    rw [Matrix.sum_mulVec]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.smul_mulVec, hx i, smul_zero]
  have hpos := hpd.dotProduct_mulVec_pos hxne
  rw [hzero, dotProduct_zero] at hpos
  exact lt_irrefl _ hpos

/-- **T1(a), backward direction.** If the kernels of PSD matrices
intersect trivially and all weights are positive, the weighted sum is
positive definite. -/
theorem posDef_of_kernels_trivial
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (hker : (⨅ i, matKer (H i)) = ⊥) :
    (∑ i, w i • H i).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hxne => ?_
  · -- Hermitian: sum of real symmetric matrices with real scalars
    exact isSelfAdjoint_sum _ fun i _ => (hpsd i).1.smul (IsSelfAdjoint.all (w i))
  · -- quadratic form of the sum = Σ w_i ⟪x, H_i x⟫, each term ≥ 0
    rw [star_trivial, dotProduct_sum_smul_mulVec]
    have hterm : ∀ i ∈ Finset.univ, (0:ℝ) ≤ w i * (x ⬝ᵥ H i *ᵥ x) := fun i _ => by
      have h := (hpsd i).dotProduct_mulVec_nonneg x
      rw [star_trivial] at h
      exact mul_nonneg (hw i).le h
    -- strict: if every term were zero, x would lie in every kernel,
    -- contradicting triviality of the intersection (L1 assembly)
    refine lt_of_le_of_ne (Finset.sum_nonneg hterm) (Ne.symm fun h0 => ?_)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp h0
    have hxker : ∀ i, H i *ᵥ x = 0 := fun i => by
      have hq : x ⬝ᵥ H i *ᵥ x = 0 :=
        (mul_eq_zero.mp (hz i (Finset.mem_univ i))).resolve_left (hw i).ne'
      have hiff := (hpsd i).dotProduct_mulVec_zero_iff x
      rw [star_trivial] at hiff
      exact hiff.mp hq
    have hmem : x ∈ ⨅ i, matKer (H i) := by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, mulVecLin_apply]
      exact hxker
    rw [hker, Submodule.mem_bot] at hmem
    exact hxne hmem

/-- **T1(a), the dichotomy as one iff** (dossier statement:
H ≻ 0 ⟺ ∩ᵢ Kᵢ = {0}). -/
theorem posDef_iff_kernels_trivial
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef) :
    (∑ i, w i • H i).PosDef ↔ (⨅ i, matKer (H i)) = ⊥ :=
  ⟨kernels_trivial_of_posDef H w, posDef_of_kernels_trivial H w hw hpsd⟩

end OCF

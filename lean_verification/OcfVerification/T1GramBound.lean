/-
T1 (Composite gap via kernel transversality) — part (b), the quantitative
Gram-defect bound (primary bound with the weight-splitting step ST.4).

Source of truth: project_plan/done/proof_audits/T1_composite_gap/01_derivation.md
(adjudicated 2026-07-27). This file formalises T1(b)'s display

  λ_min(Σᵢ wᵢ Hᵢ) ≥ (minᵢ wᵢ γᵢ) · (n − λ_max(G)),   s = n − λ_max(G),

for real symmetric PSD Hᵢ with kernels Kᵢ, positive weights wᵢ, per-term
restricted gaps γᵢ, and G the Gram matrix of stacked orthonormal bases of
the kernels. Proof shape per the dossier: L2 (per-term spectral minorant,
S2.4 quadratic form) → L3 + ST.4 (projector reduction and the
freeze-the-smallest-coefficient splitting) → L4 (Gram transfer) → ST
assembly.

DEFINITIONAL MAP (dossier D1–D9 → Lean; the design choices of this file):

* (H1) d ≥ 1; (H2) n ≥ 1, Hᵢ PSD; (H3) wᵢ > 0; (H4) Hᵢ ≠ 0 —
  hypotheses `_hd`, `hn`, `hpsd`, `hw`, `_hH4` below. `_hd` and `_hH4`
  are not consumed by the proof of the inequality (the `sInf` rendering
  of γᵢ makes the bound provable without them) but are kept so the
  formal hypotheses are exactly the dossier's standing hypotheses.
* (D2) Kᵢ = ker Hᵢ — `matKer (H i)` (imported from part (a)).
* (D4) γᵢ = min { xᵀHᵢx : x ∈ Kᵢ^⊥, ‖x‖ = 1 } — `restrictedGap`, the
  `sInf` of the quadratic form over exactly that set (unit sphere of the
  orthogonal complement, both conditions in `⬝ᵥ` form). When the minimum
  exists — it does under (H2)+(H4), by compactness — the minimum IS the
  infimum of the set, so this denotes the dossier's number; the proof
  only consumes the lower-bound direction (`csInf_le`), which is why
  (H4) goes unused.
* (D5) aᵢ = wᵢγᵢ and minᵢ aᵢ — `⨅ i, w i * restrictedGap (H i)`, a
  genuine minimum (`Fin n` nonempty by `hn`, finite).
* (D6) stacked orthonormal kernel bases — `b : (i : Fin n) → Fin (k i) →
  (Fin d → ℝ)` with `hbo` (orthonormal columns, BᵢᵀBᵢ = I) and `hbs`
  (columns span Kᵢ; with `hbo` this makes them an orthonormal basis of
  Kᵢ). The stacked column index is the sigma type `(i : Fin n) × Fin (k i)`
  (k = Σᵢ kᵢ columns in total); kᵢ = 0 gives an empty block, as in (D6).
* (D7) G = BᵀB — `gramMatrix b`, the matrix of pairwise dot products of
  the stacked columns; λ_max(G) — `lambdaMax (gramMatrix b)`, where
  `lambdaMax` is the supremum of `Matrix.IsHermitian.eigenvalues`
  (Mathlib's eigenvalues via the spectral theorem). The (D7) convention
  λ_max := 0 for k = 0 holds automatically: `⨆` over an empty index type
  is 0 in ℝ (`Real.sSup_empty`).
* (D8) s = n − λ_max(G) — appears inline.
* "λ_min(S) ≥ c" — rendered as `(S − c • 1).PosSemidef` (exact for
  Hermitian S), theorem `composite_gap_posSemidef`; made literal by the
  corollaries `composite_gap_le_eigenvalues` (c ≤ every eigenvalue) and
  `composite_gap_le_iInf_eigenvalues` (c ≤ ⨅ⱼ eigenvalues = λ_min).

PROOF-ROUTE NOTE (audit honesty): the L4 Gram-transfer inequality is
proved here by a Cauchy–Schwarz argument
  (Σᵢ‖P_{Kᵢ}x‖²)² = ((Bc)ᵀx)² ≤ ‖Bc‖²‖x‖² = (cᵀGc)‖x‖²
    ≤ λ_max(G)·(Σᵢ‖P_{Kᵢ}x‖²)·‖x‖²,  c := Bᵀx,
rather than by the dossier's S4.2 ("nonzero spectra of XXᵀ and XᵀX
agree"); the statement proved, Σᵢ‖P_{Kᵢ}x‖² ≤ λ_max(G)‖x‖², is exactly
the inequality direction of L4 consumed by ST.4. L2's statement is the
dossier's S2.4 quadratic form; the splitting and assembly follow ST.4.
The dossier's Δ_w (weighted Gram defect, the primary bound's middle
term) is NOT formalised here — this file proves the commissioned
(minᵢ wᵢγᵢ)·s form end-to-end.

Status tier: FORMALISED (statement + proof, no sorry).
-/
import Mathlib
import OcfVerification.T1KernelTransversality

open Matrix BigOperators

namespace OCF

variable {d n : ℕ}

/-! ### (D4) The per-term restricted gap -/

/-- (D4) The restricted gap of a matrix: the infimum (= minimum, when
attained; it is attained for PSD `A ≠ 0` by compactness) of the quadratic
form over unit vectors orthogonal to the kernel. -/
noncomputable def restrictedGap (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  sInf ((fun x => x ⬝ᵥ A *ᵥ x) ''
    {x | x ⬝ᵥ x = 1 ∧ ∀ y ∈ matKer A, y ⬝ᵥ x = 0})

lemma restrictedGap_nonneg {A : Matrix (Fin d) (Fin d) ℝ}
    (hA : A.PosSemidef) : 0 ≤ restrictedGap A := by
  apply Real.sInf_nonneg
  rintro r ⟨x, -, rfl⟩
  have h := hA.dotProduct_mulVec_nonneg x
  rwa [star_trivial] at h

/-- The defining lower-bound property of (D4): the restricted gap is at
most the Rayleigh value of any unit vector orthogonal to the kernel. -/
lemma restrictedGap_le {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.PosSemidef)
    {v : Fin d → ℝ} (hv1 : v ⬝ᵥ v = 1) (hv2 : ∀ y ∈ matKer A, y ⬝ᵥ v = 0) :
    restrictedGap A ≤ v ⬝ᵥ A *ᵥ v := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨x, -, rfl⟩
    have h := hA.dotProduct_mulVec_nonneg x
    rwa [star_trivial] at h
  · exact ⟨v, ⟨hv1, hv2⟩, rfl⟩

/-! ### λ_max of a symmetric matrix (D7 convention for the empty case) -/

/-- The largest eigenvalue of a Hermitian real matrix (0 by convention
otherwise, and 0 when the index type is empty — the (D7) k = 0
convention, automatic since `⨆` over an empty type is 0 in ℝ). -/
noncomputable def lambdaMax {m : Type*} [Fintype m] [DecidableEq m]
    (A : Matrix m m ℝ) : ℝ :=
  if h : A.IsHermitian then ⨆ i, h.eigenvalues i else 0

/-- Rayleigh upper bound: the quadratic form of a Hermitian matrix is at
most λ_max times the squared norm (S3.3/S3.4's classical input, proved
via the spectral theorem through `Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg`). -/
lemma dotProduct_mulVec_le_lambdaMax {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} (hA : A.IsHermitian) (x : m → ℝ) :
    x ⬝ᵥ A *ᵥ x ≤ lambdaMax A * (x ⬝ᵥ x) := by
  have hlam : lambdaMax A = ⨆ i, hA.eigenvalues i := dif_pos hA
  have hpsd : ((lambdaMax A) • (1 : Matrix m m ℝ) - A).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨(Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub hA, ?_⟩
    intro μ hμ
    rw [show (lambdaMax A) • (1 : Matrix m m ℝ)
          = algebraMap ℝ (Matrix m m ℝ) (lambdaMax A) from
        (Algebra.algebraMap_eq_smul_one _).symm,
      ← spectrum.singleton_sub_eq] at hμ
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_sub.mp hμ
    rw [Set.mem_singleton_iff] at ha
    subst ha
    rw [hA.spectrum_real_eq_range_eigenvalues] at hc
    obtain ⟨i, rfl⟩ := hc
    have hle : hA.eigenvalues i ≤ ⨆ j, hA.eigenvalues j :=
      le_ciSup (Set.finite_range hA.eigenvalues).bddAbove i
    simp only [Set.mem_setOf_eq, sub_nonneg, hlam]
    exact hle
  have h0 := hpsd.dotProduct_mulVec_nonneg x
  rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  linarith

lemma lambdaMax_nonneg {m : Type*} [Fintype m] [DecidableEq m]
    {A : Matrix m m ℝ} (hA : A.PosSemidef) : 0 ≤ lambdaMax A := by
  rw [show lambdaMax A = ⨆ i, hA.1.eigenvalues i from dif_pos hA.1]
  exact Real.iSup_nonneg fun i => hA.eigenvalues_nonneg i

/-! ### (D6/D7) The stacked kernel Gram matrix -/

variable {k : Fin n → ℕ}

/-- (D7) The Gram matrix G = BᵀB of a stacked family of columns
`b i p` (the stacked index is the sigma type; empty blocks kᵢ = 0 are
allowed, as in (D6)). -/
def gramMatrix (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) :
    Matrix ((i : Fin n) × Fin (k i)) ((i : Fin n) × Fin (k i)) ℝ :=
  Matrix.of fun z w => b z.1 z.2 ⬝ᵥ b w.1 w.2

lemma gramMatrix_isHermitian (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) :
    (gramMatrix b).IsHermitian := by
  show (gramMatrix b)ᴴ = gramMatrix b
  ext z w
  simp [gramMatrix, Matrix.conjTranspose_apply, dotProduct_comm]

/-- The quadratic form of the Gram matrix is the squared norm of the
corresponding combination of columns (S4.1's computation, quadratic-form
version): cᵀGc = ‖Bc‖². -/
lemma dotProduct_gramMatrix_mulVec (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (c : ((i : Fin n) × Fin (k i)) → ℝ) :
    c ⬝ᵥ (gramMatrix b) *ᵥ c
      = (∑ z, c z • b z.1 z.2) ⬝ᵥ (∑ z, c z • b z.1 z.2) := by
  have hrow : ∀ z, ((gramMatrix b) *ᵥ c) z = b z.1 z.2 ⬝ᵥ (∑ w, c w • b w.1 w.2) := by
    intro z
    rw [dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul]
    simp only [Matrix.mulVec, dotProduct, gramMatrix, Matrix.of_apply]
    exact Finset.sum_congr rfl fun w _ => mul_comm _ _
  calc c ⬝ᵥ (gramMatrix b) *ᵥ c
      = ∑ z, c z * ((gramMatrix b) *ᵥ c) z := by simp [dotProduct]
    _ = ∑ z, c z * (b z.1 z.2 ⬝ᵥ (∑ w, c w • b w.1 w.2)) := by
        exact Finset.sum_congr rfl fun z _ => by rw [hrow z]
    _ = (∑ z, c z • b z.1 z.2) ⬝ᵥ (∑ w, c w • b w.1 w.2) := by
        rw [sum_dotProduct]
        exact Finset.sum_congr rfl fun z _ => by
          rw [smul_dotProduct, smul_eq_mul]

lemma gramMatrix_posSemidef (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) :
    (gramMatrix b).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨gramMatrix_isHermitian b, fun c => ?_⟩
  rw [star_trivial, dotProduct_gramMatrix_mulVec]
  simp only [dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

/-- **L4, Gram transfer (inequality direction consumed by ST.4).**
Σ over all stacked columns of ⟨bᵢₚ, x⟩² — which under orthonormality is
Σᵢ ‖P_{Kᵢ}x‖² — is at most λ_max(G)·‖x‖². Proved by Cauchy–Schwarz
(see the proof-route note in the header); orthonormality of the columns
is not needed for this inequality. -/
lemma sum_sq_dotProduct_le_lambdaMax
    (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ)) (x : Fin d → ℝ) :
    ∑ z : (i : Fin n) × Fin (k i), (b z.1 z.2 ⬝ᵥ x) ^ 2
      ≤ lambdaMax (gramMatrix b) * (x ⬝ᵥ x) := by
  set c : ((i : Fin n) × Fin (k i)) → ℝ := fun z => b z.1 z.2 ⬝ᵥ x with hc
  set v : Fin d → ℝ := ∑ z, c z • b z.1 z.2 with hv
  have hS : ∑ z : (i : Fin n) × Fin (k i), (b z.1 z.2 ⬝ᵥ x) ^ 2 = c ⬝ᵥ c := by
    simp [dotProduct, hc, pow_two]
  have hvx : v ⬝ᵥ x = c ⬝ᵥ c := by
    rw [hv, sum_dotProduct]
    simp only [smul_dotProduct, smul_eq_mul]
    simp [dotProduct, hc]
  have hvv : v ⬝ᵥ v = c ⬝ᵥ (gramMatrix b) *ᵥ c :=
    (dotProduct_gramMatrix_mulVec b c).symm
  have hCS : (v ⬝ᵥ x) ^ 2 ≤ (v ⬝ᵥ v) * (x ⬝ᵥ x) := by
    simpa [dotProduct, sq] using
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ v x
  have hRay : c ⬝ᵥ (gramMatrix b) *ᵥ c ≤ lambdaMax (gramMatrix b) * (c ⬝ᵥ c) :=
    dotProduct_mulVec_le_lambdaMax (gramMatrix_isHermitian b) c
  have hlam0 : 0 ≤ lambdaMax (gramMatrix b) :=
    lambdaMax_nonneg (gramMatrix_posSemidef b)
  have hcc0 : 0 ≤ c ⬝ᵥ c := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun z _ => mul_self_nonneg _
  have hxx0 : 0 ≤ x ⬝ᵥ x := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
  rw [hS]
  rcases hcc0.lt_or_eq with hpos | h0
  · have key : (c ⬝ᵥ c) * (c ⬝ᵥ c)
        ≤ (c ⬝ᵥ c) * (lambdaMax (gramMatrix b) * (x ⬝ᵥ x)) := by
      have h1 : (c ⬝ᵥ c) ^ 2 ≤ lambdaMax (gramMatrix b) * (c ⬝ᵥ c) * (x ⬝ᵥ x) :=
        calc (c ⬝ᵥ c) ^ 2 = (v ⬝ᵥ x) ^ 2 := by rw [hvx]
          _ ≤ (v ⬝ᵥ v) * (x ⬝ᵥ x) := hCS
          _ = (c ⬝ᵥ (gramMatrix b) *ᵥ c) * (x ⬝ᵥ x) := by rw [hvv]
          _ ≤ lambdaMax (gramMatrix b) * (c ⬝ᵥ c) * (x ⬝ᵥ x) :=
              mul_le_mul_of_nonneg_right hRay hxx0
      nlinarith [h1]
    exact le_of_mul_le_mul_left key hpos
  · rw [← h0]
    exact mul_nonneg hlam0 hxx0

/-! ### L2 machinery: residual vector and the per-term spectral minorant -/

section PerTerm

variable {A : Matrix (Fin d) (Fin d) ℝ} {κ : ℕ} {b : Fin κ → (Fin d → ℝ)}

/-- Squared norm of the residual x − Σₚ⟨bₚ,x⟩bₚ (= x − P_K x under
orthonormality): the Pythagoras/Bessel computation behind S2.4 and S5.1. -/
private lemma residual_dotProduct_self
    (hbo : ∀ p q, b p ⬝ᵥ b q = if p = q then 1 else 0) (x : Fin d → ℝ) :
    (x - ∑ p, (b p ⬝ᵥ x) • b p) ⬝ᵥ (x - ∑ p, (b p ⬝ᵥ x) • b p)
      = x ⬝ᵥ x - ∑ p, (b p ⬝ᵥ x) ^ 2 := by
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
  rw [sub_dotProduct, dotProduct_sub, dotProduct_sub, hxu, hux, huu]
  ring

/-- The residual is orthogonal to everything in the span of the columns
(hence, via `hbs`, to the kernel). -/
private lemma span_dotProduct_residual
    (hbo : ∀ p q, b p ⬝ᵥ b q = if p = q then 1 else 0) (x : Fin d → ℝ)
    {y : Fin d → ℝ} (hy : y ∈ Submodule.span ℝ (Set.range b)) :
    y ⬝ᵥ (x - ∑ p, (b p ⬝ᵥ x) • b p) = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      rw [dotProduct_sub, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul, hbo]
      simp [mul_ite, Finset.sum_ite_eq]
  | zero => simp
  | add y z hy hz ihy ihz => rw [add_dotProduct, ihy, ihz, add_zero]
  | smul a y hy ih => rw [smul_dotProduct, ih, smul_zero]

/-- **L2 (quadratic-form version, dossier S2.4).** For PSD `A` with an
orthonormal spanning family of its kernel,
γ · dist(x, K)² = γ·(‖x‖² − ‖P_K x‖²) ≤ xᵀAx. -/
lemma gap_mul_residual_le_quadForm (hA : A.PosSemidef)
    (hbo : ∀ p q, b p ⬝ᵥ b q = if p = q then 1 else 0)
    (hbs : Submodule.span ℝ (Set.range b) = matKer A) (x : Fin d → ℝ) :
    restrictedGap A * (x ⬝ᵥ x - ∑ p, (b p ⬝ᵥ x) ^ 2) ≤ x ⬝ᵥ A *ᵥ x := by
  set u : Fin d → ℝ := ∑ p, (b p ⬝ᵥ x) • b p with hu
  set v : Fin d → ℝ := x - u with hvdef
  have hvv : v ⬝ᵥ v = x ⬝ᵥ x - ∑ p, (b p ⬝ᵥ x) ^ 2 :=
    residual_dotProduct_self hbo x
  have hv2 : ∀ y ∈ matKer A, y ⬝ᵥ v = 0 := fun y hy =>
    span_dotProduct_residual hbo x (hbs ▸ hy)
  -- A kills u (columns lie in the kernel via hbs)
  have hAu : A *ᵥ u = 0 := by
    have hbker : ∀ p, A *ᵥ b p = 0 := by
      intro p
      have hmem : b p ∈ matKer A := hbs ▸ Submodule.subset_span ⟨p, rfl⟩
      simpa [Matrix.mulVecLin_apply] using hmem
    rw [hu, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [Matrix.mulVec_smul, hbker p, smul_zero]
  -- symmetry: Aᵀ = A (real Hermitian)
  have hAT : Aᵀ = A := by
    ext i j
    have h := congrFun (congrFun hA.1 i) j
    simpa [Matrix.conjTranspose_apply] using h
  -- quadratic form drops to the residual: xᵀAx = vᵀAv
  have hquad : x ⬝ᵥ A *ᵥ x = v ⬝ᵥ A *ᵥ v := by
    have hx : x = v + u := by rw [hvdef]; ring
    calc x ⬝ᵥ A *ᵥ x = (v + u) ⬝ᵥ A *ᵥ (v + u) := by rw [← hx]
      _ = v ⬝ᵥ A *ᵥ v + v ⬝ᵥ A *ᵥ u + (u ⬝ᵥ A *ᵥ v + u ⬝ᵥ A *ᵥ u) := by
          rw [Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]
      _ = v ⬝ᵥ A *ᵥ v := by
          have h1 : v ⬝ᵥ A *ᵥ u = 0 := by rw [hAu, dotProduct_zero]
          have h2 : u ⬝ᵥ A *ᵥ v = 0 := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hAT, hAu,
              zero_dotProduct]
          have h3 : u ⬝ᵥ A *ᵥ u = 0 := by rw [hAu, dotProduct_zero]
          rw [h1, h2, h3]; ring
  rcases eq_or_ne v 0 with hv0 | hv0
  · -- residual zero: LHS is γ·0
    have hres0 : x ⬝ᵥ x - ∑ p, (b p ⬝ᵥ x) ^ 2 = 0 := by
      rw [← hvv, hv0, zero_dotProduct]
    rw [hres0, mul_zero]
    have h := hA.dotProduct_mulVec_nonneg x
    rwa [star_trivial] at h
  · -- normalise the residual and apply (D4)'s lower-bound property
    have hvv0 : 0 ≤ v ⬝ᵥ v := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    have hvvpos : 0 < v ⬝ᵥ v := by
      rcases hvv0.lt_or_eq with h | h
      · exact h
      · exact absurd (dotProduct_self_eq_zero.mp h.symm) hv0
    set s : ℝ := v ⬝ᵥ v with hs
    have hsq : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hvvpos.le
    have hsqpos : 0 < Real.sqrt s := Real.sqrt_pos.mpr hvvpos
    set vu : Fin d → ℝ := (Real.sqrt s)⁻¹ • v with hvu
    have hvu1 : vu ⬝ᵥ vu = 1 := by
      rw [hvu, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul, ← hs]
      calc (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * s)
          = (Real.sqrt s * Real.sqrt s)⁻¹ * s := by rw [mul_inv]; ring
        _ = s⁻¹ * s := by rw [hsq]
        _ = 1 := inv_mul_cancel₀ hvvpos.ne'
    have hvu2 : ∀ y ∈ matKer A, y ⬝ᵥ vu = 0 := fun y hy => by
      rw [hvu, dotProduct_smul, hv2 y hy, smul_zero]
    have hgap := restrictedGap_le hA hvu1 hvu2
    have hquadu : vu ⬝ᵥ A *ᵥ vu = (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * (v ⬝ᵥ A *ᵥ v)) := by
      rw [hvu, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul,
        smul_eq_mul, smul_eq_mul]
    have hfin : restrictedGap A * s ≤ v ⬝ᵥ A *ᵥ v := by
      have h2 : restrictedGap A ≤ s⁻¹ * (v ⬝ᵥ A *ᵥ v) := by
        rw [hquadu] at hgap
        have hrw : (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * (v ⬝ᵥ A *ᵥ v))
            = s⁻¹ * (v ⬝ᵥ A *ᵥ v) := by
          calc (Real.sqrt s)⁻¹ * ((Real.sqrt s)⁻¹ * (v ⬝ᵥ A *ᵥ v))
              = (Real.sqrt s * Real.sqrt s)⁻¹ * (v ⬝ᵥ A *ᵥ v) := by
                rw [mul_inv]; ring
            _ = s⁻¹ * (v ⬝ᵥ A *ᵥ v) := by rw [hsq]
        rwa [hrw] at hgap
      calc restrictedGap A * s ≤ (s⁻¹ * (v ⬝ᵥ A *ᵥ v)) * s :=
            mul_le_mul_of_nonneg_right h2 hvvpos.le
        _ = v ⬝ᵥ A *ᵥ v := by
            rw [mul_comm (s⁻¹ * (v ⬝ᵥ A *ᵥ v)) s, ← mul_assoc,
              mul_inv_cancel₀ hvvpos.ne', one_mul]
    rw [← hvv, hquad]
    exact hfin

end PerTerm

/-! ### The theorem: T1(b), (minᵢ wᵢγᵢ)·s form -/

/-- S1.1: quadratic form of the weighted sum expands termwise (local copy;
the part-(a) file's version is `private`). -/
private lemma dotProduct_sum_smul_mulVec'
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (∑ i, w i • H i) *ᵥ x = ∑ i, w i * (x ⬝ᵥ H i *ᵥ x) := by
  rw [Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

/-- **T1(b) (composite gap, primary bound in the (minᵢ wᵢγᵢ)·s form).**
Under the dossier's standing hypotheses (H1)–(H4), with orthonormal
bases of the kernels stacked into the Gram matrix G,

  λ_min(Σᵢ wᵢHᵢ) ≥ (minᵢ wᵢγᵢ) · (n − λ_max(G)),

rendered as: the composite minus that multiple of the identity is PSD.
Proof: L2 → weight splitting (ST.4) → Gram transfer (L4) → assembly. -/
theorem composite_gap_posSemidef
    (hn : 0 < n) (_hd : 0 < d)
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (_hH4 : ∀ i, H i ≠ 0)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0)
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = matKer (H i)) :
    ((∑ i, w i • H i)
      - ((⨅ i, w i * restrictedGap (H i)) * ((n : ℝ) - lambdaMax (gramMatrix b)))
        • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  haveI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp hn
  set m : ℝ := ⨅ i, w i * restrictedGap (H i) with hm
  set g : ℝ := lambdaMax (gramMatrix b) with hg
  have hm0 : 0 ≤ m :=
    le_ciInf fun i => mul_nonneg (hw i).le (restrictedGap_nonneg (hpsd i))
  have hmle : ∀ i, m ≤ w i * restrictedGap (H i) := fun i =>
    ciInf_le (Set.finite_range _).bddBelow i
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  constructor
  · -- Hermitian
    exact (isSelfAdjoint_sum _ fun i _ =>
        (hpsd i).1.smul (IsSelfAdjoint.all (w i))).sub
      (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))
  · intro x
    rw [star_trivial]
    set t : Fin n → ℝ := fun i => ∑ p, (b i p ⬝ᵥ x) ^ 2 with ht
    -- L2 per term, scaled by wᵢ (S3.1)
    have hL2 : ∀ i, (w i * restrictedGap (H i)) * (x ⬝ᵥ x - t i)
        ≤ w i * (x ⬝ᵥ H i *ᵥ x) := by
      intro i
      have h := gap_mul_residual_le_quadForm (hpsd i) (hbo i) (hbs i) x
      calc (w i * restrictedGap (H i)) * (x ⬝ᵥ x - t i)
          = w i * (restrictedGap (H i) * (x ⬝ᵥ x - t i)) := by ring
        _ ≤ w i * (x ⬝ᵥ H i *ᵥ x) := mul_le_mul_of_nonneg_left h (hw i).le
    -- Bessel: each residual is nonnegative (S5.1's classical input)
    have hres : ∀ i, 0 ≤ x ⬝ᵥ x - t i := by
      intro i
      have h := residual_dotProduct_self (hbo i) x
      have h0 : 0 ≤ (x - ∑ p, (b i p ⬝ᵥ x) • b i p)
          ⬝ᵥ (x - ∑ p, (b i p ⬝ᵥ x) • b i p) := by
        simp only [dotProduct]
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
      rw [h] at h0
      exact h0
    -- ST.4 splitting: freeze the smallest coefficient
    have hsplit : ∀ i, m * (x ⬝ᵥ x - t i)
        ≤ (w i * restrictedGap (H i)) * (x ⬝ᵥ x - t i) := fun i =>
      mul_le_mul_of_nonneg_right (hmle i) (hres i)
    have hsum : ∑ i, m * (x ⬝ᵥ x - t i) ≤ x ⬝ᵥ (∑ i, w i • H i) *ᵥ x := by
      rw [dotProduct_sum_smul_mulVec']
      exact Finset.sum_le_sum fun i _ => (hsplit i).trans (hL2 i)
    have hsum2 : ∑ i, m * (x ⬝ᵥ x - t i)
        = m * ((n : ℝ) * (x ⬝ᵥ x) - ∑ i, t i) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    -- L4 Gram transfer: Σᵢ tᵢ ≤ λ_max(G)·‖x‖²
    have htg : ∑ i, t i ≤ g * (x ⬝ᵥ x) := by
      have h := sum_sq_dotProduct_le_lambdaMax b x
      have hsigma : ∑ z : (i : Fin n) × Fin (k i), (b z.1 z.2 ⬝ᵥ x) ^ 2
          = ∑ i, t i := by
        rw [ht, ← Finset.univ_sigma_univ, Finset.sum_sigma]
      rwa [hsigma] at h
    have hxx0 : 0 ≤ x ⬝ᵥ x := by
      simp only [dotProduct]
      exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
    -- assemble
    have hexpand : x ⬝ᵥ ((∑ i, w i • H i) - (m * ((n : ℝ) - g)) • 1) *ᵥ x
        = x ⬝ᵥ (∑ i, w i • H i) *ᵥ x - (m * ((n : ℝ) - g)) * (x ⬝ᵥ x) := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
        dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [hexpand]
    have hchain : m * ((n : ℝ) - g) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (∑ i, w i • H i) *ᵥ x := by
      calc m * ((n : ℝ) - g) * (x ⬝ᵥ x)
          = m * ((n : ℝ) * (x ⬝ᵥ x) - g * (x ⬝ᵥ x)) := by ring
        _ ≤ m * ((n : ℝ) * (x ⬝ᵥ x) - ∑ i, t i) := by
            apply mul_le_mul_of_nonneg_left _ hm0
            linarith
        _ = ∑ i, m * (x ⬝ᵥ x - t i) := hsum2.symm
        _ ≤ x ⬝ᵥ (∑ i, w i • H i) *ᵥ x := hsum
    linarith

/-- **T1(b), eigenvalue form:** every eigenvalue of the composite is at
least (minᵢ wᵢγᵢ)·(n − λ_max(G)); in particular λ_min is. -/
theorem composite_gap_le_eigenvalues
    (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (hH4 : ∀ i, H i ≠ 0)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0)
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = matKer (H i))
    (hS : (∑ i, w i • H i).IsHermitian) (j : Fin d) :
    (⨅ i, w i * restrictedGap (H i)) * ((n : ℝ) - lambdaMax (gramMatrix b))
      ≤ hS.eigenvalues j := by
  set c : ℝ := (⨅ i, w i * restrictedGap (H i))
    * ((n : ℝ) - lambdaMax (gramMatrix b)) with hc
  have hpsd' := composite_gap_posSemidef hn hd H w hw hpsd hH4 b hbo hbs
  rw [← hc] at hpsd'
  have hmem : hS.eigenvalues j ∈ spectrum ℝ (∑ i, w i • H i) := by
    rw [hS.spectrum_real_eq_range_eigenvalues]
    exact ⟨j, rfl⟩
  have hsub : hS.eigenvalues j - c
      ∈ spectrum ℝ ((∑ i, w i • H i) - algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ) c) := by
    rw [← spectrum.sub_singleton_eq]
    exact Set.sub_mem_sub hmem rfl
  have hmat : (∑ i, w i • H i) - algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ) c
      = (∑ i, w i • H i) - c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Algebra.algebraMap_eq_smul_one]
  rw [hmat] at hsub
  have hnn := (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hpsd').2 hsub
  simpa [sub_nonneg] using hnn

/-- **T1(b), λ_min form:** the commissioned display
λ_min(Σᵢ wᵢHᵢ) ≥ (minᵢ wᵢγᵢ)·(n − λ_max(G)), with λ_min written as the
minimum (`⨅`, over the nonempty finite index) of the eigenvalues. -/
theorem composite_gap_le_iInf_eigenvalues
    (hn : 0 < n) (hd : 0 < d)
    (H : Fin n → Matrix (Fin d) (Fin d) ℝ) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (hpsd : ∀ i, (H i).PosSemidef)
    (hH4 : ∀ i, H i ≠ 0)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → (Fin d → ℝ))
    (hbo : ∀ i, ∀ p q, b i p ⬝ᵥ b i q = if p = q then 1 else 0)
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = matKer (H i))
    (hS : (∑ i, w i • H i).IsHermitian) :
    (⨅ i, w i * restrictedGap (H i)) * ((n : ℝ) - lambdaMax (gramMatrix b))
      ≤ ⨅ j, hS.eigenvalues j := by
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  exact le_ciInf fun j =>
    composite_gap_le_eigenvalues hn hd H w hw hpsd hH4 b hbo hbs hS j

end OCF

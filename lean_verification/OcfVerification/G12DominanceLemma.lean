/-
G12 (atom types and typing rules) — the dominance lemma of S2.8:
"nesting is dominated by the flat sum with the right subset".

Source of truth: project_plan/done/proof_audits/G12_typing_calculus/01_derivation.md
(sha256 prefix 04bc98fa19e21ad2), S2.8 as extended in the stage-3
addendum (invariant (I2*), internal saturation and weakening), with the
definitions of S2.1–S2.7 (G2.1(a)–(e), b(T), σ_𝔈^T, Δ_w(T)) and Lemma
G1.3(b),(c); rulings in 03_adjudication.md (S1, RA-M1, RA-M2; tier call:
"FORMALISED for the dominance claim of S2.8"). New mathematics by the
stage-3 adjudicator; this file is its machine check.

STATEMENT (S2.8 *Claim*): for every sum derivation of F = Σ_{i∈S} ω_i f_i
(any bracketing; at each internal node any curvature rule (a)/(c)/(d) of
G2.1 with weakening, and as kernel attribute void or a weakening of rule
(e)'s output or of a saturation G1.3(c)(ii)/(iii)), σ_root ≤ b(T) for a
subset T ⊆ S_K that the proof constructs; in particular
σ_root ≤ max_{T⊆S_K} b(T), b(T) = Δ_w(T) + Σ_{i∉T} ω_iσ_i.

DEFINITIONAL MAP:
* ℝᵈ, d ≥ 1 — `Fin d → ℝ` with the dot product (as in the T1 files);
  `hd : 0 < d` (for d = 0, ℝᵈ = {0} and the two saturations coincide; the
  claim is about ℝᵈ, d ≥ 1).
* σ ∈ [−∞, ∞) — `WithBot ℝ`; Σ_a c_aσ_a with the §0 convention (−∞
  absorbs) — `extSum`. β plays no role in the claim and is not modelled.
* kernel attribute (K, ν), K a subspace, ν > 0 — `KAttr` with orthonormal
  columns `b` spanning K (`KAttr.K`), `KAttr.OK`; void — `none`.
  P_{K⊥} — `perpProj b` = I − Σₚ bₚbₚᵀ; ‖P_{K⊥}x‖² — `resid b x`.
* weakening (Definition G1.2) — K ⊇ K′ as `≤` of submodules, ν ≤ ν′;
  curvature weakening — `σ_v ≤ ·`.
* sum derivation — `SumDeriv ι d`: leaves are atoms `i : ι` with declared
  (σ_i, A_i) = (`σL i`, `AL i`); an internal node has children `child u`,
  weights `w u`, and its derived declaration (σ_v, A_v).
  Λ_v — `leaves`; ω^v_i — `omega` (recursion ω^v_i = Σ_u w_uω^u_i; it is
  the path product, `omega_node_of_mem`, because the Λ_u are disjoint);
  S_K — `SK` (leaves with a declared kernel attribute).
* the rules at a node — `CurvRule` ((a), (c), (d), weakening), `KernRule`
  ((e) with K = ⋂_u K_u and ν′ ≤ λ⁺(Q_v) when Q_v ≠ 0, saturations,
  weakening), Q_v — `Qnode`, λ⁺ — `lambdaPlus` (smallest nonzero
  eigenvalue, via `Matrix.IsHermitian.eigenvalues`); well-formedness
  (weights > 0, disjoint Λ_u, rules hold at every node) — `WF σL AL false`.
* Δ_w(T) — T1SharpBound's `deltaW` (Kernel Gram defect
  Σa − λ_max(A^{1/2}GA^{1/2})) of (K_i, a_i = ω_iν_i)_{i∈T}, listed by an
  enumeration e : Fin m ≃ T (`deltaWOn`); the theorem holds for EVERY
  enumeration, and in rules (d) an enumeration is existentially chosen
  (Δ_w is enumeration-independent anyway: `deltaW_isGreatest`).
  b(T) — `bFlat`; ρ_v(T) — `rho`/`rhoVal`; Q^v(T) — `Qmat`/`Qf`.

THEOREMS: `SumDeriv.dominance` (the claim), `SumDeriv.dominance_max`
(σ_root ≤ max_T b(T)), invariants `SumDeriv.invariants` (I1, I2*) and
their matrix PosSemidef forms `inv1_posSemidef`, `inv2_posSemidef`;
supporting `deltaW_isGreatest` (lem:flat-minorant(i), Δ_w = λ_min),
`exists_ker_lambdaPlus_le` (Rayleigh for λ⁺), `resid_anti` (S1.4),
`matKer_Qnode_le` (ker Q_v ⊆ ⋂K_u). EXTENSION beyond the dossier's
setting: `SumDeriv.dominance_ext` also allows Lemma G1.3(c)(i) (σ_v ≤ 0
from the rule-(e) attribute) at internal nodes.

PROOF ROUTE: as S2.8 — induction from the leaves with (I1) and (I2*) in
Loewner (quadratic-form) form, so λ_min superadditivity and
λ_min(M + rI) = λ_min(M) + r become sums of Loewner inequalities; the
final step uses Δ_w ≥ λ_min(Q(T)) (`le_deltaW_of_forall`).

Status tier: FORMALISED (statement + proof, no sorry).
-/
import Mathlib
import OcfVerification.B1pUniformGap

open Matrix BigOperators

namespace OCF.G12

variable {d : ℕ}

/-! ### Kernel attributes in coordinates -/

/-- Orthonormal columns for the dot product. -/
def OrthonormalCols {κ : ℕ} (b : Fin κ → (Fin d → ℝ)) : Prop :=
  ∀ p q, b p ⬝ᵥ b q = if p = q then 1 else 0

/-- The squared residual ‖P_{K⊥}x‖² = ‖x‖² − Σₚ⟨bₚ,x⟩². -/
def resid {κ : ℕ} (b : Fin κ → (Fin d → ℝ)) (x : Fin d → ℝ) : ℝ :=
  x ⬝ᵥ x - ∑ p, (b p ⬝ᵥ x) ^ 2

/-- The projector matrix P_{K⊥} = I − Σₚ bₚbₚᵀ. -/
noncomputable def perpProj {κ : ℕ} (b : Fin κ → (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  1 - ∑ p, vecMulVec (b p) (b p)

lemma quad_perpProj {κ : ℕ} (b : Fin κ → (Fin d → ℝ)) (x : Fin d → ℝ) :
    x ⬝ᵥ perpProj b *ᵥ x = resid b x := by
  simp only [perpProj, resid, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    Matrix.sum_mulVec, dotProduct_sum]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  simp only [vecMulVec, mulVec, dotProduct, Matrix.of_apply, sq, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-! ### Projector geometry of the residual -/

section Resid

variable {κ : ℕ} {b : Fin κ → (Fin d → ℝ)}

/-- The residual vector x − Σₚ⟨bₚ,x⟩bₚ (= P_{K⊥}x under orthonormality). -/
def residVec (b : Fin κ → (Fin d → ℝ)) (x : Fin d → ℝ) : Fin d → ℝ :=
  x - ∑ p, (b p ⬝ᵥ x) • b p

lemma dotProduct_self_nonneg' (v : Fin d → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simp only [dotProduct]
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg _

lemma residVec_dotProduct_self (hbo : OrthonormalCols b) (x : Fin d → ℝ) :
    residVec b x ⬝ᵥ residVec b x = resid b x := by
  set u : Fin d → ℝ := ∑ p, (b p ⬝ᵥ x) • b p with hu
  have hbu : ∀ p, b p ⬝ᵥ u = b p ⬝ᵥ x := by
    intro p
    rw [hu, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, hbo p]
    simp [mul_ite, Finset.sum_ite_eq]
  have hxu : x ⬝ᵥ u = ∑ p, (b p ⬝ᵥ x) ^ 2 := by
    rw [hu, dotProduct_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [dotProduct_smul, smul_eq_mul, dotProduct_comm x (b p), sq]
  have hux : u ⬝ᵥ x = ∑ p, (b p ⬝ᵥ x) ^ 2 := by
    rw [dotProduct_comm, hxu]
  have huu : u ⬝ᵥ u = ∑ p, (b p ⬝ᵥ x) ^ 2 := by
    conv_lhs => rw [hu, sum_dotProduct]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [smul_dotProduct, smul_eq_mul, hbu p, sq]
  rw [residVec, ← hu, sub_dotProduct, dotProduct_sub, dotProduct_sub, hxu, hux, huu, resid]
  ring

lemma resid_nonneg (hbo : OrthonormalCols b) (x : Fin d → ℝ) : 0 ≤ resid b x := by
  rw [← residVec_dotProduct_self hbo]
  exact dotProduct_self_nonneg' _

lemma resid_le_self (x : Fin d → ℝ) : resid b x ≤ x ⬝ᵥ x := by
  rw [resid, sub_le_self_iff]
  exact Finset.sum_nonneg fun p _ => sq_nonneg _

lemma span_dotProduct_residVec (hbo : OrthonormalCols b) (x : Fin d → ℝ)
    {y : Fin d → ℝ} (hy : y ∈ Submodule.span ℝ (Set.range b)) :
    y ⬝ᵥ residVec b x = 0 := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
      obtain ⟨q, rfl⟩ := hy
      rw [residVec, dotProduct_sub, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul, hbo q]
      simp [mul_ite, Finset.sum_ite_eq]
  | zero => simp
  | add y z _ _ ihy ihz => rw [add_dotProduct, ihy, ihz, add_zero]
  | smul a y _ ih => rw [smul_dotProduct, ih, smul_zero]

lemma proj_mem_span (x : Fin d → ℝ) :
    (∑ p, (b p ⬝ᵥ x) • b p) ∈ Submodule.span ℝ (Set.range b) :=
  Submodule.sum_mem _ fun p _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)

/-- The residual is the squared distance to K: ‖P_{K⊥}x‖² ≤ ‖x − y‖² for
every y ∈ K. -/
lemma resid_le_of_mem_span (hbo : OrthonormalCols b) (x : Fin d → ℝ)
    {y : Fin d → ℝ} (hy : y ∈ Submodule.span ℝ (Set.range b)) :
    resid b x ≤ (x - y) ⬝ᵥ (x - y) := by
  set u : Fin d → ℝ := ∑ p, (b p ⬝ᵥ x) • b p with hu
  set r := residVec b x with hr
  have hz : u - y ∈ Submodule.span ℝ (Set.range b) := Submodule.sub_mem _ (proj_mem_span x) hy
  have hrz : (u - y) ⬝ᵥ r = 0 := span_dotProduct_residVec hbo x hz
  have hxy : x - y = r + (u - y) := by rw [hr, residVec, ← hu]; abel
  rw [← residVec_dotProduct_self hbo, ← hr, hxy, add_dotProduct, dotProduct_add,
    dotProduct_add, hrz, dotProduct_comm r (u - y), hrz]
  linarith [dotProduct_self_nonneg' (u - y)]

/-- A vector with zero residual lies in K. -/
lemma mem_span_of_resid_eq_zero (hbo : OrthonormalCols b) {x : Fin d → ℝ}
    (h : resid b x = 0) : x ∈ Submodule.span ℝ (Set.range b) := by
  have h0 : residVec b x = 0 := by
    rw [← residVec_dotProduct_self hbo] at h
    exact dotProduct_self_eq_zero.mp h
  have hx : x = ∑ p, (b p ⬝ᵥ x) • b p := by
    rw [residVec, sub_eq_zero] at h0
    exact h0
  rw [hx]
  exact proj_mem_span x

/-- **Weakening of the kernel component (S1.4), Loewner form.** If
K ⊇ K′ (as spans of orthonormal columns), then ‖P_{K⊥}x‖² ≤ ‖P_{K′⊥}x‖². -/
lemma resid_anti {κ' : ℕ} {b' : Fin κ' → (Fin d → ℝ)} (hbo : OrthonormalCols b)
    (hbo' : OrthonormalCols b')
    (hle : Submodule.span ℝ (Set.range b') ≤ Submodule.span ℝ (Set.range b))
    (x : Fin d → ℝ) : resid b x ≤ resid b' x := by
  rw [← residVec_dotProduct_self hbo']
  have h := resid_le_of_mem_span hbo x (hle (proj_mem_span (b := b') x))
  simpa [residVec] using h

end Resid

/-! ### λ⁺ (smallest nonzero eigenvalue) and its Rayleigh bound -/

/-- λ⁺(Q): the smallest nonzero eigenvalue of a Hermitian matrix (the
dossier's §0 notation, for nonzero PSD Q). `sInf` of the finite set of
nonzero eigenvalues; 0 by convention when there is none, or when Q is not
Hermitian (never used in those cases). -/
noncomputable def lambdaPlus (Q : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : Q.IsHermitian then sInf {μ | ∃ j, h.eigenvalues j = μ ∧ μ ≠ 0} else 0

/-- **Rayleigh bound for λ⁺ (spectral decomposition, Boyd–Vandenberghe §A.5.2).**
For Hermitian Q and every x there is y ∈ ker Q with
λ⁺(Q)·‖x − y‖² ≤ xᵀQx. -/
lemma exists_ker_lambdaPlus_le {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsHermitian)
    (x : Fin d → ℝ) :
    ∃ y ∈ matKer Q, lambdaPlus Q * ((x - y) ⬝ᵥ (x - y)) ≤ x ⬝ᵥ Q *ᵥ x := by
  classical
  set E : Fin d → (Fin d → ℝ) := fun j => ⇑(hQ.eigenvectorBasis j) with hE
  set lam := hQ.eigenvalues with hlam
  have hEo : ∀ i j, E i ⬝ᵥ E j = if i = j then 1 else 0 := fun i j =>
    OCF.ofLp_dotProduct_of_orthonormal hQ.eigenvectorBasis.orthonormal i j
  set c : Fin d → ℝ := fun j => E j ⬝ᵥ x with hc
  have hexp : x = ∑ j, c j • E j := by
    have h := hQ.eigenvectorBasis.sum_repr' (WithLp.toLp 2 x)
    have h2 := congrArg WithLp.ofLp h
    simp only [WithLp.ofLp_sum, WithLp.ofLp_smul] at h2
    conv_lhs => rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [OCF.inner_eq_ofLp_dotProduct, WithLp.ofLp_toLp]
  have hQE : ∀ j, Q *ᵥ E j = lam j • E j := fun j => hQ.mulVec_eigenvectorBasis j
  -- ‖Σ gⱼEⱼ‖² = Σ gⱼ²
  have hnorm : ∀ g : Fin d → ℝ, (∑ j, g j • E j) ⬝ᵥ (∑ j, g j • E j) = ∑ j, g j ^ 2 := by
    intro g
    rw [sum_dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_dotProduct, dotProduct_sum]
    simp only [dotProduct_smul, smul_eq_mul, hEo i]
    simp [mul_ite, Finset.sum_ite_eq, sq]
  have hQx : x ⬝ᵥ Q *ᵥ x = ∑ j, lam j * c j ^ 2 := by
    conv_lhs => rw [hexp]
    rw [Matrix.mulVec_sum, dotProduct_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_smul, hQE j, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : (∑ j, c j • E j) ⬝ᵥ E j = c j := by
      rw [← hexp, dotProduct_comm]
    rw [this]
    ring
  set g : Fin d → ℝ := fun j => if lam j = 0 then 0 else c j with hg
  set y : Fin d → ℝ := ∑ j, (if lam j = 0 then c j else 0) • E j with hy
  have hyker : y ∈ matKer Q := by
    show Q.mulVecLin y = 0
    rw [Matrix.mulVecLin_apply, hy, Matrix.mulVec_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Matrix.mulVec_smul, hQE j]
    by_cases h : lam j = 0
    · rw [h, zero_smul, smul_zero]
    · rw [if_neg h, zero_smul]
  have hxy : x - y = ∑ j, g j • E j := by
    conv_lhs => rw [hexp]
    rw [hy, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul]
    congr 1
    by_cases h : lam j = 0 <;> simp [hg, h]
  refine ⟨y, hyker, ?_⟩
  rw [hxy, hnorm, hQx, Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  by_cases h : lam j = 0
  · simp [hg, h]
  · have hle : lambdaPlus Q ≤ lam j := by
      rw [lambdaPlus, dif_pos hQ]
      apply csInf_le
      · exact ((Set.finite_range hQ.eigenvalues).subset
          (by rintro μ ⟨i, rfl, -⟩; exact ⟨i, rfl⟩)).bddBelow
      · exact ⟨j, rfl, h⟩
    simp only [hg, if_neg h]
    exact mul_le_mul_of_nonneg_right hle (sq_nonneg _)

/-! ### lem:flat-minorant(i), the direction λ_min(Σ aᵢP_{Kᵢ⊥}) ≤ Δ_w -/

/-- **Δ_w dominates every Loewner lower bound of the flat minorant.** If
c·I ⪯ Σⱼ aⱼP_{Kⱼ⊥} (quadratic-form reading) with aⱼ ≥ 0 and d ≥ 1, then
c ≤ Δ_w = Σⱼaⱼ − λ_max(A^{1/2}GA^{1/2}). Together with T1SharpBound's
`flat_minorant_ge` (Δ_w·I ⪯ Σⱼ aⱼP_{Kⱼ⊥}) this is lem:flat-minorant(i):
Δ_w = λ_min(Σⱼ aⱼP_{Kⱼ⊥}). -/
lemma le_deltaW_of_forall (hd : 0 < d) {m : ℕ} {k : Fin m → ℕ}
    (b : (j : Fin m) → Fin (k j) → (Fin d → ℝ)) {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    {c : ℝ} (h : ∀ x : Fin d → ℝ, c * (x ⬝ᵥ x) ≤ ∑ j, a j * resid (b j) x) :
    c ≤ OCF.deltaW b a := by
  set C : ℝ := ∑ j, a j - c with hC
  -- c ≤ Σ aⱼ, from a unit vector
  have hC0 : 0 ≤ C := by
    have hx := h (Pi.single ⟨0, hd⟩ 1)
    have h1 : (Pi.single ⟨0, hd⟩ 1 : Fin d → ℝ) ⬝ᵥ Pi.single ⟨0, hd⟩ 1 = 1 := by simp
    rw [h1, mul_one] at hx
    have h2 : ∑ j, a j * resid (b j) (Pi.single ⟨0, hd⟩ 1) ≤ ∑ j, a j := by
      refine Finset.sum_le_sum fun j _ => ?_
      have := resid_le_self (b := b j) (Pi.single ⟨0, hd⟩ 1)
      rw [h1] at this
      nlinarith [ha j]
    linarith
  have hq : ∀ y : Fin d → ℝ, ∑ z : (j : Fin m) × Fin (k j),
      ((Real.sqrt (a z.1) • b z.1 z.2) ⬝ᵥ y) ^ 2 ≤ C * (y ⬝ᵥ y) := by
    intro y
    rw [OCF.sum_sq_scaled_eq ha b y]
    have hy := h y
    have hexp : ∑ j, a j * resid (b j) y
        = (∑ j, a j) * (y ⬝ᵥ y) - ∑ j, a j * ∑ p, (b j p ⬝ᵥ y) ^ 2 := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by rw [resid]; ring
    rw [hexp] at hy
    rw [hC]
    linarith
  have hlam : OCF.lambdaMax (OCF.weightedGram b a) ≤ C := by
    rw [OCF.weightedGram_eq_gramMatrix_scaled]
    exact OCF.lambdaMax_gramMatrix_le _ hC0 hq
  rw [OCF.deltaW]
  linarith

/-- **lem:flat-minorant(i) in Loewner reading:** Δ_w is the greatest c with
c·I ⪯ Σⱼ aⱼP_{Kⱼ⊥}, i.e. Δ_w = λ_min(Σⱼ aⱼP_{Kⱼ⊥}) (d ≥ 1, aⱼ ≥ 0). In
particular Δ_w(T) does not depend on how T is enumerated. -/
theorem deltaW_isGreatest (hd : 0 < d) {m : ℕ} {k : Fin m → ℕ}
    (b : (j : Fin m) → Fin (k j) → (Fin d → ℝ)) {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) :
    IsGreatest {c : ℝ | ∀ x : Fin d → ℝ, c * (x ⬝ᵥ x) ≤ ∑ j, a j * resid (b j) x}
      (OCF.deltaW b a) :=
  ⟨fun x => by simpa [resid] using OCF.flat_minorant_ge ha b x,
    fun _ hc => le_deltaW_of_forall hd b ha hc⟩

/-! ### Declared curvature constants in [−∞, ∞) and their positive sums -/

/-- Σ_{a∈s} c_a·σ_a in [−∞, ∞) = `WithBot ℝ`, with the dossier's §0
convention: −∞ if some σ_a = −∞ (a ∈ s), otherwise the real sum. -/
noncomputable def extSum {α : Type*} (s : Finset α) (c : α → ℝ) (σ : α → WithBot ℝ) :
    WithBot ℝ := by
  classical
  exact if ∀ a ∈ s, σ a ≠ ⊥ then ((∑ a ∈ s, c a * (σ a).unbotD 0 : ℝ) : WithBot ℝ) else ⊥

lemma extSum_of_fin {α : Type*} {s : Finset α} {c : α → ℝ} {σ : α → WithBot ℝ}
    (h : ∀ a ∈ s, σ a ≠ ⊥) :
    extSum s c σ = ((∑ a ∈ s, c a * (σ a).unbotD 0 : ℝ) : WithBot ℝ) := by
  classical
  simp only [extSum, if_pos h]

lemma extSum_fin_of_ne_bot {α : Type*} {s : Finset α} {c : α → ℝ} {σ : α → WithBot ℝ}
    (h : extSum s c σ ≠ ⊥) : ∀ a ∈ s, σ a ≠ ⊥ := by
  classical
  by_contra hc
  exact h (by simp only [extSum, if_neg hc])

/-! ### Declarations: kernel attributes -/

/-- A kernel attribute (K, ν), with K given by orthonormal columns `b`
(K = span b; every subspace has such a basis). -/
structure KAttr (d : ℕ) where
  k : ℕ
  b : Fin k → (Fin d → ℝ)
  ν : ℝ

/-- The subspace K of a kernel attribute. -/
def KAttr.K (A : KAttr d) : Submodule ℝ (Fin d → ℝ) := Submodule.span ℝ (Set.range A.b)

/-- Well-formedness of a kernel attribute (S1.1: K a subspace — given by
orthonormal columns — and ν > 0). -/
def KAttr.OK (A : KAttr d) : Prop := OrthonormalCols A.b ∧ 0 < A.ν

/-- Well-formedness of an optional (void = `none`) kernel attribute. -/
def AttrOK : Option (KAttr d) → Prop
  | none => True
  | some A => A.OK

/-- Placeholder for void (never read on a kernel-carrying position). -/
def KAttr.zero : KAttr d := ⟨0, fun p => p.elim0, 0⟩

/-- The attribute of a position, with a dummy value for void. -/
def kz (o : Option (KAttr d)) : KAttr d := o.getD KAttr.zero

lemma kz_some (A : KAttr d) : kz (some A) = A := rfl

lemma eq_some_kz {o : Option (KAttr d)} (h : o.isSome) : o = some (kz o) := by
  cases o with
  | none => simp at h
  | some A => rfl

lemma kz_nu_nonneg {o : Option (KAttr d)} (h : AttrOK o) : 0 ≤ (kz o).ν := by
  cases o with
  | none => exact le_rfl
  | some A => exact h.2.le

lemma kz_orth {o : Option (KAttr d)} (h : AttrOK o) : OrthonormalCols (kz o).b := by
  cases o with
  | none => intro p; exact p.elim0
  | some A => exact h.1

/-! ### Sum derivations (S2.8 *Setting*) -/

/-- A sum derivation: a finite rooted tree. A leaf is an atom `i : ι`
(its declaration is read from the atom data); an internal node has `n`
children `child u` with weights `w u`, and carries the declaration
(σ_v, A_v) that the node derives. -/
inductive SumDeriv (ι : Type) (d : ℕ) where
  | leaf (i : ι)
  | node (n : ℕ) (w : Fin n → ℝ) (child : Fin n → SumDeriv ι d)
      (σ : WithBot ℝ) (A : Option (KAttr d))

namespace SumDeriv

variable {ι : Type} [DecidableEq ι]

/-- Λ_v, the leaf set of a node. -/
def leaves : SumDeriv ι d → Finset ι
  | leaf i => {i}
  | node _ _ c _ _ => Finset.univ.biUnion fun u => leaves (c u)

/-- ω^v_i, the product of the weights from v down to leaf i (0 off Λ_v);
recursively ω^{leaf i} = 𝟙_i and ω^v_i = Σ_u w_u ω^u_i, which is the path
product because the Λ_u are disjoint (`omega_node_of_mem`). -/
def omega : SumDeriv ι d → ι → ℝ
  | leaf i => fun j => if j = i then 1 else 0
  | node _ w c _ _ => fun j => ∑ u, w u * omega (c u) j

variable (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))

/-- The declared curvature constant σ_v of a node. -/
def sig : SumDeriv ι d → WithBot ℝ
  | leaf i => σL i
  | node _ _ _ σ _ => σ

/-- The declared kernel attribute of a node (`none` = void). -/
def attr : SumDeriv ι d → Option (KAttr d)
  | leaf i => AL i
  | node _ _ _ _ A => A

/-- S_K ∩ Λ_v: the leaves of v with a declared kernel attribute. -/
def SK (t : SumDeriv ι d) : Finset ι := (leaves t).filter fun i => (AL i).isSome

/-- Q^v(T) := Σ_{i∈T} ω^v_i ν_i P_{Kᵢ⊥}, as a matrix. -/
noncomputable def Qmat (t : SumDeriv ι d) (T : Finset ι) : Matrix (Fin d) (Fin d) ℝ :=
  ∑ i ∈ T, (omega t i * (kz (AL i)).ν) • perpProj (kz (AL i)).b

/-- The quadratic form of Q^v(T). -/
noncomputable def Qf (t : SumDeriv ι d) (T : Finset ι) (x : Fin d → ℝ) : ℝ :=
  ∑ i ∈ T, omega t i * (kz (AL i)).ν * resid (kz (AL i)).b x

/-- ρ_v(T) := Σ_{i∈Λ_v∖T} ω^v_i σ_i ∈ [−∞, ∞). -/
noncomputable def rho (t : SumDeriv ι d) (T : Finset ι) : WithBot ℝ :=
  extSum (leaves t \ T) (omega t) σL

/-- The real value of ρ_v(T) when it is finite. -/
noncomputable def rhoVal (t : SumDeriv ι d) (T : Finset ι) : ℝ :=
  ∑ i ∈ leaves t \ T, omega t i * (σL i).unbotD 0

/-- Δ_w(T) for the flat sum at v, computed (T1SharpBound's `deltaW`) from
(K_i, a_i = ω^v_iν_i)_{i∈T} listed by an enumeration e of T. -/
noncomputable def deltaWOn (t : SumDeriv ι d) (T : Finset ι) {m : ℕ} (e : Fin m ≃ T) : ℝ :=
  OCF.deltaW (k := fun j => (kz (AL (e j))).k) (fun j => (kz (AL (e j))).b)
    (fun j => omega t (e j) * (kz (AL (e j))).ν)

/-- **The flat subset bound** b(T) := Δ_w(T) + Σ_{i∈Λ∖T} ω_iσ_i
(G2.1(d)), in [−∞, ∞). -/
noncomputable def bFlat (t : SumDeriv ι d) (T : Finset ι) {m : ℕ} (e : Fin m ≃ T) :
    WithBot ℝ :=
  ((deltaWOn AL t T e : ℝ) : WithBot ℝ) + rho σL t T

end SumDeriv

/-! ### The rules at an internal node (S2.8 *Setting*) -/

section Rules

variable {n : ℕ}

/-- Q_v := Σ_u w_uν_uP_{K_u⊥} (rule (e)). -/
noncomputable def Qnode (w : Fin n → ℝ) (cA : Fin n → Option (KAttr d)) :
    Matrix (Fin d) (Fin d) ℝ :=
  ∑ u, (w u * (kz (cA u)).ν) • perpProj (kz (cA u)).b

/-- Δ_w of the children listed by e : Fin m ≃ U, a_u = w_uν_u. -/
noncomputable def deltaWChildren (w : Fin n → ℝ) (cA : Fin n → Option (KAttr d))
    (U : Finset (Fin n)) {m : ℕ} (e : Fin m ≃ U) : ℝ :=
  OCF.deltaW (k := fun j => (kz (cA (e j))).k) (fun j => (kz (cA (e j))).b)
    (fun j => w (e j) * (kz (cA (e j))).ν)

/-- **Curvature rules at v** (S2.8 *Setting*, "Curvature"): σ_v is
(a) σ̂_S of the children, or (c) max{σ̂_S, Δ} when every child carries a
kernel attribute, or (d) σ_𝔈^{T_v} = max{σ̂_S, b(T_v)} for a subset T_v
of the kernel-carrying children — or any weakening (σ_v ≤ ·) of one of
these (Lemma G1.3(b)). In (c), Δ is Δ_w of all children listed in their
order; in (d), Δ_w(T_v) is computed from some enumeration of T_v. -/
def CurvRule (w : Fin n → ℝ) (cσ : Fin n → WithBot ℝ) (cA : Fin n → Option (KAttr d))
    (σv : WithBot ℝ) : Prop :=
  -- (a)
  σv ≤ extSum Finset.univ w cσ ∨
  -- (c)
  ((∀ u, (cA u).isSome) ∧
    σv ≤ max (extSum Finset.univ w cσ)
      ((OCF.deltaW (k := fun u => (kz (cA u)).k) (fun u => (kz (cA u)).b)
        (fun u => w u * (kz (cA u)).ν) : ℝ) : WithBot ℝ)) ∨
  -- (d)
  (∃ U : Finset (Fin n), (∀ u ∈ U, (cA u).isSome) ∧ ∃ (m : ℕ) (e : Fin m ≃ U),
    σv ≤ max (extSum Finset.univ w cσ)
      (((deltaWChildren w cA U e : ℝ) : WithBot ℝ) + extSum (Finset.univ \ U) w cσ))

/-- The curvature rules, optionally (`ext = true`) extended by Lemma
G1.3(c)(i) applied to the rule-(e) attribute at v: C(F_v, 0), i.e. σ_v ≤ 0
when every child carries a kernel attribute. The dossier's S2.8 setting is
`ext = false`. -/
def CurvRule' (ext : Bool) (w : Fin n → ℝ) (cσ : Fin n → WithBot ℝ)
    (cA : Fin n → Option (KAttr d)) (σv : WithBot ℝ) : Prop :=
  CurvRule w cσ cA σv ∨ (ext = true ∧ (∀ u, (cA u).isSome) ∧ σv ≤ 0)

/-- **Kernel-attribute rules at v** (S2.8 *Setting*, "Kernel attribute"):
void, or a weakening (K ⊇ K′, ν ≤ ν′; Definition G1.2) of one of
* the output (⋂_u K_u, ν′) of rule (e), every child carrying an attribute,
  ν′ > 0 and ν′ ≤ λ⁺(Q_v) when Q_v ≠ 0 (G2.1(e));
* the saturation ({0}, ν′) with ν′ ≤ σ_v, σ_v > 0 (Lemma G1.3(c)(iii));
* the saturation (ℝᵈ, ν′), ν′ > 0, σ_v ≥ 0 (Lemma G1.3(c)(ii)). -/
def KernRule (w : Fin n → ℝ) (cA : Fin n → Option (KAttr d)) (σv : WithBot ℝ) :
    Option (KAttr d) → Prop
  | none => True
  | some A =>
    ((∀ u, (cA u).isSome) ∧ ∃ ν' : ℝ, 0 < ν' ∧
        (Qnode w cA ≠ 0 → ν' ≤ lambdaPlus (Qnode w cA)) ∧
        (⨅ u, (kz (cA u)).K) ≤ A.K ∧ A.ν ≤ ν') ∨
    (∃ ν' : ℝ, 0 < ν' ∧ (0 : WithBot ℝ) < σv ∧ (ν' : WithBot ℝ) ≤ σv ∧
        (⊥ : Submodule ℝ (Fin d → ℝ)) ≤ A.K ∧ A.ν ≤ ν') ∨
    (∃ ν' : ℝ, 0 < ν' ∧ (0 : WithBot ℝ) ≤ σv ∧
        (⊤ : Submodule ℝ (Fin d → ℝ)) ≤ A.K ∧ A.ν ≤ ν')

end Rules

namespace SumDeriv

variable {ι : Type} [DecidableEq ι]
variable (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))

/-- **Well-formed sum derivation.** At every internal node: positive
weights, pairwise disjoint children's leaf sets (each atom is one leaf),
a well-formed own attribute, and the node's declaration obtained by the
rules from its children's declarations. -/
def WF (ext : Bool) : SumDeriv ι d → Prop
  | leaf _ => True
  | node _ w c σv Av =>
      (∀ u, 0 < w u) ∧
      (∀ u u', u ≠ u' → Disjoint (leaves (c u)) (leaves (c u'))) ∧
      AttrOK Av ∧
      CurvRule' ext w (fun u => sig σL (c u)) (fun u => attr AL (c u)) σv ∧
      KernRule w (fun u => attr AL (c u)) σv Av ∧
      ∀ u, WF ext (c u)

end SumDeriv

/-! ### Structural lemmas -/

namespace SumDeriv

variable {ι : Type} [DecidableEq ι]

lemma omega_eq_zero_of_not_mem : ∀ (t : SumDeriv ι d) {i : ι}, i ∉ leaves t → omega t i = 0
  | leaf j, i, h => by
      simp only [leaves, Finset.mem_singleton] at h
      simp [omega, h]
  | node _ w c _ _, i, h => by
      simp only [leaves, Finset.mem_biUnion, Finset.mem_univ, true_and, not_exists] at h
      simp only [omega]
      exact Finset.sum_eq_zero fun u _ => by
        rw [omega_eq_zero_of_not_mem (c u) (h u), mul_zero]

variable (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))

lemma omega_nonneg {ext : Bool} : ∀ (t : SumDeriv ι d), WF σL AL ext t → ∀ i, 0 ≤ omega t i
  | leaf j, _, i => by simp only [omega]; split_ifs <;> norm_num
  | node _ w c _ _, h, i => by
      simp only [omega]
      exact Finset.sum_nonneg fun u _ =>
        mul_nonneg (h.1 u).le (omega_nonneg (c u) (h.2.2.2.2.2 u) i)

/-- ω is the path product: ω^{node}_i = w_u ω^u_i for i ∈ Λ_u. -/
lemma omega_node_of_mem {n : ℕ} {w : Fin n → ℝ} {c : Fin n → SumDeriv ι d} {σv : WithBot ℝ}
    {Av : Option (KAttr d)}
    (hdisj : ∀ u u', u ≠ u' → Disjoint (leaves (c u)) (leaves (c u')))
    {u : Fin n} {i : ι} (hi : i ∈ leaves (c u)) :
    omega (node n w c σv Av) i = w u * omega (c u) i := by
  simp only [omega]
  rw [Finset.sum_eq_single u]
  · intro u' _ hu'
    have : i ∉ leaves (c u') := fun h' =>
      Finset.disjoint_left.mp (hdisj u' u hu') h' hi
    rw [omega_eq_zero_of_not_mem _ this, mul_zero]
  · simp

lemma omega_leaf_self (i : ι) : omega (leaf i : SumDeriv ι d) i = 1 := by
  simp [omega]

end SumDeriv

/-! ### Facts about Q_v -/

section QnodeFacts

variable {n : ℕ}

lemma perpProj_isHermitian {κ : ℕ} (b : Fin κ → (Fin d → ℝ)) : (perpProj b).IsHermitian := by
  unfold perpProj
  refine Matrix.isHermitian_one.sub ?_
  have h : ∀ p, IsSelfAdjoint (vecMulVec (b p) (b p)) := by
    intro p
    show (vecMulVec (b p) (b p))ᴴ = vecMulVec (b p) (b p)
    rw [Matrix.conjTranspose_vecMulVec]
    simp
  exact isSelfAdjoint_sum (Finset.univ : Finset (Fin κ)) fun p _ => h p

lemma Qnode_isHermitian (w : Fin n → ℝ) (cA : Fin n → Option (KAttr d)) :
    (Qnode w cA).IsHermitian := by
  have h : ∀ u, IsSelfAdjoint ((w u * (kz (cA u)).ν) • perpProj (kz (cA u)).b) := fun u =>
    (perpProj_isHermitian _).smul (IsSelfAdjoint.all _)
  exact isSelfAdjoint_sum (Finset.univ : Finset (Fin n)) fun u _ => h u

lemma quad_Qnode (w : Fin n → ℝ) (cA : Fin n → Option (KAttr d)) (x : Fin d → ℝ) :
    x ⬝ᵥ Qnode w cA *ᵥ x = ∑ u, w u * (kz (cA u)).ν * resid (kz (cA u)).b x := by
  rw [Qnode, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quad_perpProj]

/-- ker Q_v ⊆ ⋂_u K_u (thm:composite-gap(a), the inclusion consumed). -/
lemma matKer_Qnode_le {w : Fin n → ℝ} (hw : ∀ u, 0 < w u) {cA : Fin n → Option (KAttr d)}
    (hA : ∀ u, AttrOK (cA u)) (hcar : ∀ u, (cA u).isSome) :
    OCF.matKer (Qnode w cA) ≤ ⨅ u, (kz (cA u)).K := by
  intro x hx
  have hQx : Qnode w cA *ᵥ x = 0 := by simpa [Matrix.mulVecLin_apply] using hx
  have h0 : ∑ u, w u * (kz (cA u)).ν * resid (kz (cA u)).b x = 0 := by
    rw [← quad_Qnode, hQx, dotProduct_zero]
  have hnn : ∀ u ∈ Finset.univ, 0 ≤ w u * (kz (cA u)).ν * resid (kz (cA u)).b x :=
    fun u _ => mul_nonneg (mul_nonneg (hw u).le (kz_nu_nonneg (hA u)))
      (resid_nonneg (kz_orth (hA u)) x)
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
  rw [Submodule.mem_iInf]
  intro u
  have hu := h0 u (Finset.mem_univ u)
  have hpos : 0 < w u * (kz (cA u)).ν := by
    have hs := eq_some_kz (hcar u)
    have hok := hA u
    rw [hs] at hok
    exact mul_pos (hw u) hok.2
  have hr : resid (kz (cA u)).b x = 0 := by
    rcases mul_eq_zero.mp hu with h | h
    · exact absurd h hpos.ne'
    · exact h
  exact mem_span_of_resid_eq_zero (kz_orth (hA u)) hr

end QnodeFacts

/-! ### Reduction of the curvature rules to one shape (S2.8, step for (I1), first sentence) -/

section Reduce

variable {n : ℕ}

/-- Every curvature-rule choice has the form
σ_v ≤ D + Σ_{u∉U} w_uσ_u with D·I ⪯ Σ_{u∈U} w_uν_uP_{K_u⊥}, for a set U
of kernel-carrying children ("a maximum is bounded through the entry that
attains it"; Δ_w ≤ λ_min by T1SharpBound's `flat_minorant_ge`). -/
lemma curv_reduce {ext : Bool} {w : Fin n → ℝ} (hw : ∀ u, 0 < w u)
    {cσ : Fin n → WithBot ℝ} {cA : Fin n → Option (KAttr d)} (hA : ∀ u, AttrOK (cA u))
    {σv : WithBot ℝ} (h : CurvRule' ext w cσ cA σv) :
    ∃ U : Finset (Fin n), (∀ u ∈ U, (cA u).isSome) ∧ ∃ D : ℝ,
      (∀ x : Fin d → ℝ, D * (x ⬝ᵥ x) ≤ ∑ u ∈ U, w u * (kz (cA u)).ν * resid (kz (cA u)).b x) ∧
      σv ≤ (D : WithBot ℝ) + extSum (Finset.univ \ U) w cσ := by
  have ha : ∀ u, 0 ≤ w u * (kz (cA u)).ν := fun u => mul_nonneg (hw u).le (kz_nu_nonneg (hA u))
  have hextEmpty : extSum (∅ : Finset (Fin n)) w cσ = ((0 : ℝ) : WithBot ℝ) := by
    rw [extSum_of_fin (by simp)]; simp
  -- the (a) shape: U = ∅, D = 0
  have caseA : σv ≤ extSum Finset.univ w cσ → ∃ U : Finset (Fin n), (∀ u ∈ U, (cA u).isSome) ∧
      ∃ D : ℝ, (∀ x : Fin d → ℝ, D * (x ⬝ᵥ x) ≤
        ∑ u ∈ U, w u * (kz (cA u)).ν * resid (kz (cA u)).b x) ∧
      σv ≤ (D : WithBot ℝ) + extSum (Finset.univ \ U) w cσ := by
    intro h0
    refine ⟨∅, by simp, 0, fun x => by simp, ?_⟩
    simpa using h0
  rcases h with (h | h | ⟨U, hU, m, e, h⟩) | ⟨-, hcar, h⟩
  · exact caseA h
  · obtain ⟨hcar, h⟩ := h
    rcases le_max_iff.mp h with h | h
    · exact caseA h
    · refine ⟨Finset.univ, fun u _ => hcar u, OCF.deltaW (k := fun u => (kz (cA u)).k)
        (fun u => (kz (cA u)).b) (fun u => w u * (kz (cA u)).ν), fun x => ?_, ?_⟩
      · have := OCF.flat_minorant_ge (k := fun u => (kz (cA u)).k) ha
          (fun u => (kz (cA u)).b) x
        simpa [resid] using this
      · rw [Finset.sdiff_self, hextEmpty, ← WithBot.coe_add, add_zero]
        exact h
  · rcases le_max_iff.mp h with h | h
    · exact caseA h
    · refine ⟨U, hU, deltaWChildren w cA U e, fun x => ?_, h⟩
      have := OCF.flat_minorant_ge (k := fun j => (kz (cA (e j))).k)
        (fun j => ha (e j)) (fun j => (kz (cA (e j))).b) x
      have hre : ∑ j, w (e j) * (kz (cA (e j))).ν *
            (x ⬝ᵥ x - ∑ p, ((kz (cA (e j))).b p ⬝ᵥ x) ^ 2)
          = ∑ u ∈ U, w u * (kz (cA u)).ν * resid (kz (cA u)).b x := by
        rw [Equiv.sum_comp e (fun v : U => w v * (kz (cA v)).ν *
            (x ⬝ᵥ x - ∑ p, ((kz (cA v)).b p ⬝ᵥ x) ^ 2))]
        rw [Finset.sum_coe_sort U (fun v => w v * (kz (cA v)).ν *
            (x ⬝ᵥ x - ∑ p, ((kz (cA v)).b p ⬝ᵥ x) ^ 2))]
        rfl
      rw [← hre]
      exact this
  · refine ⟨Finset.univ, fun u _ => hcar u, 0, fun x => ?_, ?_⟩
    · rw [zero_mul]
      exact Finset.sum_nonneg fun u _ => mul_nonneg (ha u) (resid_nonneg (kz_orth (hA u)) x)
    · rw [Finset.sdiff_self, hextEmpty, ← WithBot.coe_add, add_zero]
      exact h

end Reduce

/-! ### Assembly at a node: T_v := ⋃_u T_u (S2.8, "the Λ_u are disjoint") -/

namespace SumDeriv

variable {ι : Type} [DecidableEq ι]
variable (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))

lemma SK_subset_leaves (t : SumDeriv ι d) : SK AL t ⊆ leaves t := Finset.filter_subset _ _

/-- Σ_{i∈S} ω^{node}_i g_i = Σ_u w_u Σ_{i∈S} ω^u_i g_i. -/
lemma sum_omega_node {n : ℕ} (w : Fin n → ℝ) (c : Fin n → SumDeriv ι d) (σv : WithBot ℝ)
    (Av : Option (KAttr d)) (S : Finset ι) (g : ι → ℝ) :
    ∑ i ∈ S, omega (node n w c σv Av) i * g i = ∑ u, w u * ∑ i ∈ S, omega (c u) i * g i := by
  simp only [omega, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun i _ => by ring

/-- **Assembly.** For subsets T_u ⊆ Λ_u ∩ S_K with ρ_u(T_u) finite, the
union T := ⋃_u T_u satisfies T ⊆ Λ_v ∩ S_K, ρ_v(T) finite,
ρ_v(T) = Σ_u w_uρ_u(T_u), and Q^v(T) = Σ_u w_uQ^u(T_u). -/
lemma assembly {n : ℕ} {w : Fin n → ℝ} {c : Fin n → SumDeriv ι d} {σv : WithBot ℝ}
    {Av : Option (KAttr d)}
    (hdisj : ∀ u u', u ≠ u' → Disjoint (leaves (c u)) (leaves (c u')))
    (Tsel : Fin n → Finset ι) (hsub : ∀ u, Tsel u ⊆ SK AL (c u))
    (hfin : ∀ u, ∀ i ∈ leaves (c u) \ Tsel u, σL i ≠ ⊥) :
    Finset.univ.biUnion Tsel ⊆ SK AL (node n w c σv Av) ∧
    (∀ i ∈ leaves (node n w c σv Av) \ Finset.univ.biUnion Tsel, σL i ≠ ⊥) ∧
    rhoVal σL (node n w c σv Av) (Finset.univ.biUnion Tsel)
      = ∑ u, w u * rhoVal σL (c u) (Tsel u) ∧
    ∀ x, Qf AL (node n w c σv Av) (Finset.univ.biUnion Tsel) x
      = ∑ u, w u * Qf AL (c u) (Tsel u) x := by
  set T := Finset.univ.biUnion Tsel with hT
  have hsubL : ∀ u, Tsel u ⊆ leaves (c u) := fun u => (hsub u).trans (SK_subset_leaves AL _)
  -- on Λ_u, membership in T is membership in T_u
  have key : ∀ u, ∀ i ∈ leaves (c u), (i ∈ T ↔ i ∈ Tsel u) := by
    intro u i hi
    constructor
    · intro hiT
      rw [hT, Finset.mem_biUnion] at hiT
      obtain ⟨u', -, hu'⟩ := hiT
      by_cases huu : u' = u
      · rwa [huu] at hu'
      · exact absurd hi (Finset.disjoint_left.mp (hdisj u' u huu) (hsubL u' hu'))
    · intro h
      rw [hT, Finset.mem_biUnion]
      exact ⟨u, Finset.mem_univ _, h⟩
  have hmemL : ∀ u, ∀ i ∈ leaves (c u), i ∈ leaves (node n w c σv Av) := by
    intro u i hi
    simp only [leaves, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨u, hi⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hT, Finset.mem_biUnion] at hi
    obtain ⟨u, -, hu⟩ := hi
    have h1 := hsub u hu
    simp only [SK, Finset.mem_filter] at h1 ⊢
    exact ⟨hmemL u i h1.1, h1.2⟩
  · intro i hi
    rw [Finset.mem_sdiff] at hi
    obtain ⟨hiL, hiT⟩ := hi
    simp only [leaves, Finset.mem_biUnion, Finset.mem_univ, true_and] at hiL
    obtain ⟨u, hu⟩ := hiL
    exact hfin u i (Finset.mem_sdiff.mpr ⟨hu, fun h => hiT ((key u i hu).mpr h)⟩)
  · rw [rhoVal, sum_omega_node]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [rhoVal]
    symm
    apply Finset.sum_subset
    · intro i hi
      rw [Finset.mem_sdiff] at hi ⊢
      exact ⟨hmemL u i hi.1, fun h => hi.2 ((key u i hi.1).mp h)⟩
    · intro i hi hni
      have : i ∉ leaves (c u) := by
        intro hL
        apply hni
        rw [Finset.mem_sdiff] at hi ⊢
        exact ⟨hL, fun h => hi.2 ((key u i hL).mpr h)⟩
      rw [omega_eq_zero_of_not_mem _ this, zero_mul]
  · intro x
    rw [Qf]
    simp only [mul_assoc]
    rw [sum_omega_node]
    refine Finset.sum_congr rfl fun u _ => ?_
    congr 1
    rw [Qf]
    simp only [mul_assoc]
    symm
    apply Finset.sum_subset
    · intro i hi
      rw [hT, Finset.mem_biUnion]
      exact ⟨u, Finset.mem_univ _, hi⟩
    · intro i hi hni
      have : i ∉ leaves (c u) := fun hL => hni ((key u i hL).mp hi)
      rw [omega_eq_zero_of_not_mem _ this, zero_mul]

end SumDeriv

/-! ### The two invariants and the induction (S2.8 *Proof*) -/

namespace SumDeriv

variable {ι : Type} [DecidableEq ι]
variable (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))

/-- **(I1)** σ_v ≤ b_v(T_v) for some T_v ⊆ Λ_v ∩ S_K, in Loewner form:
if σ_v = s is finite then ρ_v(T_v) is finite and
(s − ρ_v(T_v))·I ⪯ Q^v(T_v) (quadratic forms). Since λ_min(M) is the
largest c with c·I ⪯ M, this is σ_v ≤ λ_min(Q^v(T_v)) + ρ_v(T_v). -/
def Inv1 (t : SumDeriv ι d) : Prop :=
  ∃ T ⊆ SK AL t, ∀ s : ℝ, sig σL t = (s : WithBot ℝ) →
    (∀ i ∈ leaves t \ T, σL i ≠ ⊥) ∧
    ∀ x : Fin d → ℝ, (s - rhoVal σL t T) * (x ⬝ᵥ x) ≤ Qf AL t T x

/-- **(I2\*)** If v carries (K_v, ν_v), then for some T′ ⊆ Λ_v ∩ S_K with
ρ_v(T′) finite, ν_vP_{K_v⊥} ⪯ Q^v(T′) + ρ_v(T′)·I (quadratic forms). -/
def Inv2 (t : SumDeriv ι d) : Prop :=
  ∀ A : KAttr d, attr AL t = some A → ∃ T ⊆ SK AL t,
    (∀ i ∈ leaves t \ T, σL i ≠ ⊥) ∧
    ∀ x : Fin d → ℝ, A.ν * resid A.b x ≤ Qf AL t T x + rhoVal σL t T * (x ⬝ᵥ x)

/-- **Both invariants hold at every node** (induction from the leaves). -/
theorem invariants {ext : Bool} (hAL : ∀ i, AttrOK (AL i)) :
    ∀ t : SumDeriv ι d, WF σL AL ext t → Inv1 σL AL t ∧ Inv2 σL AL t
  | leaf i, _ => by
      refine ⟨⟨∅, Finset.empty_subset _, fun s hs => ⟨?_, fun x => ?_⟩⟩, ?_⟩
      · intro j hj
        simp only [leaves, Finset.sdiff_empty, Finset.mem_singleton] at hj
        subst hj
        simp only [sig] at hs
        rw [hs]; exact WithBot.coe_ne_bot
      · simp only [sig] at hs
        simp [rhoVal, Qf, leaves, omega, hs]
      · intro A hA
        simp only [attr] at hA
        refine ⟨{i}, ?_, by simp [leaves], fun x => ?_⟩
        · intro j hj
          rw [Finset.mem_singleton] at hj
          subst hj
          simp [SK, leaves, hA]
        · have hk : kz (AL i) = A := by rw [hA]; rfl
          simp [Qf, rhoVal, leaves, omega, hk]
          rw [hk]
  | node n w c σv Av, hWF => by
      obtain ⟨hw, hdisj, hAv, hcurv, hkern, hch⟩ := hWF
      have ih : ∀ u, Inv1 σL AL (c u) ∧ Inv2 σL AL (c u) := fun u =>
        invariants hAL (c u) (hch u)
      have hcA : ∀ u, AttrOK (attr AL (c u)) := by
        intro u
        cases hcu : c u with
        | leaf j => exact hAL j
        | node _ _ _ _ A' =>
            have := hch u
            rw [hcu] at this
            exact this.2.2.1
      have hxx : ∀ x : Fin d → ℝ, 0 ≤ x ⬝ᵥ x := dotProduct_self_nonneg'
      -- children's (I2*) data, for kernel-carrying children
      have child2 : ∀ u, (attr AL (c u)).isSome → ∃ T ⊆ SK AL (c u),
          (∀ i ∈ leaves (c u) \ T, σL i ≠ ⊥) ∧ ∀ x : Fin d → ℝ,
            w u * (kz (attr AL (c u))).ν * resid (kz (attr AL (c u))).b x
              ≤ w u * (Qf AL (c u) T x + rhoVal σL (c u) T * (x ⬝ᵥ x)) := by
        intro u hu
        obtain ⟨T, hT, hfin, hineq⟩ := (ih u).2 _ (eq_some_kz hu)
        exact ⟨T, hT, hfin, fun x => by
          rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (hineq x) (hw u).le⟩
      ------------------------------------------------------------------
      -- (I1) at the node
      have I1 : Inv1 σL AL (node n w c σv Av) := by
        obtain ⟨U, hUcar, D, hD, hσ⟩ := curv_reduce hw hcA hcurv
        by_cases hbot : σv = ⊥
        · refine ⟨∅, Finset.empty_subset _, fun s hs => ?_⟩
          simp only [sig] at hs
          rw [hbot] at hs
          exact absurd hs.symm WithBot.coe_ne_bot
        · obtain ⟨s0, hs0'⟩ := WithBot.ne_bot_iff_exists.mp hbot
          have hs0 : σv = (s0 : WithBot ℝ) := hs0'.symm
          -- the extended sum over u ∉ U is finite
          have hne : extSum (Finset.univ \ U) w (fun u => sig σL (c u)) ≠ ⊥ := by
            intro hb
            rw [hb, WithBot.add_bot, hs0] at hσ
            exact WithBot.coe_ne_bot (le_bot_iff.mp hσ)
          have hfinU := extSum_fin_of_ne_bot hne
          rw [extSum_of_fin hfinU, hs0, ← WithBot.coe_add, WithBot.coe_le_coe] at hσ
          -- per-child choice of T_u
          have hchoice : ∀ u, ∃ T ⊆ SK AL (c u), (∀ i ∈ leaves (c u) \ T, σL i ≠ ⊥) ∧
              ∀ x : Fin d → ℝ,
                (if u ∈ U then w u * (kz (attr AL (c u))).ν * resid (kz (attr AL (c u))).b x
                  else w u * (sig σL (c u)).unbotD 0 * (x ⬝ᵥ x))
                ≤ w u * (Qf AL (c u) T x + rhoVal σL (c u) T * (x ⬝ᵥ x)) := by
            intro u
            by_cases hu : u ∈ U
            · obtain ⟨T, hT, hfin, hineq⟩ := child2 u (hUcar u hu)
              exact ⟨T, hT, hfin, fun x => by rw [if_pos hu]; exact hineq x⟩
            · obtain ⟨T, hT, h1⟩ := (ih u).1
              have hsu : sig σL (c u) ≠ ⊥ :=
                hfinU u (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hu⟩)
              obtain ⟨su, hsu'⟩ := WithBot.ne_bot_iff_exists.mp hsu
              obtain ⟨hfin, hineq⟩ := h1 su hsu'.symm
              refine ⟨T, hT, hfin, fun x => ?_⟩
              rw [if_neg hu, ← hsu', WithBot.unbotD_coe, mul_assoc]
              apply mul_le_mul_of_nonneg_left _ (hw u).le
              have := hineq x
              linarith
          choose Tsel hTsub hTfin hTineq using hchoice
          obtain ⟨hsubT, hfinT, hrho, hQ⟩ := assembly σL AL hdisj Tsel hTsub hTfin
          refine ⟨_, hsubT, fun s hs => ?_⟩
          simp only [sig] at hs
          rw [hs0, WithBot.coe_inj] at hs
          subst hs
          refine ⟨hfinT, fun x => ?_⟩
          rw [hrho, hQ]
          -- s0‖x‖² ≤ D‖x‖² + Σ_{u∉U} w_uσ_u‖x‖² ≤ Σ_u (ite) ≤ Σ_u w_u(Q^u + ρ_u)
          have h1 : s0 * (x ⬝ᵥ x) ≤ D * (x ⬝ᵥ x) +
              (∑ u ∈ Finset.univ \ U, w u * (sig σL (c u)).unbotD 0) * (x ⬝ᵥ x) := by
            rw [← add_mul]; exact mul_le_mul_of_nonneg_right hσ (hxx x)
          have h2 : D * (x ⬝ᵥ x) +
              (∑ u ∈ Finset.univ \ U, w u * (sig σL (c u)).unbotD 0) * (x ⬝ᵥ x)
              ≤ ∑ u, (if u ∈ U then
                  w u * (kz (attr AL (c u))).ν * resid (kz (attr AL (c u))).b x
                  else w u * (sig σL (c u)).unbotD 0 * (x ⬝ᵥ x)) := by
            rw [← Finset.sum_add_sum_compl U, Finset.compl_eq_univ_sdiff, Finset.sum_mul]
            apply add_le_add
            · refine (hD x).trans (le_of_eq ?_)
              exact Finset.sum_congr rfl fun u hu => by rw [if_pos hu]
            · refine le_of_eq (Finset.sum_congr rfl fun u hu => ?_)
              rw [if_neg (Finset.mem_sdiff.mp hu).2]
          have h3 := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hTineq u x
          have h4 : ∑ u, w u * (Qf AL (c u) (Tsel u) x + rhoVal σL (c u) (Tsel u) * (x ⬝ᵥ x))
              = ∑ u, w u * Qf AL (c u) (Tsel u) x
                + (∑ u, w u * rhoVal σL (c u) (Tsel u)) * (x ⬝ᵥ x) := by
            rw [Finset.sum_mul, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun u _ => by ring
          rw [h4] at h3
          nlinarith [h1, h2, h3]
      ------------------------------------------------------------------
      -- (I2*) at the node
      refine ⟨I1, fun A hA => ?_⟩
      simp only [attr] at hA
      subst hA
      have hAok : A.OK := hAv
      rcases hkern with ⟨hcar, ν', hν', hlam, hK, hAν⟩ | ⟨ν', hν', hpos, hνσ, -, hAν⟩ |
          ⟨ν', hν', hnn, htop, hAν⟩
      · -- weakening of the output of rule (e)
        have hQbound : ∀ x : Fin d → ℝ, A.ν * resid A.b x
            ≤ x ⬝ᵥ Qnode w (fun u => attr AL (c u)) *ᵥ x := by
          intro x
          have hker := matKer_Qnode_le hw hcA hcar
          by_cases hQ0 : Qnode w (fun u => attr AL (c u)) = 0
          · have hx : x ∈ A.K := by
              apply hK
              apply hker
              show (Qnode w (fun u => attr AL (c u))).mulVecLin x = 0
              rw [hQ0]; simp
            have hr := resid_le_of_mem_span hAok.1 x hx
            rw [sub_self, zero_dotProduct] at hr
            rw [hQ0, Matrix.zero_mulVec, dotProduct_zero]
            exact mul_nonpos_of_nonneg_of_nonpos hAok.2.le hr
          · obtain ⟨y, hy, hlamy⟩ :=
              exists_ker_lambdaPlus_le (Qnode_isHermitian w (fun u => attr AL (c u))) x
            have hyK : y ∈ A.K := hK (hker hy)
            have hr := resid_le_of_mem_span hAok.1 x hyK
            have hle : A.ν ≤ lambdaPlus (Qnode w (fun u => attr AL (c u))) :=
              hAν.trans (hlam hQ0)
            calc A.ν * resid A.b x ≤ A.ν * ((x - y) ⬝ᵥ (x - y)) :=
                  mul_le_mul_of_nonneg_left hr hAok.2.le
              _ ≤ lambdaPlus (Qnode w (fun u => attr AL (c u))) * ((x - y) ⬝ᵥ (x - y)) :=
                  mul_le_mul_of_nonneg_right hle (hxx _)
              _ ≤ _ := hlamy
        choose Tsel hTsub hTfin hTineq using fun u => child2 u (hcar u)
        obtain ⟨hsubT, hfinT, hrho, hQ⟩ := assembly σL AL hdisj Tsel hTsub hTfin
        refine ⟨_, hsubT, hfinT, fun x => ?_⟩
        rw [hrho, hQ]
        have h3 := Finset.sum_le_sum fun u (_ : u ∈ Finset.univ) => hTineq u x
        have h4 : ∑ u, w u * (Qf AL (c u) (Tsel u) x + rhoVal σL (c u) (Tsel u) * (x ⬝ᵥ x))
            = ∑ u, w u * Qf AL (c u) (Tsel u) x
              + (∑ u, w u * rhoVal σL (c u) (Tsel u)) * (x ⬝ᵥ x) := by
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun u _ => by ring
        rw [h4] at h3
        have h5 := hQbound x
        rw [quad_Qnode] at h5
        linarith
      · -- weakening of the saturation ({0}, ν′), ν′ ≤ σ_v, σ_v > 0
        obtain ⟨T, hT, h1⟩ := I1
        obtain ⟨s0, hs0⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_gt hpos)
        obtain ⟨hfin, hineq⟩ := h1 s0 (by simp only [sig]; exact hs0.symm)
        refine ⟨T, hT, hfin, fun x => ?_⟩
        rw [← hs0, WithBot.coe_le_coe] at hνσ
        have hr := resid_le_self (b := A.b) x
        have := hineq x
        have e1 : A.ν * resid A.b x ≤ A.ν * (x ⬝ᵥ x) :=
          mul_le_mul_of_nonneg_left hr hAok.2.le
        have e2 : A.ν * (x ⬝ᵥ x) ≤ s0 * (x ⬝ᵥ x) :=
          mul_le_mul_of_nonneg_right (hAν.trans hνσ) (hxx x)
        nlinarith
      · -- weakening of the saturation (ℝᵈ, ν′), σ_v ≥ 0
        obtain ⟨T, hT, h1⟩ := I1
        have hne : σv ≠ ⊥ := fun h => by
          rw [h] at hnn; exact absurd hnn (by simp)
        obtain ⟨s0, hs0⟩ := WithBot.ne_bot_iff_exists.mp hne
        obtain ⟨hfin, hineq⟩ := h1 s0 (by simp only [sig]; exact hs0.symm)
        refine ⟨T, hT, hfin, fun x => ?_⟩
        rw [← hs0] at hnn
        have hs0nn : 0 ≤ s0 := by exact_mod_cast hnn
        have hx : x ∈ A.K := htop Submodule.mem_top
        have hr := resid_le_of_mem_span hAok.1 x hx
        rw [sub_self, zero_dotProduct] at hr
        have := hineq x
        have e1 : A.ν * resid A.b x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hAok.2.le hr
        have e2 : 0 ≤ s0 * (x ⬝ᵥ x) := mul_nonneg hs0nn (hxx x)
        linarith

end SumDeriv

/-! ### The dominance lemma (S2.8 *Claim*) -/

namespace SumDeriv

variable {ι : Type} [DecidableEq ι]

/-- **S2.8, dominance of nesting by the flat subset bound (general form).**
For every well-formed sum derivation t (any bracketing; at each node any
of the curvature rules (a)/(c)/(d) with weakening, and the kernel
attribute void, or a weakening of rule (e)'s output or of a saturation;
with `ext = true` also Lemma G1.3(c)(i) at nodes), there is a subset
T ⊆ S_K of the kernel-carrying leaves such that the root's declared
curvature satisfies σ_root ≤ b(T) = Δ_w(T) + Σ_{i∉T} ω_iσ_i, with Δ_w(T)
computed from ANY enumeration of T. -/
theorem dominance_gen (hd : 0 < d) (ext : Bool) (σL : ι → WithBot ℝ)
    (AL : ι → Option (KAttr d)) (hAL : ∀ i, AttrOK (AL i))
    (t : SumDeriv ι d) (ht : WF σL AL ext t) :
    ∃ T ⊆ SK AL t, ∀ (m : ℕ) (e : Fin m ≃ T), sig σL t ≤ bFlat σL AL t T e := by
  obtain ⟨T, hT, h1⟩ := (invariants σL AL hAL t ht).1
  refine ⟨T, hT, fun m e => ?_⟩
  by_cases hbot : sig σL t = ⊥
  · rw [hbot]; exact bot_le
  obtain ⟨s, hs'⟩ := WithBot.ne_bot_iff_exists.mp hbot
  obtain ⟨hfin, hineq⟩ := h1 s hs'.symm
  rw [← hs', bFlat, rho, extSum_of_fin hfin, ← WithBot.coe_add, WithBot.coe_le_coe]
  have ha : ∀ j, 0 ≤ omega t (e j) * (kz (AL (e j))).ν := fun j =>
    mul_nonneg (omega_nonneg σL AL t ht _) (kz_nu_nonneg (hAL _))
  have key := le_deltaW_of_forall hd (k := fun j => (kz (AL (e j))).k)
    (fun j => (kz (AL (e j))).b) ha (c := s - rhoVal σL t T) (fun x => by
      have hre : ∑ j, omega t (e j) * (kz (AL (e j))).ν * resid (kz (AL (e j))).b x
          = Qf AL t T x := by
        rw [Equiv.sum_comp e (fun v : T => omega t v * (kz (AL v)).ν * resid (kz (AL v)).b x),
          Finset.sum_coe_sort T (fun v => omega t v * (kz (AL v)).ν * resid (kz (AL v)).b x)]
        rfl
      rw [hre]; exact hineq x)
  have : s - rhoVal σL t T ≤ deltaWOn AL t T e := key
  rw [rhoVal] at this
  linarith

/-- **S2.8 dominance lemma (the dossier's setting, `ext = false`).**
σ_root ≤ b(T) for a subset T ⊆ S_K that the proof constructs. -/
theorem dominance (hd : 0 < d) (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))
    (hAL : ∀ i, AttrOK (AL i)) (t : SumDeriv ι d) (ht : WF σL AL false t) :
    ∃ T ⊆ SK AL t, ∀ (m : ℕ) (e : Fin m ≃ T), sig σL t ≤ bFlat σL AL t T e :=
  dominance_gen hd false σL AL hAL t ht

/-- **S2.8, "in particular": σ_root ≤ max_{T ⊆ S_K} b(T)** (Δ_w(T) computed
with the canonical enumeration of each T). -/
theorem dominance_max (hd : 0 < d) (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))
    (hAL : ∀ i, AttrOK (AL i)) (t : SumDeriv ι d) (ht : WF σL AL false t) :
    sig σL t ≤ (SK AL t).powerset.sup fun T => bFlat σL AL t T T.equivFin.symm := by
  obtain ⟨T, hT, h⟩ := dominance hd σL AL hAL t ht
  exact (h _ T.equivFin.symm).trans
    (Finset.le_sup (f := fun T => bFlat σL AL t T T.equivFin.symm) (Finset.mem_powerset.mpr hT))

/-- **Extension** (not in the dossier's setting): the dominance lemma still
holds when Lemma G1.3(c)(i) — C(F_v, 0) from the rule-(e) kernel attribute
at v — is also allowed at internal nodes (`ext = true`). -/
theorem dominance_ext (hd : 0 < d) (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))
    (hAL : ∀ i, AttrOK (AL i)) (t : SumDeriv ι d) (ht : WF σL AL true t) :
    ∃ T ⊆ SK AL t, ∀ (m : ℕ) (e : Fin m ≃ T), sig σL t ≤ bFlat σL AL t T e :=
  dominance_gen hd true σL AL hAL t ht

/-! ### The invariants in matrix Loewner (PosSemidef) form -/

variable (σL : ι → WithBot ℝ) (AL : ι → Option (KAttr d))

lemma quad_Qmat (t : SumDeriv ι d) (T : Finset ι) (x : Fin d → ℝ) :
    x ⬝ᵥ Qmat AL t T *ᵥ x = Qf AL t T x := by
  rw [Qmat, Matrix.sum_mulVec, dotProduct_sum, Qf]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quad_perpProj]

lemma Qmat_isHermitian (t : SumDeriv ι d) (T : Finset ι) : (Qmat AL t T).IsHermitian := by
  have h : ∀ i, IsSelfAdjoint ((omega t i * (kz (AL i)).ν) • perpProj (kz (AL i)).b) :=
    fun i => (perpProj_isHermitian _).smul (IsSelfAdjoint.all _)
  exact isSelfAdjoint_sum T fun i _ => h i

/-- **(I1), matrix form.** At every node v of a well-formed derivation
there is T_v ⊆ Λ_v ∩ S_K such that, if σ_v = s is finite, ρ_v(T_v) is
finite and Q^v(T_v) − (s − ρ_v(T_v))·I is PSD. -/
theorem inv1_posSemidef {ext : Bool} (hAL : ∀ i, AttrOK (AL i)) (t : SumDeriv ι d)
    (ht : WF σL AL ext t) :
    ∃ T ⊆ SK AL t, ∀ s : ℝ, sig σL t = (s : WithBot ℝ) →
      rho σL t T = ((rhoVal σL t T : ℝ) : WithBot ℝ) ∧
      (Qmat AL t T - (s - rhoVal σL t T) • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
  obtain ⟨T, hT, h⟩ := (invariants σL AL hAL t ht).1
  refine ⟨T, hT, fun s hs => ?_⟩
  obtain ⟨hfin, hineq⟩ := h s hs
  refine ⟨extSum_of_fin hfin, ?_⟩
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨(Qmat_isHermitian AL t T).sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)),
    fun x => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub,
    dotProduct_smul, smul_eq_mul, quad_Qmat, sub_nonneg]
  exact hineq x

/-- **(I2\*), matrix form.** If v carries (K_v, ν_v), there is
T′ ⊆ Λ_v ∩ S_K with ρ_v(T′) finite and
Q^v(T′) + ρ_v(T′)·I − ν_vP_{K_v⊥} PSD. -/
theorem inv2_posSemidef {ext : Bool} (hAL : ∀ i, AttrOK (AL i)) (t : SumDeriv ι d)
    (ht : WF σL AL ext t) (A : KAttr d) (hA : attr AL t = some A) :
    ∃ T ⊆ SK AL t, rho σL t T = ((rhoVal σL t T : ℝ) : WithBot ℝ) ∧
      (Qmat AL t T + rhoVal σL t T • (1 : Matrix (Fin d) (Fin d) ℝ)
        - A.ν • perpProj A.b).PosSemidef := by
  obtain ⟨T, hT, hfin, hineq⟩ := (invariants σL AL hAL t ht).2 A hA
  refine ⟨T, hT, extSum_of_fin hfin, ?_⟩
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨((Qmat_isHermitian AL t T).add
    (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _))).sub
      ((perpProj_isHermitian _).smul (IsSelfAdjoint.all _)), fun x => ?_⟩
  rw [star_trivial, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul,
    dotProduct_smul, smul_eq_mul, smul_eq_mul, quad_Qmat, quad_perpProj, sub_nonneg]
  exact hineq x

end SumDeriv

/-! ### Non-vacuity check: a well-formed two-leaf derivation with saturation -/

namespace SumDeriv

/-- Two atoms on ℝ¹ with declared σ = 1 and σ = 2, no kernel attributes;
the node sums them with unit weights by rule (a) (σ_v = 3) and saturates
to ({0}, 3) (Lemma G1.3(c)(iii)). The `WF` predicate is satisfiable with
internal saturation, so the theorems above are not vacuous. -/
example : WF (d := 1) (fun i : Fin 2 => if i = 0 then ((1 : ℝ) : WithBot ℝ) else ((2 : ℝ) : WithBot ℝ))
    (fun _ => none) false
    (node 2 (fun _ => 1) (fun u => leaf u) ((3 : ℝ) : WithBot ℝ)
      (some ⟨0, fun p => p.elim0, 3⟩)) := by
  refine ⟨fun _ => one_pos, ?_, ⟨fun p => p.elim0, by norm_num⟩, ?_, ?_, fun _ => trivial⟩
  · intro u u' h
    simp [leaves, h]
  · left; left
    rw [extSum_of_fin (by intro a _; simp only [sig]; split_ifs <;> exact WithBot.coe_ne_bot)]
    simp [Fin.sum_univ_two, sig]
    norm_num
  · right; left
    refine ⟨3, by norm_num, by simp, le_rfl, bot_le, le_rfl⟩

end SumDeriv

end OCF.G12

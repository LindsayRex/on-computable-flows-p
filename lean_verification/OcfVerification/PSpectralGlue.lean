/-
P (Preliminaries I: spectral facts) — the novel spectral glue and the four
matrix examples of the P1 sub-unit, as queued by Decision 4 of the stage-3
adjudication.

Source of truth: project_plan/done/proof_audits/P_preliminaries/01_derivation.md
(sha256 prefix 853f3dd20ae94f1c; items P1.2, P1.3, P1.5, P1.6, P1.12, P1.13,
P1.16), as landed in 04_landing_draft_spectral.tex (Lemma
lem:signed-gershgorin, Lemma lem:certified-lmin and the examples);
rulings in 03_adjudication.md (M10: n ≥ 2 in P1.12; Decision 4).
Cited classical facts (Gershgorin = Mathlib `eigenvalue_mem_ball`; real
spectrum and A ≻ 0 ⟺ λ_min > 0 = Mathlib `IsHermitian.posDef_iff_eigenvalues_pos`;
the spectral theorem = Mathlib `IsHermitian.eigenvectorBasis`) are used, not
re-proved. Kato–Temple, inertia and Courant–Fischer are not formalised: the
certified bound is proved directly from the spectral theorem.

DEFINITIONAL MAP:
* A ∈ ℝⁿˣⁿ — `Matrix (Fin n) (Fin n) ℝ`; "symmetric" — `A.IsHermitian`
  (over ℝ, star is trivial, so this is Aᵀ = A).
* rᵢ(A) = Σ_{j≠i}|a_ij| — B6's `gershRadius` (reused, not duplicated);
  minᵢ — `⨅ i`. B6's dominance test is linked by `posDef_of_passesDominance`
  through B6 `passes_iff_signedGershgorin`.
* eigenvalues in increasing order with multiplicity λ₁ ≤ … ≤ λₙ —
  `eigAsc hA k` = Mathlib's antitone `eigenvalues₀` reversed (Mathlib's
  `sort_roots_charpoly_eq_eigenvalues₀`: the sorted charpoly roots);
  λ_min — `lamMin hA hn` (n ≥ 1), with `lamMin_eq_iInf` (= minⱼ λⱼ) and
  `lamMin_isLeast` (least element of the real spectrum); λ₂ — `lamTwo hA hn`
  (n ≥ 2).
* R_A(x) = xᵀAx/xᵀx — `rq`; r = (A − λ̃I)u — `resid`; ‖u‖₂ = 1 — `u ⬝ᵥ u = 1`
  (`certified_lmin`) or the EuclideanSpace norm (`certified_lmin_norm`);
  ‖r‖₂² — `resid A u ⬝ᵥ resid A u` (resp. the EuclideanSpace norm squared).
* A ≻ 0 — `Matrix.PosDef`.
* Examples: A = −Iₙ — `-1`; tridiag(−1,2,−1) — `dirichlet n`; the periodic
  Laplacian — `periodic n` := `dirichlet n` plus a₁ₙ = aₙ₁ = −1 (literal);
  diag(−M, 1), e₂ — `diagonal ![-M, 1]`, `Pi.single 1 1`; the non-normal
  matrix — `nonNormal` = !![1/2, 4; 0, 1/2]; ρ(A) — Mathlib `spectralRadius ℂ`
  of the complexification; ‖A‖₂ — the scoped `Matrix.Norms.L2Operator` norm.

THEOREMS:
* Lemma lem:signed-gershgorin (P1.2, P1.5): `signed_gershgorin`,
  `signed_gershgorin_eigenvalues` (every eigenvalue), `posDef_of_signed_dominant`,
  `lamMin_pos_of_signed_dominant`, `posDef_of_passesDominance`.
* Lemma lem:certified-lmin (P1.12): `certified_lmin`, `certified_lmin_norm`.
* Example A = −I (P1.3): `example_neg_one`.
* Example Dirichlet (P1.6): `dirichlet_interior_row`,
  `dirichlet_not_strictly_dominant` (n ≥ 3), `dirichlet_quadratic`
  (the identity, n ≥ 1), `dirichlet_posDef` (every n).
* Example periodic (P1.6 contrast): `periodic_row`, `periodic_singular` (n ≥ 3).
* Example isolation (P1.13): `example_isolation`.
* Example non-normal (P1.16): `example_nonNormal`, `nonNormal_l2_opNorm_gt`,
  `nonNormal_pow`.

PROOF ROUTE for `certified_lmin`: every eigenvalue is λ_min or ≥ λ₂ ≥ ℓ, so
(λⱼ − λ_min)(λⱼ − ℓ) ≥ 0; expanding in the eigenbasis (Parseval) gives
((A − λ_min)u)·((A − ℓ)u) ≥ 0, which equals ‖r‖² + (λ̃ − λ_min)(λ̃ − ℓ) since
u·r = 0. This is the right Kato–Temple inequality for the isolated λ_min,
proved in place rather than cited. The non-normal example's Aᵏ → 0 is
proved directly from Aᵏ = 2⁻ᵏ[[1, 8k], [0, 1]], not via Gelfand's formula.

Status tier: FORMALISED (statement + proof, no sorry).
-/
import Mathlib
import OcfVerification.B6Witnesses

open Matrix BigOperators

namespace OCF.P

open OCF.B6 (gershRadius PassesDominance passes_iff_signedGershgorin)

variable {n : ℕ}

/-! ### Eigenvalues in increasing order -/

/-- Eigenvalues of a symmetric matrix listed increasingly with multiplicity:
`eigAsc hA k` is λ_{k+1} (0-indexed). Mathlib's `eigenvalues₀` is antitone;
we reverse it. -/
noncomputable def eigAsc {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (k : Fin (Fintype.card (Fin n))) : ℝ :=
  hA.eigenvalues₀ k.rev

lemma eigAsc_mono {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Monotone (eigAsc hA) := fun _ _ h =>
  hA.eigenvalues₀_antitone (Fin.rev_le_rev.mpr h)

lemma eigenvalues_eq_eigAsc {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (j : Fin n) :
    hA.eigenvalues j =
      eigAsc hA ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev := by
  simp [eigAsc, IsHermitian.eigenvalues]

lemma range_eigAsc {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Set.range (eigAsc hA) = Set.range hA.eigenvalues := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)) k.rev, ?_⟩
    simp [eigAsc, IsHermitian.eigenvalues]
  · rintro ⟨j, rfl⟩
    exact ⟨_, (eigenvalues_eq_eigAsc hA j).symm⟩

/-- λ_min(A) = λ₁ (needs n ≥ 1). -/
noncomputable def lamMin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n) : ℝ :=
  eigAsc hA ⟨0, by simpa using hn⟩

/-- λ₂(A) (needs n ≥ 2). -/
noncomputable def lamTwo {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 2 ≤ n) : ℝ :=
  eigAsc hA ⟨1, by simp; omega⟩

lemma lamMin_le_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n)
    (j : Fin n) : lamMin hA hn ≤ hA.eigenvalues j := by
  rw [eigenvalues_eq_eigAsc]
  apply eigAsc_mono hA; rw [Fin.le_def]; exact Nat.zero_le _

lemma lamMin_mem {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n) :
    lamMin hA hn ∈ Set.range hA.eigenvalues := by
  rw [← range_eigAsc]; exact ⟨_, rfl⟩

/-- λ_min is the minimum of the eigenvalues. -/
lemma lamMin_eq_iInf {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n) :
    lamMin hA hn = ⨅ j, hA.eigenvalues j := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := lamMin_mem hA hn
  apply le_antisymm
  · exact le_ciInf (lamMin_le_eigenvalues hA hn)
  · rw [← hj]; exact ciInf_le (Finite.bddBelow_range _) j

/-- λ_min is the minimum of the real spectrum. -/
lemma lamMin_isLeast {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n) :
    IsLeast (spectrum ℝ A) (lamMin hA hn) := by
  rw [hA.spectrum_real_eq_range_eigenvalues]
  exact ⟨lamMin_mem hA hn, by rintro _ ⟨j, rfl⟩; exact lamMin_le_eigenvalues hA hn j⟩


/-! ### Lemma lem:signed-gershgorin -/

/-- Gershgorin (P1.1, Mathlib `eigenvalue_mem_ball`) on the real line: every
real eigenvalue μ of a real matrix satisfies μ ≥ a_ii − rᵢ(A) for some i. -/
lemma exists_le_of_mem_spectrum {A : Matrix (Fin n) (Fin n) ℝ} {μ : ℝ}
    (hμ : μ ∈ spectrum ℝ A) : ∃ i, A i i - gershRadius A i ≤ μ := by
  have hμ' : Module.End.HasEigenvalue (Matrix.toLin' A) μ := by
    rw [Module.End.hasEigenvalue_iff_mem_spectrum]
    rwa [← AlgEquiv.spectrum_eq (Matrix.toLinAlgEquiv' (R := ℝ) (n := Fin n)) A] at hμ
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ'
  refine ⟨i, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  have : gershRadius A i = ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
    simp [gershRadius, Real.norm_eq_abs]
  rw [this]
  linarith [neg_abs_le (μ - A i i)]

/-- **Lemma lem:signed-gershgorin, first claim, every-eigenvalue form.** For
symmetric A, every eigenvalue is ≥ minᵢ (a_ii − rᵢ(A)). -/
theorem signed_gershgorin_eigenvalues {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (j : Fin n) : (⨅ i, (A i i - gershRadius A i)) ≤ hA.eigenvalues j := by
  obtain ⟨i, hi⟩ := exists_le_of_mem_spectrum (hA.eigenvalues_mem_spectrum_real j)
  exact (ciInf_le (Finite.bddBelow_range _) i).trans hi

/-- **Lemma lem:signed-gershgorin, first claim** (P1.2):
λ_min(A) ≥ minᵢ (a_ii − rᵢ(A)) for symmetric A ∈ ℝⁿˣⁿ, n ≥ 1. -/
theorem signed_gershgorin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n) :
    (⨅ i, (A i i - gershRadius A i)) ≤ lamMin hA hn := by
  obtain ⟨j, hj⟩ := lamMin_mem hA hn
  rw [← hj]; exact signed_gershgorin_eigenvalues hA j

/-- **Lemma lem:signed-gershgorin, second claim** (P1.5): symmetric,
a_ii > rᵢ(A) for every i ⟹ A ≻ 0; moreover λ_min(A) ≥ minᵢ(a_ii − rᵢ) > 0. -/
theorem posDef_of_signed_dominant {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hdom : ∀ i, gershRadius A i < A i i) : A.PosDef := by
  rw [hA.posDef_iff_eigenvalues_pos]
  intro j
  obtain ⟨i, hi⟩ := exists_le_of_mem_spectrum (hA.eigenvalues_mem_spectrum_real j)
  linarith [hdom i]

/-- The quantitative form of P1.5: 0 < minᵢ(a_ii − rᵢ) ≤ λ_min(A). -/
theorem lamMin_pos_of_signed_dominant {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hn : 0 < n) (hdom : ∀ i, gershRadius A i < A i i) :
    0 < (⨅ i, (A i i - gershRadius A i)) ∧ (⨅ i, (A i i - gershRadius A i)) ≤ lamMin hA hn := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  refine ⟨?_, signed_gershgorin hA hn⟩
  obtain ⟨i, hi⟩ := exists_eq_ciInf_of_finite (f := fun i => A i i - gershRadius A i)
  rw [← hi]; linarith [hdom i]

/-- The same, with B6's dominance test as hypothesis (B6
`passes_iff_signedGershgorin`: the test is exactly ∀ i, rᵢ < a_ii). -/
theorem posDef_of_passesDominance {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (h : PassesDominance A) : A.PosDef :=
  posDef_of_signed_dominant hA ((passes_iff_signedGershgorin A).mp h)


/-! ### Lemma lem:certified-lmin -/

/-- Rayleigh quotient R_A(x) = xᵀAx / xᵀx. -/
noncomputable def rq (A : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  (x ⬝ᵥ (A *ᵥ x)) / (x ⬝ᵥ x)

/-- The residual r = (A − λ̃I)u with λ̃ = R_A(u). -/
noncomputable def resid (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) : Fin n → ℝ :=
  (A - rq A u • (1 : Matrix (Fin n) (Fin n) ℝ)) *ᵥ u

lemma resid_eq (A : Matrix (Fin n) (Fin n) ℝ) (u : Fin n → ℝ) :
    resid A u = A *ᵥ u - rq A u • u := by
  simp [resid, sub_mulVec, smul_mulVec]

lemma inner_toLp (x y : Fin n → ℝ) :
    inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) (WithLp.toLp 2 y) = x ⬝ᵥ y := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

/-- Spectral step: for symmetric A and reals a, c with
(λ_j − a)(λ_j − c) ≥ 0 for every eigenvalue, ((A − a)u)·((A − c)u) ≥ 0. -/
lemma quad_nonneg_of_eig {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (a c : ℝ)
    (h : ∀ j, 0 ≤ (hA.eigenvalues j - a) * (hA.eigenvalues j - c)) (u : Fin n → ℝ) :
    0 ≤ (A *ᵥ u - a • u) ⬝ᵥ (A *ᵥ u - c • u) := by
  set b := hA.eigenvectorBasis
  have hsym : Aᵀ = A := by
    have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  -- coordinates of (A − t)u in the eigenbasis
  have hcoord : ∀ (t : ℝ) (j : Fin n), (b j).ofLp ⬝ᵥ (A *ᵥ u - t • u) =
      (hA.eigenvalues j - t) * ((b j).ofLp ⬝ᵥ u) := by
    intro t j
    have h1 : (b j).ofLp ⬝ᵥ (A *ᵥ u) = (A *ᵥ (b j).ofLp) ⬝ᵥ u := by
      rw [dotProduct_mulVec, ← mulVec_transpose, hsym]
    rw [dotProduct_sub, dotProduct_smul, h1, hA.mulVec_eigenvectorBasis, smul_dotProduct]
    simp only [smul_eq_mul]; ring
  have hpars := b.sum_inner_mul_inner (WithLp.toLp 2 (A *ᵥ u - a • u))
    (WithLp.toLp 2 (A *ᵥ u - c • u))
  rw [inner_toLp] at hpars
  rw [← hpars]
  refine Finset.sum_nonneg fun j _ => ?_
  have e1 : inner ℝ (WithLp.toLp 2 (A *ᵥ u - a • u) : EuclideanSpace ℝ (Fin n)) (b j) =
      (hA.eigenvalues j - a) * ((b j).ofLp ⬝ᵥ u) := by
    rw [real_inner_comm, ← hcoord, ← inner_toLp]
  have e2 : inner ℝ (b j) (WithLp.toLp 2 (A *ᵥ u - c • u) : EuclideanSpace ℝ (Fin n)) =
      (hA.eigenvalues j - c) * ((b j).ofLp ⬝ᵥ u) := by
    rw [← hcoord, ← inner_toLp]
  rw [e1, e2]
  have := h j
  nlinarith [sq_nonneg ((b j).ofLp ⬝ᵥ u)]

/-- **Lemma lem:certified-lmin** (P1.12). Let A ∈ ℝⁿˣⁿ be symmetric with
n ≥ 2, ‖u‖₂ = 1 (uᵀu = 1), λ̃ := R_A(u), r := (A − λ̃I)u. If
λ̃ < ℓ ≤ λ₂(A), then λ_min(A) ≥ λ̃ − ‖r‖₂²/(ℓ − λ̃).
(Proof: the right Kato–Temple inequality for the isolated λ_min, in
eigen-coordinates: (λⱼ − λ_min)(λⱼ − ℓ) ≥ 0 for every eigenvalue.) -/
theorem certified_lmin (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (u : Fin n → ℝ) (hu : u ⬝ᵥ u = 1) (ℓ : ℝ)
    (hℓ : rq A u < ℓ) (hℓ2 : ℓ ≤ lamTwo hA hn) :
    rq A u - (resid A u ⬝ᵥ resid A u) / (ℓ - rq A u) ≤ lamMin hA (by omega) := by
  set lt := rq A u with hlt
  set l1 := lamMin hA (by omega)
  -- every eigenvalue is λ_min or ≥ λ₂ ≥ ℓ
  have heig : ∀ j, 0 ≤ (hA.eigenvalues j - l1) * (hA.eigenvalues j - ℓ) := by
    intro j
    have hge : l1 ≤ hA.eigenvalues j := lamMin_le_eigenvalues hA _ j
    rw [eigenvalues_eq_eigAsc]
    set k := ((Fintype.equivOfCardEq (Fintype.card_fin _)).symm j).rev
    by_cases hk : k.val = 0
    · have : k = ⟨0, by simp; omega⟩ := Fin.ext hk
      rw [this]; simp [l1, lamMin]
    · have h2 : lamTwo hA hn ≤ eigAsc hA k := by
        apply eigAsc_mono hA; rw [Fin.le_def]; simp; omega
      rw [eigenvalues_eq_eigAsc] at hge
      apply mul_nonneg <;> linarith
  have hq := quad_nonneg_of_eig hA l1 ℓ heig u
  have hut : u ⬝ᵥ (A *ᵥ u) = lt := by rw [hlt, rq, hu, div_one]
  have hr : resid A u = A *ᵥ u - lt • u := resid_eq A u
  -- expand ((A − λ₁)u)·((A − ℓ)u) = ‖r‖² + (λ̃ − λ₁)(λ̃ − ℓ)
  have hAuu : (A *ᵥ u) ⬝ᵥ u = lt := by rw [dotProduct_comm, hut]
  have hexp : (A *ᵥ u - l1 • u) ⬝ᵥ (A *ᵥ u - ℓ • u) =
      resid A u ⬝ᵥ resid A u + (lt - l1) * (lt - ℓ) := by
    rw [hr]
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hut, hAuu, hu]
    ring
  rw [hexp] at hq
  have hpos : 0 < ℓ - lt := by linarith
  rw [sub_le_comm, le_div_iff₀ hpos]
  nlinarith

/-- The same in Euclidean-norm notation: ‖u‖₂ = 1 and ‖r‖₂². -/
theorem certified_lmin_norm (hn : 2 ≤ n) {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (u : EuclideanSpace ℝ (Fin n)) (hu : ‖u‖ = 1) (ℓ : ℝ)
    (hℓ : rq A u.ofLp < ℓ) (hℓ2 : ℓ ≤ lamTwo hA hn) :
    rq A u.ofLp - ‖(WithLp.toLp 2 (resid A u.ofLp) : EuclideanSpace ℝ (Fin n))‖ ^ 2
      / (ℓ - rq A u.ofLp) ≤ lamMin hA (by omega) := by
  have hu' : u.ofLp ⬝ᵥ u.ofLp = 1 := by
    rw [← inner_toLp]; simp [hu]
  rw [← real_inner_self_eq_norm_sq, inner_toLp]
  exact certified_lmin hn hA u.ofLp hu' ℓ hℓ hℓ2


/-! ### Example: A = −Iₙ (the sign of the centre matters) -/

lemma gershRadius_neg_one (i : Fin n) : gershRadius (-1 : Matrix (Fin n) (Fin n) ℝ) i = 0 := by
  unfold gershRadius
  refine Finset.sum_eq_zero fun j hj => ?_
  have : i ≠ j := fun h => (Finset.mem_erase.mp hj).1 h.symm
  simp [one_apply, this]

/-- **Example (A = −Iₙ), P1.3.** For n ≥ 1: minᵢ(a_ii − rᵢ) = −1 = λ_min (the
signed bound holds with equality), whereas discs centred at |a_ii| would give
minᵢ(|a_ii| − rᵢ) = 1 > λ_min, a false bound. -/
theorem example_neg_one (hn : 0 < n) :
    let A : Matrix (Fin n) (Fin n) ℝ := -1
    ∃ hA : A.IsHermitian,
      (⨅ i, (A i i - gershRadius A i)) = -1 ∧ lamMin hA hn = -1 ∧
      (⨅ i, (|A i i| - gershRadius A i)) = 1 ∧ lamMin hA hn < ⨅ i, (|A i i| - gershRadius A i) := by
  intro A
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hA : A.IsHermitian := by simp [A, IsHermitian]
  have hl : lamMin hA hn = -1 := by
    obtain ⟨j, hj⟩ := lamMin_mem hA hn
    have hmem := hA.eigenvalues_mem_spectrum_real j
    have hsp : spectrum ℝ A = {-1} := by
      have : A = algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) (-1) := by
        rw [Algebra.algebraMap_eq_smul_one, neg_one_smul]
      rw [this, spectrum.scalar_eq]
    have h' : lamMin hA hn ∈ spectrum ℝ A := hj ▸ hmem
    rw [hsp] at h'
    simpa using h'
  refine ⟨hA, ?_, hl, ?_, ?_⟩
  · simp [A, gershRadius_neg_one]
  · simp [A, gershRadius_neg_one]
  · simp [A, gershRadius_neg_one, hl]

/-! ### A row with exactly two off-diagonal −1 entries -/

lemma row_two_nbrs {A : Matrix (Fin n) (Fin n) ℝ} {i j₁ j₂ : Fin n}
    (h₁ : j₁ ≠ i) (h₂ : j₂ ≠ i) (h₁₂ : j₁ ≠ j₂)
    (hA : ∀ j, A i j = if j = i then 2 else if j = j₁ ∨ j = j₂ then -1 else 0) :
    gershRadius A i = 2 ∧ A i i = 2 ∧ ∑ j, A i j = 0 := by
  have hii : A i i = 2 := by simp [hA]
  refine ⟨?_, hii, ?_⟩
  · unfold gershRadius
    have : ∀ j ∈ Finset.univ.erase i, |A i j| =
        (if j = j₁ then 1 else 0) + (if j = j₂ then 1 else 0) := by
      intro j hj
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      rw [hA j]
      by_cases a : j = j₁
      · subst a; simp [hji, h₁₂]
      · by_cases b : j = j₂
        · subst b; simp [hji, a]
        · simp [hji, a, b]
    rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, Finset.sum_ite_eq',
      Finset.sum_ite_eq']
    simp [h₁, h₂]; norm_num
  · have : ∀ j, A i j = 2 * (if j = i then 1 else 0) - (if j = j₁ then 1 else 0)
        - (if j = j₂ then 1 else 0) := by
      intro j
      rw [hA j]
      by_cases c : j = i
      · subst c; simp [h₁.symm, h₂.symm]
      · by_cases a : j = j₁
        · subst a; simp [c, h₁₂]
        · by_cases b : j = j₂
          · subst b; simp [c, a]
          · simp [c, a, b]
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    norm_num

/-! ### Example: the Dirichlet 1-D Laplacian tridiag(−1, 2, −1) -/

/-- tridiag(−1, 2, −1) ∈ ℝⁿˣⁿ. -/
def dirichlet (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j =>
    if i = j then 2 else if (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i then -1 else 0

lemma dirichlet_isHermitian (n : ℕ) : (dirichlet n).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, dirichlet, of_apply]
  by_cases h : i = j
  · subst h; simp
  · simp [h, Ne.symm h, or_comm]

/-- For n ≥ 3, rows 2, …, n−1 (0-indexed 1, …, n−2) have a_ii = rᵢ(A) = 2. -/
lemma dirichlet_interior_row {n : ℕ} (i : Fin n) (h1 : 1 ≤ (i : ℕ)) (h2 : (i : ℕ) + 2 ≤ n) :
    gershRadius (dirichlet n) i = 2 ∧ dirichlet n i i = 2 := by
  have := row_two_nbrs (A := dirichlet n) (i := i) (j₁ := ⟨i - 1, by omega⟩)
    (j₂ := ⟨i + 1, by omega⟩) (by simp only [ne_eq, Fin.ext_iff]; omega)
    (by simp only [ne_eq, Fin.ext_iff]; omega) (by simp only [ne_eq, Fin.ext_iff]; omega) (by
      intro j
      simp only [dirichlet, of_apply, Fin.ext_iff]
      by_cases a : (i : ℕ) = j
      · simp [a]
      · rw [if_neg a, if_neg (Ne.symm a)]
        congr 1
        apply propext; omega)
  exact ⟨this.1, this.2.1⟩

/-- **Example (Dirichlet), non-dominance.** For n ≥ 3 the Dirichlet Laplacian is
not strictly diagonally dominant (neither in the |a_ii| > rᵢ form nor in the
signed form). -/
theorem dirichlet_not_strictly_dominant {n : ℕ} (hn : 3 ≤ n) :
    ¬ (∀ i, gershRadius (dirichlet n) i < |dirichlet n i i|) ∧
    ¬ (∀ i, gershRadius (dirichlet n) i < dirichlet n i i) := by
  obtain ⟨h1, h2⟩ := dirichlet_interior_row (n := n) ⟨1, by omega⟩ le_rfl (by simp; omega)
  constructor
  · intro h; have := h ⟨1, by omega⟩; rw [h1, h2] at this; norm_num at this
  · intro h; have := h ⟨1, by omega⟩; rw [h1, h2] at this; norm_num at this

/-- The shift S with S i j = 1 iff j = i + 1. -/
def shiftUp (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) + 1 = j then 1 else 0

lemma dirichlet_eq (n : ℕ) :
    dirichlet n = (2 : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ) - shiftUp n - (shiftUp n)ᵀ := by
  ext i j
  simp only [dirichlet, shiftUp, of_apply, Matrix.sub_apply, Matrix.smul_apply, one_apply,
    transpose_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · have h' : (i : ℕ) ≠ j := fun e => h (Fin.ext e)
    rw [if_neg h, if_neg h]
    by_cases a : (i : ℕ) + 1 = j
    · have : ¬ ((j : ℕ) + 1 = i) := by omega
      simp [a, this]
    · by_cases b : (j : ℕ) + 1 = i
      · simp [a, b]
      · simp [a, b]

lemma shiftUp_dot (m : ℕ) (x : Fin (m + 1) → ℝ) :
    x ⬝ᵥ (shiftUp (m + 1) *ᵥ x) = ∑ k : Fin m, x k.castSucc * x k.succ := by
  have hc : ∀ k : Fin m, (shiftUp (m + 1) *ᵥ x) k.castSucc = x k.succ := by
    intro k
    simp only [mulVec, dotProduct, shiftUp, of_apply]
    rw [Finset.sum_eq_single k.succ]
    · simp
    · intro j _ hj
      rw [if_neg]
      · simp
      · intro h; exact hj (Fin.ext (by simp only [Fin.val_castSucc] at h; simp [Fin.val_succ]; omega))
    · simp
  have hl : (shiftUp (m + 1) *ᵥ x) (Fin.last m) = 0 := by
    simp only [mulVec, dotProduct, shiftUp, of_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [if_neg]
    · simp
    · simp only [Fin.val_last]; omega
  rw [dotProduct, Fin.sum_univ_castSucc]
  simp [hc, hl]

/-- **Example (Dirichlet), the identity** xᵀAx = x₁² + Σ_{i=1}^{n−1}(xᵢ − x_{i+1})² + xₙ²
(stated for n = m + 1 ≥ 1). -/
theorem dirichlet_quadratic (m : ℕ) (x : Fin (m + 1) → ℝ) :
    x ⬝ᵥ (dirichlet (m + 1) *ᵥ x) =
      x 0 ^ 2 + ∑ k : Fin m, (x k.castSucc - x k.succ) ^ 2 + x (Fin.last m) ^ 2 := by
  have hT : x ⬝ᵥ ((shiftUp (m + 1))ᵀ *ᵥ x) = x ⬝ᵥ (shiftUp (m + 1) *ᵥ x) := by
    rw [mulVec_transpose, dotProduct_comm, ← dotProduct_mulVec]
  rw [dirichlet_eq, sub_mulVec, sub_mulVec, dotProduct_sub, dotProduct_sub, hT, shiftUp_dot,
    smul_mulVec, one_mulVec, dotProduct_smul]
  have h1 := Fin.sum_univ_castSucc (fun i => x i ^ 2)
  have h2 := Fin.sum_univ_succ (fun i => x i ^ 2)
  have hxx : x ⬝ᵥ x = ∑ i, x i ^ 2 := by simp [dotProduct, sq]
  rw [hxx]
  simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib] at *
  simp only [smul_eq_mul]
  have h3 : ∑ k : Fin m, 2 * x k.castSucc * x k.succ = 2 * ∑ k : Fin m, x k.castSucc * x k.succ := by
    rw [Finset.mul_sum]; simp [mul_assoc]
  rw [h3]
  linarith


/-- **Example (Dirichlet), positive definiteness**: A ≻ 0 for every n (the
dossier states n ≥ 3; for n ≤ 2 it also follows from P1.5). -/
theorem dirichlet_posDef (n : ℕ) : (dirichlet n).PosDef := by
  rw [posDef_iff_dotProduct_mulVec]
  refine ⟨dirichlet_isHermitian n, fun x hx => ?_⟩
  rw [star_trivial]
  obtain _ | m := n
  · exact absurd (funext fun i => i.elim0) hx
  rw [dirichlet_quadratic]
  by_contra hle
  replace hle := not_lt.mp hle
  have hs : 0 ≤ ∑ k : Fin m, (x k.castSucc - x k.succ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h0 : x 0 = 0 := by nlinarith [sq_nonneg (x 0), sq_nonneg (x (Fin.last m))]
  have hsum : ∑ k : Fin m, (x k.castSucc - x k.succ) ^ 2 = 0 := by
    nlinarith [sq_nonneg (x 0), sq_nonneg (x (Fin.last m))]
  have hstep : ∀ k : Fin m, x k.succ = x k.castSucc := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)).mp hsum k
      (Finset.mem_univ _)
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linarith
  apply hx
  funext i
  induction i using Fin.induction with
  | zero => exact h0
  | succ k ih => rw [hstep k, ih]; rfl

/-! ### Example: the periodic Laplacian (Dirichlet plus corners a₁ₙ = aₙ₁ = −1) -/

/-- The periodic Laplacian: tridiag(−1, 2, −1) with a_{1n} = a_{n1} = −1 added. -/
def periodic (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  dirichlet n + Matrix.of fun (i j : Fin n) =>
    if ((i : ℕ) = 0 ∧ (j : ℕ) = n - 1) ∨ ((i : ℕ) = n - 1 ∧ (j : ℕ) = 0) then -1 else 0

/-- For n ≥ 3, each row i of the periodic Laplacian has 2 on the diagonal and −1
exactly at its two cyclic neighbours. -/
lemma periodic_row {n : ℕ} (hn : 3 ≤ n) (i : Fin n) :
    gershRadius (periodic n) i = 2 ∧ periodic n i i = 2 ∧ ∑ j, periodic n i j = 0 := by
  have hp : ∀ j : Fin n, periodic n i j = if j = i then 2 else
      if j = ⟨if (i : ℕ) = 0 then n - 1 else i - 1, by split_ifs <;> omega⟩ ∨
        j = ⟨if (i : ℕ) = n - 1 then 0 else i + 1, by split_ifs <;> omega⟩ then -1 else 0 := by
    intro j
    simp only [periodic, dirichlet, Matrix.add_apply, of_apply, Fin.ext_iff]
    have hj := j.isLt; have hi := i.isLt
    by_cases a : (i : ℕ) = j
    · rw [if_pos a, if_pos a.symm]
      have : ¬ (((i : ℕ) = 0 ∧ (j : ℕ) = n - 1) ∨ ((i : ℕ) = n - 1 ∧ (j : ℕ) = 0)) := by omega
      rw [if_neg this]; ring
    · rw [if_neg a, if_neg (Ne.symm a)]
      split_ifs <;> first | omega | norm_num
  exact row_two_nbrs (by simp only [ne_eq, Fin.ext_iff]; split_ifs <;> omega)
    (by simp only [ne_eq, Fin.ext_iff]; split_ifs <;> omega)
    (by simp only [ne_eq, Fin.ext_iff]; split_ifs <;> omega) hp

/-- **Example (periodic Laplacian).** For n ≥ 3: a_ii = rᵢ(A) in every row
(the same equality pattern), A𝟙 = 0, hence A is singular. -/
theorem periodic_singular {n : ℕ} (hn : 3 ≤ n) :
    (∀ i, periodic n i i = gershRadius (periodic n) i) ∧
    periodic n *ᵥ (fun _ => 1) = 0 ∧ (periodic n).det = 0 ∧ ¬ IsUnit (periodic n) := by
  have h1 : periodic n *ᵥ (fun _ => 1) = 0 := by
    funext i; simp [mulVec, dotProduct, (periodic_row hn i).2.2]
  have hdet : (periodic n).det = 0 := by
    rw [← exists_mulVec_eq_zero_iff]
    exact ⟨fun _ => 1, fun h => by
      have := congr_fun h ⟨0, by omega⟩; simp at this, h1⟩
  refine ⟨fun i => ?_, h1, hdet, ?_⟩
  · rw [(periodic_row hn i).1, (periodic_row hn i).2.1]
  · rw [isUnit_iff_isUnit_det, hdet]; simp


/-! ### Example: the isolation hypothesis cannot be dropped -/

/-- **Example (isolation), P1.13.** For M > 0, A = diag(−M, 1), u = e₂:
R_A(u) = 1, r = 0, λ_min = −M, λ₂ = 1 = λ̃; no ℓ satisfies λ̃ < ℓ ≤ λ₂, and
for every ℓ > λ̃ the bound λ̃ − ‖r‖²/(ℓ − λ̃) = 1 exceeds λ_min = −M (the
conclusion of `certified_lmin` fails once isolation is dropped). -/
theorem example_isolation (M : ℝ) (hM : 0 < M) :
    let A : Matrix (Fin 2) (Fin 2) ℝ := diagonal ![-M, 1]
    let u : Fin 2 → ℝ := Pi.single 1 1
    ∃ hA : A.IsHermitian,
      u ⬝ᵥ u = 1 ∧ rq A u = 1 ∧ resid A u = 0 ∧
      lamMin hA (by norm_num) = -M ∧ lamTwo hA le_rfl = 1 ∧
      (¬ ∃ ℓ, rq A u < ℓ ∧ ℓ ≤ lamTwo hA le_rfl) ∧
      ∀ ℓ, rq A u < ℓ →
        lamMin hA (by norm_num) < rq A u - (resid A u ⬝ᵥ resid A u) / (ℓ - rq A u) := by
  intro A u
  have hA : A.IsHermitian := isHermitian_diagonal _
  have huu : u ⬝ᵥ u = 1 := by simp [u]
  have hAu : A *ᵥ u = u := by
    funext i; fin_cases i <;> simp [A, u, mulVec_single]
  have hrq : rq A u = 1 := by rw [rq, hAu, huu]; norm_num
  have hres : resid A u = 0 := by rw [resid_eq, hAu, hrq, one_smul, sub_self]
  -- the sorted eigenvalues are (−M, 1)
  have hrange : Set.range (eigAsc hA) = {-M, 1} := by
    rw [range_eigAsc, ← hA.spectrum_real_eq_range_eigenvalues]
    simp only [A, spectrum_diagonal]
    ext x; simp [or_comm]
  have hcard : Fintype.card (Fin 2) = 2 := rfl
  set a := lamMin hA (by norm_num) with ha
  set b := lamTwo hA le_rfl with hb
  have hab : a ≤ b := by
    apply eigAsc_mono hA; rw [Fin.le_def]; simp
  have hall : ∀ k, eigAsc hA k = a ∨ eigAsc hA k = b := by
    intro k
    rcases k with ⟨k, hk⟩
    have : k = 0 ∨ k = 1 := by simp at hk; omega
    rcases this with rfl | rfl
    · left; rfl
    · right; rfl
  have hmem : ∀ x, x ∈ Set.range (eigAsc hA) ↔ x = -M ∨ x = 1 := by
    intro x; rw [hrange]; simp
  have haM : a = -M ∨ a = 1 := (hmem a).mp ⟨_, rfl⟩
  have hbM : b = -M ∨ b = 1 := (hmem b).mp ⟨_, rfl⟩
  have hM1 : -M = a ∨ -M = b := by
    obtain ⟨k, hk⟩ := (hmem (-M)).mpr (Or.inl rfl)
    rcases hall k with h | h <;> [left; right] <;> rw [← hk, h]
  have h11 : (1 : ℝ) = a ∨ 1 = b := by
    obtain ⟨k, hk⟩ := (hmem 1).mpr (Or.inr rfl)
    rcases hall k with h | h <;> [left; right] <;> rw [← hk, h]
  have hav : a = -M := by
    rcases haM with h | h
    · exact h
    · exfalso; rcases hM1 with h' | h' <;> rcases hbM with h'' | h'' <;> linarith
  have hbv : b = 1 := by
    rcases hbM with h | h
    · exfalso; rcases h11 with h' | h' <;> linarith
    · exact h
  rw [ha] at hav; rw [hb] at hbv
  refine ⟨hA, huu, hrq, hres, hav, hbv, ?_, ?_⟩
  · rintro ⟨ℓ, h1, h2⟩; rw [hrq] at h1; linarith
  · intro ℓ _; rw [hres, hrq]; simp; linarith

/-! ### Example: a non-normal matrix -/

/-- A = [[1/2, 4], [0, 1/2]]. -/
noncomputable def nonNormal : Matrix (Fin 2) (Fin 2) ℝ := !![1/2, 4; 0, 1/2]

lemma nonNormal_pow (k : ℕ) :
    nonNormal ^ k = !![(1/2 : ℝ) ^ k, 8 * k * (1/2) ^ k; 0, (1/2) ^ k] := by
  induction k with
  | zero => ext i j; fin_cases i <;> fin_cases j <;> simp
  | succ k ih =>
    rw [pow_succ, ih]
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [nonNormal, Matrix.mul_apply, Fin.sum_univ_two, pow_succ]
    ring

/-- **Example (non-normal matrix), P1.16.** The complex spectrum of A is {1/2},
so ρ(A) = 1/2; Aᵏ → 0; yet ‖Ae₂‖₂ = ‖(4, 1/2)‖₂ > 4, hence the induced
2-norm satisfies ‖A‖₂ > 4. -/
theorem example_nonNormal :
    spectrum ℂ (nonNormal.map (algebraMap ℝ ℂ)) = {1/2} ∧
    spectralRadius ℂ (nonNormal.map (algebraMap ℝ ℂ)) = (1/2 : NNReal) ∧
    Filter.Tendsto (fun k : ℕ => nonNormal ^ k) Filter.atTop (nhds 0) ∧
    nonNormal *ᵥ Pi.single 1 1 = ![4, 1/2] ∧
    4 < ‖(WithLp.toLp 2 (nonNormal *ᵥ Pi.single 1 1) : EuclideanSpace ℝ (Fin 2))‖ := by
  have hsp : spectrum ℂ (nonNormal.map (algebraMap ℝ ℂ)) = {1/2} := by
    ext z
    rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
      Set.mem_singleton_iff, Matrix.det_fin_two]
    simp [nonNormal, Matrix.algebraMap_matrix_apply]
    constructor
    · intro h; linear_combination h
    · intro h; rw [h]; ring
  refine ⟨hsp, ?_, ?_, ?_, ?_⟩
  · rw [spectralRadius, hsp]
    simp only [Set.mem_singleton_iff, iSup_iSup_eq_left]
    congr 1
    ext; simp
  · refine tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j => ?_
    simp only [nonNormal_pow]
    have h1 : Filter.Tendsto (fun k : ℕ => (1/2 : ℝ) ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h2 : Filter.Tendsto (fun k : ℕ => 8 * ((k : ℝ) * (1/2 : ℝ) ^ k)) Filter.atTop
        (nhds 0) := by
      simpa using (tendsto_self_mul_const_pow_of_lt_one (r := (1/2 : ℝ)) (by norm_num)
        (by norm_num)).const_mul 8
    fin_cases i <;> fin_cases j <;> simp
    · simpa using h1
    · simpa [mul_assoc] using h2
    · simpa using h1
  · funext i; fin_cases i <;> simp [nonNormal, mulVec_single]
  · have : nonNormal *ᵥ Pi.single 1 1 = ![4, 1/2] := by
      funext i; fin_cases i <;> simp [nonNormal, mulVec_single]
    rw [this, EuclideanSpace.norm_eq]
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_lt_sqrt (by norm_num)
    simp [Fin.sum_univ_two]

section L2
open scoped Matrix.Norms.L2Operator

/-- The induced 2-norm of the non-normal example exceeds 4. -/
theorem nonNormal_l2_opNorm_gt : 4 < ‖nonNormal‖ := by
  have hx : ‖(EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2))‖ = 1 := by simp
  have h := nonNormal.l2_opNorm_mulVec (EuclideanSpace.single 1 1)
  rw [hx, mul_one] at h
  have h4 := example_nonNormal.2.2.2.2
  have heq : (EuclideanSpace.equiv (Fin 2) ℝ).symm
      (nonNormal *ᵥ (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)).ofLp) =
      WithLp.toLp 2 (nonNormal *ᵥ Pi.single 1 1) := by
    simp [EuclideanSpace.equiv]
  rw [heq] at h
  linarith

end L2

end OCF.P

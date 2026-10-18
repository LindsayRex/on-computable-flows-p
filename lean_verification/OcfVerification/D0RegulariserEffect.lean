/-
D0 (Effect of an added term on λ_min) — Lemma D0.1 (i)–(v) with the approach bound (1.2)
(Remark D0.2(ii)), Lemma D0.4, and Lemma D0.6 (a)–(d) with Remark D0.6.1.

Source of truth: project_plan/done/proof_audits/D0_regulariser_effect/01_derivation.md (stage-1 dossier
revised at stage 3; sha16 0d342e9eb98fb471 at the start and at the end of formalisation; file
not edited), 03_adjudication.md (DECISION 7: division-free form of Lemma D0.6(d); DECISION 8 and
the Lean-tractability notes), and the stage-4 draft 04_landing_draft.tex (Lemma lem:ray-lmin,
eq:ray-approach, Lemma lem:l1-hessian, Lemma lem:restricted-factor). Theorem D0.5 (partial
smoothness, finite identification) and the endpoint counterexample are PROSE-ONLY by ruling and
are not attempted here.

DEFINITIONAL MAP:
* 𝕊^d (d ≥ 1) — `Matrix (Fin d) (Fin d) ℝ` with `IsHermitian` (over ℝ: Aᵀ = A); Q ⪰ 0 —
  `Q.PosSemidef`; ker Q — `OCF.matKer Q` (T1KernelTransversality), ker Q ≠ {0} —
  `OCF.matKer Q ≠ ⊥`.
* λ_min — PSpectralGlue's `lamMin` (smallest eigenvalue, from Mathlib's spectral theorem);
  λ_max — T1GramBound's `OCF.lambdaMax` (largest eigenvalue). The Rayleigh characterisation
  S0.2 is proved here (`lamMin_mul_le`, `exists_unit_lamMin`, `exists_unit_lambdaMax`), not
  assumed. ‖M‖₂ — Mathlib's scoped `Matrix.Norms.L2Operator` norm.
* φ(θ) = λ_min(H + θQ) — `phi hH hQ hd θ`.
* P with orthonormal columns spanning K = ker Q — `P : Matrix (Fin d) (Fin m) ℝ`,
  `Pᵀ * P = 1`, `LinearMap.range P.mulVecLin = OCF.matKer Q`; φ_∞ = λ_min(PᵀHP) — `phiInf`
  (m ≥ 1 is derived from ker Q ≠ {0}, `m_pos`).
* P_⊥ with [P P_⊥] orthogonal — `Pp : Matrix (Fin d) (Fin p) ℝ`, p ≥ 1, `Ppᵀ * Pp = 1`,
  `Pᵀ * Pp = 0`, `P * Pᵀ + Pp * Ppᵀ = 1`; q_⊥, c_⊥, ω — `qPerp`, `cPerp`, `omegaCross`;
  θ₀ = (φ_∞ − c_⊥)/q_⊥.
* H_SS for ∅ ≠ S ⊆ {1,…,d} — `subMat H S` (rows/columns of S in increasing order, via
  `S.orderEmbOfFin`); λ_S, Λ_S — `lamS`, `LamS`; ρ* — `rhoStar`; q_B3(a) = max{|1 − αa|,
  |1 − αβ|} — `qB3 α β a`; α ≤ 1/β with β > 0 — literally `α ≤ 1 / β`.
* g = λ‖·‖₁ on ℝᵈ — `gL1 lam` on `Fin d → ℝ` (λ is a Lean keyword); Ω — `Omega d`;
  ∇²h(x) — `fderiv ℝ (fderiv ℝ h) x` (differentiability and C^k do not depend on the norm
  of ℝᵈ). "f twice differentiable at x" is used only through "f differentiable near x".

THEOREMS:
* Lemma D0.1 (i)–(iv): `lemma_D01_i_iv` (bundle); pieces `phi_concaveOn` (also
  `phi_concaveOn_univ`, all of ℝ, S1.1's remark), `phi_monotoneOn` (also `phi_monotone`),
  `phi_zero` (φ(0) = λ_min(H)), `phi_ge_weyl`, `phi_bddAbove_iff`.
* Lemma D0.1 (v): `phi_tendsto_phiInf` (φ ≤ φ_∞ for every θ, and φ(θ) → φ_∞);
  `phi_le_phiInf` (S1.4); `phiInf_indep` (S0.1: φ_∞ does not depend on P).
* Bound (1.2): `approach_bound` (with `qPerp_pos`: Q_⊥ ≻ 0); general form `phi_ge_general`.
* Lemma D0.4: `Omega_isOpen`, `Omega_dense`, `gL1_contDiffOn` (C^n for every n, incl. ∞),
  `gL1_hessian_zero`, `gL1_not_differentiableAt` (λ > 0), `gL1_differentiable_set`,
  `gL1_C2_set` (Ω is exactly where g is differentiable, resp. C²), `hessian_add_gL1` (S4.4).
* Lemma D0.6: `lemma_D06` (bundle of (a)–(d)); pieces `D06_a`, `D06_b`, `D06_c_antitone`,
  `D06_c_chain`, `D06_d` (division-free), `D06_d_of_le_inv`; Remark D0.6.1: `D06_remark1`.

HYPOTHESES DROPPED (theorems proved under fewer hypotheses than stated, i.e. stronger):
Lemma D0.6 does not use H ⪰ 0, α < 2/β, or σ_f ≥ 0 (only σ_f ≤ λ_min(H)); (b) and (d) need
only α ≥ 0. Remark D0.6.1 does not use σ_f ≥ 0. D0.1(i), (ii) hold on all of ℝ, and the upper
bound of (v) for every θ ∈ ℝ. No hypothesis was strengthened.

PROOF ROUTE: as the dossier — Rayleigh quotients throughout. For (v) and (1.2) the 2×2
eigenvalue step of S1.6 is replaced by the equivalent elementary inequality
φa² − 2ωab + (φ + δ)b² ≥ φ − ω²/δ for a² + b² = 1, δ > 0 (`two_by_two`), which is exactly
what S1.6 extracts from λ_min(N(θ)); (1.1) itself is not stated. For the limit (v) without a
P_⊥, positivity on (ker Q)^⊥ uses G12's smallest nonzero eigenvalue λ⁺(Q)
(`OCF.G12.exists_ker_lambdaPlus_le`), with c = λ_min(H) and ω = ‖H‖₂.

Status tier: FORMALISED (statement + proof, no sorry) for Lemma D0.1 (i)–(v), the bound
(1.2), Lemma D0.4 and Lemma D0.6 (a)–(d) with Remark D0.6.1.
-/
import Mathlib
import OcfVerification.PSpectralGlue
import OcfVerification.G12DominanceLemma

open Matrix BigOperators Filter Topology

namespace OCF.D0

open OCF.P (lamMin lamMin_mem lamMin_le_eigenvalues lamMin_isLeast)

/-! ## §0 Rayleigh characterisation (S0.2), proved from the spectral theorem -/

section Rayleigh

variable {n : ℕ}

lemma lamMin_congr {A B : Matrix (Fin n) (Fin n) ℝ} (h : A = B) (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hn : 0 < n) : lamMin hA hn = lamMin hB hn := by
  subst h; rfl

lemma transpose_eq_of_isHermitian {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) :
    Aᵀ = A := by
  have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this

/-- Symmetry of the bilinear form of a symmetric matrix. -/
lemma dot_mulVec_comm {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (x y : Fin n → ℝ) :
    x ⬝ᵥ A *ᵥ y = y ⬝ᵥ A *ᵥ x := by
  rw [dotProduct_mulVec, ← mulVec_transpose, transpose_eq_of_isHermitian hA, dotProduct_comm]

/-- Rayleigh lower bound: λ_min(A)·xᵀx ≤ xᵀAx. -/
lemma lamMin_mul_le {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hn : 0 < n)
    (x : Fin n → ℝ) : lamMin hA hn * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  have hpsd : (A - (lamMin hA hn) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨hA.sub (Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)), ?_⟩
    intro μ hμ
    rw [show (lamMin hA hn) • (1 : Matrix (Fin n) (Fin n) ℝ)
          = algebraMap ℝ (Matrix (Fin n) (Fin n) ℝ) (lamMin hA hn) from
        (Algebra.algebraMap_eq_smul_one _).symm, ← spectrum.sub_singleton_eq] at hμ
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_sub.mp hμ
    rw [Set.mem_singleton_iff] at hc
    subst hc
    have := (lamMin_isLeast hA hn).2 ha
    simp only [Set.mem_setOf_eq, sub_nonneg]
    exact this
  have h0 := hpsd.dotProduct_mulVec_nonneg x
  rw [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_sub, dotProduct_smul, smul_eq_mul] at h0
  linarith

/-- λ_min is attained at a unit eigenvector. -/
lemma exists_unit_eigvec_lamMin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hn : 0 < n) : ∃ x : Fin n → ℝ, x ⬝ᵥ x = 1 ∧ A *ᵥ x = lamMin hA hn • x := by
  obtain ⟨j, hj⟩ := lamMin_mem hA hn
  refine ⟨(hA.eigenvectorBasis j).ofLp, ?_, ?_⟩
  · have := OCF.ofLp_dotProduct_of_orthonormal hA.eigenvectorBasis.orthonormal j j
    simpa using this
  · rw [← hj]; exact hA.mulVec_eigenvectorBasis j

lemma exists_unit_lamMin {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hn : 0 < n) : ∃ x : Fin n → ℝ, x ⬝ᵥ x = 1 ∧ x ⬝ᵥ A *ᵥ x = lamMin hA hn := by
  obtain ⟨x, hx, hAx⟩ := exists_unit_eigvec_lamMin hA hn
  exact ⟨x, hx, by rw [hAx, dotProduct_smul, hx, smul_eq_mul, mul_one]⟩

end Rayleigh

/-! ### Compressions EᵀAE by a matrix with orthonormal columns -/

section Compress

variable {n k : ℕ}

lemma isHermitian_compress {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (E : Matrix (Fin n) (Fin k) ℝ) : (Eᵀ * A * E).IsHermitian := by
  simpa [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_mul E hA

lemma dot_compress (A : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin k) ℝ)
    (z w : Fin k → ℝ) : z ⬝ᵥ (Eᵀ * A * E) *ᵥ w = (E *ᵥ z) ⬝ᵥ A *ᵥ (E *ᵥ w) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma dot_compress2 {l : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (E : Matrix (Fin n) (Fin k) ℝ)
    (F : Matrix (Fin n) (Fin l) ℝ) (z : Fin k → ℝ) (w : Fin l → ℝ) :
    z ⬝ᵥ (Eᵀ * A * F) *ᵥ w = (E *ᵥ z) ⬝ᵥ A *ᵥ (F *ᵥ w) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma dot_orthonormal {E : Matrix (Fin n) (Fin k) ℝ} (hE : Eᵀ * E = 1) (z w : Fin k → ℝ) :
    (E *ᵥ z) ⬝ᵥ (E *ᵥ w) = z ⬝ᵥ w := by
  have := dot_compress (1 : Matrix (Fin n) (Fin n) ℝ) E z w
  rw [Matrix.mul_one, hE, Matrix.one_mulVec, Matrix.one_mulVec] at this
  exact this.symm

lemma transpose_mulVec_mulVec {E : Matrix (Fin n) (Fin k) ℝ} (hE : Eᵀ * E = 1)
    (z : Fin k → ℝ) : Eᵀ *ᵥ (E *ᵥ z) = z := by
  rw [mulVec_mulVec, hE, one_mulVec]

/-- λ_min of a compression by orthonormal columns is at least λ_min. -/
lemma lamMin_le_lamMin_compress {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hn : 0 < n) {E : Matrix (Fin n) (Fin k) ℝ} (hE : Eᵀ * E = 1) (hk : 0 < k) :
    lamMin hA hn ≤ lamMin (isHermitian_compress hA E) hk := by
  obtain ⟨z, hz, hzA⟩ := exists_unit_lamMin (isHermitian_compress hA E) hk
  have h := lamMin_mul_le hA hn (E *ᵥ z)
  rw [dot_orthonormal hE, hz, mul_one, ← dot_compress, hzA] at h
  exact h

end Compress

/-! ## Lemma D0.1 — λ_min along a ray of PSD perturbations -/

section RayLemma

variable {d : ℕ} {H Q : Matrix (Fin d) (Fin d) ℝ}

lemma isHermitian_ray (hH : H.IsHermitian) (hQ : Q.IsHermitian) (θ : ℝ) :
    (H + θ • Q).IsHermitian :=
  hH.add (hQ.smul (IsSelfAdjoint.all θ))

/-- φ(θ) := λ_min(H + θQ). -/
noncomputable def phi (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) (θ : ℝ) : ℝ :=
  lamMin (isHermitian_ray hH hQ θ) hd

lemma quad_ray (x : Fin d → ℝ) (θ : ℝ) :
    x ⬝ᵥ (H + θ • Q) *ᵥ x = x ⬝ᵥ H *ᵥ x + θ * (x ⬝ᵥ Q *ᵥ x) := by
  rw [add_mulVec, smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul]

variable (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d)

lemma phi_le (θ : ℝ) {x : Fin d → ℝ} (hx : x ⬝ᵥ x = 1) :
    phi hH hQ hd θ ≤ x ⬝ᵥ H *ᵥ x + θ * (x ⬝ᵥ Q *ᵥ x) := by
  have h := lamMin_mul_le (isHermitian_ray hH hQ θ) hd x
  rw [hx, mul_one, quad_ray] at h
  exact h

lemma exists_phi_eq (θ : ℝ) : ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧
    phi hH hQ hd θ = x ⬝ᵥ H *ᵥ x + θ * (x ⬝ᵥ Q *ᵥ x) := by
  obtain ⟨x, hx, hxA⟩ := exists_unit_lamMin (isHermitian_ray hH hQ θ) hd
  exact ⟨x, hx, by rw [phi, ← hxA, quad_ray]⟩

/-- φ(0) = λ_min(H). -/
theorem phi_zero : phi hH hQ hd 0 = lamMin hH hd :=
  lamMin_congr (by simp) _ _ hd

lemma lamMin_le_quad {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) {x : Fin d → ℝ}
    (hx : x ⬝ᵥ x = 1) : lamMin hA hd ≤ x ⬝ᵥ A *ᵥ x := by
  have := lamMin_mul_le hA hd x; rwa [hx, mul_one] at this

/-- **Lemma D0.1(i)**, on all of ℝ (S1.1's remark). -/
theorem phi_concaveOn_univ : ConcaveOn ℝ Set.univ (phi hH hQ hd) := by
  refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
  obtain ⟨x, hx, hφ⟩ := exists_phi_eq hH hQ hd (a • s + b • t)
  have h1 := phi_le hH hQ hd s hx
  have h2 := phi_le hH hQ hd t hx
  simp only [smul_eq_mul] at hφ ⊢
  have e : a * (x ⬝ᵥ H *ᵥ x + s * (x ⬝ᵥ Q *ᵥ x)) + b * (x ⬝ᵥ H *ᵥ x + t * (x ⬝ᵥ Q *ᵥ x))
      = (a + b) * (x ⬝ᵥ H *ᵥ x) + (a * s + b * t) * (x ⬝ᵥ Q *ᵥ x) := by ring
  rw [hab, one_mul] at e
  rw [hφ, ← e]
  exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)

/-- **Lemma D0.1(i)**: φ is concave on [0, ∞). -/
theorem phi_concaveOn : ConcaveOn ℝ (Set.Ici 0) (phi hH hQ hd) :=
  (phi_concaveOn_univ hH hQ hd).subset (Set.subset_univ _) (convex_Ici 0)

variable (hQpsd : Q.PosSemidef)

include hQpsd in
lemma quad_nonneg (x : Fin d → ℝ) : 0 ≤ x ⬝ᵥ Q *ᵥ x := by
  simpa using hQpsd.dotProduct_mulVec_nonneg x

include hQpsd in
/-- **Lemma D0.1(ii)**, on all of ℝ. -/
theorem phi_monotone : Monotone (phi hH hQ hd) := by
  intro s t hst
  obtain ⟨x, hx, hφ⟩ := exists_phi_eq hH hQ hd t
  have h1 := phi_le hH hQ hd s hx
  have := quad_nonneg hQpsd x
  rw [hφ]; nlinarith

include hQpsd in
/-- **Lemma D0.1(ii)**: φ is non-decreasing on [0, ∞). -/
theorem phi_monotoneOn : MonotoneOn (phi hH hQ hd) (Set.Ici 0) :=
  (phi_monotone hH hQ hd hQpsd).monotoneOn _

/-- **Lemma D0.1(iii)**: φ(θ) ≥ φ(0) + θ·λ_min(Q) for θ ≥ 0. -/
theorem phi_ge_weyl {θ : ℝ} (hθ : 0 ≤ θ) :
    phi hH hQ hd 0 + θ * lamMin hQ hd ≤ phi hH hQ hd θ := by
  obtain ⟨x, hx, hφ⟩ := exists_phi_eq hH hQ hd θ
  rw [phi_zero, hφ]
  have h1 := lamMin_le_quad hd hH hx
  have h2 := lamMin_le_quad hd hQ hx
  nlinarith

include hQpsd in
/-- If ker Q = {0} then λ_min(Q) > 0 (S1.5, via S0.4). -/
lemma lamMin_pos_of_ker_eq_bot (hK : OCF.matKer Q = ⊥) : 0 < lamMin hQ hd := by
  obtain ⟨x, hx, hQx⟩ := exists_unit_eigvec_lamMin hQ hd
  have hq : x ⬝ᵥ Q *ᵥ x = lamMin hQ hd := by
    rw [hQx, dotProduct_smul, hx, smul_eq_mul, mul_one]
  rcases (quad_nonneg hQpsd x).lt_or_eq with h | h
  · rwa [← hq]
  · exfalso
    have h0 : Q *ᵥ x = 0 := by
      rw [← hQpsd.dotProduct_mulVec_zero_iff, star_trivial]; exact h.symm
    have hx0 : x ∈ OCF.matKer Q := by
      show Q.mulVecLin x = 0; rw [mulVecLin_apply]; exact h0
    rw [hK, Submodule.mem_bot] at hx0
    rw [hx0, dotProduct_zero] at hx
    exact zero_ne_one hx

include hQpsd in
/-- **Lemma D0.1(iv)**: φ is bounded above on [0, ∞) iff ker Q ≠ {0}. -/
theorem phi_bddAbove_iff :
    BddAbove (phi hH hQ hd '' Set.Ici 0) ↔ OCF.matKer Q ≠ ⊥ := by
  constructor
  · intro hb hK
    obtain ⟨M, hM⟩ := hb
    have hpos := lamMin_pos_of_ker_eq_bot hQ hd hQpsd hK
    set c := lamMin hQ hd
    set θ : ℝ := max 0 ((M - phi hH hQ hd 0) / c + 1) with hθdef
    have hθ0 : 0 ≤ θ := le_max_left _ _
    have hθ1 : (M - phi hH hQ hd 0) / c + 1 ≤ θ := le_max_right _ _
    have hle : phi hH hQ hd θ ≤ M := hM ⟨θ, hθ0, rfl⟩
    have hw := phi_ge_weyl hH hQ hd hθ0
    have : M - phi hH hQ hd 0 < θ * c := by
      have h3 : (M - phi hH hQ hd 0) / c * c = M - phi hH hQ hd 0 := div_mul_cancel₀ _ hpos.ne'
      nlinarith
    linarith
  · intro hK
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hK
    have hQv : Q *ᵥ v = 0 := by simpa [mulVecLin_apply] using hv
    have hvv : 0 < v ⬝ᵥ v := by
      rcases (dotProduct_self_star_nonneg v).lt_or_eq with h | h
      · simpa using h
      · exfalso; exact hv0 (dotProduct_star_self_eq_zero.mp (by simpa using h.symm))
    set y : Fin d → ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹ • v
    have hy : y ⬝ᵥ y = 1 := by
      simp only [y, smul_dotProduct, dotProduct_smul, smul_eq_mul]
      have hs := Real.mul_self_sqrt hvv.le
      have hs0 : Real.sqrt (v ⬝ᵥ v) ≠ 0 := (Real.sqrt_pos.mpr hvv).ne'
      field_simp
      linarith
    have hQy : Q *ᵥ y = 0 := by simp [y, mulVec_smul, hQv]
    refine ⟨y ⬝ᵥ H *ᵥ y, ?_⟩
    rintro _ ⟨θ, -, rfl⟩
    have := phi_le hH hQ hd θ hy
    rwa [hQy, dotProduct_zero, mul_zero, add_zero] at this

/-- **Lemma D0.1(i)–(iv)** bundled. For H symmetric, Q ⪰ 0 (d ≥ 1) and φ(θ) = λ_min(H + θQ):
(i) φ is concave on [0, ∞); (ii) φ is non-decreasing on [0, ∞); (iii) φ(θ) ≥ φ(0) + θλ_min(Q)
for θ ≥ 0, with φ(0) = λ_min(H); (iv) φ is bounded above on [0, ∞) iff ker Q ≠ {0}. -/
theorem lemma_D01_i_iv (hQpsd : Q.PosSemidef) :
    ConcaveOn ℝ (Set.Ici 0) (phi hH hQ hd) ∧
    MonotoneOn (phi hH hQ hd) (Set.Ici 0) ∧
    (phi hH hQ hd 0 = lamMin hH hd ∧
      ∀ θ, 0 ≤ θ → phi hH hQ hd 0 + θ * lamMin hQ hd ≤ phi hH hQ hd θ) ∧
    (BddAbove (phi hH hQ hd '' Set.Ici 0) ↔ OCF.matKer Q ≠ ⊥) :=
  ⟨phi_concaveOn hH hQ hd, phi_monotoneOn hH hQ hd hQpsd,
    ⟨phi_zero hH hQ hd, fun _ hθ => phi_ge_weyl hH hQ hd hθ⟩, phi_bddAbove_iff hH hQ hd hQpsd⟩

end RayLemma

/-! ## Lemma D0.1(v) and the approach bound (1.2) -/

section Limit

/-- Cauchy–Schwarz for the dot product, squared form. -/
lemma dot_sq_le {n : ℕ} (u v : Fin n → ℝ) : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
  simp only [dotProduct]
  have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simpa [sq] using this

open scoped Matrix.Norms.L2Operator in
/-- ‖Mw‖² ≤ ‖M‖₂²‖w‖² in dot-product form. -/
lemma mulVec_dot_le {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) (w : Fin p → ℝ) :
    (M *ᵥ w) ⬝ᵥ (M *ᵥ w) ≤ ‖M‖ ^ 2 * (w ⬝ᵥ w) := by
  have h := M.l2_opNorm_mulVec (WithLp.toLp 2 w)
  have heq : (EuclideanSpace.equiv (Fin m) ℝ).symm (M *ᵥ (WithLp.toLp 2 w :
      EuclideanSpace ℝ (Fin p)).ofLp) = WithLp.toLp 2 (M *ᵥ w) := by
    simp [EuclideanSpace.equiv]
  rw [heq] at h
  have h1 := OCF.norm_sq_eq_ofLp_dotProduct (WithLp.toLp 2 (M *ᵥ w) : EuclideanSpace ℝ (Fin m))
  have h2 := OCF.norm_sq_eq_ofLp_dotProduct (WithLp.toLp 2 w : EuclideanSpace ℝ (Fin p))
  rw [← h1, ← h2, ← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

open scoped Matrix.Norms.L2Operator in
/-- The cross-term bound (uᵀMw)² ≤ ‖M‖₂²·‖u‖²‖w‖². -/
lemma cross_sq_le {m p : ℕ} (M : Matrix (Fin m) (Fin p) ℝ) (u : Fin m → ℝ) (w : Fin p → ℝ) :
    (u ⬝ᵥ M *ᵥ w) ^ 2 ≤ ‖M‖ ^ 2 * (u ⬝ᵥ u) * (w ⬝ᵥ w) := by
  have h1 := dot_sq_le u (M *ᵥ w)
  have h2 := mulVec_dot_le M w
  have hu : 0 ≤ u ⬝ᵥ u := by simpa using dotProduct_self_star_nonneg u
  calc (u ⬝ᵥ M *ᵥ w) ^ 2 ≤ (u ⬝ᵥ u) * ((M *ᵥ w) ⬝ᵥ (M *ᵥ w)) := h1
    _ ≤ (u ⬝ᵥ u) * (‖M‖ ^ 2 * (w ⬝ᵥ w)) := mul_le_mul_of_nonneg_left h2 hu
    _ = ‖M‖ ^ 2 * (u ⬝ᵥ u) * (w ⬝ᵥ w) := by ring

/-- The scalar step of S1.6 (the 2×2 reduction solved): for a, b ≥ 0 with a² + b² = 1,
δ > 0 and ω ≥ 0, φ a² − 2ωab + (φ + δ) b² ≥ φ − ω²/δ. -/
lemma two_by_two {φ ω δ a b : ℝ} (hω : 0 ≤ ω) (hδ : 0 < δ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a ^ 2 + b ^ 2 = 1) :
    φ - ω ^ 2 / δ ≤ φ * a ^ 2 - 2 * ω * a * b + (φ + δ) * b ^ 2 := by
  have ha1 : a ≤ 1 := by nlinarith
  have key : 2 * ω * a * b - δ * b ^ 2 ≤ ω ^ 2 / δ := by
    rw [le_div_iff₀ hδ]
    have h1 : δ * ω * a * b ≤ δ * ω * b := by
      have : 0 ≤ δ * ω * b := by positivity
      nlinarith
    nlinarith [sq_nonneg (δ * b - ω)]
  have : φ * a ^ 2 - 2 * ω * a * b + (φ + δ) * b ^ 2 = φ - (2 * ω * a * b - δ * b ^ 2) := by
    have : a ^ 2 = 1 - b ^ 2 := by linarith
    rw [this]; ring
  rw [this]; linarith

variable {d m : ℕ} {H Q : Matrix (Fin d) (Fin d) ℝ}
  (hH : H.IsHermitian) (hQ : Q.IsHermitian) (hd : 0 < d) {P : Matrix (Fin d) (Fin m) ℝ}

/-- A nonzero kernel spanned by the columns of P forces m ≥ 1. -/
lemma m_pos (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q) (hK : OCF.matKer Q ≠ ⊥) :
    0 < m := by
  rcases Nat.eq_zero_or_pos m with h | h
  · exfalso; apply hK; rw [← hspan]; subst h
    rw [LinearMap.range_eq_bot]
    ext z i; simp [mulVec, dotProduct]
  · exact h

/-- (Ez)·r = z·(Eᵀr). -/
lemma mulVec_dot_eq {n k : ℕ} (E : Matrix (Fin n) (Fin k) ℝ) (z : Fin k → ℝ) (r : Fin n → ℝ) :
    (E *ᵥ z) ⬝ᵥ r = z ⬝ᵥ (Eᵀ *ᵥ r) := by
  rw [dotProduct_comm, dotProduct_mulVec, mulVec_transpose, dotProduct_comm]

/-- φ_∞ := λ_min(PᵀHP). -/
noncomputable def phiInf (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q)
    (hK : OCF.matKer Q ≠ ⊥) : ℝ :=
  lamMin (isHermitian_compress hH P) (m_pos hspan hK)

lemma mulVec_P_mem (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q) (z : Fin m → ℝ) :
    Q *ᵥ (P *ᵥ z) = 0 := by
  have : P *ᵥ z ∈ OCF.matKer Q := by rw [← hspan]; exact ⟨z, rfl⟩
  simpa [mulVecLin_apply] using this

lemma exists_of_ker (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q) {v : Fin d → ℝ}
    (hv : Q *ᵥ v = 0) : ∃ z, P *ᵥ z = v := by
  have : v ∈ LinearMap.range P.mulVecLin := by
    rw [hspan]; show Q.mulVecLin v = 0; simpa [mulVecLin_apply] using hv
  obtain ⟨z, hz⟩ := this
  exact ⟨z, by simpa [mulVecLin_apply] using hz⟩

/-- **Upper bound in Lemma D0.1(v)** (S1.4): φ(θ) ≤ φ_∞ for every θ. -/
theorem phi_le_phiInf (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q)
    (hK : OCF.matKer Q ≠ ⊥) (hPo : Pᵀ * P = 1) (θ : ℝ) :
    phi hH hQ hd θ ≤ phiInf hH hspan hK := by
  obtain ⟨z, hz, hzA⟩ := exists_unit_lamMin (isHermitian_compress hH P) (m_pos hspan hK)
  have h := phi_le hH hQ hd θ (x := P *ᵥ z) (by rw [dot_orthonormal hPo, hz])
  rw [mulVec_P_mem hspan, dotProduct_zero, mul_zero, add_zero, ← dot_compress, hzA] at h
  exact h

/-- **General lower bound (S1.6).** If the cross term, the H-form and the Q-form on the
orthogonal complement of range P are controlled by ω, c, q, then for θ ≥ 0 with
δ := θq + c − φ_∞ > 0, φ(θ) ≥ φ_∞ − ω²/δ. -/
theorem phi_ge_general (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q)
    (hK : OCF.matKer Q ≠ ⊥) (hPo : Pᵀ * P = 1) {ω c q θ : ℝ} (hω : 0 ≤ ω)
    (hcross : ∀ u r, Pᵀ *ᵥ r = 0 → ((P *ᵥ u) ⬝ᵥ H *ᵥ r) ^ 2 ≤ ω ^ 2 * (u ⬝ᵥ u) * (r ⬝ᵥ r))
    (hc : ∀ r, Pᵀ *ᵥ r = 0 → c * (r ⬝ᵥ r) ≤ r ⬝ᵥ H *ᵥ r)
    (hq : ∀ r, Pᵀ *ᵥ r = 0 → q * (r ⬝ᵥ r) ≤ r ⬝ᵥ Q *ᵥ r)
    (hθ : 0 ≤ θ) (hδ : 0 < θ * q + c - phiInf hH hspan hK) :
    phiInf hH hspan hK - ω ^ 2 / (θ * q + c - phiInf hH hspan hK) ≤ phi hH hQ hd θ := by
  set φ := phiInf hH hspan hK with hφdef
  set δ := θ * q + c - φ with hδdef
  obtain ⟨x, hx, hφx⟩ := exists_phi_eq hH hQ hd θ
  set u := Pᵀ *ᵥ x with hu
  set r := x - P *ᵥ u with hr
  have hPr : Pᵀ *ᵥ r = 0 := by
    rw [hr, mulVec_sub, transpose_mulVec_mulVec hPo, sub_self]
  have hxdec : x = P *ᵥ u + r := by rw [hr]; abel
  have hPu_r : (P *ᵥ u) ⬝ᵥ r = 0 := by rw [mulVec_dot_eq, hPr, dotProduct_zero]
  have hQPu : Q *ᵥ (P *ᵥ u) = 0 := mulVec_P_mem hspan u
  have hxx : x ⬝ᵥ x = u ⬝ᵥ u + r ⬝ᵥ r := by
    rw [hxdec]
    simp only [dotProduct_add, add_dotProduct]
    rw [dot_orthonormal hPo, hPu_r, dotProduct_comm r, hPu_r]; ring
  have hxQ : x ⬝ᵥ Q *ᵥ x = r ⬝ᵥ Q *ᵥ r := by
    rw [hxdec]
    simp only [mulVec_add, dotProduct_add, add_dotProduct, hQPu, dotProduct_zero]
    rw [dot_mulVec_comm hQ (P *ᵥ u) r, hQPu, dotProduct_zero]; ring
  have hxH : x ⬝ᵥ H *ᵥ x = (P *ᵥ u) ⬝ᵥ H *ᵥ (P *ᵥ u) + 2 * ((P *ᵥ u) ⬝ᵥ H *ᵥ r)
      + r ⬝ᵥ H *ᵥ r := by
    rw [hxdec]
    simp only [mulVec_add, dotProduct_add, add_dotProduct]
    rw [dot_mulVec_comm hH r (P *ᵥ u)]; ring
  have hPHP : φ * (u ⬝ᵥ u) ≤ (P *ᵥ u) ⬝ᵥ H *ᵥ (P *ᵥ u) := by
    rw [← dot_compress]; exact lamMin_mul_le _ _ u
  have huu : 0 ≤ u ⬝ᵥ u := by simpa using dotProduct_self_star_nonneg u
  have hrr : 0 ≤ r ⬝ᵥ r := by simpa using dotProduct_self_star_nonneg r
  set a := Real.sqrt (u ⬝ᵥ u)
  set b := Real.sqrt (r ⬝ᵥ r)
  have ha2 : a ^ 2 = u ⬝ᵥ u := Real.sq_sqrt huu
  have hb2 : b ^ 2 = r ⬝ᵥ r := Real.sq_sqrt hrr
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hcr : -(ω * a * b) ≤ (P *ᵥ u) ⬝ᵥ H *ᵥ r := by
    have h1 := hcross u r hPr
    rw [← ha2, ← hb2] at h1
    have hs : 0 ≤ ω * a * b := by positivity
    by_contra hcon
    have hcon := lt_of_not_ge hcon
    nlinarith
  have hQr := mul_le_mul_of_nonneg_left (hq r hPr) hθ
  have hHr := hc r hPr
  have hab : a ^ 2 + b ^ 2 = 1 := by rw [ha2, hb2, ← hxx, hx]
  have h2 := two_by_two (φ := φ) hω hδ ha0 hb0 hab
  rw [hφx, hxH, hxQ]
  rw [← ha2] at hPHP
  rw [← hb2] at hQr hHr
  have : (φ + δ) * b ^ 2 = c * b ^ 2 + θ * (q * b ^ 2) := by rw [hδdef]; ring
  nlinarith

include hQ in
/-- On the orthogonal complement of ker Q = range P, xᵀQx ≥ q‖x‖² for some q > 0
(via the smallest nonzero eigenvalue λ⁺(Q) of G12, S1.6's Q_⊥ ≻ 0). -/
lemma exists_q_pos (hQpsd : Q.PosSemidef) (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q)
    (hPo : Pᵀ * P = 1) :
    ∃ q : ℝ, 0 < q ∧ ∀ r, Pᵀ *ᵥ r = 0 → q * (r ⬝ᵥ r) ≤ r ⬝ᵥ Q *ᵥ r := by
  have hr0 : ∀ r, Pᵀ *ᵥ r = 0 → Q *ᵥ r = 0 → r = 0 := by
    intro r hPr hQr
    obtain ⟨z, rfl⟩ := exists_of_ker hspan hQr
    rw [transpose_mulVec_mulVec hPo] at hPr
    rw [hPr, mulVec_zero]
  by_cases hQ0 : Q = 0
  · refine ⟨1, one_pos, fun r hPr => ?_⟩
    have := hr0 r hPr (by rw [hQ0, zero_mulVec])
    subst this; simp
  · set S : Set ℝ := {μ | ∃ j, hQ.eigenvalues j = μ ∧ μ ≠ 0}
    have hne : S.Nonempty := by
      by_contra hS
      apply hQ0
      rw [← hQ.eigenvalues_eq_zero_iff]
      funext j
      by_contra hj
      exact hS ⟨_, j, rfl, hj⟩
    have hfin : S.Finite := (Set.finite_range hQ.eigenvalues).subset
      (by rintro μ ⟨i, rfl, -⟩; exact ⟨i, rfl⟩)
    have hlp : OCF.G12.lambdaPlus Q = sInf S := by
      rw [OCF.G12.lambdaPlus, dif_pos hQ]
    have hmem := hne.csInf_mem hfin
    rw [← hlp] at hmem
    obtain ⟨j, hj, hj0⟩ := hmem
    have hpos : 0 < OCF.G12.lambdaPlus Q := by
      have := hQpsd.eigenvalues_nonneg j
      rw [← hj]; exact lt_of_le_of_ne this (Ne.symm (hj ▸ hj0))
    refine ⟨_, hpos, fun r hPr => ?_⟩
    obtain ⟨y, hy, hle⟩ := OCF.G12.exists_ker_lambdaPlus_le hQ r
    have hQy : Q *ᵥ y = 0 := by simpa [mulVecLin_apply] using hy
    obtain ⟨z, rfl⟩ := exists_of_ker hspan hQy
    have hexp : (r - P *ᵥ z) ⬝ᵥ (r - P *ᵥ z) = r ⬝ᵥ r + z ⬝ᵥ z := by
      have h1 : (P *ᵥ z) ⬝ᵥ r = 0 := by rw [mulVec_dot_eq, hPr, dotProduct_zero]
      have h2 : r ⬝ᵥ (P *ᵥ z) = 0 := by rw [dotProduct_comm]; exact h1
      simp only [dotProduct_sub, sub_dotProduct]
      rw [dot_orthonormal hPo, h1, h2]; ring
    rw [hexp] at hle
    have hzz : 0 ≤ z ⬝ᵥ z := by simpa using dotProduct_self_star_nonneg z
    nlinarith

open scoped Matrix.Norms.L2Operator in
/-- **Lemma D0.1(v)**: if ker Q ≠ {0} and the columns of P are orthonormal and span ker Q,
then φ(θ) ≤ φ_∞ = λ_min(PᵀHP) for every θ, and φ(θ) → φ_∞ as θ → ∞. -/
theorem phi_tendsto_phiInf (hQpsd : Q.PosSemidef)
    (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q) (hK : OCF.matKer Q ≠ ⊥)
    (hPo : Pᵀ * P = 1) :
    (∀ θ, phi hH hQ hd θ ≤ phiInf hH hspan hK) ∧
      Tendsto (phi hH hQ hd) atTop (𝓝 (phiInf hH hspan hK)) := by
  refine ⟨phi_le_phiInf hH hQ hd hspan hK hPo, ?_⟩
  obtain ⟨q, hq, hqb⟩ := exists_q_pos hQ hQpsd hspan hPo
  set φ := phiInf hH hspan hK
  set c := lamMin hH hd
  set ω := ‖H‖
  have hcross : ∀ u r, Pᵀ *ᵥ r = 0 → ((P *ᵥ u) ⬝ᵥ H *ᵥ r) ^ 2 ≤ ω ^ 2 * (u ⬝ᵥ u) * (r ⬝ᵥ r) := by
    intro u r _
    have := cross_sq_le H (P *ᵥ u) r
    rwa [dot_orthonormal hPo] at this
  have hc : ∀ r, Pᵀ *ᵥ r = 0 → c * (r ⬝ᵥ r) ≤ r ⬝ᵥ H *ᵥ r := fun r _ => lamMin_mul_le hH hd r
  have hden : Tendsto (fun θ : ℝ => θ * q + c - φ) atTop atTop := by
    have := tendsto_id.atTop_mul_const hq
    exact tendsto_atTop_add_const_right _ _ (tendsto_atTop_add_const_right _ _ this)
  have hlow : Tendsto (fun θ : ℝ => φ - ω ^ 2 / (θ * q + c - φ)) atTop (𝓝 φ) := by
    have := (tendsto_const_nhds (x := ω ^ 2)).div_atTop hden
    simpa using (tendsto_const_nhds (x := φ)).sub this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_
    (Eventually.of_forall (phi_le_phiInf hH hQ hd hspan hK hPo))
  filter_upwards [eventually_ge_atTop 0, hden.eventually_gt_atTop 0] with θ hθ hδ
  exact phi_ge_general hH hQ hd hspan hK hPo (norm_nonneg _) hcross hc hqb hθ hδ

include hQ hd in
/-- φ_∞ does not depend on the choice of orthonormal basis P of ker Q (S0.1), as a
consequence of the uniqueness of the limit. -/
theorem phiInf_indep (hQpsd : Q.PosSemidef) {m' : ℕ} {P' : Matrix (Fin d) (Fin m') ℝ}
    (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q)
    (hspan' : LinearMap.range P'.mulVecLin = OCF.matKer Q) (hK : OCF.matKer Q ≠ ⊥)
    (hPo : Pᵀ * P = 1) (hPo' : P'ᵀ * P' = 1) :
    phiInf hH hspan hK = phiInf hH hspan' hK :=
  tendsto_nhds_unique (phi_tendsto_phiInf hH hQ hd hQpsd hspan hK hPo).2
    (phi_tendsto_phiInf hH hQ hd hQpsd hspan' hK hPo').2

/-- q_⊥ := λ_min(P_⊥ᵀQP_⊥). -/
noncomputable def qPerp {p : ℕ} (hQ : Q.IsHermitian) (Pp : Matrix (Fin d) (Fin p) ℝ)
    (hp : 0 < p) : ℝ :=
  lamMin (isHermitian_compress hQ Pp) hp

/-- c_⊥ := λ_min(P_⊥ᵀHP_⊥). -/
noncomputable def cPerp {p : ℕ} (hH : H.IsHermitian) (Pp : Matrix (Fin d) (Fin p) ℝ)
    (hp : 0 < p) : ℝ :=
  lamMin (isHermitian_compress hH Pp) hp

open scoped Matrix.Norms.L2Operator in
/-- ω := ‖PᵀHP_⊥‖₂ (the induced 2-norm). -/
noncomputable def omegaCross {p : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (P : Matrix (Fin d) (Fin m) ℝ)
    (Pp : Matrix (Fin d) (Fin p) ℝ) : ℝ :=
  ‖Pᵀ * H * Pp‖

open scoped Matrix.Norms.L2Operator in
lemma omegaCross_nonneg {p : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (P : Matrix (Fin d) (Fin m) ℝ)
    (Pp : Matrix (Fin d) (Fin p) ℝ) : 0 ≤ omegaCross H P Pp := norm_nonneg _

/-- **S1.6, Q_⊥ ≻ 0**: q_⊥ > 0 when [P P_⊥] is orthogonal and P spans ker Q. -/
theorem qPerp_pos (hQpsd : Q.PosSemidef) (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q)
    {p : ℕ} (hp : 0 < p) {Pp : Matrix (Fin d) (Fin p) ℝ} (hPpo : Ppᵀ * Pp = 1)
    (hPPp : Pᵀ * Pp = 0) : 0 < qPerp hQ Pp hp := by
  obtain ⟨w, hw, hwA⟩ := exists_unit_lamMin (isHermitian_compress hQ Pp) hp
  rw [qPerp, ← hwA, dot_compress]
  rcases (quad_nonneg hQpsd (Pp *ᵥ w)).lt_or_eq with h | h
  · exact h
  · exfalso
    have h0 : Q *ᵥ (Pp *ᵥ w) = 0 := by
      rw [← hQpsd.dotProduct_mulVec_zero_iff, star_trivial]; exact h.symm
    obtain ⟨z, hz⟩ := exists_of_ker hspan h0
    have : w = 0 := by
      have e := congrArg (fun v => Ppᵀ *ᵥ v) hz
      rw [transpose_mulVec_mulVec hPpo, mulVec_mulVec,
        show Ppᵀ * P = (Pᵀ * Pp)ᵀ by rw [transpose_mul, transpose_transpose], hPPp,
        transpose_zero, zero_mulVec] at e
      exact e.symm
    rw [this, dotProduct_zero] at hw
    exact zero_ne_one hw

/-- **The approach bound (1.2)** (Lemma D0.1(v) with Remark D0.2(ii)). Let [P P_⊥] be
orthogonal with the columns of P spanning ker Q ≠ {0} and P_⊥ having p ≥ 1 columns. Put
q_⊥ := λ_min(P_⊥ᵀQP_⊥) (> 0), c_⊥ := λ_min(P_⊥ᵀHP_⊥), ω := ‖PᵀHP_⊥‖₂. Then for every
θ ≥ 0 with θ > θ₀ := (φ_∞ − c_⊥)/q_⊥,
  φ_∞ − ω²/(θq_⊥ + c_⊥ − φ_∞) ≤ φ(θ) ≤ φ_∞. -/
theorem approach_bound (hQpsd : Q.PosSemidef)
    (hspan : LinearMap.range P.mulVecLin = OCF.matKer Q) (hK : OCF.matKer Q ≠ ⊥)
    (hPo : Pᵀ * P = 1) {p : ℕ} (hp : 0 < p) {Pp : Matrix (Fin d) (Fin p) ℝ}
    (hPpo : Ppᵀ * Pp = 1) (hPPp : Pᵀ * Pp = 0) (hcomp : P * Pᵀ + Pp * Ppᵀ = 1)
    {θ : ℝ} (hθ : 0 ≤ θ)
    (hθ₀ : (phiInf hH hspan hK - cPerp hH Pp hp) / qPerp hQ Pp hp < θ) :
    phiInf hH hspan hK - omegaCross H P Pp ^ 2 /
        (θ * qPerp hQ Pp hp + cPerp hH Pp hp - phiInf hH hspan hK) ≤ phi hH hQ hd θ ∧
      phi hH hQ hd θ ≤ phiInf hH hspan hK := by
  refine ⟨?_, phi_le_phiInf hH hQ hd hspan hK hPo θ⟩
  have hq := qPerp_pos hQ hQpsd hspan hp hPpo hPPp
  have hδ : 0 < θ * qPerp hQ Pp hp + cPerp hH Pp hp - phiInf hH hspan hK := by
    rw [div_lt_iff₀ hq] at hθ₀; linarith
  -- every r ⊥ range P is P_⊥ w with w = P_⊥ᵀ r, and ‖r‖ = ‖w‖
  have hdec : ∀ r, Pᵀ *ᵥ r = 0 → Pp *ᵥ (Ppᵀ *ᵥ r) = r := by
    intro r hPr
    have e := congrArg (fun M => M *ᵥ r) hcomp
    simp only [add_mulVec, ← mulVec_mulVec, hPr, mulVec_zero, zero_add, one_mulVec] at e
    exact e
  have hnorm : ∀ r, Pᵀ *ᵥ r = 0 → (Ppᵀ *ᵥ r) ⬝ᵥ (Ppᵀ *ᵥ r) = r ⬝ᵥ r := by
    intro r hPr
    conv_rhs => rw [← hdec r hPr]
    rw [dot_orthonormal hPpo]
  refine phi_ge_general hH hQ hd hspan hK hPo (omegaCross_nonneg H P Pp) ?_ ?_ ?_ hθ hδ
  · intro u r hPr
    have h := cross_sq_le (Pᵀ * H * Pp) u (Ppᵀ *ᵥ r)
    rw [dot_compress2, hdec r hPr, hnorm r hPr] at h
    exact h
  · intro r hPr
    have h := lamMin_mul_le (isHermitian_compress hH Pp) hp (Ppᵀ *ᵥ r)
    rw [dot_compress, hdec r hPr, hnorm r hPr] at h
    exact h
  · intro r hPr
    have h := lamMin_mul_le (isHermitian_compress hQ Pp) hp (Ppᵀ *ᵥ r)
    rw [dot_compress, hdec r hPr, hnorm r hPr] at h
    exact h

end Limit

/-! ## Lemma D0.6 — the restricted curvature is never worse -/

section Restricted

/-- λ_max is attained at a unit vector (for the `OCF.lambdaMax` of T1GramBound). -/
lemma exists_unit_lambdaMax {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hn : 0 < n) : ∃ x : Fin n → ℝ, x ⬝ᵥ x = 1 ∧ x ⬝ᵥ A *ᵥ x = OCF.lambdaMax A := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := hA.eigenvalues)
  have hlm : OCF.lambdaMax A = hA.eigenvalues j := by
    rw [OCF.lambdaMax, dif_pos hA, hj]
  refine ⟨(hA.eigenvectorBasis j).ofLp, ?_, ?_⟩
  · have := OCF.ofLp_dotProduct_of_orthonormal hA.eigenvectorBasis.orthonormal j j
    simpa using this
  · have hx := OCF.ofLp_dotProduct_of_orthonormal hA.eigenvectorBasis.orthonormal j j
    simp only [if_true] at hx
    rw [hlm, hA.mulVec_eigenvectorBasis j, dotProduct_smul, hx, smul_eq_mul, mul_one]

lemma lamMin_le_lambdaMax {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    (hn : 0 < n) : lamMin hA hn ≤ OCF.lambdaMax A := by
  obtain ⟨x, hx, hxA⟩ := exists_unit_lambdaMax hA hn
  have := lamMin_mul_le hA hn x
  rw [hx, mul_one, hxA] at this
  exact this

lemma lambdaMax_compress_le {n k : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian)
    {E : Matrix (Fin n) (Fin k) ℝ} (hE : Eᵀ * E = 1) (hk : 0 < k) :
    OCF.lambdaMax (Eᵀ * A * E) ≤ OCF.lambdaMax A := by
  obtain ⟨z, hz, hzA⟩ := exists_unit_lambdaMax (isHermitian_compress hA E) hk
  have h := OCF.dotProduct_mulVec_le_lambdaMax hA (E *ᵥ z)
  rw [dot_orthonormal hE, hz, mul_one, ← dot_compress, hzA] at h
  exact h

variable {d : ℕ} {H : Matrix (Fin d) (Fin d) ℝ}

/-- The principal submatrix H_SS (rows and columns in S, in increasing order). -/
def subMat (H : Matrix (Fin d) (Fin d) ℝ) (S : Finset (Fin d)) :
    Matrix (Fin S.card) (Fin S.card) ℝ :=
  H.submatrix (S.orderEmbOfFin rfl) (S.orderEmbOfFin rfl)

/-- The coordinate-injection matrix of S (columns e_i, i ∈ S). -/
def injMat (S : Finset (Fin d)) : Matrix (Fin d) (Fin S.card) ℝ :=
  (1 : Matrix (Fin d) (Fin d) ℝ).submatrix id (S.orderEmbOfFin rfl)

lemma subMat_eq (H : Matrix (Fin d) (Fin d) ℝ) (S : Finset (Fin d)) :
    subMat H S = (injMat S)ᵀ * H * injMat S := by
  ext i j
  simp [subMat, injMat, mul_apply, one_apply]

lemma injMat_orthonormal (S : Finset (Fin d)) : (injMat S)ᵀ * injMat S = 1 := by
  ext i j
  simp [injMat, mul_apply, one_apply]

lemma isHermitian_subMat (hH : H.IsHermitian) (S : Finset (Fin d)) :
    (subMat H S).IsHermitian := by
  rw [subMat_eq]; exact isHermitian_compress hH _

/-- λ_S := λ_min(H_SS). -/
noncomputable def lamS (hH : H.IsHermitian) {S : Finset (Fin d)} (hS : S.Nonempty) : ℝ :=
  lamMin (isHermitian_subMat hH S) (Finset.card_pos.mpr hS)

/-- Λ_S := λ_max(H_SS). -/
noncomputable def LamS (H : Matrix (Fin d) (Fin d) ℝ) (S : Finset (Fin d)) : ℝ :=
  OCF.lambdaMax (subMat H S)

/-- ρ* := max{|1 − αλ_S|, |1 − αΛ_S|}. -/
noncomputable def rhoStar (hH : H.IsHermitian) {S : Finset (Fin d)} (hS : S.Nonempty)
    (α : ℝ) : ℝ :=
  max |1 - α * lamS hH hS| |1 - α * LamS H S|

/-- q_B3(a) := max{|1 − αa|, |1 − αβ|}. -/
def qB3 (α β a : ℝ) : ℝ := max |1 - α * a| |1 - α * β|

/-- t ↦ |1 − αt| on [a, b]: the middle value is dominated by the endpoints. -/
lemma abs_mid_le {α a t b : ℝ} (hα : 0 ≤ α) (hat : a ≤ t) (htb : t ≤ b) :
    |1 - α * t| ≤ max |1 - α * a| |1 - α * b| := by
  have h1 : α * a ≤ α * t := mul_le_mul_of_nonneg_left hat hα
  have h2 : α * t ≤ α * b := mul_le_mul_of_nonneg_left htb hα
  rcases le_total 0 (1 - α * t) with h | h
  · rw [abs_of_nonneg h]
    exact le_max_of_le_left (le_trans (by linarith) (le_abs_self _))
  · rw [abs_of_nonpos h]
    exact le_max_of_le_right (le_trans (by linarith) (neg_le_abs _))

lemma qB3_antitoneOn_Iic {α β : ℝ} (hα : 0 ≤ α) : AntitoneOn (qB3 α β) (Set.Iic β) := by
  intro a ha a' ha' haa'
  simp only [Set.mem_Iic] at ha ha'
  simp only [qB3]
  exact max_le (abs_mid_le hα haa' ha') (le_max_right _ _)

variable (hH : H.IsHermitian) (hd : 0 < d) {S : Finset (Fin d)} (hS : S.Nonempty)

lemma pos_of_nonempty {S : Finset (Fin d)} (hS : S.Nonempty) : 0 < d := by
  obtain ⟨i, -⟩ := hS; exact i.pos

/-- **Lemma D0.6(a)**: λ_min(H) ≤ λ_min(H_SS) ≤ λ_max(H_SS) ≤ λ_max(H). -/
theorem D06_a : lamMin hH hd ≤ lamS hH hS ∧ lamS hH hS ≤ LamS H S ∧
    LamS H S ≤ OCF.lambdaMax H := by
  have hk := Finset.card_pos.mpr hS
  refine ⟨?_, lamMin_le_lambdaMax _ hk, ?_⟩
  · have h := lamMin_le_lamMin_compress hH hd (injMat_orthonormal S) hk
    rw [lamS]
    rwa [lamMin_congr (subMat_eq H S) (isHermitian_subMat hH S)
      (isHermitian_compress hH _) hk]
  · rw [LamS, subMat_eq]
    exact lambdaMax_compress_le hH (injMat_orthonormal S) hk

/-- **Lemma D0.6(b)**: ρ* ≤ max{|1 − αλ_min(H_SS)|, |1 − αβ|} = q_B3(λ_S). -/
theorem D06_b {α β : ℝ} (hα : 0 ≤ α) (hβ : OCF.lambdaMax H ≤ β) :
    rhoStar hH hS α ≤ qB3 α β (lamS hH hS) := by
  obtain ⟨-, h2, h3⟩ := D06_a hH (pos_of_nonempty hS) hS
  exact max_le (le_max_left _ _) (abs_mid_le hα h2 (h3.trans hβ))

/-- **Lemma D0.6(c)**, monotonicity: q_B3 is non-increasing on [0, β]. -/
theorem D06_c_antitone {α β : ℝ} (hα : 0 ≤ α) : AntitoneOn (qB3 α β) (Set.Icc 0 β) :=
  (qB3_antitoneOn_Iic hα).mono (fun _ h => h.2)

/-- **Lemma D0.6(c)**, chain: q_B3(λ_S) ≤ q_B3(λ_min(H)) ≤ q_B3(σ_f) for σ_f ≤ λ_min(H). -/
theorem D06_c_chain {α β σ : ℝ} (hα : 0 ≤ α) (hβ : OCF.lambdaMax H ≤ β)
    (hσ : σ ≤ lamMin hH hd) :
    qB3 α β (lamS hH hS) ≤ qB3 α β (lamMin hH hd) ∧ qB3 α β (lamMin hH hd) ≤ qB3 α β σ := by
  obtain ⟨h1, h2, h3⟩ := D06_a hH hd hS
  have hSβ : lamS hH hS ≤ β := h2.trans (h3.trans hβ)
  have hmβ : lamMin hH hd ≤ β := h1.trans hSβ
  exact ⟨qB3_antitoneOn_Iic hα hmβ hSβ h1,
    qB3_antitoneOn_Iic hα (hσ.trans hmβ) hmβ hσ⟩

/-- **Lemma D0.6(d)**, division-free form: if α(λ_S + Λ_S) ≤ 2 then ρ* = 1 − αλ_S. -/
theorem D06_d {α : ℝ} (hα : 0 ≤ α) (h2 : α * (lamS hH hS + LamS H S) ≤ 2) :
    rhoStar hH hS α = 1 - α * lamS hH hS := by
  obtain ⟨-, hle, -⟩ := D06_a hH (pos_of_nonempty hS) hS
  have hm : α * lamS hH hS ≤ α * LamS H S := mul_le_mul_of_nonneg_left hle hα
  have h0 : 0 ≤ 1 - α * lamS hH hS := by nlinarith
  rw [rhoStar, abs_of_nonneg h0]
  refine max_eq_left ?_
  rcases le_total 0 (1 - α * LamS H S) with h | h
  · rw [abs_of_nonneg h]; linarith
  · rw [abs_of_nonpos h]; nlinarith

/-- **Lemma D0.6(d)**, the case α ≤ 1/β: ρ* = 1 − αλ_S. -/
theorem D06_d_of_le_inv {α β : ℝ} (hβ0 : 0 < β) (hα : 0 < α) (hα1 : α ≤ 1 / β)
    (hβ : OCF.lambdaMax H ≤ β) : rhoStar hH hS α = 1 - α * lamS hH hS := by
  obtain ⟨-, h2, h3⟩ := D06_a hH (pos_of_nonempty hS) hS
  have hαβ : α * β ≤ 1 := by rwa [le_div_iff₀ hβ0] at hα1
  apply D06_d hH hS hα.le
  have : lamS hH hS + LamS H S ≤ 2 * β := by linarith
  nlinarith

/-- **Remark D0.6.1** (strictness): for α ∈ (0, 1/β] and 0 ≤ σ_f ≤ λ_min(H),
q_B3(σ_f) = 1 − ασ_f and q_B3(σ_f) − ρ* = α(λ_S − σ_f). -/
theorem D06_remark1 {α β σ : ℝ} (hβ0 : 0 < β) (hα : 0 < α) (hα1 : α ≤ 1 / β)
    (hβ : OCF.lambdaMax H ≤ β) (hσ : σ ≤ lamMin hH hd) :
    qB3 α β σ = 1 - α * σ ∧ qB3 α β σ - rhoStar hH hS α = α * (lamS hH hS - σ) := by
  obtain ⟨h1, h2, h3⟩ := D06_a hH hd hS
  have hαβ : α * β ≤ 1 := by rwa [le_div_iff₀ hβ0] at hα1
  have hσβ : σ ≤ β := by linarith
  have hq : qB3 α β σ = 1 - α * σ := by
    have hασ : α * σ ≤ α * β := mul_le_mul_of_nonneg_left hσβ hα.le
    have e1 : |1 - α * σ| = 1 - α * σ := abs_of_nonneg (by linarith)
    have e2 : |1 - α * β| = 1 - α * β := abs_of_nonneg (by linarith)
    rw [qB3, e1, e2]; exact max_eq_left (by linarith)
  refine ⟨hq, ?_⟩
  rw [hq, D06_d_of_le_inv hH hS hβ0 hα hα1 hβ]; ring

/-- **Lemma D0.6** bundled ((a)–(d)), under H_d: H symmetric with λ_max(H) ≤ β, ∅ ≠ S,
α > 0 (the hypotheses H ⪰ 0 and α < 2/β of H_d are not needed). -/
theorem lemma_D06 {α β σ : ℝ} (hα : 0 < α) (hβ : OCF.lambdaMax H ≤ β)
    (hσ : σ ≤ lamMin hH hd) :
    (lamMin hH hd ≤ lamS hH hS ∧ LamS H S ≤ OCF.lambdaMax H) ∧
    rhoStar hH hS α ≤ max |1 - α * lamS hH hS| |1 - α * β| ∧
    (AntitoneOn (qB3 α β) (Set.Icc 0 β) ∧
      qB3 α β (lamS hH hS) ≤ qB3 α β (lamMin hH hd) ∧ qB3 α β (lamMin hH hd) ≤ qB3 α β σ) ∧
    (α * (lamS hH hS + LamS H S) ≤ 2 → rhoStar hH hS α = 1 - α * lamS hH hS) ∧
    (0 < β → α ≤ 1 / β → rhoStar hH hS α = 1 - α * lamS hH hS) := by
  obtain ⟨h1, -, h3⟩ := D06_a hH hd hS
  exact ⟨⟨h1, h3⟩, D06_b hH hS hα.le hβ, ⟨D06_c_antitone hα.le,
    D06_c_chain hH hd hS hα.le hβ hσ⟩, D06_d hH hS hα.le,
    fun hβ0 hα1 => D06_d_of_le_inv hH hS hβ0 hα hα1 hβ⟩

end Restricted

/-! ## Lemma D0.4 — the ℓ1 term is invisible to the Hessian -/

section L1

variable {d : ℕ}

/-- g := λ‖·‖₁ on ℝᵈ. -/
noncomputable def gL1 (lam : ℝ) (x : Fin d → ℝ) : ℝ := lam * ∑ i, |x i|

/-- Ω := {x : xᵢ ≠ 0 for all i}. -/
def Omega (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ i, x i ≠ 0}

/-- **Lemma D0.4**: Ω is open. -/
theorem Omega_isOpen : IsOpen (Omega d) := by
  have : Omega d = ⋂ i, {x : Fin d → ℝ | x i ≠ 0} := by ext x; simp [Omega]
  rw [this]
  exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const

/-- **Lemma D0.4**: Ω is dense. -/
theorem Omega_dense : Dense (Omega d) := by
  rw [dense_iff_closure_eq]
  refine Set.eq_univ_of_forall fun x => Metric.mem_closure_iff.mpr fun ε hε => ?_
  refine ⟨fun i => if x i = 0 then ε / 2 else x i, fun i => ?_, ?_⟩
  · by_cases h : x i = 0 <;> simp [h, hε.ne']
  · rw [dist_eq_norm]
    refine lt_of_le_of_lt ((pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i => ?_)
      (half_lt_self hε)
    by_cases h : x i = 0
    · simp [h, abs_of_pos hε]
    · simp [h]; linarith

/-- The linear map y ↦ λ·Σᵢ sign(xᵢ)yᵢ. -/
noncomputable def signLin (lam : ℝ) (x : Fin d → ℝ) : (Fin d → ℝ) →L[ℝ] ℝ :=
  lam • ∑ i, Real.sign (x i) • ContinuousLinearMap.proj i

lemma signLin_apply (lam : ℝ) (x y : Fin d → ℝ) :
    signLin lam x y = lam * ∑ i, Real.sign (x i) * y i := by
  simp [signLin]

/-- The open sign-cell of x. -/
def cell (x : Fin d → ℝ) : Set (Fin d → ℝ) := {y | ∀ i, 0 < y i * x i}

lemma cell_isOpen (x : Fin d → ℝ) : IsOpen (cell x) := by
  have : cell x = ⋂ i, {y : Fin d → ℝ | 0 < y i * x i} := by ext y; simp [cell]
  rw [this]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_lt continuous_const ((continuous_apply i).mul continuous_const)

lemma mem_cell {x : Fin d → ℝ} (hx : x ∈ Omega d) : x ∈ cell x := fun i =>
  mul_self_pos.mpr (hx i)

lemma gL1_eq_on_cell (lam : ℝ) {x y : Fin d → ℝ} (hy : y ∈ cell x) :
    gL1 lam y = signLin lam x y := by
  rw [gL1, signLin_apply]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := hy i
  rcases lt_trichotomy (x i) 0 with hx | hx | hx
  · have : y i < 0 := by nlinarith
    rw [Real.sign_of_neg hx, abs_of_neg this]; ring
  · rw [hx, mul_zero] at h; exact absurd h (lt_irrefl 0)
  · have : 0 < y i := by nlinarith
    rw [Real.sign_of_pos hx, abs_of_pos this]; ring

lemma gL1_eventuallyEq (lam : ℝ) {x y : Fin d → ℝ} (hy : y ∈ cell x) :
    gL1 lam =ᶠ[𝓝 y] signLin lam x :=
  Filter.mem_of_superset ((cell_isOpen x).mem_nhds hy) fun _ hz => gL1_eq_on_cell lam hz

/-- **Lemma D0.4**: g is C^n (every n, including ∞ and ω) on Ω. -/
theorem gL1_contDiffAt (lam : ℝ) (n : WithTop ℕ∞) {x : Fin d → ℝ} (hx : x ∈ Omega d) :
    ContDiffAt ℝ n (gL1 lam) x :=
  (signLin lam x).contDiff.contDiffAt.congr_of_eventuallyEq (gL1_eventuallyEq lam (mem_cell hx))

theorem gL1_contDiffOn (lam : ℝ) (n : WithTop ℕ∞) : ContDiffOn ℝ n (gL1 lam) (Omega d) :=
  fun _ hx => (gL1_contDiffAt lam n hx).contDiffWithinAt

/-- ∇g is locally constant on Ω. -/
lemma fderiv_gL1_eventuallyEq (lam : ℝ) {x : Fin d → ℝ} (hx : x ∈ Omega d) :
    fderiv ℝ (gL1 lam) =ᶠ[𝓝 x] fun _ => signLin lam x := by
  refine Filter.mem_of_superset ((cell_isOpen x).mem_nhds (mem_cell hx)) fun y hy => ?_
  show fderiv ℝ (gL1 lam) y = signLin lam x
  rw [(gL1_eventuallyEq lam hy).fderiv_eq]
  exact (signLin lam x).fderiv

/-- **Lemma D0.4**: ∇²g ≡ 0 on Ω. -/
theorem gL1_hessian_zero (lam : ℝ) {x : Fin d → ℝ} (hx : x ∈ Omega d) :
    fderiv ℝ (fderiv ℝ (gL1 lam)) x = 0 := by
  rw [(fderiv_gL1_eventuallyEq lam hx).fderiv_eq]
  exact fderiv_const_apply _

/-- **Lemma D0.4**: for λ > 0, g is not differentiable at any point outside Ω. -/
theorem gL1_not_differentiableAt {lam : ℝ} (hlam : 0 < lam) {x : Fin d → ℝ}
    (hx : x ∉ Omega d) : ¬ DifferentiableAt ℝ (gL1 lam) x := by
  intro hg
  simp only [Omega, Set.mem_setOf_eq, not_forall, not_not] at hx
  obtain ⟨i, hi⟩ := hx
  set e : Fin d → ℝ := Pi.single i 1
  have hline : DifferentiableAt ℝ (fun t : ℝ => x + t • e) 0 := by fun_prop
  have hg0 : DifferentiableAt ℝ (gL1 lam) (x + (0 : ℝ) • e) := by simpa using hg
  have hcomp := hg0.comp (0 : ℝ) hline
  have heq : ∀ t : ℝ, (gL1 lam ∘ fun t : ℝ => x + t • e) t = gL1 lam x + lam * |t| := by
    intro t
    simp only [Function.comp, gL1]
    have : ∑ j, |(x + t • e) j| = ∑ j, |x j| + |t| := by
      rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single i]
      · simp [e, hi]
      · intro j _ hj; simp [e, hj]
      · simp
    rw [this]; ring
  have habs : DifferentiableAt ℝ (fun t : ℝ => |t|) 0 := by
    have h2 := (hcomp.sub_const (gL1 lam x)).const_mul lam⁻¹
    refine h2.congr_of_eventuallyEq (Eventually.of_forall fun t => ?_)
    simp only [heq]; field_simp; ring
  exact not_differentiableAt_abs_zero habs

/-- **Lemma D0.4**: Ω is exactly the set where g is differentiable (λ > 0). -/
theorem gL1_differentiable_set {lam : ℝ} (hlam : 0 < lam) :
    {x : Fin d → ℝ | DifferentiableAt ℝ (gL1 lam) x} = Omega d := by
  ext x
  constructor
  · intro h; by_contra hx; exact gL1_not_differentiableAt hlam hx h
  · intro hx; exact (gL1_contDiffAt lam 1 hx).differentiableAt one_ne_zero

/-- **Lemma D0.4**: Ω is exactly the set where g is C² (λ > 0). -/
theorem gL1_C2_set {lam : ℝ} (hlam : 0 < lam) :
    {x : Fin d → ℝ | ContDiffAt ℝ 2 (gL1 lam) x} = Omega d := by
  ext x
  constructor
  · intro h; by_contra hx
    exact gL1_not_differentiableAt hlam hx
      ((show ContDiffAt ℝ 2 (gL1 lam) x from h).differentiableAt (by norm_num))
  · intro hx; exact gL1_contDiffAt lam 2 hx

/-- **Lemma D0.4, consequence (S4.4)**: if f is twice differentiable at x ∈ Ω (∇f exists
near x and is differentiable at x), then ∇²(f + g)(x) = ∇²f(x). -/
theorem hessian_add_gL1 (lam : ℝ) {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ} (hx : x ∈ Omega d)
    (hf : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f y) :
    fderiv ℝ (fderiv ℝ (fun y => f y + gL1 lam y)) x = fderiv ℝ (fderiv ℝ f) x := by
  have hE : fderiv ℝ (fun y => f y + gL1 lam y) =ᶠ[𝓝 x]
      fun y => fderiv ℝ f y + signLin lam x := by
    have hcell := (cell_isOpen x).mem_nhds (mem_cell hx)
    filter_upwards [hf, hcell] with y hfy hy
    have hgy : DifferentiableAt ℝ (gL1 lam) y :=
      ((signLin lam x).differentiableAt).congr_of_eventuallyEq (gL1_eventuallyEq lam hy)
    rw [show (fun y => f y + gL1 lam y) = f + gL1 lam from rfl, fderiv_add hfy hgy,
      (gL1_eventuallyEq lam hy).fderiv_eq, (signLin lam x).fderiv]
  rw [hE.fderiv_eq, fderiv_add_const]

end L1

end OCF.D0

#print axioms OCF.D0.lemma_D01_i_iv
#print axioms OCF.D0.phi_concaveOn_univ
#print axioms OCF.D0.phi_monotone
#print axioms OCF.D0.phi_tendsto_phiInf
#print axioms OCF.D0.phiInf_indep
#print axioms OCF.D0.qPerp_pos
#print axioms OCF.D0.approach_bound
#print axioms OCF.D0.lemma_D06
#print axioms OCF.D0.D06_remark1
#print axioms OCF.D0.Omega_isOpen
#print axioms OCF.D0.Omega_dense
#print axioms OCF.D0.gL1_contDiffOn
#print axioms OCF.D0.gL1_hessian_zero
#print axioms OCF.D0.gL1_not_differentiableAt
#print axioms OCF.D0.gL1_differentiable_set
#print axioms OCF.D0.gL1_C2_set
#print axioms OCF.D0.hessian_add_gL1

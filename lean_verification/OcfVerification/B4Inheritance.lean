/-
B4 (What a composition inherits, and what must be recomputed) — the targets named for
formalisation in the stage-3 adjudication's tractability notes, in its cost order:
Lemma B4.0; Proposition B4.4 (at d = 2, and for every d ≥ 2 and every square lens);
the exact two-angle witness of S5.5a; the equality clauses of Lemma B4.1 with S6.0
(Theorem B4 (i)1); Proposition B4.3(c). Also, beyond the list: the general existence
form of S5.5a (Theorem B4 (ii)(b), every unequal weight pair) and Theorem B4 (ii)(a) as
a non-determination statement.

Source of truth: project_plan/done/proof_audits/B4_inheritance/01_derivation.md (adjudicated
2026-10-10; sha16 f9af466cc829680f at the start and at the end of formalisation; file not
edited), 03_adjudication.md ("Formalisation (stage 3½) — tractability"; rulings S1, S2, M7,
M9), 02b_reaudit_B4.md (R1–R5; none touches a formalised statement), 04_landing_draft.tex
(lem:b4-equality, prop:b4-step(b), prop:b4-signflip, thm:b4-inheritance (i)1, (ii)(a),
(ii)(b)). Prop. B4.3(a)–(b) (C¹ atoms, Ryu–Yin operator theory) is PROSE-ONLY by ruling and
is not attempted; Lemma B4.2 (classical: Bullo Lemma 2.3) is not formalised.

DEFINITIONAL MAP:
* ℝᵈ — `EuclideanSpace ℝ (Fin d)` for maps, `Fin d → ℝ` for quadratic forms; d ≥ 1 is
  `[NeZero d]` (needed: "some unit x" is false at d = 0); d ≥ 2 is d = m + 2.
* 𝕊ᵈ — `Matrix (Fin d) (Fin d) ℝ` with `IsHermitian`; λ_min, λ_max — `lmin`, `lmax`
  (⨅ / ⨆ of Mathlib's eigenvalues; `lmax` is T1's `lambdaMax`, `lmax_eq_lambdaMax`);
  ‖A‖₂ — `opNorm2 A` := the operator norm of x ↦ Ax on Euclidean ℝᵈ;
  `opNorm2_eq`: = max{|λ_min|, |λ_max|} (proved from the spectral theorem).
* Quadratic atom f(x) = ½xᵀHx + pᵀx — `quadF H c` := ½⟨Hx, x⟩ − ⟨c, x⟩ (c = −p; G3's
  `quadAtom` form); composite F = Σwᵢfᵢ — `fun z => Σ wᵢ * quadF (Hᵢ) (cᵢ) z`
  (`quadF_wsum`: = quadF (ΣwᵢHᵢ) (Σwᵢcᵢ)).
* Landed moduli (def:moduli; prop:spec-moduli(b), here PROVED for quadratic atoms, not
  assumed): C(f, σ) — G3's `ModC`; f β-smooth — G3's `LipGrad`;
  `modC_quadF_iff`/`sigma_quadF`: σ(f) = max{σ : C(f, σ)} = λ_min(H);
  `beta_quadF`: β(f) = min{β : LipGrad f β} = ‖H‖₂. Valid declarations σᵢ ≤ σ(fᵢ),
  βᵢ ≥ β(fᵢ) are therefore stated as `σ i ≤ lmin (H i)`, `opNorm2 (H i) ≤ β i`.
* Kernel attribute ({0}, ν) valid (def:kernel-attribute) — G3's `KernelValid _ ⊥ ν`;
  `kernelValid_bot_quadF`: ⟺ H ⪰ νI. Δ_w — T1's `deltaW` with empty kernel bases
  (`propB44_deltaW`).
* q(α; m, L) := max{|1 − αm|, |1 − αL|} — `qfac`. Lip(T) — the least element of
  `lipSet T` = {K | ∀ x y, ‖Tx − Ty‖ ≤ K‖x − y‖}; "Lip(Id − α∇F) = q" is
  `IsLeast (lipSet (fun x => x - α • gradient F x)) q` with Mathlib's `gradient`.
* η, the dominance test, lens matrix M_W = WMWᵀ, rotations, B6's atoms and sum —
  B6's `domRatio`, `PassesDominance`, `conj`, `rot`, `atom1`, `atom2`, `sumH` (reused).
  Square lens: `W : Matrix (Fin d) (Fin d) ℝ`, `Wᵀ * W = c • 1`, `0 < c`; O := c^{−1/2}W.
* E± = [[1, ±½], [±½, 1]] ⊕ I_{d−2} — `Emat 1`, `Emat (-1)` (`Emat_two`: the 2×2 case);
  H± = OᵀE±O. Record rec_W(f) (S0.6) — `record W H` := (charpoly H, diag of H_W, entrywise
  |H_W|); "spectrum with multiplicities" = equal characteristic polynomials (equivalently
  equal ordered eigenvalues, Mathlib `eigenvalues_eq_eigenvalues_iff`, also proved).
* Own-lens setting (B6): W₁ = `rot 1 0`, W₂ = `rot (cos θ) (sin θ)`,
  W_m = `rot (cos (θ/2)) (sin (θ/2))`; θ-form with the real `Real.cos`, `Real.sin`.

THEOREMS:
* Lemma B4.0 (a), (b), (c) — `lemmaB40_a`, `lemmaB40_b`, `lemmaB40_c`.
* Lemma B4.1 (a), (b) with equality clauses — `lemmaB41_a`, `lemmaB41_b`.
* Theorem B4 (i)1 with declared attributes (S6.0, [ADJ: S1]) — `thmB4_i1_sigma`,
  `thmB4_i1_beta`; the λ_max reading (S3.8, landing "with χ = 1") — `lmax_eq_betaHat_iff`.
* Prop. B4.3(c) (S3.7–S3.8) — `propB43_c_lip` (Lip(Id − α∇F) = q(α; λ_min, λ_max), every
  real α), `propB43_c` (composite of quadratic atoms: Lip = q(α; λ_min(H), λ_max(H)) ≤
  q(α; σ̂, β̂) with the exact equality criterion, α > 0).
* Prop. B4.4 (S4.1–S4.7), every d ≥ 2, every square lens — `propB44`, `propB44_deltaW`;
  at d = 2, W = I with the explicit E± — `propB44_d2`.
* Theorem B4 (ii)(a) — `thmB4_ii_a` (η(H_W), λ_min, λ_max, ‖H‖₂ and Lip(Id − α∇F), α > 0,
  are not functions of (wᵢ, rec_W(fᵢ), valid declared attributes)).
* Theorem B4 (ii)(b) / Prop. B4.5(c) — `ownLens_record` (the record is θ-independent),
  `ownLens_two_angle` (w = (1, 3), δ = 1/100: η = 9/7, 6/5, 15/11 at cos θ = 4/5, fail;
  η = 36/49, 12/17, 20/21 at cos θ = 3/5, pass; λ_min(H) = 51/25 − √73/5 vs
  51/25 − 2√13/5), `ownLens_both_sides` (every w₁ ≠ w₂: one δ, a failing θ₀ in all three
  lenses and a passing θ₁ in all three — S5.5a, adjudicator-derived, now machine-checked).

NOT COVERED: Prop. B4.3(a), (b), (d) (C¹ atoms; Ryu–Yin §13.3; PROSE-ONLY by ruling);
Lemma B4.2 / Theorem (i)4 (classical, Bullo Lemma 2.3); Theorem (i)2, (i)3 (landed
thm:uniform-gap and B3 thm:fb(b), cited); Theorem (ii)(c) and S5.8 (B6); S5.10 bounds;
Remark B4.6 and S7.1; S1.11, S4.9 (d = 1 and C¹ scope remarks).

Status tier: FORMALISED (statement + proof, no sorry) for every theorem listed above.
-/
import Mathlib
import OcfVerification.B6Witnesses
import OcfVerification.G3SoundnessQuadratic

open Matrix BigOperators

namespace OCF.B4

open OCF.B6 (domRatio PassesDominance gershRadius conj rot atom1 atom2 sumH domRatio_smul
  domRatio_explicit passes_explicit not_passes_of_one_lt halfAngle lemma2_Q1 lemma2_Q2 lemma2_Qm)

/-! ### Lemma B4.0 -/

/-- q(α; m, L) := max{|1 − αm|, |1 − αL|}. -/
noncomputable def qfac (α m L : ℝ) : ℝ := max |1 - α * m| |1 - α * L|

theorem lemmaB40_a {α m L : ℝ} (hα : 0 < α) (hmL : m ≤ L) :
    qfac α m L = max (1 - α * m) (α * L - 1) := by
  have h : α * m ≤ α * L := mul_le_mul_of_nonneg_left hmL hα.le
  unfold qfac
  rcases le_total 0 (1 - α * m) with h1 | h1 <;> rcases le_total 0 (1 - α * L) with h2 | h2
  · rw [abs_of_nonneg h1, abs_of_nonneg h2, max_eq_left (by linarith), max_eq_left (by linarith)]
  · rw [abs_of_nonneg h1, abs_of_nonpos h2]; congr 1; ring
  · have e1 : α * m = 1 := by linarith
    have e2 : α * L = 1 := by linarith
    simp [e1, e2]
  · rw [abs_of_nonpos h1, abs_of_nonpos h2, max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

theorem lemmaB40_b {a a' t t' : ℝ} (ha : a ≤ a') (ht : t ≤ t') :
    max a t = max a' t' ↔ (a = a' ∧ t' ≤ a') ∨ (t = t' ∧ a' ≤ t') := by
  constructor
  · intro h
    rcases le_total t' a' with h1 | h1
    · rw [max_eq_left h1] at h
      by_cases haa : a = a'
      · exact Or.inl ⟨haa, h1⟩
      · have hlt : a < a' := lt_of_le_of_ne ha haa
        have : max a t = t := by
          rcases le_total a t with h2 | h2
          · exact max_eq_right h2
          · rw [max_eq_left h2] at h; exact absurd h hlt.ne
        right; constructor <;> linarith
    · rw [max_eq_right h1] at h
      by_cases htt : t = t'
      · exact Or.inr ⟨htt, h1⟩
      · have hlt : t < t' := lt_of_le_of_ne ht htt
        have : max a t = a := by
          rcases le_total a t with h2 | h2
          · rw [max_eq_right h2] at h; exact absurd h hlt.ne
          · exact max_eq_left h2
        left; constructor <;> linarith
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
    · rw [max_eq_left h, max_eq_left (ht.trans h)]
    · rw [max_eq_right h, max_eq_right (ha.trans h)]

theorem lemmaB40_c {ι : Type*} [Fintype ι] (ω a t : ι → ℝ) (hω : ∀ i, 0 < ω i) :
    max (∑ i, ω i * a i) (∑ i, ω i * t i) ≤ ∑ i, ω i * max (a i) (t i) ∧
    (∑ i, ω i * max (a i) (t i) = max (∑ i, ω i * a i) (∑ i, ω i * t i) ↔
      (∀ i, t i ≤ a i) ∨ (∀ i, a i ≤ t i)) := by
  have hA : ∑ i, ω i * a i ≤ ∑ i, ω i * max (a i) (t i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_max_left _ _) (hω i).le
  have hT : ∑ i, ω i * t i ≤ ∑ i, ω i * max (a i) (t i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (le_max_right _ _) (hω i).le
  refine ⟨max_le hA hT, ?_, ?_⟩
  · intro h
    rcases le_total (∑ i, ω i * t i) (∑ i, ω i * a i) with h1 | h1
    · rw [max_eq_left h1] at h
      left
      have hz : ∑ i, ω i * (max (a i) (t i) - a i) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib]; linarith
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ ω i * (max (a i) (t i) - a i) := fun i _ =>
        mul_nonneg (hω i).le (sub_nonneg.2 (le_max_left _ _))
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz i (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (hω i).ne'
      · have : max (a i) (t i) = a i := by linarith
        rw [← this]; exact le_max_right _ _
    · rw [max_eq_right h1] at h
      right
      have hz : ∑ i, ω i * (max (a i) (t i) - t i) = 0 := by
        simp only [mul_sub, Finset.sum_sub_distrib]; linarith
      have hnn : ∀ i ∈ Finset.univ, 0 ≤ ω i * (max (a i) (t i) - t i) := fun i _ =>
        mul_nonneg (hω i).le (sub_nonneg.2 (le_max_right _ _))
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hz i (Finset.mem_univ _)
      rcases mul_eq_zero.1 this with h0 | h0
      · exact absurd h0 (hω i).ne'
      · have : max (a i) (t i) = t i := by linarith
        rw [← this]; exact le_max_left _ _
  · rintro (h | h)
    · have e : ∑ i, ω i * max (a i) (t i) = ∑ i, ω i * a i :=
        Finset.sum_congr rfl fun i _ => by rw [max_eq_left (h i)]
      rw [e, max_eq_left (e ▸ hT)]
    · have e : ∑ i, ω i * max (a i) (t i) = ∑ i, ω i * t i :=
        Finset.sum_congr rfl fun i _ => by rw [max_eq_right (h i)]
      rw [e, max_eq_right (e ▸ hA)]

/-! ### Spectral toolkit (λ_min, λ_max, Rayleigh bounds, ‖·‖₂) -/

section Spectral

variable {d : ℕ}

/-- λ_min of a real symmetric matrix: the minimum (`⨅`) of its eigenvalues (B6's convention);
0 for a non-symmetric argument (never used). -/
noncomputable def lmin (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : A.IsHermitian then ⨅ j, h.eigenvalues j else 0

/-- λ_max of a real symmetric matrix: the maximum (`⨆`) of its eigenvalues. -/
noncomputable def lmax (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  if h : A.IsHermitian then ⨆ j, h.eigenvalues j else 0

/-- The spectral (ℓ₂-operator) norm ‖A‖₂ := ‖x ↦ Ax‖ on Euclidean ℝᵈ. -/
noncomputable def opNorm2 (A : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A‖

lemma lmax_eq_lambdaMax (A : Matrix (Fin d) (Fin d) ℝ) : lmax A = OCF.lambdaMax A := rfl

variable {A : Matrix (Fin d) (Fin d) ℝ}

lemma lmin_eq (hA : A.IsHermitian) : lmin A = ⨅ j, hA.eigenvalues j := dif_pos hA
lemma lmax_eq (hA : A.IsHermitian) : lmax A = ⨆ j, hA.eigenvalues j := dif_pos hA

lemma lmin_le_eig (hA : A.IsHermitian) (j : Fin d) : lmin A ≤ hA.eigenvalues j := by
  rw [lmin_eq hA]; exact ciInf_le (Finite.bddBelow_range _) j

lemma eig_le_lmax (hA : A.IsHermitian) (j : Fin d) : hA.eigenvalues j ≤ lmax A := by
  rw [lmax_eq hA]; exact le_ciSup (Finite.bddAbove_range _) j

lemma exists_eig_eq_lmin [NeZero d] (hA : A.IsHermitian) : ∃ j, hA.eigenvalues j = lmin A := by
  rw [lmin_eq hA]; exact exists_eq_ciInf_of_finite

lemma exists_eig_eq_lmax [NeZero d] (hA : A.IsHermitian) : ∃ j, hA.eigenvalues j = lmax A := by
  rw [lmax_eq hA]; exact exists_eq_ciSup_of_finite

lemma dot_self_nonneg (x : Fin d → ℝ) : 0 ≤ x ⬝ᵥ x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (x i)

lemma dot_self_pos {x : Fin d → ℝ} (hx : x ≠ 0) : 0 < x ⬝ᵥ x :=
  lt_of_le_of_ne (dot_self_nonneg x) (fun h => hx (dotProduct_self_eq_zero.1 h.symm))

/-- PSD from a nonnegative quadratic form (real symmetric case). -/
lemma psd_of_form {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian)
    (h : ∀ x, 0 ≤ x ⬝ᵥ S *ᵥ x) : S.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  exact ⟨hS, fun x => by simpa using h x⟩

/-- For a nonnegative symmetric form, xᵀSx = 0 forces Sx = 0 (B&V §A.5.2 via S^{1/2};
Mathlib `PosSemidef.dotProduct_mulVec_zero_iff`). -/
lemma mulVec_eq_zero_of_form {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian)
    (h : ∀ x, 0 ≤ x ⬝ᵥ S *ᵥ x) {x : Fin d → ℝ} (hx : x ⬝ᵥ S *ᵥ x = 0) : S *ᵥ x = 0 := by
  have := (psd_of_form hS h).dotProduct_mulVec_zero_iff x
  rw [star_trivial] at this
  exact this.1 hx

lemma isHermitian_smul_one (c : ℝ) : (c • (1 : Matrix (Fin d) (Fin d) ℝ)).IsHermitian :=
  Matrix.isHermitian_one.smul (IsSelfAdjoint.all _) |>.trans (by rfl)

lemma form_sub_smul (S : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (S - c • (1 : Matrix (Fin d) (Fin d) ℝ)) *ᵥ x = x ⬝ᵥ S *ᵥ x - c * (x ⬝ᵥ x) := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

lemma form_smul_sub (S : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (c • (1 : Matrix (Fin d) (Fin d) ℝ) - S) *ᵥ x = c * (x ⬝ᵥ x) - x ⬝ᵥ S *ᵥ x := by
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul]

/-- Attainment of a Loewner floor forces an eigenvector: if μ‖y‖² ≤ yᵀSy for all y and
xᵀSx = μ‖x‖², then Sx = μx (S1.8). -/
lemma eig_of_floor {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian) {μ : ℝ}
    (h : ∀ y, μ * (y ⬝ᵥ y) ≤ y ⬝ᵥ S *ᵥ y) {x : Fin d → ℝ}
    (hx : x ⬝ᵥ S *ᵥ x = μ * (x ⬝ᵥ x)) : S *ᵥ x = μ • x := by
  have hz := mulVec_eq_zero_of_form (S := S - μ • 1) (hS.sub (isHermitian_smul_one μ))
    (fun y => by rw [form_sub_smul]; linarith [h y]) (by rw [form_sub_smul]; linarith)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  exact hz

/-- Attainment of a Loewner ceiling forces an eigenvector. -/
lemma eig_of_ceil {S : Matrix (Fin d) (Fin d) ℝ} (hS : S.IsHermitian) {μ : ℝ}
    (h : ∀ y, y ⬝ᵥ S *ᵥ y ≤ μ * (y ⬝ᵥ y)) {x : Fin d → ℝ}
    (hx : x ⬝ᵥ S *ᵥ x = μ * (x ⬝ᵥ x)) : S *ᵥ x = μ • x := by
  have hz := mulVec_eq_zero_of_form (S := μ • 1 - S) ((isHermitian_smul_one μ).sub hS)
    (fun y => by rw [form_smul_sub]; linarith [h y]) (by rw [form_smul_sub]; linarith)
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hz
  exact hz.symm

/-- Rayleigh lower bound: λ_min‖x‖² ≤ xᵀAx (B&V §A.5.2, p. 647). -/
lemma lmin_mul_le (hA : A.IsHermitian) (x : Fin d → ℝ) : lmin A * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  have hpsd : (A - lmin A • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef := by
    rw [Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg]
    refine ⟨hA.sub (isHermitian_smul_one _), ?_⟩
    intro μ hμ
    rw [show lmin A • (1 : Matrix (Fin d) (Fin d) ℝ)
          = algebraMap ℝ (Matrix (Fin d) (Fin d) ℝ) (lmin A) from
        (Algebra.algebraMap_eq_smul_one _).symm, ← spectrum.sub_singleton_eq] at hμ
    obtain ⟨a, ha, c, hc, rfl⟩ := Set.mem_sub.mp hμ
    rw [Set.mem_singleton_iff] at hc
    subst hc
    rw [hA.spectrum_real_eq_range_eigenvalues] at ha
    obtain ⟨i, rfl⟩ := ha
    simp only [Set.mem_setOf_eq, sub_nonneg]
    exact lmin_le_eig hA i
  have h0 := hpsd.dotProduct_mulVec_nonneg x
  rw [star_trivial, form_sub_smul] at h0
  linarith

/-- Rayleigh upper bound: xᵀAx ≤ λ_max‖x‖² (T1's `dotProduct_mulVec_le_lambdaMax`). -/
lemma le_lmax_mul (hA : A.IsHermitian) (x : Fin d → ℝ) : x ⬝ᵥ A *ᵥ x ≤ lmax A * (x ⬝ᵥ x) :=
  OCF.dotProduct_mulVec_le_lambdaMax hA x

/-- A unit eigenvector for each eigenvalue (orthonormal eigenbasis, B&V (A.10)). -/
lemma exists_unit_eigvec (hA : A.IsHermitian) (j : Fin d) :
    ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ A *ᵥ x = hA.eigenvalues j • x := by
  refine ⟨(hA.eigenvectorBasis j).ofLp, ?_, hA.mulVec_eigenvectorBasis j⟩
  have h1 : ‖hA.eigenvectorBasis j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
  have h2 := real_inner_self_eq_norm_sq (hA.eigenvectorBasis j)
  rw [h1, EuclideanSpace.inner_eq_star_dotProduct, star_trivial] at h2
  simpa using h2

lemma exists_unit_eig_lmin [NeZero d] (hA : A.IsHermitian) :
    ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ A *ᵥ x = lmin A • x := by
  obtain ⟨j, hj⟩ := exists_eig_eq_lmin hA
  rw [← hj]; exact exists_unit_eigvec hA j

lemma exists_unit_eig_lmax [NeZero d] (hA : A.IsHermitian) :
    ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ A *ᵥ x = lmax A • x := by
  obtain ⟨j, hj⟩ := exists_eig_eq_lmax hA
  rw [← hj]; exact exists_unit_eigvec hA j

lemma form_of_eig {x : Fin d → ℝ} {μ : ℝ} (h : A *ᵥ x = μ • x) :
    x ⬝ᵥ A *ᵥ x = μ * (x ⬝ᵥ x) := by
  rw [h, dotProduct_smul, smul_eq_mul]

/-- Every eigenvalue lies in [λ_min, λ_max]. -/
lemma lmin_le_of_eig (hA : A.IsHermitian) {x : Fin d → ℝ} (hx : x ≠ 0) {μ : ℝ}
    (h : A *ᵥ x = μ • x) : lmin A ≤ μ ∧ μ ≤ lmax A := by
  have hp := dot_self_pos hx
  have e := form_of_eig h
  constructor
  · have := lmin_mul_le hA x; rw [e] at this; exact le_of_mul_le_mul_right this hp
  · have := le_lmax_mul hA x; rw [e] at this; exact le_of_mul_le_mul_right this hp

lemma lmin_le_lmax [NeZero d] (hA : A.IsHermitian) : lmin A ≤ lmax A := by
  obtain ⟨j, hj⟩ := exists_eig_eq_lmin hA
  rw [← hj]; exact eig_le_lmax hA j

/-- Characterisation of λ_min: a Loewner floor μ that is an eigenvalue is λ_min. -/
lemma lmin_eq_of (hA : A.IsHermitian) [NeZero d] {μ : ℝ}
    (hfloor : ∀ y, μ * (y ⬝ᵥ y) ≤ y ⬝ᵥ A *ᵥ y) {x : Fin d → ℝ} (hx : x ≠ 0)
    (hev : A *ᵥ x = μ • x) : lmin A = μ := by
  apply le_antisymm (lmin_le_of_eig hA hx hev).1
  obtain ⟨y, hy1, hy⟩ := exists_unit_eig_lmin hA
  have := hfloor y
  rw [form_of_eig hy, hy1] at this
  simpa using this

/-- Characterisation of λ_max: a Loewner ceiling μ that is an eigenvalue is λ_max. -/
lemma lmax_eq_of (hA : A.IsHermitian) [NeZero d] {μ : ℝ}
    (hceil : ∀ y, y ⬝ᵥ A *ᵥ y ≤ μ * (y ⬝ᵥ y)) {x : Fin d → ℝ} (hx : x ≠ 0)
    (hev : A *ᵥ x = μ • x) : lmax A = μ := by
  apply le_antisymm _ (lmin_le_of_eig hA hx hev).2
  obtain ⟨y, hy1, hy⟩ := exists_unit_eig_lmax hA
  have := hceil y
  rw [form_of_eig hy, hy1] at this
  simpa using this

/-- σ ≤ λ_min(A) iff A ⪰ σI (the Loewner form of a valid curvature declaration). -/
lemma le_lmin_iff (hA : A.IsHermitian) [NeZero d] (σ : ℝ) :
    σ ≤ lmin A ↔ ∀ x, σ * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  constructor
  · intro h x
    exact (mul_le_mul_of_nonneg_right h (dot_self_nonneg x)).trans (lmin_mul_le hA x)
  · intro h
    obtain ⟨y, hy1, hy⟩ := exists_unit_eig_lmin hA
    have := h y
    rw [form_of_eig hy, hy1] at this
    simpa using this

end Spectral

/-! ### ‖·‖₂ of a symmetric matrix and of I − αH -/

section OpNorm

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℝ}

open scoped Matrix.Norms.L2Operator

/-- Real spectral decomposition A = U diag(λ) Uᵀ (Mathlib `IsHermitian.spectral_theorem`). -/
lemma spectral_real (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) := by
  conv_lhs => rw [hA.spectral_theorem]
  simp [RCLike.ofReal_real_eq_id]

lemma opNorm2_conj_diag (hA : A.IsHermitian) (v : Fin d → ℝ) :
    opNorm2 ((hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) * diagonal v *
      star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)) = ‖v‖ := by
  unfold opNorm2
  rw [← Matrix.cstar_norm_def,
    CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem hA.eigenvectorUnitary.2),
    CStarRing.norm_mem_unitary_mul _ hA.eigenvectorUnitary.2, Matrix.l2_opNorm_diagonal]

/-- Sup norm of a vector whose entries lie between p and q and attain both. -/
lemma pi_norm_eq_max_abs {v : Fin d → ℝ} {p q : ℝ}
    (hbt : ∀ j, min p q ≤ v j ∧ v j ≤ max p q) (hp : ∃ j, v j = p) (hq : ∃ j, v j = q) :
    ‖v‖ = max |p| |q| := by
  apply le_antisymm
  · refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
    rw [Real.norm_eq_abs, abs_le]
    obtain ⟨h1, h2⟩ := hbt j
    constructor
    · rcases le_total p q with h | h
      · rw [min_eq_left h] at h1
        linarith [neg_abs_le p, le_max_left |p| |q|]
      · rw [min_eq_right h] at h1
        linarith [neg_abs_le q, le_max_right |p| |q|]
    · rcases le_total p q with h | h
      · rw [max_eq_right h] at h2
        linarith [le_abs_self q, le_max_right |p| |q|]
      · rw [max_eq_left h] at h2
        linarith [le_abs_self p, le_max_left |p| |q|]
  · obtain ⟨j, hj⟩ := hp
    obtain ⟨k, hk⟩ := hq
    refine max_le ?_ ?_
    · have := norm_le_pi_norm v j; rwa [Real.norm_eq_abs, hj] at this
    · have := norm_le_pi_norm v k; rwa [Real.norm_eq_abs, hk] at this

/-- ‖A‖₂ = max{|λ_min(A)|, |λ_max(A)|} for symmetric A (B&V §A.5.2, p. 647). -/
theorem opNorm2_eq [NeZero d] (hA : A.IsHermitian) : opNorm2 A = max |lmin A| |lmax A| := by
  conv_lhs => rw [spectral_real hA]
  rw [opNorm2_conj_diag hA]
  refine pi_norm_eq_max_abs (fun j => ⟨?_, ?_⟩) (exists_eig_eq_lmin hA) (exists_eig_eq_lmax hA)
  · exact (min_le_left _ _).trans (lmin_le_eig hA j)
  · exact (eig_le_lmax hA j).trans (le_max_right _ _)

theorem opNorm2_eq' [NeZero d] (hA : A.IsHermitian) : opNorm2 A = max (lmax A) (-lmin A) := by
  rw [opNorm2_eq hA]
  have h := lmin_le_lmax hA
  rcases le_total 0 (lmin A) with h1 | h1 <;> rcases le_total 0 (lmax A) with h2 | h2
  · rw [abs_of_nonneg h1, abs_of_nonneg h2, max_eq_right h, max_eq_left (by linarith)]
  · rw [abs_of_nonneg h1, abs_of_nonpos h2]
    have : lmax A = 0 := by linarith
    have : lmin A = 0 := by linarith
    simp [*]
  · rw [abs_of_nonpos h1, abs_of_nonneg h2]; exact max_comm _ _
  · rw [abs_of_nonpos h1, abs_of_nonpos h2, max_eq_left (by linarith), max_eq_right (by linarith)]

/-- I − αA = U diag(1 − αλ) Uᵀ. -/
lemma one_sub_smul_spectral (hA : A.IsHermitian) (α : ℝ) :
    (1 - α • A) = (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) *
      diagonal (fun j => 1 - α * hA.eigenvalues j) *
      star (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) := by
  set U := (hA.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ)
  have hd : diagonal (fun j => 1 - α * hA.eigenvalues j) = 1 - α • diagonal hA.eigenvalues := by
    ext i j; by_cases h : i = j <;> simp [diagonal, one_apply, h]
  have hU : U * star U = 1 := Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2
  rw [hd, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU, Matrix.mul_smul, Matrix.smul_mul,
    ← spectral_real hA]

/-- ‖I − αA‖₂ = q(α; λ_min(A), λ_max(A)) for symmetric A (S3.7). -/
theorem opNorm2_one_sub [NeZero d] (hA : A.IsHermitian) (α : ℝ) :
    opNorm2 (1 - α • A) = qfac α (lmin A) (lmax A) := by
  rw [one_sub_smul_spectral hA α, opNorm2_conj_diag hA, qfac]
  obtain ⟨j₀, hj₀⟩ := exists_eig_eq_lmin hA
  obtain ⟨j₁, hj₁⟩ := exists_eig_eq_lmax hA
  refine pi_norm_eq_max_abs (fun j => ?_) ⟨j₀, by simp [hj₀]⟩ ⟨j₁, by simp [hj₁]⟩
  have h1 := lmin_le_eig hA j
  have h2 := eig_le_lmax hA j
  rcases le_total 0 α with hα | hα
  · have a1 : α * hA.eigenvalues j ≤ α * lmax A := mul_le_mul_of_nonneg_left h2 hα
    have a2 : α * lmin A ≤ α * hA.eigenvalues j := mul_le_mul_of_nonneg_left h1 hα
    exact ⟨(min_le_right _ _).trans (by linarith), le_trans (by linarith) (le_max_left _ _)⟩
  · have a1 : α * lmax A ≤ α * hA.eigenvalues j := mul_le_mul_of_nonpos_left h2 hα
    have a2 : α * hA.eigenvalues j ≤ α * lmin A := mul_le_mul_of_nonpos_left h1 hα
    exact ⟨(min_le_left _ _).trans (by linarith), le_trans (by linarith) (le_max_right _ _)⟩

/-- |xᵀAx| ≤ ‖A‖₂‖x‖², and χ·xᵀAx ≤ ‖A‖₂‖x‖² for χ = ±1. -/
lemma signed_form_le [NeZero d] (hA : A.IsHermitian) {χ : ℝ} (hχ : χ = 1 ∨ χ = -1)
    (x : Fin d → ℝ) : χ * (x ⬝ᵥ A *ᵥ x) ≤ opNorm2 A * (x ⬝ᵥ x) := by
  rw [opNorm2_eq' hA]
  have h1 := lmin_mul_le hA x
  have h2 := le_lmax_mul hA x
  have hx := dot_self_nonneg x
  rcases hχ with rfl | rfl
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_left (lmax A) (-lmin A)) hx]
  · nlinarith [mul_le_mul_of_nonneg_right (le_max_right (lmax A) (-lmin A)) hx]

/-- Every eigenvalue has modulus ≤ ‖A‖₂. -/
lemma abs_eig_le [NeZero d] (hA : A.IsHermitian) {x : Fin d → ℝ} (hx : x ≠ 0) {μ : ℝ}
    (h : A *ᵥ x = μ • x) : |μ| ≤ opNorm2 A := by
  rw [opNorm2_eq hA]
  obtain ⟨h1, h2⟩ := lmin_le_of_eig hA hx h
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (lmin A), le_max_left |lmin A| |lmax A|]
  · linarith [le_abs_self (lmax A), le_max_right |lmin A| |lmax A|]

/-- A unit eigenvector for an eigenvalue of largest modulus: Ax = χ‖A‖₂x, χ = ±1. -/
lemma exists_unit_eig_norm [NeZero d] (hA : A.IsHermitian) :
    ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ ∃ χ : ℝ, (χ = 1 ∨ χ = -1) ∧ A *ᵥ x = (χ * opNorm2 A) • x := by
  rw [opNorm2_eq' hA]
  rcases le_total (-lmin A) (lmax A) with h | h
  · obtain ⟨x, hx1, hx⟩ := exists_unit_eig_lmax hA
    exact ⟨x, hx1, 1, Or.inl rfl, by rw [max_eq_left h, one_mul]; exact hx⟩
  · obtain ⟨x, hx1, hx⟩ := exists_unit_eig_lmin hA
    exact ⟨x, hx1, -1, Or.inr rfl, by rw [max_eq_right h]; simpa using hx⟩

lemma lmax_le_opNorm2 [NeZero d] (hA : A.IsHermitian) : lmax A ≤ opNorm2 A := by
  rw [opNorm2_eq' hA]; exact le_max_left _ _

lemma neg_opNorm2_le_lmin [NeZero d] (hA : A.IsHermitian) : -opNorm2 A ≤ lmin A := by
  rw [opNorm2_eq' hA]; linarith [le_max_right (lmax A) (-lmin A)]

/-- β ≥ ‖A‖₂ iff −βI ⪯ A ⪯ βI (the Loewner form of a valid smoothness declaration). -/
lemma opNorm2_le_iff [NeZero d] (hA : A.IsHermitian) (β : ℝ) :
    opNorm2 A ≤ β ↔ ∀ x, |x ⬝ᵥ A *ᵥ x| ≤ β * (x ⬝ᵥ x) := by
  constructor
  · intro h x
    have hx := dot_self_nonneg x
    rw [abs_le]
    have a := signed_form_le hA (Or.inl rfl) x
    have b := signed_form_le hA (Or.inr rfl) x
    have c := mul_le_mul_of_nonneg_right h hx
    constructor <;> linarith
  · intro h
    obtain ⟨x, hx1, χ, hχ, hx⟩ := exists_unit_eig_norm hA
    have := h x
    rw [form_of_eig hx, hx1, mul_one, mul_one, abs_mul] at this
    rcases hχ with rfl | rfl <;> simp at this <;>
      linarith [abs_nonneg (opNorm2 A), le_abs_self (opNorm2 A)]

end OpNorm

/-! ### Weighted sums -/

section Sums

variable {d : ℕ} {ι : Type*} [Fintype ι]

lemma isHermitian_wsum {H : ι → Matrix (Fin d) (Fin d) ℝ} (hH : ∀ i, (H i).IsHermitian)
    (w : ι → ℝ) : (∑ i, w i • H i).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_smul, (hH i).eq, star_trivial]

lemma wsum_mulVec (H : ι → Matrix (Fin d) (Fin d) ℝ) (w : ι → ℝ) (x : Fin d → ℝ) :
    (∑ i, w i • H i) *ᵥ x = ∑ i, w i • (H i *ᵥ x) := by
  rw [Matrix.sum_mulVec]
  exact Finset.sum_congr rfl fun i _ => Matrix.smul_mulVec _ _ _

lemma form_wsum (H : ι → Matrix (Fin d) (Fin d) ℝ) (w : ι → ℝ) (x : Fin d → ℝ) :
    x ⬝ᵥ (∑ i, w i • H i) *ᵥ x = ∑ i, w i * (x ⬝ᵥ H i *ᵥ x) := by
  rw [wsum_mulVec, dotProduct_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [dotProduct_smul, smul_eq_mul]

lemma wsum_eig {H : ι → Matrix (Fin d) (Fin d) ℝ} (w : ι → ℝ) {x : Fin d → ℝ} {μ : ι → ℝ}
    (h : ∀ i, H i *ᵥ x = μ i • x) : (∑ i, w i • H i) *ᵥ x = (∑ i, w i * μ i) • x := by
  rw [wsum_mulVec, Finset.sum_smul]
  exact Finset.sum_congr rfl fun i _ => by rw [h i, smul_smul]

/-- A vanishing positive-weight sum of nonnegative terms has every term zero. -/
lemma terms_zero {w e : ι → ℝ} (hw : ∀ i, 0 < w i) (he : ∀ i, 0 ≤ e i)
    (hs : ∑ i, w i * e i = 0) (i : ι) : e i = 0 := by
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_nonneg (hw j).le (he j))).1 hs i
    (Finset.mem_univ _)
  rcases mul_eq_zero.1 this with h | h
  · exact absurd h (hw i).ne'
  · exact h

end Sums

/-! ### Lemma B4.1 and Theorem B4 (i)1 (equality in the inherited moduli, quadratic atoms) -/

section LemmaB41

variable {d : ℕ} [NeZero d] {ι : Type*} [Fintype ι]
  {H : ι → Matrix (Fin d) (Fin d) ℝ} {w : ι → ℝ}

/-- **Lemma B4.1(a)** (S1.9). λ_min(ΣwᵢHᵢ) ≥ Σwᵢλ_min(Hᵢ), with equality iff some unit x
satisfies Hᵢx = λ_min(Hᵢ)x for every i. -/
theorem lemmaB41_a (hH : ∀ i, (H i).IsHermitian) (hw : ∀ i, 0 < w i) :
    ∑ i, w i * lmin (H i) ≤ lmin (∑ i, w i • H i) ∧
    (lmin (∑ i, w i • H i) = ∑ i, w i * lmin (H i) ↔
      ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ ∀ i, H i *ᵥ x = lmin (H i) • x) := by
  have hS := isHermitian_wsum hH w
  obtain ⟨x, hx1, hx⟩ := exists_unit_eig_lmin hS
  have hval : lmin (∑ i, w i • H i) = ∑ i, w i * (x ⬝ᵥ H i *ᵥ x) := by
    rw [← form_wsum, form_of_eig hx, hx1, mul_one]
  have hterm : ∀ i, lmin (H i) ≤ x ⬝ᵥ H i *ᵥ x := fun i => by
    have := lmin_mul_le (hH i) x; rwa [hx1, mul_one] at this
  have hle : ∑ i, w i * lmin (H i) ≤ lmin (∑ i, w i • H i) := by
    rw [hval]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw i).le
  refine ⟨hle, ⟨fun heq => ⟨x, hx1, fun i => ?_⟩, fun ⟨y, hy1, hy⟩ => ?_⟩⟩
  · have hz : ∑ i, w i * (x ⬝ᵥ H i *ᵥ x - lmin (H i)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]; rw [← hval]; linarith
    have := terms_zero hw (fun i => sub_nonneg.2 (hterm i)) hz i
    exact eig_of_floor (hH i) (fun y => lmin_mul_le (hH i) y) (by rw [hx1]; linarith)
  · have hev := wsum_eig w hy
    have hy0 : y ≠ 0 := fun h => by rw [h] at hy1; simp at hy1
    exact le_antisymm (lmin_le_of_eig hS hy0 hev).1 hle

/-- **Lemma B4.1(b)** (S1.10). ‖ΣwᵢHᵢ‖₂ ≤ Σwᵢ‖Hᵢ‖₂, with equality iff some unit x and
χ ∈ {−1, +1} satisfy Hᵢx = χ‖Hᵢ‖₂x for every i. -/
theorem lemmaB41_b (hH : ∀ i, (H i).IsHermitian) (hw : ∀ i, 0 < w i) :
    opNorm2 (∑ i, w i • H i) ≤ ∑ i, w i * opNorm2 (H i) ∧
    (opNorm2 (∑ i, w i • H i) = ∑ i, w i * opNorm2 (H i) ↔
      ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ ∃ χ : ℝ, (χ = 1 ∨ χ = -1) ∧
        ∀ i, H i *ᵥ x = (χ * opNorm2 (H i)) • x) := by
  have hS := isHermitian_wsum hH w
  obtain ⟨x, hx1, χ, hχ, hx⟩ := exists_unit_eig_norm hS
  have hχ2 : χ * χ = 1 := by rcases hχ with rfl | rfl <;> norm_num
  have hval : opNorm2 (∑ i, w i • H i) = ∑ i, w i * (χ * (x ⬝ᵥ H i *ᵥ x)) := by
    have e := form_of_eig hx
    rw [hx1, mul_one, form_wsum] at e
    have : χ * (∑ i, w i * (x ⬝ᵥ H i *ᵥ x)) = opNorm2 (∑ i, w i • H i) := by
      rw [e, ← mul_assoc, hχ2, one_mul]
    rw [← this, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hterm : ∀ i, χ * (x ⬝ᵥ H i *ᵥ x) ≤ opNorm2 (H i) := fun i => by
    have := signed_form_le (hH i) hχ x; rwa [hx1, mul_one] at this
  have hle : opNorm2 (∑ i, w i • H i) ≤ ∑ i, w i * opNorm2 (H i) := by
    rw [hval]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw i).le
  refine ⟨hle, ⟨fun heq => ⟨x, hx1, χ, hχ, fun i => ?_⟩, fun ⟨y, hy1, χ', hχ', hy⟩ => ?_⟩⟩
  · have hz : ∑ i, w i * (opNorm2 (H i) - χ * (x ⬝ᵥ H i *ᵥ x)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]; rw [← hval]; linarith
    have h0 := terms_zero hw (fun i => sub_nonneg.2 (hterm i)) hz i
    have hχH : (χ • H i).IsHermitian := (hH i).smul (IsSelfAdjoint.all _) |>.trans (by rfl)
    have hceil : ∀ y, y ⬝ᵥ (χ • H i) *ᵥ y ≤ opNorm2 (H i) * (y ⬝ᵥ y) := fun y => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]; exact signed_form_le (hH i) hχ y
    have hev := eig_of_ceil hχH hceil (x := x) (by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, hx1]; linarith)
    rw [Matrix.smul_mulVec] at hev
    have := congrArg (fun v => χ • v) hev
    simp only [smul_smul, hχ2, one_smul] at this
    rw [this]
  · have hev := wsum_eig w hy
    have hy0 : y ≠ 0 := fun h => by rw [h] at hy1; simp at hy1
    have habs := abs_eig_le hS hy0 hev
    have hnn : 0 ≤ ∑ i, w i * opNorm2 (H i) := Finset.sum_nonneg fun i _ =>
      mul_nonneg (hw i).le (le_trans (abs_nonneg _) (abs_eig_le (hH i) hy0 (hy i)) |>.trans
        (by rcases hχ' with rfl | rfl <;> simp))
    have e : ∑ i, w i * (χ' * opNorm2 (H i)) = χ' * ∑ i, w i * opNorm2 (H i) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, abs_mul] at habs
    have : |χ'| = 1 := by rcases hχ' with rfl | rfl <;> simp
    rw [this, one_mul, abs_of_nonneg hnn] at habs
    exact le_antisymm hle habs

/-- **Theorem B4 (i)1, curvature clause, with declared attributes** (S6.0, [ADJ: S1]).
For valid declarations σᵢ ≤ λ_min(Hᵢ) = σ(fᵢ): σ(F) = λ_min(H) ≥ σ̂ := Σwᵢσᵢ, and
σ(F) = σ̂ iff every declaration is exact and the atoms share a bottom eigenvector. -/
theorem thmB4_i1_sigma (hH : ∀ i, (H i).IsHermitian) (hw : ∀ i, 0 < w i) (σ : ι → ℝ)
    (hσ : ∀ i, σ i ≤ lmin (H i)) :
    ∑ i, w i * σ i ≤ lmin (∑ i, w i • H i) ∧
    (lmin (∑ i, w i • H i) = ∑ i, w i * σ i ↔
      (∀ i, σ i = lmin (H i)) ∧ ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ ∀ i, H i *ᵥ x = lmin (H i) • x) := by
  obtain ⟨hle, hiff⟩ := lemmaB41_a hH hw
  have hdec : ∑ i, w i * σ i ≤ ∑ i, w i * lmin (H i) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hσ i) (hw i).le
  refine ⟨hdec.trans hle, fun heq => ?_, fun ⟨hex, hx⟩ => ?_⟩
  · have h1 : lmin (∑ i, w i • H i) = ∑ i, w i * lmin (H i) := le_antisymm (heq ▸ hdec) hle
    have h2 : ∑ i, w i * (lmin (H i) - σ i) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]; linarith
    exact ⟨fun i => by linarith [terms_zero hw (fun i => sub_nonneg.2 (hσ i)) h2 i],
      hiff.1 h1⟩
  · rw [hiff.2 hx]
    exact Finset.sum_congr rfl fun i _ => by rw [hex i]

/-- **Theorem B4 (i)1, smoothness clause, with declared attributes** (S6.0). For valid
declarations βᵢ ≥ ‖Hᵢ‖₂ = β(fᵢ): β(F) = ‖H‖₂ ≤ β̂ := Σwᵢβᵢ, and β(F) = β̂ iff every
declaration is exact and some unit x, χ = ±1 satisfy Hᵢx = χ‖Hᵢ‖₂x for every i. -/
theorem thmB4_i1_beta (hH : ∀ i, (H i).IsHermitian) (hw : ∀ i, 0 < w i) (β : ι → ℝ)
    (hβ : ∀ i, opNorm2 (H i) ≤ β i) :
    opNorm2 (∑ i, w i • H i) ≤ ∑ i, w i * β i ∧
    (opNorm2 (∑ i, w i • H i) = ∑ i, w i * β i ↔
      (∀ i, β i = opNorm2 (H i)) ∧ ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧ ∃ χ : ℝ, (χ = 1 ∨ χ = -1) ∧
        ∀ i, H i *ᵥ x = (χ * opNorm2 (H i)) • x) := by
  obtain ⟨hle, hiff⟩ := lemmaB41_b hH hw
  have hdec : ∑ i, w i * opNorm2 (H i) ≤ ∑ i, w i * β i :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hβ i) (hw i).le
  refine ⟨hle.trans hdec, fun heq => ?_, fun ⟨hex, hx⟩ => ?_⟩
  · have h1 : opNorm2 (∑ i, w i • H i) = ∑ i, w i * opNorm2 (H i) := le_antisymm hle (heq ▸ hdec)
    have h2 : ∑ i, w i * (β i - opNorm2 (H i)) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]; linarith
    exact ⟨fun i => by linarith [terms_zero hw (fun i => sub_nonneg.2 (hβ i)) h2 i], hiff.1 h1⟩
  · rw [hiff.2 hx]
    exact Finset.sum_congr rfl fun i _ => by rw [hex i]

/-- **λ_max reading** (S3.8, landing Lemma lem:b4-equality(b) "with χ = 1"). For valid
declarations βᵢ ≥ ‖Hᵢ‖₂: λ_max(H) ≤ β̂, and λ_max(H) = β̂ iff every declaration is exact
and some unit x satisfies Hᵢx = ‖Hᵢ‖₂x for every i. -/
theorem lmax_eq_betaHat_iff (hH : ∀ i, (H i).IsHermitian) (hw : ∀ i, 0 < w i) (β : ι → ℝ)
    (hβ : ∀ i, opNorm2 (H i) ≤ β i) :
    lmax (∑ i, w i • H i) ≤ ∑ i, w i * β i ∧
    (lmax (∑ i, w i • H i) = ∑ i, w i * β i ↔
      (∀ i, β i = opNorm2 (H i)) ∧ ∃ x : Fin d → ℝ, x ⬝ᵥ x = 1 ∧
        ∀ i, H i *ᵥ x = opNorm2 (H i) • x) := by
  have hS := isHermitian_wsum hH w
  obtain ⟨x, hx1, hx⟩ := exists_unit_eig_lmax hS
  have hval : lmax (∑ i, w i • H i) = ∑ i, w i * (x ⬝ᵥ H i *ᵥ x) := by
    rw [← form_wsum, form_of_eig hx, hx1, mul_one]
  have hterm : ∀ i, x ⬝ᵥ H i *ᵥ x ≤ β i := fun i => by
    have := signed_form_le (hH i) (Or.inl rfl) x
    rw [hx1, mul_one, one_mul] at this; exact this.trans (hβ i)
  have hle : lmax (∑ i, w i • H i) ≤ ∑ i, w i * β i := by
    rw [hval]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hterm i) (hw i).le
  refine ⟨hle, fun heq => ?_, fun ⟨hex, y, hy1, hy⟩ => ?_⟩
  · have hz : ∑ i, w i * (β i - x ⬝ᵥ H i *ᵥ x) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]; rw [← hval]; linarith
    have h0 := fun i => terms_zero hw (fun i => sub_nonneg.2 (hterm i)) hz i
    have hform : ∀ i, x ⬝ᵥ H i *ᵥ x ≤ opNorm2 (H i) := fun i => by
      have := signed_form_le (hH i) (Or.inl rfl) x; rwa [hx1, mul_one, one_mul] at this
    have hex : ∀ i, β i = opNorm2 (H i) := fun i =>
      le_antisymm (by linarith [h0 i, hform i]) (hβ i)
    refine ⟨hex, x, hx1, fun i => ?_⟩
    have hceil : ∀ y, y ⬝ᵥ H i *ᵥ y ≤ opNorm2 (H i) * (y ⬝ᵥ y) := fun y => by
      simpa using signed_form_le (hH i) (Or.inl rfl) y
    exact eig_of_ceil (hH i) hceil (by rw [hx1, mul_one]; linarith [h0 i, hex i])
  · have hev := wsum_eig w hy
    have hy0 : y ≠ 0 := fun h => by rw [h] at hy1; simp at hy1
    have := (lmin_le_of_eig hS hy0 hev).2
    have e : ∑ i, w i * opNorm2 (H i) = ∑ i, w i * β i :=
      Finset.sum_congr rfl fun i _ => by rw [hex i]
    rw [e] at this
    exact le_antisymm hle this

end LemmaB41

/-! ### Proposition B4.3(c): the gradient-step factor for quadratic atoms -/

section PropB43

variable {d : ℕ}

/-- The set of Lipschitz constants of T; Lip(T) is its least element. -/
def lipSet {E : Type*} [NormedAddCommGroup E] (T : E → E) : Set ℝ :=
  {K | ∀ x y, ‖T x - T y‖ ≤ K * ‖x - y‖}

lemma isLeast_lipSet_clm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    (f : E →L[ℝ] E) : IsLeast (lipSet f) ‖f‖ := by
  refine ⟨fun x y => by rw [← map_sub]; exact f.le_opNorm _, fun K hK => ?_⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : E)
  have hK0 : 0 ≤ K := by
    have h1 := hK x 0
    simp only [map_zero, sub_zero] at h1
    have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
    by_contra hneg
    push Not at hneg
    nlinarith [norm_nonneg (f x)]
  exact f.opNorm_le_bound hK0 fun z => by simpa using hK z 0

/-- A quadratic atom f(x) = ½⟨Ax, x⟩ − ⟨c, x⟩ on ℝᵈ (G3's `quadAtom` form; p = −c). -/
noncomputable def quadF (A : Matrix (Fin d) (Fin d) ℝ) (c : EuclideanSpace ℝ (Fin d))
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / 2 * inner ℝ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x) x - inner ℝ c x

lemma gradient_quadF {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c x : EuclideanSpace ℝ (Fin d)) :
    gradient (quadF A c) x = Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A x - c :=
  (OCF.G3.hasGradientAt_quad _ c (fun u v => Matrix.isSymmetric_toEuclideanLin_iff.2 hA u v)
    x).gradient

/-- The composite of quadratic atoms is the quadratic atom of (ΣwᵢHᵢ, Σwᵢcᵢ). -/
lemma quadF_wsum {ι : Type*} [Fintype ι] (H : ι → Matrix (Fin d) (Fin d) ℝ) (w : ι → ℝ)
    (c : ι → EuclideanSpace ℝ (Fin d)) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ i, w i * quadF (H i) (c i) x = quadF (∑ i, w i • H i) (∑ i, w i • c i) x := by
  simp only [quadF, map_sum, map_smul, FunLike.coe_sum, FunLike.coe_smul,
    Finset.sum_apply, Pi.smul_apply, sum_inner, inner_smul_left, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [RCLike.conj_to_real]
  ring

/-! The landed moduli of a quadratic atom (landed `prop:spec-moduli`(b), here proved):
σ(f) = λ_min(A) is the greatest σ with C(f, σ); β(f) = ‖A‖₂ is the least β with ∇f
β-Lipschitz; ({0}, ν) is a valid kernel attribute iff A ⪰ νI. -/

lemma grad_diff_quadF {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c x y : EuclideanSpace ℝ (Fin d)) :
    gradient (quadF A c) x - gradient (quadF A c) y =
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A (x - y) := by
  rw [gradient_quadF hA, gradient_quadF hA, map_sub]; abel

lemma inner_clm_self (A : Matrix (Fin d) (Fin d) ℝ) (v : EuclideanSpace ℝ (Fin d)) :
    inner ℝ (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A v) v = v.ofLp ⬝ᵥ A *ᵥ v.ofLp := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]

lemma norm_sq_eq_dot (v : EuclideanSpace ℝ (Fin d)) : ‖v‖ ^ 2 = v.ofLp ⬝ᵥ v.ofLp := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct, star_trivial]

lemma forall_euclid_iff (P : (Fin d → ℝ) → Prop) :
    (∀ v : EuclideanSpace ℝ (Fin d), P v.ofLp) ↔ ∀ x : Fin d → ℝ, P x :=
  ⟨fun h x => by simpa using h (WithLp.toLp 2 x), fun h v => h _⟩

/-- σ(f) for a quadratic atom: C(f, σ) ⟺ σ ≤ λ_min(A); so λ_min(A) = max{σ : C(f, σ)}. -/
theorem modC_quadF_iff [NeZero d] {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c : EuclideanSpace ℝ (Fin d)) (σ : ℝ) : OCF.G3.ModC (quadF A c) σ ↔ σ ≤ lmin A := by
  have hd : Differentiable ℝ (quadF A c) := fun x =>
    (OCF.G3.hasGradientAt_quad _ c (fun u v => Matrix.isSymmetric_toEuclideanLin_iff.2 hA u v)
      x).differentiableAt
  rw [OCF.G3.modC_iff_strongMono hd, le_lmin_iff hA, ← forall_euclid_iff]
  unfold OCF.G3.StrongMono
  simp only [grad_diff_quadF hA, inner_clm_self, ← norm_sq_eq_dot]
  constructor
  · intro h v; simpa using h v 0
  · intro h x y; exact h (x - y)

theorem sigma_quadF [NeZero d] {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c : EuclideanSpace ℝ (Fin d)) : IsGreatest {σ | OCF.G3.ModC (quadF A c) σ} (lmin A) :=
  ⟨(modC_quadF_iff hA c _).2 le_rfl, fun _ h => (modC_quadF_iff hA c _).1 h⟩

/-- β(f) for a quadratic atom: ∇f is β-Lipschitz ⟺ ‖A‖₂ ≤ β; so ‖A‖₂ = min{β : f β-smooth}. -/
theorem beta_quadF [NeZero d] {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c : EuclideanSpace ℝ (Fin d)) : IsLeast {β | OCF.G3.LipGrad (quadF A c) β} (opNorm2 A) := by
  have hset : {β | OCF.G3.LipGrad (quadF A c) β} =
      lipSet (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A) := by
    ext β
    simp only [Set.mem_setOf_eq, OCF.G3.LipGrad, lipSet, grad_diff_quadF hA, map_sub]
  rw [hset]
  exact isLeast_lipSet_clm _

/-- The kernel attribute ({0}, ν) (landed def:kernel-attribute, G3's `KernelValid` with
K = ⊥) is valid for a quadratic atom iff A ⪰ νI. -/
theorem kernelValid_bot_quadF {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c : EuclideanSpace ℝ (Fin d)) (ν : ℝ) :
    OCF.G3.KernelValid (quadF A c) ⊥ ν ↔ ∀ x : Fin d → ℝ, ν * (x ⬝ᵥ x) ≤ x ⬝ᵥ A *ᵥ x := by
  rw [← forall_euclid_iff]
  unfold OCF.G3.KernelValid
  simp only [Submodule.bot_orthogonal_eq_top, Submodule.starProjection_top,
    ContinuousLinearMap.id_apply, grad_diff_quadF hA, inner_clm_self, ← norm_sq_eq_dot]
  constructor
  · intro h v; simpa using h v 0
  · intro h x y; exact h (x - y)

lemma step_sub (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (c : EuclideanSpace ℝ (Fin d))
    (α : ℝ) (x y : EuclideanSpace ℝ (Fin d)) :
    (x - α • gradient (quadF A c) x) - (y - α • gradient (quadF A c) y) =
      Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (1 - α • A) (x - y) := by
  have e : Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (1 - α • A) =
      1 - α • Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) A := by
    rw [map_sub, map_one, map_smul]
  rw [gradient_quadF hA, gradient_quadF hA, e]
  simp only [_root_.sub_apply, one_apply_eq_self,
    _root_.smul_apply, map_sub, smul_sub]
  abel

/-- **Prop. B4.3(c), first clause** (S3.7). For a quadratic F with symmetric Hessian A,
Lip(Id − α∇F) = ‖I − αA‖₂ = q(α; λ_min(A), λ_max(A)), for every real α. -/
theorem propB43_c_lip [NeZero d] {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian)
    (c : EuclideanSpace ℝ (Fin d)) (α : ℝ) :
    IsLeast (lipSet (fun x => x - α • gradient (quadF A c) x)) (qfac α (lmin A) (lmax A)) := by
  have hset : lipSet (fun x => x - α • gradient (quadF A c) x) =
      lipSet (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (1 - α • A)) := by
    ext K
    simp only [lipSet, Set.mem_setOf_eq, step_sub A hA c α, map_sub]
  rw [hset, ← opNorm2_one_sub hA α]
  exact isLeast_lipSet_clm _

/-- **Prop. B4.3(c)** (S3.7–S3.8). Quadratic atoms fᵢ(x) = ½⟨Hᵢx, x⟩ − ⟨cᵢ, x⟩, weights
wᵢ > 0, valid declarations σᵢ ≤ λ_min(Hᵢ), βᵢ ≥ ‖Hᵢ‖₂, F = Σwᵢfᵢ, H = ΣwᵢHᵢ, α > 0:
Lip(Id − α∇F) = q(α; λ_min(H), λ_max(H)) ≤ q(α; σ̂, β̂), with equality iff
[λ_min(H) = σ̂ and 1 − ασ̂ ≥ αβ̂ − 1] or [λ_max(H) = β̂ and αβ̂ − 1 ≥ 1 − ασ̂]. -/
theorem propB43_c [NeZero d] {ι : Type*} [Fintype ι] {H : ι → Matrix (Fin d) (Fin d) ℝ}
    (hH : ∀ i, (H i).IsHermitian) {w : ι → ℝ} (hw : ∀ i, 0 < w i)
    (c : ι → EuclideanSpace ℝ (Fin d)) (σ β : ι → ℝ)
    (hσ : ∀ i, σ i ≤ lmin (H i)) (hβ : ∀ i, opNorm2 (H i) ≤ β i) {α : ℝ} (hα : 0 < α) :
    IsLeast (lipSet (fun x => x - α • gradient (fun z => ∑ i, w i * quadF (H i) (c i) z) x))
        (qfac α (lmin (∑ i, w i • H i)) (lmax (∑ i, w i • H i))) ∧
    qfac α (lmin (∑ i, w i • H i)) (lmax (∑ i, w i • H i)) ≤
        qfac α (∑ i, w i * σ i) (∑ i, w i * β i) ∧
    (qfac α (lmin (∑ i, w i • H i)) (lmax (∑ i, w i • H i)) =
        qfac α (∑ i, w i * σ i) (∑ i, w i * β i) ↔
      (lmin (∑ i, w i • H i) = ∑ i, w i * σ i ∧
          α * (∑ i, w i * β i) - 1 ≤ 1 - α * (∑ i, w i * σ i)) ∨
      (lmax (∑ i, w i • H i) = ∑ i, w i * β i ∧
          1 - α * (∑ i, w i * σ i) ≤ α * (∑ i, w i * β i) - 1)) := by
  have hS := isHermitian_wsum hH w
  have hF : (fun z => ∑ i, w i * quadF (H i) (c i) z) = quadF (∑ i, w i • H i) (∑ i, w i • c i) :=
    funext (quadF_wsum H w c)
  have h1 := (thmB4_i1_sigma hH hw σ hσ).1
  have h2 := (lmax_eq_betaHat_iff hH hw β hβ).1
  have h3 := lmin_le_lmax hS
  rw [hF, lemmaB40_a hα h3, lemmaB40_a hα (h1.trans (h3.trans h2))]
  refine ⟨?_, ?_, ?_⟩
  · rw [← lemmaB40_a hα h3]; exact propB43_c_lip hS _ α
  · exact max_le_max (by nlinarith) (by nlinarith)
  · rw [lemmaB40_b (by nlinarith) (by nlinarith)]
    constructor
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · left; exact ⟨by nlinarith [mul_left_cancel₀ hα.ne' (by linarith : α * lmin (∑ i, w i • H i)
          = α * ∑ i, w i * σ i)], hb⟩
      · right; exact ⟨mul_left_cancel₀ hα.ne' (by linarith), hb⟩
    · rintro (⟨ha, hb⟩ | ⟨ha, hb⟩)
      · left; exact ⟨by rw [ha], hb⟩
      · right; exact ⟨by rw [ha], hb⟩

end PropB43

/-! ### Proposition B4.4: the sign-flip pair in a common square lens (every d ≥ 2) -/

section SignFlip

variable {m : ℕ}

/-- E_s := [[1, s/2], [s/2, 1]] ⊕ I_{d−2} on ℝᵈ, d = m + 2; E₊ = E 1, E₋ = E (−1). -/
noncomputable def Emat (s : ℝ) : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ :=
  Matrix.of fun i j => (if i = j then 1 else 0) +
    s / 2 * ((if i = 0 ∧ j = 1 then 1 else 0) + (if i = 1 ∧ j = 0 then 1 else 0))

lemma Emat_apply (s : ℝ) (i j : Fin (m + 2)) : Emat s i j = (if i = j then 1 else 0) +
    s / 2 * ((if i = 0 ∧ j = 1 then 1 else 0) + (if i = 1 ∧ j = 0 then 1 else 0)) := rfl

lemma Emat_isHermitian (s : ℝ) : (Emat (m := m) s).IsHermitian := by
  ext i j
  simp only [conjTranspose_apply, star_trivial, Emat_apply]
  by_cases h1 : i = j
  · subst h1; rfl
  · rw [if_neg h1, if_neg (Ne.symm h1)]
    by_cases a : i = 0 <;> by_cases b : j = 1 <;> by_cases c : i = 1 <;> by_cases e : j = 0 <;>
      simp_all

lemma Emat_mulVec (s : ℝ) (y : Fin (m + 2) → ℝ) :
    Emat s *ᵥ y = y + (s / 2) • (Pi.single 0 (y 1) + Pi.single 1 (y 0)) := by
  ext i
  simp only [mulVec, dotProduct, Emat_apply, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_add, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, ite_and]
  by_cases h0 : i = 0
  · subst h0; simp
  · by_cases h1 : i = 1
    · subst h1; simp
    · simp [h0, h1]

lemma dot_self_ge_two (y : Fin (m + 2) → ℝ) : y 0 ^ 2 + y 1 ^ 2 ≤ y ⬝ᵥ y := by
  simp only [dotProduct, Fin.sum_univ_succ]
  have : 0 ≤ ∑ i : Fin m, y i.succ.succ * y i.succ.succ :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  simp only [Fin.succ_zero_eq_one]
  nlinarith

lemma Emat_form (s : ℝ) (y : Fin (m + 2) → ℝ) :
    y ⬝ᵥ Emat s *ᵥ y = y ⬝ᵥ y + s * (y 0 * y 1) := by
  rw [Emat_mulVec, dotProduct_add, dotProduct_smul, dotProduct_add]
  simp only [dotProduct_single, smul_eq_mul]
  ring

lemma Emat_floor {s : ℝ} (hs : s ^ 2 = 1) (y : Fin (m + 2) → ℝ) :
    1 / 2 * (y ⬝ᵥ y) ≤ y ⬝ᵥ Emat s *ᵥ y := by
  rw [Emat_form]
  nlinarith [dot_self_ge_two y, sq_nonneg (y 0 + s * y 1)]

lemma Emat_ceil {s : ℝ} (hs : s ^ 2 = 1) (y : Fin (m + 2) → ℝ) :
    y ⬝ᵥ Emat s *ᵥ y ≤ 3 / 2 * (y ⬝ᵥ y) := by
  rw [Emat_form]
  nlinarith [dot_self_ge_two y, sq_nonneg (y 0 - s * y 1)]

/-- Eigenvectors e₀ ∓ s e₁ (eigenvalues ½, 3/2). -/
lemma Emat_eig_low {s : ℝ} (hs : s ^ 2 = 1) :
    Emat (m := m) s *ᵥ (Pi.single 0 1 - s • Pi.single 1 1) =
      (1 / 2 : ℝ) • (Pi.single 0 1 - s • Pi.single 1 1) := by
  rw [Emat_mulVec]
  ext i
  by_cases h0 : i = 0
  · subst h0; simp; nlinarith
  · by_cases h1 : i = 1
    · subst h1; simp; ring
    · simp [h0, h1]

lemma Emat_eig_high {s : ℝ} (hs : s ^ 2 = 1) :
    Emat (m := m) s *ᵥ (Pi.single 0 1 + s • Pi.single 1 1) =
      (3 / 2 : ℝ) • (Pi.single 0 1 + s • Pi.single 1 1) := by
  rw [Emat_mulVec]
  ext i
  by_cases h0 : i = 0
  · subst h0; simp; nlinarith
  · by_cases h1 : i = 1
    · subst h1; simp; ring
    · simp [h0, h1]

lemma vec_ne_zero (t : ℝ) : (Pi.single 0 1 + t • Pi.single 1 1 : Fin (m + 2) → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

lemma Emat_add_neg : Emat (m := m) 1 + Emat (-1) = (2 : ℝ) • 1 := by
  ext i j
  simp only [Matrix.add_apply, Emat_apply, Matrix.smul_apply, one_apply, smul_eq_mul]
  split_ifs <;> ring

/-- The reflection J = diag(1, −1, 1, …, 1): J E₊ J = E₋. -/
def Jmat : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ := diagonal fun i => if i = 1 then -1 else 1

lemma Jmat_mul_self : Jmat (m := m) * Jmat = 1 := by
  rw [Jmat, diagonal_mul_diagonal, ← diagonal_one]
  congr 1; funext i; split_ifs <;> norm_num

lemma Jmat_conj : Jmat * Emat (m := m) 1 * Jmat = Emat (-1) := by
  ext i j
  rw [Jmat, mul_diagonal, diagonal_mul, Emat_apply, Emat_apply]
  by_cases a : i = 0 <;> by_cases b : j = 1 <;> by_cases c : i = 1 <;> by_cases e : j = 0 <;>
    by_cases f : i = j <;> simp_all <;> norm_num

/-! Orthogonal conjugation -/

variable {O : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}

lemma form_conj (M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (y : Fin (m + 2) → ℝ) :
    y ⬝ᵥ (Oᵀ * M * O) *ᵥ y = (O *ᵥ y) ⬝ᵥ M *ᵥ (O *ᵥ y) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]

lemma dot_orth (hO : Oᵀ * O = 1) (y : Fin (m + 2) → ℝ) : (O *ᵥ y) ⬝ᵥ (O *ᵥ y) = y ⬝ᵥ y := by
  have := form_conj (O := O) 1 y
  rw [Matrix.mul_one, hO, one_mulVec, one_mulVec] at this
  exact this.symm

lemma isHermitian_conj' {M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} (hM : M.IsHermitian) :
    (Oᵀ * M * O).IsHermitian := by
  have := isHermitian_conjTranspose_mul_mul O hM
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma conj_eigvec (hO' : O * Oᵀ = 1) {M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} {μ : ℝ}
    {v : Fin (m + 2) → ℝ} (hev : M *ᵥ v = μ • v) :
    (Oᵀ * M * O) *ᵥ (Oᵀ *ᵥ v) = μ • (Oᵀ *ᵥ v) := by
  have h : O *ᵥ (Oᵀ *ᵥ v) = v := by rw [mulVec_mulVec, hO', one_mulVec]
  rw [← mulVec_mulVec, ← mulVec_mulVec, h, hev, mulVec_smul]

lemma transpose_mulVec_ne (hO' : O * Oᵀ = 1) {v : Fin (m + 2) → ℝ} (hv : v ≠ 0) :
    Oᵀ *ᵥ v ≠ 0 := by
  intro h
  apply hv
  have := congrArg (fun z => O *ᵥ z) h
  simpa [mulVec_mulVec, hO'] using this

lemma lmin_conj (hO : Oᵀ * O = 1) (hO' : O * Oᵀ = 1) {M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}
    (hM : M.IsHermitian) {μ : ℝ} (hfl : ∀ z, μ * (z ⬝ᵥ z) ≤ z ⬝ᵥ M *ᵥ z) {v : Fin (m + 2) → ℝ}
    (hv : v ≠ 0) (hev : M *ᵥ v = μ • v) : lmin (Oᵀ * M * O) = μ :=
  lmin_eq_of (isHermitian_conj' hM)
    (fun y => by rw [form_conj, ← dot_orth hO y]; exact hfl _)
    (transpose_mulVec_ne hO' hv) (conj_eigvec hO' hev)

lemma lmax_conj (hO : Oᵀ * O = 1) (hO' : O * Oᵀ = 1) {M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ}
    (hM : M.IsHermitian) {μ : ℝ} (hcl : ∀ z, z ⬝ᵥ M *ᵥ z ≤ μ * (z ⬝ᵥ z)) {v : Fin (m + 2) → ℝ}
    (hv : v ≠ 0) (hev : M *ᵥ v = μ • v) : lmax (Oᵀ * M * O) = μ :=
  lmax_eq_of (isHermitian_conj' hM)
    (fun y => by rw [form_conj, ← dot_orth hO y]; exact hcl _)
    (transpose_mulVec_ne hO' hv) (conj_eigvec hO' hev)

lemma charpoly_conj (hO' : O * Oᵀ = 1) (M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) :
    (Oᵀ * M * O).charpoly = M.charpoly := by
  rw [Matrix.mul_assoc, charpoly_mul_comm, Matrix.mul_assoc, hO', Matrix.mul_one]

/-! The square lens W (WᵀW = cI, c > 0) and O := c^{−1/2}W -/

variable {W : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} {c : ℝ}

lemma lens_WWt (hc : 0 < c) (hW : Wᵀ * W = c • 1) : W * Wᵀ = c • 1 := by
  have h1 : (c⁻¹ • Wᵀ) * W = 1 := by
    rw [Matrix.smul_mul, hW, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have h2 := mul_eq_one_comm.1 h1
  rw [Matrix.mul_smul] at h2
  have := congrArg (fun M => c • M) h2
  simpa [smul_smul, mul_inv_cancel₀ hc.ne'] using this

lemma lens_O (hc : 0 < c) (hW : Wᵀ * W = c • 1) :
    ((Real.sqrt c)⁻¹ • W)ᵀ * ((Real.sqrt c)⁻¹ • W) = 1 ∧
    ((Real.sqrt c)⁻¹ • W) * ((Real.sqrt c)⁻¹ • W)ᵀ = 1 := by
  have hs : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  constructor
  · rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, hW, smul_smul, smul_smul, hs, one_smul]
  · rw [transpose_smul, Matrix.smul_mul, Matrix.mul_smul, lens_WWt hc hW, smul_smul, smul_smul, hs,
      one_smul]

lemma lens_conj (hc : 0 < c) (hW : Wᵀ * W = c • 1) (M : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) :
    conj W (((Real.sqrt c)⁻¹ • W)ᵀ * M * ((Real.sqrt c)⁻¹ • W)) = c • M := by
  have hs : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  have hWW := lens_WWt hc hW
  set O := (Real.sqrt c)⁻¹ • W
  have h1 : W * Oᵀ = ((Real.sqrt c)⁻¹ * c) • 1 := by
    rw [transpose_smul, Matrix.mul_smul, hWW, smul_smul]
  have h2 : O * Wᵀ = ((Real.sqrt c)⁻¹ * c) • 1 := by
    rw [Matrix.smul_mul, hWW, smul_smul]
  have e : conj W (Oᵀ * M * O) = (W * Oᵀ) * M * (O * Wᵀ) := by
    simp only [conj, Matrix.mul_assoc]
  rw [e, h1, h2, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, Matrix.mul_one, smul_smul]
  congr 1
  calc (Real.sqrt c)⁻¹ * c * ((Real.sqrt c)⁻¹ * c) = ((Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ * c) * c
        := by ring
    _ = c := by rw [hs, one_mul]

/-! η of the lens matrices -/

lemma gershRadius_Emat {s : ℝ} (hs : s ^ 2 = 1) (i : Fin (m + 2)) :
    gershRadius (Emat s) i = if i = 0 ∨ i = 1 then 1 / 2 else 0 := by
  have habs : |s| = 1 := by
    have : |s| ^ 2 = 1 := by rw [sq_abs]; exact hs
    nlinarith [abs_nonneg s]
  have h01 : (0 : Fin (m + 2)) ≠ 1 := by simp
  unfold gershRadius
  by_cases h0 : i = 0
  · subst h0
    rw [Finset.sum_eq_single (1 : Fin (m + 2))]
    · simp [Emat_apply, abs_div, habs]
    · intro b hb' hb
      have := Finset.ne_of_mem_erase hb'
      rw [Emat_apply]; simp [hb, Ne.symm this]
    · intro h; exact absurd (Finset.mem_erase.2 ⟨h01.symm, Finset.mem_univ _⟩) h
  · by_cases h1 : i = 1
    · subst h1
      rw [Finset.sum_eq_single (0 : Fin (m + 2))]
      · simp [Emat_apply, abs_div, habs]
      · intro b hb' hb
        have := Finset.ne_of_mem_erase hb'
        rw [Emat_apply]; simp [hb, Ne.symm this]
      · intro h; exact absurd (Finset.mem_erase.2 ⟨h01, Finset.mem_univ _⟩) h
    · rw [if_neg (by tauto)]
      refine Finset.sum_eq_zero fun j hj => ?_
      rw [Emat_apply, if_neg (Finset.ne_of_mem_erase hj).symm]
      simp [h0, h1]

lemma domRatio_Emat {s : ℝ} (hs : s ^ 2 = 1) : domRatio (Emat (m := m) s) = 1 / 2 := by
  have hd : ∀ i : Fin (m + 2), Emat s i i = 1 := fun i => by
    rw [Emat_apply]
    by_cases h0 : i = 0
    · subst h0; simp
    · simp [h0]
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    rw [gershRadius_Emat hs, hd]
    split_ifs <;> norm_num
  · have := le_ciSup (Finite.bddAbove_range (fun i => gershRadius (Emat (m := m) s) i /
      Emat s i i)) 0
    rw [gershRadius_Emat hs, hd] at this
    unfold domRatio
    simpa using this

lemma domRatio_one : domRatio (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) = 0 := by
  unfold domRatio gershRadius
  have : ∀ i : Fin (m + 2), ∑ j ∈ Finset.univ.erase i, |(1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) i j|
      = 0 := fun i => Finset.sum_eq_zero fun j hj => by
    rw [one_apply_ne (Finset.ne_of_mem_erase hj).symm, abs_zero]
  simp [this]

/-! The atoms f± and the families P = (f₊, f₊), M = (f₊, f₋) -/

lemma quadF_add (A B : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ) (z : EuclideanSpace ℝ (Fin (m + 2))) :
    quadF A 0 z + quadF B 0 z = quadF (A + B) 0 z := by
  simp only [quadF, map_add, _root_.add_apply, inner_add_left, inner_zero_left]
  ring

lemma qfac_two_lt {α : ℝ} (hα : 0 < α) : qfac α 2 2 < qfac α 1 3 := by
  unfold qfac
  rw [max_self]
  rcases le_total α (1 / 2) with h | h
  · rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - α * 2)]
    exact lt_of_lt_of_le (by linarith) ((le_abs_self _).trans (le_max_left _ _))
  · rw [abs_of_nonpos (by linarith : 1 - α * 2 ≤ 0)]
    exact lt_of_lt_of_le (by linarith) ((neg_le_abs _).trans (le_max_right _ _))

lemma Emat_diag (s : ℝ) (i : Fin (m + 2)) : Emat s i i = 1 := by
  rw [Emat_apply]
  by_cases h0 : i = 0
  · subst h0; simp
  · simp [h0]

lemma Emat_abs (i j : Fin (m + 2)) : |Emat 1 i j| = |Emat (-1) i j| := by
  rw [Emat_apply, Emat_apply]
  by_cases a : i = 0 <;> by_cases b : j = 1 <;> by_cases c : i = 1 <;> by_cases e : j = 0 <;>
    by_cases f : i = j <;> simp_all <;> norm_num

lemma vec_ne_zero_sub (t : ℝ) : (Pi.single 0 1 - t • Pi.single 1 1 : Fin (m + 2) → ℝ) ≠ 0 := by
  intro h
  have := congrFun h 0
  simp at this

lemma Emat_two_floor {s : ℝ} (hs : s ^ 2 = 1) (y : Fin (m + 2) → ℝ) :
    1 * (y ⬝ᵥ y) ≤ y ⬝ᵥ (Emat s + Emat s) *ᵥ y := by
  rw [add_mulVec, dotProduct_add]; linarith [Emat_floor hs y]

lemma Emat_two_ceil {s : ℝ} (hs : s ^ 2 = 1) (y : Fin (m + 2) → ℝ) :
    y ⬝ᵥ (Emat s + Emat s) *ᵥ y ≤ 3 * (y ⬝ᵥ y) := by
  rw [add_mulVec, dotProduct_add]; linarith [Emat_ceil hs y]

/-- **Proposition B4.4** (sign-flip pair in a common square lens; S4.1–S4.7), for every
d = m + 2 ≥ 2 and every square lens W ∈ ℝ^{d×d} with WᵀW = cI_d, c > 0. With
O := c^{−1/2}W, H± := OᵀE±O and the quadratic atoms f±(x) = ½⟨H±x, x⟩:
1. the per-atom records in W coincide: (H±)_W = cE± (equal diagonals, equal entrywise
   absolute values), equal spectra with multiplicities (equal characteristic polynomials,
   hence equal ordered eigenvalues), η = ½, σ(f±) = λ_min = ½, λ_max = 3/2,
   β(f±) = ‖H±‖₂ = 3/2, and ({0}, ν) is a valid kernel attribute iff ν ≤ ½;
2. the unit-weight composites P = f₊ + f₊ and M = f₊ + f₋ differ: η(H_W) = ½ resp. 0,
   λ_min(H) = σ(F) = 1 resp. 2, λ_max(H) = ‖H‖₂ = β(F) = 3 resp. 2,
   Lip(Id − α∇F) = q(α; 1, 3) resp. |1 − 2α| < q(α; 1, 3) for every α > 0.
With the exact declarations σᵢ = ½, βᵢ = 3/2 the inherited bounds are σ̂ = 1, β̂ = 3,
maxᵢ η = ½, Δ_w = 1 (`propB44_deltaW`): P attains every one and M is strictly inside
every one. -/
theorem propB44 {W : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • 1) :
    let O := (Real.sqrt c)⁻¹ • W
    let Hp := Oᵀ * Emat 1 * O
    let Hm := Oᵀ * Emat (-1) * O
    ∃ (hp : Hp.IsHermitian) (hm : Hm.IsHermitian),
    -- 1. equal per-atom records in the lens W
    conj W Hp = c • Emat 1 ∧ conj W Hm = c • Emat (-1) ∧
    (∀ i, conj W Hp i i = c ∧ conj W Hm i i = c) ∧
    (∀ i j, |conj W Hp i j| = |conj W Hm i j|) ∧
    Hp.charpoly = Hm.charpoly ∧ hp.eigenvalues = hm.eigenvalues ∧
    domRatio (conj W Hp) = 1 / 2 ∧ domRatio (conj W Hm) = 1 / 2 ∧
    lmin Hp = 1 / 2 ∧ lmin Hm = 1 / 2 ∧ lmax Hp = 3 / 2 ∧ lmax Hm = 3 / 2 ∧
    opNorm2 Hp = 3 / 2 ∧ opNorm2 Hm = 3 / 2 ∧
    (∀ ν : ℝ, OCF.G3.KernelValid (quadF Hp 0) ⊥ ν ↔ ν ≤ 1 / 2) ∧
    (∀ ν : ℝ, OCF.G3.KernelValid (quadF Hm 0) ⊥ ν ↔ ν ≤ 1 / 2) ∧
    -- 2. the composites differ
    conj W (Hp + Hp) = (2 * c) • Emat 1 ∧ conj W (Hp + Hm) = (2 * c) • 1 ∧
    domRatio (conj W (Hp + Hp)) = 1 / 2 ∧ domRatio (conj W (Hp + Hm)) = 0 ∧
    lmin (Hp + Hp) = 1 ∧ lmin (Hp + Hm) = 2 ∧
    lmax (Hp + Hp) = 3 ∧ lmax (Hp + Hm) = 2 ∧
    opNorm2 (Hp + Hp) = 3 ∧ opNorm2 (Hp + Hm) = 2 ∧
    (∀ α : ℝ, IsLeast (lipSet (fun x => x - α • gradient
      (fun z => quadF Hp 0 z + quadF Hp 0 z) x)) (qfac α 1 3)) ∧
    (∀ α : ℝ, IsLeast (lipSet (fun x => x - α • gradient
      (fun z => quadF Hp 0 z + quadF Hm 0 z) x)) |1 - 2 * α|) ∧
    (∀ α : ℝ, 0 < α → |1 - 2 * α| < qfac α 1 3) := by
  intro O Hp Hm
  obtain ⟨hO, hO'⟩ := lens_O hc hW
  have s1 : (1 : ℝ) ^ 2 = 1 := by norm_num
  have s2 : (-1 : ℝ) ^ 2 = 1 := by norm_num
  have hE1 := Emat_isHermitian (m := m) 1
  have hE2 := Emat_isHermitian (m := m) (-1)
  have hp : Hp.IsHermitian := isHermitian_conj' hE1
  have hm : Hm.IsHermitian := isHermitian_conj' hE2
  have hPP : Hp + Hp = Oᵀ * (Emat 1 + Emat 1) * O := by
    simp only [Hp, Matrix.mul_add, Matrix.add_mul]
  have hPM : Hp + Hm = (2 : ℝ) • 1 := by
    simp only [Hp, Hm, ← Matrix.add_mul, ← Matrix.mul_add, Emat_add_neg, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul]
    rw [show Oᵀ * O = 1 from hO]
  have hEE : (Emat (m := m) 1 + Emat 1).IsHermitian := hE1.add hE1
  have hpp : (Hp + Hp).IsHermitian := hp.add hp
  have hpm : (Hp + Hm).IsHermitian := hp.add hm
  have cp : conj W Hp = c • Emat 1 := lens_conj hc hW _
  have cm : conj W Hm = c • Emat (-1) := lens_conj hc hW _
  have cpp : conj W (Hp + Hp) = (2 * c) • Emat 1 := by
    rw [hPP, lens_conj hc hW, smul_add, ← add_smul]; ring_nf
  have cpm : conj W (Hp + Hm) = (2 * c) • 1 := by
    rw [hPM, conj, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, lens_WWt hc hW, smul_smul]
  have lp : lmin Hp = 1 / 2 := lmin_conj hO hO' hE1 (Emat_floor s1) (vec_ne_zero_sub 1)
    (Emat_eig_low s1)
  have lm : lmin Hm = 1 / 2 := lmin_conj hO hO' hE2 (Emat_floor s2) (vec_ne_zero_sub (-1))
    (Emat_eig_low s2)
  have up : lmax Hp = 3 / 2 := lmax_conj hO hO' hE1 (Emat_ceil s1) (vec_ne_zero 1)
    (Emat_eig_high s1)
  have um : lmax Hm = 3 / 2 := lmax_conj hO hO' hE2 (Emat_ceil s2) (vec_ne_zero (-1))
    (Emat_eig_high s2)
  have lpp : lmin (Hp + Hp) = 1 := by
    rw [hPP]
    refine lmin_conj hO hO' hEE (Emat_two_floor s1) (vec_ne_zero_sub 1) ?_
    rw [add_mulVec, Emat_eig_low s1, ← add_smul]; norm_num
  have upp : lmax (Hp + Hp) = 3 := by
    rw [hPP]
    refine lmax_conj hO hO' hEE (Emat_two_ceil s1) (vec_ne_zero 1) ?_
    rw [add_mulVec, Emat_eig_high s1, ← add_smul]; norm_num
  have h2I : ∀ y : Fin (m + 2) → ℝ, y ⬝ᵥ ((2 : ℝ) • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ))
      *ᵥ y = 2 * (y ⬝ᵥ y) := fun y => by
    rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul]
  have hsingle : (Pi.single 0 1 : Fin (m + 2) → ℝ) ≠ 0 := by
    intro h; have := congrFun h 0; simp at this
  have hev2 : ((2 : ℝ) • (1 : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ)) *ᵥ Pi.single 0 1 =
      (2 : ℝ) • Pi.single 0 1 := by rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have lpm : lmin (Hp + Hm) = 2 := by
    rw [hPM]
    exact lmin_eq_of (hPM ▸ hpm) (fun y => (h2I y).ge) hsingle hev2
  have upm : lmax (Hp + Hm) = 2 := by
    rw [hPM]
    exact lmax_eq_of (hPM ▸ hpm) (fun y => (h2I y).le) hsingle hev2
  have np : opNorm2 Hp = 3 / 2 := by
    rw [opNorm2_eq hp, lp, up]; norm_num [abs_of_pos]
  have nm : opNorm2 Hm = 3 / 2 := by
    rw [opNorm2_eq hm, lm, um]; norm_num [abs_of_pos]
  have npp : opNorm2 (Hp + Hp) = 3 := by
    rw [opNorm2_eq hpp, lpp, upp]; norm_num
  have npm : opNorm2 (Hp + Hm) = 2 := by
    rw [opNorm2_eq hpm, lpm, upm]; norm_num
  have chp : Hp.charpoly = Hm.charpoly := by
    simp only [Hp, Hm]
    rw [charpoly_conj hO', charpoly_conj hO', ← Jmat_conj, Matrix.mul_assoc, charpoly_mul_comm,
      Matrix.mul_assoc, Jmat_mul_self, Matrix.mul_one]
  have hF1 : (fun z => quadF Hp 0 z + quadF Hp 0 z) = quadF (Hp + Hp) 0 :=
    funext fun z => quadF_add _ _ z
  have hF2 : (fun z => quadF Hp 0 z + quadF Hm 0 z) = quadF (Hp + Hm) 0 :=
    funext fun z => quadF_add _ _ z
  refine ⟨hp, hm, cp, cm, fun i => ?_, fun i j => ?_, chp,
    (hp.eigenvalues_eq_eigenvalues_iff hm).2 chp, ?_, ?_, lp, lm, up, um, np, nm,
    fun ν => ?_, fun ν => ?_, cpp, cpm, ?_, ?_, lpp, lpm, upp, upm, npp, npm,
    fun α => ?_, fun α => ?_, fun α hα => ?_⟩
  · rw [cp, cm]; simp [Emat_diag]
  · rw [cp, cm]; simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, Emat_abs]
  · rw [cp, domRatio_smul hc, domRatio_Emat s1]
  · rw [cm, domRatio_smul hc, domRatio_Emat s2]
  · rw [kernelValid_bot_quadF hp, ← le_lmin_iff hp, lp]
  · rw [kernelValid_bot_quadF hm, ← le_lmin_iff hm, lm]
  · rw [cpp, domRatio_smul (by linarith), domRatio_Emat s1]
  · rw [cpm, domRatio_smul (by linarith), domRatio_one]
  · have := propB43_c_lip hpp 0 α
    rwa [lpp, upp, ← hF1] at this
  · have := propB43_c_lip hpm 0 α
    rw [lpm, upm, ← hF2] at this
    simpa [qfac, mul_comm] using this
  · have := qfac_two_lt hα
    simpa [qfac, mul_comm] using this

/-- Δ_w of the sign-flip families (S4.7): each atom carries ({0}, ½), i.e. an empty kernel
basis and weight wᵢνᵢ = ½, so Δ_w = Σwᵢνᵢ − λ_max(empty Gram) = 1 (T1's `deltaW`). -/
theorem propB44_deltaW :
    OCF.deltaW (n := 2) (k := fun _ => 0) (fun _ p => (Fin.elim0 p : Fin (m + 2) → ℝ))
      (fun _ => (1 : ℝ) * (1 / 2)) = 1 := by
  unfold OCF.deltaW OCF.lambdaMax
  haveI : IsEmpty ((i : Fin 2) × Fin ((fun _ => 0) i)) := ⟨fun z => z.2.elim0⟩
  split_ifs with h
  · rw [Real.iSup_of_isEmpty]; norm_num
  · norm_num

/-- At d = 2 the matrices are the dossier's E± = [[1, ±½], [±½, 1]]. -/
lemma Emat_two (s : ℝ) : Emat (m := 0) s = !![1, s / 2; s / 2, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Emat_apply]

/-- **Proposition B4.4 at d = 2, W = I** (the adjudicator's cheap target): the explicit pair
E₊ = [[1, ½], [½, 1]], E₋ = [[1, −½], [−½, 1]]. -/
theorem propB44_d2 :
    let Ep : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1]
    let Em : Matrix (Fin 2) (Fin 2) ℝ := !![1, -1 / 2; -1 / 2, 1]
    (∀ i, Ep i i = Em i i) ∧ (∀ i j, |Ep i j| = |Em i j|) ∧ Ep.charpoly = Em.charpoly ∧
    domRatio Ep = 1 / 2 ∧ domRatio Em = 1 / 2 ∧
    lmin Ep = 1 / 2 ∧ lmin Em = 1 / 2 ∧ lmax Ep = 3 / 2 ∧ lmax Em = 3 / 2 ∧
    opNorm2 Ep = 3 / 2 ∧ opNorm2 Em = 3 / 2 ∧
    domRatio (Ep + Ep) = 1 / 2 ∧ domRatio (Ep + Em) = 0 ∧
    lmin (Ep + Ep) = 1 ∧ lmin (Ep + Em) = 2 ∧ lmax (Ep + Ep) = 3 ∧ lmax (Ep + Em) = 2 ∧
    opNorm2 (Ep + Ep) = 3 ∧ opNorm2 (Ep + Em) = 2 ∧
    (∀ α : ℝ, IsLeast (lipSet (fun x => x - α • gradient
      (fun z => quadF Ep 0 z + quadF Ep 0 z) x)) (qfac α 1 3)) ∧
    (∀ α : ℝ, IsLeast (lipSet (fun x => x - α • gradient
      (fun z => quadF Ep 0 z + quadF Em 0 z) x)) |1 - 2 * α|) ∧
    (∀ α : ℝ, 0 < α → |1 - 2 * α| < qfac α 1 3) := by
  intro Ep Em
  have hW : (1 : Matrix (Fin 2) (Fin 2) ℝ)ᵀ * 1 = (1 : ℝ) • 1 := by simp
  obtain ⟨hp, hm, cp, cm, hdiag, habs, chp, -, dp, dm, lp, lm, up, um, np, nm, -, -, cpp, cpm,
    dpp, dpm, lpp, lpm, upp, upm, npp, npm, lipP, lipM, strict⟩ := propB44 (m := 0) one_pos hW
  have hO : (Real.sqrt 1)⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ) = 1 := by simp
  have eP : Ep = Emat (m := 0) 1 := by rw [Emat_two]
  have eM : Em = Emat (m := 0) (-1) := by rw [Emat_two]
  simp only [hO, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one, one_smul] at *
  rw [← eP, ← eM] at *
  have c1 : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, conj 1 M = M := fun M => by simp [conj]
  simp only [c1] at *
  exact ⟨fun i => by rw [(hdiag i).1, (hdiag i).2], habs, chp, dp, dm, lp, lm, up, um, np, nm,
    dpp, dpm, lpp, lpm, upp, upm, npp, npm, lipP, lipM, strict⟩

end SignFlip

/-! ### Theorem B4 (ii)(a): nothing is determined by per-atom data (common square lens) -/

/-- The per-atom record of a quadratic atom with Hessian H in the square lens W (S0.6):
the spectrum with multiplicities (as the characteristic polynomial), the diagonal of
H_W = WHWᵀ, and the entrywise absolute values of H_W. -/
noncomputable def record {d : ℕ} (W H : Matrix (Fin d) (Fin d) ℝ) :
    Polynomial ℝ × (Fin d → ℝ) × (Fin d → Fin d → ℝ) :=
  (H.charpoly, fun i => conj W H i i, fun i j => |conj W H i j|)

/-- Valid declared attributes (σ, β, ν) of a quadratic atom with Hessian H, the kernel
attribute being ({0}, ν), ν > 0 (landed def:energy-spec, def:kernel-attribute). -/
def ValidDecl {d : ℕ} (H : Matrix (Fin d) (Fin d) ℝ) (a : ℝ × ℝ × ℝ) : Prop :=
  OCF.G3.ModC (quadF H 0) a.1 ∧ OCF.G3.LipGrad (quadF H 0) a.2.1 ∧ 0 < a.2.2 ∧
    OCF.G3.KernelValid (quadF H 0) ⊥ a.2.2

/-- Per-atom data (wᵢ, rec_W(fᵢ), declared attributes) of a two-atom family. -/
abbrev AtomData (d : ℕ) := ℝ × (Polynomial ℝ × (Fin d → ℝ) × (Fin d → Fin d → ℝ)) × (ℝ × ℝ × ℝ)

/-- A composite quantity q is determined by per-atom data if some Φ computes q(w₁H₁ + w₂H₂)
from the two atoms' data, for every pair of quadratic atoms and every valid declaration. -/
def Determined {d : ℕ} (W : Matrix (Fin d) (Fin d) ℝ) (q : Matrix (Fin d) (Fin d) ℝ → ℝ) : Prop :=
  ∃ Φ : AtomData d → AtomData d → ℝ, ∀ (H₁ H₂ : Matrix (Fin d) (Fin d) ℝ) (w₁ w₂ : ℝ)
    (a₁ a₂ : ℝ × ℝ × ℝ), H₁.IsHermitian → H₂.IsHermitian → 0 < w₁ → 0 < w₂ →
    ValidDecl H₁ a₁ → ValidDecl H₂ a₂ →
    q (w₁ • H₁ + w₂ • H₂) = Φ (w₁, record W H₁, a₁) (w₂, record W H₂, a₂)

/-- **Theorem B4 (ii)(a)** (via Prop. B4.4). Let d = m + 2 ≥ 2 and W a square lens
(WᵀW = cI, c > 0). None of η(H_W), σ(F) = λ_min(H), λ_max(H), β(F) = ‖H‖₂, or
Lip(Id − α∇F) (any α > 0) is a function of the per-atom data (wᵢ, rec_W(fᵢ), valid
declared attributes including the kernel attribute). -/
theorem thmB4_ii_a {m : ℕ} {W : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • 1) :
    ¬ Determined W (fun H => domRatio (conj W H)) ∧ ¬ Determined W lmin ∧
    ¬ Determined W lmax ∧ ¬ Determined W opNorm2 ∧
    ∀ α : ℝ, 0 < α → ¬ Determined W (fun H => sInf (lipSet (fun x => x - α • gradient
      (quadF H 0) x))) := by
  obtain ⟨hp, hm, cp, cm, hdiag, habs, chp, -, -, -, lp, lm, up, um, np, nm, kp, km, -, -,
    dpp, dpm, lpp, lpm, upp, upm, npp, npm, lipP, lipM, strict⟩ := propB44 (m := m) hc hW
  set O := (Real.sqrt c)⁻¹ • W
  set Hp := Oᵀ * Emat 1 * O
  set Hm := Oᵀ * Emat (-1) * O
  have hrec : record W Hp = record W Hm := by
    unfold record
    rw [chp]
    congr 1
    congr 1
    · funext i; rw [(hdiag i).1, (hdiag i).2]
    · funext i j; exact habs i j
  have hv : ∀ H : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ, H.IsHermitian → lmin H = 1 / 2 →
      opNorm2 H = 3 / 2 → (∀ ν : ℝ, OCF.G3.KernelValid (quadF H 0) ⊥ ν ↔ ν ≤ 1 / 2) →
      ValidDecl H (1 / 2, 3 / 2, 1 / 2) := fun H hH hl hn hk =>
    ⟨(modC_quadF_iff hH 0 _).2 hl.ge, ((beta_quadF hH 0).1 : _) |> fun h => by
      simpa [hn] using h, by norm_num, (hk _).2 le_rfl⟩
  have vp := hv Hp hp lp np kp
  have vm := hv Hm hm lm nm km
  -- a determined quantity takes equal values on the two families
  have key : ∀ q : Matrix (Fin (m + 2)) (Fin (m + 2)) ℝ → ℝ, Determined W q →
      q (Hp + Hp) = q (Hp + Hm) := by
    rintro q ⟨Φ, hΦ⟩
    have e1 := hΦ Hp Hp 1 1 _ _ hp hp one_pos one_pos vp vp
    have e2 := hΦ Hp Hm 1 1 _ _ hp hm one_pos one_pos vp vm
    simp only [one_smul] at e1 e2
    rw [e1, e2, hrec]
  have hF1 : (fun z => quadF Hp 0 z + quadF Hp 0 z) = quadF (Hp + Hp) 0 :=
    funext fun z => quadF_add _ _ z
  have hF2 : (fun z => quadF Hp 0 z + quadF Hm 0 z) = quadF (Hp + Hm) 0 :=
    funext fun z => quadF_add _ _ z
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, fun α hα h => ?_⟩
  · have := key _ h; simp only [dpp, dpm] at this; norm_num at this
  · have := key _ h; rw [lpp, lpm] at this; norm_num at this
  · have := key _ h; rw [upp, upm] at this; norm_num at this
  · have := key _ h; rw [npp, npm] at this; norm_num at this
  · have := key _ h
    have a1 := (lipP α).csInf_eq
    have a2 := (lipM α).csInf_eq
    rw [hF1] at a1; rw [hF2] at a2
    rw [a1, a2] at this
    exact absurd this (strict α hα).ne'

/-! ### Theorem B4 (ii)(b): the own-lens record on both sides of the threshold (S5.5a) -/

section OwnLens

open OCF.B6 (instance_1_3 lemma1_atom1 lemma1_atom2 lemma5_theta ellW)

/-- The atoms' spectra do not depend on θ: λ_min(H₂) = δ, λ_max(H₂) = 1 + δ for
H₂ = vvᵀ + δI, v = (ξ, ζ) unit. -/
lemma atom2_spectrum {ξ ζ : ℝ} (h : ξ ^ 2 + ζ ^ 2 = 1) (δ : ℝ) :
    lmin (atom2 ξ ζ δ) = δ ∧ lmax (atom2 ξ ζ δ) = 1 + δ := by
  have hA : (atom2 ξ ζ δ).IsHermitian := OCF.B6.isHermitian_two _ _ _
  have hform : ∀ x : Fin 2 → ℝ, x ⬝ᵥ atom2 ξ ζ δ *ᵥ x =
      (ξ * x 0 + ζ * x 1) ^ 2 + δ * (x ⬝ᵥ x) := fun x => by
    simp [atom2, dotProduct, mulVec, Fin.sum_univ_two]; ring
  have hdot : ∀ x : Fin 2 → ℝ, x ⬝ᵥ x = x 0 ^ 2 + x 1 ^ 2 := fun x => by
    simp [dotProduct, Fin.sum_univ_two]; ring
  have hne1 : (![-ζ, ξ] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have a := congrFun h0 0; have b := congrFun h0 1
    simp at a b; rw [a, b] at h; norm_num at h
  have hne2 : (![ξ, ζ] : Fin 2 → ℝ) ≠ 0 := by
    intro h0
    have a := congrFun h0 0; have b := congrFun h0 1
    simp at a b; rw [a, b] at h; norm_num at h
  constructor
  · refine lmin_eq_of hA (fun y => by rw [hform]; nlinarith [sq_nonneg (ξ * y 0 + ζ * y 1)])
      hne1 ?_
    ext i; fin_cases i <;> simp [atom2, mulVec, dotProduct, Fin.sum_univ_two] <;> ring
  · refine lmax_eq_of hA (fun y => by
      rw [hform, hdot]
      nlinarith [sq_nonneg (-ζ * y 0 + ξ * y 1), sq_nonneg (ξ * y 0 + ζ * y 1)]) hne2 ?_
    ext i; fin_cases i <;> simp [atom2, mulVec, dotProduct, Fin.sum_univ_two] <;>
      first | linear_combination ξ * h | linear_combination ζ * h

lemma sumH_isHermitian (w₁ w₂ ξ ζ δ : ℝ) : (sumH w₁ w₂ ξ ζ δ).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sumH, atom1, atom2]

lemma atom1_eq (δ : ℝ) : atom1 δ = atom2 1 0 δ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [atom1, atom2]

/-- The per-atom record of Prop. B4.5 (wᵢ; η in the own lens = 0; λ_min = δ; λ_max = 1 + δ)
holds for every θ: it does not depend on θ (S5.2). -/
theorem ownLens_record (θ : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    domRatio (conj (rot 1 0) (atom1 δ)) = 0 ∧
    domRatio (conj (rot (Real.cos θ) (Real.sin θ)) (atom2 (Real.cos θ) (Real.sin θ) δ)) = 0 ∧
    lmin (atom1 δ) = δ ∧ lmax (atom1 δ) = 1 + δ ∧
    lmin (atom2 (Real.cos θ) (Real.sin θ) δ) = δ ∧
    lmax (atom2 (Real.cos θ) (Real.sin θ) δ) = 1 + δ := by
  have hh := Real.cos_sq_add_sin_sq θ
  obtain ⟨a1, a2⟩ := atom2_spectrum hh δ
  obtain ⟨b1, b2⟩ := atom2_spectrum (by norm_num : (1 : ℝ) ^ 2 + 0 ^ 2 = 1) δ
  refine ⟨?_, ?_, by rw [atom1_eq]; exact b1, by rw [atom1_eq]; exact b2, a1, a2⟩
  · rw [lemma1_atom1, domRatio_explicit hδ (by linarith)]; simp
  · rw [lemma1_atom2 hh, domRatio_explicit hδ (by linarith)]; simp

open Real in
/-- The three lens matrices at cos θ = 3/5 (sin θ = 4/5, cos²(θ/2) = 4/5, sin²(θ/2) = 1/5,
cos(θ/2)sin(θ/2) = 2/5), any weights (companion of B6's `lenses_at_four_fifths`). -/
lemma lenses_at_three_fifths {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (hc : cos θ = 3 / 5)
    (w₁ w₂ δ : ℝ) :
    let H := sumH w₁ w₂ (cos θ) (sin θ) δ
    conj (rot 1 0) H = !![w₁ + w₂ * (9 / 25) + (w₁ + w₂) * δ, w₂ * (12 / 25);
                           w₂ * (12 / 25), w₂ * (16 / 25) + (w₁ + w₂) * δ] ∧
    conj (rot (cos θ) (sin θ)) H = !![w₂ + w₁ * (9 / 25) + (w₁ + w₂) * δ, -(w₁ * (12 / 25));
                           -(w₁ * (12 / 25)), w₁ * (16 / 25) + (w₁ + w₂) * δ] ∧
    conj (rot (cos (θ / 2)) (sin (θ / 2))) H =
      !![(w₁ + w₂) * (4 / 5) + (w₁ + w₂) * δ, (w₂ - w₁) * (2 / 5);
         (w₂ - w₁) * (2 / 5), (w₁ + w₂) * (1 / 5) + (w₁ + w₂) * δ] := by
  intro H
  obtain ⟨h, hS, hSC, hcθ, hsθ⟩ := halfAngle h0 h1
  have hsin : sin θ = 4 / 5 := by
    have hpos : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
    have := sin_sq_add_cos_sq θ
    rw [hc] at this
    nlinarith
  have hC2 : cos (θ / 2) ^ 2 = 4 / 5 := by linarith
  have hS2 : sin (θ / 2) ^ 2 = 1 / 5 := by linarith
  have hCS : cos (θ / 2) * sin (θ / 2) = 2 / 5 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [H, lemma2_Q1, hc, hsin]; norm_num
  · have hh : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
    simp only [H]; rw [lemma2_Q2 hh, hc, hsin]; norm_num
  · simp only [H]; rw [hcθ, hsθ, lemma2_Qm h, hC2, hS2, hCS]

open Real in
/-- **Theorem B4 (ii)(b), exact instance** (S5.5a, `[adj:S2a]`). w = (1, 3), δ = 1/100,
lenses W₁ = Q(0), W₂ = Q(θ), W_m = Q(θ/2). With one and the same per-atom record
(`ownLens_record`: own-lens η = 0, λ_min = δ, λ_max = 1 + δ, for every θ), the composite
fails the dominance test in all three lenses at cos θ₀ = 4/5 (η = 9/7, 6/5, 15/11) and
passes in all three at cos θ₁ = 3/5 (η = 36/49, 12/17, 20/21); γ(H) = λ_min(H) differs:
51/25 − √73/5 versus 51/25 − 2√13/5. -/
theorem ownLens_two_angle {θ₀ θ₁ : ℝ} (h00 : 0 < θ₀) (h01 : θ₀ < π / 2) (hc0 : cos θ₀ = 4 / 5)
    (h10 : 0 < θ₁) (h11 : θ₁ < π / 2) (hc1 : cos θ₁ = 3 / 5) :
    let H₀ := sumH 1 3 (cos θ₀) (sin θ₀) (1 / 100)
    let H₁ := sumH 1 3 (cos θ₁) (sin θ₁) (1 / 100)
    domRatio (conj (rot 1 0) H₀) = 9 / 7 ∧
    domRatio (conj (rot (cos θ₀) (sin θ₀)) H₀) = 6 / 5 ∧
    domRatio (conj (rot (cos (θ₀ / 2)) (sin (θ₀ / 2))) H₀) = 15 / 11 ∧
    ¬ PassesDominance (conj (rot 1 0) H₀) ∧
    ¬ PassesDominance (conj (rot (cos θ₀) (sin θ₀)) H₀) ∧
    ¬ PassesDominance (conj (rot (cos (θ₀ / 2)) (sin (θ₀ / 2))) H₀) ∧
    domRatio (conj (rot 1 0) H₁) = 36 / 49 ∧
    domRatio (conj (rot (cos θ₁) (sin θ₁)) H₁) = 12 / 17 ∧
    domRatio (conj (rot (cos (θ₁ / 2)) (sin (θ₁ / 2))) H₁) = 20 / 21 ∧
    PassesDominance (conj (rot 1 0) H₁) ∧
    PassesDominance (conj (rot (cos θ₁) (sin θ₁)) H₁) ∧
    PassesDominance (conj (rot (cos (θ₁ / 2)) (sin (θ₁ / 2))) H₁) ∧
    lmin H₀ = 51 / 25 - Real.sqrt 73 / 5 ∧ lmin H₁ = 51 / 25 - 2 * Real.sqrt 13 / 5 ∧
    lmin H₀ ≠ lmin H₁ := by
  intro H₀ H₁
  obtain ⟨r1, r2, r3, n1, n2, n3, -, -, -⟩ := instance_1_3 h00 h01 hc0
  obtain ⟨e1, e2, e3⟩ := lenses_at_three_fifths h10 h11 hc1 1 3 (1 / 100)
  have q1 : domRatio (conj (rot 1 0) H₁) = 36 / 49 := by
    rw [e1, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have q2 : domRatio (conj (rot (cos θ₁) (sin θ₁)) H₁) = 12 / 17 := by
    rw [e2, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_neg]
  have q3 : domRatio (conj (rot (cos (θ₁ / 2)) (sin (θ₁ / 2))) H₁) = 20 / 21 := by
    rw [e3, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have hS0 : H₀.IsHermitian := sumH_isHermitian _ _ _ _ _
  have hS1 : H₁.IsHermitian := sumH_isHermitian _ _ _ _ _
  have l0 : lmin H₀ = 51 / 25 - Real.sqrt 73 / 5 := by
    rw [lmin_eq hS0, lemma5_theta θ₀ one_pos (by norm_num) _ hS0, ellW, hc0]
    rw [show ((1 : ℝ) - 3) ^ 2 / 4 + 1 * 3 * (4 / 5) ^ 2 = (Real.sqrt 73 / 5) ^ 2 by
      rw [div_pow (Real.sqrt 73), Real.sq_sqrt (by norm_num)]; norm_num, Real.sqrt_sq (by positivity)]
    ring
  have l1 : lmin H₁ = 51 / 25 - 2 * Real.sqrt 13 / 5 := by
    rw [lmin_eq hS1, lemma5_theta θ₁ one_pos (by norm_num) _ hS1, ellW, hc1]
    rw [show ((1 : ℝ) - 3) ^ 2 / 4 + 1 * 3 * (3 / 5) ^ 2 = (2 * Real.sqrt 13 / 5) ^ 2 by
      rw [div_pow (2 * Real.sqrt 13), mul_pow, Real.sq_sqrt (by norm_num)]; norm_num, Real.sqrt_sq (by positivity)]
    ring
  refine ⟨r1, r2, r3, n1, n2, n3, q1, q2, q3, ?_, ?_, ?_, l0, l1, ?_⟩
  · rw [e1]; exact passes_explicit (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
  · rw [e2]; exact passes_explicit (by norm_num) (by norm_num) (by norm_num [abs_of_neg])
  · rw [e3]; exact passes_explicit (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
  · rw [l0, l1]
    intro h
    have h' : Real.sqrt 73 = 2 * Real.sqrt 13 := by linarith
    have := congrArg (fun x => x ^ 2) h'
    simp only [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 73),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)] at this
    norm_num at this

/-- A symmetric 2×2 matrix passes the dominance test when |b| is below both diagonal
entries (B6 `passes_iff_signedGershgorin`). -/
lemma passes_two {a b c : ℝ} (ha : |b| < a) (hc : |b| < c) : PassesDominance !![a, b; b, c] := by
  rw [OCF.B6.passes_iff_signedGershgorin]
  intro i
  fin_cases i
  · simp [gershRadius, show (Finset.univ.erase (0 : Fin 2)) = {1} by decide]; exact ha
  · simp [gershRadius, show (Finset.univ.erase (1 : Fin 2)) = {0} by decide]; exact hc

lemma half_angle_aux {C S t : ℝ} (hC : 0 < C) (hSt : S = t * C) (h : C ^ 2 + S ^ 2 = 1)
    (ht0 : 0 < t) (ht1 : t < 1) :
    0 ≤ C ^ 2 - S ^ 2 ∧ C ^ 2 - S ^ 2 ≤ 2 * (1 - t) ∧ 2 * C * S ≤ 1 ∧ 0 ≤ 2 * C * S := by
  have e : C ^ 2 - S ^ 2 = C ^ 2 * (1 - t ^ 2) := by rw [hSt]; ring
  have hC1 : C ^ 2 ≤ 1 := by nlinarith [sq_nonneg S]
  have h1t : 0 ≤ 1 - t ^ 2 := by nlinarith
  refine ⟨by rw [e]; positivity, ?_, by nlinarith [sq_nonneg (C - S)], ?_⟩
  · rw [e]
    have := mul_le_of_le_one_left h1t hC1
    nlinarith
  · rw [hSt]; positivity

lemma off_small {w W τ ξ ζ t : ℝ} (hw : 0 < w) (hwW : w ≤ W) (hτ : 0 < τ) (hξ : 0 ≤ ξ)
    (hξs : ξ ≤ 2 * (1 - t)) (_hζ0 : 0 ≤ ζ) (hζ : ζ ≤ 1) (hτW : 2 * (1 - t) ≤ τ / (2 * W)) :
    w * (ξ * ζ) < τ := by
  have hW : 0 < W := lt_of_lt_of_le hw hwW
  have h1 : ξ * ζ ≤ τ / (2 * W) := (mul_le_of_le_one_right hξ hζ).trans (hξs.trans hτW)
  have h2 : w * (τ / (2 * W)) ≤ τ / 2 := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hw.le]

lemma midpoint_off_small {w₁ w₂ C S t : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hC : 0 < C)
    (hSt : S = t * C) (ht0 : 0 < t) (htr : |w₁ - w₂| / (w₁ + w₂) < t) :
    |(w₂ - w₁) * (C * S)| < (w₁ + w₂) * S ^ 2 := by
  have hW : 0 < w₁ + w₂ := add_pos hw₁ hw₂
  have habs : |w₂ - w₁| < t * (w₁ + w₂) := by
    rw [abs_sub_comm]; rwa [div_lt_iff₀ hW] at htr
  rw [abs_mul, hSt, abs_of_pos (show 0 < C * (t * C) by positivity)]
  have hC2 : 0 < t * C * C := by positivity
  have : |w₂ - w₁| * (C * (t * C)) < t * (w₁ + w₂) * (C * (t * C)) :=
    mul_lt_mul_of_pos_right habs (by positivity)
  nlinarith

open Real in
/-- **Theorem B4 (ii)(b)** (Prop. B4.5(c); S5.5 with the adjudicator-derived S5.5a, here
machine-checked). For every unequal positive weight pair there are δ > 0 and two angles
θ₀, θ₁ ∈ (0, π/2) such that, with this one δ (so with one and the same per-atom record,
`ownLens_record`), the composite H = w₁(uuᵀ + δI) + w₂(vvᵀ + δI) fails the dominance test
in all three lenses W₁ = Q(0), W₂ = Q(θ), W_m = Q(θ/2) at θ₀ and passes in all three at θ₁. -/
theorem ownLens_both_sides {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hne : w₁ ≠ w₂) :
    ∃ δ θ₀ θ₁ : ℝ, 0 < δ ∧ 0 < θ₀ ∧ θ₀ < π / 2 ∧ 0 < θ₁ ∧ θ₁ < π / 2 ∧
      ¬ PassesDominance (conj (rot 1 0) (sumH w₁ w₂ (cos θ₀) (sin θ₀) δ)) ∧
      ¬ PassesDominance (conj (rot (cos θ₀) (sin θ₀)) (sumH w₁ w₂ (cos θ₀) (sin θ₀) δ)) ∧
      ¬ PassesDominance (conj (rot (cos (θ₀ / 2)) (sin (θ₀ / 2)))
          (sumH w₁ w₂ (cos θ₀) (sin θ₀) δ)) ∧
      PassesDominance (conj (rot 1 0) (sumH w₁ w₂ (cos θ₁) (sin θ₁) δ)) ∧
      PassesDominance (conj (rot (cos θ₁) (sin θ₁)) (sumH w₁ w₂ (cos θ₁) (sin θ₁) δ)) ∧
      PassesDominance (conj (rot (cos (θ₁ / 2)) (sin (θ₁ / 2)))
          (sumH w₁ w₂ (cos θ₁) (sin θ₁) δ)) := by
  obtain ⟨θ₀, δ, h00, h01, hδ, -, -, -, n1, n2, n3⟩ := OCF.B6.lemma4_exists hw₁ hw₂ hne
  simp only [cos_zero, sin_zero] at n1
  have hW : 0 < w₁ + w₂ := add_pos hw₁ hw₂
  set τ := (w₁ + w₂) * δ with hτ
  have hτ0 : 0 < τ := mul_pos hW hδ
  set r := |w₁ - w₂| / (w₁ + w₂) with hr
  have hr0 : 0 ≤ r := div_nonneg (abs_nonneg _) hW.le
  have hr1 : r < 1 := by
    rw [hr, div_lt_one hW]
    rcases le_total w₁ w₂ with h | h
    · rw [abs_of_nonpos (by linarith)]; linarith
    · rw [abs_of_nonneg (by linarith)]; linarith
  -- the passing half-angle tangent t ∈ (r, 1), close to 1
  set t := max ((1 + r) / 2) (1 - τ / (4 * (w₁ + w₂))) with ht
  have htr : r < t := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have ht1 : t < 1 := max_lt (by linarith) (by have : 0 < τ / (4 * (w₁ + w₂)) := by positivity
                                               linarith)
  have ht0 : 0 < t := lt_of_le_of_lt hr0 htr
  have htc : 1 - t ≤ τ / (4 * (w₁ + w₂)) := by
    have := le_max_right ((1 + r) / 2) (1 - τ / (4 * (w₁ + w₂))); linarith
  set α := arctan t
  set C := cos α
  set S := sin α
  have hC : 0 < C := cos_arctan_pos t
  have hSt : S = t * C := by
    have := tan_arctan t
    rw [tan_eq_sin_div_cos] at this
    simp only [S, C]; field_simp at this ⊢; linarith
  have h : C ^ 2 + S ^ 2 = 1 := cos_sq_add_sin_sq α
  have hS : 0 < S := by rw [hSt]; positivity
  have hSC : S < C := by rw [hSt]; nlinarith
  have hα0 : 0 < α := arctan_pos.2 ht0
  have hα1 : α < π / 4 := by
    rw [← arctan_one]; exact arctan_strictMono ht1
  have hc2 : cos (2 * α) = C ^ 2 - S ^ 2 := cos_two_mul' α
  have hs2 : sin (2 * α) = 2 * C * S := by rw [sin_two_mul]; ring
  have hhalf : 2 * α / 2 = α := by ring
  have hτW : 2 * (1 - t) ≤ τ / (2 * (w₁ + w₂)) := by
    have : τ / (4 * (w₁ + w₂)) * 2 = τ / (2 * (w₁ + w₂)) := by field_simp; ring
    linarith
  obtain ⟨hξ, hξs, hζ, hζ0⟩ := half_angle_aux hC hSt h ht0 ht1
  have hoff1 := off_small hw₂ (by linarith) hτ0 hξ hξs hζ0 hζ hτW
  have hoff2 := off_small hw₁ (by linarith) hτ0 hξ hξs hζ0 hζ hτW
  refine ⟨δ, θ₀, 2 * α, hδ, h00, by linarith [pi_pos], by linarith, by linarith, n1, n2, n3,
    ?_, ?_, ?_⟩
  · rw [hc2, hs2, lemma2_Q1]
    apply passes_two
    · rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (C ^ 2 - S ^ 2)]
    · rw [abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (2 * C * S)]
  · have hh2 : (C ^ 2 - S ^ 2) ^ 2 + (2 * C * S) ^ 2 = 1 := by
      have : (C ^ 2 - S ^ 2) ^ 2 + (2 * C * S) ^ 2 = (C ^ 2 + S ^ 2) ^ 2 := by ring
      rw [this, h]; norm_num
    rw [hc2, hs2, lemma2_Q2 hh2]
    apply passes_two
    · rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (C ^ 2 - S ^ 2)]
    · rw [abs_neg, abs_of_nonneg (by positivity)]; nlinarith [sq_nonneg (2 * C * S)]
  · rw [hhalf, hc2, hs2, lemma2_Qm h]
    have hoff := midpoint_off_small hw₁ hw₂ hC hSt ht0 htr
    have hSC2 : S ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ hS.le hSC.le 2
    have h3 := mul_le_mul_of_nonneg_left hSC2 hW.le
    have h4 : 0 < (w₁ + w₂) * δ := hτ0
    apply passes_two
    · linarith
    · linarith

end OwnLens

end OCF.B4

#print axioms OCF.B4.lemmaB40_a
#print axioms OCF.B4.lemmaB40_b
#print axioms OCF.B4.lemmaB40_c
#print axioms OCF.B4.lemmaB41_a
#print axioms OCF.B4.lemmaB41_b
#print axioms OCF.B4.thmB4_i1_sigma
#print axioms OCF.B4.thmB4_i1_beta
#print axioms OCF.B4.lmax_eq_betaHat_iff
#print axioms OCF.B4.sigma_quadF
#print axioms OCF.B4.beta_quadF
#print axioms OCF.B4.kernelValid_bot_quadF
#print axioms OCF.B4.opNorm2_eq
#print axioms OCF.B4.propB43_c_lip
#print axioms OCF.B4.propB43_c
#print axioms OCF.B4.propB44
#print axioms OCF.B4.propB44_deltaW
#print axioms OCF.B4.propB44_d2
#print axioms OCF.B4.thmB4_ii_a
#print axioms OCF.B4.ownLens_record
#print axioms OCF.B4.ownLens_two_angle
#print axioms OCF.B4.ownLens_both_sides

/-
B6 (Certificates do not compose: explicit witnesses) — the seven statements
named for formalisation in the adjudication.

Source of truth: project_plan/done/proof_audits/B6_noncompositionality_witnesses/01_derivation.md
(adjudicated 2026-10-09; cleared for stage 3½ under the author's overnight
delegation, 03_adjudication.md "Formalisation tier: FORMALISED expected").
Re-entry of July audits L2 / U5.

DEFINITIONAL MAP:
* η (0.4, signed-diagonal convention, adjudication Decision 1) —
  `domRatio M := ⨆ i, gershRadius M i / M i i`, Rᵢ = `gershRadius`
  = Σ_{j≠i} |M i j|; the test — `PassesDominance M := (∀ i, 0 < M i i) ∧
  domRatio M < 1`. `passes_iff_signedGershgorin` proves the test is exactly
  ∀ i, Rᵢ(M) < M i i (the signed-Gershgorin rule).
* Lenses (0.3): `conj W M := W * M * Wᵀ`; the rotation Q(α) with rows
  (cos α, sin α), (−sin α, cos α) is `rot (cos α) (sin α)`; Q₁ = `rot 1 0`
  (= Q(0)), Q₂ = `rot (cos θ) (sin θ)`, Q_m = `rot (cos (θ/2)) (sin (θ/2))`.
  Integer lenses T₂ = `rot 4 3` = 5·Q₂, T_m = `rot 3 1` = √10·Q_m at
  cos θ = 4/5 (square tight frames, `T2_tight`, `Tm_tight`; η is invariant
  under positive scaling, `domRatio_smul`).
* Atoms (0.2): H₁ = `atom1 δ`, H₂ = `atom2 ξ ζ δ`, H = `sumH w₁ w₂ ξ ζ δ`.
* TRIGONOMETRIC PARAMETRISATION (flagged as instructed): general lemmas are
  stated for (ξ, ζ) with ξ² + ζ² = 1 standing for (cos θ, sin θ), and for
  the half angle (C, S) with C² + S² = 1, 0 < S < C (⟺ θ ∈ (0, π/2)),
  ξ = C² − S², ζ = 2CS; t = S/C = tan(θ/2). Every headline statement is
  ALSO stated in θ-form with the real `Real.cos`, `Real.sin`, `Real.tan`
  (`halfAngle` is the bridge), so no meaning is lost.
* λ_min(H) — `⨅ j, hS.eigenvalues j` (as in T1SharpBound.lean).
* T1 quantities (Lemma 6(c)) — `restrictedGap` (ν), `gramMatrix`,
  `lambdaMax`, `deltaW` from T1GramBound.lean / T1SharpBound.lean, with
  kernel bases `kerBasis` (b₁ = e₂, b₂ = v^⊥).

COVERAGE (adjudication's list, in its order):
 1. Instance (1, 3), cos θ = 4/5, δ = 1/100 — `instance_1_3_int` (integer
    lenses: the three matrices, η = 9/7, 6/5, 15/11, atoms diagonal with
    η = 0, tr H = 102/25, det H = 776/625, H ≻ 0, det(λI − H) = 0 at
    λ = (51 ∓ 5√73)/25) and `instance_1_3` (θ-form).
 2. Instance (1, 11/10) — `instance_1_11_10` (η(H_{Q_m}) = 10/77 passes;
    176/139, 160/127 fail; also (1, 6/5): 30/121, and boundary 41/19: η = 1).
 3. Lemma 2 — `lemma2_Q1`, `lemma2_Q2`, `lemma2_Qm`; Lemma 3 — `lemma3`,
    `lemma3_theta`; Lemma 3′ — `lemma3'` (half-angle t), `lemma3'_theta`
    (exact criterion r < tan(θ/2) + 2δ/sin θ), `lemma3'_ratio` (ρ-interval).
 4. Lemma 4 — `lemma4b` (sufficient conditions, parametrised),
    `lemma4_exists` (θ-form: for every w₁ ≠ w₂, ∃ θ ∈ (0, π/4), δ > 0 with
    all three η > 1 / all three tests failing).
 5. Lemma 6 — `atom2_projector`, `matKer_atom2`, `restrictedGap_atom2`
    (ν = 1), `lemma6_certificate`, `lemma6b`, `lemma6b_theta`
    (λ_min = 1 − cos θ), `lemma6_T1` (s = 1 − ξ, Δ_w = 1 − ξ, chain
    equality at unit weights), `lemma6_T1_display_applies` (the landed
    `composite_gap_display` applies verbatim), `lemma6d` (2/(p²+1)).
 6. Lemma 7 — `lemma7` (any n, any W with WᵀW = cI, c > 0).
 7. Lemma 5 — `lemma5`, `lemma5_theta`, `ellW_zero`, `ellW_one`,
    `ellW_strictMonoOn`, `ellW_range` (open interval), `lemma5_limit`.
 Also Lemma 1 — `lemma1_atom1`, `lemma1_atom2`.

NOT COVERED: Lemma 6(c) for general (unequal) weights (Δ_w = ℓ_w(θ));
Lemma 4(a) for EVERY θ ∈ (0, π/4) with tan(θ/2) < r (one explicit θ is
constructed); Remark 3.3 (principal-axis angle), Remark 6.7
(discontinuity of λ⁺ at θ = 0), Remark 7.3 (redundant frames), the
interpretive remarks.

Status tier: FORMALISED (statement + proof, no sorry).
-/
import Mathlib
import OcfVerification.T1SharpBound

open Matrix BigOperators

namespace OCF.B6

/-! ### 0.4 Dominance ratio (signed-diagonal convention) and the test -/

variable {d : ℕ}

/-- Gershgorin radius Rᵢ(M) = Σ_{j≠i} |M i j|. -/
def gershRadius (M : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) : ℝ :=
  ∑ j ∈ Finset.univ.erase i, |M i j|

/-- η(M) := maxᵢ Rᵢ(M)/M i i (signed diagonal). Meaningful when every
M i i > 0; the test `PassesDominance` requires that. -/
noncomputable def domRatio (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ⨆ i, gershRadius M i / M i i

/-- M passes the dominance test iff every M i i > 0 and η(M) < 1. -/
def PassesDominance (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∀ i, 0 < M i i) ∧ domRatio M < 1

lemma passes_imp_row_lt {M : Matrix (Fin d) (Fin d) ℝ} (h : PassesDominance M) (i : Fin d) :
    gershRadius M i < M i i := by
  have hle : gershRadius M i / M i i ≤ domRatio M :=
    le_ciSup (f := fun i => gershRadius M i / M i i) (Finite.bddAbove_range _) i
  exact (div_lt_one (h.1 i)).mp (hle.trans_lt h.2)

/-- 0.4: the test is exactly the signed-Gershgorin rule:
M passes ⟺ minᵢ (M i i − Rᵢ(M)) > 0, i.e. ∀ i, Rᵢ(M) < M i i. -/
theorem passes_iff_signedGershgorin (M : Matrix (Fin d) (Fin d) ℝ) :
    PassesDominance M ↔ ∀ i, gershRadius M i < M i i := by
  constructor
  · exact fun h i => passes_imp_row_lt h i
  · intro h
    have hpos : ∀ i, 0 < M i i := fun i =>
      lt_of_le_of_lt (Finset.sum_nonneg fun j _ => abs_nonneg _) (h i)
    refine ⟨hpos, ?_⟩
    rcases isEmpty_or_nonempty (Fin d) with hE | hN
    · simp [domRatio]
    · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := fun i => gershRadius M i / M i i)
      rw [domRatio, ← hi]
      exact (div_lt_one (hpos i)).mpr (h i)

/-- For 2×2 matrices, η(M) = max(|M₀₁|/M₀₀, |M₁₀|/M₁₁). -/
lemma domRatio_two (M : Matrix (Fin 2) (Fin 2) ℝ) :
    domRatio M = max (|M 0 1| / M 0 0) (|M 1 0| / M 1 1) := by
  have h0 : gershRadius M 0 = |M 0 1| := by
    simp [gershRadius, show (Finset.univ.erase (0 : Fin 2)) = {1} by decide]
  have h1 : gershRadius M 1 = |M 1 0| := by
    simp [gershRadius, show (Finset.univ.erase (1 : Fin 2)) = {0} by decide]
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    fin_cases i
    · simp [h0]
    · simp [h1]
  · refine max_le ?_ ?_
    · have := le_ciSup (Finite.bddAbove_range (fun i => gershRadius M i / M i i)) 0
      rw [domRatio]; simpa [h0] using this
    · have := le_ciSup (Finite.bddAbove_range (fun i => gershRadius M i / M i i)) 1
      rw [domRatio]; simpa [h1] using this

/-- For a symmetric 2×2 matrix with 0 < M₁₁ ≤ M₀₀: η(M) = |M₀₁|/M₁₁. -/
lemma domRatio_two_of_le {M : Matrix (Fin 2) (Fin 2) ℝ} (hs : M 1 0 = M 0 1)
    (h1 : 0 < M 1 1) (hle : M 1 1 ≤ M 0 0) :
    domRatio M = |M 0 1| / M 1 1 := by
  rw [domRatio_two, hs]
  exact max_eq_right (div_le_div_of_nonneg_left (abs_nonneg _) h1 hle)

/-- (0.1): η(M) ≥ |M₁₀|/M₁₁. -/
lemma domRatio_two_ge (M : Matrix (Fin 2) (Fin 2) ℝ) :
    |M 1 0| / M 1 1 ≤ domRatio M := by
  rw [domRatio_two]; exact le_max_right _ _

/-! ### 0.2–0.3 The atoms, the sum, the lenses

Trigonometric data are parametrised: `ξ, ζ` stand for (cos θ, sin θ),
`C, S` for (cos(θ/2), sin(θ/2)). The θ-forms below substitute the real
`Real.cos`, `Real.sin`. -/

/-- Rotation Q(α) with rows (cos α, sin α), (−sin α, cos α); `c, s` stand
for cos α, sin α. -/
def rot (c s : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![c, s; -s, c]

/-- H₁ = uuᵀ + δI, u = e₁. -/
def atom1 (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 + δ, 0; 0, δ]

/-- H₂ = vvᵀ + δI, v = (ξ, ζ) = (cos θ, sin θ). -/
def atom2 (ξ ζ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![ξ ^ 2 + δ, ξ * ζ; ξ * ζ, ζ ^ 2 + δ]

/-- H = w₁H₁ + w₂H₂. -/
def sumH (w₁ w₂ ξ ζ δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := w₁ • atom1 δ + w₂ • atom2 ξ ζ δ

/-- The conjugate by an analysis operator: M ↦ W M Wᵀ. -/
def conj {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (M : Matrix (Fin d) (Fin d) ℝ) :
    Matrix (Fin n) (Fin n) ℝ := W * M * Wᵀ

lemma rot_orth {c s : ℝ} (h : c ^ 2 + s ^ 2 = 1) : rot c s * (rot c s)ᵀ = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | ring1 | linear_combination h

/-! ### Lemma 1: each atom is diagonal in its own lens -/

theorem lemma1_atom1 (δ : ℝ) : conj (rot 1 0) (atom1 δ) = !![1 + δ, 0; 0, δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conj, rot, atom1, Matrix.mul_apply, Fin.sum_univ_two]

theorem lemma1_atom2 {ξ ζ : ℝ} (h : ξ ^ 2 + ζ ^ 2 = 1) (δ : ℝ) :
    conj (rot ξ ζ) (atom2 ξ ζ δ) = !![1 + δ, 0; 0, δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conj, rot, atom2, Matrix.mul_apply, Fin.sum_univ_two] <;>
    first
    | ring1
    | linear_combination (ξ ^ 2 + ζ ^ 2 + 1 + δ) * h
    | linear_combination δ * h


/-! ### Lemma 2: the sum in the three lenses (τ = (w₁+w₂)δ) -/

theorem lemma2_Q1 (w₁ w₂ ξ ζ δ : ℝ) :
    conj (rot 1 0) (sumH w₁ w₂ ξ ζ δ) =
      !![w₁ + w₂ * ξ ^ 2 + (w₁ + w₂) * δ, w₂ * (ξ * ζ);
         w₂ * (ξ * ζ), w₂ * ζ ^ 2 + (w₁ + w₂) * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conj, rot, sumH, atom1, atom2, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem lemma2_Q2 {ξ ζ : ℝ} (h : ξ ^ 2 + ζ ^ 2 = 1) (w₁ w₂ δ : ℝ) :
    conj (rot ξ ζ) (sumH w₁ w₂ ξ ζ δ) =
      !![w₂ + w₁ * ξ ^ 2 + (w₁ + w₂) * δ, -(w₁ * (ξ * ζ));
         -(w₁ * (ξ * ζ)), w₁ * ζ ^ 2 + (w₁ + w₂) * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conj, rot, sumH, atom1, atom2, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

/-- Lens Q_m = Q(θ/2), parametrised by C = cos(θ/2), S = sin(θ/2), with
cos θ = C² − S², sin θ = 2CS. -/
theorem lemma2_Qm {C S : ℝ} (h : C ^ 2 + S ^ 2 = 1) (w₁ w₂ δ : ℝ) :
    conj (rot C S) (sumH w₁ w₂ (C ^ 2 - S ^ 2) (2 * C * S) δ) =
      !![(w₁ + w₂) * C ^ 2 + (w₁ + w₂) * δ, (w₂ - w₁) * (C * S);
         (w₂ - w₁) * (C * S), (w₁ + w₂) * S ^ 2 + (w₁ + w₂) * δ] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [conj, rot, sumH, atom1, atom2, Matrix.mul_apply, Fin.sum_univ_two] <;> grind

/-! ### Lemma 3: the midpoint diagonalises the sum iff w₁ = w₂ -/

/-- Lemma 3 (parametrised): the off-diagonal entry of H_{Q_m} is
½(w₂ − w₁)·sin θ (sin θ = 2CS); H_{Q_m} is diagonal iff w₁ = w₂; then
η = 0 and the test passes; otherwise η > 0. Range θ ∈ (0, π/2) is
0 < S < C. -/
theorem lemma3 {C S : ℝ} (h : C ^ 2 + S ^ 2 = 1) (hS : 0 < S) (hSC : S < C)
    {w₁ w₂ δ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hδ : 0 ≤ δ) :
    let M := conj (rot C S) (sumH w₁ w₂ (C ^ 2 - S ^ 2) (2 * C * S) δ)
    M 0 1 = (1 / 2) * (w₂ - w₁) * (2 * C * S) ∧
    ((M 0 1 = 0 ∧ M 1 0 = 0) ↔ w₁ = w₂) ∧
    (w₁ = w₂ → domRatio M = 0 ∧ PassesDominance M) ∧
    (w₁ ≠ w₂ → 0 < domRatio M) := by
  intro M
  have hC : 0 < C := hS.trans hSC
  have hM : M = _ := lemma2_Qm h w₁ w₂ δ
  have hCS : 0 < C * S := mul_pos hC hS
  have h11 : 0 < M 1 1 := by rw [hM]; simp; positivity
  have hle : M 1 1 ≤ M 0 0 := by
    rw [hM]; simp; nlinarith [mul_pos (add_pos hw₁ hw₂) (mul_pos (add_pos hC hS) (sub_pos.2 hSC))]
  have hsym : M 1 0 = M 0 1 := by rw [hM]; simp
  have heta : domRatio M = |M 0 1| / M 1 1 := domRatio_two_of_le hsym h11 hle
  refine ⟨by rw [hM]; simp; ring, ?_, ?_, ?_⟩
  · rw [hsym, and_self, hM]; simp
    constructor
    · intro h0; rcases h0 with h0 | h0
      · linarith
      · rcases h0 with h0 | h0
        · exact absurd h0 hC.ne'
        · exact absurd h0 hS.ne'
    · intro h0; left; linarith
  · intro he
    have h0 : M 0 1 = 0 := by rw [hM]; simp [he]
    have heta0 : domRatio M = 0 := by rw [heta, h0]; simp
    refine ⟨heta0, fun i => ?_, by rw [heta0]; norm_num⟩
    fin_cases i
    · exact h11.trans_le hle
    · exact h11
  · intro hne
    rw [heta]
    apply div_pos _ h11
    rw [abs_pos, hM]; simp
    exact ⟨sub_ne_zero.2 (Ne.symm hne), hC.ne', hS.ne'⟩

/-! ### Lemma 3′: exactly when the midpoint lens passes -/

/-- Lemma 3′ (half-angle parametrisation t = S/C = tan(θ/2)):
η(H_{Q_m}) = r / (t + δ(1+t²)/t), r = |w₁ − w₂|/(w₁ + w₂); the test
passes iff r < t*, and η > 1 iff r > t*. -/
theorem lemma3' {C S : ℝ} (h : C ^ 2 + S ^ 2 = 1) (hS : 0 < S) (hSC : S < C)
    {w₁ w₂ δ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hδ : 0 ≤ δ) :
    let M := conj (rot C S) (sumH w₁ w₂ (C ^ 2 - S ^ 2) (2 * C * S) δ)
    let t := S / C
    let r := |w₁ - w₂| / (w₁ + w₂)
    let tstar := t + δ * (1 + t ^ 2) / t
    domRatio M = r / tstar ∧ (PassesDominance M ↔ r < tstar) ∧
      (1 < domRatio M ↔ tstar < r) := by
  intro M t r tstar
  have hC : 0 < C := hS.trans hSC
  have hM : M = _ := lemma2_Qm h w₁ w₂ δ
  have hw : 0 < w₁ + w₂ := add_pos hw₁ hw₂
  have h11 : 0 < M 1 1 := by rw [hM]; simp; positivity
  have hle : M 1 1 ≤ M 0 0 := by
    rw [hM]; simp; nlinarith [mul_pos hw (mul_pos (add_pos hC hS) (sub_pos.2 hSC))]
  have hsym : M 1 0 = M 0 1 := by rw [hM]; simp
  have ht : 0 < t := div_pos hS hC
  have hts : 0 < tstar := by positivity
  have heta : domRatio M = r / tstar := by
    rw [domRatio_two_of_le hsym h11 hle, hM]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    simp only [r, tstar, t]
    rw [abs_mul, abs_of_pos (mul_pos hC hS), abs_sub_comm]
    have hS2 : 0 < S ^ 2 + δ := by positivity
    field_simp
    grind
  refine ⟨heta, ?_, ?_⟩
  · constructor
    · intro hp; rw [← div_lt_one hts, ← heta]; exact hp.2
    · intro hr
      refine ⟨fun i => ?_, by rw [heta, div_lt_one hts]; exact hr⟩
      fin_cases i
      · exact h11.trans_le hle
      · exact h11
  · rw [heta, one_lt_div hts]


/-! ### Bridge to the angle θ -/

open Real in
/-- Half-angle data: for θ ∈ (0, π/2), C = cos(θ/2), S = sin(θ/2) satisfy
C² + S² = 1, 0 < S < C, cos θ = C² − S², sin θ = 2CS. -/
lemma halfAngle {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) :
    cos (θ / 2) ^ 2 + sin (θ / 2) ^ 2 = 1 ∧ 0 < sin (θ / 2) ∧ sin (θ / 2) < cos (θ / 2) ∧
    cos θ = cos (θ / 2) ^ 2 - sin (θ / 2) ^ 2 ∧ sin θ = 2 * cos (θ / 2) * sin (θ / 2) := by
  have hθ : θ = 2 * (θ / 2) := by ring
  have hc : cos θ = cos (θ / 2) ^ 2 - sin (θ / 2) ^ 2 := by
    conv_lhs => rw [hθ]
    exact cos_two_mul' _
  have hs : sin θ = 2 * cos (θ / 2) * sin (θ / 2) := by
    conv_lhs => rw [hθ]
    rw [sin_two_mul]; ring
  have hS : 0 < sin (θ / 2) := sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [pi_pos])
  have hC : 0 < cos (θ / 2) := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], by linarith⟩
  have hcθ : 0 < cos θ := cos_pos_of_mem_Ioo ⟨by linarith [pi_pos], h1⟩
  refine ⟨cos_sq_add_sin_sq _, hS, ?_, hc, hs⟩
  nlinarith

open Real in
lemma lt_pi_div_four_of_sin_lt_cos {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ π / 2)
    (h : sin θ < cos θ) : θ < π / 4 := by
  by_contra hc
  push Not at hc
  have h2 : sin (π / 4) ≤ sin θ :=
    sin_le_sin_of_le_of_le_pi_div_two (by linarith [pi_pos]) h1 hc
  have h3 : cos θ ≤ cos (π / 4) :=
    cos_le_cos_of_nonneg_of_le_pi (by linarith [pi_pos]) (by linarith [pi_pos]) hc
  rw [sin_pi_div_four] at h2
  rw [cos_pi_div_four] at h3
  linarith

open Real in
/-- **Lemma 3, θ-form.** For θ ∈ (0, π/2): the off-diagonal entry of
H_{Q_m} (Q_m = Q(θ/2)) is ½(w₂ − w₁) sin θ; it is diagonal iff w₁ = w₂. -/
theorem lemma3_theta {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2)
    {w₁ w₂ δ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hδ : 0 ≤ δ) :
    let M := conj (rot (cos (θ / 2)) (sin (θ / 2))) (sumH w₁ w₂ (cos θ) (sin θ) δ)
    M 0 1 = (1 / 2) * (w₂ - w₁) * sin θ ∧
    ((M 0 1 = 0 ∧ M 1 0 = 0) ↔ w₁ = w₂) ∧
    (w₁ = w₂ → domRatio M = 0 ∧ PassesDominance M) ∧
    (w₁ ≠ w₂ → 0 < domRatio M) := by
  obtain ⟨h, hS, hSC, hc, hs⟩ := halfAngle h0 h1
  intro M
  have := lemma3 h hS hSC hw₁ hw₂ hδ
  simp only [M, hc, hs]
  exact this

open Real in
/-- **Lemma 3′, θ-form (the exact midpoint pass criterion).** For
θ ∈ (0, π/2), δ ≥ 0, w₁, w₂ > 0, with r = |w₁ − w₂|/(w₁ + w₂) and
t* = tan(θ/2) + 2δ/sin θ: η(H_{Q_m}) = r/t*; H_{Q_m} passes the dominance
test iff r < t*; η(H_{Q_m}) > 1 iff r > t*. -/
theorem lemma3'_theta {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2)
    {w₁ w₂ δ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hδ : 0 ≤ δ) :
    let M := conj (rot (cos (θ / 2)) (sin (θ / 2))) (sumH w₁ w₂ (cos θ) (sin θ) δ)
    let r := |w₁ - w₂| / (w₁ + w₂)
    let tstar := tan (θ / 2) + 2 * δ / sin θ
    domRatio M = r / tstar ∧ (PassesDominance M ↔ r < tstar) ∧
      (1 < domRatio M ↔ tstar < r) := by
  obtain ⟨h, hS, hSC, hc, hs⟩ := halfAngle h0 h1
  intro M r tstar
  have hC : 0 < cos (θ / 2) := hS.trans hSC
  have key := lemma3' h hS hSC hw₁ hw₂ hδ
  have ht : tstar = sin (θ / 2) / cos (θ / 2) +
      δ * (1 + (sin (θ / 2) / cos (θ / 2)) ^ 2) / (sin (θ / 2) / cos (θ / 2)) := by
    simp only [tstar, tan_eq_sin_div_cos, hs]
    field_simp
    grind
  simp only [M, hc, hs] at *
  rw [ht]
  exact key

/-- Lemma 3′, weight-ratio form: with ρ = w₂/w₁ and t* > 0, r < t* holds
for all weights if t* ≥ 1, and iff ρ ∈ ((1−t*)/(1+t*), (1+t*)/(1−t*)) if
t* < 1. -/
theorem lemma3'_ratio {w₁ w₂ ts : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hts : 0 < ts) :
    (1 ≤ ts → |w₁ - w₂| / (w₁ + w₂) < ts) ∧
    (ts < 1 → (|w₁ - w₂| / (w₁ + w₂) < ts ↔
      (1 - ts) / (1 + ts) < w₂ / w₁ ∧ w₂ / w₁ < (1 + ts) / (1 - ts))) := by
  have hw : 0 < w₁ + w₂ := add_pos hw₁ hw₂
  constructor
  · intro h1
    rw [div_lt_iff₀ hw]
    rcases le_total w₁ w₂ with h | h
    · rw [abs_of_nonpos (by linarith)]; nlinarith
    · rw [abs_of_nonneg (by linarith)]; nlinarith
  · intro h1
    have h1' : 0 < 1 - ts := by linarith
    rw [div_lt_iff₀ hw, div_lt_div_iff₀ (by linarith) hw₁, div_lt_div_iff₀ hw₁ h1', abs_lt]
    constructor
    · rintro ⟨ha, hb⟩; constructor <;> nlinarith
    · rintro ⟨ha, hb⟩; constructor <;> nlinarith

/-! ### Lemma 4: unequal weights — all three lenses fail -/

/-- **Lemma 4(b), parametrised** (ξ = C² − S² = cos θ, ζ = 2CS = sin θ;
ζ < ξ is θ < π/4; τ = (w₁+w₂)δ below τ̄): all three ratios exceed 1. -/
theorem lemma4b {C S : ℝ} (h : C ^ 2 + S ^ 2 = 1) (hS : 0 < S) (hSC : S < C)
    (hπ4 : 2 * C * S < C ^ 2 - S ^ 2)
    {w₁ w₂ δ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hδ : 0 < δ)
    (hb1 : (w₁ + w₂) * δ < w₁ * (2 * C * S) * ((C ^ 2 - S ^ 2) - 2 * C * S))
    (hb2 : (w₁ + w₂) * δ < w₂ * (2 * C * S) * ((C ^ 2 - S ^ 2) - 2 * C * S))
    (hb3 : (w₁ + w₂) * δ < S * (|w₂ - w₁| * C - (w₁ + w₂) * S)) :
    let H := sumH w₁ w₂ (C ^ 2 - S ^ 2) (2 * C * S) δ
    1 < domRatio (conj (rot 1 0) H) ∧
    1 < domRatio (conj (rot (C ^ 2 - S ^ 2) (2 * C * S)) H) ∧
    1 < domRatio (conj (rot C S) H) := by
  intro H
  have hC : 0 < C := hS.trans hSC
  have hζ : 0 < 2 * C * S := by positivity
  have hξ : 0 < C ^ 2 - S ^ 2 := hζ.trans hπ4
  have hξζ : 0 < (C ^ 2 - S ^ 2) * (2 * C * S) := mul_pos hξ hζ
  have hh : (C ^ 2 - S ^ 2) ^ 2 + (2 * C * S) ^ 2 = 1 := by
    have : (C ^ 2 - S ^ 2) ^ 2 + (2 * C * S) ^ 2 = (C ^ 2 + S ^ 2) ^ 2 := by ring
    rw [this, h]; norm_num
  have key : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, 0 < M 1 1 → M 1 1 < |M 1 0| →
      1 < domRatio M := fun M hpos hlt =>
    ((one_lt_div hpos).2 hlt).trans_le (domRatio_two_ge M)
  refine ⟨?_, ?_, ?_⟩
  · apply key <;> rw [lemma2_Q1] <;> simp
    · positivity
    · rw [abs_of_pos hw₂, abs_of_pos hξ, abs_of_pos hC, abs_of_pos hS]; nlinarith
  · apply key <;> rw [lemma2_Q2 hh] <;> simp
    · positivity
    · rw [abs_of_pos hw₁, abs_of_pos hξ, abs_of_pos hC, abs_of_pos hS]; nlinarith
  · apply key <;> rw [lemma2_Qm h] <;> simp
    · positivity
    · rw [abs_of_pos hC, abs_of_pos hS]; nlinarith

open Real in
/-- **Lemma 4(a)+(b), θ-form (existence).** For every unequal positive
weight pair there are θ ∈ (0, π/4) and δ > 0 at which the sum fails the
dominance test (η > 1) in all three lenses Q₁ = Q(0), Q₂ = Q(θ),
Q_m = Q(θ/2). -/
theorem lemma4_exists {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (hne : w₁ ≠ w₂) :
    ∃ θ δ : ℝ, 0 < θ ∧ θ < π / 4 ∧ 0 < δ ∧
      let H := sumH w₁ w₂ (cos θ) (sin θ) δ
      1 < domRatio (conj (rot (cos 0) (sin 0)) H) ∧
      1 < domRatio (conj (rot (cos θ) (sin θ)) H) ∧
      1 < domRatio (conj (rot (cos (θ / 2)) (sin (θ / 2))) H) ∧
      ¬ PassesDominance (conj (rot (cos 0) (sin 0)) H) ∧
      ¬ PassesDominance (conj (rot (cos θ) (sin θ)) H) ∧
      ¬ PassesDominance (conj (rot (cos (θ / 2)) (sin (θ / 2))) H) := by
  have hw : 0 < w₁ + w₂ := add_pos hw₁ hw₂
  set r := |w₁ - w₂| / (w₁ + w₂) with hr
  have hr0 : 0 < r := div_pos (abs_pos.2 (sub_ne_zero.2 hne)) hw
  set t := min (r / 2) (1 / 4) with ht
  have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
  have ht1 : t ≤ 1 / 4 := min_le_right _ _
  have ht2 : t ≤ r / 2 := min_le_left _ _
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
    rw [← arctan_one]; exact arctan_strictMono (by linarith)
  set k := C ^ 2
  have hk : 0 < k := by positivity
  have hπ4 : 2 * C * S < C ^ 2 - S ^ 2 := by rw [hSt]; nlinarith
  set B1 := w₁ * (2 * C * S) * ((C ^ 2 - S ^ 2) - 2 * C * S)
  set B2 := w₂ * (2 * C * S) * ((C ^ 2 - S ^ 2) - 2 * C * S)
  set B3 := S * (|w₂ - w₁| * C - (w₁ + w₂) * S)
  have hB1 : 0 < B1 := by
    have : 0 < (C ^ 2 - S ^ 2) - 2 * C * S := by linarith
    positivity
  have hB2 : 0 < B2 := by
    have : 0 < (C ^ 2 - S ^ 2) - 2 * C * S := by linarith
    positivity
  have hB3 : 0 < B3 := by
    have habs : |w₂ - w₁| = r * (w₁ + w₂) := by
      rw [hr, abs_sub_comm]; field_simp
    have : B3 = k * t * ((w₁ + w₂) * (r - t)) := by
      simp only [B3, k]; rw [habs, hSt]; ring
    rw [this]
    have : 0 < r - t := by linarith
    positivity
  set m := min (min B1 B2) B3
  have hm : 0 < m := lt_min (lt_min hB1 hB2) hB3
  set δ := m / (2 * (w₁ + w₂))
  have hδ : 0 < δ := by positivity
  have hτ : (w₁ + w₂) * δ = m / 2 := by simp only [δ]; field_simp
  have hm1 : m ≤ B1 := (min_le_left _ _).trans (min_le_left _ _)
  have hm2 : m ≤ B2 := (min_le_left _ _).trans (min_le_right _ _)
  have hm3 : m ≤ B3 := min_le_right _ _
  have hb := lemma4b h hS hSC hπ4 hw₁ hw₂ hδ (by rw [hτ]; linarith) (by rw [hτ]; linarith)
    (by rw [hτ]; linarith)
  refine ⟨2 * α, δ, by linarith, ?_, hδ, ?_⟩
  · apply lt_pi_div_four_of_sin_lt_cos (by linarith) (by linarith)
    rw [sin_two_mul, cos_two_mul']
    linarith
  · have hhalf : 2 * α / 2 = α := by ring
    have hc2 : cos (2 * α) = C ^ 2 - S ^ 2 := cos_two_mul' α
    have hs2 : sin (2 * α) = 2 * C * S := by rw [sin_two_mul]; ring
    simp only [hhalf, hc2, hs2, cos_zero, sin_zero]
    obtain ⟨h1, h2, h3⟩ := hb
    have np : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, 1 < domRatio M → ¬ PassesDominance M :=
      fun M hM hp => absurd hp.2 (not_lt.2 hM.le)
    exact ⟨h1, h2, h3, np _ h1, np _ h2, np _ h3⟩


/-! ### 2×2 helpers: η of an explicit matrix, positive (semi)definiteness,
spectrum membership, extreme eigenvalues -/

lemma domRatio_explicit {a b c : ℝ} (hc : 0 < c) (hca : c ≤ a) :
    domRatio !![a, b; b, c] = |b| / c :=
  domRatio_two_of_le (M := !![a, b; b, c]) (by simp) (by simpa using hc) (by simpa using hca)

lemma isHermitian_two (a b c : ℝ) : (!![a, b; b, c]).IsHermitian := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma posDef_two {a b c : ℝ} (ha : 0 < a) (hdet : 0 < a * c - b ^ 2) :
    (!![a, b; b, c]).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_two a b c, fun x hx => ?_⟩
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra hcon; push Not at hcon
    exact hx (by ext i; fin_cases i <;> simp [hcon.1, hcon.2])
  have key : a * (x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1))
      = (a * x 0 + b * x 1) ^ 2 + (a * c - b ^ 2) * x 1 ^ 2 := by ring
  have hpos : 0 < a * (x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1)) := by
    rw [key]
    by_cases h1 : x 1 = 0
    · have h0 : x 0 ≠ 0 := by rcases hx' with h | h; exact h; exact absurd h1 h
      have hne : a * x 0 + b * x 1 ≠ 0 := by
        rw [h1]; simp; exact ⟨ha.ne', h0⟩
      have := sq_pos_of_ne_zero hne
      rw [h1] at this ⊢; nlinarith
    · have := sq_pos_of_ne_zero h1; nlinarith [sq_nonneg (a * x 0 + b * x 1)]
  have hQ : 0 < x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1) :=
    pos_of_mul_pos_right hpos ha.le
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  nlinarith [hQ]

lemma posSemidef_two {a b c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hdet : 0 ≤ a * c - b ^ 2) :
    (!![a, b; b, c]).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_two a b c, fun x => ?_⟩
  have hQ : 0 ≤ x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1) := by
    rcases ha.lt_or_eq with ha | ha
    · have key : a * (x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1))
          = (a * x 0 + b * x 1) ^ 2 + (a * c - b ^ 2) * x 1 ^ 2 := by ring
      have : 0 ≤ a * (x 0 * (a * x 0 + b * x 1) + x 1 * (b * x 0 + c * x 1)) := by
        rw [key]; positivity
      exact nonneg_of_mul_nonneg_right (by linarith) ha
    · subst ha
      have hb : b = 0 := by nlinarith [sq_nonneg b]
      subst hb
      nlinarith [sq_nonneg (x 1)]
  simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec]
  nlinarith [hQ]

/-- λ is in the spectrum of A when det(λ·I − A) = 0. -/
lemma mem_spectrum_of_det {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} {μ : ℝ}
    (h : (μ • (1 : Matrix (Fin m) (Fin m) ℝ) - A).det = 0) : μ ∈ spectrum ℝ A := by
  rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one, Matrix.isUnit_iff_isUnit_det, h]
  exact not_isUnit_zero

/-- If A − μ·I is PSD and μ is in the spectrum, then λ_min(A) = μ. -/
lemma iInf_eigenvalues_eq {m : ℕ} [NeZero m] {A : Matrix (Fin m) (Fin m) ℝ}
    (hA : A.IsHermitian) {μ : ℝ}
    (hpsd : (A - μ • (1 : Matrix (Fin m) (Fin m) ℝ)).PosSemidef) (hmem : μ ∈ spectrum ℝ A) :
    (⨅ j, hA.eigenvalues j) = μ := by
  apply le_antisymm
  · rw [hA.spectrum_real_eq_range_eigenvalues] at hmem
    obtain ⟨j, hj⟩ := hmem
    rw [← hj]; exact ciInf_le (Finite.bddBelow_range _) j
  · exact le_ciInf fun j => le_eigenvalues_of_sub_posSemidef hA hpsd j

/-- Mirror of `le_eigenvalues_of_sub_posSemidef`: if μ·I − S is PSD then every
eigenvalue of S is ≤ μ. -/
lemma eigenvalues_le_of_posSemidef_sub {ι : Type*} [Fintype ι] [DecidableEq ι]
    {S : Matrix ι ι ℝ} (hS : S.IsHermitian) {μ : ℝ}
    (hpsd : (μ • (1 : Matrix ι ι ℝ) - S).PosSemidef) (j : ι) : hS.eigenvalues j ≤ μ := by
  have hmem : hS.eigenvalues j ∈ spectrum ℝ S := hS.eigenvalues_mem_spectrum_real j
  have hsub : μ - hS.eigenvalues j
      ∈ spectrum ℝ (algebraMap ℝ (Matrix ι ι ℝ) μ - S) := by
    rw [← spectrum.singleton_sub_eq]
    exact Set.sub_mem_sub rfl hmem
  rw [Algebra.algebraMap_eq_smul_one] at hsub
  have hnn := (Matrix.posSemidef_iff_isHermitian_and_spectrum_nonneg.mp hpsd).2 hsub
  simp only [Set.mem_setOf_eq] at hnn
  linarith

/-! ### Statement 1: the instance (w₁, w₂) = (1, 3), cos θ = 4/5, δ = 1/100 -/

/-- The integer-scaled lenses T₂ = 5·Q₂, T_m = √10·Q_m are square tight
frames (TTᵀ = cI; 0.3: η is invariant under the positive scaling). -/
theorem T2_tight : rot 4 3 * (rot 4 3)ᵀ = (25 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

theorem Tm_tight : rot 3 1 * (rot 3 1)ᵀ = (10 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [rot, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num

/-- η is invariant under positive scaling. -/
lemma domRatio_smul {M : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 < c) :
    domRatio (c • M) = domRatio M := by
  unfold domRatio gershRadius
  congr 1; ext i
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hc, ← Finset.mul_sum]
  rcases eq_or_ne (M i i) 0 with h | h
  · simp [h]
  · field_simp

/-- **Statement 1 (integer lenses).** H = 1·H₁ + 3·H₂ at cos θ = 4/5,
sin θ = 3/5, δ = 1/100. -/
theorem instance_1_3_int :
    let H := sumH 1 3 (4 / 5) (3 / 5) (1 / 100)
    conj (rot 1 0) H = !![74 / 25, 36 / 25; 36 / 25, 28 / 25] ∧
    conj (rot 4 3) H = (25 : ℝ) • !![92 / 25, -12 / 25; -12 / 25, 10 / 25] ∧
    conj (rot 3 1) H = (10 : ℝ) • !![91 / 25, 15 / 25; 15 / 25, 11 / 25] ∧
    domRatio (conj (rot 1 0) H) = 9 / 7 ∧
    domRatio (conj (rot 4 3) H) = 6 / 5 ∧
    domRatio (conj (rot 3 1) H) = 15 / 11 ∧
    conj (rot 1 0) (atom1 (1 / 100)) = !![101 / 100, 0; 0, 1 / 100] ∧
    conj (rot 4 3) (atom2 (4 / 5) (3 / 5) (1 / 100)) =
      (25 : ℝ) • !![101 / 100, 0; 0, 1 / 100] ∧
    domRatio (conj (rot 1 0) (atom1 (1 / 100))) = 0 ∧
    domRatio (conj (rot 4 3) (atom2 (4 / 5) (3 / 5) (1 / 100))) = 0 ∧
    H.trace = 102 / 25 ∧ H.det = 776 / 625 ∧ H.PosDef ∧
    (((51 - 5 * Real.sqrt 73) / 25) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - H).det = 0 ∧
    (((51 + 5 * Real.sqrt 73) / 25) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - H).det = 0 := by
  intro H
  have hH : H = !![74 / 25, 36 / 25; 36 / 25, 28 / 25] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [H, sumH, atom1, atom2] <;> norm_num
  have e1 : conj (rot 1 0) H = !![74 / 25, 36 / 25; 36 / 25, 28 / 25] := by
    rw [hH]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [conj, rot, Matrix.mul_apply, Fin.sum_univ_two]
  have e2 : conj (rot 4 3) H = (25 : ℝ) • !![92 / 25, -12 / 25; -12 / 25, 10 / 25] := by
    rw [hH]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [conj, rot, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have e3 : conj (rot 3 1) H = (10 : ℝ) • !![91 / 25, 15 / 25; 15 / 25, 11 / 25] := by
    rw [hH]; ext i j; fin_cases i <;> fin_cases j <;>
      simp [conj, rot, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have a1 : conj (rot 1 0) (atom1 (1 / 100)) = !![101 / 100, 0; 0, 1 / 100] := by
    rw [lemma1_atom1]; norm_num
  have a2 : conj (rot 4 3) (atom2 (4 / 5) (3 / 5) (1 / 100)) =
      (25 : ℝ) • !![101 / 100, 0; 0, 1 / 100] := by
    ext i j; fin_cases i <;> fin_cases j <;>
      simp [conj, rot, atom2, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have h73 : Real.sqrt 73 ^ 2 = 73 := Real.sq_sqrt (by norm_num)
  refine ⟨e1, e2, e3, ?_, ?_, ?_, a1, a2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [e1, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  · rw [e2, domRatio_smul (by norm_num), domRatio_explicit (by norm_num) (by norm_num)]
    norm_num [abs_of_neg]
  · rw [e3, domRatio_smul (by norm_num), domRatio_explicit (by norm_num) (by norm_num)]
    norm_num [abs_of_pos]
  · rw [a1, domRatio_explicit (by norm_num) (by norm_num)]; simp
  · rw [a2, domRatio_smul (by norm_num), domRatio_explicit (by norm_num) (by norm_num)]; simp
  · rw [hH, Matrix.trace_fin_two]; simp; norm_num
  · rw [hH, Matrix.det_fin_two]; simp; norm_num
  · rw [hH]; exact posDef_two (by norm_num) (by norm_num)
  · rw [hH, Matrix.det_fin_two]; simp; ring_nf; rw [h73]; norm_num
  · rw [hH, Matrix.det_fin_two]; simp; ring_nf; rw [h73]; norm_num


/-! ### Statements 1–2, θ-form: cos θ = 4/5 -/

open Real in
/-- The three lens matrices at cos θ = 4/5 (so sin θ = 3/5,
cos²(θ/2) = 9/10, sin²(θ/2) = 1/10, cos(θ/2)sin(θ/2) = 3/10), any weights. -/
lemma lenses_at_four_fifths {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (hc : cos θ = 4 / 5)
    (w₁ w₂ δ : ℝ) :
    let H := sumH w₁ w₂ (cos θ) (sin θ) δ
    conj (rot 1 0) H = !![w₁ + w₂ * (16 / 25) + (w₁ + w₂) * δ, w₂ * (12 / 25);
                           w₂ * (12 / 25), w₂ * (9 / 25) + (w₁ + w₂) * δ] ∧
    conj (rot (cos θ) (sin θ)) H = !![w₂ + w₁ * (16 / 25) + (w₁ + w₂) * δ, -(w₁ * (12 / 25));
                           -(w₁ * (12 / 25)), w₁ * (9 / 25) + (w₁ + w₂) * δ] ∧
    conj (rot (cos (θ / 2)) (sin (θ / 2))) H =
      !![(w₁ + w₂) * (9 / 10) + (w₁ + w₂) * δ, (w₂ - w₁) * (3 / 10);
         (w₂ - w₁) * (3 / 10), (w₁ + w₂) * (1 / 10) + (w₁ + w₂) * δ] := by
  intro H
  obtain ⟨h, hS, hSC, hcθ, hsθ⟩ := halfAngle h0 h1
  have hsin : sin θ = 3 / 5 := by
    have hpos : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
    have := sin_sq_add_cos_sq θ
    rw [hc] at this
    nlinarith
  have hC2 : cos (θ / 2) ^ 2 = 9 / 10 := by linarith
  have hS2 : sin (θ / 2) ^ 2 = 1 / 10 := by linarith
  have hCS : cos (θ / 2) * sin (θ / 2) = 3 / 10 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · simp only [H, lemma2_Q1, hc, hsin]; norm_num
  · have hh : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
    simp only [H]; rw [lemma2_Q2 hh, hc, hsin]; norm_num
  · simp only [H]; rw [hcθ, hsθ, lemma2_Qm h, hC2, hS2, hCS]

lemma passes_explicit {a b c : ℝ} (hc : 0 < c) (hca : c ≤ a) (h : |b| / c < 1) :
    PassesDominance !![a, b; b, c] := by
  refine ⟨fun i => ?_, by rw [domRatio_explicit hc hca]; exact h⟩
  fin_cases i
  · simpa using hc.trans_le hca
  · simpa using hc

lemma not_passes_of_one_lt {M : Matrix (Fin d) (Fin d) ℝ} (h : 1 < domRatio M) :
    ¬ PassesDominance M := fun hp => absurd hp.2 (not_lt.2 h.le)

open Real in
/-- **Statement 1 (θ-form).** w = (1, 3), cos θ = 4/5, δ = 1/100:
η(H_{Q₁}) = 9/7, η(H_{Q₂}) = 6/5, η(H_{Q_m}) = 15/11 — all three lenses
fail — while each atom is diagonal in its own lens (Lemma 1) and H ≻ 0. -/
theorem instance_1_3 {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (hc : cos θ = 4 / 5) :
    let H := sumH 1 3 (cos θ) (sin θ) (1 / 100)
    domRatio (conj (rot 1 0) H) = 9 / 7 ∧
    domRatio (conj (rot (cos θ) (sin θ)) H) = 6 / 5 ∧
    domRatio (conj (rot (cos (θ / 2)) (sin (θ / 2))) H) = 15 / 11 ∧
    ¬ PassesDominance (conj (rot 1 0) H) ∧
    ¬ PassesDominance (conj (rot (cos θ) (sin θ)) H) ∧
    ¬ PassesDominance (conj (rot (cos (θ / 2)) (sin (θ / 2))) H) ∧
    domRatio (conj (rot 1 0) (atom1 (1 / 100))) = 0 ∧
    domRatio (conj (rot (cos θ) (sin θ)) (atom2 (cos θ) (sin θ) (1 / 100))) = 0 ∧
    H.PosDef := by
  intro H
  obtain ⟨e1, e2, e3⟩ := lenses_at_four_fifths h0 h1 hc 1 3 (1 / 100)
  have hh : cos θ ^ 2 + sin θ ^ 2 = 1 := cos_sq_add_sin_sq θ
  have r1 : domRatio (conj (rot 1 0) H) = 9 / 7 := by
    rw [e1, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have r2 : domRatio (conj (rot (cos θ) (sin θ)) H) = 6 / 5 := by
    rw [e2, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_neg]
  have r3 : domRatio (conj (rot (cos (θ / 2)) (sin (θ / 2))) H) = 15 / 11 := by
    rw [e3, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  refine ⟨r1, r2, r3, not_passes_of_one_lt (by rw [r1]; norm_num),
    not_passes_of_one_lt (by rw [r2]; norm_num), not_passes_of_one_lt (by rw [r3]; norm_num),
    ?_, ?_, ?_⟩
  · rw [lemma1_atom1, domRatio_explicit (by norm_num) (by norm_num)]; simp
  · rw [lemma1_atom2 hh, domRatio_explicit (by norm_num) (by norm_num)]; simp
  · have hsin : sin θ = 3 / 5 := by
      have hpos : 0 < sin θ := sin_pos_of_pos_of_lt_pi h0 (by linarith [pi_pos])
      nlinarith
    have hH : H = !![74 / 25, 36 / 25; 36 / 25, 28 / 25] := by
      ext i j; fin_cases i <;> fin_cases j <;> simp [H, sumH, atom1, atom2, hc, hsin] <;> norm_num
    rw [hH]; exact posDef_two (by norm_num) (by norm_num)

open Real in
/-- **Statement 2 (θ-form; the counterexample to the withdrawn "midpoint
works iff equal weights").** w = (1, 11/10), cos θ = 4/5, δ = 1/100: the
midpoint passes with η = 10/77 while both atoms' own lenses fail
(η = 176/139, 160/127). Also the Lemma 3′ instances: w = (1, 6/5) passes
with η = 30/121; the boundary ratio w = (1, 41/19) gives η = 1 exactly. -/
theorem instance_1_11_10 {θ : ℝ} (h0 : 0 < θ) (h1 : θ < π / 2) (hc : cos θ = 4 / 5) :
    let H := sumH 1 (11 / 10) (cos θ) (sin θ) (1 / 100)
    let Qm := rot (cos (θ / 2)) (sin (θ / 2))
    conj Qm H = !![1911 / 1000, 3 / 100; 3 / 100, 231 / 1000] ∧
    domRatio (conj Qm H) = 10 / 77 ∧ PassesDominance (conj Qm H) ∧
    domRatio (conj (rot 1 0) H) = 176 / 139 ∧
    domRatio (conj (rot (cos θ) (sin θ)) H) = 160 / 127 ∧
    ¬ PassesDominance (conj (rot 1 0) H) ∧
    ¬ PassesDominance (conj (rot (cos θ) (sin θ)) H) ∧
    domRatio (conj Qm (sumH 1 (6 / 5) (cos θ) (sin θ) (1 / 100))) = 30 / 121 ∧
    PassesDominance (conj Qm (sumH 1 (6 / 5) (cos θ) (sin θ) (1 / 100))) ∧
    domRatio (conj Qm (sumH 1 (41 / 19) (cos θ) (sin θ) (1 / 100))) = 1 := by
  intro H Qm
  obtain ⟨e1, e2, e3⟩ := lenses_at_four_fifths h0 h1 hc 1 (11 / 10) (1 / 100)
  obtain ⟨-, -, f3⟩ := lenses_at_four_fifths h0 h1 hc 1 (6 / 5) (1 / 100)
  obtain ⟨-, -, g3⟩ := lenses_at_four_fifths h0 h1 hc 1 (41 / 19) (1 / 100)
  have m3 : conj Qm H = !![1911 / 1000, 3 / 100; 3 / 100, 231 / 1000] := by
    rw [e3]; norm_num
  have r3 : domRatio (conj Qm H) = 10 / 77 := by
    rw [m3, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have r1 : domRatio (conj (rot 1 0) H) = 176 / 139 := by
    rw [e1, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  have r2 : domRatio (conj (rot (cos θ) (sin θ)) H) = 160 / 127 := by
    rw [e2, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_neg]
  have s3 : domRatio (conj Qm (sumH 1 (6 / 5) (cos θ) (sin θ) (1 / 100))) = 30 / 121 := by
    rw [f3, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]
  refine ⟨m3, r3, ?_, r1, r2, not_passes_of_one_lt (by rw [r1]; norm_num),
    not_passes_of_one_lt (by rw [r2]; norm_num), s3, ?_, ?_⟩
  · rw [m3]; exact passes_explicit (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
  · rw [f3]; exact passes_explicit (by norm_num) (by norm_num) (by norm_num [abs_of_pos])
  · rw [g3, domRatio_explicit (by norm_num) (by norm_num)]; norm_num [abs_of_pos]


/-! ### Lemma 7: a singular matrix fails the dominance test in every lens -/

/-- **Lemma 7.** For M ∈ ℝ^{d×d} singular and W ∈ ℝ^{n×d} with WᵀW = cI,
c > 0 (any n), the conjugate WMWᵀ fails the dominance test. (Symmetry of M
is not needed.) Kernel vector y = c⁻¹Wx (Step 7.1) and Mathlib's
strict-diagonal-dominance nonsingularity theorem
`det_ne_zero_of_sum_row_lt_diag` (Gershgorin file; Step 7.2). -/
theorem lemma7 {n : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.det = 0)
    {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    ¬ PassesDominance (conj W M) := by
  intro hp
  -- Step 7.1: WMWᵀ is singular.
  obtain ⟨x, hx0, hMx⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hM
  have hsing : (conj W M).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨c⁻¹ • (W *ᵥ x), ?_, ?_⟩
    · intro hy
      have : Wᵀ *ᵥ (c⁻¹ • (W *ᵥ x)) = x := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hW, Matrix.smul_mulVec,
          Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [hy, Matrix.mulVec_zero] at this
      exact hx0 this.symm
    · have hWt : Wᵀ *ᵥ (c⁻¹ • (W *ᵥ x)) = x := by
        rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hW, Matrix.smul_mulVec,
          Matrix.one_mulVec, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [conj, ← Matrix.mulVec_mulVec, hWt, ← Matrix.mulVec_mulVec, hMx, Matrix.mulVec_zero]
  -- Step 7.2: passing ⇒ strictly diagonally dominant ⇒ nonsingular.
  refine absurd hsing (det_ne_zero_of_sum_row_lt_diag (A := conj W M) ?_)
  intro k
  have hk := passes_imp_row_lt hp k
  rw [Real.norm_eq_abs, abs_of_pos (hp.1 k)]
  simpa [gershRadius, Real.norm_eq_abs] using hk


/-! ### Lemma 6: the two-projector family (δ = 0) and the composite-gap theorem -/

section Lemma6

variable {ξ ζ : ℝ}

lemma atom1_zero_eq : atom1 0 = atom2 1 0 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [atom1, atom2]

lemma mem_matKer_atom2 {y : Fin 2 → ℝ} :
    y ∈ matKer (atom2 ξ ζ 0) ↔ ξ * (ξ * y 0 + ζ * y 1) = 0 ∧ ζ * (ξ * y 0 + ζ * y 1) = 0 := by
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hy
    have h0 := congrFun hy 0
    have h1 := congrFun hy 1
    simp [atom2, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
    exact ⟨by linear_combination h0, by linear_combination h1⟩
  · rintro ⟨h0, h1⟩
    ext i; fin_cases i <;> simp [atom2, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · linear_combination h0
    · linear_combination h1

/-- (C4) H₂ = vvᵀ (δ = 0) is an orthogonal projector. -/
lemma atom2_projector (h : ξ ^ 2 + ζ ^ 2 = 1) :
    atom2 ξ ζ 0 * atom2 ξ ζ 0 = atom2 ξ ζ 0 ∧ (atom2 ξ ζ 0)ᵀ = atom2 ξ ζ 0 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;>
      simp [atom2, Matrix.mul_apply, Fin.sum_univ_two] <;> grind
  · ext i j; fin_cases i <;> fin_cases j <;> simp [atom2]

/-- Lemma 6(a): ker H₂ = span{v^⊥}, v^⊥ = (−ζ, ξ). -/
lemma matKer_atom2 (h : ξ ^ 2 + ζ ^ 2 = 1) :
    matKer (atom2 ξ ζ 0) = Submodule.span ℝ {![-ζ, ξ]} := by
  apply le_antisymm
  · intro y hy
    rw [mem_matKer_atom2] at hy
    have hv : ξ * y 0 + ζ * y 1 = 0 := by
      linear_combination ξ * hy.1 + ζ * hy.2 - (ξ * y 0 + ζ * y 1) * h
    rw [Submodule.mem_span_singleton]
    refine ⟨ξ * y 1 - ζ * y 0, ?_⟩
    ext i; fin_cases i <;> simp
    · linear_combination (-ξ) * hv + y 0 * h
    · linear_combination (-ζ) * hv + y 1 * h
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    show _ ∈ matKer (atom2 ξ ζ 0)
    rw [mem_matKer_atom2]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    constructor <;> ring

/-- Lemma 6(a): the per-term restricted gap of H₂ = vvᵀ is 1 (T1's
`restrictedGap`, the infimum of the quadratic form over unit vectors
orthogonal to the kernel). -/
lemma restrictedGap_atom2 (h : ξ ^ 2 + ζ ^ 2 = 1) : restrictedGap (atom2 ξ ζ 0) = 1 := by
  have himg : (fun x => x ⬝ᵥ atom2 ξ ζ 0 *ᵥ x) ''
      {x | x ⬝ᵥ x = 1 ∧ ∀ y ∈ matKer (atom2 ξ ζ 0), y ⬝ᵥ x = 0} = {1} := by
    apply Set.eq_singleton_iff_unique_mem.mpr
    constructor
    · refine ⟨![ξ, ζ], ⟨?_, fun y hy => ?_⟩, ?_⟩
      · simp [dotProduct, Fin.sum_univ_two]; linear_combination h
      · rw [mem_matKer_atom2] at hy
        simp [dotProduct, Fin.sum_univ_two]
        linear_combination ξ * hy.1 + ζ * hy.2 - (ξ * y 0 + ζ * y 1) * h
      · simp [atom2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]; grind
    · rintro _ ⟨x, ⟨hx1, hx2⟩, rfl⟩
      have hperp := hx2 ![-ζ, ξ] (by rw [matKer_atom2 h]; exact Submodule.mem_span_singleton_self _)
      simp [dotProduct, Fin.sum_univ_two] at hperp hx1
      simp [atom2, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
      have : (ξ * x 0 + ζ * x 1) ^ 2 + (-ζ * x 0 + ξ * x 1) ^ 2
          = (ξ ^ 2 + ζ ^ 2) * (x 0 * x 0 + x 1 * x 1) := by ring
      rw [h, hx1, one_mul] at this
      have h2 : (-ζ * x 0 + ξ * x 1) = 0 := by linarith
      rw [h2] at this
      nlinarith [this]
  rw [restrictedGap, himg, csInf_singleton]


/-- Lemma 6(b), Step 6.3′ certificate (unit weights, δ = 0):
H − (1 − ξ)I = ξ · [[1 + ξ, ζ], [ζ, 1 − ξ]]. -/
lemma lemma6_certificate (h : ξ ^ 2 + ζ ^ 2 = 1) :
    sumH 1 1 ξ ζ 0 - (1 - ξ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) = ξ • !![1 + ξ, ζ; ζ, 1 - ξ] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [sumH, atom1, atom2] <;> grind

lemma lemma6_psd (h : ξ ^ 2 + ζ ^ 2 = 1) (hξ : 0 ≤ ξ) :
    (sumH 1 1 ξ ζ 0 - (1 - ξ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)).PosSemidef := by
  have hξ1 : ξ ≤ 1 := by nlinarith [sq_nonneg ζ]
  rw [lemma6_certificate h]
  exact (posSemidef_two (by linarith) (by linarith) (by nlinarith)).smul hξ

lemma lemma6_mem (h : ξ ^ 2 + ζ ^ 2 = 1) : (1 - ξ) ∈ spectrum ℝ (sumH 1 1 ξ ζ 0) := by
  apply mem_spectrum_of_det
  rw [Matrix.det_fin_two]
  simp [sumH, atom1, atom2]
  grind

/-- **Lemma 6(b)** (unit weights, δ = 0, ξ = cos θ ≥ 0): λ_min(H) = 1 − ξ,
via the PSD certificate (lower bound) and det((1 − ξ)I − H) = 0 (attained). -/
theorem lemma6b (h : ξ ^ 2 + ζ ^ 2 = 1) (hξ : 0 ≤ ξ) (hS : (sumH 1 1 ξ ζ 0).IsHermitian) :
    (⨅ j, hS.eigenvalues j) = 1 - ξ :=
  iInf_eigenvalues_eq hS (lemma6_psd h hξ) (lemma6_mem h)

/-- The kernel bases of Lemma 6(c): b₁ = e₂ (for ker H₁), b₂ = v^⊥ (for ker H₂),
one column each. -/
def kerBasis (ξ ζ : ℝ) : (i : Fin 2) → Fin ((fun _ : Fin 2 => 1) i) → (Fin 2 → ℝ) :=
  fun i _ => if i = 0 then ![0, 1] else ![-ζ, ξ]

/-- The two atoms as T1's family (δ = 0). -/
def atoms0 (ξ ζ : ℝ) : Fin 2 → Matrix (Fin 2) (Fin 2) ℝ := ![atom1 0, atom2 ξ ζ 0]

lemma sum_sigma_two {M : Type*} [AddCommMonoid M] (f : ((_ : Fin 2) × Fin 1) → M) :
    ∑ z, f z = f ⟨0, 0⟩ + f ⟨1, 0⟩ := by
  rw [Fintype.sum_sigma, Fin.sum_univ_two]
  simp

/-- T1's Gram matrix for this family has λ_max = 1 + ξ. -/
lemma lambdaMax_gram (h : ξ ^ 2 + ζ ^ 2 = 1) (hξ : 0 ≤ ξ) :
    lambdaMax (gramMatrix (kerBasis ξ ζ)) = 1 + ξ := by
  set G := gramMatrix (kerBasis ξ ζ)
  have hG : G.IsHermitian := gramMatrix_isHermitian _
  -- quadratic form of G
  have hq : ∀ c, c ⬝ᵥ G *ᵥ c = c ⟨0, 0⟩ ^ 2 + c ⟨1, 0⟩ ^ 2 + 2 * ξ * (c ⟨0, 0⟩ * c ⟨1, 0⟩) := by
    intro c
    rw [dotProduct_gramMatrix_mulVec, sum_sigma_two]
    simp [kerBasis, dotProduct, Fin.sum_univ_two]
    linear_combination (c ⟨1, 0⟩) ^ 2 * h
  apply le_antisymm
  · unfold lambdaMax
    rw [dif_pos hG]
    haveI : Nonempty ((_ : Fin 2) × Fin 1) := ⟨⟨0, 0⟩⟩
    refine ciSup_le fun j => eigenvalues_le_of_posSemidef_sub hG ?_ j
    rw [Matrix.posSemidef_iff_dotProduct_mulVec]
    refine ⟨(Matrix.isHermitian_one.smul (IsSelfAdjoint.all _)).sub hG, fun c => ?_⟩
    rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, Matrix.one_mulVec,
      dotProduct_smul, smul_eq_mul, hq]
    have : c ⬝ᵥ c = c ⟨0, 0⟩ ^ 2 + c ⟨1, 0⟩ ^ 2 := by
      rw [dotProduct, sum_sigma_two]; ring
    rw [this]
    nlinarith [sq_nonneg (c ⟨0, 0⟩ - c ⟨1, 0⟩), mul_nonneg hξ (sq_nonneg (c ⟨0, 0⟩ - c ⟨1, 0⟩))]
  · have := dotProduct_mulVec_le_lambdaMax hG (fun _ => 1)
    rw [hq] at this
    have h2 : (fun _ : (_ : Fin 2) × Fin 1 => (1 : ℝ)) ⬝ᵥ (fun _ => (1 : ℝ)) =
        (2 : ℝ) := by
      rw [dotProduct, sum_sigma_two]; norm_num
    rw [h2] at this
    linarith

/-- **Lemma 6(a), 6(c): relation to the landed composite-gap theorem**
(`thm:composite-gap`(b), formalised in T1SharpBound.lean). Unit weights,
δ = 0, ξ = cos θ ≥ 0, ζ = sin θ: the hypotheses of `composite_gap_display`
hold for this family (orthonormal kernel bases spanning the kernels);
ν₁ = ν₂ = 1, so Σ wᵢνᵢ = 2; s = 2 − λ_max(G) = 1 − ξ; Δ_w = 1 − ξ; and
T1's chain λ_min(H) ≥ Δ_w ≥ (minᵢ aᵢ)·s holds with all three members equal
to 1 − ξ (the equality case). -/
theorem lemma6_T1 (h : ξ ^ 2 + ζ ^ 2 = 1) (hξ : 0 ≤ ξ)
    (hS : (∑ i, (fun _ : Fin 2 => (1 : ℝ)) i • atoms0 ξ ζ i).IsHermitian) :
    let a : Fin 2 → ℝ := fun i => (fun _ : Fin 2 => (1 : ℝ)) i * restrictedGap (atoms0 ξ ζ i)
    (∀ i, (atoms0 ξ ζ i).PosSemidef) ∧ (∀ i, atoms0 ξ ζ i ≠ 0) ∧
    (∀ i, ∀ p q, kerBasis ξ ζ i p ⬝ᵥ kerBasis ξ ζ i q = if p = q then 1 else 0) ∧
    (∀ i, Submodule.span ℝ (Set.range (kerBasis ξ ζ i)) = matKer (atoms0 ξ ζ i)) ∧
    (∀ i, restrictedGap (atoms0 ξ ζ i) = 1) ∧ (∑ i, a i = 2) ∧
    ∑ i, (fun _ : Fin 2 => (1 : ℝ)) i • atoms0 ξ ζ i = sumH 1 1 ξ ζ 0 ∧
    ((2 : ℕ) : ℝ) - lambdaMax (gramMatrix (kerBasis ξ ζ)) = 1 - ξ ∧
    deltaW (kerBasis ξ ζ) a = 1 - ξ ∧
    (⨅ j, hS.eigenvalues j) = deltaW (kerBasis ξ ζ) a ∧
    (⨅ i, a i) * (((2 : ℕ) : ℝ) - lambdaMax (gramMatrix (kerBasis ξ ζ)))
      = deltaW (kerBasis ξ ζ) a := by
  intro a
  have hξ1 : ξ ≤ 1 := by nlinarith [sq_nonneg ζ]
  have hξ1' : -1 ≤ ξ := by nlinarith [sq_nonneg ζ]
  have hgap : ∀ i, restrictedGap (atoms0 ξ ζ i) = 1 := by
    intro i; fin_cases i
    · simp only [atoms0]; simp [atom1_zero_eq, restrictedGap_atom2 (by norm_num : (1:ℝ) ^ 2 + 0 ^ 2 = 1)]
    · simp [atoms0, restrictedGap_atom2 h]
  have ha : a = fun _ => 1 := by funext i; simp [a, hgap i]
  have hsum : ∑ i, (fun _ : Fin 2 => (1 : ℝ)) i • atoms0 ξ ζ i = sumH 1 1 ξ ζ 0 := by
    simp [Fin.sum_univ_two, atoms0, sumH]
  have hlam := lambdaMax_gram h hξ
  have hwg : weightedGram (kerBasis ξ ζ) (fun _ => (1 : ℝ)) = gramMatrix (kerBasis ξ ζ) := by
    simp [weightedGram, blockWeightSqrt]
  have hdelta : deltaW (kerBasis ξ ζ) a = 1 - ξ := by
    rw [ha, deltaW, hwg, hlam]; simp; ring
  have hmin : (⨅ j, hS.eigenvalues j) = 1 - ξ :=
    iInf_eigenvalues_eq hS (by rw [hsum]; exact lemma6_psd h hξ) (by rw [hsum]; exact lemma6_mem h)
  refine ⟨?_, ?_, ?_, ?_, hgap, by rw [ha]; norm_num, hsum, ?_, hdelta,
    by rw [hmin, hdelta], ?_⟩
  · intro i; fin_cases i
    · simp only [atoms0]; rw [atom1_zero_eq]; simp [atom2]
      exact posSemidef_two (by norm_num) (by norm_num) (by norm_num)
    · simp [atoms0, atom2]
      exact posSemidef_two (sq_nonneg _) (sq_nonneg _) (by ring_nf; rfl)
  · intro i; fin_cases i
    · simp only [atoms0]; intro h0
      have := congrFun (congrFun h0 0) 0; simp [atom1] at this
    · simp only [atoms0]; intro h0
      have e0 := congrFun (congrFun h0 0) 0
      have e1 := congrFun (congrFun h0 1) 1
      simp [atom2] at e0 e1
      rw [e0, e1] at h; norm_num at h
  · intro i p q; fin_cases i <;> fin_cases p <;> fin_cases q <;>
      simp [kerBasis, dotProduct, Fin.sum_univ_two]; linear_combination h
  · intro i; fin_cases i
    · change Submodule.span ℝ (Set.range (kerBasis ξ ζ 0)) = matKer (atom1 0)
      have hb : kerBasis ξ ζ 0 = fun _ => ![0, 1] := by funext p; simp [kerBasis]
      rw [atom1_zero_eq, matKer_atom2 (by norm_num), hb, Set.range_const]
      simp
    · change Submodule.span ℝ (Set.range (kerBasis ξ ζ 1)) = matKer (atom2 ξ ζ 0)
      have hb : kerBasis ξ ζ 1 = fun _ => ![-ζ, ξ] := by funext p; simp [kerBasis]
      rw [matKer_atom2 h, hb, Set.range_const]
  · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, hlam]; ring
  · rw [show ((2 : ℕ) : ℝ) = 2 by norm_num, hlam, hdelta, ha]
    simp; ring

/-- **Lemma 6(d)**: rational instances cos θ = (p²−1)/(p²+1),
sin θ = 2p/(p²+1), p ≥ 2: λ_min(H) = s = 2/(p²+1) (p = 3: cos θ = 4/5,
λ_min = 1/5). -/
theorem lemma6d (p : ℕ) (hp : 2 ≤ p)
    (hS : (sumH 1 1 ((p ^ 2 - 1) / (p ^ 2 + 1)) (2 * p / (p ^ 2 + 1)) 0).IsHermitian) :
    ((p : ℝ) ^ 2 - 1) / (p ^ 2 + 1) ∈ Set.Ioo (0 : ℝ) 1 ∧
    (((p : ℝ) ^ 2 - 1) / (p ^ 2 + 1)) ^ 2 + (2 * p / (p ^ 2 + 1)) ^ 2 = 1 ∧
    (⨅ j, hS.eigenvalues j) = 2 / ((p : ℝ) ^ 2 + 1) := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hpos : (0 : ℝ) < (p : ℝ) ^ 2 + 1 := by positivity
  have hpyth : (((p : ℝ) ^ 2 - 1) / (p ^ 2 + 1)) ^ 2 + (2 * p / (p ^ 2 + 1)) ^ 2 = 1 := by
    field_simp; ring
  have hξ0 : 0 < ((p : ℝ) ^ 2 - 1) / (p ^ 2 + 1) := div_pos (by nlinarith) hpos
  refine ⟨⟨hξ0, (div_lt_one hpos).2 (by linarith)⟩, hpyth, ?_⟩
  rw [lemma6b hpyth hξ0.le hS]
  field_simp; ring

open Real in
/-- **Lemma 6(b), θ-form**: for θ ∈ (0, π/2], λ_min(uuᵀ + vvᵀ) = 1 − cos θ. -/
theorem lemma6b_theta {θ : ℝ} (h0 : 0 < θ) (h1 : θ ≤ π / 2)
    (hS : (sumH 1 1 (cos θ) (sin θ) 0).IsHermitian) :
    (⨅ j, hS.eigenvalues j) = 1 - cos θ :=
  lemma6b (cos_sq_add_sin_sq θ) (cos_nonneg_of_mem_Icc ⟨by linarith [pi_pos], h1⟩) hS

/-- The family satisfies the hypotheses of the landed T1(b) display
(`composite_gap_display`, T1SharpBound.lean) verbatim, with n = 2 terms,
unit weights and one kernel-basis column per term. -/
theorem lemma6_T1_display_applies (h : ξ ^ 2 + ζ ^ 2 = 1) (hξ : 0 ≤ ξ)
    (hS : (∑ i, (fun _ : Fin 2 => (1 : ℝ)) i • atoms0 ξ ζ i).IsHermitian) :
    deltaW (kerBasis ξ ζ) (fun i => (fun _ : Fin 2 => (1 : ℝ)) i * restrictedGap (atoms0 ξ ζ i))
        ≤ ⨅ j, hS.eigenvalues j ∧
    (⨅ i, (fun _ : Fin 2 => (1 : ℝ)) i * restrictedGap (atoms0 ξ ζ i)) *
        (((2 : ℕ) : ℝ) - lambdaMax (gramMatrix (kerBasis ξ ζ)))
      ≤ deltaW (kerBasis ξ ζ)
          (fun i => (fun _ : Fin 2 => (1 : ℝ)) i * restrictedGap (atoms0 ξ ζ i)) := by
  obtain ⟨hpsd, hne, hbo, hbs, -⟩ := lemma6_T1 h hξ hS
  exact composite_gap_display (by norm_num) (by norm_num) (atoms0 ξ ζ) (fun _ => 1)
    (fun _ => by norm_num) hpsd hne (kerBasis ξ ζ) hbo hbs hS

end Lemma6

/-! ### Lemma 5: λ_min(H) = τ + ℓ_w(θ) -/

/-- ℓ_w(ξ) := ½(w₁+w₂) − √(¼(w₁−w₂)² + w₁w₂ξ²), ξ = cos θ. -/
noncomputable def ellW (w₁ w₂ ξ : ℝ) : ℝ :=
  (w₁ + w₂) / 2 - Real.sqrt ((w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * ξ ^ 2)

/-- **Lemma 5** (parametrised): λ_min(H) = (w₁+w₂)δ + ℓ_w. -/
theorem lemma5 {ξ ζ : ℝ} (h : ξ ^ 2 + ζ ^ 2 = 1) {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂)
    (δ : ℝ) (hS : (sumH w₁ w₂ ξ ζ δ).IsHermitian) :
    (⨅ j, hS.eigenvalues j) = (w₁ + w₂) * δ + ellW w₁ w₂ ξ := by
  set D := (w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * ξ ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  set R := Real.sqrt D
  have hR : R ^ 2 = D := Real.sq_sqrt hD0
  have hR0 : 0 ≤ R := Real.sqrt_nonneg D
  have hμ : sumH w₁ w₂ ξ ζ δ - ((w₁ + w₂) * δ + ellW w₁ w₂ ξ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)
      = !![w₁ + w₂ * ξ ^ 2 - ellW w₁ w₂ ξ, w₂ * (ξ * ζ);
           w₂ * (ξ * ζ), w₂ * ζ ^ 2 - ellW w₁ w₂ ξ] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [sumH, atom1, atom2] <;> ring
  have hdet : (w₁ + w₂ * ξ ^ 2 - ellW w₁ w₂ ξ) * (w₂ * ζ ^ 2 - ellW w₁ w₂ ξ)
      - (w₂ * (ξ * ζ)) ^ 2 = 0 := by
    simp only [ellW]
    rw [show Real.sqrt ((w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * ξ ^ 2) = R from rfl]
    have hζ2 : ζ ^ 2 = 1 - ξ ^ 2 := by linarith
    rw [hζ2]
    linear_combination hR - w₂ ^ 2 * ξ ^ 2 * h
  have hsum : (w₁ + w₂ * ξ ^ 2 - ellW w₁ w₂ ξ) + (w₂ * ζ ^ 2 - ellW w₁ w₂ ξ) = 2 * R := by
    simp only [ellW]; linear_combination w₂ * h
  apply iInf_eigenvalues_eq hS
  · rw [hμ]
    have hb := sq_nonneg (w₂ * (ξ * ζ))
    apply posSemidef_two _ _ (by linarith)
    · nlinarith
    · nlinarith
  · apply mem_spectrum_of_det
    rw [Matrix.det_fin_two]
    simp [sumH, atom1, atom2]
    linear_combination hdet

open Real in
/-- **Lemma 5, θ-form**: for θ ∈ (0, π/2], λ_min(H) = τ + ℓ_w(θ) with
ℓ_w(θ) = ½(w₁+w₂) − √(¼(w₁−w₂)² + w₁w₂cos²θ). -/
theorem lemma5_theta (θ : ℝ) {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) (δ : ℝ)
    (hS : (sumH w₁ w₂ (cos θ) (sin θ) δ).IsHermitian) :
    (⨅ j, hS.eigenvalues j) = (w₁ + w₂) * δ + ellW w₁ w₂ (cos θ) :=
  lemma5 (cos_sq_add_sin_sq θ) hw₁ hw₂ δ hS

/-- ℓ_w at θ = π/2 (ξ = 0) is min(w₁, w₂); at θ = 0 (ξ = 1) it is 0. -/
lemma ellW_zero (w₁ w₂ : ℝ) : ellW w₁ w₂ 0 = min w₁ w₂ := by
  simp only [ellW]
  rw [show (w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * 0 ^ 2 = (|w₁ - w₂| / 2) ^ 2 by
    rw [div_pow, sq_abs]; ring]
  rw [Real.sqrt_sq (by positivity)]
  rcases le_total w₁ w₂ with hle | hle
  · rw [min_eq_left hle, abs_of_nonpos (by linarith)]; ring
  · rw [min_eq_right hle, abs_of_nonneg (by linarith)]; ring

lemma ellW_one {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) : ellW w₁ w₂ 1 = 0 := by
  simp only [ellW]
  rw [show (w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * 1 ^ 2 = ((w₁ + w₂) / 2) ^ 2 by ring]
  rw [Real.sqrt_sq (by positivity)]; ring

open Real in
/-- Lemma 5: ℓ_w(θ) is strictly increasing on [0, π/2]. -/
lemma ellW_strictMonoOn {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    StrictMonoOn (fun θ => ellW w₁ w₂ (cos θ)) (Set.Icc 0 (π / 2)) := by
  intro x hx y hy hxy
  have hc : cos y < cos x := cos_lt_cos_of_nonneg_of_le_pi hx.1 (by linarith [hy.2, pi_pos]) hxy
  have hcy : 0 ≤ cos y := cos_nonneg_of_mem_Icc ⟨by linarith [hy.1, pi_pos], hy.2⟩
  have hsq : cos y ^ 2 < cos x ^ 2 := by nlinarith
  simp only [ellW]
  have : Real.sqrt ((w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * cos y ^ 2)
      < Real.sqrt ((w₁ - w₂) ^ 2 / 4 + w₁ * w₂ * cos x ^ 2) :=
    Real.sqrt_lt_sqrt (by positivity) (by nlinarith [mul_pos hw₁ hw₂])
  linarith

open Real in
/-- **Lemma 5 / headline (i), range.** With δ fixed, as θ ranges over the
open interval (0, π/2), λ_min(H) − (w₁+w₂)δ = ℓ_w(θ) ranges over exactly the
open interval (0, min(w₁, w₂)); the right endpoint is attained at θ = π/2. -/
theorem ellW_range {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    (fun θ => ellW w₁ w₂ (cos θ)) '' Set.Ioo 0 (π / 2) = Set.Ioo 0 (min w₁ w₂) := by
  have hmono := ellW_strictMonoOn hw₁ hw₂
  have h0 : ellW w₁ w₂ (cos 0) = 0 := by rw [cos_zero]; exact ellW_one hw₁ hw₂
  have h1 : ellW w₁ w₂ (cos (π / 2)) = min w₁ w₂ := by rw [cos_pi_div_two]; exact ellW_zero w₁ w₂
  have hpi : (0 : ℝ) ≤ π / 2 := by linarith [pi_pos]
  apply le_antisymm
  · rintro _ ⟨θ, hθ, rfl⟩
    have hθI : θ ∈ Set.Icc 0 (π / 2) := ⟨hθ.1.le, hθ.2.le⟩
    constructor
    · rw [← h0]; exact hmono ⟨le_refl 0, hpi⟩ hθI hθ.1
    · rw [← h1]; exact hmono hθI ⟨hpi, le_refl _⟩ hθ.2
  · have hcont : ContinuousOn (fun θ => ellW w₁ w₂ (cos θ)) (Set.Icc 0 (π / 2)) := by
      unfold ellW; fun_prop
    have := intermediate_value_Ioo hpi hcont
    rw [h0, h1] at this
    exact this

open Real in
/-- **Lemma 5, limit**: λ_min(H) → 0 as (θ, δ) → (0, 0). -/
theorem lemma5_limit {w₁ w₂ : ℝ} (hw₁ : 0 < w₁) (hw₂ : 0 < w₂) :
    Filter.Tendsto (fun p : ℝ × ℝ => (w₁ + w₂) * p.2 + ellW w₁ w₂ (cos p.1))
      (nhds (0, 0)) (nhds 0) := by
  have hc : Continuous (fun p : ℝ × ℝ => (w₁ + w₂) * p.2 + ellW w₁ w₂ (cos p.1)) := by
    unfold ellW; fun_prop
  have := hc.tendsto (0, 0)
  simpa [ellW_one hw₁ hw₂] using this

end OCF.B6

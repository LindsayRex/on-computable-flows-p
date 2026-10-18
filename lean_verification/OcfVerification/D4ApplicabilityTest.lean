/-
D4 (+A7) (The a priori applicability test) — Lemma 3.3 (outcome meanings), Proposition 4.1
(vacuity), Remark 4.2 (tight frames), Lemma 6.1 (trace criterion), and the exact
counterexamples M1–M6 of Remark 6.7, as recommended for stage 3½ by DECISION 4 of the
stage-3 adjudication.

Source of truth: project_plan/done/proof_audits/D4_applicability_test/01_derivation.md (stage-1 dossier
revised at stage 3 and its re-audit; sha16 8cb6f3db21a188fd at the start and at the end of
formalisation; file not edited), 03_adjudication.md (DECISION 4, re-audit addendum: M6,
Remark 4.2 for all tight frames), and the stage-4 draft 04_landing_draft_a.tex
(Definition def:d4-test, Lemma lem:d4-outcomes, Proposition prop:d4-vacuity, Remark
rem:d4-frames). Theorem 6.3, Corollary 6.4, Proposition 6.5 (Gaussian concentration) and the
GOE null are PROSE-ONLY by ruling and are not attempted here.

DEFINITIONAL MAP:
* 𝕊ᵈ — `Matrix (Fin d) (Fin d) ℝ` with `IsHermitian` (over ℝ: Hᵀ = H); H ≻ 0 —
  `Matrix.PosDef`.
* rᵢ(M), η(M), "M passes" — B6's `gershRadius`, `domRatio`, `PassesDominance` (reused, not
  redefined; B6 `passes_iff_signedGershgorin` is the signed-Gershgorin form). λ_min —
  PSpectralGlue's `lamMin`. Lens matrix W H Wᵀ — B6's `conj W H`. Frame facts — A56's
  `frame_injective`, `frame_d_le_n`, `A56_6d_scale`, `A56_6d_frame`, `A56_6f`.
* Square tight frame — `W : Matrix (Fin d) (Fin d) ℝ`, `Wᵀ * W = c • 1`, `0 < c`; tight frame
  (Remark 4.2) — the same with `W : Matrix (Fin n) (Fin d) ℝ`.
* Declared family F = (W₁,…,W_m), m ≥ 1 (Definition 3.1) — `LensFamily d m` (fields `W`, `c`,
  `hm : 0 < m`, `hc`, `hW`). "Fixed before H is examined" is a protocol condition with no
  mathematical content in the deterministic statements; it is not encoded. Accordingly the
  H-dependent tuple of Proposition 4.1(a) is also a `LensFamily` (`single`), exactly as the
  dossier applies "the procedure of Definition 3.2" to it.
* Definition 3.2 — M_j: `F.lensMat H j`; "η_j(H) defined": `F.Defined H j` (∀ i, 0 < (M_j)ᵢᵢ);
  η_j(H): `F.eta H j` (= η(M_j), used only where defined); T_F(H) := min over defined η_j with
  min ∅ = +∞: `F.T H : WithTop ℝ`; outcome: `F.outcome ηbar H : Outcome m` with constructors
  `accept j*` (j* the least index attaining T_F(H)), `reject`, `undetermined`. The
  characterisations `outcome_eq_accept_iff`, `exists_accept_iff`, `outcome_eq_reject_iff`,
  `outcome_eq_undetermined_iff` restate Definition 3.2 verbatim (S10: the inductive type makes
  the outcomes mutually exclusive and exhaustive). η̄ ∈ (0, 1] is a hypothesis where used
  (only η̄ ≤ 1 is ever needed, and η̄ > 0 in Proposition 4.1(a)).
* Q_j := c_j^{-1/2} W_j — `(Real.sqrt (F.c j))⁻¹ • F.W j`; orthogonal — QᵀQ = QQᵀ = I.
* minᵢ — `⨅ i`; Σ_{i≠k}|M_ik| — `offDiagMass M`; tr — `Matrix.trace`.
* Remark 6.7 statistics: η_avg — `etaAvg` (Σ_{i≠k}|M_ik| / tr M); η_frob — `etaFrob`
  (‖M − diag M‖_F/‖diag M‖_F); η_mean — `etaMean` ((1/d)Σᵢ rᵢ/|Mᵢᵢ|), as in STATE.md and
  adjudication_scripts/j_d4_adjudication_checks.py. I + b(J − I) — `IbJ d b`. M5 and M6 are
  the block sums written out entry by entry.

THEOREMS:
* Lemma 3.3(a): `LensFamily.lemma33a_orthogonal` (Q_j orthogonal, M_j = c_j Q_jHQ_jᵀ, same
  definedness, same η), `LensFamily.lemma33a_scale` (bH, b > 0: same definedness, η_j, T_F,
  outcome).
* Lemma 3.3(b): `LensFamily.lemma33b` (accept with witness j*, η̄ ≤ 1 ⇒ M_{j*} passes, H ≻ 0,
  0 < c_{j*}⁻¹(1 − η_{j*})minᵢ(M_{j*})ᵢᵢ ≤ λ_min(H)).
* Lemma 3.3(c): `LensFamily.lemma33c` (η̄ ≤ 1: undetermined ⟺ some η_j undefined; then
  H not ≻ 0 and every square tight frame fails); pieces `LensFamily.not_posDef_of_not_defined`
  (S18), `LensFamily.fails_every_sq_frame` (S19).
* Lemma 3.3(d): `LensFamily.lemma33d` (reject ⇒ all defined, no η_j < η̄),
  `lemma33d_examples` (S21: [[1,1],[1,2]] rejected and ≻ 0; [[1,2],[2,1]] rejected,
  det −3, indefinite).
* Proposition 4.1: `prop41a` (eigenbasis lens: orthogonal, positive diagonal, η = 0, the
  one-lens procedure accepts at every η̄ ∈ (0,1]), `prop41b`, `prop41c`.
* Remark 4.2: `rem42_tight_frames` (not ≻ 0 ⇒ every tight frame, any n, fails),
  `rem42_redundant` (d ≤ n for every tight frame; n > d ⇒ never passes, any H),
  `rem42_nonframe` (diag(1,−1), W = e₁ᵀ: not a frame, passes with η = 0),
  `rem42_trace` and `rem42_trace_outcome` (tr H ≤ 0 ⇒ a non-positive lens diagonal entry in
  every tight frame; every η_j undefined; outcome undetermined for every family).
* Lemma 6.1: `lemma61a` (d ≥ 1), `lemma61b`, `lemma61b_threshold` (d ≥ 1);
  `offDiagMass_eq_sum_gershRadius` (S30); `etaAvg_le_domRatio`.
* Counterexamples: `M1_facts` (η_avg = 9/5, η_frob = 3/5, η = 9/5), `M2_facts` (η_frob² =
  18/25, η_frob = √18/5 < 1, charpoly (X − 8/5)²(X + 1/5), not ≻ 0, η = 6/5), `M3_facts`
  (η_mean = 3/5 < η_avg = 60/67), `M4_facts` (positive diagonal, η_avg = 100/101 < 1,
  det = −6/25, indefinite, η = 50), `M5_facts` (η_mean = 3/4, indefinite), `M6_facts`
  (η_mean = 11/15 < 1 ≤ η_avg = 22/21, indefinite).

HYPOTHESES (relative to the dossier): the dossier's standing convention is d ≥ 2. Lemma 3.3(b)
and Remark 4.2's trace clause carry d ≥ 1; Lemma 6.1(a) and the threshold form of 6.1(b)
carry d ≥ 1 because they are false at d = 0 (an `example` in the file shows the empty matrix
passes while 0 ≥ 0). Lemma 3.3(a), 3.3(d), Lemma 6.1 do not use symmetry of H or M; Remark 4.2
for non-square tight frames is proved by the same quadratic-form argument as the square case
(passing ⇒ W H Wᵀ ≻ 0 ⇒ H ≻ 0, via WᵀW = cI), with the rank argument (A56_6f) giving the
stronger "redundant frames never pass". No hypothesis was strengthened beyond d ≥ 1.

Status tier: FORMALISED (statement + proof, no sorry) for every theorem listed above.
Theorem 6.3, Corollary 6.4, Proposition 6.5 and Remarks 6.7(a)–(b), 6.8–6.10: PROSE-ONLY.
-/
import Mathlib
import OcfVerification.B6Witnesses
import OcfVerification.PSpectralGlue
import OcfVerification.A56FrameBookkeeping

open Matrix BigOperators

noncomputable section

open scoped Classical

namespace OCF.D4

open OCF.B6 (gershRadius domRatio PassesDominance passes_iff_signedGershgorin
  passes_imp_row_lt conj domRatio_two)
open OCF.P (lamMin lamMin_mem lamMin_le_eigenvalues posDef_of_passesDominance)
open OCF.A56 (A56_6d_scale A56_6d_frame A56_6f frame_injective frame_d_le_n conjOp pushDown)

variable {d : ℕ}

/-! ### Generic linear-algebra glue -/

/-- Gershgorin on the real line, eigenvector form: if `A v = μ v`, `v ≠ 0`,
then `μ ≥ A i i − rᵢ(A)` for some `i`. -/
lemma exists_le_of_eigvec {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {v : Fin n → ℝ} {μ : ℝ}
    (hv : v ≠ 0) (h : A *ᵥ v = μ • v) : ∃ i, A i i - gershRadius A i ≤ μ := by
  have hμ' : Module.End.HasEigenvalue (Matrix.toLin' A) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector (x := v)
      ⟨by rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]; exact h, hv⟩
  obtain ⟨i, hi⟩ := eigenvalue_mem_ball hμ'
  refine ⟨i, ?_⟩
  rw [Metric.mem_closedBall, Real.dist_eq] at hi
  have : gershRadius A i = ∑ j ∈ Finset.univ.erase i, ‖A i j‖ := by
    simp [gershRadius, Real.norm_eq_abs]
  rw [this]
  linarith [neg_abs_le (μ - A i i)]

/-- For a square tight frame (`Wᵀ W = c I`, `c > 0`), also `W Wᵀ = c I`. -/
lemma sq_frame_mul_transpose {W : Matrix (Fin d) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    W * Wᵀ = c • (1 : Matrix (Fin d) (Fin d) ℝ) := by
  have h1 : (c⁻¹ • Wᵀ) * W = 1 := by
    rw [Matrix.smul_mul, hW, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  have h2 : W * (c⁻¹ • Wᵀ) = 1 := mul_eq_one_comm.mp h1
  rw [Matrix.mul_smul] at h2
  calc W * Wᵀ = c • (c⁻¹ • (W * Wᵀ)) := by
        rw [smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
    _ = c • 1 := by rw [h2]

/-- The lens matrix of a symmetric matrix is symmetric. -/
lemma conj_isHermitian {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) : (conj W H).IsHermitian := by
  have hH' : Hᵀ = H := by
    have := hH.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  unfold conj
  show (W * H * Wᵀ)ᴴ = W * H * Wᵀ
  rw [conjTranspose_eq_transpose_of_trivial]
  simp [Matrix.transpose_mul, hH', Matrix.mul_assoc]

/-- Lens of a scaled matrix: `W (bH) Wᵀ = b · W H Wᵀ`. -/
lemma conj_smul {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (b : ℝ) :
    conj W (b • H) = b • conj W H := by
  unfold conj; rw [Matrix.mul_smul, Matrix.smul_mul]

/-- Diagonal entries of the lens matrix: `(W H Wᵀ)ᵢᵢ = wᵢᵀ H wᵢ`. -/
lemma conj_diag {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (i : Fin n) :
    conj W H i i = W i ⬝ᵥ (H *ᵥ W i) :=
  (A56_6d_frame (c := 1) one_pos H).2.1 i

/-- **S19 / S25 core (any tight frame, square or not).** If `Wᵀ W = c I`,
`c > 0`, `H` symmetric and `W H Wᵀ` passes the dominance test, then `H ≻ 0`. -/
theorem posDef_of_conj_passes {n : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) {H : Matrix (Fin d) (Fin d) ℝ}
    (hH : H.IsHermitian) (hp : PassesDominance (conj W H)) : H.PosDef := by
  have hM : (conj W H).PosDef := posDef_of_passesDominance (conj_isHermitian W hH) hp
  have hinj : Function.Injective W.mulVec := frame_injective hc hW
  have h2 := hM.conjTranspose_mul_mul_same hinj
  rw [conjTranspose_eq_transpose_of_trivial] at h2
  have heq : Wᵀ * conj W H * W = (c * c) • H := by
    unfold conj
    calc Wᵀ * (W * H * Wᵀ) * W = (Wᵀ * W) * H * (Wᵀ * W) := by
          simp only [Matrix.mul_assoc]
      _ = (c * c) • H := by
          rw [hW, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_smul,
            Matrix.mul_one, smul_smul]
  rw [heq] at h2
  have hcc : 0 < (c * c)⁻¹ := inv_pos.mpr (mul_pos hc hc)
  have := h2.smul hcc
  rwa [smul_smul, inv_mul_cancel₀ (mul_pos hc hc).ne', one_smul] at this

/-- Eigen-transfer: if `H v = λ v` and `Wᵀ W = c I`, then
`(W H Wᵀ)(W v) = (cλ)(W v)`. -/
lemma conj_mulVec_eig {n : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ}
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) {H : Matrix (Fin d) (Fin d) ℝ}
    {v : Fin d → ℝ} {μ : ℝ} (hv : H *ᵥ v = μ • v) :
    conj W H *ᵥ (W *ᵥ v) = (c * μ) • (W *ᵥ v) := by
  unfold conj
  rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hW, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul, hv]
  simp only [Matrix.mulVec_smul, smul_smul]

/-- The eigenvector of a symmetric real matrix, as a plain function, is nonzero. -/
lemma eigvec_ne_zero {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (j : Fin d) :
    (⇑(hA.eigenvectorBasis j) : Fin d → ℝ) ≠ 0 := by
  intro h
  have h1 : ‖hA.eigenvectorBasis j‖ = 1 := hA.eigenvectorBasis.orthonormal.1 j
  have h0 : hA.eigenvectorBasis j = 0 := by
    ext i; simpa using congrFun h i
  rw [h0, norm_zero] at h1; exact zero_ne_one h1


/-! ### Definition 3.1: declared family of square tight frames -/

/-- A (declared) family F = (W₁,…,W_m), m ≥ 1, of square tight frames:
`W j ∈ ℝ^{d×d}`, `(W j)ᵀ (W j) = c j · I`, `c j > 0`. "Fixed before H is
examined" is a protocol condition, not a mathematical one; it is recorded in
the header and is not (and cannot be) part of this structure. -/
structure LensFamily (d m : ℕ) where
  W : Fin m → Matrix (Fin d) (Fin d) ℝ
  c : Fin m → ℝ
  hm : 0 < m
  hc : ∀ j, 0 < c j
  hW : ∀ j, (W j)ᵀ * W j = c j • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- The three outcomes of Definition 3.2 (accept carries the witness j*). -/
inductive Outcome (m : ℕ) where
  | accept (j : Fin m)
  | reject
  | undetermined
  deriving DecidableEq

namespace LensFamily

variable {m : ℕ} (F : LensFamily d m)

/-! ### Definition 3.2: the applicability test -/

/-- M_j := W_j H W_jᵀ. -/
def lensMat (H : Matrix (Fin d) (Fin d) ℝ) (j : Fin m) : Matrix (Fin d) (Fin d) ℝ :=
  conj (F.W j) H

/-- η_j(H) is *defined* iff (M_j)ᵢᵢ > 0 for every i. -/
def Defined (H : Matrix (Fin d) (Fin d) ℝ) (j : Fin m) : Prop :=
  ∀ i, 0 < F.lensMat H j i i

/-- The value η(M_j) (the B6 signed dominance ratio); it is η_j(H) when
`F.Defined H j`. -/
def eta (H : Matrix (Fin d) (Fin d) ℝ) (j : Fin m) : ℝ :=
  domRatio (F.lensMat H j)

/-- T_F(H) := min{η_j(H) : η_j(H) defined}, min ∅ := +∞ (in `WithTop ℝ`). -/
def T (H : Matrix (Fin d) (Fin d) ℝ) : WithTop ℝ :=
  (Finset.univ.filter (F.Defined H)).inf (fun j => ((F.eta H j : ℝ) : WithTop ℝ))

/-- Indices attaining T_F(H) among the defined ones. -/
def attainSet (H : Matrix (Fin d) (Fin d) ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun j => F.Defined H j ∧ ((F.eta H j : ℝ) : WithTop ℝ) = F.T H)

/-- The outcome: accept (witness = least index attaining T_F(H)) if
T_F(H) < η̄; reject if T_F(H) ≥ η̄ and every η_j is defined; undetermined if
T_F(H) ≥ η̄ and some η_j is undefined. (The `Nonempty` conjunct is automatic
when T_F(H) < η̄, see `attainSet_nonempty`; `outcome_eq_accept_iff` states
the clean form.) -/
def outcome (ηbar : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) : Outcome m :=
  if h : F.T H < ((ηbar : ℝ) : WithTop ℝ) ∧ (F.attainSet H).Nonempty then
    Outcome.accept ((F.attainSet H).min' h.2)
  else if ∀ j, F.Defined H j then Outcome.reject else Outcome.undetermined

lemma T_le {H : Matrix (Fin d) (Fin d) ℝ} {j : Fin m} (hj : F.Defined H j) :
    F.T H ≤ ((F.eta H j : ℝ) : WithTop ℝ) :=
  Finset.inf_le (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

lemma le_T {H : Matrix (Fin d) (Fin d) ℝ} {x : WithTop ℝ}
    (h : ∀ j, F.Defined H j → x ≤ ((F.eta H j : ℝ) : WithTop ℝ)) : x ≤ F.T H :=
  Finset.le_inf fun j hj => h j (Finset.mem_filter.mp hj).2

lemma attainSet_nonempty {H : Matrix (Fin d) (Fin d) ℝ} (hT : F.T H ≠ ⊤) :
    (F.attainSet H).Nonempty := by
  have hS : (Finset.univ.filter (F.Defined H)).Nonempty := by
    by_contra hE
    rw [Finset.not_nonempty_iff_eq_empty] at hE
    exact hT (by rw [T, hE, Finset.inf_empty])
  obtain ⟨j, hj, hjT⟩ := Finset.exists_mem_eq_inf _ hS (fun j => ((F.eta H j : ℝ) : WithTop ℝ))
  exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2, hjT.symm⟩⟩

/-- **S10, accept.** The outcome is `accept j` iff T_F(H) < η̄ and j is the
least index with η_j(H) defined and equal to T_F(H). -/
theorem outcome_eq_accept_iff (ηbar : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) (j : Fin m) :
    F.outcome ηbar H = Outcome.accept j ↔
      F.T H < ((ηbar : ℝ) : WithTop ℝ) ∧ F.Defined H j ∧
        ((F.eta H j : ℝ) : WithTop ℝ) = F.T H ∧
        ∀ k, F.Defined H k → ((F.eta H k : ℝ) : WithTop ℝ) = F.T H → j ≤ k := by
  unfold outcome
  split_ifs with h h'
  · simp only [Outcome.accept.injEq]
    constructor
    · rintro rfl
      have hmem := Finset.min'_mem _ h.2
      refine ⟨h.1, (Finset.mem_filter.mp hmem).2.1, (Finset.mem_filter.mp hmem).2.2, ?_⟩
      intro k hk hkT
      exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk, hkT⟩)
    · rintro ⟨_, hj, hjT, hmin⟩
      apply le_antisymm
      · exact Finset.min'_le _ _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hjT⟩)
      · have hmem := Finset.min'_mem _ h.2
        exact hmin _ (Finset.mem_filter.mp hmem).2.1 (Finset.mem_filter.mp hmem).2.2
  · simp only [false_iff]
    rintro ⟨hT, hj, hjT, -⟩
    exact h ⟨hT, ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hjT⟩⟩⟩
  · simp only [false_iff]
    rintro ⟨hT, hj, hjT, -⟩
    exact h ⟨hT, ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj, hjT⟩⟩⟩

/-- **S10, accept (existential form).** Some accept ⟺ T_F(H) < η̄. -/
theorem exists_accept_iff (ηbar : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    (∃ j, F.outcome ηbar H = Outcome.accept j) ↔ F.T H < ((ηbar : ℝ) : WithTop ℝ) := by
  constructor
  · rintro ⟨j, hj⟩; exact ((F.outcome_eq_accept_iff ηbar H j).mp hj).1
  · intro hT
    have hne := F.attainSet_nonempty (ne_top_of_lt hT)
    exact ⟨_, by unfold outcome; rw [dif_pos ⟨hT, hne⟩]⟩

/-- **S10, reject.** -/
theorem outcome_eq_reject_iff (ηbar : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    F.outcome ηbar H = Outcome.reject ↔
      ((ηbar : ℝ) : WithTop ℝ) ≤ F.T H ∧ ∀ j, F.Defined H j := by
  unfold outcome
  split_ifs with h h'
  · simp only [false_iff, not_and]; intro hle; exact absurd h.1 (not_lt.mpr hle)
  · simp only [true_iff]
    refine ⟨not_lt.mp fun hT => h ⟨hT, F.attainSet_nonempty (ne_top_of_lt hT)⟩, h'⟩
  · simp only [false_iff, not_and]; intro _; exact h'

/-- **S10, undetermined.** -/
theorem outcome_eq_undetermined_iff (ηbar : ℝ) (H : Matrix (Fin d) (Fin d) ℝ) :
    F.outcome ηbar H = Outcome.undetermined ↔
      ((ηbar : ℝ) : WithTop ℝ) ≤ F.T H ∧ ∃ j, ¬ F.Defined H j := by
  unfold outcome
  split_ifs with h h'
  · simp only [false_iff, not_and]; intro hle; exact absurd h.1 (not_lt.mpr hle)
  · simp only [false_iff, not_and, not_exists, not_not]; intro _; exact h'
  · simp only [true_iff]
    push Not at h'
    exact ⟨not_lt.mp fun hT => h ⟨hT, F.attainSet_nonempty (ne_top_of_lt hT)⟩, h'⟩


/-! ### Lemma 3.3 (what each outcome means) -/

/-- **Lemma 3.3(a), lens part.** Q_j := c_j^{-1/2} W_j is orthogonal
(Q_jᵀQ_j = Q_jQ_jᵀ = I), M_j = c_j · Q_j H Q_jᵀ, η_j(H) is defined iff
η(Q_j H Q_jᵀ) is (positive diagonal), and the two values are equal. -/
theorem lemma33a_orthogonal (H : Matrix (Fin d) (Fin d) ℝ) (j : Fin m) :
    let Q := (Real.sqrt (F.c j))⁻¹ • F.W j
    Qᵀ * Q = 1 ∧ Q * Qᵀ = 1 ∧ F.lensMat H j = F.c j • conj Q H ∧
    (F.Defined H j ↔ ∀ i, 0 < conj Q H i i) ∧ F.eta H j = domRatio (conj Q H) := by
  intro Q
  have hc := F.hc j
  have hs : 0 < Real.sqrt (F.c j) := Real.sqrt_pos.mpr hc
  have hss : (Real.sqrt (F.c j))⁻¹ * (Real.sqrt (F.c j))⁻¹ = (F.c j)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le]
  have hss' : (Real.sqrt (F.c j))⁻¹ * ((Real.sqrt (F.c j))⁻¹ * F.c j) = 1 := by
    rw [← mul_assoc, hss, inv_mul_cancel₀ hc.ne']
  have hQQ : Qᵀ * Q = 1 := by
    simp only [Q, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, F.hW j, hss',
      one_smul]
  have hQQ' : Q * Qᵀ = 1 := by
    simp only [Q, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      sq_frame_mul_transpose hc (F.hW j), hss', one_smul]
  have hM : F.lensMat H j = F.c j • conj Q H := by
    simp only [lensMat, conj, Q, Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul]
    rw [mul_assoc, hss, mul_inv_cancel₀ hc.ne', one_smul]
  have hsc := A56_6d_scale (conj Q H) hc
  refine ⟨hQQ, hQQ', hM, ?_, ?_⟩
  · rw [Defined, hM]; exact hsc.2.1
  · rw [eta, hM]; exact hsc.1

lemma defined_smul (H : Matrix (Fin d) (Fin d) ℝ) {b : ℝ} (hb : 0 < b) :
    F.Defined (b • H) = F.Defined H := by
  funext j
  apply propext
  unfold Defined lensMat
  rw [conj_smul]; exact (A56_6d_scale _ hb).2.1

lemma eta_smul (H : Matrix (Fin d) (Fin d) ℝ) {b : ℝ} (hb : 0 < b) :
    F.eta (b • H) = F.eta H := by
  funext j
  unfold eta lensMat
  rw [conj_smul]; exact (A56_6d_scale _ hb).1

/-- **Lemma 3.3(a), scale part.** For b > 0 the test on bH gives the same
definedness, the same η_j, the same T_F and the same outcome as on H. -/
theorem lemma33a_scale (H : Matrix (Fin d) (Fin d) ℝ) {b : ℝ} (hb : 0 < b) (ηbar : ℝ) :
    (∀ j, F.Defined (b • H) j ↔ F.Defined H j) ∧ (∀ j, F.eta (b • H) j = F.eta H j) ∧
    F.T (b • H) = F.T H ∧ F.outcome ηbar (b • H) = F.outcome ηbar H := by
  have hD := F.defined_smul H hb
  have hE := F.eta_smul H hb
  refine ⟨fun j => by rw [hD], fun j => by rw [hE], ?_, ?_⟩
  · unfold T; rw [hD, hE]
  · have hT : F.T (b • H) = F.T H := by unfold T; rw [hD, hE]
    cases h : F.outcome ηbar H with
    | accept j =>
      rw [outcome_eq_accept_iff, hT, hD, hE]; exact (F.outcome_eq_accept_iff ηbar H j).mp h
    | reject =>
      rw [outcome_eq_reject_iff, hT, hD]; exact (F.outcome_eq_reject_iff ηbar H).mp h
    | undetermined =>
      rw [outcome_eq_undetermined_iff, hT, hD]; exact (F.outcome_eq_undetermined_iff ηbar H).mp h

/-- A defined lens value bounds every row: rᵢ(M) ≤ η(M)·Mᵢᵢ. -/
lemma row_le_eta {M : Matrix (Fin d) (Fin d) ℝ} (hpos : ∀ i, 0 < M i i) (i : Fin d) :
    gershRadius M i ≤ domRatio M * M i i := by
  have hle : gershRadius M i / M i i ≤ domRatio M :=
    le_ciSup (f := fun i => gershRadius M i / M i i) (Finite.bddAbove_range _) i
  exact (div_le_iff₀ (hpos i)).mp hle

/-- **Lemma 3.3(b).** If the outcome is accept with witness j* (η̄ ≤ 1), then
M_{j*} passes, H ≻ 0, and
λ_min(H) ≥ c_{j*}⁻¹ (1 − η_{j*}(H)) minᵢ (M_{j*})ᵢᵢ > 0. -/
theorem lemma33b (hd : 0 < d) {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) {ηbar : ℝ}
    (hη1 : ηbar ≤ 1) {j : Fin m} (hacc : F.outcome ηbar H = Outcome.accept j) :
    PassesDominance (F.lensMat H j) ∧ H.PosDef ∧
    0 < (F.c j)⁻¹ * ((1 - F.eta H j) * ⨅ i, F.lensMat H j i i) ∧
    (F.c j)⁻¹ * ((1 - F.eta H j) * ⨅ i, F.lensMat H j i i) ≤ lamMin hH hd := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨hT, hj, hjT, -⟩ := (F.outcome_eq_accept_iff ηbar H j).mp hacc
  set M := F.lensMat H j with hMdef
  have hc := F.hc j
  have hη : F.eta H j < 1 := by
    have : ((F.eta H j : ℝ) : WithTop ℝ) < ((ηbar : ℝ) : WithTop ℝ) := hjT ▸ hT
    exact (WithTop.coe_lt_coe.mp this).trans_le hη1
  have hpass : PassesDominance M := ⟨hj, hη⟩
  -- the bound B := (1 − η) minᵢ Mᵢᵢ is positive
  obtain ⟨i₀, hi₀⟩ := exists_eq_ciInf_of_finite (f := fun i => M i i)
  have hmin_pos : 0 < ⨅ i, M i i := by rw [← hi₀]; exact hj i₀
  have hB : 0 < (1 - F.eta H j) * ⨅ i, M i i := mul_pos (by linarith) hmin_pos
  -- every eigenvalue λ of H satisfies cλ ≥ B
  have heig : ∀ k, (1 - F.eta H j) * (⨅ i, M i i) ≤ F.c j * hH.eigenvalues k := by
    intro k
    have hv := hH.mulVec_eigenvectorBasis k
    have hWv : F.W j *ᵥ ⇑(hH.eigenvectorBasis k) ≠ 0 := by
      intro h0
      apply eigvec_ne_zero hH k
      apply frame_injective hc (F.hW j)
      simp only [h0, Matrix.mulVec_zero]
    obtain ⟨i, hi⟩ := exists_le_of_eigvec hWv (conj_mulVec_eig (F.hW j) hv)
    have hr : gershRadius M i ≤ F.eta H j * M i i := row_le_eta hj i
    have hmi : (⨅ i, M i i) ≤ M i i := ciInf_le (Finite.bddBelow_range _) i
    have : (1 - F.eta H j) * (⨅ i, M i i) ≤ (1 - F.eta H j) * M i i :=
      mul_le_mul_of_nonneg_left hmi (by linarith)
    change M i i - gershRadius M i ≤ _ at hi
    nlinarith
  have hPD : H.PosDef := by
    rw [hH.posDef_iff_eigenvalues_pos]
    intro k
    have := heig k
    have : 0 < F.c j * hH.eigenvalues k := hB.trans_le this
    exact pos_of_mul_pos_right this hc.le
  refine ⟨hpass, hPD, mul_pos (inv_pos.mpr hc) hB, ?_⟩
  obtain ⟨k, hk⟩ := lamMin_mem hH hd
  rw [← hk, inv_mul_le_iff₀ hc]
  exact heig k

/-- **Lemma 3.3(c), first half (S18).** If some (M_j)ᵢᵢ ≤ 0, then H is not
positive definite. -/
theorem not_posDef_of_not_defined {H : Matrix (Fin d) (Fin d) ℝ} {j : Fin m}
    (hj : ¬ F.Defined H j) : ¬ H.PosDef := by
  intro hPD
  apply hj
  intro i
  have hc := F.hc j
  have hWW := sq_frame_mul_transpose hc (F.hW j)
  have hrow : F.W j i ≠ 0 := by
    intro h0
    have h1 : (F.W j * (F.W j)ᵀ) i i = F.W j i ⬝ᵥ F.W j i := by
      simp [Matrix.mul_apply, dotProduct]
    rw [hWW, h0] at h1
    simp at h1
    exact hc.ne' h1
  have := hPD.dotProduct_mulVec_pos hrow
  rw [star_trivial] at this
  rw [lensMat, conj_diag]; exact this

/-- **Lemma 3.3(c), S19.** If H is not positive definite, W H Wᵀ fails the
dominance test for every square tight frame W (declared or not). -/
theorem fails_every_sq_frame {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian)
    (hnpd : ¬ H.PosDef) (W : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : ¬ PassesDominance (conj W H) :=
  fun hp => hnpd (posDef_of_conj_passes hc hW hH hp)

/-- **Lemma 3.3(c).** For η̄ ≤ 1: the outcome is undetermined iff some η_j(H)
is undefined; in that case H is not positive definite and W H Wᵀ fails the
dominance test for every square tight frame W, declared or not. -/
theorem lemma33c {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) {ηbar : ℝ}
    (hη1 : ηbar ≤ 1) :
    (F.outcome ηbar H = Outcome.undetermined ↔ ∃ j, ¬ F.Defined H j) ∧
    ((∃ j, ¬ F.Defined H j) →
      ¬ H.PosDef ∧ ∀ (W : Matrix (Fin d) (Fin d) ℝ) (c : ℝ), 0 < c →
        Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ) → ¬ PassesDominance (conj W H)) := by
  have hcons : (∃ j, ¬ F.Defined H j) →
      ¬ H.PosDef ∧ ∀ (W : Matrix (Fin d) (Fin d) ℝ) (c : ℝ), 0 < c →
        Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ) → ¬ PassesDominance (conj W H) := by
    rintro ⟨j, hj⟩
    have hnpd := F.not_posDef_of_not_defined hj
    exact ⟨hnpd, fun W c hc hW => fails_every_sq_frame hH hnpd W c hc hW⟩
  refine ⟨⟨fun h => ((F.outcome_eq_undetermined_iff ηbar H).mp h).2, fun hex => ?_⟩, hcons⟩
  rw [outcome_eq_undetermined_iff]
  refine ⟨F.le_T fun k hk => ?_, hex⟩
  -- a defined lens that fails has η ≥ 1 ≥ η̄
  have hfail := (hcons hex).2 (F.W k) (F.c k) (F.hc k) (F.hW k)
  have h1 : 1 ≤ F.eta H k := by
    by_contra hlt; exact hfail ⟨hk, lt_of_not_ge hlt⟩
  exact WithTop.coe_le_coe.mpr (hη1.trans h1)

/-- **Lemma 3.3(d), first claim.** If the outcome is reject, no declared lens
passes at threshold η̄: there is no j with η_j(H) defined and η_j(H) < η̄
(all η_j are defined). -/
theorem lemma33d {H : Matrix (Fin d) (Fin d) ℝ} {ηbar : ℝ}
    (hrej : F.outcome ηbar H = Outcome.reject) :
    (∀ j, F.Defined H j) ∧ ∀ j, ¬ (F.Defined H j ∧ F.eta H j < ηbar) := by
  obtain ⟨hle, hall⟩ := (F.outcome_eq_reject_iff ηbar H).mp hrej
  refine ⟨hall, fun j ⟨hj, hlt⟩ => ?_⟩
  have := hle.trans (F.T_le hj)
  exact absurd (WithTop.coe_le_coe.mp this) (not_le.mpr hlt)


/-! ### One-lens families -/

/-- For a one-lens family, T_F(H) = η₁(H) if defined, +∞ otherwise. -/
lemma T_one (F : LensFamily d 1) (H : Matrix (Fin d) (Fin d) ℝ) :
    F.T H = if F.Defined H 0 then ((F.eta H 0 : ℝ) : WithTop ℝ) else ⊤ := by
  unfold T
  rw [Finset.univ_unique]
  by_cases h : F.Defined H 0
  · rw [if_pos h, Finset.filter_singleton, if_pos (by simpa using h), Finset.inf_singleton]; rfl
  · rw [if_neg h, Finset.filter_singleton, if_neg (by simpa using h), Finset.inf_empty]

/-- One-lens family, defined lens with η₁ < η̄: the outcome is accept (witness 0). -/
lemma outcome_one_accept (F : LensFamily d 1) {H : Matrix (Fin d) (Fin d) ℝ} {ηbar : ℝ}
    (hD : F.Defined H 0) (hlt : F.eta H 0 < ηbar) : F.outcome ηbar H = Outcome.accept 0 := by
  rw [outcome_eq_accept_iff, T_one, if_pos hD]
  exact ⟨WithTop.coe_lt_coe.mpr hlt, hD, rfl, fun k _ _ => Fin.zero_le _⟩

/-- One-lens family, defined lens with η₁ ≥ η̄: the outcome is reject. -/
lemma outcome_one_reject (F : LensFamily d 1) {H : Matrix (Fin d) (Fin d) ℝ} {ηbar : ℝ}
    (hD : F.Defined H 0) (hle : ηbar ≤ F.eta H 0) : F.outcome ηbar H = Outcome.reject := by
  rw [outcome_eq_reject_iff, T_one, if_pos hD]
  exact ⟨WithTop.coe_le_coe.mpr hle, fun k => by rwa [Subsingleton.elim k 0]⟩

end LensFamily

/-- The one-element tuple (W) for a square tight frame W. -/
def single (W : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : LensFamily d 1 where
  W := fun _ => W
  c := fun _ => c
  hm := Nat.one_pos
  hc := fun _ => hc
  hW := fun _ => hW

/-- The identity lens family F = (I_d). -/
def idFamily (d : ℕ) : LensFamily d 1 :=
  single 1 1 one_pos (by simp)

/-! ### Lemma 3.3(d): rejection occurs for some H ≻ 0 and for some indefinite H -/

/-- **Lemma 3.3(d), examples (S21).** d = 2, F = (I₂), η̄ = 1.
H = [[1,1],[1,2]] has η = 1, is rejected, and H ≻ 0 (det 1, trace 3).
H' = [[1,2],[2,1]] has η = 2, is rejected, det H' = −3 < 0, and H' is
indefinite (xᵀH'x < 0 at x = (1,−1), > 0 at x = (1,0)). -/
theorem lemma33d_examples :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 2]
    let H' : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2; 2, 1]
    domRatio H = 1 ∧ (idFamily 2).outcome 1 H = Outcome.reject ∧ H.PosDef ∧
    domRatio H' = 2 ∧ (idFamily 2).outcome 1 H' = Outcome.reject ∧ H'.det = -3 ∧
    (∃ x : Fin 2 → ℝ, x ⬝ᵥ (H' *ᵥ x) < 0) ∧ (∃ y : Fin 2 → ℝ, 0 < y ⬝ᵥ (H' *ᵥ y)) := by
  intro H H'
  have hl : ∀ M : Matrix (Fin 2) (Fin 2) ℝ, (idFamily 2).lensMat M 0 = M := by
    intro M; simp [LensFamily.lensMat, idFamily, single, conj]
  have hηH : domRatio H = 1 := by rw [domRatio_two]; norm_num [H]
  have hηH' : domRatio H' = 2 := by rw [domRatio_two]; norm_num [H']
  have hDH : (idFamily 2).Defined H 0 := by
    intro i; rw [hl]; fin_cases i <;> norm_num [H]
  have hDH' : (idFamily 2).Defined H' 0 := by
    intro i; rw [hl]; fin_cases i <;> norm_num [H']
  refine ⟨hηH, ?_, ?_, hηH', ?_, ?_, ⟨![1, -1], ?_⟩, ⟨![1, 0], ?_⟩⟩
  · apply LensFamily.outcome_one_reject _ hDH
    simp only [LensFamily.eta, hl, hηH, le_refl]
  · exact OCF.B6.posDef_two (by norm_num) (by norm_num)
  · apply LensFamily.outcome_one_reject _ hDH'
    simp only [LensFamily.eta, hl, hηH']; norm_num
  · simp [H', Matrix.det_fin_two]; norm_num
  · norm_num [H', dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  · simp [H', dotProduct, Matrix.mulVec, Fin.sum_univ_two]

/-! ### Proposition 4.1 (vacuity) -/

/-- η of a diagonal matrix is 0. -/
lemma domRatio_diagonal (v : Fin d → ℝ) : domRatio (diagonal v) = 0 := by
  have hg : ∀ i, gershRadius (diagonal v) i = 0 := by
    intro i
    unfold gershRadius
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [diagonal_apply_ne _ (Finset.ne_of_mem_erase hk).symm, abs_zero]
  unfold domRatio
  simp only [hg, zero_div]
  exact Real.iSup_const_zero

/-- **Proposition 4.1(a).** If H ≻ 0 there is an orthogonal W (WᵀW = WWᵀ = I)
with W H Wᵀ having positive diagonal and η(W H Wᵀ) = 0; hence the procedure
of Definition 3.2 applied to the (H-dependent) one-element tuple (W) accepts,
with witness its only index, at every η̄ ∈ (0, 1]. -/
theorem prop41a {H : Matrix (Fin d) (Fin d) ℝ} (hPD : H.PosDef) :
    ∃ (W : Matrix (Fin d) (Fin d) ℝ) (hW : Wᵀ * W = (1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)),
      W * Wᵀ = 1 ∧ (∀ i, 0 < conj W H i i) ∧ domRatio (conj W H) = 0 ∧
      ∀ ηbar : ℝ, 0 < ηbar → ηbar ≤ 1 →
        (single W 1 one_pos hW).outcome ηbar H = Outcome.accept 0 := by
  have hH := hPD.isHermitian
  set U : Matrix (Fin d) (Fin d) ℝ := (hH.eigenvectorUnitary : Matrix (Fin d) (Fin d) ℝ) with hU
  have hstar : star U = Uᵀ := by
    rw [Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have hdiag : Uᵀ * H * U = diagonal hH.eigenvalues := by
    have := hH.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at this
    rw [← hstar]
    simpa [RCLike.ofReal_real_eq_id] using this
  have hUU : Uᵀ * U = 1 := by
    rw [← hstar]; exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
  have hUU' : U * Uᵀ = 1 := by
    rw [← hstar]; exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
  have hconj : conj Uᵀ H = diagonal hH.eigenvalues := by
    rw [conj, Matrix.transpose_transpose, hdiag]
  have hW : (Uᵀ)ᵀ * Uᵀ = (1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [Matrix.transpose_transpose, hUU', one_smul]
  have hpos : ∀ i, 0 < conj Uᵀ H i i := by
    intro i; rw [hconj, diagonal_apply_eq]
    exact (hH.posDef_iff_eigenvalues_pos.mp hPD) i
  have hη : domRatio (conj Uᵀ H) = 0 := by rw [hconj]; exact domRatio_diagonal _
  refine ⟨Uᵀ, hW, by rw [Matrix.transpose_transpose, hUU], hpos, hη, fun ηbar hη0 _ => ?_⟩
  apply LensFamily.outcome_one_accept
  · exact hpos
  · show domRatio (conj Uᵀ H) < ηbar
    rw [hη]; exact hη0

/-- **Proposition 4.1(b).** If H (symmetric) is not positive definite,
W H Wᵀ fails the dominance test for every square tight frame W. -/
theorem prop41b {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) (hnpd : ¬ H.PosDef)
    (W : Matrix (Fin d) (Fin d) ℝ) (c : ℝ) (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : ¬ PassesDominance (conj W H) :=
  LensFamily.fails_every_sq_frame hH hnpd W c hc hW

/-- **Proposition 4.1(c).** Some square tight frame W makes W H Wᵀ pass iff
H ≻ 0. -/
theorem prop41c {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian) :
    (∃ (W : Matrix (Fin d) (Fin d) ℝ) (c : ℝ), 0 < c ∧
        Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ) ∧ PassesDominance (conj W H)) ↔
      H.PosDef := by
  constructor
  · rintro ⟨W, c, hc, hW, hp⟩; exact posDef_of_conj_passes hc hW hH hp
  · intro hPD
    obtain ⟨W, hW, -, hpos, hη, -⟩ := prop41a hPD
    exact ⟨W, 1, one_pos, hW, hpos, by rw [hη]; exact one_pos⟩

/-! ### Remark 4.2 (tight frames, as adjudicated) -/

/-- **Remark 4.2, all tight frames.** If H (symmetric) is not positive
definite, then for every tight frame W ∈ ℝ^{n×d} (WᵀW = cI, c > 0, any n),
W H Wᵀ fails the dominance test. -/
theorem rem42_tight_frames {H : Matrix (Fin d) (Fin d) ℝ} (hH : H.IsHermitian)
    (hnpd : ¬ H.PosDef) {n : ℕ} (W : Matrix (Fin n) (Fin d) ℝ) (c : ℝ) (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : ¬ PassesDominance (conj W H) :=
  fun hp => hnpd (posDef_of_conj_passes hc hW hH hp)

/-- **Remark 4.2 / Remark 2.1, redundant tight frames.** If n > d, W H Wᵀ
never passes, for any H (the rank argument; via A56 `A56_6f`). Every tight
frame has n ≥ d (A56 `frame_d_le_n`), so square and redundant exhaust the
tight frames. -/
theorem rem42_redundant {n : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) :
    d ≤ n ∧ (d < n → ∀ H : Matrix (Fin d) (Fin d) ℝ, ¬ PassesDominance (conj W H)) := by
  refine ⟨frame_d_le_n hc hW, fun hnd H hp => ?_⟩
  have hfr := A56_6d_frame (W := W) hc H
  have hp' : PassesDominance (conjOp W c H) := hfr.2.2.2.2.2.mp hp
  exact (A56_6f hc hW H hnd hp'.1).2 hp'

/-- **Remark 4.2, the non-frame example (J5).** H = diag(1, −1) (not positive
definite) and W = e₁ᵀ ∈ ℝ^{1×2}: WᵀW = diag(1, 0) is not c·I for any c, and
W H Wᵀ = (1) passes with η = 0. -/
theorem rem42_nonframe :
    let H : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]
    let W : Matrix (Fin 1) (Fin 2) ℝ := !![1, 0]
    ¬ H.PosDef ∧ Wᵀ * W = !![1, 0; 0, 0] ∧
    (∀ c : ℝ, Wᵀ * W ≠ c • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ∧
    conj W H = !![1] ∧ domRatio (conj W H) = 0 ∧ PassesDominance (conj W H) := by
  intro H W
  have hWW : Wᵀ * W = !![1, 0; 0, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [W, Matrix.mul_apply]
  have hC : conj W H = !![1] := by
    ext i j; fin_cases i; fin_cases j; simp [W, H, conj, Matrix.mul_apply, Fin.sum_univ_two]
  have hη : domRatio (conj W H) = 0 := by
    rw [hC]; simp [domRatio, gershRadius]
  refine ⟨?_, hWW, ?_, hC, hη, ⟨?_, by rw [hη]; exact one_pos⟩⟩
  · intro hPD
    have := hPD.diag_pos (i := 1)
    simp [H] at this
    linarith
  · intro c h
    rw [hWW] at h
    have h0 := congrFun (congrFun h 0) 0
    have h1 := congrFun (congrFun h 1) 1
    simp at h0 h1
    linarith
  · intro i; fin_cases i; rw [hC]; simp

/-- **Remark 4.2, trace clause.** If d ≥ 1 and tr H ≤ 0, then for every tight
frame W (any n, WᵀW = cI, c > 0) some diagonal entry of W H Wᵀ is ≤ 0. -/
theorem rem42_trace {H : Matrix (Fin d) (Fin d) ℝ} (hd : 0 < d) (htr : H.trace ≤ 0)
    {n : ℕ} {W : Matrix (Fin n) (Fin d) ℝ} {c : ℝ} (hc : 0 < c)
    (hW : Wᵀ * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)) : ∃ i, conj W H i i ≤ 0 := by
  have htrW : (conj W H).trace = c * H.trace := by
    rw [conj, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hW, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_smul, smul_eq_mul]
  have hn : 0 < n := lt_of_lt_of_le hd (frame_d_le_n hc hW)
  by_contra hall
  push Not at hall
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hpos : 0 < (conj W H).trace := by
    unfold Matrix.trace
    exact Finset.sum_pos (fun i _ => hall i) Finset.univ_nonempty
  rw [htrW] at hpos
  nlinarith

/-- **Remark 4.2, trace clause, test form.** If d ≥ 1 and tr H ≤ 0, then for
every declared family every η_j(H) is undefined and the outcome is
undetermined (at every η̄). -/
theorem rem42_trace_outcome {m : ℕ} (F : LensFamily d m) {H : Matrix (Fin d) (Fin d) ℝ}
    (hd : 0 < d) (htr : H.trace ≤ 0) (ηbar : ℝ) :
    (∀ j, ¬ F.Defined H j) ∧ F.outcome ηbar H = Outcome.undetermined := by
  have hund : ∀ j, ¬ F.Defined H j := by
    intro j hD
    obtain ⟨i, hi⟩ := rem42_trace hd htr (F.hc j) (F.hW j)
    exact absurd (hD i) (not_lt.mpr hi)
  refine ⟨hund, ?_⟩
  rw [LensFamily.outcome_eq_undetermined_iff]
  refine ⟨F.le_T fun k hk => absurd hk (hund k), ⟨⟨0, F.hm⟩, hund _⟩⟩

/-! ### Lemma 6.1 (the trace criterion) -/

/-- Σ_{i≠k} |M_ik| (the off-diagonal ℓ¹ mass). -/
def offDiagMass (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ k ∈ Finset.univ.erase i, |M i k|

/-- S30: Σ_{i≠k}|M_ik| = Σᵢ rᵢ(M). -/
lemma offDiagMass_eq_sum_gershRadius (M : Matrix (Fin d) (Fin d) ℝ) :
    offDiagMass M = ∑ i, gershRadius M i := rfl

/-- **Lemma 6.1(a).** If Σ_{i≠k}|M_ik| ≥ tr M, then M fails the dominance
test. (Symmetry of M is not used.) -/
theorem lemma61a (hd : 0 < d) (M : Matrix (Fin d) (Fin d) ℝ) (h : M.trace ≤ offDiagMass M) :
    ¬ PassesDominance M := by
  intro hp
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hlt : offDiagMass M < M.trace := by
    unfold offDiagMass Matrix.trace
    exact Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty
      (fun i _ => passes_imp_row_lt hp i)
  linarith

/-- At d = 0 Lemma 6.1(a) is false (the empty matrix passes vacuously and
0 ≥ 0): this is why `lemma61a` carries d ≥ 1 (the dossier's standing
convention is d ≥ 2). -/
example : PassesDominance (0 : Matrix (Fin 0) (Fin 0) ℝ) ∧
    (0 : Matrix (Fin 0) (Fin 0) ℝ).trace ≤ offDiagMass (0 : Matrix (Fin 0) (Fin 0) ℝ) :=
  ⟨⟨fun i => i.elim0, by simp [domRatio]⟩, by simp [offDiagMass]⟩

/-- **Lemma 6.1(b).** If Mᵢᵢ > 0 for all i, then η(M) ≥ Σᵢ rᵢ(M) / tr M. -/
theorem lemma61b (M : Matrix (Fin d) (Fin d) ℝ) (hpos : ∀ i, 0 < M i i) :
    offDiagMass M / M.trace ≤ domRatio M := by
  have hsum : offDiagMass M ≤ domRatio M * M.trace := by
    unfold offDiagMass Matrix.trace
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => LensFamily.row_le_eta hpos i
  rcases isEmpty_or_nonempty (Fin d) with hE | hN
  · simp [Matrix.trace, offDiagMass, domRatio]
  · have htr : 0 < M.trace :=
      Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
    exact (div_le_iff₀ htr).mpr hsum

/-- **Lemma 6.1(b), threshold form.** For d ≥ 1, positive diagonal and t > 0:
Σ_{i≠k}|M_ik| ≥ t · tr M implies η(M) ≥ t. -/
theorem lemma61b_threshold (hd : 0 < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∀ i, 0 < M i i) {t : ℝ} (_ht : 0 < t) (h : t * M.trace ≤ offDiagMass M) :
    t ≤ domRatio M := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have htr : 0 < M.trace := Finset.sum_pos (fun i _ => hpos i) Finset.univ_nonempty
  exact ((le_div_iff₀ htr).mpr h).trans (lemma61b M hpos)

/-! ### Remark 6.7: the alternative statistics and the counterexamples M1–M6 -/

/-- η_avg(M) := Σ_{i≠k}|M_ik| / tr M (the averaged ratio). -/
def etaAvg (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := offDiagMass M / M.trace

/-- η_frob(M) := ‖M − diag M‖_F / ‖diag M‖_F (v3/exp_006). -/
def etaFrob (M : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  Real.sqrt (∑ i, ∑ k ∈ Finset.univ.erase i, M i k ^ 2) / Real.sqrt (∑ i, M i i ^ 2)

/-- η_mean(M) := (1/d) Σᵢ rᵢ(M)/|Mᵢᵢ| (v3/exp_006). -/
def etaMean (M : Matrix (Fin d) (Fin d) ℝ) : ℝ := (∑ i, gershRadius M i / |M i i|) / d

/-- η_avg ≤ η on positive-diagonal matrices (Lemma 6.1(b) restated). -/
theorem etaAvg_le_domRatio (M : Matrix (Fin d) (Fin d) ℝ) (hpos : ∀ i, 0 < M i i) :
    etaAvg M ≤ domRatio M := lemma61b M hpos

/-- I + b(J − I). -/
def IbJ (d : ℕ) (b : ℝ) : Matrix (Fin d) (Fin d) ℝ := Matrix.of fun i k => if i = k then 1 else b

lemma IbJ_erase_sum (b : ℝ) (f : ℝ → ℝ) (i : Fin d) :
    ∑ k ∈ Finset.univ.erase i, f (IbJ d b i k) = (d - 1 : ℝ) * f b := by
  rw [Finset.sum_congr rfl (g := fun _ => f b)]
  · rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (fun h => by subst h; exact i.elim0)
    rw [Nat.cast_sub this]; simp
  · intro k hk
    simp [IbJ, (Finset.ne_of_mem_erase hk).symm]

lemma gershRadius_IbJ (b : ℝ) (i : Fin d) : gershRadius (IbJ d b) i = (d - 1 : ℝ) * |b| :=
  IbJ_erase_sum b (fun x => |x|) i

lemma offDiagMass_IbJ (b : ℝ) : offDiagMass (IbJ d b) = d * ((d - 1 : ℝ) * |b|) := by
  simp only [offDiagMass_eq_sum_gershRadius, gershRadius_IbJ, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

lemma trace_IbJ (b : ℝ) : (IbJ d b).trace = d := by
  simp [Matrix.trace, IbJ]

lemma domRatio_IbJ (hd : 0 < d) (b : ℝ) : domRatio (IbJ d b) = (d - 1 : ℝ) * |b| := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  unfold domRatio
  simp only [gershRadius_IbJ]
  simp [IbJ]

lemma etaFrob_IbJ (b : ℝ) :
    etaFrob (IbJ d b) = Real.sqrt (d * ((d - 1 : ℝ) * b ^ 2)) / Real.sqrt d := by
  unfold etaFrob
  congr 2
  · simp only [IbJ_erase_sum b (fun x => x ^ 2), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  · simp [IbJ]

/-- M1 := I + (1/5)(J − I), d = 10. -/
def M1 : Matrix (Fin 10) (Fin 10) ℝ := IbJ 10 (1 / 5)

/-- **M1 (Remark 6.7(d)).** η_avg(M1) = 9/5 ≥ 1 while η_frob(M1) = 3/5 < 1:
η_frob is not bounded below by η_avg, and violates the inclusion
{s < 1} ⊆ {η_avg < 1} of (c1). Also η(M1) = 9/5. -/
theorem M1_facts :
    etaAvg M1 = 9 / 5 ∧ etaFrob M1 = 3 / 5 ∧ domRatio M1 = 9 / 5 ∧
    etaFrob M1 < 1 ∧ 1 ≤ etaAvg M1 := by
  have hA : etaAvg M1 = 9 / 5 := by
    rw [etaAvg, M1, offDiagMass_IbJ, trace_IbJ]; norm_num [abs_of_pos]
  have hF : etaFrob M1 = 3 / 5 := by
    rw [M1, etaFrob_IbJ, ← Real.sqrt_div (by norm_num)]
    rw [show (↑(10:ℕ) : ℝ) * ((↑(10:ℕ) - 1) * (1 / 5) ^ 2) / ↑(10:ℕ) = (3 / 5) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  refine ⟨hA, hF, ?_, by rw [hF]; norm_num, by rw [hA]; norm_num⟩
  rw [M1, domRatio_IbJ (by norm_num)]; norm_num [abs_of_pos]

/-- M2 := I − (3/5)(J − I), d = 3. -/
def M2 : Matrix (Fin 3) (Fin 3) ℝ := IbJ 3 (-3 / 5)

/-- **M2 (Remark 6.7(d)).** η_frob(M2)² = 18/25, so η_frob(M2) = √18/5 < 1,
while M2 is indefinite: its characteristic polynomial is
(X − 8/5)²(X + 1/5) (spectrum {8/5, 8/5, −1/5}), (1,1,1) is an eigenvector
for −1/5, and M2 is not positive definite. η(M2) = 6/5 rejects it. -/
theorem M2_facts :
    etaFrob M2 ^ 2 = 18 / 25 ∧ etaFrob M2 = Real.sqrt 18 / 5 ∧ etaFrob M2 < 1 ∧
    M2.charpoly = (Polynomial.X - Polynomial.C (8 / 5)) ^ 2 * (Polynomial.X - Polynomial.C (-1 / 5)) ∧
    M2 *ᵥ (fun _ => 1) = (-1 / 5 : ℝ) • (fun _ => 1) ∧
    ¬ M2.PosDef ∧ domRatio M2 = 6 / 5 := by
  have hF : etaFrob M2 = Real.sqrt 18 / 5 := by
    rw [M2, etaFrob_IbJ, ← Real.sqrt_div (by norm_num)]
    rw [show (↑(3:ℕ) : ℝ) * ((↑(3:ℕ) - 1) * (-3 / 5) ^ 2) / ↑(3:ℕ) = 18 / 25 by norm_num,
      Real.sqrt_div (by norm_num), show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  have hF2 : etaFrob M2 ^ 2 = 18 / 25 := by
    rw [hF, div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hev : M2 *ᵥ (fun _ => 1) = (-1 / 5 : ℝ) • (fun _ => 1) := by
    ext i; fin_cases i <;> simp [M2, IbJ, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> norm_num
  refine ⟨hF2, hF, ?_, ?_, hev, ?_, ?_⟩
  · rw [hF, div_lt_one (by norm_num), Real.sqrt_lt' (by norm_num)]; norm_num
  · apply Polynomial.funext
    intro r
    rw [Matrix.eval_charpoly, Matrix.det_fin_three]
    simp [M2, IbJ, Matrix.scalar_apply]
    ring
  · intro hPD
    have := hPD.dotProduct_mulVec_pos (x := fun _ => (1 : ℝ)) (by
      intro h; have := congrFun h 0; simp at this)
    rw [hev, star_trivial] at this
    simp [dotProduct] at this
    linarith
  · rw [M2, domRatio_IbJ (by norm_num)]; norm_num [abs_of_neg]

/-- gershRadius as full row sum minus the diagonal term. -/
lemma gershRadius_eq_sub {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) :
    gershRadius M i = ∑ k, |M i k| - |M i i| := by
  unfold gershRadius
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]

/-- M3 := [[1, 9/10, 0], [9/10, 1, 0], [0, 0, 1/100]]. -/
def M3 : Matrix (Fin 3) (Fin 3) ℝ := !![1, 9 / 10, 0; 9 / 10, 1, 0; 0, 0, 1 / 100]

/-- **M3.** η_mean(M3) = 3/5 < η_avg(M3) = 60/67: η_mean is not bounded below
by η_avg. -/
theorem M3_facts : etaMean M3 = 3 / 5 ∧ etaAvg M3 = 60 / 67 ∧ etaMean M3 < etaAvg M3 := by
  have hm : etaMean M3 = 3 / 5 := by
    simp [etaMean, M3, gershRadius_eq_sub, Fin.sum_univ_three]; norm_num
  have ha : etaAvg M3 = 60 / 67 := by
    simp [etaAvg, offDiagMass_eq_sum_gershRadius, M3, gershRadius_eq_sub, Fin.sum_univ_three,
      Matrix.trace]; norm_num
  exact ⟨hm, ha, by rw [hm, ha]; norm_num⟩

/-- M4 := [[1, 1/2], [1/2, 1/100]]. -/
def M4 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1 / 2; 1 / 2, 1 / 100]

/-- **M4 (Remark 6.7(c2)).** M4 has positive diagonal and η_avg(M4) =
100/101 < 1, yet det M4 = −6/25 < 0 and M4 is indefinite (not positive
definite): η_avg does not keep the certificate. η(M4) = 50. -/
theorem M4_facts :
    (∀ i, 0 < M4 i i) ∧ etaAvg M4 = 100 / 101 ∧ etaAvg M4 < 1 ∧ M4.det = -6 / 25 ∧
    ¬ M4.PosDef ∧ (∃ x : Fin 2 → ℝ, x ⬝ᵥ (M4 *ᵥ x) < 0) ∧
    (∃ y : Fin 2 → ℝ, 0 < y ⬝ᵥ (M4 *ᵥ y)) ∧ domRatio M4 = 50 := by
  have ha : etaAvg M4 = 100 / 101 := by
    simp [etaAvg, offDiagMass_eq_sum_gershRadius, M4, gershRadius_eq_sub, Fin.sum_univ_two,
      Matrix.trace]; norm_num
  have hneg : (![1, -2] : Fin 2 → ℝ) ⬝ᵥ (M4 *ᵥ ![1, -2]) < 0 := by
    norm_num [M4, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  refine ⟨?_, ha, by rw [ha]; norm_num, ?_, ?_, ⟨_, hneg⟩, ⟨![1, 0], ?_⟩, ?_⟩
  · intro i; fin_cases i <;> norm_num [M4]
  · simp [M4, Matrix.det_fin_two]; norm_num
  · intro hPD
    have := hPD.dotProduct_mulVec_pos (x := ![1, -2]) (by
      intro h; have := congrFun h 0; simp at this)
    rw [star_trivial] at this
    linarith
  · norm_num [M4, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  · rw [M4, domRatio_two]; norm_num

/-- M5 := [[1, 3/2], [3/2, 1]] ⊕ I₂ (written out as a 4×4 matrix). -/
def M5 : Matrix (Fin 4) (Fin 4) ℝ :=
  !![1, 3 / 2, 0, 0; 3 / 2, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1]

/-- **M5 (Remark 6.7, η_mean).** η_mean(M5) = 3/4 < 1, and M5 is indefinite
(xᵀM5x = −1 at x = (1,−1,0,0), yᵀM5y = 1 at y = e₃): η_mean violates the
inclusion {s < 1} ⊆ {M ≻ 0} of (c2). -/
theorem M5_facts :
    etaMean M5 = 3 / 4 ∧ etaMean M5 < 1 ∧ ¬ M5.PosDef ∧
    (∃ x : Fin 4 → ℝ, x ⬝ᵥ (M5 *ᵥ x) < 0) ∧ (∃ y : Fin 4 → ℝ, 0 < y ⬝ᵥ (M5 *ᵥ y)) := by
  have hm : etaMean M5 = 3 / 4 := by
    simp [etaMean, M5, gershRadius_eq_sub, Fin.sum_univ_four]; norm_num
  have hneg : (![1, -1, 0, 0] : Fin 4 → ℝ) ⬝ᵥ (M5 *ᵥ ![1, -1, 0, 0]) < 0 := by
    simp [M5, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]; norm_num
  refine ⟨hm, by rw [hm]; norm_num, ?_, ⟨_, hneg⟩, ⟨![0, 0, 1, 0], ?_⟩⟩
  · intro hPD
    have := hPD.dotProduct_mulVec_pos (x := ![1, -1, 0, 0]) (by
      intro h; have := congrFun h 0; simp at this)
    rw [star_trivial] at this
    linarith
  · simp [M5, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

/-- M6 := [[10, 11], [11, 10]] ⊕ [1] (written out as a 3×3 matrix). -/
def M6 : Matrix (Fin 3) (Fin 3) ℝ := !![10, 11, 0; 11, 10, 0; 0, 0, 1]

/-- **M6 (re-audit addendum).** η_mean(M6) = 11/15 < 1 ≤ η_avg(M6) = 22/21:
η_mean violates the inclusion {s < 1} ⊆ {η_avg < 1} of (c1); M6 is also
indefinite (xᵀM6x = −2 at x = (1,−1,0), yᵀM6y = 1 at y = e₃). -/
theorem M6_facts :
    etaMean M6 = 11 / 15 ∧ etaAvg M6 = 22 / 21 ∧ etaMean M6 < 1 ∧ 1 ≤ etaAvg M6 ∧
    ¬ M6.PosDef ∧ (∃ x : Fin 3 → ℝ, x ⬝ᵥ (M6 *ᵥ x) < 0) ∧
    (∃ y : Fin 3 → ℝ, 0 < y ⬝ᵥ (M6 *ᵥ y)) := by
  have hm : etaMean M6 = 11 / 15 := by
    simp [etaMean, M6, gershRadius_eq_sub, Fin.sum_univ_three]; norm_num
  have ha : etaAvg M6 = 22 / 21 := by
    simp [etaAvg, offDiagMass_eq_sum_gershRadius, M6, gershRadius_eq_sub, Fin.sum_univ_three,
      Matrix.trace]; norm_num
  have hneg : (![1, -1, 0] : Fin 3 → ℝ) ⬝ᵥ (M6 *ᵥ ![1, -1, 0]) < 0 := by
    simp [M6, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]; norm_num
  refine ⟨hm, ha, by rw [hm]; norm_num, by rw [ha]; norm_num, ?_, ⟨_, hneg⟩, ⟨![0, 0, 1], ?_⟩⟩
  · intro hPD
    have := hPD.dotProduct_mulVec_pos (x := ![1, -1, 0]) (by
      intro h; have := congrFun h 0; simp at this)
    rw [star_trivial] at this
    linarith
  · simp [M6, dotProduct, Matrix.mulVec, Fin.sum_univ_succ]

/-! ### Axiom audit (headline theorems) -/

#print axioms LensFamily.outcome_eq_accept_iff
#print axioms LensFamily.exists_accept_iff
#print axioms LensFamily.outcome_eq_reject_iff
#print axioms LensFamily.outcome_eq_undetermined_iff
#print axioms LensFamily.lemma33a_orthogonal
#print axioms LensFamily.lemma33a_scale
#print axioms LensFamily.lemma33b
#print axioms LensFamily.lemma33c
#print axioms LensFamily.not_posDef_of_not_defined
#print axioms LensFamily.fails_every_sq_frame
#print axioms LensFamily.lemma33d
#print axioms lemma33d_examples
#print axioms prop41a
#print axioms prop41b
#print axioms prop41c
#print axioms rem42_tight_frames
#print axioms rem42_redundant
#print axioms rem42_nonframe
#print axioms rem42_trace
#print axioms rem42_trace_outcome
#print axioms lemma61a
#print axioms lemma61b
#print axioms lemma61b_threshold
#print axioms offDiagMass_eq_sum_gershRadius
#print axioms etaAvg_le_domRatio
#print axioms M1_facts
#print axioms M2_facts
#print axioms M3_facts
#print axioms M4_facts
#print axioms M5_facts
#print axioms M6_facts
#print axioms posDef_of_conj_passes

end OCF.D4

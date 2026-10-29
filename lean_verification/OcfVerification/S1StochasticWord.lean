/-
S1 (the stochastic-word certificate) — the Lean target of section 11 of the adjudicated dossier:
the new algebra of Theorem S for the word  W_h = N_h ∘ D^{h,I}_E  (noise after a gradient step)
at temperature τ, on a smooth declaration with a COMPUTED pair (m, L).

Source of truth: project_plan/doing/proof_audits/S1_stochastic_word/01_derivation.md (stage-3
revised, 2026-10-19), section 1 (Theorem S, hypotheses H-decl, H-curv, H-word, H-law), section 2
(Lemma S1 steps 3 and 5), section 3 (Lemma S2), section 5 (Lemma S4), section 6 (assembly),
section 11 (Lean target); rulings in 03_adjudication.md (finding 1: the computed pair
0 < m ≤ σ^T, β̂ ≤ L; finding 13: Lean limited to the new algebra).

DEFINITIONAL MAP (dossier symbol — Lean name):
* ℝᵈ — a real inner product space `X` (every algebraic lemma holds in any such space; the
  dimension `d` enters only as the natural number `d` in the bias term; `d ≥ 1` — `0 < d`, and
  `[Nontrivial X]` where a pair of distinct points is needed).
* E (the energy of the declaration), ∇E — `E : X → ℝ`, `gradient E` (Mathlib). E ∈ C¹ is
  `Differentiable ℝ E` where a gradient identity needs it.
* C(E, σ), "E − (σ/2)‖·‖² is convex" — G3's `OCF.G3.ModC E σ` (landed def:moduli).
* "∇E is β-Lipschitz" — G3's `OCF.G3.LipGrad E β`.
* σ^T, β̂, m, L — real numbers `σT`, `β̂`, `m`, `L`; the hypotheses (H-curv) are
  `0 < m`, `m ≤ σT`, `β̂ ≤ L`; the fact that σ^T is a maximum of two numbers is
  `modC_max`. The landed facts `ModC E σT` and `LipGrad E β̂` (lem:rule-sum) enter as hypotheses.
* Dalalyan's assumption (1a) with constant m — `Dal1a E m` (verbatim: for all θ θ′,
  E θ − E θ′ − ⟨∇E θ′, θ − θ′⟩ ≥ (m/2)‖θ − θ′‖²); (1b) with constant M — `LipGrad E M`.
* τ (temperature), h (step), d, f = E/τ, h′ = τh, (m′, M′) = (m/τ, L/τ) — `τ`, `h`, `d`,
  `fun x => E x / τ`, `τ * h`, `m / τ`, `L / τ`.
* q = 1 − m h, bias(h) = 1.82 (L/m)(τ h d)^{1/2}, Ψ_K = q^K r₀ + bias(h), r₀ —
  `1 - m * h`, `bias τ d m L h`, `Psi q r₀ b K`, `r0 g0 τ d m` (g0 stands for ‖∇E(x₀)‖).
* K_ε = least K ≥ 0 with q^K r₀ ≤ ε − bias(h) — `Keps q r₀ c = sInf {K | q^K * r₀ ≤ c}` with
  `c = ε − bias`; the comparison loop "multiply by q until ≤ ε − bias" — `loopAux`.
* h_θ(ε) = min{2/(m+L), (θ ε m)²/(1.82² L² τ d)} — `hTheta m L τ d ε θ`.
* The Gaussian kernel P_h(x, ·) = Normal(x − h∇E(x), 2τh I) and the law ν₀ P_h^K of the K-th
  iterate — a family `G : X → ℝ → Measure X` (mean, variance factor; its Gaussian character is
  never used), `kernel G E τ h`, `lawIter P ν K = (fun μ => μ.bind P)^[K] ν`.
* W2 and the laws (ν₀, δ_{x₀}, π_τ, step map ν ↦ νP_h) — abstract: a type `Law`, a function
  `W2 : Law → Law → ℝ` and `step : Law → Law`. Nothing about W2 is assumed except the named
  hypotheses below (W2 as a measure-theoretic object is outside the Lean target).

NAMED HYPOTHESES (classical inputs, per the house pattern: hypotheses of the statements that use
them, never global axioms; each is stated as the cited source states it):
* `hDalalyan : DalalyanThm1a …` — [CLASSICAL] Dalalyan, arXiv:1704.04752v2, Thm 1(a), p. 3: for
  an initial law ν₀ (here: those satisfying `Adm`, "finite second moment", dossier H-law) and
  every K, W2(ν₀ P_h^K, π_τ) ≤ (1 − m h)^K W2(ν₀, π_τ) + 1.82 (L/m)(τ h d)^{1/2}. This is Theorem S(a)
  of the dossier VERBATIM (the dossier obtains it from Thm 1(a) by Lemmas S1, S2; those
  identifications are the prose-only kernel/word identification, not formalised here).
* `hSecondMoment : M2 ≤ τ * d / m` — [CLASSICAL] Durmus–Moulines, arXiv:1605.01559v4, Prop. 1(ii),
  p. 6, for U = E/τ: ∫‖y − x*‖² π_τ(dy) ≤ τ d / m. `M2` is the value of that integral (a real number).
* `hDiracCoupling : W2 δ π ^ 2 = A` — [CLASSICAL] W2(δ_x, ν)² = ∫‖x − y‖² ν(dy), Dalalyan p. 3,
  display (4), first line; `A` is the value of that integral.
* `hMinkowski : √A ≤ ‖x₀ − x*‖ + √M2` — [CLASSICAL] triangle inequality in L²(π_τ; ℝᵈ) applied to
  x₀ − y = (x₀ − x*) + (x* − y) (dossier C6). Together the last three are the Dirac-start
  bound of Lemma S3(ii) (printed neighbours: Durmus–Moulines Prop. 1(iv) p. 6, Thm 5 p. 8).
* `hDist : ‖x₀ − x*‖ ≤ ‖∇E(x₀)‖ / m` — [LANDED] thm:soundness(c) with no non-smooth term (g = 0);
  machine-checked in G3SoundnessProx.lean (`regimeAP_of`: ‖x − x*‖ ≤ ‖R_α(x)‖/σ, with
  R_α = ∇F when g = 0, then σ ≥ m) and NOT re-proved here.

COVERAGE (dossier item — Lean name), all FORMALISED (statement + proof, no sorry):
* (L-A′) Lemma S1 step 3, `m ≤ σ^T` ⟹ C(E, m): `modC_mono`; σ^T = max{σ̂, b(T)}: `modC_max`;
  Lemma S1 step 5: β̂ > 0 from (1a) (and more: m ≤ β̂): `dal1a_strongMono`, `betaHat_pos`,
  `m_le_betaHat`; the order of the constants `m ≤ σ^T ≤ β̂ ≤ L` and `m ≤ L`:
  `curv_order`, `m_le_L_of_dal`.
* (L-C) Lemma S2: (i) `kernel_mean_eq`, `kernel_eq`; (ii) `dal1a_div`, `dal1b_div`,
  `rescaled_order`, `gradient_div_const`; (iii) `step_range_iff`, `step_lt_two_div`; (v) `contraction_eq`,
  `condition_ratio_eq`, `bias_rescaled` ((h′ d)^{1/2} = (τ h d)^{1/2} is syntactic); (vi) at the level of algebra
  `lawIter_congr`, `lawIter_succ`.
* (L-E) Lemma S4: (i) `q_mem`; (ii) `Psi_antitone`, `Psi_ge`, `Psi_tendsto`; (iii)
  `Keps_nonempty`, `Keps_mem`, `Keps_le_of_mem`, `Keps_upward`, `Keps_zero`, `Keps_one`, `Keps_log`,
  `Keps_le_ceil`, `Keps_le_int_ceil`, and the exact floor remark `Psi_gt_of_lt_bias`;
  (iv) `loopAux_eq`, `loop_eq_Keps`; (v) `bias_le_iff`, `hTheta_pos`, `hTheta_admissible`,
  `bias_hTheta_le`, `Psi_le_of_step_rule`.
* Assembly of Theorem S (b) and (c) from the named hypotheses (real inequalities only):
  `theoremS_b`, `theoremS_c`, `theoremS_step_rule`.
* Theorem S (d) is Lemma S2 (iii), (v) (`step_range_iff`, `contraction_eq`, `bias_rescaled`):
  the step condition and the contraction factor are the same numbers for (m, L) and
  (m/τ, L/τ), and τ enters only through `bias` and `r0`.

NOT COVERED (remain prose-only, per section 11): W2 as a measure-theoretic object; Lemma S1
steps 1, 2, 4, 6 (domain, landed Lipschitz, the Beck/Bauschke–Combettes first-order and
unique-minimiser textbook statements); Lemma S2 (iv) (e^{−f} = e^{−E/τ}, a definition) and the
identification of the manuscript word with the kernel P_h (by construction); Lemma S3 (i), (ii)
beyond the real-inequality chain above; the exact-arithmetic provenance of the pair (m, L)
(rem:exact-arithmetic); every numerical check.

Status tier: FORMALISED (statement + proof, no sorry) for (L-A′), (L-C), (L-E) and the real-inequality
assembly of Theorem S(b),(c) from the named hypotheses. Theorem S as a statement about Wasserstein
distances of laws is NOT formalised (the analytic content is the hypothesis `hDalalyan`).
-/
import Mathlib
import OcfVerification.G3SoundnessQuadratic

open Set Filter Topology OCF.G3

namespace OCF.S1

/-! ## Section A: Lemma S1, the order of the constants (L-A′) -/

section A

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The squared norm is convex on the whole space (tool). -/
lemma convexOn_normsq : ConvexOn ℝ univ (fun x : X => ‖x‖ ^ 2) := by
  have := (convexOn_univ_norm (E := X)).pow (fun _ _ => norm_nonneg _) 2
  simpa [Pi.pow_def] using this

/-- Dalalyan's assumption (1a), p. 2, with constant `m` and the gradient of `E`:
for all θ θ′, `E θ − E θ′ − ⟨∇E θ′, θ − θ′⟩ ≥ (m/2)‖θ − θ′‖²`. (Assumption (1b) is G3's `LipGrad`.) -/
def Dal1a (E : X → ℝ) (m : ℝ) : Prop :=
  ∀ θ θ' : X, m / 2 * ‖θ - θ'‖ ^ 2 ≤ E θ - E θ' - inner ℝ (gradient E θ') (θ - θ')

/-- Lemma S1 step 3, the new line: `m ≤ σ^T` and C(E, σ^T) give C(E, m)
(`E − (m/2)‖·‖² = [E − (σ^T/2)‖·‖²] + ((σ^T − m)/2)‖·‖²`, a sum of two convex functions). -/
lemma modC_mono {E : X → ℝ} {σT m : ℝ} (h : ModC E σT) (hm : m ≤ σT) : ModC E m := by
  have h2 : ConvexOn ℝ univ (fun x : X => (σT - m) / 2 * ‖x‖ ^ 2) := by
    simpa [smul_eq_mul] using
      (convexOn_normsq (X := X)).smul (c := (σT - m) / 2) (by linarith)
  have e : (fun x : X => E x - m / 2 * ‖x‖ ^ 2)
      = (fun x : X => E x - σT / 2 * ‖x‖ ^ 2) + fun x : X => (σT - m) / 2 * ‖x‖ ^ 2 := by
    funext x
    simp only [Pi.add_apply]
    ring
  unfold ModC
  rw [e]
  exact h.add h2

/-- Lemma S1 step 3, "σ^T = max{σ̂, b(T)} equals one of the two": C(E, a) and C(E, b) give C(E, max a b). -/
lemma modC_max {E : X → ℝ} {a b : ℝ} (ha : ModC E a) (hb : ModC E b) : ModC E (max a b) := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

/-- Adding (1a) written for (θ, θ′) and (θ′, θ): strong monotonicity of `∇E` with constant `m`
(Lemma S1 step 5, the first line). -/
lemma dal1a_strongMono {E : X → ℝ} {m : ℝ} (h : Dal1a E m) : StrongMono E m := by
  intro x y
  have h1 := h x y
  have h2 := h y x
  have hn : ‖y - x‖ = ‖x - y‖ := norm_sub_rev y x
  have hi : inner ℝ (gradient E x - gradient E y) (x - y)
      = inner ℝ (gradient E y) (x - y) * (-1) + inner ℝ (gradient E x) (y - x) * (-1) := by
    have : y - x = -(x - y) := by abel
    rw [this, inner_neg_right, inner_sub_left]
    ring
  rw [hn] at h2
  rw [hi]
  nlinarith

/-- Lemma S1 step 5, new content, the sharper form: (1a) and (1b) with constants `m` and `β̂`
(`X` nontrivial, i.e. `d ≥ 1`) force `m ≤ β̂`. The dossier's `β̂ > 0` (when `m > 0`) is the corollary
`betaHat_pos`. -/
lemma m_le_betaHat [Nontrivial X] {E : X → ℝ} {m β : ℝ} (h1a : Dal1a E m) (h1b : LipGrad E β) :
    m ≤ β := by
  obtain ⟨x, y, hxy⟩ := exists_pair_ne X
  have hsub : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  have hsm := dal1a_strongMono h1a x y
  have hcs := real_inner_le_norm (gradient E x - gradient E y) (x - y)
  have hl := h1b x y
  have : m * ‖x - y‖ ^ 2 ≤ β * ‖x - y‖ ^ 2 := by
    calc m * ‖x - y‖ ^ 2 ≤ _ := hsm
      _ ≤ ‖gradient E x - gradient E y‖ * ‖x - y‖ := hcs
      _ ≤ β * ‖x - y‖ * ‖x - y‖ := by gcongr
      _ = β * ‖x - y‖ ^ 2 := by ring
  exact le_of_mul_le_mul_right this (by positivity)

/-- Lemma S1 step 5, the dossier's two lines: from (1a) with `m > 0` and (1b) with constant `β̂`,
`β̂ > 0` (otherwise `∇E` would be constant, against (1a)). -/
lemma betaHat_pos [Nontrivial X] {E : X → ℝ} {m β : ℝ} (hm : 0 < m) (h1a : Dal1a E m)
    (h1b : LipGrad E β) : 0 < β :=
  lt_of_lt_of_le hm (m_le_betaHat h1a h1b)

/-- The order of the constants of Lemma S1 step 5: `m ≤ σ^T`, `σ^T ≤ β̂` (landed
thm:soundness(a)) and `β̂ ≤ L` give `m ≤ σ^T ≤ β̂ ≤ L`. -/
lemma curv_order {m σT β L : ℝ} (hm : m ≤ σT) (hσβ : σT ≤ β) (hβL : β ≤ L) :
    m ≤ σT ∧ σT ≤ β ∧ β ≤ L ∧ m ≤ L :=
  ⟨hm, hσβ, hβL, hm.trans (hσβ.trans hβL)⟩

/-- The same `m ≤ L` obtained directly from (1a), (1b) with constants `(m, L)`, without
the landed soundness theorem: used for Dalalyan's constants `(m, M) = (m, L)`. -/
lemma m_le_L_of_dal [Nontrivial X] {E : X → ℝ} {m L : ℝ} (h1a : Dal1a E m) (h1b : LipGrad E L) :
    m ≤ L :=
  m_le_betaHat h1a h1b

end A

/-! ## Section C: Lemma S2, the temperature rescaling (L-C) -/

section C

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- `∇(E/τ) = τ⁻¹ ∇E` for differentiable `E` (tool for Lemma S2 (i), (ii)). -/
lemma gradient_div_const {E : X → ℝ} (hE : Differentiable ℝ E) {τ : ℝ} (x : X) :
    gradient (fun y => E y / τ) x = τ⁻¹ • gradient E x := by
  have h2 : fderiv ℝ (fun y => E y / τ) x = τ⁻¹ • fderiv ℝ E x := by
    have : (fun y => E y / τ) = fun y => τ⁻¹ • E y := by
      funext y; simp [div_eq_inv_mul]
    rw [this, fderiv_fun_const_smul (hE x)]
  unfold gradient
  rw [h2, map_smul]

/-- Lemma S2 (i), the mean: `x − h ∇E(x) = x − (τ h) ∇(E/τ)(x)`  (`h′ ∇f = (τ h)(∇E/τ) = h ∇E`). -/
lemma kernel_mean_eq {E : X → ℝ} (hE : Differentiable ℝ E) {τ : ℝ} (hτ : τ ≠ 0) (h : ℝ) (x : X) :
    x - h • gradient E x = x - (τ * h) • gradient (fun y => E y / τ) x := by
  rw [gradient_div_const hE, smul_smul]
  congr 2
  field_simp

/-- Lemma S2 (ii), the order of the constants: `0 < m′ ≤ M′` for `m′ = m/τ`, `M′ = L/τ`. -/
lemma rescaled_order {m L τ : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ) :
    0 < m / τ ∧ m / τ ≤ L / τ :=
  ⟨div_pos hm hτ, div_le_div_of_nonneg_right hmL hτ.le⟩

/-- Lemma S2 (ii), (1a): `E/τ` satisfies (1a) with constant `m/τ`. -/
lemma dal1a_div {E : X → ℝ} (hE : Differentiable ℝ E) {m τ : ℝ} (hτ : 0 < τ) (h : Dal1a E m) :
    Dal1a (fun y => E y / τ) (m / τ) := by
  intro θ θ'
  have := h θ θ'
  rw [gradient_div_const hE, inner_smul_left]
  simp only [conj_trivial]
  have e : m / τ / 2 * ‖θ - θ'‖ ^ 2 = (m / 2 * ‖θ - θ'‖ ^ 2) / τ := by ring
  have e2 : E θ / τ - E θ' / τ - τ⁻¹ * inner ℝ (gradient E θ') (θ - θ')
      = (E θ - E θ' - inner ℝ (gradient E θ') (θ - θ')) / τ := by
    field_simp
  rw [e, e2]
  exact div_le_div_of_nonneg_right this hτ.le

/-- Lemma S2 (ii), (1b): `E/τ` has an `M/τ`-Lipschitz gradient when `E` has an `M`-Lipschitz one. -/
lemma dal1b_div {E : X → ℝ} (hE : Differentiable ℝ E) {M τ : ℝ} (hτ : 0 < τ) (h : LipGrad E M) :
    LipGrad (fun y => E y / τ) (M / τ) := by
  intro u v
  rw [gradient_div_const hE, gradient_div_const hE, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_inv, abs_of_pos hτ]
  have := h u v
  have e : M / τ * ‖u - v‖ = τ⁻¹ * (M * ‖u - v‖) := by ring
  rw [e]
  exact mul_le_mul_of_nonneg_left this (inv_nonneg.2 hτ.le)

/-- Lemma S2 (iii): `h ≤ 2/(m + L)  ⟺  τ h ≤ 2/(m/τ + L/τ)`. -/
lemma step_range_iff {m L τ h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ) :
    h ≤ 2 / (m + L) ↔ τ * h ≤ 2 / (m / τ + L / τ) := by
  have hL : 0 < L := hm.trans_le hmL
  have e : 2 / (m / τ + L / τ) = τ * (2 / (m + L)) := by
    field_simp
  rw [e]
  exact (mul_le_mul_iff_right₀ hτ).symm

/-- Lemma S2 (iii), second half: in that case `h′ = τ h < 2/M′ = 2/(L/τ)`. -/
lemma step_lt_two_div {m L τ h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ)
    (hh : h ≤ 2 / (m + L)) : τ * h < 2 / (L / τ) := by
  have hL : 0 < L := hm.trans_le hmL
  have e : 2 / (L / τ) = τ * (2 / L) := by field_simp
  rw [e]
  refine mul_lt_mul_of_pos_left (lt_of_le_of_lt hh ?_) hτ
  exact div_lt_div_of_pos_left (by norm_num) hL (by linarith)

/-- Lemma S2 (v): the contraction factor is unchanged, `m′ h′ = (m/τ)(τ h) = m h`. -/
lemma contraction_eq {m τ h : ℝ} (hτ : τ ≠ 0) : m / τ * (τ * h) = m * h := by
  field_simp

/-- Lemma S2 (v): `M′/m′ = (L/τ)/(m/τ) = L/m`. -/
lemma condition_ratio_eq {m L τ : ℝ} (hτ : τ ≠ 0) : (L / τ) / (m / τ) = L / m := by
  field_simp

/-- The bias floor of Theorem S(a): `bias(h) = 1.82 (L/m)(τ h d)^{1/2}`. -/
noncomputable def bias (τ : ℝ) (d : ℕ) (m L h : ℝ) : ℝ :=
  1.82 * (L / m) * Real.sqrt (τ * h * d)

/-- Lemma S2 (v), assembled: Dalalyan's bias term for the normalised chain `(f, h′) = (E/τ, τ h)`,
constants `(m/τ, L/τ)` and dimension `d`, namely `1.82 (M′/m′)(h′ d)^{1/2}`, is the `bias(h)`
of Theorem S(a). -/
lemma bias_rescaled {m L τ h : ℝ} (d : ℕ) (hτ : τ ≠ 0) :
    1.82 * ((L / τ) / (m / τ)) * Real.sqrt ((τ * h) * d) = bias τ d m L h := by
  unfold bias
  rw [condition_ratio_eq hτ]

/-! The Gaussian kernel and the K-th law, at the level of algebra. -/

variable [MeasurableSpace X]

/-- The kernel of the word at temperature τ and step h: `Normal(x − h ∇E(x), 2τh I)`, with the
Gaussian family `G mean variance-factor` abstract (its Gaussian character is never used). -/
noncomputable def kernel (G : X → ℝ → MeasureTheory.Measure X) (E : X → ℝ) (τ h : ℝ) (x : X) :
    MeasureTheory.Measure X :=
  G (x - h • gradient E x) (2 * τ * h)

/-- Lemma S2 (i), the whole kernel: the word's kernel at `(E, τ, h)` is the kernel of Dalalyan's
update (2) for `(f, h′) = (E/τ, τ h)`, which is `Normal(x − h′∇f(x), 2h′ I)` (temperature one). -/
lemma kernel_eq (G : X → ℝ → MeasureTheory.Measure X) {E : X → ℝ} (hE : Differentiable ℝ E)
    {τ : ℝ} (hτ : τ ≠ 0) (h : ℝ) :
    kernel G E τ h = fun x => G (x - (τ * h) • gradient (fun y => E y / τ) x) (2 * (τ * h)) := by
  funext x
  unfold kernel
  rw [← kernel_mean_eq hE hτ h x]
  congr 1
  ring

/-- The law of the K-th iterate of the chain with kernel `P` started at `ν`: `ν P^K`
(definition C7, `Measure.bind` iterated). -/
noncomputable def lawIter (P : X → MeasureTheory.Measure X) (ν : MeasureTheory.Measure X) (K : ℕ) :
    MeasureTheory.Measure X :=
  (fun μ => μ.bind P)^[K] ν

/-- Lemma S2 (vi) at the level of algebra: equal kernels give equal K-th laws for every K. -/
lemma lawIter_congr {P P' : X → MeasureTheory.Measure X} (h : P = P')
    (ν : MeasureTheory.Measure X) (K : ℕ) : lawIter P ν K = lawIter P' ν K := by
  rw [h]

/-- The K-th law is obtained by one more kernel step from the (K−1)-st. -/
lemma lawIter_succ (P : X → MeasureTheory.Measure X) (ν : MeasureTheory.Measure X) (K : ℕ) :
    lawIter P ν (K + 1) = (lawIter P ν K).bind P := by
  unfold lawIter
  rw [Function.iterate_succ_apply']

/-- Lemma S2 (vi) applied to the word: the K-th law of the word at `(E, τ, h)` is the K-th law of
Dalalyan's chain for `(E/τ, τ h)` (same initial law). -/
lemma lawIter_word_eq (G : X → ℝ → MeasureTheory.Measure X) {E : X → ℝ}
    (hE : Differentiable ℝ E) {τ : ℝ} (hτ : τ ≠ 0) (h : ℝ) (ν : MeasureTheory.Measure X) (K : ℕ) :
    lawIter (kernel G E τ h) ν K
      = lawIter (fun x => G (x - (τ * h) • gradient (fun y => E y / τ) x) (2 * (τ * h))) ν K :=
  lawIter_congr (kernel_eq G hE hτ h) ν K

end C

/-! ## Section E: Lemma S4, the count and the bias floor (L-E) -/

section E

/-- The bound after `K` steps, `Ψ_K = q^K r₀ + bias`. -/
def Psi (q r0 b : ℝ) (K : ℕ) : ℝ := q ^ K * r0 + b

/-- Lemma S4 (i): `q = 1 − m h ∈ [0, 1)` for `0 < m ≤ L`, `0 < h ≤ 2/(m+L)`. -/
lemma q_mem {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hhL : h ≤ 2 / (m + L)) :
    0 ≤ 1 - m * h ∧ 1 - m * h < 1 := by
  have hL : 0 < L := hm.trans_le hmL
  have hpos : 0 < m + L := by linarith
  have h1 : h * (m + L) ≤ 2 := by
    have := (le_div_iff₀ hpos).1 hhL
    exact this
  refine ⟨?_, by nlinarith [mul_pos hm hh]⟩
  nlinarith [mul_pos hm hh]

/-- Lemma S4 (ii): `Ψ_K` is non-increasing in `K` (for `q ∈ [0, 1]`, `r₀ ≥ 0`). -/
lemma Psi_antitone {q r0 b : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 ≤ r0) :
    Antitone (Psi q r0 b) := by
  apply antitone_nat_of_succ_le
  intro K
  unfold Psi
  have : q ^ (K + 1) ≤ q ^ K := pow_le_pow_of_le_one hq0 hq1 (Nat.le_succ K)
  nlinarith

/-- Lemma S4 (ii): `Ψ_K ≥ bias` for all `K` (the floor). -/
lemma Psi_ge {q r0 b : ℝ} (hq0 : 0 ≤ q) (hr : 0 ≤ r0) (K : ℕ) : b ≤ Psi q r0 b K := by
  unfold Psi
  have : 0 ≤ q ^ K * r0 := mul_nonneg (pow_nonneg hq0 K) hr
  linarith

/-- Lemma S4 (ii): `Ψ_K → bias`. -/
lemma Psi_tendsto {q r0 b : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Tendsto (Psi q r0 b) atTop (𝓝 b) := by
  have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const r0).add_const b
  show Tendsto (fun K : ℕ => q ^ K * r0 + b) atTop (𝓝 b)
  simpa using this

/-- The floor remark of Theorem S(c): for `ε < bias`, no `K` has `Ψ_K ≤ ε`. (At `ε = bias`
the bound of (b) is `≤ ε` only when `q^K r₀ = 0`, i.e. `q = 0`, `K ≥ 1`; see the report.) -/
lemma Psi_gt_of_lt_bias {q r0 b ε : ℝ} (hq0 : 0 ≤ q) (hr : 0 ≤ r0) (hε : ε < b) (K : ℕ) :
    ε < Psi q r0 b K :=
  lt_of_lt_of_le hε (Psi_ge hq0 hr K)

/-- The set `{K | q^K r₀ ≤ c}` of Lemma S4 (iii) and its least element `K_ε` (with `c = ε − bias`). -/
noncomputable def Keps (q r0 c : ℝ) : ℕ := sInf {K : ℕ | q ^ K * r0 ≤ c}

/-- Lemma S4 (iii): the set is nonempty for `q ∈ [0, 1)`, `r₀ > 0`, `c > 0`. -/
lemma Keps_nonempty {q r0 c : ℝ} (hq1 : q < 1) (_hq0 : 0 ≤ q) (hr : 0 < r0) (hc : 0 < c) :
    {K : ℕ | q ^ K * r0 ≤ c}.Nonempty := by
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hc hr) hq1
  refine ⟨n, ?_⟩
  show q ^ n * r0 ≤ c
  have := (lt_div_iff₀ hr).1 hn
  exact this.le

/-- Lemma S4 (iii): `K_ε` belongs to the set. -/
lemma Keps_mem {q r0 c : ℝ} (hq1 : q < 1) (hq0 : 0 ≤ q) (hr : 0 < r0) (hc : 0 < c) :
    q ^ Keps q r0 c * r0 ≤ c :=
  Nat.sInf_mem (Keps_nonempty hq1 hq0 hr hc)

/-- Lemma S4 (iii): `K_ε` is the least element. -/
lemma Keps_le_of_mem {q r0 c : ℝ} {K : ℕ} (hK : q ^ K * r0 ≤ c) : Keps q r0 c ≤ K :=
  Nat.sInf_le hK

/-- Lemma S4 (iii): the set is upward closed (`q ∈ [0, 1]`, `r₀ ≥ 0`). -/
lemma Keps_upward {q r0 c : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hr : 0 ≤ r0) {K K' : ℕ}
    (hK : q ^ K * r0 ≤ c) (hKK : K ≤ K') : q ^ K' * r0 ≤ c :=
  le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hq0 hq1 hKK) hr) hK

/-- Lemma S4 (iii), first case: `K_ε = 0` if `r₀ ≤ c`. -/
lemma Keps_zero {q r0 c : ℝ} (h : r0 ≤ c) : Keps q r0 c = 0 :=
  Nat.eq_zero_of_le_zero (Keps_le_of_mem (K := 0) (by simpa using h))

/-- Lemma S4 (iii), second case: `K_ε = 1` if `q = 0` and `r₀ > c > 0`. -/
lemma Keps_one {r0 c : ℝ} (hr : c < r0) (hc : 0 < c) : Keps 0 r0 c = 1 := by
  have h1 : (0 : ℝ) ^ 1 * r0 ≤ c := by simpa using hc.le
  have hle : Keps 0 r0 c ≤ 1 := Keps_le_of_mem h1
  have hne : Keps 0 r0 c ≠ 0 := by
    intro h0
    have hmem := Keps_mem (q := 0) (r0 := r0) (c := c) (by norm_num) le_rfl (hc.trans hr) hc
    rw [h0] at hmem
    simp at hmem
    linarith
  omega

/-- Tool: for `q ∈ (0,1)` and `0 < c < r₀`, `q^K r₀ ≤ c ⟺ log(r₀/c) / log(1/q) ≤ K`. -/
lemma pow_le_iff_log {q r0 c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hr : 0 < r0) (hc : 0 < c) (K : ℕ) :
    q ^ K * r0 ≤ c ↔ Real.log (r0 / c) / Real.log (1 / q) ≤ K := by
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  rw [div_le_iff₀ hlq]
  have e : (K : ℝ) * Real.log (1 / q) = Real.log ((1 / q) ^ K) := by
    rw [Real.log_pow]
  rw [e, Real.log_le_log_iff (div_pos hr hc) (pow_pos (by positivity) K), div_le_iff₀ hc,
    one_div, inv_pow, le_inv_mul_iff₀ (pow_pos hq0 K)]

/-- Lemma S4 (iii), third case: for `q ∈ (0,1)` and `0 < c < r₀`,
`K_ε = ⌈ log(r₀/c) / log(1/q) ⌉`. -/
lemma Keps_log {q r0 c : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hr : 0 < r0) (hc : 0 < c) :
    Keps q r0 c = ⌈Real.log (r0 / c) / Real.log (1 / q)⌉₊ := by
  have hiff := pow_le_iff_log hq0 hq1 hr hc
  apply le_antisymm
  · apply Keps_le_of_mem
    rw [hiff]
    exact Nat.le_ceil _
  · have hmem := Keps_mem hq1 hq0.le hr hc
    rw [hiff] at hmem
    exact Nat.ceil_le.2 hmem

/-- Core of the logarithmic upper bound: for `0 < a = m h ≤ 1`, `r₀, c > 0`, every natural
`K ≥ log(r₀/c)/a` has `(1 − a)^K r₀ ≤ c` (from `1 − a ≤ e^{−a}`, i.e. `log y ≤ y − 1`). -/
lemma pow_le_of_log_le {a r0 c : ℝ} (ha1 : a ≤ 1) (ha0 : 0 < a) (hr : 0 < r0) (hc : 0 < c) (K : ℕ)
    (hK : Real.log (r0 / c) / a ≤ K) : (1 - a) ^ K * r0 ≤ c := by
  have h1 : (1 - a) ^ K ≤ Real.exp (-a) ^ K :=
    pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg a) K
  have h2 : Real.exp (-a) ^ K = Real.exp (-(a * K)) := by
    rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : Real.log (r0 / c) ≤ a * K := by
    rwa [div_le_iff₀ ha0, mul_comm] at hK
  have h4 : Real.exp (-(a * K)) ≤ c / r0 := by
    have : Real.exp (-(a * K)) ≤ Real.exp (-Real.log (r0 / c)) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_neg (Real.log (r0 / c)), Real.exp_log (div_pos hr hc), inv_div] at this
    exact this
  calc (1 - a) ^ K * r0 ≤ (c / r0) * r0 := by
        apply mul_le_mul_of_nonneg_right _ hr.le
        exact h1.trans (h2.le.trans h4)
    _ = c := by field_simp

/-- Lemma S4 (iii), the logarithmic upper bound, natural-number form: for `0 < m h ≤ 1`,
`q = 1 − m h`, `K_ε ≤ ⌈log(r₀/c)/(m h)⌉`. (Proved for all cases at once, `q = 0` included.) -/
lemma Keps_le_ceil {m h r0 c : ℝ} (hmh0 : 0 < m * h) (hmh1 : m * h ≤ 1) (hr : 0 < r0)
    (hc : 0 < c) : Keps (1 - m * h) r0 c ≤ ⌈Real.log (r0 / c) / (m * h)⌉₊ :=
  Keps_le_of_mem (pow_le_of_log_le hmh1 hmh0 hr hc _ (Nat.le_ceil _))

/-- Lemma S4 (iii), the stated form: `K_ε ≤ max{0, ⌈log(r₀/(ε − bias))/(m h)⌉}` in `ℤ`. -/
lemma Keps_le_int_ceil {m h r0 c : ℝ} (hmh0 : 0 < m * h) (hmh1 : m * h ≤ 1) (hr : 0 < r0)
    (hc : 0 < c) :
    (Keps (1 - m * h) r0 c : ℤ) ≤ max 0 ⌈Real.log (r0 / c) / (m * h)⌉ := by
  have h1 := Keps_le_ceil (m := m) (h := h) hmh0 hmh1 hr hc
  have h2 : ((⌈Real.log (r0 / c) / (m * h)⌉₊ : ℕ) : ℤ)
      = max 0 ⌈Real.log (r0 / c) / (m * h)⌉ := by
    rw [← Int.ceil_toNat, Int.toNat_eq_max, max_comm]
  rw [← h2]
  exact_mod_cast h1

/-- The comparison loop of Lemma S4 (iv): start from `x = r₀` and counter `0`, test `x ≤ c`, else
multiply `x` by `q` and increment the counter. `fuel` bounds the number of tests. Uses only
multiplication and comparison. -/
noncomputable def loopAux (q c : ℝ) : ℕ → ℝ → ℕ → ℕ
  | 0, _, k => k
  | n + 1, x, k => if x ≤ c then k else loopAux q c n (q * x) (k + 1)

/-- Lemma S4 (iv): for fuel `n ≥ k̄ − k` the loop returns the least index not earlier than `k`
at which the test succeeds; here stated for the invariant "all `j < k` failed". -/
lemma loopAux_eq {q r0 c : ℝ} (hq1 : q < 1) (hq0 : 0 ≤ q) (hr : 0 < r0) (hc : 0 < c) :
    ∀ (n k : ℕ), (∀ j < k, c < q ^ j * r0) → Keps q r0 c ≤ k + n →
      loopAux q c n (q ^ k * r0) k = Keps q r0 c := by
  have hmem := Keps_mem hq1 hq0 hr hc
  intro n
  induction n with
  | zero =>
    intro k hk hle
    have hge : k ≤ Keps q r0 c := by
      by_contra hlt
      push Not at hlt
      exact absurd (hk _ hlt) (not_lt.2 hmem)
    simp only [loopAux]
    omega
  | succ n ih =>
    intro k hk hle
    simp only [loopAux]
    split_ifs with hx
    · have hge : k ≤ Keps q r0 c := by
        by_contra hlt
        push Not at hlt
        exact absurd (hk _ hlt) (not_lt.2 hmem)
      have := Keps_le_of_mem hx
      omega
    · have hx' : c < q ^ k * r0 := not_le.1 hx
      have := ih (k + 1) (fun j hj => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
        · exact hk j h
        · subst h; exact hx') (by omega)
      rw [← this]
      congr 1
      rw [pow_succ']
      ring_nf

/-- Lemma S4 (iv): with fuel `n ≥ K_ε` the comparison loop started at `r₀` returns `K_ε`. -/
lemma loop_eq_Keps {q r0 c : ℝ} (hq1 : q < 1) (hq0 : 0 ≤ q) (hr : 0 < r0) (hc : 0 < c) (n : ℕ)
    (hn : Keps q r0 c ≤ n) : loopAux q c n r0 0 = Keps q r0 c := by
  have := loopAux_eq hq1 hq0 hr hc n 0 (fun j hj => absurd hj (Nat.not_lt_zero _))
    (by simpa using hn)
  simpa using this

/-- Lemma S4 (v), first half: for `h > 0`, `c ≥ 0`, `0 < m ≤ L`, `τ, d > 0`,
`bias(h) ≤ c ⟺ h ≤ (c m)² / (1.82² L² τ d)`. -/
lemma bias_le_iff {m L τ h c : ℝ} {d : ℕ} (hm : 0 < m) (hL : 0 < L) (hτ : 0 < τ) (hd : 0 < d)
    (_hh : 0 < h) (hc : 0 ≤ c) :
    bias τ d m L h ≤ c ↔ h ≤ (c * m) ^ 2 / (1.82 ^ 2 * L ^ 2 * τ * d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hk : 0 < (1.82 : ℝ) * (L / m) := by positivity
  unfold bias
  rw [mul_comm, ← le_div_iff₀ hk]
  rw [Real.sqrt_le_left (by positivity)]
  have e : (c / (1.82 * (L / m))) ^ 2 = (c * m) ^ 2 / (1.82 ^ 2 * L ^ 2) := by
    field_simp
  rw [e, le_div_iff₀ (by positivity), le_div_iff₀ (by positivity)]
  have e2 : τ * h * d * (1.82 ^ 2 * L ^ 2) = h * (1.82 ^ 2 * L ^ 2 * τ * d) := by ring
  rw [e2]

/-- Lemma S4 (v): the step `h_θ(ε) = min{2/(m+L), (θ ε m)²/(1.82² L² τ d)}`. -/
noncomputable def hTheta (m L τ : ℝ) (d : ℕ) (ε θ : ℝ) : ℝ :=
  min (2 / (m + L)) ((θ * ε * m) ^ 2 / (1.82 ^ 2 * L ^ 2 * τ * d))

/-- Lemma S4 (v): `h_θ(ε) > 0`. -/
lemma hTheta_pos {m L τ ε θ : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ) (hd : 0 < d)
    (hε : 0 < ε) (hθ : 0 < θ) : 0 < hTheta m L τ d ε θ := by
  have hL : 0 < L := hm.trans_le hmL
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold hTheta
  apply lt_min (by positivity) (by positivity)

/-- Lemma S4 (v): `h_θ(ε)` is admissible, `h_θ(ε) ≤ 2/(m+L)`. -/
lemma hTheta_admissible (m L τ : ℝ) (d : ℕ) (ε θ : ℝ) : hTheta m L τ d ε θ ≤ 2 / (m + L) :=
  min_le_left _ _

/-- Lemma S4 (v): `bias(h_θ(ε)) ≤ θ ε`. -/
lemma bias_hTheta_le {m L τ ε θ : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ) (hd : 0 < d)
    (hε : 0 < ε) (hθ : 0 < θ) : bias τ d m L (hTheta m L τ d ε θ) ≤ θ * ε := by
  have hL : 0 < L := hm.trans_le hmL
  rw [bias_le_iff hm hL hτ hd (hTheta_pos hm hmL hτ hd hε hθ) (by positivity)]
  exact min_le_right _ _

/-- Lemma S4 (v), the count: for `θ ∈ (0,1)`, `ε > 0`, `h = h_θ(ε)`, `q = 1 − m h`, `r₀ > 0`, every
natural `K ≥ log(r₀/((1−θ)ε))/(m h)` has `Ψ_K = q^K r₀ + bias(h) ≤ ε`. (`K ≥ max{0, ·}` is the same
as `K ≥ ·` for a natural `K`.) -/
lemma Psi_le_of_step_rule {m L τ ε θ r0 : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ)
    (hd : 0 < d) (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1) (hr : 0 < r0) (K : ℕ)
    (hK : Real.log (r0 / ((1 - θ) * ε)) / (m * hTheta m L τ d ε θ) ≤ K) :
    Psi (1 - m * hTheta m L τ d ε θ) r0 (bias τ d m L (hTheta m L τ d ε θ)) K ≤ ε := by
  have hh : 0 < hTheta m L τ d ε θ := hTheta_pos hm hmL hτ hd hε hθ
  have hq := q_mem hm hmL hh (hTheta_admissible m L τ d ε θ)
  have hmh0 : 0 < m * hTheta m L τ d ε θ := mul_pos hm hh
  have hc : 0 < (1 - θ) * ε := mul_pos (by linarith) hε
  have h1 := pow_le_of_log_le (by linarith [hq.1]) hmh0 hr hc K hK
  have h2 := bias_hTheta_le hm hmL hτ hd hε hθ
  unfold Psi
  nlinarith

end E

/-! ## Section G: assembly of Theorem S (b), (c) from the named hypotheses -/

section Assembly

/-- The computed start bound of Theorem S(b): `r₀ = ‖∇E(x₀)‖/m + (τ d/m)^{1/2}`, with
`g0` standing for `‖∇E(x₀)‖`. -/
noncomputable def r0 (g0 τ : ℝ) (d : ℕ) (m : ℝ) : ℝ := g0 / m + Real.sqrt (τ * d / m)

/-- `r₀ > 0` (in Theorem S, `r₀ ≥ (τ d/m)^{1/2} > 0`). -/
lemma r0_pos {g0 τ m : ℝ} {d : ℕ} (hm : 0 < m) (hτ : 0 < τ) (hd : 0 < d) (hg : 0 ≤ g0) :
    0 < r0 g0 τ d m := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold r0
  have : 0 < Real.sqrt (τ * d / m) := Real.sqrt_pos.2 (by positivity)
  have : 0 ≤ g0 / m := by positivity
  linarith

variable {Law : Type*}

/-- NAMED HYPOTHESIS (Theorem S(a), verbatim; [CLASSICAL] Dalalyan, arXiv:1704.04752v2, Thm 1(a), p. 3,
after the identifications of Lemmas S1, S2): for every admissible initial law `ν₀` (finite second
moment, H-law) and every `K`, `W2(ν₀ P_h^K, π_τ) ≤ (1 − m h)^K W2(ν₀, π_τ) + bias(h)`.
`W2`, `step` (`ν ↦ ν P_h`), `Adm` and `π_τ` are abstract. -/
def DalalyanThm1a (W2 : Law → Law → ℝ) (step : Law → Law) (Adm : Law → Prop) (πτ : Law)
    (m L τ : ℝ) (d : ℕ) (h : ℝ) : Prop :=
  ∀ ν₀ : Law, Adm ν₀ → ∀ K : ℕ,
    W2 (step^[K] ν₀) πτ ≤ (1 - m * h) ^ K * W2 ν₀ πτ + bias τ d m L h

/-- Lemma S3 (ii) as the real-inequality chain: the Dirac-start bound
`W2(δ, π_τ) ≤ ‖x₀ − x*‖ + (τ d/m)^{1/2}` from the three named classical hypotheses
`hDiracCoupling` (`W2(δ,π)² = A`, Dalalyan display (4)), `hSecondMoment` (`M2 ≤ τ d/m`,
Durmus–Moulines Prop. 1(ii)) and `hMinkowski` (`√A ≤ ‖x₀ − x*‖ + √M2`), with `W2 ≥ 0`. -/
lemma diracStart {W0 A M2 dist0 τ m : ℝ} {d : ℕ} (hW0 : 0 ≤ W0)
    (hDiracCoupling : W0 ^ 2 = A) (hSecondMoment : M2 ≤ τ * d / m)
    (hMinkowski : Real.sqrt A ≤ dist0 + Real.sqrt M2) :
    W0 ≤ dist0 + Real.sqrt (τ * d / m) := by
  have h1 : Real.sqrt A = W0 := by rw [← hDiracCoupling]; exact Real.sqrt_sq hW0
  have h2 : Real.sqrt M2 ≤ Real.sqrt (τ * d / m) := Real.sqrt_le_sqrt hSecondMoment
  linarith

/-- Theorem S(b), glue. Hypotheses: (H-curv)/(H-word) numbers `0 < m ≤ L`, `τ > 0`, `d ≥ 1`,
`0 < h ≤ 2/(m+L)`; the named hypotheses `hDalalyan`, `hDiracCoupling`, `hSecondMoment`,
`hMinkowski` and the landed `hDist : ‖x₀ − x*‖ ≤ ‖∇E(x₀)‖/m` (`dist0`, `g0`). Conclusion:
`W2(δ, π_τ) ≤ ‖x₀ − x*‖ + (τ d/m)^{1/2} ≤ r₀` and `W2(δ P_h^K, π_τ) ≤ (1 − m h)^K r₀ + bias(h)`
for every `K`. -/
theorem theoremS_b (W2 : Law → Law → ℝ) (step : Law → Law) (Adm : Law → Prop) (πτ δ : Law)
    {m L τ h : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (_hτ : 0 < τ) (_hd : 0 < d) (hh : 0 < h)
    (hhL : h ≤ 2 / (m + L))
    (hDalalyan : DalalyanThm1a W2 step Adm πτ m L τ d h) (hδ : Adm δ) (hW0 : 0 ≤ W2 δ πτ)
    {A M2 dist0 g0 : ℝ}
    (hDiracCoupling : W2 δ πτ ^ 2 = A) (hSecondMoment : M2 ≤ τ * d / m)
    (hMinkowski : Real.sqrt A ≤ dist0 + Real.sqrt M2) (hDist : dist0 ≤ g0 / m) :
    W2 δ πτ ≤ dist0 + Real.sqrt (τ * d / m) ∧ dist0 + Real.sqrt (τ * d / m) ≤ r0 g0 τ d m ∧
      ∀ K : ℕ, W2 (step^[K] δ) πτ ≤ (1 - m * h) ^ K * r0 g0 τ d m + bias τ d m L h := by
  have hstart := diracStart (d := d) hW0 hDiracCoupling hSecondMoment hMinkowski
  have hr : dist0 + Real.sqrt (τ * d / m) ≤ r0 g0 τ d m := by
    unfold r0; linarith
  refine ⟨hstart, hr, fun K => ?_⟩
  have hq := q_mem hm hmL hh hhL
  have hpow : 0 ≤ (1 - m * h) ^ K := pow_nonneg hq.1 K
  have h1 := hDalalyan δ hδ K
  have h2 : W2 δ πτ ≤ r0 g0 τ d m := hstart.trans hr
  nlinarith

/-- Theorem S(c), glue (count with the bias floor). With the hypotheses of `theoremS_b`, `g0 ≥ 0`,
and `ε > bias(h)`: every `K ≥ K_ε` (the least `K` with `q^K r₀ ≤ ε − bias`) has
`W2(δ P_h^K, π_τ) ≤ ε`; `K_ε ≤ max{0, ⌈log(r₀/(ε − bias))/(m h)⌉}`; and the comparison loop with
`K_ε` tests returns `K_ε`. -/
theorem theoremS_c (W2 : Law → Law → ℝ) (step : Law → Law) (Adm : Law → Prop) (πτ δ : Law)
    {m L τ h ε : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ) (hd : 0 < d) (hh : 0 < h)
    (hhL : h ≤ 2 / (m + L))
    (hDalalyan : DalalyanThm1a W2 step Adm πτ m L τ d h) (hδ : Adm δ) (hW0 : 0 ≤ W2 δ πτ)
    {A M2 dist0 g0 : ℝ} (hg0 : 0 ≤ g0)
    (hDiracCoupling : W2 δ πτ ^ 2 = A) (hSecondMoment : M2 ≤ τ * d / m)
    (hMinkowski : Real.sqrt A ≤ dist0 + Real.sqrt M2) (hDist : dist0 ≤ g0 / m)
    (hε : bias τ d m L h < ε) :
    (∀ K : ℕ, Keps (1 - m * h) (r0 g0 τ d m) (ε - bias τ d m L h) ≤ K →
        W2 (step^[K] δ) πτ ≤ ε) ∧
    ((Keps (1 - m * h) (r0 g0 τ d m) (ε - bias τ d m L h) : ℤ)
        ≤ max 0 ⌈Real.log (r0 g0 τ d m / (ε - bias τ d m L h)) / (m * h)⌉) ∧
    (∀ n : ℕ, Keps (1 - m * h) (r0 g0 τ d m) (ε - bias τ d m L h) ≤ n →
        loopAux (1 - m * h) (ε - bias τ d m L h) n (r0 g0 τ d m) 0
          = Keps (1 - m * h) (r0 g0 τ d m) (ε - bias τ d m L h)) := by
  have hq := q_mem hm hmL hh hhL
  have hr := r0_pos (g0 := g0) hm hτ hd hg0
  have hc : 0 < ε - bias τ d m L h := by linarith
  have hb := (theoremS_b W2 step Adm πτ δ hm hmL hτ hd hh hhL hDalalyan hδ hW0 hDiracCoupling
    hSecondMoment hMinkowski hDist).2.2
  have hq1 : m * h ≤ 1 := by linarith [hq.1]
  refine ⟨fun K hK => ?_, Keps_le_int_ceil (mul_pos hm hh) hq1 hr hc, fun n hn =>
    loop_eq_Keps hq.2 hq.1 hr hc n hn⟩
  have hmem := Keps_mem hq.2 hq.1 hr hc
  have hup := Keps_upward hq.1 (by linarith [hq.2]) hr.le hmem hK
  have := hb K
  linarith

/-- Theorem S(c), the step prescribed from the target accuracy: for `ε > 0`, `θ ∈ (0,1)` and
`h = h_θ(ε)` (admissible by Lemma S4(v)), `bias(h) ≤ θ ε` and every `K ≥ log(r₀/((1−θ)ε))/(m h)`
has `W2(δ P_h^K, π_τ) ≤ ε`. The named Dalalyan hypothesis is taken at `h = h_θ(ε)`. -/
theorem theoremS_step_rule (W2 : Law → Law → ℝ) (step : Law → Law) (Adm : Law → Prop)
    (πτ δ : Law) {m L τ ε θ : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hτ : 0 < τ) (hd : 0 < d)
    (hε : 0 < ε) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hDalalyan : DalalyanThm1a W2 step Adm πτ m L τ d (hTheta m L τ d ε θ)) (hδ : Adm δ)
    (hW0 : 0 ≤ W2 δ πτ) {A M2 dist0 g0 : ℝ} (hg0 : 0 ≤ g0)
    (hDiracCoupling : W2 δ πτ ^ 2 = A) (hSecondMoment : M2 ≤ τ * d / m)
    (hMinkowski : Real.sqrt A ≤ dist0 + Real.sqrt M2) (hDist : dist0 ≤ g0 / m) :
    bias τ d m L (hTheta m L τ d ε θ) ≤ θ * ε ∧
    ∀ K : ℕ, Real.log (r0 g0 τ d m / ((1 - θ) * ε)) / (m * hTheta m L τ d ε θ) ≤ K →
      W2 (step^[K] δ) πτ ≤ ε := by
  have hh := hTheta_pos hm hmL hτ hd hε hθ
  have hb := (theoremS_b W2 step Adm πτ δ hm hmL hτ hd hh (hTheta_admissible m L τ d ε θ)
    hDalalyan hδ hW0 hDiracCoupling hSecondMoment hMinkowski hDist).2.2
  have hr := r0_pos (g0 := g0) hm hτ hd hg0
  refine ⟨bias_hTheta_le hm hmL hτ hd hε hθ, fun K hK => ?_⟩
  have := Psi_le_of_step_rule hm hmL hτ hd hε hθ hθ1 hr K hK
  unfold Psi at this
  exact (hb K).trans this

end Assembly

end OCF.S1

#print axioms OCF.S1.modC_mono
#print axioms OCF.S1.modC_max
#print axioms OCF.S1.m_le_betaHat
#print axioms OCF.S1.betaHat_pos
#print axioms OCF.S1.dal1a_div
#print axioms OCF.S1.dal1b_div
#print axioms OCF.S1.step_range_iff
#print axioms OCF.S1.step_lt_two_div
#print axioms OCF.S1.bias_rescaled
#print axioms OCF.S1.lawIter_word_eq
#print axioms OCF.S1.q_mem
#print axioms OCF.S1.Psi_antitone
#print axioms OCF.S1.Psi_tendsto
#print axioms OCF.S1.Keps_one
#print axioms OCF.S1.Keps_log
#print axioms OCF.S1.Keps_le_int_ceil
#print axioms OCF.S1.loop_eq_Keps
#print axioms OCF.S1.bias_le_iff
#print axioms OCF.S1.Psi_le_of_step_rule
#print axioms OCF.S1.theoremS_b
#print axioms OCF.S1.theoremS_c
#print axioms OCF.S1.theoremS_step_rule

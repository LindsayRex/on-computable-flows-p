/-
C1 (the conservative-word certificate) — the Lean target of section 14 of the adjudicated dossier:
the new algebra of Theorem C for the heavy-ball word  W = Φ^SV_1 ∘ D^{1−β,M'}_Kin  (a Störmer–Verlet
step with V = E followed by damping of the momentum) on a smooth declaration with a COMPUTED pair
(m, L), at the tuning  α ∈ (0, 1/L],  β = √((1−αm)(1−αL)),  q = 1 − αm.

Source of truth: project_plan/doing/proof_audits/C1_conservative_word/01_derivation.md (adjudicated
stage 3, 2026-10-19): section 1 (Theorem C, hypotheses H-tune, H-word, H-start), section 4 (Lemma C2),
section 5 (Lemma C3), section 6 (Lemma C4), section 7 (Lemmas C5, C6), section 14 (Lean target);
rulings in 03_adjudication.md (finding 1: Lemma C4 is an admissible gap-fill, one chain including
α = 1/L; finding 5: Lemma C2 (iii) and the region-(25) inequality are dossier-only and are NOT
formalised; findings 15, 22: Remarks C4a, C4b, C5 are dossier-only, not formalised).

DEFINITIONAL MAP (dossier symbol — Lean name):
* ℝᵈ — a real inner product space `X` (complete, because Mathlib's `gradient` needs it);
  E ∈ C¹ — `E : X → ℝ`, `Differentiable ℝ E`; ∇E — `gradient E`.
* (1a) first-order m-strong convexity (Lemma C1 output) — S1's `OCF.S1.Dal1a E m`;
  (1b) L-Lipschitz gradient — G3's `OCF.G3.LipGrad E L`; the unique minimiser x*, E* := E(x*) —
  `xs : X` with `hmin : ∀ y, E xs ≤ E y` and `E xs` (uniqueness is `min_unique`).
  The Lemma C1 bridge itself (declaration ↦ (1a), (1b), x*, m ≤ L) is the landed S1 bridge and is
  NOT restated: its outputs are hypotheses `h1a`, `h1b`, `hmin`, `hmL`, exactly as S1StochasticWord does.
* (H-tune) α, β, q, s, c_β, b — `α`, `hbBeta m L α`, `hbQ m α`, `hbS α β` (= 2α/(1+β)),
  `cBeta L α β` (= 2α(1−αL)/(1+β)²), `bW L α` (= (1−αL)/(2α)).
* S(x, x') = (x − α∇E(x) + β(x − x'), x) — E0's `OCF.E0.hbStep E α β (x, x')`.
* The word W = Φ^SV_1 ∘ D^{1−β,M'}_Kin — `hbWord E α β GK`  (`sv (gradient E) (MpHBinv s) 1` after
  `dstep (1−β) (MprInv s) GK`), with `GK` the phase-space gradient of Kin(v) = (s/2)‖v‖²
  (hypothesis `hGK : IsGradPS …`, the DEFINITION of GK; satisfiable by E0's `isGradPS_kinS`).
* χ(x, x') = (x, (x − x')/s − ½∇E(x)) and χ⁻¹ — E0's `chiHB E s`, `chiHBinv E s`.
* x_{-1} := x_0, x_{j+1} = x_j − α∇E(x_j) + β(x_j − x_{j−1}) — `hbIter E α β x0 K`
  (= S^K (x_0, x_0), the pair (x_K, x_{K−1})), `hbX E α β x0 K` (its first component);
  recursion: `hbX_zero`, `hbX_one`, `hbX_add_two`, `hbIter_succ`.
* z_0 = χ(x_0, x_0) — `z0 E α β x0`; (x_K, v_K) = W^K z_0 — `(hbWord E α β GK)^[K] (z0 E α β x0)`,
  `xK E α β GK x0 K` its first component.
* Λ(x, x') = E(x) − E* + b‖x − x'‖² — `Lam E Es b x x'`  (on pairs: `LamP E Es b z`);
  Λ_W(x, v) = E(x) − E* + c_β‖v + ½∇E(x)‖² — `LamW E Es c z`  (`Es = E xs`).
* r_0 = ‖∇E(x_0)‖/m — `r0C E m x0`.
* K_ε = least K ≥ 0 with q^K r_0² ≤ ε² — S1's `OCF.S1.Keps q (r0^2) (ε^2)` (`sInf`); the comparison
  loop — S1's `OCF.S1.loopAux`. 0^0 = 1 is Lean's convention. q^{K/2} — `q ^ ((K : ℝ) / 2)`.

NAMED HYPOTHESES (classical inputs, per the house pattern: hypotheses of the statements that use them,
never global axioms; each is stated as the cited source states it):
* `hBeck : Beck57 E L` — [CLASSICAL] Beck, First-Order Methods in Optimization (2017), Lemma 5.7
  (descent lemma), p. 109: for f ∈ C^{1,1}_L(ℝⁿ), f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)‖x − y‖².
  (Page-verified by the librarian, dossier row K3.)
* `hBubeck : Bubeck69 E m xs` — [CLASSICAL] Bubeck, Convex Optimization: Algorithms and Complexity
  (FnT 2015), Lemma 6.9, p. 341: α-strongly convex (in the sense of (3.13), p. 276, `StrongConv313`)
  with minimiser x* gives f(x) − f(x*) ≤ ‖∇f(x)‖²/(2α) (Euclidean case). (Page-verified, row K4.)
* BOTH are in fact discharged in this file, as a consistency check that they are not vacuous or false
  in this formalisation: `beck57_holds` (from A1's segment lemma) and `bubeck69_holds` (from (1a), five
  lines), and `theoremC_closed` is Theorem C with no classical hypothesis. The theorems proper keep the
  hypotheses named, as the dossier tags them classical (cited, not derived, in the paper).
* `hGK` — not classical: the definition of GK as the phase-space gradient of Kin, as in E0's `hb_word`.
* `hb_word` (E0MethodWords.lean) is POINTED AT, not restated: `word_chi` is its third clause and
  `lamW_eq_lam_chiinv`, `lamW_decay` use its first two (χ is a bijection with inverse `chiHBinv`).
* The start bound `‖x_0 − x*‖ ≤ ‖∇E(x_0)‖/m` is the landed thm:soundness(c) (G3SoundnessProx.lean,
  `regimeAP_of`, stated for the proximal setting). Here, with no non-smooth term, it is not imported:
  it is `dist_chain` (iii), proved from (1a), `hmin` and the gradient-dominance hypothesis (the dossier's
  Lemma C5 (iv), "self-contained"); the two agree.

COVERAGE (dossier item — Lean name), all FORMALISED (statement + proof, no sorry):
* Lemma C2 (i), (ii), (iv) and the first equality of (v): `beta_nonneg`, `beta_lt_one` (hence
  β ∈ (−1, 1): `beta_gt_neg_one`), `beta_eq_zero_iff` (β = 0 ⟺ αL = 1), `q_nonneg`, `q_lt_one`,
  `q_eq_zero_iff` (q = 0 ⟺ m = L ∧ α = 1/L), `q_ge` (q ≥ 1 − m/L), `beta_sq` (β² = q(1−αL)),
  `cBeta_nonneg`, `bW_nonneg`; degenerate case m = L: `beta_of_eq` (β = 1 − αm).
  NOT formalised (dossier-only by ruling): C2 (iii) α < 2/L, region (25) membership.
* Lemma C3 (ii), (iii): `hbIter_succ`, `hbX_zero`, `hbX_one`, `hbX_add_two`, `word_iter`
  (W^K χ(x_0, x_0) = χ(S^K(x_0, x_0))), `xK_eq_hbX`, `chi_diag` (z_0 = (x_0, −½∇E(x_0))),
  `lamW_chi` (Λ_W ∘ χ = Λ, i.e. Lemma C3(iii)), `lamW_eq_lam_chiinv` (Λ_W = Λ ∘ χ⁻¹).
  Lemma C3 (i) is hb_word (pointer): `word_chi`.
* Lemma C4 steps 1–5 (the gap-filled one-step chain, α = 1/L included): `lam_step`
  (Λ(S(x,x')) ≤ q Λ(x,x')); step 6, the phase-space form: `lamW_decay` (Λ_W(Wz) ≤ qΛ_W(z) ∀z);
  iterates: `lam_iter`, `lamW_iter`.
* Theorem C (a): `theoremC_a`.
* Lemma C5 (i)–(iv): `dist_chain`; Theorem C (b): `theoremC_b`.
* Lemma C6 (i), (iii) and the loop (ii), the ceiling bound, the r_0 = 0 case; Theorem C (c):
  `theoremC_c` (using S1's `Keps_mem`, `Keps_le_of_mem`, `Keps_upward`, `Keps_le_int_ceil`,
  `loop_eq_Keps`).
* Assembly with the classical hypotheses discharged: `theoremC_closed`.

NOT COVERED (prose-only, per section 14 of the dossier): Known result S (symplecticity of
Störmer–Verlet words: classical, cite only), Remark C0 (determinant β^d), the bridge Lemma C1
(declaration ↦ (1a), (1b), x*), the certificate/scheme packaging (`def:scheme`, `def:certificate`),
Lemma C2 (iii)/(v)-region, the dossier-only Remarks C4a, C4b, C5, the sharpness witness (LRP (4.11)),
every numerical check.

Status tier: FORMALISED (statement + proof, no sorry) for the tuning algebra, Lemma C4 (including the
phase-space form and α = 1/L), the distance chain, the count, and Theorem C (a), (b), (c) relative to the
named classical hypotheses `hBeck`, `hBubeck` (and the Lemma C1 outputs as hypotheses); additionally
`theoremC_closed` without the two classical hypotheses.
-/
import Mathlib
import OcfVerification.S1StochasticWord
import OcfVerification.E0MethodWords
import OcfVerification.A1DescentLemma

open Set Filter Topology

namespace OCF.C1

/-! ## Section A: the tuning (Lemma C2) -/

section A

/-- `β := √((1 − αm)(1 − αL))` (H-tune). -/
noncomputable def hbBeta (m L α : ℝ) : ℝ := Real.sqrt ((1 - α * m) * (1 - α * L))

/-- `q := 1 − αm` (H-tune). -/
def hbQ (m α : ℝ) : ℝ := 1 - α * m

/-- `s := 2α/(1 + β)` (H-tune). -/
noncomputable def hbS (α β : ℝ) : ℝ := 2 * α / (1 + β)

/-- `c_β := 2α(1 − αL)/(1 + β)²` (Theorem C (a)). -/
noncomputable def cBeta (L α β : ℝ) : ℝ := 2 * α * (1 - α * L) / (1 + β) ^ 2

/-- `b := (1 − αL)/(2α)` (Lemma C3 (iii)). -/
noncomputable def bW (L α : ℝ) : ℝ := (1 - α * L) / (2 * α)

/-- `α ≤ 1/L` is `αL ≤ 1` (`L > 0`). -/
lemma alphaL_le_one {L α : ℝ} (hL : 0 < L) (h : α ≤ 1 / L) : α * L ≤ 1 :=
  (le_div_iff₀ hL).1 h

/-- Lemma C2 (i): `β ≥ 0`. -/
lemma beta_nonneg (m L α : ℝ) : 0 ≤ hbBeta m L α := Real.sqrt_nonneg _

/-- Lemma C2 (i): `β < 1` for `0 < m ≤ L`, `0 < α`, `αL ≤ 1`. -/
lemma beta_lt_one {m L α : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α * L ≤ 1) :
    hbBeta m L α < 1 := by
  unfold hbBeta
  rw [Real.sqrt_lt' one_pos]
  have h1 : 0 < α * m := mul_pos hα hm
  have h2 : 0 ≤ 1 - α * L := by linarith
  have h3 : α * m ≤ α * L := by nlinarith
  nlinarith [mul_nonneg h1.le h2]

/-- Lemma C2 (i): `β ∈ (−1, 1)`, the standing hypothesis of `hb_word`. -/
lemma beta_gt_neg_one (m L α : ℝ) : -1 < hbBeta m L α := by
  have := beta_nonneg m L α
  linarith

/-- Lemma C2 (v), first equality: `β² = q(1 − αL)`. -/
lemma beta_sq {m L α : ℝ} (hmL : m ≤ L) (hα : 0 < α) (hαL : α * L ≤ 1) :
    hbBeta m L α ^ 2 = hbQ m α * (1 - α * L) := by
  unfold hbBeta hbQ
  have hmα : α * m ≤ α * L := by nlinarith
  rw [Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))]

/-- Lemma C2 (i): `β = 0 ⟺ αL = 1`. -/
lemma beta_eq_zero_iff {m L α : ℝ} (hmL : m ≤ L) (hα : 0 < α) (hαL : α * L ≤ 1) :
    hbBeta m L α = 0 ↔ α * L = 1 := by
  have hmα : α * m ≤ α * L := by nlinarith
  unfold hbBeta
  rw [Real.sqrt_eq_zero (mul_nonneg (by linarith) (by linarith)), mul_eq_zero]
  constructor
  · rintro (h | h) <;> linarith
  · intro h; right; linarith

/-- Lemma C2 (ii): `q ≥ 0`. -/
lemma q_nonneg {m L α : ℝ} (hmL : m ≤ L) (hα : 0 < α) (hαL : α * L ≤ 1) : 0 ≤ hbQ m α := by
  unfold hbQ; nlinarith

/-- Lemma C2 (ii): `q < 1`. -/
lemma q_lt_one {m α : ℝ} (hm : 0 < m) (hα : 0 < α) : hbQ m α < 1 := by
  unfold hbQ; nlinarith [mul_pos hα hm]

/-- Lemma C2 (ii): `q = 0 ⟺ m = L ∧ α = 1/L`. -/
lemma q_eq_zero_iff {m L α : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α * L ≤ 1) :
    hbQ m α = 0 ↔ m = L ∧ α = 1 / L := by
  have hL : 0 < L := hm.trans_le hmL
  unfold hbQ
  constructor
  · intro h
    have h1 : α * m = 1 := by linarith
    have h2 : α * L = 1 := by nlinarith
    have h3 : m = L := by
      have : α * (L - m) = 0 := by linarith
      rcases mul_eq_zero.1 this with h | h
      · linarith
      · linarith
    refine ⟨h3, ?_⟩
    field_simp; linarith
  · rintro ⟨rfl, h⟩
    rw [h]; field_simp; ring

/-- Lemma C2 (iv): `q ≥ 1 − m/L`. -/
lemma q_ge {m L α : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hαL : α ≤ 1 / L) :
    1 - m / L ≤ hbQ m α := by
  have hL : 0 < L := hm.trans_le hmL
  unfold hbQ
  have : α * m ≤ m / L := by
    calc α * m ≤ 1 / L * m := by gcongr
      _ = m / L := by ring
  linarith

/-- The degenerate case `m = L`: `β = 1 − αm` (so `β = q`; it is `0` only at `α = 1/L`, not for
every `α`). -/
lemma beta_of_eq {m α : ℝ} (hαm : α * m ≤ 1) : hbBeta m m α = 1 - α * m := by
  unfold hbBeta
  rw [← sq, Real.sqrt_sq (by linarith)]

/-- `b ≥ 0` (`αL ≤ 1`). -/
lemma bW_nonneg {L α : ℝ} (hα : 0 < α) (hαL : α * L ≤ 1) : 0 ≤ bW L α := by
  unfold bW
  apply div_nonneg (by linarith) (by linarith)

/-- `c_β ≥ 0` (`αL ≤ 1`). -/
lemma cBeta_nonneg {L α β : ℝ} (hα : 0 < α) (hαL : α * L ≤ 1) : 0 ≤ cBeta L α β := by
  unfold cBeta
  apply div_nonneg (mul_nonneg (by linarith) (by linarith)) (sq_nonneg _)

end A

/-! ## Section B: Lemma C4, the one-step Lyapunov inequality (gap-filled, GFJ Section 4 at θ = 1 − αL) -/

section B

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- `Λ(x, x') = E(x) − E* + b‖x − x'‖²` (Lemma C3 (iii)); `Es = E*`. -/
def Lam (E : X → ℝ) (Es b : ℝ) (x x' : X) : ℝ := E x - Es + b * ‖x - x'‖ ^ 2

/-- `Λ` on a pair `z = (x, x')`. -/
def LamP (E : X → ℝ) (Es b : ℝ) (z : X × X) : ℝ := Lam E Es b z.1 z.2

/-- The conclusion of the descent lemma (Beck Lemma 5.7): the quadratic upper bound. -/
def DescentIneq (E : X → ℝ) (L : ℝ) : Prop :=
  ∀ x y : X, E y ≤ E x + inner ℝ (gradient E x) (y - x) + L / 2 * ‖y - x‖ ^ 2

/-- The conclusion of gradient dominance (Bubeck Lemma 6.9): `E(x) − E* ≤ ‖∇E(x)‖²/(2m)`. -/
def GradDomIneq (E : X → ℝ) (m Es : ℝ) : Prop :=
  ∀ x : X, E x - Es ≤ ‖gradient E x‖ ^ 2 / (2 * m)

/-- NAMED HYPOTHESIS. [CLASSICAL] Beck, First-Order Methods in Optimization (2017), Lemma 5.7,
p. 109 (descent lemma): `f ∈ C^{1,1}_L(ℝⁿ)` (differentiable with `L`-Lipschitz gradient) gives
`f(y) ≤ f(x) + ⟨∇f(x), y − x⟩ + (L/2)‖x − y‖²` for all `x, y`. -/
def Beck57 (E : X → ℝ) (L : ℝ) : Prop :=
  Differentiable ℝ E → OCF.G3.LipGrad E L → DescentIneq E L

/-- Bubeck (3.13), p. 276, the definition of `m`-strong convexity used in Lemma 6.9, Euclidean norm:
`f(x) − f(y) ≤ ⟨∇f(x), x − y⟩ − (m/2)‖x − y‖²`. -/
def StrongConv313 (E : X → ℝ) (m : ℝ) : Prop :=
  ∀ x y : X, E x - E y ≤ inner ℝ (gradient E x) (x - y) - m / 2 * ‖x - y‖ ^ 2

/-- NAMED HYPOTHESIS. [CLASSICAL] Bubeck, Convex Optimization: Algorithms and Complexity (FnT 2015),
Lemma 6.9, p. 341 (Euclidean case): for `f` `m`-strongly convex (3.13) with minimiser `x*` over the
whole space, `f(x) − f(x*) ≤ ‖∇f(x)‖²/(2m)` for every `x`. -/
def Bubeck69 (E : X → ℝ) (m : ℝ) (xs : X) : Prop :=
  0 < m → StrongConv313 E m → (∀ y, E xs ≤ E y) → GradDomIneq E m (E xs)

/-- Bubeck (3.13) is (1a) with the two points exchanged. -/
lemma strongConv313_iff {E : X → ℝ} {m : ℝ} : StrongConv313 E m ↔ OCF.S1.Dal1a E m := by
  constructor
  · intro h θ θ'
    have := h θ' θ
    have e : inner ℝ (gradient E θ') (θ' - θ) = -inner ℝ (gradient E θ') (θ - θ') := by
      rw [← inner_neg_right, neg_sub]
    rw [norm_sub_rev] at this
    linarith
  · intro h x y
    have := h y x
    have e : inner ℝ (gradient E x) (y - x) = -inner ℝ (gradient E x) (x - y) := by
      rw [← inner_neg_right, neg_sub]
    rw [norm_sub_rev] at this
    linarith

lemma hbStep_fst (E : X → ℝ) (α β : ℝ) (z : X × X) :
    (OCF.E0.hbStep E α β z).1 = z.1 - α • gradient E z.1 + β • (z.1 - z.2) := rfl

/-- **Lemma C4** (steps 1–5): for every pair `z = (x, x')`, with `x⁺ = x − α∇E(x) + β(x − x')`,
`Λ(x⁺, x) ≤ q Λ(x, x')`, `q = 1 − αm`, `b = (1 − αL)/(2α)`. Inputs: the descent inequality, gradient
dominance, and `β² = (1 − αm)(1 − αL)` (the only use of the value of `β`). Covers `αL = 1`
(`b = 0`) in the same chain. -/
lemma lam_step {E : X → ℝ} {Es m L α β : ℝ} (hm : 0 < m) (hα : 0 < α)
    (hβsq : β ^ 2 = (1 - α * m) * (1 - α * L))
    (hD : DescentIneq E L) (hGD : GradDomIneq E m Es) (z : X × X) :
    LamP E Es (bW L α) (OCF.E0.hbStep E α β z) ≤ (1 - α * m) * LamP E Es (bW L α) z := by
  obtain ⟨x, x'⟩ := z
  set g := gradient E x with hg
  set D := x - x' with hDdef
  have hxp : (OCF.E0.hbStep E α β (x, x')).1 = x + (-(α • g) + β • D) := by
    rw [hbStep_fst]; simp only [hg, hDdef]; abel
  have hxp2 : (OCF.E0.hbStep E α β (x, x')).2 = x := rfl
  have hP : ‖(OCF.E0.hbStep E α β (x, x')).1 - x‖ ^ 2
      = α ^ 2 * ‖g‖ ^ 2 - 2 * α * β * inner ℝ g D + β ^ 2 * ‖D‖ ^ 2 := by
    rw [hxp, add_sub_cancel_left, norm_add_sq_real, norm_neg, norm_smul, norm_smul,
      inner_neg_left, inner_smul_left, inner_smul_right, Real.norm_eq_abs, Real.norm_eq_abs,
      mul_pow, mul_pow, sq_abs, sq_abs]
    simp only [conj_trivial]
    ring
  have hdesc := hD x (OCF.E0.hbStep E α β (x, x')).1
  have hinner : inner ℝ g ((OCF.E0.hbStep E α β (x, x')).1 - x)
      = -(α * ‖g‖ ^ 2) + β * inner ℝ g D := by
    rw [hxp, add_sub_cancel_left, inner_add_right, inner_neg_right, inner_smul_right,
      inner_smul_right, real_inner_self_eq_norm_sq]
  rw [hinner] at hdesc
  have hgd := hGD x
  unfold LamP Lam
  rw [hxp2]
  simp only
  rw [hP] at hdesc ⊢
  set a := ‖g‖ ^ 2 with ha
  set c := inner ℝ g D with hc
  set d := ‖D‖ ^ 2 with hd
  set A := E x - Es with hA
  set Ap := E (OCF.E0.hbStep E α β (x, x')).1 - Es with hAp
  have hα0 : α ≠ 0 := hα.ne'
  have h2m : 0 < 2 * m := by linarith
  have hgd' : A * (2 * m) ≤ a := (le_div_iff₀ h2m).1 hgd
  unfold bW
  set b := (1 - α * L) / (2 * α) with hbdef
  have hb : 2 * α * b = 1 - α * L := by rw [hbdef]; field_simp
  set t := L / 2 + b with htdef
  have hLb : t * (2 * α) = 1 := by
    rw [htdef]; linear_combination hb
  have e1 : t * (α ^ 2 * a - 2 * α * β * c + β ^ 2 * d)
      = (α * a - 2 * β * c) / 2 + (1 - α * m) * b * d := by
    linear_combination ((α * a - 2 * β * c) / 2 + d * (1 - α * m) * b) * hLb
      + d * t * hβsq - d * t * (1 - α * m) * hb
  have hmul := mul_le_mul_of_nonneg_left hgd' hα.le
  have : t * (α ^ 2 * a - 2 * α * β * c + β ^ 2 * d)
      = L / 2 * (α ^ 2 * a - 2 * α * β * c + β ^ 2 * d)
        + b * (α ^ 2 * a - 2 * α * β * c + β ^ 2 * d) := by rw [htdef]; ring
  nlinarith [hdesc, e1, this, hmul]

/-- Lemma C4, iterated: `Λ(S^K z) ≤ q^K Λ(z)` (`q ≥ 0`). -/
lemma lam_iter {E : X → ℝ} {Es m L α β : ℝ} (hm : 0 < m) (hα : 0 < α) (hq : 0 ≤ 1 - α * m)
    (hβsq : β ^ 2 = (1 - α * m) * (1 - α * L))
    (hD : DescentIneq E L) (hGD : GradDomIneq E m Es) (z : X × X) (K : ℕ) :
    LamP E Es (bW L α) ((OCF.E0.hbStep E α β)^[K] z) ≤ (1 - α * m) ^ K * LamP E Es (bW L α) z := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc _ ≤ (1 - α * m) * LamP E Es (bW L α) ((OCF.E0.hbStep E α β)^[K] z) :=
          lam_step hm hα hβsq hD hGD _
      _ ≤ (1 - α * m) * ((1 - α * m) ^ K * LamP E Es (bW L α) z) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = _ := by ring

end B

/-! ## Section C: the word, the start, and the phase-space form (Lemma C3, Lemma C4 step 6) -/

section C

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

open OCF.E0

/-- The word `W = Φ^SV_1 ∘ D^{1−β,M'}_Kin` of `prop:hb-word` for `f = E`: the damping letter
`dstep (1−β) M'⁻¹ GK` (`GK` the phase-space gradient of `Kin(v) = (s/2)‖v‖²`) followed by the
Störmer–Verlet letter with potential `E`, mass `M_p = s⁻¹ I`, step `1`. -/
noncomputable def hbWord (E : X → ℝ) (α β : ℝ) (GK : X × X → X × X) (z : X × X) : X × X :=
  sv (gradient E) (MpHBinv (hbS α β)) 1 (dstep (1 - β) (MprInv (hbS α β)) GK z)

/-- `S^K (x_0, x_0)`: the pair `(x_K, x_{K−1})` of the recursion started at `x_{−1} = x_0`. -/
noncomputable def hbIter (E : X → ℝ) (α β : ℝ) (x0 : X) (K : ℕ) : X × X :=
  (hbStep E α β)^[K] (x0, x0)

/-- `x_K`, the first component. -/
noncomputable def hbX (E : X → ℝ) (α β : ℝ) (x0 : X) (K : ℕ) : X := (hbIter E α β x0 K).1

/-- The start `z_0 = χ(x_0, x_0)` (H-start). -/
noncomputable def z0 (E : X → ℝ) (α β : ℝ) (x0 : X) : X × X := chiHB E (hbS α β) (x0, x0)

/-- `x_K` of the word: the first component of `W^K z_0`. -/
noncomputable def xK (E : X → ℝ) (α β : ℝ) (GK : X × X → X × X) (x0 : X) (K : ℕ) : X :=
  ((hbWord E α β GK)^[K] (z0 E α β x0)).1

/-- `Λ_W(x, v) = E(x) − E* + c‖v + ½∇E(x)‖²`. -/
noncomputable def LamW (E : X → ℝ) (Es c : ℝ) (z : X × X) : ℝ :=
  E z.1 - Es + c * ‖z.2 + (1 / 2 : ℝ) • gradient E z.1‖ ^ 2

/-- `z_0 = χ(x_0, x_0) = (x_0, −½∇E(x_0))`. -/
lemma chi_diag (E : X → ℝ) (s : ℝ) (x0 : X) :
    chiHB E s (x0, x0) = (x0, -((1 / 2 : ℝ) • gradient E x0)) := by
  simp [chiHB]

lemma hbIter_zero (E : X → ℝ) (α β : ℝ) (x0 : X) : hbIter E α β x0 0 = (x0, x0) := rfl

/-- One step of the recursion: `(x_{K+1}, x_K) = S(x_K, x_{K−1})`. -/
lemma hbIter_succ (E : X → ℝ) (α β : ℝ) (x0 : X) (K : ℕ) :
    hbIter E α β x0 (K + 1)
      = (hbX E α β x0 K - α • gradient E (hbX E α β x0 K)
          + β • (hbX E α β x0 K - (hbIter E α β x0 K).2), hbX E α β x0 K) := by
  unfold hbIter hbX
  rw [Function.iterate_succ_apply']
  rfl

lemma hbX_zero (E : X → ℝ) (α β : ℝ) (x0 : X) : hbX E α β x0 0 = x0 := rfl

/-- `x_1 = x_0 − α∇E(x_0)`: the recursion at `x_{−1} = x_0`. -/
lemma hbX_one (E : X → ℝ) (α β : ℝ) (x0 : X) :
    hbX E α β x0 1 = x0 - α • gradient E x0 := by
  unfold hbX
  rw [hbIter_succ]
  simp [hbIter_zero, hbX_zero]

/-- The recursion `x_{j+1} = x_j − α∇E(x_j) + β(x_j − x_{j−1})` for `j ≥ 1`. -/
lemma hbX_add_two (E : X → ℝ) (α β : ℝ) (x0 : X) (K : ℕ) :
    hbX E α β x0 (K + 2)
      = hbX E α β x0 (K + 1) - α • gradient E (hbX E α β x0 (K + 1))
          + β • (hbX E α β x0 (K + 1) - hbX E α β x0 K) := by
  have h1 := hbIter_succ E α β x0 (K + 1)
  have h2 := hbIter_succ E α β x0 K
  have h3 : (hbIter E α β x0 (K + 1)).2 = hbX E α β x0 K := by rw [h2]
  unfold hbX at h1 ⊢
  rw [h1]
  rw [h3]
  rfl

/-- Lemma C3 (i) (pointer to `hb_word`, E0MethodWords.lean): `W ∘ χ = χ ∘ S`. -/
lemma word_chi {E : X → ℝ} {α β : ℝ} (hα : 0 < α) (hβ1 : -1 < β) (hβ2 : β < 1)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α β * ‖z.2‖ ^ 2) GK) (z : X × X) :
    hbWord E α β GK (chiHB E (hbS α β) z) = chiHB E (hbS α β) (hbStep E α β z) :=
  (hb_word E hα hβ1 hβ2 GK hGK).2.2 z

/-- Lemma C3 (ii): `W^K χ(x_0, x_0) = χ(S^K(x_0, x_0)) = χ(x_K, x_{K−1})`. -/
lemma word_iter {E : X → ℝ} {α β : ℝ} (hα : 0 < α) (hβ1 : -1 < β) (hβ2 : β < 1)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α β * ‖z.2‖ ^ 2) GK) (x0 : X) (K : ℕ) :
    (hbWord E α β GK)^[K] (z0 E α β x0) = chiHB E (hbS α β) (hbIter E α β x0 K) := by
  induction K with
  | zero => rfl
  | succ K ih =>
    rw [Function.iterate_succ_apply', ih, word_chi hα hβ1 hβ2 hGK]
    unfold hbIter
    rw [Function.iterate_succ_apply']

/-- Lemma C3 (ii): the first component of `W^K z_0` is `x_K` of the recursion at `x_{−1} = x_0`. -/
lemma xK_eq_hbX {E : X → ℝ} {α β : ℝ} (hα : 0 < α) (hβ1 : -1 < β) (hβ2 : β < 1)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α β * ‖z.2‖ ^ 2) GK) (x0 : X) (K : ℕ) :
    xK E α β GK x0 K = hbX E α β x0 K := by
  unfold xK hbX
  rw [word_iter hα hβ1 hβ2 hGK]
  rfl

/-- Lemma C3 (iii): `Λ_W ∘ χ = Λ`, because `b s² = c_β`. -/
lemma lamW_chi {E : X → ℝ} {Es L α β : ℝ} (hα : 0 < α) (hβ : -1 < β) (z : X × X) :
    LamW E Es (cBeta L α β) (chiHB E (hbS α β) z) = LamP E Es (bW L α) z := by
  obtain ⟨x, x'⟩ := z
  have h1β : 0 < 1 + β := by linarith
  have h1 : (chiHB E (hbS α β) (x, x')).2 + (1 / 2 : ℝ) • gradient E x
      = (1 / hbS α β) • (x - x') := by
    simp [chiHB]
  unfold LamW LamP Lam
  simp only [chiHB] at h1 ⊢
  rw [h1, norm_smul, mul_pow]
  have hs : hbS α β = 2 * α / (1 + β) := rfl
  rw [Real.norm_eq_abs, sq_abs, hs, cBeta, bW]
  congr 1
  field_simp

/-- Lemma C3 (iii) in the form `Λ_W = Λ ∘ χ⁻¹`. -/
lemma lamW_eq_lam_chiinv {E : X → ℝ} {Es L α β : ℝ} {GK : X × X → X × X} (hα : 0 < α)
    (hβ1 : -1 < β) (hβ2 : β < 1)
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α β * ‖z.2‖ ^ 2) GK) (z : X × X) :
    LamW E Es (cBeta L α β) z = LamP E Es (bW L α) (chiHBinv E (hbS α β) z) := by
  have h : chiHB E (hbS α β) (chiHBinv E (hbS α β) z) = z :=
    (hb_word E hα hβ1 hβ2 GK hGK).2.1 z
  rw [← lamW_chi (Es := Es) (L := L) hα hβ1, h]

/-- **Lemma C4 step 6, the phase-space form.** `Λ_W(W z) ≤ q Λ_W(z)` for every phase point `z`. -/
lemma lamW_decay {E : X → ℝ} {Es m L α β : ℝ} {GK : X × X → X × X} (hm : 0 < m) (hα : 0 < α)
    (hβ1 : -1 < β) (hβ2 : β < 1)
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α β * ‖z.2‖ ^ 2) GK)
    (hβsq : β ^ 2 = (1 - α * m) * (1 - α * L))
    (hD : DescentIneq E L) (hGD : GradDomIneq E m Es) (z : X × X) :
    LamW E Es (cBeta L α β) (hbWord E α β GK z)
      ≤ (1 - α * m) * LamW E Es (cBeta L α β) z := by
  set p := chiHBinv E (hbS α β) z with hp
  have hz : z = chiHB E (hbS α β) p := ((hb_word E hα hβ1 hβ2 GK hGK).2.1 z).symm
  conv_lhs => rw [hz]
  conv_rhs => rw [hz]
  rw [word_chi hα hβ1 hβ2 hGK, lamW_chi hα hβ1, lamW_chi hα hβ1]
  exact lam_step hm hα hβsq hD hGD p

/-- Iterated: `Λ_W(W^K z) ≤ q^K Λ_W(z)`. -/
lemma lamW_iter {E : X → ℝ} {Es m L α β : ℝ} {GK : X × X → X × X} (hm : 0 < m) (hα : 0 < α)
    (hq : 0 ≤ 1 - α * m) (hβ1 : -1 < β) (hβ2 : β < 1)
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α β * ‖z.2‖ ^ 2) GK)
    (hβsq : β ^ 2 = (1 - α * m) * (1 - α * L))
    (hD : DescentIneq E L) (hGD : GradDomIneq E m Es) (z : X × X) (K : ℕ) :
    LamW E Es (cBeta L α β) ((hbWord E α β GK)^[K] z)
      ≤ (1 - α * m) ^ K * LamW E Es (cBeta L α β) z := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    calc _ ≤ (1 - α * m) * LamW E Es (cBeta L α β) ((hbWord E α β GK)^[K] z) :=
          lamW_decay hm hα hβ1 hβ2 hGK hβsq hD hGD _
      _ ≤ (1 - α * m) * ((1 - α * m) ^ K * LamW E Es (cBeta L α β) z) :=
          mul_le_mul_of_nonneg_left ih hq
      _ = _ := by ring

end C

/-! ## Section D: the classical hypotheses are consistent (discharge), minimiser facts -/

section D

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- `Beck57` holds for every `E` (via A1's segment bound with `t = 1`); a consistency check that
the named hypothesis is not vacuous. -/
theorem beck57_holds (E : X → ℝ) (L : ℝ) : Beck57 E L := by
  intro hdiff hL x y
  have := OCF.A1.upper_bound_on_segment (f := E) (x := x) (d := x - y) (β := L) (t := 1)
    zero_le_one (fun s _ => hdiff _)
    (fun s _ => by
      have := hL (x - s • (x - y)) x
      exact this)
  simp only [one_smul, sub_sub_cancel, one_mul, one_pow, mul_one] at this
  have e : inner ℝ (gradient E x) (y - x) = -inner ℝ (gradient E x) (x - y) := by
    rw [← inner_neg_right, neg_sub]
  rw [norm_sub_rev y x, e]
  linarith

/-- `Bubeck69` holds for every `E` (five lines from (3.13): `⟨g, w⟩ − (m/2)‖w‖² ≤ ‖g‖²/(2m)`). -/
theorem bubeck69_holds (E : X → ℝ) (m : ℝ) (xs : X) : Bubeck69 E m xs := by
  intro hm hsc _ x
  have h := hsc x xs
  have hcs := real_inner_le_norm (gradient E x) (x - xs)
  have hn := norm_nonneg (gradient E x)
  have hw := norm_nonneg (x - xs)
  rw [le_div_iff₀ (by linarith : 0 < 2 * m)]
  nlinarith [sq_nonneg (m * ‖x - xs‖ - ‖gradient E x‖), mul_le_mul_of_nonneg_left hcs hm.le]

/-- A global minimiser of a function has zero gradient. -/
lemma grad_zero_of_min {E : X → ℝ} {xs : X} (hmin : ∀ y, E xs ≤ E y) : gradient E xs = 0 := by
  have h : IsLocalMin E xs := Filter.Eventually.of_forall hmin
  unfold gradient
  rw [h.fderiv_eq_zero]
  simp

/-- Lemma C1 consequence: `E(y) ≥ E* + (m/2)‖y − x*‖²` (from (1a) at `(y, x*)`, `∇E(x*) = 0`). -/
lemma strong_lower {E : X → ℝ} {xs : X} {m : ℝ} (h1a : OCF.S1.Dal1a E m)
    (hmin : ∀ y, E xs ≤ E y) (x : X) : m / 2 * ‖x - xs‖ ^ 2 ≤ E x - E xs := by
  have := h1a x xs
  rw [grad_zero_of_min hmin, inner_zero_left, sub_zero] at this
  exact this

/-- The minimiser is unique (Lemma C1: "a unique minimiser `x*`"), for `m > 0`. -/
lemma min_unique {E : X → ℝ} {xs ys : X} {m : ℝ} (hm : 0 < m) (h1a : OCF.S1.Dal1a E m)
    (hmin : ∀ y, E xs ≤ E y) (hmin' : ∀ y, E ys ≤ E y) : xs = ys := by
  have h1 := strong_lower h1a hmin ys
  have h2 : E ys ≤ E xs := hmin' xs
  have h3 : E xs ≤ E ys := hmin ys
  have : ‖ys - xs‖ ^ 2 ≤ 0 := by nlinarith
  have h4 : ‖ys - xs‖ = 0 := by nlinarith [norm_nonneg (ys - xs)]
  have := sub_eq_zero.1 (norm_eq_zero.1 h4)
  exact this.symm

/-- Lemma C5 (i)–(iv) as real inequalities: given the decay `E(x_K) − E* ≤ q^K (E(x_0) − E*)` of
the energy gap along any sequence `x`. -/
lemma dist_chain {E : X → ℝ} {xs x0 : X} {m L q : ℝ} (hm : 0 < m) (hq : 0 ≤ q)
    (h1a : OCF.S1.Dal1a E m) (hmin : ∀ y, E xs ≤ E y)
    (hD : DescentIneq E L) (hGD : GradDomIneq E m (E xs))
    (x : ℕ → X) (hx0 : x 0 = x0) (hdec : ∀ K, E (x K) - E xs ≤ q ^ K * (E x0 - E xs)) :
    (E x0 - E xs ≤ ‖gradient E x0‖ ^ 2 / (2 * m)) ∧
    (E x0 - E xs ≤ L / 2 * ‖x0 - xs‖ ^ 2) ∧
    ‖x0 - xs‖ ≤ ‖gradient E x0‖ / m ∧
    ∀ K : ℕ,
      (m / 2 * ‖x K - xs‖ ^ 2 ≤ E (x K) - E xs) ∧
      ‖x K - xs‖ ^ 2 ≤ q ^ K * (‖gradient E x0‖ / m) ^ 2 ∧
      ‖x K - xs‖ ^ 2 ≤ L / m * q ^ K * ‖x0 - xs‖ ^ 2 := by
  have hA0 : E x0 - E xs ≤ ‖gradient E x0‖ ^ 2 / (2 * m) := hGD x0
  have hA1 : E x0 - E xs ≤ L / 2 * ‖x0 - xs‖ ^ 2 := by
    have := hD xs x0
    rw [grad_zero_of_min hmin, inner_zero_left, add_zero] at this
    linarith
  have hlow := fun K => strong_lower h1a hmin (x K)
  have hqK : ∀ K : ℕ, 0 ≤ q ^ K := fun K => pow_nonneg hq K
  have hpos : (0 : ℝ) < m / 2 := by linarith
  refine ⟨hA0, hA1, ?_, fun K => ⟨hlow K, ?_, ?_⟩⟩
  · -- K = 0
    have h0 := hlow 0
    rw [hx0] at h0
    have h2 : m / 2 * ‖x0 - xs‖ ^ 2 ≤ ‖gradient E x0‖ ^ 2 / (2 * m) := h0.trans hA0
    rw [le_div_iff₀ hm]
    have h3 : ‖x0 - xs‖ ^ 2 * m ^ 2 ≤ ‖gradient E x0‖ ^ 2 := by
      have : m / 2 * ‖x0 - xs‖ ^ 2 * (2 * m) ≤ ‖gradient E x0‖ ^ 2 := by
        rwa [le_div_iff₀ (by linarith : 0 < 2 * m)] at h2
      nlinarith
    have := abs_le_of_sq_le_sq' (by nlinarith [h3] : (‖x0 - xs‖ * m) ^ 2 ≤ ‖gradient E x0‖ ^ 2)
      (norm_nonneg _)
    exact this.2
  · have h1 := (hlow K).trans (hdec K)
    have h2 : q ^ K * (E x0 - E xs) ≤ q ^ K * (‖gradient E x0‖ ^ 2 / (2 * m)) :=
      mul_le_mul_of_nonneg_left hA0 (hqK K)
    have h3 : m / 2 * ‖x K - xs‖ ^ 2 ≤ q ^ K * (‖gradient E x0‖ ^ 2 / (2 * m)) := h1.trans h2
    have e : q ^ K * (‖gradient E x0‖ / m) ^ 2
        = (q ^ K * (‖gradient E x0‖ ^ 2 / (2 * m))) / (m / 2) := by
      field_simp
    rw [e, le_div_iff₀ hpos]
    linarith
  · have h1 := (hlow K).trans (hdec K)
    have h2 : q ^ K * (E x0 - E xs) ≤ q ^ K * (L / 2 * ‖x0 - xs‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hA1 (hqK K)
    have h3 : m / 2 * ‖x K - xs‖ ^ 2 ≤ q ^ K * (L / 2 * ‖x0 - xs‖ ^ 2) := h1.trans h2
    have e : L / m * q ^ K * ‖x0 - xs‖ ^ 2
        = (q ^ K * (L / 2 * ‖x0 - xs‖ ^ 2)) / (m / 2) := by
      field_simp
    rw [e, le_div_iff₀ hpos]
    linarith

/-- The square root of the squared bound: for `q ≥ 0`, `(q^{K/2})² = q^K`. -/
lemma rpow_half_sq {q : ℝ} (hq : 0 ≤ q) (K : ℕ) : (q ^ ((K : ℝ) / 2)) ^ 2 = q ^ K := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hq]
  have : ((K : ℝ) / 2 * ((2 : ℕ) : ℝ)) = (K : ℝ) := by push_cast; ring
  rw [this, Real.rpow_natCast]

/-- From `y² ≤ q^K r²` to `y ≤ q^{K/2} r` (`y, r, q ≥ 0`). -/
lemma le_rpow_of_sq_le {q y r : ℝ} (hq : 0 ≤ q) (hy : 0 ≤ y) (hr : 0 ≤ r) (K : ℕ)
    (h : y ^ 2 ≤ q ^ K * r ^ 2) : y ≤ q ^ ((K : ℝ) / 2) * r := by
  have hpow : 0 ≤ q ^ ((K : ℝ) / 2) := Real.rpow_nonneg hq _
  have : y ^ 2 ≤ (q ^ ((K : ℝ) / 2) * r) ^ 2 := by
    rw [mul_pow, rpow_half_sq hq]; exact h
  exact (sq_le_sq₀ hy (mul_nonneg hpow hr)).1 this

end D

/-! ## Section E: Theorem C (a), (b), (c) -/

section E

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

open OCF.E0

/-- The computed start bound `r_0 = ‖∇E(x_0)‖/m` (Theorem C (b)). -/
noncomputable def r0C (E : X → ℝ) (m : ℝ) (x0 : X) : ℝ := ‖gradient E x0‖ / m

lemma r0C_nonneg (E : X → ℝ) {m : ℝ} (hm : 0 < m) (x0 : X) : 0 ≤ r0C E m x0 :=
  div_nonneg (norm_nonneg _) hm.le

/-- **Theorem C (a)** (decay). Hypotheses: the Lemma C1 outputs `h1a`, `h1b`, `hmin`, `hmL` and
`E ∈ C¹`; the named classical inputs `hBeck`, `hBubeck`; `GK` the gradient of `Kin`. Conclusions:
`β ∈ [0, 1)`, `q ∈ [0, 1)`; `Λ_W(W z) ≤ q Λ_W(z)` for every `z`; `Λ_W(z_0) = E(x_0) − E*`;
`E(x_K) − E* ≤ Λ_W(W^K z_0) ≤ q^K (E(x_0) − E*)` for every `K`; and `x_K`, the first component of
`W^K z_0`, is the `K`th iterate of the recursion started at `x_{−1} = x_0`. -/
theorem theoremC_a {E : X → ℝ} {xs : X} {m L α : ℝ} (x0 : X)
    (hm : 0 < m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α ≤ 1 / L)
    (hdiff : Differentiable ℝ E) (h1a : OCF.S1.Dal1a E m) (h1b : OCF.G3.LipGrad E L)
    (hmin : ∀ y, E xs ≤ E y) (hBeck : Beck57 E L) (hBubeck : Bubeck69 E m xs)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α (hbBeta m L α) * ‖z.2‖ ^ 2) GK) :
    (0 ≤ hbBeta m L α ∧ hbBeta m L α < 1 ∧ 0 ≤ hbQ m α ∧ hbQ m α < 1) ∧
    (∀ z : X × X,
      LamW E (E xs) (cBeta L α (hbBeta m L α)) (hbWord E α (hbBeta m L α) GK z)
        ≤ hbQ m α * LamW E (E xs) (cBeta L α (hbBeta m L α)) z) ∧
    LamW E (E xs) (cBeta L α (hbBeta m L α)) (z0 E α (hbBeta m L α) x0) = E x0 - E xs ∧
    (∀ K : ℕ,
      E (xK E α (hbBeta m L α) GK x0 K) - E xs
          ≤ LamW E (E xs) (cBeta L α (hbBeta m L α))
              ((hbWord E α (hbBeta m L α) GK)^[K] (z0 E α (hbBeta m L α) x0)) ∧
      LamW E (E xs) (cBeta L α (hbBeta m L α))
              ((hbWord E α (hbBeta m L α) GK)^[K] (z0 E α (hbBeta m L α) x0))
          ≤ hbQ m α ^ K * (E x0 - E xs)) ∧
    (∀ K : ℕ, xK E α (hbBeta m L α) GK x0 K = hbX E α (hbBeta m L α) x0 K) := by
  have hL : 0 < L := hm.trans_le hmL
  have hαL' : α * L ≤ 1 := alphaL_le_one hL hαL
  have hβ0 := beta_nonneg m L α
  have hβ1 := beta_lt_one hm hmL hα hαL'
  have hq0 := q_nonneg hmL hα hαL'
  have hq1 := q_lt_one hm hα
  have hβsq : hbBeta m L α ^ 2 = (1 - α * m) * (1 - α * L) := by
    have := beta_sq hmL hα hαL'
    rwa [hbQ] at this
  have hD : DescentIneq E L := hBeck hdiff h1b
  have hGD : GradDomIneq E m (E xs) := hBubeck hm (strongConv313_iff.2 h1a) hmin
  have hq0' : 0 ≤ 1 - α * m := hq0
  have hβ1' : -1 < hbBeta m L α := beta_gt_neg_one m L α
  have hLamz0 : LamW E (E xs) (cBeta L α (hbBeta m L α)) (z0 E α (hbBeta m L α) x0)
      = E x0 - E xs := by
    unfold z0
    rw [lamW_chi hα hβ1']
    unfold LamP Lam
    simp
  refine ⟨⟨hβ0, hβ1, hq0, hq1⟩, fun z => ?_, hLamz0, fun K => ?_, fun K => ?_⟩
  · exact lamW_decay hm hα hβ1' hβ1 hGK hβsq hD hGD z
  · have hit := lamW_iter hm hα hq0' hβ1' hβ1 hGK hβsq hD hGD (z0 E α (hbBeta m L α) x0) K
    rw [hLamz0] at hit
    refine ⟨?_, hit⟩
    have hc : 0 ≤ cBeta L α (hbBeta m L α) := cBeta_nonneg hα hαL'
    unfold xK LamW
    have := mul_nonneg hc (pow_nonneg (norm_nonneg
      (((hbWord E α (hbBeta m L α) GK)^[K] (z0 E α (hbBeta m L α) x0)).2
        + (1 / 2 : ℝ) • gradient E
          (((hbWord E α (hbBeta m L α) GK)^[K] (z0 E α (hbBeta m L α) x0)).1))) 2)
    linarith
  · exact xK_eq_hbX hα hβ1' hβ1 hGK x0 K

/-- **Theorem C (b)** (iterate distance, computed before the run). `r_0 = ‖∇E(x_0)‖/m`:
`‖x_0 − x*‖ ≤ r_0` and `‖x_K − x*‖ ≤ q^{K/2} r_0` (no floor), together with the chain of Lemma C5
(`(m/2)‖x_K − x*‖² ≤ E(x_K) − E* ≤ q^K (E(x_0) − E*)`, `E(x_0) − E* ≤ ‖∇E(x_0)‖²/(2m)` and
`≤ (L/2)‖x_0 − x*‖²`) and the second form `‖x_K − x*‖ ≤ (L/m)^{1/2} q^{K/2} ‖x_0 − x*‖`. -/
theorem theoremC_b {E : X → ℝ} {xs : X} {m L α : ℝ} (x0 : X)
    (hm : 0 < m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α ≤ 1 / L)
    (hdiff : Differentiable ℝ E) (h1a : OCF.S1.Dal1a E m) (h1b : OCF.G3.LipGrad E L)
    (hmin : ∀ y, E xs ≤ E y) (hBeck : Beck57 E L) (hBubeck : Bubeck69 E m xs)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α (hbBeta m L α) * ‖z.2‖ ^ 2) GK) :
    (E x0 - E xs ≤ ‖gradient E x0‖ ^ 2 / (2 * m)) ∧
    (E x0 - E xs ≤ L / 2 * ‖x0 - xs‖ ^ 2) ∧
    ‖x0 - xs‖ ≤ r0C E m x0 ∧
    ∀ K : ℕ,
      (m / 2 * ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ^ 2
          ≤ E (xK E α (hbBeta m L α) GK x0 K) - E xs) ∧
      (E (xK E α (hbBeta m L α) GK x0 K) - E xs ≤ hbQ m α ^ K * (E x0 - E xs)) ∧
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ^ 2 ≤ hbQ m α ^ K * r0C E m x0 ^ 2 ∧
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ hbQ m α ^ ((K : ℝ) / 2) * r0C E m x0 ∧
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖
          ≤ Real.sqrt (L / m) * hbQ m α ^ ((K : ℝ) / 2) * ‖x0 - xs‖ := by
  have hL : 0 < L := hm.trans_le hmL
  have hαL' : α * L ≤ 1 := alphaL_le_one hL hαL
  have hq0 := q_nonneg hmL hα hαL'
  have hD : DescentIneq E L := hBeck hdiff h1b
  have hGD : GradDomIneq E m (E xs) := hBubeck hm (strongConv313_iff.2 h1a) hmin
  have hA := theoremC_a (xs := xs) x0 hm hmL hα hαL hdiff h1a h1b hmin hBeck hBubeck hGK
  have hdec : ∀ K, E (xK E α (hbBeta m L α) GK x0 K) - E xs ≤ hbQ m α ^ K * (E x0 - E xs) :=
    fun K => (hA.2.2.2.1 K).1.trans (hA.2.2.2.1 K).2
  have hx0 : xK E α (hbBeta m L α) GK x0 0 = x0 := rfl
  have hch := dist_chain (xs := xs) (x0 := x0) (L := L) hm hq0 h1a hmin hD hGD
    (xK E α (hbBeta m L α) GK x0) hx0 hdec
  obtain ⟨c1, c2, c3, c4⟩ := hch
  refine ⟨c1, c2, c3, fun K => ?_⟩
  obtain ⟨d1, d2, d3⟩ := c4 K
  refine ⟨d1, hdec K, d2, ?_, ?_⟩
  · exact le_rpow_of_sq_le hq0 (norm_nonneg _) (r0C_nonneg E hm x0) K d2
  · have hLm : 0 ≤ L / m := div_nonneg hL.le hm.le
    have := le_rpow_of_sq_le (q := hbQ m α) (y := ‖xK E α (hbBeta m L α) GK x0 K - xs‖)
      (r := Real.sqrt (L / m) * ‖x0 - xs‖) hq0 (norm_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) K
      (by rw [mul_pow, Real.sq_sqrt hLm]; linarith)
    calc _ ≤ _ := this
      _ = _ := by ring

/-- Lemma C6 (i): the least `K` with `q^K r² ≤ ε²` belongs to the set (`q ∈ [0,1)`, `r ≥ 0`, `ε > 0`). -/
lemma count_mem {q r eps : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 ≤ r) (heps : 0 < eps) :
    q ^ OCF.S1.Keps q (r ^ 2) (eps ^ 2) * r ^ 2 ≤ eps ^ 2 := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]; simp; positivity
  · exact OCF.S1.Keps_mem hq1 hq0 (pow_pos h 2) (pow_pos heps 2)

/-- Lemma C6 (ii) (loop) for `r ≥ 0`: with fuel `n ≥ K_ε` the comparison loop returns `K_ε`. -/
lemma count_loop {q r eps : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) (hr : 0 ≤ r) (heps : 0 < eps) (n : ℕ)
    (hn : OCF.S1.Keps q (r ^ 2) (eps ^ 2) ≤ n) :
    OCF.S1.loopAux q (eps ^ 2) n (r ^ 2) 0 = OCF.S1.Keps q (r ^ 2) (eps ^ 2) := by
  rcases hr.eq_or_lt with h | h
  · subst h
    have hk : OCF.S1.Keps q ((0 : ℝ) ^ 2) (eps ^ 2) = 0 :=
      OCF.S1.Keps_zero (by simp; positivity)
    rw [hk]
    cases n with
    | zero => rfl
    | succ n => simp [OCF.S1.loopAux]; intro h; nlinarith [sq_nonneg eps]
  · exact OCF.S1.loop_eq_Keps hq1 hq0 (pow_pos h 2) (pow_pos heps 2) n hn

/-- **Theorem C (c)** (count). `K_ε` is the least `K` with `q^K r_0² ≤ ε²` (`OCF.S1.Keps`); every
`K ≥ K_ε` gives `‖x_K − x*‖ ≤ ε`; the comparison loop (multiply by `q` until `≤ ε²`) returns `K_ε`;
`r_0 ≤ ε` (in particular `r_0 = 0`) gives `K_ε = 0`; if `r_0 > 0`,
`K_ε ≤ max{0, ⌈2 log(r_0/ε)/(αm)⌉}`, and every `K ≥ max{0, ⌈2 log(r_0/ε)/(αm)⌉}` has
`‖x_K − x*‖ ≤ ε`. -/
theorem theoremC_c {E : X → ℝ} {xs : X} {m L α : ℝ} (x0 : X)
    (hm : 0 < m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α ≤ 1 / L)
    (hdiff : Differentiable ℝ E) (h1a : OCF.S1.Dal1a E m) (h1b : OCF.G3.LipGrad E L)
    (hmin : ∀ y, E xs ≤ E y) (hBeck : Beck57 E L) (hBubeck : Bubeck69 E m xs)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α (hbBeta m L α) * ‖z.2‖ ^ 2) GK)
    (eps : ℝ) (heps : 0 < eps) :
    (hbQ m α ^ OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) * r0C E m x0 ^ 2 ≤ eps ^ 2) ∧
    (∀ K : ℕ, hbQ m α ^ K * r0C E m x0 ^ 2 ≤ eps ^ 2 →
        OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ K) ∧
    (∀ K : ℕ, OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ K →
        hbQ m α ^ K * r0C E m x0 ^ 2 ≤ eps ^ 2 ∧
        ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ eps) ∧
    (∀ n : ℕ, OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ n →
        OCF.S1.loopAux (hbQ m α) (eps ^ 2) n (r0C E m x0 ^ 2) 0
          = OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2)) ∧
    (r0C E m x0 ≤ eps → OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) = 0) ∧
    (r0C E m x0 = 0 → OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) = 0) ∧
    (0 < r0C E m x0 →
      ((OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) : ℕ) : ℤ)
        ≤ max 0 ⌈2 * Real.log (r0C E m x0 / eps) / (α * m)⌉ ∧
      ∀ K : ℕ, max 0 ⌈2 * Real.log (r0C E m x0 / eps) / (α * m)⌉ ≤ (K : ℤ) →
        ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ eps) := by
  have hL : 0 < L := hm.trans_le hmL
  have hαL' : α * L ≤ 1 := alphaL_le_one hL hαL
  have hq0 := q_nonneg hmL hα hαL'
  have hq1 := q_lt_one hm hα
  have hr := r0C_nonneg E hm x0
  have hb := theoremC_b (xs := xs) x0 hm hmL hα hαL hdiff h1a h1b hmin hBeck hBubeck hGK
  have hdist : ∀ K : ℕ, hbQ m α ^ K * r0C E m x0 ^ 2 ≤ eps ^ 2 →
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ eps := by
    intro K hK
    have h1 := (hb.2.2.2 K).2.2.1
    exact (sq_le_sq₀ (norm_nonneg _) heps.le).1 (h1.trans hK)
  have hmem := count_mem hq0 hq1 hr heps
  have hup : ∀ K : ℕ, OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ K →
      hbQ m α ^ K * r0C E m x0 ^ 2 ≤ eps ^ 2 :=
    fun K hK => OCF.S1.Keps_upward hq0 hq1.le (sq_nonneg _) hmem hK
  have hr0eps : r0C E m x0 ≤ eps →
      OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) = 0 := fun h =>
    OCF.S1.Keps_zero ((sq_le_sq₀ hr heps.le).2 h)
  refine ⟨hmem, fun K hK => OCF.S1.Keps_le_of_mem hK, fun K hK => ⟨hup K hK, hdist K (hup K hK)⟩,
    fun n hn => count_loop hq0 hq1 hr heps n hn, hr0eps, fun h0 => hr0eps (by rw [h0]; exact heps.le),
    fun hpos => ?_⟩
  have hαm : 0 < α * m := mul_pos hα hm
  have hαm1 : α * m ≤ 1 := by nlinarith
  have hceil := OCF.S1.Keps_le_int_ceil (m := α) (h := m) hαm hαm1 (pow_pos hpos 2)
    (pow_pos heps 2)
  have elog : Real.log (r0C E m x0 ^ 2 / eps ^ 2) = 2 * Real.log (r0C E m x0 / eps) := by
    rw [← div_pow, Real.log_pow]; norm_num
  rw [elog] at hceil
  refine ⟨hceil, fun K hK => hdist K (hup K ?_)⟩
  have h2 : ((OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) : ℕ) : ℤ) ≤ (K : ℤ) :=
    hceil.trans hK
  exact_mod_cast h2

/-- **Theorem C with no classical hypothesis**: `theoremC_a`, `theoremC_b`, `theoremC_c` with
`hBeck := beck57_holds E L` and `hBubeck := bubeck69_holds E m xs` supplied (the Lemma C1 outputs
`h1a`, `h1b`, `hmin`, `hmL` and the definition `hGK` of `GK` remain hypotheses). -/
theorem theoremC_closed {E : X → ℝ} {xs : X} {m L α : ℝ} (x0 : X)
    (hm : 0 < m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α ≤ 1 / L)
    (hdiff : Differentiable ℝ E) (h1a : OCF.S1.Dal1a E m) (h1b : OCF.G3.LipGrad E L)
    (hmin : ∀ y, E xs ≤ E y)
    {GK : X × X → X × X}
    (hGK : IsGradPS (fun z : X × X => (1 / 2 : ℝ) * hbS α (hbBeta m L α) * ‖z.2‖ ^ 2) GK)
    (eps : ℝ) (heps : 0 < eps) :
    ((0 ≤ hbBeta m L α ∧ hbBeta m L α < 1 ∧ 0 ≤ hbQ m α ∧ hbQ m α < 1) ∧
    (∀ z : X × X,
      LamW E (E xs) (cBeta L α (hbBeta m L α)) (hbWord E α (hbBeta m L α) GK z)
        ≤ hbQ m α * LamW E (E xs) (cBeta L α (hbBeta m L α)) z) ∧
    LamW E (E xs) (cBeta L α (hbBeta m L α)) (z0 E α (hbBeta m L α) x0) = E x0 - E xs ∧
    (∀ K : ℕ,
      E (xK E α (hbBeta m L α) GK x0 K) - E xs
          ≤ LamW E (E xs) (cBeta L α (hbBeta m L α))
              ((hbWord E α (hbBeta m L α) GK)^[K] (z0 E α (hbBeta m L α) x0)) ∧
      LamW E (E xs) (cBeta L α (hbBeta m L α))
              ((hbWord E α (hbBeta m L α) GK)^[K] (z0 E α (hbBeta m L α) x0))
          ≤ hbQ m α ^ K * (E x0 - E xs)) ∧
    (∀ K : ℕ, xK E α (hbBeta m L α) GK x0 K = hbX E α (hbBeta m L α) x0 K)) ∧
    ((E x0 - E xs ≤ ‖gradient E x0‖ ^ 2 / (2 * m)) ∧
    (E x0 - E xs ≤ L / 2 * ‖x0 - xs‖ ^ 2) ∧
    ‖x0 - xs‖ ≤ r0C E m x0 ∧
    ∀ K : ℕ,
      (m / 2 * ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ^ 2
          ≤ E (xK E α (hbBeta m L α) GK x0 K) - E xs) ∧
      (E (xK E α (hbBeta m L α) GK x0 K) - E xs ≤ hbQ m α ^ K * (E x0 - E xs)) ∧
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ^ 2 ≤ hbQ m α ^ K * r0C E m x0 ^ 2 ∧
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ hbQ m α ^ ((K : ℝ) / 2) * r0C E m x0 ∧
      ‖xK E α (hbBeta m L α) GK x0 K - xs‖
          ≤ Real.sqrt (L / m) * hbQ m α ^ ((K : ℝ) / 2) * ‖x0 - xs‖) ∧
    ((hbQ m α ^ OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) * r0C E m x0 ^ 2 ≤ eps ^ 2) ∧
    (∀ K : ℕ, hbQ m α ^ K * r0C E m x0 ^ 2 ≤ eps ^ 2 →
        OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ K) ∧
    (∀ K : ℕ, OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ K →
        hbQ m α ^ K * r0C E m x0 ^ 2 ≤ eps ^ 2 ∧
        ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ eps) ∧
    (∀ n : ℕ, OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) ≤ n →
        OCF.S1.loopAux (hbQ m α) (eps ^ 2) n (r0C E m x0 ^ 2) 0
          = OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2)) ∧
    (r0C E m x0 ≤ eps → OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) = 0) ∧
    (r0C E m x0 = 0 → OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) = 0) ∧
    (0 < r0C E m x0 →
      ((OCF.S1.Keps (hbQ m α) (r0C E m x0 ^ 2) (eps ^ 2) : ℕ) : ℤ)
        ≤ max 0 ⌈2 * Real.log (r0C E m x0 / eps) / (α * m)⌉ ∧
      ∀ K : ℕ, max 0 ⌈2 * Real.log (r0C E m x0 / eps) / (α * m)⌉ ≤ (K : ℤ) →
        ‖xK E α (hbBeta m L α) GK x0 K - xs‖ ≤ eps)) :=
  ⟨theoremC_a x0 hm hmL hα hαL hdiff h1a h1b hmin (beck57_holds E L) (bubeck69_holds E m xs) hGK,
   theoremC_b x0 hm hmL hα hαL hdiff h1a h1b hmin (beck57_holds E L) (bubeck69_holds E m xs) hGK,
   theoremC_c x0 hm hmL hα hαL hdiff h1a h1b hmin (beck57_holds E L) (bubeck69_holds E m xs) hGK
     eps heps⟩

end E

end OCF.C1

#print axioms OCF.C1.beta_lt_one
#print axioms OCF.C1.beta_sq
#print axioms OCF.C1.q_eq_zero_iff
#print axioms OCF.C1.q_ge
#print axioms OCF.C1.lam_step
#print axioms OCF.C1.lam_iter
#print axioms OCF.C1.word_iter
#print axioms OCF.C1.lamW_chi
#print axioms OCF.C1.lamW_decay
#print axioms OCF.C1.lamW_iter
#print axioms OCF.C1.beck57_holds
#print axioms OCF.C1.bubeck69_holds
#print axioms OCF.C1.min_unique
#print axioms OCF.C1.dist_chain
#print axioms OCF.C1.theoremC_a
#print axioms OCF.C1.theoremC_b
#print axioms OCF.C1.theoremC_c
#print axioms OCF.C1.theoremC_closed

/-
C2 (Forward–backward residual certificate) — the novel algebraic core of
Proposition C2.5 (the sharp constant κ*), its strictness against the
textbook constant κ_R, the dimension-1 constant max{α, 1/σ}, and the
closed-form algebra of κ_R and α₀.

Source of truth: project_plan/done/proof_audits/C2_fb_residual/01_derivation.md
(stage 3 under overnight delegation 2026-10-10; Prop. C2.5, steps
S5.1–S5.10; Lemma C2.2, step S2.3), adjudication 03_adjudication.md
("Lean tractability", DECISION 7), targeted re-audit 02b_reaudit_C2.md
(Target 2 survives). Landing draft: 04_landing_draft.tex,
Proposition `prop:fb-sharp` (a), (c), (d) and the κ*/α₀ definitions.
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised:
ac47acb42b66d7e3.

DEFINITIONAL MAP (dossier symbol — Lean name):
* σ := σ_f, β, α — real parameters, hypotheses 0 < σ ≤ β, 0 < α
  (σ ≤ β is automatic under H0 + H_sc, B3 `thm:fb`(b)).
* α₀ := √(2/(σ(σ+β))) — `alpha0 σ β`.
* κ*(α) — `kappaStar σ β α`: 1/σ for α ≤ α₀, otherwise
  `kappaStarBranch σ β α` = α·√((α²(σ+β)²/4 − 1)/(α²σβ − 1)).
* κ_R := max{1/σ, α/(2 − αβ)} — `kappaR σ β α`.
* q := max{|1 − ασ|, |1 − αβ|} — `qFactor σ β α`.
* θ* := α/κ*(α) — written `α / kappaStar σ β α`.
* e = x − x*, r = R_α(x), δ = ∇f(x) − ∇f(x*), a = αr, b = αδ — vectors
  in an arbitrary real inner product space V (ℝᵈ with the Euclidean inner
  product is the dossier's case; the statements hold verbatim there).

COVERAGE (target → Lean name):
1. Two-point core of C2.5(a) (S5.3–S5.6): for e, a, b with
   ⟨a − b, e − a⟩ ≥ 0 (G) and ⟨b − ασe, αβe − b⟩ ≥ 0 (F),
   ‖a‖ ≥ θ*‖e‖ — `two_point_core`; in the residual variables of S5.1,
   ⟨r − δ, e − αr⟩ ≥ 0 and ⟨δ − σe, βe − δ⟩ ≥ 0 ⇒ ‖e‖ ≤ κ*‖r‖ —
   `two_point_residual_bound`. Ingredients: (G′) `norm_add_le_of_G`,
   S5.4 + S5.5 per case `scalar_case_small`, `scalar_case_large`.
2. C2.5(c) / `prop:fb-sharp`(d): κ* = κ_R for α ≤ 2/(σ+β) —
   `kappaStar_eq_kappaR`; κ* < κ_R on (2/(σ+β), 2/β), σ = β included —
   `kappaStar_lt_kappaR`; hence κ* ≤ κ_R on (0, 2/β) —
   `kappaStar_le_kappaR`.
3. C2.5(b′) / `prop:fb-sharp`(c), at the two-point level (S5.10):
   1-D bound |e| ≤ max{α, 1/σ}|r| — `dim1_two_point_bound`; the 1-D
   two-point supremum is exactly max{α, 1/σ} — `dim1_two_point_isGreatest`;
   max{α, 1/σ} = κ* if α ≤ α₀ or σ = β — `dim1_eq_kappaStar`;
   max{α, 1/σ} < κ* if α > α₀ and σ < β — `dim1_lt_kappaStar`.
4. Closed forms (S2.3, C2.5 definition): 1 − q = min{ασ, 2 − αβ} —
   `one_sub_qFactor`; κ_R = α/(1 − q) — `kappaR_eq_div_one_sub_q`;
   κ_R = 1/σ ⟺ α ≤ 2/(σ+β) — `kappaR_eq_inv_iff`; α₀ ≥ 2/(σ+β) —
   `two_div_le_alpha0`; α₀ is the threshold where the branches agree:
   `kappaStarBranch_alpha0` (σ < β) and, for α²σβ > 1,
   `kappaStarBranch_eq_inv_iff` (branch value 1/σ ⟺ α = α₀).

NOT FORMALISED (PROSE-ONLY, per the adjudication): the reduction S5.1–S5.2
from (f, g, x) to the two-point inequalities (G), (F) — prox, Γ₀, maximal
monotonicity of ∂g, cocoercivity (B&C Thm 18.15) — and the attainment
witnesses S5.7 / S2.4 as actual (f, g) pairs (they need prox_{ι_Λ} = P_Λ).
Item 3's supremum is therefore the supremum of the two-point relaxation;
its two attaining two-point configurations are exactly the values of the
dossier's (f, g) witnesses (S2.4, S5.7 last bullet).

Status tier: FORMALISED (statement + proof, no sorry) for items 1–4 at the
two-point / closed-form level stated above; the convex-analysis reduction
is PROSE-ONLY.
-/
import Mathlib

open Real

namespace OCF.C2

/-! ## Definitions -/

/-- α₀ := √(2/(σ(σ+β))). -/
noncomputable def alpha0 (σ β : ℝ) : ℝ := √(2 / (σ * (σ + β)))

/-- The large-step branch of κ*: α·√((α²(σ+β)²/4 − 1)/(α²σβ − 1)). -/
noncomputable def kappaStarBranch (σ β α : ℝ) : ℝ :=
  α * √((α ^ 2 * (σ + β) ^ 2 / 4 - 1) / (α ^ 2 * σ * β - 1))

/-- The sharp constant κ*(α) of Proposition C2.5. -/
noncomputable def kappaStar (σ β α : ℝ) : ℝ :=
  if α ≤ alpha0 σ β then 1 / σ else kappaStarBranch σ β α

/-- The textbook constant κ_R = max{1/σ, α/(2 − αβ)} of Lemma C2.2. -/
noncomputable def kappaR (σ β α : ℝ) : ℝ := max (1 / σ) (α / (2 - α * β))

/-- The contraction factor q = max{|1 − ασ|, |1 − αβ|} of Lemma C2.2. -/
noncomputable def qFactor (σ β α : ℝ) : ℝ := max |1 - α * σ| |1 - α * β|

/-! ## Elementary facts about α₀ -/

lemma le_alpha0_iff {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 ≤ α) :
    α ≤ alpha0 σ β ↔ α ^ 2 * σ * (σ + β) ≤ 2 := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  unfold alpha0
  rw [Real.le_sqrt hα (by positivity), le_div_iff₀ (by positivity)]
  constructor <;> intro h <;>
    linarith [show α ^ 2 * (σ * (σ + β)) = α ^ 2 * σ * (σ + β) by ring]

lemma alpha0_pos {σ β : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) : 0 < alpha0 σ β := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  unfold alpha0; positivity

/-- α₀ ≥ 2/(σ+β) (C2.5 definition; used in S5.8). -/
theorem two_div_le_alpha0 {σ β : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) :
    2 / (σ + β) ≤ alpha0 σ β := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  rw [le_alpha0_iff hσ hσβ (by positivity)]
  rw [div_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [mul_pos hσ hβ, sq_nonneg (σ + β)]

/-! ## Item 1: the two-point core inequality -/

/-- Lower bound p ≥ ασ‖e‖² from (F) and Cauchy–Schwarz (the disk of S5.3). -/
lemma p_lower {σ β α n p B : ℝ} (_hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (hF : 0 ≤ α * (σ + β) * p - B - α ^ 2 * σ * β * n ^ 2) (hCS : p ^ 2 ≤ n ^ 2 * B) :
    α * σ * n ^ 2 ≤ p := by
  have h1 : (p - α * (σ + β) / 2 * n ^ 2) ^ 2 ≤ (α * (β - σ) / 2 * n ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg n) hF]
  have hρ : 0 ≤ α * (β - σ) / 2 * n ^ 2 := by
    have : 0 ≤ β - σ := by linarith
    positivity
  have := (abs_le_of_sq_le_sq' h1 hρ).1
  nlinarith

/-- The hyperbola step (S5.4), homogeneous form: if W := p − θ²n² ≥ 0 and
W² ≥ θ²n²v², with u² = v² + 4p, then u − v ≥ 2θn. -/
lemma hyperbola_step {θ n v u p : ℝ} (hθ : 0 ≤ θ) (hn : 0 ≤ n) (hv : 0 ≤ v) (hu : 0 ≤ u)
    (huv : u ^ 2 = v ^ 2 + 4 * p) (hW : 0 ≤ p - θ ^ 2 * n ^ 2)
    (hZ : θ ^ 2 * n ^ 2 * v ^ 2 ≤ (p - θ ^ 2 * n ^ 2) ^ 2) :
    2 * θ * n ≤ u - v := by
  have h1 : θ * n * v ≤ p - θ ^ 2 * n ^ 2 := by
    rw [← sq_le_sq₀ (by positivity) hW]; nlinarith
  have h2 : (v + 2 * θ * n) ^ 2 ≤ u ^ 2 := by nlinarith
  have h3 := (sq_le_sq₀ (by positivity) hu).1 h2
  linarith

/-- S5.5, case α ≤ α₀ (θ = ασ): W ≥ 0 and Z ≥ 0. -/
lemma scalar_case_small {σ β α n p B v : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (hsmall : α ^ 2 * σ * (σ + β) ≤ 2) (_hn : 0 ≤ n)
    (hv : v ^ 2 = n ^ 2 - 2 * p + B)
    (hF : 0 ≤ α * (σ + β) * p - B - α ^ 2 * σ * β * n ^ 2) (hCS : p ^ 2 ≤ n ^ 2 * B) :
    0 ≤ p - (α * σ) ^ 2 * n ^ 2 ∧
      (α * σ) ^ 2 * n ^ 2 * v ^ 2 ≤ (p - (α * σ) ^ 2 * n ^ 2) ^ 2 := by
  have hp := p_lower hσ hσβ hα hF hCS
  have hm0 : 0 < α * σ := by positivity
  have hm2 : (α * σ) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hσ.le) (sub_nonneg.2 hσβ)]
  have hm1 : α * σ ≤ 1 := by nlinarith
  have hmc : 0 ≤ 1 - α * σ * (α * (σ + β) / 2) := by nlinarith
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  refine ⟨by nlinarith [mul_nonneg (mul_nonneg hm0.le (sub_nonneg.2 hm1)) hn2], ?_⟩
  have hB : B ≤ α * (σ + β) * p - α ^ 2 * σ * β * n ^ 2 := by linarith
  have hL : 0 ≤ (p - α * σ * n ^ 2) *
      (p + α * σ * n ^ 2 - 2 * (α * σ) ^ 2 * (α * (σ + β) / 2) * n ^ 2) := by
    apply mul_nonneg (by linarith)
    nlinarith [mul_nonneg (mul_nonneg hm0.le hn2) hmc]
  have hid : (p - (α * σ) ^ 2 * n ^ 2) ^ 2 - (α * σ) ^ 2 * n ^ 2 *
      (n ^ 2 - 2 * p + (α * (σ + β) * p - α ^ 2 * σ * β * n ^ 2)) =
      (p - α * σ * n ^ 2) *
      (p + α * σ * n ^ 2 - 2 * (α * σ) ^ 2 * (α * (σ + β) / 2) * n ^ 2) := by ring
  rw [hv]
  nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ (α * σ) ^ 2 * n ^ 2)]

/-- S5.5, case α > α₀ (θ² = T with T·(c² − 1) = α²σβ − 1): W ≥ 0 and Z ≥ 0. -/
lemma scalar_case_large {σ β α n p B v T : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (hN : 0 < α ^ 2 * (σ + β) ^ 2 / 4 - 1)
    (hT0 : 0 ≤ T) (hTN : T * (α ^ 2 * (σ + β) ^ 2 / 4 - 1) = α ^ 2 * σ * β - 1)
    (_hn : 0 ≤ n) (hv : v ^ 2 = n ^ 2 - 2 * p + B)
    (hF : 0 ≤ α * (σ + β) * p - B - α ^ 2 * σ * β * n ^ 2) (hCS : p ^ 2 ≤ n ^ 2 * B) :
    0 ≤ p - T * n ^ 2 ∧ T * n ^ 2 * v ^ 2 ≤ (p - T * n ^ 2) ^ 2 := by
  have hp := p_lower hσ hσβ hα hF hCS
  have hn2 : 0 ≤ n ^ 2 := sq_nonneg n
  -- m N − D = m (c − 1)² + (m − 1)² ≥ 0, hence T ≤ m = ασ
  have hmND : (α ^ 2 * σ * β - 1) ≤ α * σ * (α ^ 2 * (σ + β) ^ 2 / 4 - 1) := by
    have hid : α * σ * (α ^ 2 * (σ + β) ^ 2 / 4 - 1) - (α ^ 2 * σ * β - 1) =
        α * σ * (α * (σ + β) / 2 - 1) ^ 2 + (α * σ - 1) ^ 2 := by ring
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ α * σ) (sq_nonneg (α * (σ + β) / 2 - 1)),
      sq_nonneg (α * σ - 1)]
  have hTm : T ≤ α * σ := by
    by_contra h
    rw [not_le] at h
    nlinarith [mul_lt_mul_of_pos_right h hN]
  refine ⟨by nlinarith [mul_le_mul_of_nonneg_right hTm hn2], ?_⟩
  have hB : B ≤ α * (σ + β) * p - α ^ 2 * σ * β * n ^ 2 := by linarith
  have hid : (p - T * n ^ 2) ^ 2 - T * n ^ 2 *
      (n ^ 2 - 2 * p + (α * (σ + β) * p - α ^ 2 * σ * β * n ^ 2)) =
      (p - T * (α * (σ + β) / 2) * n ^ 2) ^ 2 := by
    linear_combination (-T * n ^ 4) * hTN
  rw [hv]
  nlinarith [mul_le_mul_of_nonneg_left hB (by positivity : 0 ≤ T * n ^ 2),
    sq_nonneg (p - T * (α * (σ + β) / 2) * n ^ 2)]

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- (G′) of S5.3: ⟨a − b, e − a⟩ ≥ 0 ⇒ ‖e + b‖ − ‖e − b‖ ≤ 2‖a‖. -/
lemma norm_add_le_of_G {e a b : V} (hG : 0 ≤ inner ℝ (a - b) (e - a)) :
    ‖e + b‖ ≤ 2 * ‖a‖ + ‖e - b‖ := by
  have h1 : ‖(2:ℝ) • a - (e + b)‖ ^ 2 = ‖e - b‖ ^ 2 - 4 * inner ℝ (a - b) (e - a) := by
    simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right, inner_add_left,
      inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm a e, real_inner_comm a b, real_inner_comm b e]
    ring
  have h2 : ‖(2:ℝ) • a - (e + b)‖ ≤ ‖e - b‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (by nlinarith)
  have h3 : ‖e + b‖ ≤ ‖(2:ℝ) • a‖ + ‖(2:ℝ) • a - (e + b)‖ := by
    have := norm_sub_le ((2:ℝ) • a) ((2:ℝ) • a - (e + b))
    rwa [sub_sub_cancel] at this
  rw [norm_smul_of_nonneg (by norm_num)] at h3
  linarith

lemma kappaStarBranch_pos {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (hlarge : 2 < α ^ 2 * σ * (σ + β)) : 0 < kappaStarBranch σ β α := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hN : 0 < α ^ 2 * (σ + β) ^ 2 / 4 - 1 := by
    nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg (β - σ))]
  have hD : 0 < α ^ 2 * σ * β - 1 := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hσ.le) (sub_nonneg.2 hσβ)]
  unfold kappaStarBranch
  have := Real.sqrt_pos.2 (div_pos hN hD)
  positivity

lemma kappaStar_pos {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α) :
    0 < kappaStar σ β α := by
  unfold kappaStar
  split_ifs with h
  · positivity
  · rw [le_alpha0_iff hσ hσβ hα.le] at h
    exact kappaStarBranch_pos hσ hσβ hα (lt_of_not_ge h)

/-- **Item 1 (two-point core of Prop. C2.5(a)).** For e, a, b in a real inner
product space with (G) ⟨a − b, e − a⟩ ≥ 0 and (F) ⟨b − ασe, αβe − b⟩ ≥ 0,
‖a‖ ≥ θ*‖e‖ with θ* = α/κ*(α), for every α > 0 and 0 < σ ≤ β. -/
theorem two_point_core {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α) {e a b : V}
    (hG : 0 ≤ inner ℝ (a - b) (e - a))
    (hF : 0 ≤ inner ℝ (b - (α * σ) • e) ((α * β) • e - b)) :
    α / kappaStar σ β α * ‖e‖ ≤ ‖a‖ := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hFs : 0 ≤ α * (σ + β) * inner ℝ e b - ‖b‖ ^ 2 - α ^ 2 * σ * β * ‖e‖ ^ 2 := by
    have : inner ℝ (b - (α * σ) • e) ((α * β) • e - b) =
        α * (σ + β) * inner ℝ e b - ‖b‖ ^ 2 - α ^ 2 * σ * β * ‖e‖ ^ 2 := by
      simp only [← real_inner_self_eq_norm_sq, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right]
      rw [real_inner_comm e b]; ring
    linarith
  have hCS : inner ℝ e b ^ 2 ≤ ‖e‖ ^ 2 * ‖b‖ ^ 2 := by
    have h := abs_real_inner_le_norm e b
    have h' := sq_le_sq' (abs_le.1 h).1 (abs_le.1 h).2
    rw [mul_pow] at h'; exact h'
  have hv : ‖e - b‖ ^ 2 = ‖e‖ ^ 2 - 2 * inner ℝ e b + ‖b‖ ^ 2 := norm_sub_sq_real e b
  have hu : ‖e + b‖ ^ 2 = ‖e - b‖ ^ 2 + 4 * inner ℝ e b := by
    rw [norm_add_sq_real, hv]; ring
  have hGp := norm_add_le_of_G hG
  have key : ∀ θ : ℝ, 0 ≤ θ → 0 ≤ inner ℝ e b - θ ^ 2 * ‖e‖ ^ 2 →
      θ ^ 2 * ‖e‖ ^ 2 * ‖e - b‖ ^ 2 ≤ (inner ℝ e b - θ ^ 2 * ‖e‖ ^ 2) ^ 2 →
      θ * ‖e‖ ≤ ‖a‖ := by
    intro θ hθ hW hZ
    have := hyperbola_step hθ (norm_nonneg e) (norm_nonneg _) (norm_nonneg _) hu hW hZ
    linarith
  unfold kappaStar
  split_ifs with h
  · rw [le_alpha0_iff hσ hσβ hα.le] at h
    obtain ⟨hW, hZ⟩ := scalar_case_small hσ hσβ hα h (norm_nonneg e) hv hFs hCS
    rw [show α / (1 / σ) = α * σ by field_simp]
    exact key _ (by positivity) hW hZ
  · rw [le_alpha0_iff hσ hσβ hα.le] at h
    have hlarge : 2 < α ^ 2 * σ * (σ + β) := lt_of_not_ge h
    set N := α ^ 2 * (σ + β) ^ 2 / 4 - 1 with hNdef
    set D := α ^ 2 * σ * β - 1 with hDdef
    have hN : 0 < N := by nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg (β - σ))]
    have hD : 0 < D := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hσ.le) (sub_nonneg.2 hσβ)]
    have hs : 0 < √(N / D) := Real.sqrt_pos.2 (div_pos hN hD)
    have hθ : α / kappaStarBranch σ β α = 1 / √(N / D) := by
      show α / (α * √(N / D)) = 1 / √(N / D)
      rw [div_mul_eq_div_div, div_self hα.ne']
    have hTN : (1 / √(N / D)) ^ 2 * N = D := by
      rw [div_pow, Real.sq_sqrt (div_pos hN hD).le]; field_simp
    obtain ⟨hW, hZ⟩ := scalar_case_large (T := (1 / √(N / D)) ^ 2) hσ hσβ hα hN
      (by positivity) hTN (norm_nonneg e) hv hFs hCS
    rw [hθ]
    exact key _ (by positivity) hW hZ

/-- **Item 1, residual form (S5.1 ⇒ C2.5(a)).** If r, δ, e satisfy the two
two-point inequalities of S5.1–S5.2, (G) ⟨r − δ, e − αr⟩ ≥ 0 and
(F) ⟨δ − σe, βe − δ⟩ ≥ 0, then ‖e‖ ≤ κ*(α)‖r‖. With e = x − x*,
r = R_α(x), δ = ∇f(x) − ∇f(x*) this is ‖x − x*‖ ≤ κ*(α)‖R_α(x)‖. -/
theorem two_point_residual_bound {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    {e r δ : V} (hG : 0 ≤ inner ℝ (r - δ) (e - α • r))
    (hF : 0 ≤ inner ℝ (δ - σ • e) (β • e - δ)) :
    ‖e‖ ≤ kappaStar σ β α * ‖r‖ := by
  have hG' : 0 ≤ inner ℝ (α • r - α • δ) (e - α • r) := by
    rw [← smul_sub, real_inner_smul_left]; positivity
  have hF' : 0 ≤ inner ℝ (α • δ - (α * σ) • e) ((α * β) • e - α • δ) := by
    rw [mul_smul, mul_smul, ← smul_sub, ← smul_sub, real_inner_smul_left,
      real_inner_smul_right]
    positivity
  have h := two_point_core hσ hσβ hα hG' hF'
  rw [norm_smul_of_nonneg hα.le] at h
  have hk := kappaStar_pos (β := β) hσ hσβ hα
  rw [div_mul_eq_mul_div, div_le_iff₀ hk] at h
  nlinarith

/-- Item 1 specialised to ℝᵈ with the Euclidean inner product (the dossier's
setting). -/
theorem two_point_residual_bound_euclidean {d : ℕ} {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β)
    (hα : 0 < α) {e r δ : EuclideanSpace ℝ (Fin d)}
    (hG : 0 ≤ inner ℝ (r - δ) (e - α • r))
    (hF : 0 ≤ inner ℝ (δ - σ • e) (β • e - δ)) :
    ‖e‖ ≤ kappaStar σ β α * ‖r‖ :=
  two_point_residual_bound hσ hσβ hα hG hF

/-! ## Item 4: closed-form algebra -/

/-- S2.3: 1 − q = min{ασ, 2 − αβ} on (0, 2/β). -/
theorem one_sub_qFactor {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (_h2 : α < 2 / β) : 1 - qFactor σ β α = min (α * σ) (2 - α * β) := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hsb : α * σ ≤ α * β := mul_le_mul_of_nonneg_left hσβ hα.le
  have hq : qFactor σ β α = max (1 - α * σ) (α * β - 1) := by
    unfold qFactor
    apply le_antisymm
    · apply max_le
      · rw [abs_le]; constructor
        · linarith [le_max_right (1 - α * σ) (α * β - 1)]
        · exact le_max_left _ _
      · rw [abs_le]; constructor
        · linarith [le_max_right (1 - α * σ) (α * β - 1)]
        · linarith [le_max_left (1 - α * σ) (α * β - 1)]
    · apply max_le
      · exact (le_abs_self _).trans (le_max_left _ _)
      · have : α * β - 1 ≤ |1 - α * β| := by
          rw [show α * β - 1 = -(1 - α * β) by ring]; exact neg_le_abs _
        exact this.trans (le_max_right _ _)
  rw [hq]
  rcases le_total (1 - α * σ) (α * β - 1) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring

/-- S2.3: κ_R = α/(1 − q) on (0, 2/β). -/
theorem kappaR_eq_div_one_sub_q {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (h2 : α < 2 / β) : kappaR σ β α = α / (1 - qFactor σ β α) := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hb2 : α * β < 2 := by rwa [lt_div_iff₀ hβ] at h2
  rw [one_sub_qFactor hσ hσβ hα h2]
  unfold kappaR
  have h2b : 0 < 2 - α * β := by linarith
  rcases le_total (α * σ) (2 - α * β) with h | h
  · rw [min_eq_left h, max_eq_left]
    · field_simp
    · rw [div_le_div_iff₀ h2b hσ]; nlinarith
  · rw [min_eq_right h, max_eq_right]
    rw [div_le_div_iff₀ hσ h2b]; nlinarith

/-- S2.3: κ_R = 1/σ ⟺ α ≤ 2/(σ+β) (for α ∈ (0, 2/β)). -/
theorem kappaR_eq_inv_iff {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (_hα : 0 < α)
    (h2 : α < 2 / β) : kappaR σ β α = 1 / σ ↔ α ≤ 2 / (σ + β) := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hb2 : α * β < 2 := by rwa [lt_div_iff₀ hβ] at h2
  have h2b : 0 < 2 - α * β := by linarith
  unfold kappaR
  rw [max_eq_left_iff, div_le_div_iff₀ h2b hσ, le_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- Key identity: σ²α²N − D = (α²σ(σ+β)/2 − 1)², N = α²(σ+β)²/4 − 1,
D = α²σβ − 1. -/
lemma branch_identity (σ β α : ℝ) :
    (α * σ) ^ 2 * (α ^ 2 * (σ + β) ^ 2 / 4 - 1) - (α ^ 2 * σ * β - 1) =
      (α ^ 2 * σ * (σ + β) / 2 - 1) ^ 2 := by ring

/-- α₀ is where the branches of κ* agree: for α with α²σβ > 1, the large-step
branch equals 1/σ iff α = α₀. -/
theorem kappaStarBranch_eq_inv_iff {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (hD : 1 < α ^ 2 * σ * β) : kappaStarBranch σ β α = 1 / σ ↔ α = alpha0 σ β := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hD' : 0 < α ^ 2 * σ * β - 1 := by linarith
  have hN : 0 < α ^ 2 * (σ + β) ^ 2 / 4 - 1 := by
    nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg (β - σ))]
  have hiff : kappaStarBranch σ β α = 1 / σ ↔
      (α * σ) ^ 2 * (α ^ 2 * (σ + β) ^ 2 / 4 - 1) = α ^ 2 * σ * β - 1 := by
    unfold kappaStarBranch
    have hs := Real.sqrt_pos.2 (div_pos hN hD')
    constructor
    · intro h
      have h2 : (α * √((α ^ 2 * (σ + β) ^ 2 / 4 - 1) / (α ^ 2 * σ * β - 1))) ^ 2 =
          (1 / σ) ^ 2 := by rw [h]
      rw [mul_pow, Real.sq_sqrt (div_pos hN hD').le] at h2
      field_simp at h2
      linarith
    · intro h
      refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
      rw [mul_pow, Real.sq_sqrt (div_pos hN hD').le]
      field_simp
      linarith
  rw [hiff]
  have hid := branch_identity σ β α
  constructor
  · intro h
    have h0 : (α ^ 2 * σ * (σ + β) / 2 - 1) ^ 2 = 0 := by linarith
    have h1 : α ^ 2 * σ * (σ + β) = 2 := by
      have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h0
      linarith
    unfold alpha0
    rw [show 2 / (σ * (σ + β)) = α ^ 2 by
      field_simp; linarith]
    exact (Real.sqrt_sq hα.le).symm
  · intro h
    have h1 : α ^ 2 * σ * (σ + β) = 2 := by
      have := Real.sq_sqrt (show (0:ℝ) ≤ 2 / (σ * (σ + β)) by positivity)
      rw [← alpha0, ← h] at this
      rw [this]; field_simp
    have : (α ^ 2 * σ * (σ + β) / 2 - 1) ^ 2 = 0 := by rw [h1]; norm_num
    linarith

/-- At α = α₀ (σ < β) the large-step branch equals 1/σ: κ* is continuous at
the threshold α₀. -/
theorem kappaStarBranch_alpha0 {σ β : ℝ} (hσ : 0 < σ) (hσβ : σ < β) :
    kappaStarBranch σ β (alpha0 σ β) = 1 / σ := by
  have hβ : 0 < β := hσ.trans hσβ
  have ha := alpha0_pos hσ hσβ.le
  have hsq : alpha0 σ β ^ 2 = 2 / (σ * (σ + β)) := by
    unfold alpha0; rw [Real.sq_sqrt (by positivity)]
  refine (kappaStarBranch_eq_inv_iff hσ hσβ.le ha ?_).2 rfl
  rw [hsq, div_mul_eq_mul_div, div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos hσ (sub_pos.2 hσβ)]

/-! ## Item 2: κ* versus κ_R -/

/-- C2.5(c), equality part: κ* = κ_R for 0 < α ≤ 2/(σ+β). -/
theorem kappaStar_eq_kappaR {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (h : α ≤ 2 / (σ + β)) : kappaStar σ β α = kappaR σ β α := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hα0 : α ≤ alpha0 σ β := h.trans (two_div_le_alpha0 hσ hσβ)
  have h2 : α < 2 / β := by
    refine h.trans_lt ?_
    rw [div_lt_div_iff₀ (by positivity) hβ]; nlinarith
  unfold kappaStar
  rw [if_pos hα0, (kappaR_eq_inv_iff hσ hσβ hα h2).2 h]

/-- **Item 2 (C2.5(c), strictness; S5.8 incl. the ρ = 0 case σ = β).**
κ* < κ_R on (2/(σ+β), 2/β). -/
theorem kappaStar_lt_kappaR {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β)
    (h1 : 2 / (σ + β) < α) (h2 : α < 2 / β) : kappaStar σ β α < kappaR σ β α := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  have hα : 0 < α := lt_trans (by positivity) h1
  have hb2 : α * β < 2 := by rwa [lt_div_iff₀ hβ] at h2
  have hsb : 2 < α * (σ + β) := by
    rw [div_lt_iff₀ (by positivity)] at h1; linarith [mul_comm (σ + β) α]
  have h2b : 0 < 2 - α * β := by linarith
  unfold kappaStar kappaR
  split_ifs with h
  · -- κ* = 1/σ < α/(2 − αβ)
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    rw [div_lt_div_iff₀ hσ h2b]; nlinarith
  · rw [le_alpha0_iff hσ hσβ hα.le] at h
    have hlarge : 2 < α ^ 2 * σ * (σ + β) := lt_of_not_ge h
    refine lt_of_lt_of_le ?_ (le_max_right _ _)
    -- notation of S5.8
    set c := α * (σ + β) / 2 with hc
    set ρ := α * (β - σ) / 2 with hρ
    set s := α * β with hs
    have hρ0 : 0 ≤ ρ := by have : 0 ≤ β - σ := by linarith
                           positivity
    have hmc : 1 < α * σ * c := by rw [hc]; nlinarith
    have hss : σ * (σ + β) ≤ 2 * β ^ 2 := by nlinarith
    have hs1 : 1 < s := by
      have : 1 < s ^ 2 := by
        rw [hs]; nlinarith [mul_le_mul_of_nonneg_left hss (sq_nonneg α)]
      nlinarith
    have hc1 : 1 < c := by
      have hcm : α * σ ≤ c := by rw [hc]; nlinarith
      have hc0 : 0 < c := by positivity
      nlinarith
    set N := α ^ 2 * (σ + β) ^ 2 / 4 - 1 with hN
    set D := α ^ 2 * σ * β - 1 with hD
    have hDpos : 0 < D := by
      nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hσ.le) (sub_nonneg.2 hσβ)]
    have hNpos : 0 < N := by nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg (β - σ))]
    -- F := D − N(2 − s)² > 0
    have hFid : D - N * (2 - s) ^ 2 =
        (α * σ * c - 1) * (s - 1) * (3 - s) + ρ * ((c * (3 - s) - 1) * (s - 1) + (c - 1)) := by
      rw [hD, hN, hc, hρ, hs]; ring
    have hpos1 : 0 < (α * σ * c - 1) * (s - 1) * (3 - s) := by
      apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    have hpos2 : 0 ≤ ρ * ((c * (3 - s) - 1) * (s - 1) + (c - 1)) := by
      apply mul_nonneg hρ0
      have : 0 < c * (3 - s) - 1 := by nlinarith
      nlinarith
    have hF : N * (2 - s) ^ 2 < D := by linarith
    unfold kappaStarBranch
    rw [← hN, ← hD]
    have hsqrt : √(N / D) < 1 / (2 - s) := by
      rw [Real.sqrt_lt' (by positivity), div_pow, one_pow,
        div_lt_div_iff₀ hDpos (by positivity)]
      linarith
    calc α * √(N / D) < α * (1 / (2 - s)) := mul_lt_mul_of_pos_left hsqrt hα
      _ = α / (2 - α * β) := by rw [hs]; ring

/-- C2.5(c): κ* ≤ κ_R on (0, 2/β). -/
theorem kappaStar_le_kappaR {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (h2 : α < 2 / β) : kappaStar σ β α ≤ kappaR σ β α := by
  rcases le_or_gt α (2 / (σ + β)) with h | h
  · exact (kappaStar_eq_kappaR hσ hσβ hα h).le
  · exact (kappaStar_lt_kappaR hσ hσβ h h2).le

/-! ## Item 3: dimension 1 -/

lemma dim1_nonneg_case {σ β α e r δ : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (he : 0 ≤ e) (hG : 0 ≤ (r - δ) * (e - α * r)) (hF : 0 ≤ (δ - σ * e) * (β * e - δ)) :
    e ≤ max α (1 / σ) * r := by
  have hM1 : α ≤ max α (1 / σ) := le_max_left _ _
  have hM2 : 1 / σ ≤ max α (1 / σ) := le_max_right _ _
  have hδ : σ * e ≤ δ := by
    by_contra h
    rw [not_le] at h
    have h' : 0 < β * e - δ := by nlinarith
    nlinarith [mul_pos (sub_pos.2 h) h']
  rcases le_or_gt e (α * r) with h | h
  · have hr : 0 ≤ r := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hM1 hr]
  · have hrδ : δ ≤ r := by
      by_contra h''
      rw [not_le] at h''
      nlinarith [mul_pos (sub_pos.2 h'') (sub_pos.2 h)]
    have hr : 0 ≤ r := by nlinarith
    have : e ≤ 1 / σ * r := by rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hσ]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hM2 hr]

/-- **Item 3, upper bound (S5.10).** In dimension 1, (G) (r − δ)(e − αr) ≥ 0
and (F) (δ − σe)(βe − δ) ≥ 0 give |e| ≤ max{α, 1/σ}|r|. -/
theorem dim1_two_point_bound {σ β α e r δ : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (hG : 0 ≤ (r - δ) * (e - α * r)) (hF : 0 ≤ (δ - σ * e) * (β * e - δ)) :
    |e| ≤ max α (1 / σ) * |r| := by
  have hM : 0 ≤ max α (1 / σ) := le_trans hα.le (le_max_left _ _)
  rcases le_total 0 e with he | he
  · have := dim1_nonneg_case hσ hσβ hα he hG hF
    rw [abs_of_nonneg he]
    exact this.trans (mul_le_mul_of_nonneg_left (le_abs_self r) hM)
  · have := dim1_nonneg_case (e := -e) (r := -r) (δ := -δ) hσ hσβ hα (by linarith)
      (by nlinarith) (by nlinarith)
    rw [abs_of_nonpos he]
    exact (by linarith : -e ≤ max α (1 / σ) * -r).trans
      (mul_le_mul_of_nonneg_left (neg_le_abs r) hM)

/-- **Item 3, supremum (two-point level).** The supremum of |e|/|r| over the
one-dimensional two-point configurations (G), (F) with e ≠ 0 is max{α, 1/σ},
and it is attained. -/
theorem dim1_two_point_isGreatest {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α) :
    IsGreatest {k : ℝ | ∃ e r δ : ℝ, e ≠ 0 ∧ 0 ≤ (r - δ) * (e - α * r) ∧
      0 ≤ (δ - σ * e) * (β * e - δ) ∧ k = |e| / |r|} (max α (1 / σ)) := by
  constructor
  · rcases le_total α (1 / σ) with h | h
    · refine ⟨1, σ, σ, one_ne_zero, by simp, by simp, ?_⟩
      rw [max_eq_right h, abs_one, abs_of_pos hσ]
    · refine ⟨1, 1 / α, σ, one_ne_zero, ?_, by simp, ?_⟩
      · field_simp; simp
      · rw [max_eq_left h, abs_one, abs_of_pos (by positivity)]; field_simp
  · rintro k ⟨e, r, δ, -, hG, hF, rfl⟩
    have hb := dim1_two_point_bound hσ hσβ hα hG hF
    have hM : 0 ≤ max α (1 / σ) := le_trans hα.le (le_max_left _ _)
    rcases eq_or_lt_of_le (abs_nonneg r) with hr | hr
    · rw [← hr, div_zero]; exact hM
    · rw [div_le_iff₀ hr]; exact hb

/-- Item 3, comparison: max{α, 1/σ} = κ* if α ≤ α₀ or σ = β. -/
theorem dim1_eq_kappaStar {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ ≤ β) (hα : 0 < α)
    (h : α ≤ alpha0 σ β ∨ σ = β) : max α (1 / σ) = kappaStar σ β α := by
  have hβ : 0 < β := lt_of_lt_of_le hσ hσβ
  unfold kappaStar
  split_ifs with h0
  · rw [le_alpha0_iff hσ hσβ hα.le] at h0
    apply max_eq_right
    rw [le_div_iff₀ hσ]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hσ.le) (sub_nonneg.2 hσβ)]
  · rcases h with h | h
    · exact absurd h h0
    · subst h
      rw [le_alpha0_iff hσ hσβ hα.le] at h0
      have hgt2 : 1 < (α * σ) ^ 2 := by nlinarith
      have hgt : 1 < α * σ := by nlinarith [mul_pos hα hσ]
      unfold kappaStarBranch
      have hD : 0 < α ^ 2 * σ * σ - 1 := by nlinarith
      rw [show α ^ 2 * (σ + σ) ^ 2 / 4 - 1 = α ^ 2 * σ * σ - 1 by ring, div_self hD.ne',
        Real.sqrt_one, mul_one]
      apply max_eq_left
      rw [div_le_iff₀ hσ]; linarith

/-- **Item 3, strict gap (S5.10).** For α > α₀ and σ < β,
max{α, 1/σ} < κ*(α). -/
theorem dim1_lt_kappaStar {σ β α : ℝ} (hσ : 0 < σ) (hσβ : σ < β) (hα : alpha0 σ β < α) :
    max α (1 / σ) < kappaStar σ β α := by
  have hβ : 0 < β := hσ.trans hσβ
  have hα0 := alpha0_pos hσ hσβ.le
  have hαpos : 0 < α := hα0.trans hα
  have h0 : ¬ α ≤ alpha0 σ β := not_le.2 hα
  have hlarge : 2 < α ^ 2 * σ * (σ + β) := by
    rw [le_alpha0_iff hσ hσβ.le hαpos.le] at h0; exact lt_of_not_ge h0
  unfold kappaStar
  rw [if_neg h0]
  unfold kappaStarBranch
  set N := α ^ 2 * (σ + β) ^ 2 / 4 - 1 with hN
  set D := α ^ 2 * σ * β - 1 with hD
  have hDpos : 0 < D := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg α) hσ.le) (sub_nonneg.2 hσβ.le)]
  have hNpos : 0 < N := by nlinarith [mul_nonneg (sq_nonneg α) (sq_nonneg (β - σ))]
  rw [max_lt_iff]
  constructor
  · -- α < α √(N/D) ⟸ D < N ⟸ ρ² > 0
    have h1 : 1 < √(N / D) := by
      rw [Real.lt_sqrt zero_le_one, one_pow, lt_div_iff₀ hDpos, one_mul]
      have : 0 < (β - σ) ^ 2 := by have := sub_pos.2 hσβ; positivity
      nlinarith [mul_pos (pow_pos hαpos 2) this]
    nlinarith
  · -- 1/σ < α √(N/D) ⟸ D < (ασ)² N ⟸ (α²σ(σ+β)/2 − 1)² > 0
    have hid := branch_identity σ β α
    have hsq : 0 < (α ^ 2 * σ * (σ + β) / 2 - 1) ^ 2 := by
      have : 0 < α ^ 2 * σ * (σ + β) / 2 - 1 := by linarith
      positivity
    have h1 : 1 / (α * σ) < √(N / D) := by
      rw [Real.lt_sqrt (by positivity), div_pow, one_pow,
        div_lt_div_iff₀ (by positivity) hDpos, one_mul]
      rw [← hN, ← hD] at hid
      nlinarith
    calc 1 / σ = α * (1 / (α * σ)) := by field_simp
      _ < α * √(N / D) := mul_lt_mul_of_pos_left h1 hαpos

end OCF.C2

/-! ## Axiom audit -/
#print axioms OCF.C2.two_point_core
#print axioms OCF.C2.two_point_residual_bound
#print axioms OCF.C2.two_point_residual_bound_euclidean
#print axioms OCF.C2.kappaStar_eq_kappaR
#print axioms OCF.C2.kappaStar_lt_kappaR
#print axioms OCF.C2.kappaStar_le_kappaR
#print axioms OCF.C2.dim1_two_point_bound
#print axioms OCF.C2.dim1_two_point_isGreatest
#print axioms OCF.C2.dim1_eq_kappaStar
#print axioms OCF.C2.dim1_lt_kappaStar
#print axioms OCF.C2.one_sub_qFactor
#print axioms OCF.C2.kappaR_eq_div_one_sub_q
#print axioms OCF.C2.kappaR_eq_inv_iff
#print axioms OCF.C2.two_div_le_alpha0
#print axioms OCF.C2.kappaStarBranch_eq_inv_iff
#print axioms OCF.C2.kappaStarBranch_alpha0

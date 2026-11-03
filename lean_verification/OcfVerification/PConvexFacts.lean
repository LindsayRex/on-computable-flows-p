/-
PConvexFacts (card 22) — the classical convex-analysis facts that the G3, H2, H3 and H4 Lean files
take as hypotheses, proved: the proximal characterisation, existence and uniqueness of the
proximal point, existence and uniqueness of a minimiser of a strongly convex lsc sum, and four
discharge corollaries that restate one headline theorem of each file with the classical
hypothesis replaced by primitive hypotheses.

CLASSICAL, NOT NOVEL.  Every statement here is textbook: Bauschke and Combettes, Convex Analysis
and Monotone Operator Theory in Hilbert Spaces, 2nd ed. (2017): prox definition Def. 12.23,
existence and uniqueness Prop. 12.15, characterisation Prop. 16.44, minimisers Cor. 11.17
(all four VERIFIED on the shelf copy: Def. 12.23 p. 211, Prop. 12.15 p. 208, Prop. 16.44 p. 276,
Cor. 11.17 p. 194; records in Background Research/prior_art/canonical_textbooks/WANTED.md).
This file exists so that the existing files' hypotheses can be shown satisfiable, not to claim
anything new.  The proofs are written from scratch; the optlib files (Apache 2.0) were consulted
for statements only and no proof is ported.

ENCODING (reused, never redefined).  An extended-valued convex g : X -> R u {+inf} is the pair
(D, g): D = dom g, g its values on D.  `ExtSub D g σ p v` (H3), `ExtModC D g σ` (H3; `ModCD` of
H2 is the same predicate, `ModC` of G3 is `ExtModC univ`), `LscExt D g` (H2: every sublevel set
{x in D | g x <= c} is closed), `ProxEps D g α ε y z` and `EpsSubgrad` (H2), `ProxChar D g α P`
(G3), `IsMinE` (H4).  Note `ExtModC D g σ` already contains convexity of D (it is `ConvexOn`).

DEFINITIONAL MAP (symbol -- Lean):
* prox_{αg}(y) = argmin_{x in D} g x + (1/(2α))‖x − y‖²  --  `proxMap D g α y` (Classical.choose
  of the A2 existence statement; junk value y when no minimiser exists).
* q = prox_{αg} y  <=>  (y − q)/α in ∂g(q)  --  `prox_char` (A1), `ProxChar D g α (proxMap D g α)`
  (A3, `proxChar_proxMap`).
* exact proximal inclusion of H2 (ε = 0)  --  `ProxEps D g α 0 y z`; `exists_proxEps_zero`,
  `proxMap_proxEps`.
* x* in argmin_D (f + g)  --  `xs ∈ D ∧ ∀ w ∈ D, f xs + g xs ≤ f w + g w` (A4); H3's
  `EIt`, H4's `IsMinE` are this statement for their E.

COVERAGE (all FORMALISED: statement and proof, no sorry; hypotheses stated exactly):
* A1 `prox_char` — any real inner product space X, no completeness, no properness.
  Hypotheses: `ExtModC D g 0` (g convex on convex D), α > 0.  Statement:
  (q ∈ D ∧ ∀ x ∈ D, g q + 1/(2α)‖q − y‖² ≤ g x + 1/(2α)‖x − y‖²) <-> `ExtSub D g 0 q (α⁻¹ • (y − q))`.
  (The ← direction does not use convexity.)  No lower semicontinuity, no nonemptiness needed.
* A2 `prox_exists_unique` — [ProperSpace X].  Hypotheses: `D.Nonempty`, `LscExt D g`,
  `ExtModC D g 0` (which includes `Convex ℝ D`), α > 0.  Conclusion: `∃! q`, minimiser as in A1.
  Core: `exists_unique_min` (any `Φ` with closed sublevel sets on a nonempty D and
  `ExtModC D Φ m`, m > 0, has exactly one minimiser on D); coercivity is proved from strong
  convexity along the segment to a base point (no affine minorant), using the minimum of Φ over
  the compact set {x ∈ D | Φ x ≤ Φ x₀} ∩ closedBall x₀ 1 (`exists_min_compact`).
* A3 `proxChar_proxMap` (G3's `ProxChar` for `proxMap`), `exists_proxEps_zero` and
  `proxMap_proxEps` (H2's exact prox point for every y).  Same hypotheses as A2.
* A4 `exists_unique_min_add_gen` (f continuous with `ModC f σf`, `ExtModC D g σg`, σf + σg > 0),
  `exists_unique_min_add` (σg = 0 form with σ > 0), `exists_unique_min_add_diff` (f
  differentiable).  [ProperSpace X]; `D.Nonempty`, `LscExt D g`.  Conclusion `∃! xs, xs ∈ D ∧ ∀ w ∈ D,
  f xs + g xs ≤ f w + g w`.  The general (σf, σg) split is added beyond the brief because the
  regime-B and consensus theorems have the curvature on g.
* A5 discharge corollaries (originals untouched):
  - G3: `soundness_prox_of_primitive` (original `OCF.G3P.soundness_prox`).  Prox field of
    `NDecl.Valid` discharged; assumed: σg ≥ 0, `ExtModC Dg g σg`, `Dg.Nonempty`, `LscExt Dg g`,
    plus all the original smooth-side hypotheses.  Conclusion `ProxConclusions` with the prox
    program `proxMap Dg g (1/β̂)`.
  - H2: `E4a_of_primitive` (original `OCF.H2.E4a`).  `hP`, `hxs`, `hmin` discharged; assumed:
    `D.Nonempty`, `LscExt D g`, `ModCD D g σg`, σg ≥ 0, the regime (`Regime β σf σg q`,
    which forces σf + σg > 0), `f` differentiable, `ModC f σf`, `LipGrad f β`, an inexact run.
    Conclusion: a minimiser exists and the two contraction inequalities of E4a hold for it.
  - H3: `cert_iter_of_primitive` (original `OCF.H3.ConsIter.cert_iter`).  The bundle
    `Realises` and the hypotheses `hxs`, `hmin` discharged: the iteration's prox programs are
    stated to BE `proxMap` (hypotheses `C.prox0 = proxMap D0 g0 C.α`,
    `C.prox j = proxMap univ (gj j) (mP ι * C.α)`).  The other fields of `Typed` stay assumed,
    as separate hypotheses: `diffF`, `curvF`, `curv0`, `sigma0`, `curv`, `sigma`, `lip`; added:
    `D0.Nonempty`, `LscExt D0 g0` (the g_j are continuous by `lip`).  Not discharged in H3:
    `apriori_rate`'s Fermat/sum-rule inclusion u*_j and the Krasnosel'skii-Mann bound `hKM`.
  - H4: `H4_7_b_of_primitive` (original `OCF.H4.Run.H4_7_b`).  `IsMinE` discharged; assumed: `SD`
    (as in the original), every `D l` nonempty, every `g l` lsc on `D l`, blocks finite
    dimensional (so `PiLp 2 Y` is proper).  Supporting: `lscExt_gsum`, `lscExt_finset_sum`,
    `lscExt_add_two` (closed-sublevel lsc is closed under finite sums on the intersection of the
    domains).
* Supporting algebra: `norm_convex_comb_sq`, `strongConv_of_extModC`, `extModC_add`,
  `extModC_sum`, `extModC_quad`, `extModC_zero_of_nonneg`, `lscExt_add_continuous`.

GENERALITY.  A1: any real inner product space.  A2, A3, A4 and all of A5: [ProperSpace X]
(finite dimension; every instantiated statement of the paper lives in Vec d =
EuclideanSpace ℝ (Fin d)); fails in infinite dimension without a weak-compactness argument,
not attempted.

NOT FORMALISED: existence of a minimiser of f + g when the total curvature is not positive
(B&C Cor. 11.17 under mere coercivity, e.g. H2 (E3), which assumes only f convex and an
existing minimiser; the minimiser there is not guaranteed and stays a hypothesis);
the other headline theorems of each file (only one per file restated); Fermat/sum rule of H3 T2.

STATUS: COMPLETE.  Status tier: FORMALISED (statement + proof, no sorry) for A1–A4 and the
four discharge corollaries of A5.  Axioms: only propext, Classical.choice, Quot.sound (see the
`#print axioms` at the end).
-/
import Mathlib
import OcfVerification.G3SoundnessProx
import OcfVerification.H2InexactOracles
import OcfVerification.H3MultiNonsmooth
import OcfVerification.H4BlockStitching

namespace OCF.PCF

open Set Filter Topology OCF.A1 OCF.G3 OCF.G3P OCF.H3
open OCF.H2 (EpsSubgrad ProxEps LscExt ModCD)

set_option linter.unusedSectionVars false

section Generic

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The norm identity for a convex combination (a + b = 1). -/
lemma norm_convex_comb_sq {a b : ℝ} (hab : a + b = 1) (x y : X) :
    ‖a • x + b • y‖ ^ 2 = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  have hb : b = 1 - a := by linarith
  subst hb
  have h1 : a • x + (1 - a) • y = y + a • (x - y) := by module
  rw [h1, norm_add_sq_real, norm_smul, inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs]
  have h2 : ‖x‖ ^ 2 = ‖(x - y) + y‖ ^ 2 := by congr 2; abel
  rw [h2, norm_add_sq_real, real_inner_comm y (x - y)]
  ring

/-- Strong convexity inequality extracted from `ExtModC D Φ m`. -/
lemma strongConv_of_extModC {D : Set X} {Φ : X → ℝ} {m : ℝ} (h : ExtModC D Φ m) :
    ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      Φ (a • x + b • y) ≤ a * Φ x + b * Φ y - m / 2 * (a * b * ‖x - y‖ ^ 2) := by
  intro x hx y hy a b ha hb hab
  have := h.2 hx hy ha hb hab
  simp only [smul_eq_mul] at this
  rw [norm_convex_comb_sq hab] at this
  nlinarith

/-! ## A1. The prox characterisation (B&C Prop. 16.44) -/

/-- Convexity of `g` on `D`, in the form used below (`ExtModC D g 0`). -/
lemma convexOn_of_extModC_zero {D : Set X} {g : X → ℝ} (h : ExtModC D g 0) : ConvexOn ℝ D g := by
  have : (fun x => g x - 0 / 2 * ‖x‖ ^ 2) = g := by funext x; ring
  unfold ExtModC at h
  rwa [this] at h

/-- `ExtSub D g 0 p v` is the subgradient inequality. -/
lemma extSub_zero_iff {D : Set X} {g : X → ℝ} {p v : X} :
    ExtSub D g 0 p v ↔ p ∈ D ∧ ∀ y ∈ D, g p + inner ℝ v (y - p) ≤ g y := by
  unfold ExtSub
  simp

/-- **A1. Prox characterisation** [B&C 2017, Def. 12.23 with Prop. 16.44]: `q` minimises
`g + (1/(2α))‖· − y‖²` over `D` iff `(y − q)/α ∈ ∂g(q)`. -/
theorem prox_char {D : Set X} {g : X → ℝ} (hg : ExtModC D g 0) {α : ℝ} (hα : 0 < α) (y q : X) :
    (q ∈ D ∧ ∀ x ∈ D, g q + 1 / (2 * α) * ‖q - y‖ ^ 2 ≤ g x + 1 / (2 * α) * ‖x - y‖ ^ 2) ↔
      ExtSub D g 0 q (α⁻¹ • (y - q)) := by
  rw [extSub_zero_iff]
  have hα' : α ≠ 0 := hα.ne'
  -- the expansion of the squares
  have key : ∀ x : X, 1 / (2 * α) * ‖x - y‖ ^ 2 - 1 / (2 * α) * ‖q - y‖ ^ 2
      = - inner ℝ (α⁻¹ • (y - q)) (x - q) + 1 / (2 * α) * ‖x - q‖ ^ 2 := by
    intro x
    have e : x - y = (x - q) + (q - y) := by abel
    rw [e, norm_add_sq_real, inner_smul_left]
    simp only [conj_trivial]
    have e2 : inner ℝ (y - q) (x - q) = - inner ℝ (q - y) (x - q) := by
      rw [← inner_neg_left]; congr 1; abel
    rw [e2, real_inner_comm]
    field_simp
    ring
  constructor
  · rintro ⟨hqD, hmin⟩
    refine ⟨hqD, fun x hx => ?_⟩
    have hconv := convexOn_of_extModC_zero hg
    -- for every t ∈ (0,1]: g q + <v, x - q> ≤ g x + t/(2α) ‖x - q‖²
    have step : ∀ t : ℝ, 0 < t → t ≤ 1 →
        g q + inner ℝ (α⁻¹ • (y - q)) (x - q) ≤ g x + t * (1 / (2 * α) * ‖x - q‖ ^ 2) := by
      intro t ht0 ht1
      have hw : (1 - t) • q + t • x ∈ D := hconv.1 hqD hx (by linarith) ht0.le (by ring)
      have h1 := hmin _ hw
      have h2 := hconv.2 hqD hx (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      simp only [smul_eq_mul] at h2
      have hk := key ((1 - t) • q + t • x)
      have e3 : (1 - t) • q + t • x - q = t • (x - q) := by module
      rw [e3, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hk
      nlinarith
    -- let t → 0
    apply le_of_forall_pos_le_add
    intro ε hε
    set C := 1 / (2 * α) * ‖x - q‖ ^ 2 with hC
    have hC0 : 0 ≤ C := by positivity
    have ht : 0 < min 1 (ε / (C + 1)) := lt_min one_pos (div_pos hε (by linarith))
    have h := step _ ht (min_le_left _ _)
    have h3 : min 1 (ε / (C + 1)) * C ≤ ε := by
      have : min 1 (ε / (C + 1)) ≤ ε / (C + 1) := min_le_right _ _
      calc min 1 (ε / (C + 1)) * C ≤ ε / (C + 1) * C := by gcongr
        _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
          nlinarith
    have : g q + inner ℝ (α⁻¹ • (y - q)) (x - q) ≤ g x + ε := by linarith
    exact this
  · rintro ⟨hqD, hsub⟩
    refine ⟨hqD, fun x hx => ?_⟩
    have h1 := hsub x hx
    have h2 := key x
    have : 0 ≤ 1 / (2 * α) * ‖x - q‖ ^ 2 := by positivity
    linarith

/-! ## Existence and uniqueness of a minimiser of a strongly convex lsc function -/

/-- A function with closed sublevel sets on `D` attains its minimum on any nonempty compact
subset of `D` (lower semicontinuity on `K`; cf. DEF1's `exists_argmin_eq_singleton`). -/
lemma exists_min_compact {D : Set X} {Φ : X → ℝ} (hl : LscExt D Φ) {K : Set X}
    (hK : IsCompact K) (hne : K.Nonempty) (hKD : K ⊆ D) : ∃ p ∈ K, ∀ x ∈ K, Φ p ≤ Φ x := by
  have hlsc : LowerSemicontinuousOn Φ K := by
    intro x hx y hy
    have hxS : x ∈ {x' | x' ∈ D ∧ Φ x' ≤ y}ᶜ := fun h => absurd h.2 (not_le.2 hy)
    filter_upwards [mem_nhdsWithin_of_mem_nhds ((hl y).isOpen_compl.mem_nhds hxS),
      self_mem_nhdsWithin] with x' h1 h2
    by_contra hcon
    exact h1 ⟨hKD h2, not_lt.1 hcon⟩
  obtain ⟨p, hp, hmin⟩ := hlsc.exists_isMinOn hne hK
  exact ⟨p, hp, fun x hx => hmin hx⟩

/-- **Core existence/uniqueness.** On a proper space, a function `Φ` with closed sublevel
sets on a nonempty `D`, and `ExtModC D Φ m` with `m > 0`, has exactly one minimiser on `D`.
(Coercivity is derived from strong convexity along the segment to a base point; no affine
minorant is used.  B&C 2017 Cor. 11.17 is the classical existence statement.) -/
theorem exists_unique_min [ProperSpace X] {D : Set X} {Φ : X → ℝ} {m : ℝ} (hm : 0 < m)
    (hne : D.Nonempty) (hl : LscExt D Φ) (hC : ExtModC D Φ m) :
    ∃! p, p ∈ D ∧ ∀ w ∈ D, Φ p ≤ Φ w := by
  have hsc := strongConv_of_extModC hC
  have hDc : Convex ℝ D := hC.1
  obtain ⟨x₀, hx₀⟩ := hne
  set c₀ := Φ x₀ with hc₀
  -- a lower bound on D ∩ closedBall x₀ 1
  have hKcl : ∀ r : ℝ, IsCompact ({x | x ∈ D ∧ Φ x ≤ c₀} ∩ Metric.closedBall x₀ r) :=
    fun r => (isCompact_closedBall x₀ r).inter_left (hl c₀)
  obtain ⟨p₁, hp₁, hmin₁⟩ := exists_min_compact hl (hKcl 1)
    ⟨x₀, ⟨hx₀, le_rfl⟩, Metric.mem_closedBall_self zero_le_one⟩ (fun x hx => hx.1.1)
  set L := Φ p₁ with hL
  have hLc : L ≤ c₀ := hmin₁ x₀ ⟨⟨hx₀, le_rfl⟩, Metric.mem_closedBall_self zero_le_one⟩
  have hLb : ∀ z ∈ D, ‖z - x₀‖ ≤ 1 → L ≤ Φ z := by
    intro z hz hz1
    by_cases hzc : Φ z ≤ c₀
    · exact hmin₁ z ⟨⟨hz, hzc⟩, by rw [Metric.mem_closedBall, dist_eq_norm]; exact hz1⟩
    · exact hLc.trans (not_le.1 hzc).le
  set R : ℝ := 1 + 2 * (c₀ - L) / m with hR
  have hR1 : 1 ≤ R := by
    have : 0 ≤ 2 * (c₀ - L) / m := div_nonneg (by linarith) hm.le
    linarith
  -- coercivity
  have grow : ∀ x ∈ D, R < ‖x - x₀‖ → c₀ < Φ x := by
    intro x hx hxR
    set ρ := ‖x - x₀‖ with hρ
    have hρ0 : 0 < ρ := by linarith
    set b := ρ⁻¹ with hb
    set a := 1 - b with ha
    have hbρ : b * ρ = 1 := inv_mul_cancel₀ hρ0.ne'
    have hb0 : 0 ≤ b := inv_nonneg.2 hρ0.le
    have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hzD : a • x₀ + b • x ∈ D := hDc hx₀ hx (by simp only [ha]; linarith) hb0 (by simp only [ha]; ring)
    have hz1 : ‖a • x₀ + b • x - x₀‖ ≤ 1 := by
      have : a • x₀ + b • x - x₀ = b • (x - x₀) := by simp only [ha]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0, ← hρ, hbρ]
    have h1 := hsc x₀ hx₀ x hx a b (by simp only [ha]; linarith) hb0 (by simp only [ha]; ring)
    have h2 := hLb _ hzD hz1
    rw [norm_sub_rev x₀ x] at h1
    have h3 : L ≤ a * c₀ + b * Φ x - m / 2 * (a * b * ρ ^ 2) := h2.trans h1
    have key : ρ * (a * c₀ + b * Φ x - m / 2 * (a * b * ρ ^ 2))
        = ρ * c₀ - c₀ + Φ x - m / 2 * ((ρ - 1) * ρ) := by
      simp only [a, b]
      field_simp
    have h4 : ρ * L ≤ ρ * c₀ - c₀ + Φ x - m / 2 * ((ρ - 1) * ρ) := by
      rw [← key]; exact mul_le_mul_of_nonneg_left h3 hρ0.le
    have h5 : m / 2 * (ρ - 1) > c₀ - L := by
      have e : m / 2 * (2 * (c₀ - L) / m) = c₀ - L := by field_simp
      have : ρ - 1 > 2 * (c₀ - L) / m := by simp only [hR] at hxR; linarith
      nlinarith
    nlinarith
  -- existence
  obtain ⟨p, hp, hpmin⟩ := exists_min_compact hl (hKcl R)
    ⟨x₀, ⟨hx₀, le_rfl⟩, Metric.mem_closedBall_self (by linarith)⟩ (fun x hx => hx.1.1)
  have hpD : p ∈ D := hp.1.1
  have hglob : ∀ w ∈ D, Φ p ≤ Φ w := by
    intro w hw
    by_cases hwc : Φ w ≤ c₀
    · apply hpmin
      refine ⟨⟨hw, hwc⟩, ?_⟩
      rw [Metric.mem_closedBall, dist_eq_norm]
      by_contra hcon
      exact absurd (grow w hw (not_le.1 hcon)) (not_lt.2 hwc)
    · exact (hpmin x₀ ⟨⟨hx₀, le_rfl⟩, Metric.mem_closedBall_self (by linarith)⟩).trans
        (not_le.1 hwc).le
  refine ⟨p, ⟨hpD, hglob⟩, ?_⟩
  -- uniqueness
  rintro q ⟨hqD, hqmin⟩
  by_contra hqp
  have hqp' : q - p ≠ 0 := sub_ne_zero.2 hqp
  have hmid := hsc q hqD p hpD (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have hmidD : (1 / 2 : ℝ) • q + (1 / 2 : ℝ) • p ∈ D := hDc hqD hpD (by norm_num) (by norm_num) (by norm_num)
  have e1 := hqmin p hpD
  have e2 := hglob q hqD
  have hqv : Φ q = Φ p := le_antisymm e1 e2
  have h6 := hglob _ hmidD
  have hpos : 0 < ‖q - p‖ ^ 2 := by positivity
  rw [hqv] at hmid
  nlinarith

/-! ## Bookkeeping: sums, the quadratic, continuity -/

lemma extModC_add {D : Set X} {g h : X → ℝ} {σ τ : ℝ} (hg : ExtModC D g σ) (hh : ExtModC D h τ) :
    ExtModC D (fun x => g x + h x) (σ + τ) := by
  have h := hg.add hh
  unfold ExtModC
  refine h.congr fun x _ => ?_
  simp only [Pi.add_apply]
  ring

lemma extModC_of_modC {D : Set X} {f : X → ℝ} {σ : ℝ} (hf : ModC f σ) (hD : Convex ℝ D) :
    ExtModC D f σ :=
  hf.subset (subset_univ D) hD

/-- The quadratic `(1/(2α))‖· − y‖²` has curvature `1/α` (everywhere). -/
lemma extModC_quad {α : ℝ} (hα : 0 < α) (y : X) (D : Set X) (hD : Convex ℝ D) :
    ExtModC D (fun x => 1 / (2 * α) * ‖x - y‖ ^ 2) (1 / α) := by
  refine ⟨hD, ?_⟩
  intro u _ v _ a b ha hb hab
  simp only [smul_eq_mul]
  have e : ∀ x : X, 1 / (2 * α) * ‖x - y‖ ^ 2 - 1 / α / 2 * ‖x‖ ^ 2
      = - (1 / α) * inner ℝ x y + 1 / (2 * α) * ‖y‖ ^ 2 := by
    intro x
    rw [norm_sub_sq_real]
    field_simp
    ring
  simp only [e]
  rw [inner_add_left, inner_smul_left, inner_smul_left]
  simp only [conj_trivial]
  have hb' : b = 1 - a := by linarith
  subst hb'
  ring_nf
  rfl

/-- Closed sublevel sets are preserved by adding a continuous function. -/
lemma lscExt_add_continuous {D : Set X} {g h : X → ℝ} (hg : LscExt D g) (hh : Continuous h) :
    LscExt D (fun x => g x + h x) := by
  intro c
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 hx
  have hhu : Tendsto (fun n => h (u n)) atTop (𝓝 (h x)) := (hh.tendsto x).comp hux
  have hD : ∀ ε : ℝ, 0 < ε → x ∈ D ∧ g x ≤ c - h x + ε := by
    intro ε hε
    have hev : ∀ᶠ n in atTop, h x - ε < h (u n) :=
      (hhu.eventually (lt_mem_nhds (by linarith : h x - ε < h x)))
    have := (hg (c - h x + ε)).mem_of_tendsto hux (by
      filter_upwards [hev] with n hn
      exact ⟨(hu n).1, by have := (hu n).2; simp only at this; linarith⟩)
    exact this
  refine ⟨(hD 1 one_pos).1, ?_⟩
  have : g x ≤ c - h x := le_of_forall_pos_le_add fun ε hε => (hD ε hε).2
  simp only
  linarith

/-! ## Lower semicontinuity of finite sums (used for the block-separable `g` of H4) -/

/-- An lsc function is eventually bounded below along a sequence in `D` converging to any point. -/
lemma lscExt_eventually_lower {D : Set X} {Φ : X → ℝ} (hl : LscExt D Φ) {u : ℕ → X} {x : X}
    (hu : ∀ n, u n ∈ D) (hux : Tendsto u atTop (𝓝 x)) {b : ℝ}
    (hb : ¬ (x ∈ D ∧ Φ x ≤ b)) : ∀ᶠ n in atTop, b < Φ (u n) := by
  have hopen : {y | y ∈ D ∧ Φ y ≤ b}ᶜ ∈ 𝓝 x := (hl b).isOpen_compl.mem_nhds hb
  filter_upwards [hux.eventually hopen] with n hn
  by_contra hcon
  exact hn ⟨hu n, not_lt.1 hcon⟩

lemma lscExt_exists_lower {D : Set X} {Φ : X → ℝ} (hl : LscExt D Φ) {u : ℕ → X} {x : X}
    (hu : ∀ n, u n ∈ D) (hux : Tendsto u atTop (𝓝 x)) : ∃ b : ℝ, ∀ᶠ n in atTop, b < Φ (u n) := by
  by_cases hx : x ∈ D
  · exact ⟨Φ x - 1, lscExt_eventually_lower hl hu hux (fun h => by linarith [h.2])⟩
  · exact ⟨0, lscExt_eventually_lower hl hu hux (fun h => hx h.1)⟩

/-- The sum of two lsc functions (closed-sublevel form) is lsc on the intersection of the domains. -/
lemma lscExt_add_two {D₁ D₂ : Set X} {Φ₁ Φ₂ : X → ℝ} (h₁ : LscExt D₁ Φ₁) (h₂ : LscExt D₂ Φ₂) :
    LscExt (D₁ ∩ D₂) (fun x => Φ₁ x + Φ₂ x) := by
  intro c
  refine isClosed_of_closure_subset fun x hx => ?_
  obtain ⟨u, hu, hux⟩ := mem_closure_iff_seq_limit.1 hx
  have hu1 : ∀ n, u n ∈ D₁ := fun n => (hu n).1.1
  have hu2 : ∀ n, u n ∈ D₂ := fun n => (hu n).1.2
  have hs : ∀ n, Φ₁ (u n) + Φ₂ (u n) ≤ c := fun n => (hu n).2
  obtain ⟨b₁, hb₁⟩ := lscExt_exists_lower h₁ hu1 hux
  obtain ⟨b₂, hb₂⟩ := lscExt_exists_lower h₂ hu2 hux
  have hx1 : x ∈ D₁ ∧ Φ₁ x ≤ c - b₂ :=
    (h₁ (c - b₂)).mem_of_tendsto hux (by
      filter_upwards [hb₂] with n hn
      exact ⟨hu1 n, by have := hs n; linarith⟩)
  have hx2 : x ∈ D₂ ∧ Φ₂ x ≤ c - b₁ :=
    (h₂ (c - b₁)).mem_of_tendsto hux (by
      filter_upwards [hb₁] with n hn
      exact ⟨hu2 n, by have := hs n; linarith⟩)
  refine ⟨⟨hx1.1, hx2.1⟩, ?_⟩
  show Φ₁ x + Φ₂ x ≤ c
  apply le_of_forall_pos_le_add
  intro ε hε
  have e1 := lscExt_eventually_lower h₁ hu1 hux (b := Φ₁ x - ε / 2)
    (fun h => by linarith [h.2])
  have e2 := lscExt_eventually_lower h₂ hu2 hux (b := Φ₂ x - ε / 2)
    (fun h => by linarith [h.2])
  obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
  have := hs n
  linarith

/-- Finite sums: `Σ_{i∈s} G i` is lsc on `⋂_{i∈s} E i` if each `G i` is lsc on `E i`. -/
lemma lscExt_finset_sum {ι : Type*} (s : Finset ι) (E : ι → Set X) (G : ι → X → ℝ)
    (h : ∀ i ∈ s, LscExt (E i) (G i)) :
    LscExt {x | ∀ i ∈ s, x ∈ E i} (fun x => ∑ i ∈ s, G i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro c
    simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true, setOf_true,
      Finset.sum_empty]
    by_cases hc : (0 : ℝ) ≤ c
    · have : {x : X | x ∈ (univ : Set X) ∧ (0 : ℝ) ≤ c} = univ := by ext; simp [hc]
      rw [this]; exact isClosed_univ
    · have : {x : X | x ∈ (univ : Set X) ∧ (0 : ℝ) ≤ c} = ∅ := by ext; simp [hc]
      rw [this]; exact isClosed_empty
  | insert j s hj ih =>
    have := lscExt_add_two (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hset : {x | ∀ i ∈ insert j s, x ∈ E i} = E j ∩ {x | ∀ i ∈ s, x ∈ E i} := by
      ext x; simp
    rw [hset]
    intro c
    have := this c
    simpa [Finset.sum_insert hj] using this

/-! ## A2. Existence and uniqueness of the proximal point (B&C Prop. 12.15) -/

/-- **A2.** For `D` nonempty (convex by `ExtModC D g 0`), `g` lsc on `D` and convex, α > 0, on a
proper space: the proximal point `prox_{αg}(y)` exists and is unique,
[B&C 2017, Prop. 12.15 and Def. 12.23]. -/
theorem prox_exists_unique [ProperSpace X] {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) {α : ℝ} (hα : 0 < α) (y : X) :
    ∃! q, q ∈ D ∧ ∀ x ∈ D, g q + 1 / (2 * α) * ‖q - y‖ ^ 2 ≤ g x + 1 / (2 * α) * ‖x - y‖ ^ 2 := by
  have hq : Continuous (fun x : X => 1 / (2 * α) * ‖x - y‖ ^ 2) := by fun_prop
  have h1 := lscExt_add_continuous hlsc hq
  have h2 : ExtModC D (fun x => g x + 1 / (2 * α) * ‖x - y‖ ^ 2) (0 + 1 / α) :=
    extModC_add hg (extModC_quad hα y D hg.1)
  have hm : (0:ℝ) < 0 + 1 / α := by simp [hα]
  exact exists_unique_min hm hne h1 h2

/-! ## A3. The proximal map and discharge of the prox hypotheses of G3 and H2 -/

open Classical in
/-- The proximal map `prox_{αg}` of the extended-valued function (`g` on `D`, +∞ off `D`):
the minimiser of `g + (1/(2α))‖· − y‖²` over `D` (chosen by `Classical.choose` when it
exists; the junk value `y` otherwise, never used under the A2 hypotheses). -/
noncomputable def proxMap (D : Set X) (g : X → ℝ) (α : ℝ) (y : X) : X :=
  if h : ∃ q, q ∈ D ∧ ∀ x ∈ D, g q + 1 / (2 * α) * ‖q - y‖ ^ 2 ≤ g x + 1 / (2 * α) * ‖x - y‖ ^ 2
  then Classical.choose h else y

lemma proxMap_spec [ProperSpace X] {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) {α : ℝ} (hα : 0 < α) (y : X) :
    proxMap D g α y ∈ D ∧ ∀ x ∈ D, g (proxMap D g α y) + 1 / (2 * α) * ‖proxMap D g α y - y‖ ^ 2
      ≤ g x + 1 / (2 * α) * ‖x - y‖ ^ 2 := by
  have h := (prox_exists_unique hne hlsc hg hα y).exists
  unfold proxMap
  rw [dif_pos h]
  exact Classical.choose_spec h

/-- **A3.** Under the A2 hypotheses the proximal map satisfies G3's `ProxChar`
(`P y = q ↔ (y − q)/α ∈ ∂g(q)`), the classical characterisation that
`G3SoundnessProx` takes as the hypothesis of a valid prox declaration
[B&C 2017, Def. 12.23, Prop. 12.15, Prop. 16.44]. -/
theorem proxChar_proxMap [ProperSpace X] {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) {α : ℝ} (hα : 0 < α) :
    ProxChar D g α (proxMap D g α) := by
  intro y q
  constructor
  · rintro rfl
    exact (prox_char hg hα y _).1 (proxMap_spec hne hlsc hg hα y)
  · intro h
    have hq := (prox_char hg hα y q).2 h
    exact ((prox_exists_unique hne hlsc hg hα y).unique (proxMap_spec hne hlsc hg hα y) hq)

/-- **A3 (H2).** The exact proximal point exists: `∃ z, ProxEps D g α 0 y z`, the hypothesis
(`P`) of H2's exact case. -/
theorem exists_proxEps_zero [ProperSpace X] {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) {α : ℝ} (hα : 0 < α) (y : X) :
    ∃ z, ProxEps D g α 0 y z := by
  refine ⟨proxMap D g α y, ?_⟩
  have h := (proxChar_proxMap hne hlsc hg hα y (proxMap D g α y)).1 rfl
  rw [extSub_zero_iff] at h
  refine ⟨h.1, fun w hw => ?_⟩
  have := h.2 w hw
  linarith

/-- The map `proxMap` is a pointwise solution of H2's exact inclusion for every `y`. -/
theorem proxMap_proxEps [ProperSpace X] {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) {α : ℝ} (hα : 0 < α) :
    ∀ y, ProxEps D g α 0 y (proxMap D g α y) := by
  intro y
  have h := (proxChar_proxMap hne hlsc hg hα y (proxMap D g α y)).1 rfl
  rw [extSub_zero_iff] at h
  refine ⟨h.1, fun w hw => ?_⟩
  have := h.2 w hw
  linarith

/-! ## A4. Existence and uniqueness of a minimiser of f + g -/

/-- **A4 (general curvature split).** `f` continuous with `C(f, σf)`, `(D, g)` with `D` nonempty,
`g` lsc on `D` with `C(g, σg)` (`ExtModC D g σg`), and `σf + σg > 0`, on a proper space: `f + g`
has exactly one minimiser on `D` [B&C 2017, Cor. 11.17 with strict convexity]. -/
theorem exists_unique_min_add_gen [ProperSpace X] {f : X → ℝ} {σf σg : ℝ} (hσ : 0 < σf + σg)
    (hf : Continuous f) (hC : ModC f σf) {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g σg) :
    ∃! xs, xs ∈ D ∧ ∀ w ∈ D, f xs + g xs ≤ f w + g w := by
  have h1 : LscExt D (fun x => f x + g x) := by
    have := lscExt_add_continuous hlsc hf
    intro c
    convert this c using 3
    ring_nf
  have h2 : ExtModC D (fun x => f x + g x) (σf + σg) :=
    extModC_add (extModC_of_modC hC hg.1) hg
  exact exists_unique_min hσ hne h1 h2

/-- **A4.** `f` continuous with `C(f, σ)`, σ > 0, and `(D, g)` with `D` nonempty, `g` lsc on `D`
and convex (`ExtModC D g 0`), on a proper space: `f + g` has exactly one minimiser on `D`
[B&C 2017, Cor. 11.17 with strict convexity]. -/
theorem exists_unique_min_add [ProperSpace X] {f : X → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hf : Continuous f) (hC : ModC f σ) {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) :
    ∃! xs, xs ∈ D ∧ ∀ w ∈ D, f xs + g xs ≤ f w + g w :=
  exists_unique_min_add_gen (by simpa using hσ) hf hC hne hlsc hg

/-- **A4, differentiable form** (the form of the hypotheses of H2/H3/H4). -/
theorem exists_unique_min_add_diff [ProperSpace X] {f : X → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hf : Differentiable ℝ f) (hC : ModC f σ) {D : Set X} {g : X → ℝ} (hne : D.Nonempty)
    (hlsc : LscExt D g) (hg : ExtModC D g 0) :
    ∃! xs, xs ∈ D ∧ ∀ w ∈ D, f xs + g xs ≤ f w + g w :=
  exists_unique_min_add hσ hf.continuous hC hne hlsc hg

/-! ## More bookkeeping for the discharge corollaries -/

/-- `C(g, σ)` with `σ ≥ 0` implies convexity `C(g, 0)`. -/
lemma extModC_zero_of_nonneg {D : Set X} {g : X → ℝ} {σ : ℝ} (hσ : 0 ≤ σ) (h : ExtModC D g σ) :
    ExtModC D g 0 := by
  have hq : ConvexOn ℝ D (fun x : X => σ / 2 * ‖x‖ ^ 2) := by
    refine ⟨h.1, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul]
    rw [norm_convex_comb_sq hab]
    have : 0 ≤ σ / 2 * (a * b * ‖x - y‖ ^ 2) := by positivity
    nlinarith
  have := h.add hq
  unfold ExtModC
  refine this.congr fun x _ => ?_
  simp only [Pi.add_apply]
  ring

/-- Finite sums of `C(g_j, σ_j)` terms on a convex `D`. -/
lemma extModC_sum {ι : Type*} {D : Set X} (hD : Convex ℝ D) (s : Finset ι) {g : ι → X → ℝ}
    {σ : ι → ℝ} (h : ∀ j ∈ s, ExtModC D (g j) (σ j)) :
    ExtModC D (fun x => ∑ j ∈ s, g j x) (∑ j ∈ s, σ j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨hD, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [Finset.sum_empty, smul_eq_mul]
    nlinarith
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact extModC_add (h j (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## A5. Discharge corollaries -/

/-- **G3 headline, prox hypothesis discharged** (`soundness_prox`).  The non-smooth term is
given by its primitive data `(Dg, g, σg)`: `σg ≥ 0`, `C(g, σg)`, `Dg` nonempty and `g` lsc on
`Dg` (the hypotheses of B&C Prop. 12.15); the prox attribute is the exact proximal map
`proxMap`.  Every conclusion of `ProxConclusions` follows.  (`NDecl.Valid` is not assumed; its
`prox` field is proved by A3.  Added hypotheses relative to `soundness_prox`: `Dg` nonempty and
lsc, the exact premises of existence of the proximal point; the original theorem quantified
over an arbitrary prox program `P` satisfying `ProxChar`, which by uniqueness (A2) is
`proxMap` whenever the A2 hypotheses hold.) -/
theorem soundness_prox_of_primitive {d n : ℕ} (hd : 0 < d) (D : Decl d n)
    (f : Fin n → Vec d → ℝ) (hv : D.Valid f) (Dg : Set (Vec d)) (g : Vec d → ℝ) (σg : ℝ)
    (hσg : 0 ≤ σg) (hC : ExtModC Dg g σg) (hne : Dg.Nonempty) (hlsc : LscExt Dg g)
    (hFB : 0 < D.betaHat) {T : Finset (Fin n)} (hT : T ⊆ D.SK) (Δm : ℝ)
    (hΔ : Δm ≤ D.deltaW T) :
    ProxConclusions (D.energy f) Dg g σg (proxMap Dg g (1 / D.betaHat)) D.betaHat
      (D.sigmaT T) (D.sigmaOf T Δm) := by
  have hg0 := extModC_zero_of_nonneg hσg hC
  let N : NDecl d := { Dg := Dg, g := g, σg := σg, P := fun a => proxMap Dg g a }
  have hN : N.Valid :=
    ⟨hσg, hC, fun a ha => proxChar_proxMap hne hlsc hg0 ha⟩
  exact soundness_prox hd D f hv N hN hFB hT Δm hΔ

/-- **H2 headline (E4)(a), classical hypotheses discharged.**  Regime A or B of H2 with
primitive data: `D` nonempty, `g` lsc on `D` with `C(g, σg)`, `σg ≥ 0`, `f` differentiable with
`C(f, σf)` and β-Lipschitz gradient.  Then (i) the minimiser `x*` of `f + g` on `D` exists and
is unique (A4; regime A has `σf > 0, σg ≥ 0`, regime B `σf ≥ 0, σg > 0`, so `σf + σg > 0`),
(ii) the exact proximal map `proxMap` satisfies H2's exact inclusion `ProxEps D g α 0 y (P y)`
for every `y` (A3), and (iii) the contraction recursion of `E4a` holds for every inexact run.
The hypotheses `hP`, `hxs`, `hmin` of `E4a` are not assumed. -/
theorem E4a_of_primitive [ProperSpace X] [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ}
    {α β σf σg q : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α)
    (hαβ : α * β = 1) (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg)
    (hne : D.Nonempty) (hlsc : LscExt D g) (hreg : OCF.H2.Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : OCF.H2.InexactRun f D g α x ε) :
    ∃ xs, xs ∈ D ∧ (∀ w ∈ D, f xs + g xs ≤ f w + g w) ∧
      (∀ k, ‖x (k + 1) - xs‖ ≤ q * ‖x k - xs‖ + √(α * ε k)) ∧
      (∀ k, ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ +
        ∑ i ∈ Finset.range k, q ^ (k - 1 - i) * √(α * ε i)) := by
  have hpos : 0 < σf + σg := by
    rcases hreg with ⟨h1, -⟩ | ⟨h1, h2, -⟩ <;> linarith
  obtain ⟨xs, ⟨hxs, hmin⟩, -⟩ := exists_unique_min_add_gen hpos hf.continuous hCf hne hlsc hCg
  have hg0 := extModC_zero_of_nonneg hσg hCg
  exact ⟨xs, hxs, hmin, OCF.H2.E4a hf hL hα hαβ hCf hCg hσg
    (P := proxMap D g α) (proxMap_proxEps hne hlsc hg0 hα) hxs hmin hreg hr⟩

end Generic

section H3

open OCF.H3.ConsIter in
/-- **H3 headline, Corollary T1-it (`ConsIter.cert_iter`), classical hypotheses discharged.**
The two prox programs of the iteration ARE the exact proximal maps (`prox_{αg₀}` and
`prox_{m'αg_j}`, as `proxMap`), so the bundle `Realises` (B&C Prop. 16.44, a field of `Typed`)
is proved by A3, not assumed; the minimiser `x*` of `E = F + g₀ + Σ g_j` (hypotheses `hxs`,
`hmin` of `cert_iter`) is produced by A4 (curvature `σ_F + σ₀ + Σσ_j > 0`, `F` and the `g_j`
continuous, `g₀` lsc on a nonempty `D₀`).  Fields of `Typed` that remain assumed (now as separate
primitive hypotheses): `diffF`, `curvF`, `curv0`, `sigma0`, `curv`, `sigma`, `lip`.  Added
relative to `Typed`: `D₀` nonempty and `g₀` lsc on `D₀` (premises of existence of the
proximal point and of the minimiser); the `g_j` need no lsc hypothesis (a finite Lipschitz
attribute makes them continuous). -/
theorem cert_iter_of_primitive {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [ProperSpace X] [Nontrivial X] {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : OCF.H3.ConsIter X ι} {σF σ0 : ℝ} {D0 : Set X} {g0 : X → ℝ} {gj : ι → X → ℝ}
    {σj Lj : ι → ℝ}
    (hdiffF : Differentiable ℝ C.F) (hcurvF : ModC C.F σF) (hcurv0 : ExtModC D0 g0 σ0)
    (hsigma0 : 0 ≤ σ0) (hcurv : ∀ j, ModC (gj j) (σj j)) (hsigma : ∀ j, 0 ≤ σj j)
    (hlip : ∀ j, OCF.H3.LipAttr (gj j) (Lj j))
    (hne : D0.Nonempty) (hlsc : LscExt D0 g0)
    (hprox0 : C.prox0 = proxMap D0 g0 C.α)
    (hprox : ∀ j, C.prox j = proxMap univ (gj j) (OCF.H3.ConsIter.mP ι * C.α))
    (hα : 0 < C.α) (hμ : 0 < σF + σ0 + ∑ j, σj j) :
    ∃ xs, xs ∈ D0 ∧
      (∀ y ∈ D0, OCF.H3.ConsIter.EIt C.F g0 gj xs ≤ OCF.H3.ConsIter.EIt C.F g0 gj y) ∧
      ∀ z : ι → X,
        ‖C.x z - xs‖ ≤ OCF.H3.tauC ‖C.r z‖ (C.epsIt Lj z) (σF + σ0 + ∑ j, σj j) ∧
        OCF.H3.tauC ‖C.r z‖ (C.epsIt Lj z) (σF + σ0 + ∑ j, σj j)
          ≤ ‖C.r z‖ / (σF + σ0 + ∑ j, σj j) + √(C.epsIt Lj z / (σF + σ0 + ∑ j, σj j)) ∧
        (∀ j, ‖C.p z j - xs‖
          ≤ OCF.H3.tauC ‖C.r z‖ (C.epsIt Lj z) (σF + σ0 + ∑ j, σj j) + ‖C.p z j - C.x z‖) ∧
        OCF.H3.ConsIter.EIt C.F g0 gj (C.x z) - OCF.H3.ConsIter.EIt C.F g0 gj xs
          ≤ ‖C.r z‖ ^ 2 / (2 * (σF + σ0 + ∑ j, σj j)) + C.epsIt Lj z ∧
        ‖C.r z‖ = ‖C.x z - C.pbar z‖ / C.α ∧
        ‖C.r z‖ ≤ C.e z / (C.α * √(OCF.H3.ConsIter.mP ι)) ∧
        C.epsIt Lj z ≤ 2 * OCF.H3.ConsIter.normL Lj * C.e z := by
  have hg0 : ExtModC D0 g0 0 := extModC_zero_of_nonneg hsigma0 hcurv0
  have hmP : 0 < OCF.H3.ConsIter.mP ι * C.α := mul_pos OCF.H3.ConsIter.mP_pos hα
  have hcont : ∀ j, Continuous (gj j) := by
    intro j
    obtain ⟨hL0, hL⟩ := hlip j
    exact (LipschitzWith.of_dist_le_mul (K := (Lj j).toNNReal) fun x y => by
      rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal _ hL0]; exact hL x y).continuous
  have hreal : C.Realises D0 g0 (fun _ => univ) gj := by
    refine ⟨fun y q => ?_, fun j y q => ?_⟩
    · rw [hprox0]; exact proxChar_proxMap hne hlsc hg0 hα y q
    · rw [hprox j]
      have hgj0 : ExtModC univ (gj j) 0 := extModC_zero_of_nonneg (hsigma j) (hcurv j)
      have hl : LscExt univ (gj j) := by
        intro c
        have : {x | x ∈ (univ : Set X) ∧ gj j x ≤ c} = gj j ⁻¹' Iic c := by ext; simp
        rw [this]; exact isClosed_Iic.preimage (hcont j)
      exact proxChar_proxMap univ_nonempty hl hgj0 hmP y q
  have hT : C.Typed σF σ0 D0 g0 gj σj Lj :=
    ⟨hdiffF, hcurvF, hcurv0, hsigma0, hcurv, hsigma, hlip, hreal⟩
  -- the minimiser of E = F + g0 + Σ g_j  (A4 with f = F + Σ g_j)
  have hfc : Continuous (fun x => C.F x + ∑ j, gj j x) :=
    hdiffF.continuous.add (continuous_finsetSum _ fun j _ => hcont j)
  have hfm : ModC (fun x => C.F x + ∑ j, gj j x) (σF + ∑ j, σj j) :=
    extModC_add hcurvF (extModC_sum convex_univ Finset.univ fun j _ => hcurv j)
  obtain ⟨xs, ⟨hxs, hmin0⟩, -⟩ := exists_unique_min_add_gen
    (by linarith : 0 < (σF + ∑ j, σj j) + σ0) hfc hfm hne hlsc hcurv0
  have hmin : ∀ y ∈ D0, OCF.H3.ConsIter.EIt C.F g0 gj xs ≤ OCF.H3.ConsIter.EIt C.F g0 gj y := by
    intro y hy
    have := hmin0 y hy
    simp only [OCF.H3.ConsIter.EIt] at *
    linarith
  exact ⟨xs, hxs, hmin, fun z => OCF.H3.ConsIter.cert_iter hT hα hμ hxs hmin z⟩

end H3


section H4

open OCF.H4

variable {m : ℕ} {Y : Fin m → Type*} [∀ l, NormedAddCommGroup (Y l)]
  [∀ l, InnerProductSpace ℝ (Y l)] [∀ l, CompleteSpace (Y l)]

/-- The block-separable `g(x) = Σ_l g_l(x_l)` is lsc on `dom g = Π_l dom g_l` when each `g_l` is
lsc on `dom g_l`. -/
lemma lscExt_gsum {D : ∀ l, Set (Y l)} {g : ∀ l, Y l → ℝ} (h : ∀ l, LscExt (D l) (g l)) :
    LscExt (domG D) (gsum g) := by
  have := lscExt_finset_sum (X := PiLp 2 Y) Finset.univ (fun l => {x : PiLp 2 Y | x l ∈ D l})
    (fun l x => g l (x l)) (fun l _ c => by
      have e : {x : PiLp 2 Y | x ∈ {x : PiLp 2 Y | x l ∈ D l} ∧ g l (x l) ≤ c}
          = (fun x : PiLp 2 Y => x l) ⁻¹' {y | y ∈ D l ∧ g l y ≤ c} := rfl
      rw [e]
      exact (h l c).preimage (PiLp.continuous_apply 2 Y l))
  have hset : domG D = {x : PiLp 2 Y | ∀ i ∈ (Finset.univ : Finset (Fin m)), x ∈ {x : PiLp 2 Y | x i ∈ D i}} := by
    ext x; simp [domG]
  rw [hset]
  exact this

/-- **H4 headline (Theorem H4.7(b)), the hypothesis `IsMinE` discharged.**  With the standing
data `SD` (so `C(F, σ)`, `σ > 0`, `F` differentiable, every `g_l` convex on `D_l`) and, as the
only added primitive hypotheses, every block domain nonempty and every `g_l` lsc on `D_l`, with
finite-dimensional blocks: a minimiser `x*` of `E = F + g` on `dom g` exists (A4 on the product
space), and for it the θ-recursion of Theorem H4.7(b) holds for every stitched run, every
`θ > 0` and every `k`. -/
theorem H4_7_b_of_primitive [∀ l, FiniteDimensional ℝ (Y l)]
    {D : ∀ l, Set (Y l)} {g : ∀ l, Y l → ℝ} {F : PiLp 2 Y → ℝ} {σ : ℝ} {τ : Fin m → ℝ}
    {L : Fin m → Fin m → ℝ} (hSD : SD F D g σ τ L) (hne : ∀ l, (D l).Nonempty)
    (hlsc : ∀ l, LscExt (D l) (g l)) (R : Run D g) :
    ∃ xs : PiLp 2 Y, IsMinE F D g xs ∧ ∀ θ : ℝ, 0 < θ → ∀ k : ℕ,
      R.ak F xs (k + 1) ≤ rhoth θ (Lam L τ) σ * R.ak F xs k
        + (1 - rhoth θ (Lam L τ) σ) * R.Bk F τ (Lam L τ) σ θ k := by
  have hDne : (domG D).Nonempty := by
    choose x hx using hne
    exact ⟨(WithLp.toLp 2 x : PiLp 2 Y), fun l => hx l⟩
  obtain ⟨xs, ⟨hxD, hmin⟩, -⟩ := exists_unique_min_add hSD.sigma_pos hSD.diff.continuous hSD.modF
    hDne (lscExt_gsum hlsc) (modCD_gsum hSD.convex_g)
  have hxs : IsMinE F D g xs := ⟨hxD, fun w hw => hmin w hw⟩
  exact ⟨xs, hxs, fun θ hθ k => R.H4_7_b hSD hxs hθ k⟩

end H4


end OCF.PCF

#print axioms OCF.PCF.prox_char
#print axioms OCF.PCF.exists_unique_min
#print axioms OCF.PCF.prox_exists_unique
#print axioms OCF.PCF.proxChar_proxMap
#print axioms OCF.PCF.exists_proxEps_zero
#print axioms OCF.PCF.proxMap_proxEps
#print axioms OCF.PCF.exists_unique_min_add_gen
#print axioms OCF.PCF.exists_unique_min_add
#print axioms OCF.PCF.exists_unique_min_add_diff
#print axioms OCF.PCF.soundness_prox_of_primitive
#print axioms OCF.PCF.E4a_of_primitive
#print axioms OCF.PCF.cert_iter_of_primitive
#print axioms OCF.PCF.H4_7_b_of_primitive

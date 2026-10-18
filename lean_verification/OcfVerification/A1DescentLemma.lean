/-
A1 (The explicit gradient step: two regimes) — Lemma A1.1 (descent, parts
(a), (b), (c)), Lemma A1.2 (nonexpansiveness ⇔ convexity), and Example A1.E
S3.2 (the cos x witness).

Source of truth: project_plan/done/proof_audits/A1_step_size_regimes/01_derivation.md
(stage-1 dossier revised at stage 3; sha16 f7e15903ee4dad1f at the time of
formalisation), 03_adjudication.md (overnight delegation 2026-10-09 queued a
Lean pass on the descent lemma incl. the novel sublevel proof S1.4), and the
stage-4 draft 04_landing_draft.tex (Lemma lem:descent-step, Lemma
lem:nonexpansive-step, Example ex:cos-two-regimes).

DEFINITIONAL MAP:
* ℝᵈ — any real Hilbert space `E` (`InnerProductSpace ℝ E`, `CompleteSpace E`);
  ℝᵈ is the instance `E = EuclideanSpace ℝ (Fin d)` (see the `_euclidean`
  corollaries). The proofs use only the inner product (cf. Remark A1.R5).
* ∇f — Mathlib's `gradient f` (Riesz representative of `fderiv ℝ f`).
* θ(α) = α(1 − αβ/2) — `theta β α`.
* S_τ = {f ≤ τ} — written out as `f y ≤ τ`.
* "∇f β-Lipschitz" — `∀ u v, ‖∇f u − ∇f v‖ ≤ β‖u − v‖` (globally for H1,
  for u, v ∈ S_τ for H1′), β a real upper bound, exactly as in the dossier.
* f ∈ C¹(ℝᵈ) with β-Lipschitz ∇f (H1) — `Differentiable ℝ f` plus the global
  Lipschitz bound. This is equivalent to H1 (a Lipschitz gradient is
  continuous, so f is C¹); no hypothesis is strengthened.
* "Id − α∇f nonexpansive" — `StepNonexpansive f α`:
  ‖(x − α∇f x) − (y − α∇f y)‖ ≤ ‖x − y‖ for all x, y.
* "∇f monotone" — `GradMonotone f`: ⟨∇f x − ∇f y, x − y⟩ ≥ 0 for all x, y.
* "f convex" — `ConvexOn ℝ univ f`.

STATEMENTS FORMALISED:
* Lemma A1.1(a) — `descent_global`: H1, every x, every α > 0,
  f(x − α∇f x) ≤ f x − θ(α)‖∇f x‖². (β > 0 is not needed and not assumed.)
  Proved via the general one-sided quadratic upper bound along a segment,
  `upper_bound_on_segment` (B&C Lemma 2.64(i), upper half, restricted to a
  segment and with the Lipschitz bound needed only between the base point
  and points of the segment) — a self-built lemma; Mathlib has no named
  descent lemma.
* Lemma A1.1(b) [NOVEL, S1.4] — `descent_sublevel`: f continuous on E,
  differentiable at every point of S_τ, ∇f β-Lipschitz between points of
  S_τ, β > 0, x ∈ S_τ, α ∈ (0, 2/β]  ⇒  x − t∇f x ∈ S_τ for all t ∈ [0, α]
  and f(x − α∇f x) ≤ f x − θ(α)‖∇f x‖². Proof: first-exit time m = inf of
  the exit set (the dossier's s* = sup J, dualised), closedness of S_τ,
  descent on [0, m], and strict descent / negative right derivative past m.
* Lemma A1.1(c) — `theta_pos_iff` (for every real α: θ(α) > 0 ⇔
  α ∈ (0, 2/β)), `half_le_theta_iff` (for α > 0, the dossier's step-size
  domain: θ(α) ≥ α/2 ⇔ α ≤ 1/β; at α = 0 both sides are 0 and the
  dossier's "α ∈ (0, 1/β]" reading is only meant for step sizes α > 0),
  `theta_le_theta_inv` and `theta_inv` (max θ = θ(1/β) = 1/(2β)).
* Lemma A1.2 — `nonexpansive_tfae`: under H1 (β > 0) TFAE
  (a) f convex, (b) ∇f monotone, (c) Id − α∇f nonexpansive ∀ α ∈ (0, 2/β],
  (d) nonexpansive for some α > 0; and `not_stepNonexpansive_of_not_convex`
  (the "in particular", needing only differentiability, as S2.5 says).
  (a) ⇔ (b) (B&C Prop. 17.7) is proved via the first-order condition;
  Baillon–Haddad (B&C Cor. 18.17), cited in the dossier, is proved here as
  `cocoercive_of_convex` from the descent upper bound plus the first-order
  condition (standard textbook route); (a) ⇒ (c) then follows by expanding
  the square (the content of B&C Prop. 4.11 used in S2.4).
* Example A1.E S3.2 — `cos_not_convexOn`, `cos_lipschitz_gradient`
  (β = 1 is a valid bound), `cos_le` (bounded below, minimum at π),
  `cos_step_not_nonexpansive` (∀ α > 0), `cos_step_descends`
  (∀ α ∈ (0, 2), strict descent wherever ∇cos x ≠ 0).

NOT COVERED (remain audited prose): Remarks A1.R1–A1.R6 (sharpness
witnesses, sublevel-hypothesis witnesses (a), (d), (e), averagedness,
weighted sums, fixed metric, continuous time); the lower half of
B&C Lemma 2.64(i) (not used by A1); S3.1; the claim β(cos) = 1 as the
exact modulus (only "1 is a valid bound" is used).

Status tier: FORMALISED (statement + proof, no sorry) for Lemma A1.1 (a),
(b), (c), Lemma A1.2 (full equivalence and its "in particular"), and the
cos witness S3.2.
-/
import Mathlib

namespace OCF.A1
open Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### The descent coefficient and the one-dimensional segment bound -/

/-- The descent coefficient θ(α) = α(1 − αβ/2). -/
noncomputable def theta (β α : ℝ) : ℝ := α * (1 - α * β / 2)

/-- Chain rule along the line t ↦ x − t•g: φ′(s) = −⟨∇f(x − s g), g⟩. -/
lemma hasDerivAt_line {f : E → ℝ} {x g : E} {s : ℝ}
    (h : DifferentiableAt ℝ f (x - s • g)) :
    HasDerivAt (fun t : ℝ => f (x - t • g)) (-inner ℝ (gradient f (x - s • g)) g) s := by
  have h1 : HasDerivAt (fun t : ℝ => x - t • g) (-g) s := by
    simpa using ((hasDerivAt_id s).smul_const g).const_sub x
  have h2 := h.hasFDerivAt.comp_hasDerivAt s h1
  rw [← inner_gradient_left, inner_neg_right] at h2
  exact h2

/-- One-sided quadratic upper bound along a segment (B&C Lemma 2.64(i), upper half):
if f is differentiable at every x − s d, s ∈ [0, t], and
‖∇f(x − s d) − ∇f x‖ ≤ β‖(x − s d) − x‖ there, then
f(x − t d) ≤ f x − t⟨∇f x, d⟩ + (βt²/2)‖d‖². No convexity. -/
theorem upper_bound_on_segment {f : E → ℝ} {x d : E} {β t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc (0 : ℝ) t, DifferentiableAt ℝ f (x - s • d))
    (hL : ∀ s ∈ Icc (0 : ℝ) t,
      ‖gradient f (x - s • d) - gradient f x‖ ≤ β * ‖(x - s • d) - x‖) :
    f (x - t • d) ≤ f x - t * inner ℝ (gradient f x) d + β * t ^ 2 / 2 * ‖d‖ ^ 2 := by
  set g := gradient f x with hg
  let ψ : ℝ → ℝ := fun s => f (x - s • d) + (s * inner ℝ g d - β * s ^ 2 / 2 * ‖d‖ ^ 2)
  let ψ' : ℝ → ℝ := fun s =>
    -inner ℝ (gradient f (x - s • d)) d + (inner ℝ g d - β * s * ‖d‖ ^ 2)
  have hder : ∀ s ∈ Icc (0 : ℝ) t, HasDerivAt ψ (ψ' s) s := by
    intro s hs
    have h1 := hasDerivAt_line (hd s hs)
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ g d - β * s ^ 2 / 2 * ‖d‖ ^ 2)
        (inner ℝ g d - β * s * ‖d‖ ^ 2) s := by
      have := ((hasDerivAt_id' s).mul_const (inner ℝ g d)).sub
        ((((hasDerivAt_pow 2 s).const_mul β).div_const 2).mul_const (‖d‖ ^ 2))
      exact this.congr_deriv (by push_cast; ring)
    exact h1.add h2
  have hanti : AntitoneOn ψ (Icc 0 t) := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := ψ') (convex_Icc 0 t)
      (fun s hs => (hder s hs).continuousAt.continuousWithinAt) ?_ ?_
    · intro s hs
      rw [interior_Icc] at hs
      exact (hder s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hb := hL s (Ioo_subset_Icc_self hs)
      have hnorm : ‖(x - s • d) - x‖ = s * ‖d‖ := by
        rw [sub_sub_cancel_left, norm_neg, norm_smul, Real.norm_of_nonneg hs.1.le]
      rw [hnorm] at hb
      have hcs : -(‖gradient f (x - s • d) - g‖ * ‖d‖) ≤ inner ℝ (gradient f (x - s • d) - g) d := by
        have := abs_real_inner_le_norm (gradient f (x - s • d) - g) d
        linarith [neg_abs_le (inner ℝ (gradient f (x - s • d) - g) d)]
      have hsplit : inner ℝ (gradient f (x - s • d)) d
          = inner ℝ (gradient f (x - s • d) - g) d + inner ℝ g d := by
        rw [inner_sub_left]; ring
      have hm : ‖gradient f (x - s • d) - g‖ * ‖d‖ ≤ β * (s * ‖d‖) * ‖d‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg _)
      simp only [ψ']
      rw [hsplit]
      nlinarith
  have := hanti (left_mem_Icc.2 ht) (right_mem_Icc.2 ht) ht
  simp only [ψ, zero_smul, sub_zero, zero_mul] at this
  linarith

/-- The descent estimate along an initial piece of the step segment (S1.4(ii)):
only gradients at points of the piece enter. -/
theorem descent_on_segment {f : E → ℝ} {x : E} {β t : ℝ} (ht : 0 ≤ t)
    (hd : ∀ s ∈ Icc (0 : ℝ) t, DifferentiableAt ℝ f (x - s • gradient f x))
    (hL : ∀ s ∈ Icc (0 : ℝ) t,
      ‖gradient f (x - s • gradient f x) - gradient f x‖ ≤ β * ‖(x - s • gradient f x) - x‖) :
    f (x - t • gradient f x) ≤ f x - theta β t * ‖gradient f x‖ ^ 2 := by
  have := upper_bound_on_segment ht hd hL
  rw [real_inner_self_eq_norm_sq] at this
  unfold theta
  linarith


/-! ### Lemma A1.1 (a), (c), (b) -/

/-- **Lemma A1.1(a).** H1 (f differentiable, ∇f β-Lipschitz on E): for every x and every
α > 0, f(x − α∇f x) ≤ f x − θ(α)‖∇f x‖². No convexity. -/
theorem descent_global {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f)
    (hL : ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖) (x : E) {α : ℝ} (hα : 0 < α) :
    f (x - α • gradient f x) ≤ f x - theta β α * ‖gradient f x‖ ^ 2 :=
  descent_on_segment hα.le (fun _ _ => hf _) (fun _ _ => hL _ _)

/-- **Lemma A1.1(c), first clause.** θ(α) > 0 ⇔ α ∈ (0, 2/β). -/
theorem theta_pos_iff {β : ℝ} (hβ : 0 < β) (α : ℝ) :
    0 < theta β α ↔ 0 < α ∧ α < 2 / β := by
  unfold theta
  rw [lt_div_iff₀ hβ]
  constructor
  · intro h
    by_contra hc
    rw [not_and_or, not_lt, not_lt] at hc
    rcases hc with hc | hc
    · have : α * β ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hc hβ.le
      nlinarith
    · nlinarith
  · rintro ⟨h1, h2⟩
    exact mul_pos h1 (by linarith)

/-- **Lemma A1.1(c), second clause** (for step sizes α > 0): θ(α) ≥ α/2 ⇔ α ≤ 1/β. -/
theorem half_le_theta_iff {β : ℝ} (hβ : 0 < β) {α : ℝ} (hα : 0 < α) :
    α / 2 ≤ theta β α ↔ α ≤ 1 / β := by
  unfold theta
  rw [le_div_iff₀ hβ]
  constructor
  · intro h
    by_contra hc
    nlinarith
  · intro h
    nlinarith

/-- **Lemma A1.1(c), third clause (maximiser).** θ(α) ≤ θ(1/β) for every α. -/
theorem theta_le_theta_inv {β : ℝ} (hβ : 0 < β) (α : ℝ) : theta β α ≤ theta β (1 / β) := by
  unfold theta
  have : β * (α - 1 / β) ^ 2 ≥ 0 := by positivity
  field_simp
  field_simp at this
  nlinarith [this]

/-- **Lemma A1.1(c), third clause (value).** θ(1/β) = 1/(2β). -/
theorem theta_inv {β : ℝ} (hβ : 0 < β) : theta β (1 / β) = 1 / (2 * β) := by
  unfold theta
  field_simp
  ring

/-- **Lemma A1.1(b) [NOVEL, S1.4].** H1′: f continuous on E, differentiable at every point
of S_τ = {f ≤ τ}, ‖∇f u − ∇f v‖ ≤ β‖u − v‖ for u, v ∈ S_τ, β > 0; H3a: α ∈ (0, 2/β].
Then for every x ∈ S_τ the whole segment {x − t∇f x : t ∈ [0, α]} lies in S_τ and
f(x − α∇f x) ≤ f x − θ(α)‖∇f x‖². No convexity of f or of S_τ. -/
theorem descent_sublevel {f : E → ℝ} {τ β α : ℝ} (hcont : Continuous f)
    (hdiff : ∀ y, f y ≤ τ → DifferentiableAt ℝ f y)
    (hL : ∀ u v, f u ≤ τ → f v ≤ τ → ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖)
    (hβ : 0 < β) {x : E} (hx : f x ≤ τ) (hα : 0 < α) (hα2 : α ≤ 2 / β) :
    (∀ t ∈ Icc (0 : ℝ) α, f (x - t • gradient f x) ≤ τ) ∧
      f (x - α • gradient f x) ≤ f x - theta β α * ‖gradient f x‖ ^ 2 := by
  set g := gradient f x with hg
  have hφcont : Continuous fun t : ℝ => f (x - t • g) :=
    hcont.comp (continuous_const.sub (continuous_id.smul continuous_const))
  have hseg : ∀ t ∈ Icc (0 : ℝ) α, f (x - t • g) ≤ τ := by
    by_contra hcon
    push Not at hcon
    set T := {t ∈ Icc (0 : ℝ) α | τ < f (x - t • g)} with hT
    have hTne : T.Nonempty := by
      obtain ⟨t, ht, h⟩ := hcon
      exact ⟨t, ht, h⟩
    have hTbdd : BddBelow T := ⟨0, fun t ht => ht.1.1⟩
    set m := sInf T with hm
    have hm0 : 0 ≤ m := le_csInf hTne (fun t ht => ht.1.1)
    have hmα : m ≤ α := by
      obtain ⟨t, ht⟩ := hTne
      exact (csInf_le hTbdd ht).trans ht.1.2
    have hbefore : ∀ u ∈ Ico 0 m, f (x - u • g) ≤ τ := by
      intro u hu
      by_contra h
      push Not at h
      exact notMem_of_lt_csInf hu.2 hTbdd ⟨⟨hu.1, hu.2.le.trans hmα⟩, h⟩
    have hupto : ∀ u ∈ Icc 0 m, f (x - u • g) ≤ τ := by
      rcases eq_or_lt_of_le hm0 with h0 | hpos
      · intro u hu
        have : u = 0 := le_antisymm (h0 ▸ hu.2) hu.1
        subst this
        simpa using hx
      · have hclosed : IsClosed {t : ℝ | f (x - t • g) ≤ τ} :=
          isClosed_le hφcont continuous_const
        have := hclosed.closure_subset_iff.2 hbefore
        rwa [closure_Ico hpos.ne] at this
    have hgne : g ≠ 0 := by
      intro hg0
      obtain ⟨t, ht⟩ := hTne
      have := ht.2
      simp [hg0] at this
      linarith
    have hgpos : 0 < ‖g‖ ^ 2 := by positivity
    have hev : ∀ᶠ t in 𝓝[>] m, f (x - t • g) ≤ τ := by
      rcases eq_or_lt_of_le hm0 with h0 | hpos
      · -- m = 0: the right derivative at 0 is -‖g‖² < 0
        rw [← h0]
        have hd0 := hasDerivAt_line (f := f) (x := x) (g := g) (s := 0) (by simpa using hdiff x hx)
        simp only [zero_smul, sub_zero] at hd0
        rw [← hg, real_inner_self_eq_norm_sq] at hd0
        have hlt : -‖g‖ ^ 2 < 0 := by linarith
        filter_upwards [hd0.tendsto_slope_zero_right.eventually_lt_const hlt, self_mem_nhdsWithin]
          with t ht htpos
        simp only [zero_add, zero_smul, sub_zero, smul_eq_mul] at ht
        have htpos' : (0 : ℝ) < t := htpos
        have : f (x - t • g) - f x < 0 := by
          by_contra hc
          push Not at hc
          have := mul_nonneg (inv_nonneg.2 htpos'.le) hc
          linarith
        linarith
      · -- m > 0: the descent estimate keeps φ(m) strictly below τ
        obtain ⟨t, ht⟩ := hTne
        have hmt : m < t := by
          rcases eq_or_lt_of_le (csInf_le hTbdd ht) with h | h
          · exfalso
            have := hupto t ⟨ht.1.1, le_of_eq h.symm⟩
            linarith [ht.2]
          · exact h
        have hm2 : m < 2 / β := lt_of_lt_of_le (hmt.trans_le ht.1.2) hα2
        have hθ : 0 < theta β m := (theta_pos_iff hβ m).2 ⟨hpos, hm2⟩
        have hdesc := descent_on_segment hm0 (fun s hs => hdiff _ (hupto s hs))
          (fun s hs => hL _ _ (hupto s hs) hx)
        have hlt : f (x - m • g) < τ := by
          have := mul_pos hθ hgpos
          linarith
        exact (((hφcont.tendsto m).eventually_lt_const hlt).filter_mono nhdsWithin_le_nhds).mono
          fun _ h => h.le
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
    obtain ⟨t, ht, htu⟩ := exists_lt_of_csInf_lt hTne hu
    have hmt : m ≤ t := csInf_le hTbdd ht
    rcases eq_or_lt_of_le hmt with h | h
    · have := hupto t ⟨ht.1.1, le_of_eq h.symm⟩
      linarith [ht.2]
    · have := hsub ⟨h, htu⟩
      simp only [mem_setOf_eq] at this
      linarith [ht.2]
  exact ⟨hseg, descent_on_segment hα.le (fun s hs => hdiff _ (hseg s hs))
    (fun s hs => hL _ _ (hseg s hs) hx)⟩

/-- Lemma A1.1(b), instantiated at ℝᵈ = `EuclideanSpace ℝ (Fin d)`. -/
theorem descent_sublevel_euclidean {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {τ β α : ℝ}
    (hcont : Continuous f) (hdiff : ∀ y, f y ≤ τ → DifferentiableAt ℝ f y)
    (hL : ∀ u v, f u ≤ τ → f v ≤ τ → ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖)
    (hβ : 0 < β) {x : EuclideanSpace ℝ (Fin d)} (hx : f x ≤ τ) (hα : 0 < α) (hα2 : α ≤ 2 / β) :
    (∀ t ∈ Icc (0 : ℝ) α, f (x - t • gradient f x) ≤ τ) ∧
      f (x - α • gradient f x) ≤ f x - theta β α * ‖gradient f x‖ ^ 2 :=
  descent_sublevel hcont hdiff hL hβ hx hα hα2

/-- Lemma A1.1(a), instantiated at ℝᵈ = `EuclideanSpace ℝ (Fin d)`. -/
theorem descent_global_euclidean {d : ℕ} {f : EuclideanSpace ℝ (Fin d) → ℝ} {β : ℝ}
    (hf : Differentiable ℝ f) (hL : ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖)
    (x : EuclideanSpace ℝ (Fin d)) {α : ℝ} (hα : 0 < α) :
    f (x - α • gradient f x) ≤ f x - theta β α * ‖gradient f x‖ ^ 2 :=
  descent_global hf hL x hα

/-! ### Lemma A1.2 — nonexpansiveness ⇔ convexity -/

/-- ∇f is monotone. -/
def GradMonotone (f : E → ℝ) : Prop :=
  ∀ x y, 0 ≤ inner ℝ (gradient f x - gradient f y) (x - y)

/-- Id − α∇f is nonexpansive. -/
def StepNonexpansive (f : E → ℝ) (α : ℝ) : Prop :=
  ∀ x y, ‖(x - α • gradient f x) - (y - α • gradient f y)‖ ≤ ‖x - y‖

omit [CompleteSpace E] in
lemma line_eq (x y : E) (t : ℝ) : x - t • (x - y) = (1 - t) • x + t • y := by module

/-- Convex + differentiable ⇒ first-order condition. -/
lemma firstOrder_of_convexOn {f : E → ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f)
    (x y : E) : f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  have hd := hasDerivAt_line (f := f) (x := x) (g := x - y) (s := 0) (by simpa using hf x)
  simp only [zero_smul, sub_zero] at hd
  have hlim := hd.tendsto_slope_zero_right
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ • (f (x - (0 + t) • (x - y)) - f (x - (0 : ℝ) • (x - y))) ≤ f y - f x := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    simp only [zero_add, zero_smul, sub_zero, smul_eq_mul]
    have hcv := hc.2 (mem_univ x) (mem_univ y) (by linarith [ht.2] : (0 : ℝ) ≤ 1 - t) ht.1.le
      (by ring)
    rw [← line_eq] at hcv
    simp only [smul_eq_mul] at hcv
    rw [inv_mul_le_iff₀ ht.1]
    nlinarith
  have := le_of_tendsto hlim hev
  rw [show y - x = -(x - y) by abel, inner_neg_right]
  linarith

/-- First-order condition ⇒ convex. -/
lemma convexOn_of_firstOrder {f : E → ℝ}
    (h : ∀ x y, f x + inner ℝ (gradient f x) (y - x) ≤ f y) : ConvexOn ℝ univ f := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  obtain rfl : b = 1 - a := by linarith
  set z := a • x + (1 - a) • y with hz
  have h1 := h z x
  have h2 := h z y
  have key : a * inner ℝ (gradient f z) (x - z) + (1 - a) * inner ℝ (gradient f z) (y - z) = 0 := by
    rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
    have : a • (x - z) + (1 - a) • (y - z) = 0 := by rw [hz]; module
    rw [this, inner_zero_right]
  simp only [smul_eq_mul]
  have e1 := mul_le_mul_of_nonneg_left h1 ha
  have e2 := mul_le_mul_of_nonneg_left h2 hb
  nlinarith

/-- First-order condition ⇒ monotone gradient. -/
lemma gradMonotone_of_firstOrder {f : E → ℝ}
    (h : ∀ x y, f x + inner ℝ (gradient f x) (y - x) ≤ f y) : GradMonotone f := by
  intro x y
  have h1 := h x y
  have h2 := h y x
  rw [show y - x = -(x - y) by abel, inner_neg_right] at h1
  rw [inner_sub_left]
  linarith

/-- Monotone gradient ⇒ first-order condition (mean value theorem on the segment). -/
lemma firstOrder_of_gradMonotone {f : E → ℝ} (hf : Differentiable ℝ f) (hm : GradMonotone f)
    (x y : E) : f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => f (x - t • (x - y)))
    (fun t => -inner ℝ (gradient f (x - t • (x - y))) (x - y)) zero_lt_one
    (fun t _ => (hasDerivAt_line (hf _)).continuousAt.continuousWithinAt)
    (fun t _ => hasDerivAt_line (hf _))
  simp only [one_smul, sub_sub_cancel, zero_smul, sub_zero, sub_zero, div_one] at hcd
  have hmc := hm (x - c • (x - y)) x
  rw [show x - c • (x - y) - x = -(c • (x - y)) by abel, inner_neg_right, inner_smul_right,
    inner_sub_left] at hmc
  have hc0 := hc.1
  have : inner ℝ (gradient f (x - c • (x - y))) (x - y) ≤ inner ℝ (gradient f x) (x - y) := by
    by_contra hcon
    push Not at hcon
    nlinarith
  rw [show y - x = -(x - y) by abel, inner_neg_right]
  linarith

/-- A1.2 (a) ⇔ (b) (B&C Prop. 17.7 (i)⇔(iii)), for differentiable f. -/
theorem convexOn_iff_gradMonotone {f : E → ℝ} (hf : Differentiable ℝ f) :
    ConvexOn ℝ univ f ↔ GradMonotone f :=
  ⟨fun hc => gradMonotone_of_firstOrder (firstOrder_of_convexOn hf hc),
   fun hm => convexOn_of_firstOrder (firstOrder_of_gradMonotone hf hm)⟩

omit [CompleteSpace E] in
lemma step_sub (x y gx gy : E) (α : ℝ) :
    (x - α • gx) - (y - α • gy) = (x - y) - α • (gx - gy) := by module

/-- A1.2 (d) ⇒ (b) (S2.5): no Lipschitz bound, no bound on α. -/
theorem gradMonotone_of_stepNonexpansive {f : E → ℝ} {α : ℝ} (hα : 0 < α)
    (h : StepNonexpansive f α) : GradMonotone f := by
  intro x y
  have hx := h x y
  rw [step_sub] at hx
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hx 2
  rw [norm_sub_sq_real, norm_smul, Real.norm_of_nonneg hα.le, inner_smul_right,
    real_inner_comm] at hsq
  have : 0 ≤ α * inner ℝ (gradient f x - gradient f y) (x - y) := by nlinarith [sq_nonneg (α * ‖gradient f x - gradient f y‖)]
  exact (mul_nonneg_iff_of_pos_left hα).1 this

/-- Half of the Baillon–Haddad argument. -/
lemma cocoercive_half {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f)
    (hL : ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖) (hβ : 0 < β) (x y : E) :
    f x - f y ≤ inner ℝ (gradient f x) (x - y)
      - (1 / β) * ‖gradient f y - gradient f x‖ ^ 2 / 2 := by
  set w := gradient f y - gradient f x with hw
  set b := 1 / β with hb
  have hβb : β * b = 1 := by rw [hb]; field_simp
  have hU := upper_bound_on_segment (f := f) (x := y) (d := b • w) (β := β) (t := 1) zero_le_one
    (fun _ _ => hf _) (fun _ _ => hL _ _)
  have hF := firstOrder_of_convexOn hf hc x (y - (1 : ℝ) • (b • w))
  rw [norm_smul, mul_pow, Real.norm_of_nonneg (by positivity), inner_smul_right] at hU
  simp only [one_smul, one_pow, one_mul, mul_one] at hU hF
  rw [show y - b • w - x = (y - x) - b • w by abel, inner_sub_right, inner_smul_right] at hF
  have hww : ‖w‖ ^ 2 = inner ℝ (gradient f y) w - inner ℝ (gradient f x) w := by
    rw [← real_inner_self_eq_norm_sq, hw, inner_sub_left]
  have hq : β * b ^ 2 * ‖w‖ ^ 2 / 2 = b * ‖w‖ ^ 2 / 2 := by
    rw [show β * b ^ 2 * ‖w‖ ^ 2 / 2 = (β * b) * (b * ‖w‖ ^ 2) / 2 by ring, hβb]; ring
  have hbw : b * ‖w‖ ^ 2 = b * inner ℝ (gradient f y) w - b * inner ℝ (gradient f x) w := by
    rw [hww]; ring
  rw [show x - y = -(y - x) by abel, inner_neg_right]
  nlinarith

/-- Baillon–Haddad (B&C Cor. 18.17): convex + β-Lipschitz gradient ⇒ ∇f is
(1/β)-cocoercive. -/
theorem cocoercive_of_convex {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ univ f)
    (hL : ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖) (hβ : 0 < β) (x y : E) :
    (1 / β) * ‖gradient f x - gradient f y‖ ^ 2
      ≤ inner ℝ (gradient f x - gradient f y) (x - y) := by
  have h1 := cocoercive_half hf hc hL hβ x y
  have h2 := cocoercive_half hf hc hL hβ y x
  rw [norm_sub_rev (gradient f y)] at h1
  rw [inner_sub_left]
  rw [show y - x = -(x - y) by abel, inner_neg_right] at h2
  linarith

/-- A1.2 (a) ⇒ (c) (S2.2–S2.4). -/
theorem stepNonexpansive_of_convex {f : E → ℝ} {β α : ℝ} (hf : Differentiable ℝ f)
    (hc : ConvexOn ℝ univ f)
    (hL : ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖) (hβ : 0 < β)
    (hα : 0 < α) (hα2 : α ≤ 2 / β) : StepNonexpansive f α := by
  intro x y
  rw [step_sub]
  have hco := cocoercive_of_convex hf hc hL hβ x y
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero, norm_sub_sq_real,
    norm_smul, Real.norm_of_nonneg hα.le, inner_smul_right, real_inner_comm]
  have hab : α * β ≤ 2 := by rwa [le_div_iff₀ hβ] at hα2
  have hb : (1 / β) * ‖gradient f x - gradient f y‖ ^ 2 * (α * β) ≤ (1 / β) * ‖gradient f x - gradient f y‖ ^ 2 * 2 :=
    mul_le_mul_of_nonneg_left hab (by positivity)
  have hb' : (1 / β) * ‖gradient f x - gradient f y‖ ^ 2 * (α * β) = α * ‖gradient f x - gradient f y‖ ^ 2 := by
    field_simp
  nlinarith

/-- **Lemma A1.2.** Under H1 (f differentiable, ∇f β-Lipschitz, β > 0):
(a) f convex ⇔ (b) ∇f monotone ⇔ (c) Id − α∇f nonexpansive for every α ∈ (0, 2/β]
⇔ (d) Id − α∇f nonexpansive for some α > 0. -/
theorem nonexpansive_tfae {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f)
    (hL : ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖) (hβ : 0 < β) :
    List.TFAE [ConvexOn ℝ univ f, GradMonotone f,
      ∀ α, 0 < α → α ≤ 2 / β → StepNonexpansive f α,
      ∃ α, 0 < α ∧ StepNonexpansive f α] := by
  tfae_have 1 ↔ 2 := convexOn_iff_gradMonotone hf
  tfae_have 1 → 3 := fun hc α hα hα2 => stepNonexpansive_of_convex hf hc hL hβ hα hα2
  tfae_have 3 → 4 := fun h => ⟨2 / β, by positivity, h _ (by positivity) le_rfl⟩
  tfae_have 4 → 2 := fun ⟨α, hα, h⟩ => gradMonotone_of_stepNonexpansive hα h
  tfae_finish

/-- **Lemma A1.2, "in particular".** If f is not convex, Id − α∇f is nonexpansive for
no α > 0 (S2.5–S2.6: uses only differentiability, no Lipschitz bound). -/
theorem not_stepNonexpansive_of_not_convex {f : E → ℝ} (hf : Differentiable ℝ f)
    (hnc : ¬ ConvexOn ℝ univ f) {α : ℝ} (hα : 0 < α) : ¬ StepNonexpansive f α :=
  fun h => hnc ((convexOn_iff_gradMonotone hf).2 (gradMonotone_of_stepNonexpansive hα h))

/-! ### Example A1.E, S3.2 — f = cos on ℝ: both regimes on one function -/

/-- ∇cos = −sin. -/
lemma gradient_cos : gradient Real.cos = fun x => -Real.sin x := by
  funext x
  rw [gradient_eq_deriv', Real.deriv_cos]

/-- cos is not convex. -/
theorem cos_not_convexOn : ¬ ConvexOn ℝ univ Real.cos := by
  intro h
  have := h.2 (mem_univ Real.pi) (mem_univ (-Real.pi)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  have e : (1 / 2 : ℝ) • Real.pi + (1 / 2 : ℝ) • -Real.pi = 0 := by simp [smul_eq_mul]
  rw [e] at this
  simp [smul_eq_mul, Real.cos_neg, Real.cos_pi] at this
  linarith

/-- β = 1 is a valid Lipschitz bound for ∇cos = −sin. -/
theorem cos_lipschitz_gradient (u v : ℝ) :
    ‖gradient Real.cos u - gradient Real.cos v‖ ≤ 1 * ‖u - v‖ := by
  rw [gradient_cos, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    show -Real.sin u - -Real.sin v = -(Real.sin u - Real.sin v) by ring, abs_neg]
  exact Real.abs_sin_sub_sin_le u v

/-- cos is bounded below and attains its minimum (at π). -/
theorem cos_le (x : ℝ) : Real.cos Real.pi ≤ Real.cos x := by
  rw [Real.cos_pi]
  exact Real.neg_one_le_cos x

/-- For every α > 0, Id − α∇cos (= x ↦ x + α sin x) is not nonexpansive. -/
theorem cos_step_not_nonexpansive {α : ℝ} (hα : 0 < α) : ¬ StepNonexpansive Real.cos α := by
  intro h
  have := h (Real.pi / 2) 0
  rw [gradient_cos] at this
  simp only [Real.sin_pi_div_two, Real.sin_zero, neg_zero, sub_zero, smul_eq_mul,
    mul_neg, mul_one, sub_neg_eq_add, Real.norm_eq_abs] at this
  have hp : 0 < Real.pi / 2 := by positivity
  rw [abs_of_pos (by linarith), abs_of_pos hp] at this
  linarith

/-- Yet every step with α ∈ (0, 2) strictly decreases cos wherever ∇cos ≠ 0
(Lemma A1.1(a) with β = 1). -/
theorem cos_step_descends {α : ℝ} (hα : 0 < α) (hα2 : α < 2) (x : ℝ)
    (hx : gradient Real.cos x ≠ 0) :
    Real.cos (x - α • gradient Real.cos x) < Real.cos x := by
  have hd := descent_global Real.differentiable_cos cos_lipschitz_gradient x hα
  have hθ : 0 < theta 1 α := (theta_pos_iff one_pos α).2 ⟨hα, by simpa using hα2⟩
  have hg : 0 < ‖gradient Real.cos x‖ ^ 2 := by positivity
  nlinarith [mul_pos hθ hg]

end OCF.A1

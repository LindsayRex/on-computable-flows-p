/-
B1p (Uniform kernel-transversal strong convexity) — Theorem (B1′) part (a),
the uniform restricted-monotonicity bound, and its clause Δ_w ≥ (minᵢ aᵢ)·s.

Source of truth: project_plan/done/proof_audits/B1p_uniform_composite_gap/01_derivation.md
(adjudicated 2026-10-09, AUTHOR-APPROVED 2026-10-09;
03_adjudication.md decision 4 commissions this Lean pass). Setting §0,
Step 0.1, Lemma 1 (iii), Theorem (a), Steps T.1–T.3, T.5's last clause.

STATEMENT FORMALISED (Theorem (a), displayed inequality):
  for terms with valid kernel attributes (Kᵢ, νᵢ),
    ⟨∇fᵢ(x) − ∇fᵢ(y), x − y⟩ ≥ νᵢ‖P_{Kᵢ^⊥}(x − y)‖²   (H3), νᵢ > 0,
  and weights wᵢ > 0 (H2), F = Σᵢ wᵢfᵢ satisfies
    ⟨∇F(x) − ∇F(y), x − y⟩ ≥ Δ_w‖x − y‖²   for all x, y,
  with aᵢ = wᵢνᵢ and Δ_w = Δ_w(K, a) the Kernel Gram defect of Step 0.1;
  and Δ_w ≥ (minᵢ wᵢνᵢ)·s (Lemma 1 (iii) / Theorem (a)'s last clause).

DEFINITIONAL MAP:
* ℝᵈ — `EuclideanSpace ℝ (Fin d)` (Euclidean inner product and norm;
  `inner ℝ`, `‖·‖`).
* Kᵢ — an arbitrary `Submodule ℝ (EuclideanSpace ℝ (Fin d))` (Step 0.1:
  arbitrary subspaces, Kᵢ = ℝᵈ and Kᵢ = {0} allowed).
* P_{Kᵢ^⊥} — Mathlib's orthogonal projection `(K i)ᗮ.starProjection`.
* (H3) — hypothesis `hval`, verbatim, νᵢ > 0 as `hν`.
* Bᵢ — `b i : Fin (k i) → EuclideanSpace ℝ (Fin d)` with `Orthonormal ℝ (b i)`
  and `span (range (b i)) = K i` (an orthonormal basis of Kᵢ; ANY choice,
  as in Step 0.1; kᵢ = 0 allowed). Δ_w and s are computed with
  T1SharpBound.lean's `deltaW` / T1GramBound.lean's `gramMatrix`, `lambdaMax`
  on the coordinate columns `(b i p).ofLp` — exactly T1's formulas
  adopted verbatim for arbitrary subspaces (Step 0.1).
* ∇fᵢ — two renderings:
  (1) `uniform_composite_gap_of_restricted_monotone`: arbitrary maps
      gᵢ : ℝᵈ → ℝᵈ satisfying (H3) in place of ∇fᵢ, with the composite
      map Σᵢ wᵢ • gᵢ in place of ∇F (the inequality is a statement about
      the gradient maps only; this is the commissioned map-level form);
  (2) `uniform_composite_gap`: the gradient instance itself — fᵢ C¹
      (`ContDiff ℝ 1`, (H1)), (H3) stated with Mathlib's `gradient`, and
      the conclusion about `gradient` of F = fun x => Σᵢ wᵢ fᵢ x. Proved
      from (1) via ∇F = Σᵢ wᵢ∇fᵢ (linearity of the derivative, Step T.1).

PROOF ROUTE: T.1 (sum the per-term inequalities with wᵢ > 0);
T.2 (‖P_{Kᵢ^⊥}v‖² = ‖v‖² − Σₚ⟨bᵢₚ, v⟩², Pythagoras with P_{Kᵢ}v =
Σₚ⟨bᵢₚ, v⟩bᵢₚ — `norm_sq_starProjection_orthogonal`); T.3 is the
flat-minorant inequality vᵀ(Σaᵢ P_{Kᵢ^⊥})v ≥ Δ_w‖v‖², which is
T1SharpBound.lean's `flat_minorant_ge` (the inequality half of Lemma 1(i)
— all that T.3 consumes). Lemma 1 (iii) is T1SharpBound.lean's
`deltaW_ge_min_mul_defect`, proved directly for arbitrary orthonormal
families (so Step 1.5's drop-the-Kᵢ = ℝᵈ-terms reduction is not needed in
Lean).

NOT COVERED (remain audited prose): the "consequently" clauses of (a)
(C(F, Δ_w), σ(F) ≥ Δ_w, strong convexity when ∩Kᵢ = {0}, which need the
monotone-gradient ⇒ convex step, Bauschke–Combettes 17.7, and Lemma 1(ii)),
Lemma 1 (i)'s equality and (ii), and parts (b), (c).

Status tier: FORMALISED (statement + proof, no sorry) for the displayed
inequality of (a) and the Δ_w ≥ (minᵢ aᵢ)·s clause.
-/
import Mathlib
import OcfVerification.T1SharpBound

open Matrix BigOperators

namespace OCF

variable {d n : ℕ}

/-! ### Step T.2: the projection identity, and the bridge to coordinates -/

/-- Pythagoras with an orthonormal basis of K:
‖P_{K^⊥}v‖² = ‖v‖² − Σₚ⟨bₚ, v⟩². -/
lemma norm_sq_starProjection_orthogonal {κ : ℕ}
    {K : Submodule ℝ (EuclideanSpace ℝ (Fin d))} {b : Fin κ → EuclideanSpace ℝ (Fin d)}
    (hbo : Orthonormal ℝ b) (hbs : Submodule.span ℝ (Set.range b) = K)
    (v : EuclideanSpace ℝ (Fin d)) :
    ‖Kᗮ.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - ∑ p, (inner ℝ (b p) v) ^ 2 := by
  set u : EuclideanSpace ℝ (Fin d) := ∑ p, inner ℝ (b p) v • b p with hu
  have hPK : K.starProjection v = u := by
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · rw [← hbs]
      exact Submodule.sum_mem _ fun p _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨p, rfl⟩)
    · intro z hz
      rw [← hbs] at hz
      induction hz using Submodule.span_induction with
      | mem y hy =>
          obtain ⟨q, rfl⟩ := hy
          rw [inner_sub_left, hu, hbo.inner_left_fintype, real_inner_comm]
          simp
      | zero => simp
      | add y z _ _ ihy ihz => rw [inner_add_right, ihy, ihz, add_zero]
      | smul c y _ ih => rw [inner_smul_right, ih, mul_zero]
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection v K
  have huu : ‖u‖ ^ 2 = ∑ p, (inner ℝ (b p) v) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, hu, hbo.inner_sum]
    simp [sq]
  rw [hPK, huu] at hpy
  linarith

/-- Coordinates: the real Euclidean inner product is the dot product of
the underlying coordinate vectors. -/
lemma inner_eq_ofLp_dotProduct (x y : EuclideanSpace ℝ (Fin d)) :
    inner ℝ x y = x.ofLp ⬝ᵥ y.ofLp := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]

lemma norm_sq_eq_ofLp_dotProduct (x : EuclideanSpace ℝ (Fin d)) :
    ‖x‖ ^ 2 = x.ofLp ⬝ᵥ x.ofLp := by
  rw [← real_inner_self_eq_norm_sq, inner_eq_ofLp_dotProduct]

/-- Orthonormality in coordinates, in the form T1's Gram files use. -/
lemma ofLp_dotProduct_of_orthonormal {κ : ℕ} {b : Fin κ → EuclideanSpace ℝ (Fin d)}
    (hbo : Orthonormal ℝ b) (p q : Fin κ) :
    (b p).ofLp ⬝ᵥ (b q).ofLp = if p = q then 1 else 0 := by
  rw [← inner_eq_ofLp_dotProduct]
  exact orthonormal_iff_ite.mp hbo p q

/-! ### Theorem (B1′)(a), map-level form -/

/-- **B1p Theorem (a), displayed inequality — map-level form.** For maps
gᵢ (in the role of ∇fᵢ) satisfying the restricted monotonicity of a kernel
attribute (Kᵢ, νᵢ), νᵢ > 0, and weights wᵢ > 0, the composite map
Σᵢ wᵢ gᵢ (in the role of ∇F) satisfies
⟨G(x) − G(y), x − y⟩ ≥ Δ_w‖x − y‖², with Δ_w = Δ_w(K, (wᵢνᵢ)) the Kernel
Gram defect computed from ANY orthonormal bases bᵢ of the Kᵢ. -/
theorem uniform_composite_gap_of_restricted_monotone
    (_hn : 0 < n) (_hd : 0 < d)
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (K : Fin n → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (hval : ∀ i x y, ν i * ‖(K i)ᗮ.starProjection (x - y)‖ ^ 2
      ≤ inner ℝ (g i x - g i y) (x - y))
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → EuclideanSpace ℝ (Fin d))
    (hbo : ∀ i, Orthonormal ℝ (b i))
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = K i)
    (x y : EuclideanSpace ℝ (Fin d)) :
    deltaW (fun i p => (b i p).ofLp) (fun i => w i * ν i) * ‖x - y‖ ^ 2
      ≤ inner ℝ ((∑ i, w i • g i) x - (∑ i, w i • g i) y) (x - y) := by
  set v := x - y with hv
  have ha : ∀ i, 0 ≤ w i * ν i := fun i => (mul_pos (hw i) (hν i)).le
  -- T.3 (flat minorant) in coordinates
  have hflat := flat_minorant_ge ha (fun i p => (b i p).ofLp) v.ofLp
  -- T.2: rewrite coordinates back to ‖P_{Kᵢ^⊥} v‖²
  have hT2 : ∀ i, v.ofLp ⬝ᵥ v.ofLp - ∑ p, ((b i p).ofLp ⬝ᵥ v.ofLp) ^ 2
      = ‖(K i)ᗮ.starProjection v‖ ^ 2 := by
    intro i
    rw [norm_sq_starProjection_orthogonal (hbo i) (hbs i), norm_sq_eq_ofLp_dotProduct]
    simp only [inner_eq_ofLp_dotProduct]
  simp only [hT2] at hflat
  rw [← norm_sq_eq_ofLp_dotProduct] at hflat
  -- T.1: sum the per-term inequalities with wᵢ > 0
  have hT1 : ∑ i, w i * ν i * ‖(K i)ᗮ.starProjection v‖ ^ 2
      ≤ inner ℝ ((∑ i, w i • g i) x - (∑ i, w i • g i) y) v := by
    have hexp : inner ℝ ((∑ i, w i • g i) x - (∑ i, w i • g i) y) v
        = ∑ i, w i * inner ℝ (g i x - g i y) v := by
      simp only [Finset.sum_apply, Pi.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub,
        sum_inner, real_inner_smul_left]
    rw [hexp]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hval i x y) (hw i).le
  exact hflat.trans hT1

/-- **B1p Theorem (a), last clause (Lemma 1 (iii)):**
Δ_w ≥ (minᵢ wᵢνᵢ)·s, s = n − λ_max(G), for arbitrary subspaces with
orthonormal bases (Step 0.1's definitional extension). -/
theorem uniform_composite_gap_defect_bound (hn : 0 < n)
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → EuclideanSpace ℝ (Fin d))
    (hbo : ∀ i, Orthonormal ℝ (b i)) :
    (⨅ i, w i * ν i) * ((n : ℝ) - lambdaMax (gramMatrix fun i p => (b i p).ofLp))
      ≤ deltaW (fun i p => (b i p).ofLp) (fun i => w i * ν i) :=
  deltaW_ge_min_mul_defect hn (fun i => (mul_pos (hw i) (hν i)).le) _
    fun i => ofLp_dotProduct_of_orthonormal (hbo i)

/-! ### Theorem (B1′)(a), gradient form -/

/-- ∇(Σᵢ wᵢfᵢ) = Σᵢ wᵢ∇fᵢ for differentiable fᵢ (Step T.1's linearity). -/
lemma gradient_weighted_sum (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (w : Fin n → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (x : EuclideanSpace ℝ (Fin d)) :
    gradient (fun z => ∑ i, w i * f i z) x = (∑ i, w i • gradient (f i)) x := by
  have hF : HasFDerivAt (fun z => ∑ i, w i * f i z) (∑ i, w i • fderiv ℝ (f i) x) x :=
    HasFDerivAt.fun_sum fun i _ => ((hf i x).hasFDerivAt).const_mul (w i)
  rw [gradient, hF.fderiv, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smulₛₗ, Pi.smul_apply, gradient]
  simp

/-- **B1p Theorem (a), displayed inequality — gradient form.** (H1) fᵢ ∈ C¹,
(H2) wᵢ > 0, (H3) (Kᵢ, νᵢ) valid kernel attributes:
⟨∇fᵢ(x) − ∇fᵢ(y), x − y⟩ ≥ νᵢ‖P_{Kᵢ^⊥}(x − y)‖², νᵢ > 0. Then for
F = Σᵢ wᵢfᵢ and all x, y: ⟨∇F(x) − ∇F(y), x − y⟩ ≥ Δ_w‖x − y‖². -/
theorem uniform_composite_gap
    (hn : 0 < n) (hd : 0 < d)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i))
    (w : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (K : Fin n → Submodule ℝ (EuclideanSpace ℝ (Fin d))) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i)
    (hval : ∀ i x y, ν i * ‖(K i)ᗮ.starProjection (x - y)‖ ^ 2
      ≤ inner ℝ (gradient (f i) x - gradient (f i) y) (x - y))
    {k : Fin n → ℕ} (b : (i : Fin n) → Fin (k i) → EuclideanSpace ℝ (Fin d))
    (hbo : ∀ i, Orthonormal ℝ (b i))
    (hbs : ∀ i, Submodule.span ℝ (Set.range (b i)) = K i)
    (x y : EuclideanSpace ℝ (Fin d)) :
    deltaW (fun i p => (b i p).ofLp) (fun i => w i * ν i) * ‖x - y‖ ^ 2
      ≤ inner ℝ (gradient (fun z => ∑ i, w i * f i z) x
          - gradient (fun z => ∑ i, w i * f i z) y) (x - y) := by
  have hdiff : ∀ i, Differentiable ℝ (f i) := fun i => (hf i).differentiable one_ne_zero
  rw [gradient_weighted_sum f w hdiff x, gradient_weighted_sum f w hdiff y]
  exact uniform_composite_gap_of_restricted_monotone hn hd (fun i => gradient (f i)) w hw
    K ν hν hval b hbo hbs x y

end OCF

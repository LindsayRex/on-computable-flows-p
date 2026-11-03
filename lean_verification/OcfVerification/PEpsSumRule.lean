/-
P (card 22, Agent B) -- the epsilon-subdifferential sum rule, proved.

STATUS: FORMALISED (no sorry; standard axioms only, see the `#print axioms` at the foot).

WHAT IS PROVED. `OCF.P.epsSumRule_of_convex_continuous`: the hypothesis predicate
`OCF.H4.EpsSumRule D φ g` of H4BlockStitching.lean (the classical epsilon-subdifferential sum
rule, previously taken as a hypothesis) holds whenever
  * Y is a real Hilbert space (`InnerProductSpace ℝ Y`, `CompleteSpace Y`; finite dimension and
    `ProperSpace` are NOT needed, so the statement covers every `Vec d`),
  * φ : Y -> ℝ is convex on the whole space (`ConvexOn ℝ univ φ`) and continuous,
  * (D, g) is the pair encoding of an extended-valued function with `ExtModC D g 0`
    (D convex, g convex on D).
Not needed (and not assumed): D nonempty (z ∈ D comes from the epsilon-subgradient hypothesis),
lower semicontinuity of g (`LscExt`), differentiability of φ, ε ≥ 0 (follows from the hypothesis).
So the statement proved is the textbook one with the closedness (Gamma_0) hypothesis on g
dropped; this is a strengthening of the theorem (weaker hypotheses), not a weakening.

CLASSICAL SOURCE (the statement; the proof below is a direct separation argument, not a port):
Hiriart-Urruty and Lemarechal, Convex Analysis and Minimization Algorithms II (1993), Ch. XI,
Thm 3.1.1 (the volume is not on the shelf, so the locator is not page-checked and the manuscript
does not cite it; the proof below is self-contained from Mathlib's Hahn-Banach and needs no citation).

PROOF ROUTE (no conjugates). With F(x) = φ(x) - φ(z) - ⟨u, x - z⟩ + e and G(y) = g(y) - g(z),
the hypothesis u ∈ ∂_e(φ+g)(z) says F + G ≥ 0 on D. The strict epigraph S of F (open, as φ is
continuous; convex) and the hypograph T of -G over D (convex) are disjoint, so Mathlib's
`geometric_hahn_banach_open` gives f(x,t) = ℓ x + λ t and c with f < c on S, f ≥ c on T.
The case λ >= 0 is excluded (λ > 0: S is unbounded above in t; λ = 0: ℓ is bounded above hence
zero, and c > 0 contradicts (z, 0) ∈ T). Normalising by -λ and writing ℓ = ⟨p, ·⟩ gives
F(x) ≥ ⟨p, x⟩ - c' and G(y) ≥ c' - ⟨p, y⟩; with e₂ = ⟨p, z⟩ - c' ∈ [0, e], e₁ = e - e₂,
w = u + p, v = -p the two epsilon-subgradient inequalities follow by rearrangement.

DEFINITIONAL MAP.
  ∂_ε g(z) ∋ v           -- `OCF.H2.EpsSubgrad D g ε z v`
  C(g, 0), g convex on D -- `OCF.H3.ExtModC D g 0`
  sum rule               -- `OCF.H4.EpsSumRule D φ g`

COVERAGE. Formalised: the sum rule in the generality above. Hypothesis: none. Not formalised:
the conjugate-function route and the exactness of the infimal convolution (not needed).
-/
import Mathlib
import OcfVerification.H3MultiNonsmooth
import OcfVerification.H4BlockStitching

open Set

namespace OCF.P

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

lemma comb_sub (a b : ℝ) (hab : a + b = 1) (x y z : Y) :
    a • x + b • y - z = a • (x - z) + b • (y - z) := by
  have : z = (a + b) • z := by rw [hab, one_smul]
  conv_lhs => rw [this]
  rw [smul_sub, smul_sub, add_smul]; abel

theorem epsSumRule_of_convex_continuous [CompleteSpace Y] {D : Set Y} {φ g : Y → ℝ}
    (hφ : ConvexOn ℝ univ φ) (hφc : Continuous φ) (hg : OCF.H3.ExtModC D g 0) :
    OCF.H4.EpsSumRule D φ g := by
  intro e z u he hu
  obtain ⟨hzD, hu⟩ := hu
  -- the two sets
  set S : Set (Y × ℝ) := {p | φ p.1 - φ z - inner ℝ u (p.1 - z) + e < p.2} with hS
  set T : Set (Y × ℝ) := {p | p.1 ∈ D ∧ p.2 ≤ -(g p.1 - g z)} with hT
  have hgc : ConvexOn ℝ D g := by
    have := hg
    unfold OCF.H3.ExtModC at this
    simpa using this
  have hSc : Convex ℝ S := by
    intro p hp q hq a b ha hb hab
    simp only [hS, mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have h1 := hφ.2 (mem_univ p.1) (mem_univ q.1) ha hb hab
    rw [comb_sub a b hab, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    simp only [smul_eq_mul] at h1
    have e1 : e = a * e + b * e := by rw [← add_mul, hab, one_mul]
    have e2 : φ z = a * φ z + b * φ z := by rw [← add_mul, hab, one_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · simp at hab; subst hab; simpa using hq
    rcases hb.eq_or_lt with rfl | hb'
    · simp at hab; subst hab; simpa using hp
    nlinarith [mul_lt_mul_of_pos_left hp ha', mul_lt_mul_of_pos_left hq hb']
  have hSo : IsOpen S := by
    apply isOpen_lt
    · fun_prop
    · fun_prop
  have hTc : Convex ℝ T := by
    have : ConcaveOn ℝ D (fun x => -(g x - g z)) := by
      have := hgc.neg
      have h2 := this.add_const (g z)
      refine ⟨hgc.1, ?_⟩
      intro x hx y hy a b ha hb hab
      have := hgc.2 hx hy ha hb hab
      simp only [smul_eq_mul] at this ⊢
      nlinarith [hab, show a * g z + b * g z = g z by rw [← add_mul, hab, one_mul]]
    exact this.convex_hypograph
  have hdisj : Disjoint S T := by
    rw [Set.disjoint_left]
    intro p hp hpT
    simp only [hS, hT, mem_setOf_eq] at hp hpT
    have := hu p.1 hpT.1
    beta_reduce at this
    linarith [hpT.2]
  obtain ⟨f, c, hfS, hfT⟩ := geometric_hahn_banach_open hSc hSo hTc hdisj
  -- decompose the separating functional f(x,t) = ℓ x + t * lam
  set ℓ : StrongDual ℝ Y := f.comp (ContinuousLinearMap.inl ℝ Y ℝ) with hℓ
  set lam : ℝ := f (0, 1) with hlamdef
  have hf : ∀ x t, f (x, t) = ℓ x + t * lam := by
    intro x t
    have : (x, t) = (x, (0 : ℝ)) + t • ((0 : Y), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
    simp [hℓ]
    left; rfl
  have hA : ∀ x, ∀ t, φ x - φ z - inner ℝ u (x - z) + e < t → ℓ x + t * lam < c := by
    intro x t ht
    have := hfS (x, t) ht
    rwa [hf] at this
  have hB : ∀ y ∈ D, c ≤ ℓ y + (-(g y - g z)) * lam := by
    intro y hy
    have := hfT (y, -(g y - g z)) ⟨hy, le_rfl⟩
    rwa [hf] at this
  have hlam : lam < 0 := by
    by_contra hnn
    push Not at hnn
    rcases hnn.eq_or_lt with h0 | hpos
    · -- lam = 0 : ℓ is bounded above by c, hence zero, contradiction
      rw [← h0] at hA hB
      have hlt : ∀ x, ℓ x < c := fun x => by
        have := hA x (φ x - φ z - inner ℝ u (x - z) + e + 1) (by linarith)
        simpa using this
      have hl0 : ∀ x, ℓ x = 0 := by
        intro x
        by_contra hx
        have h1 := hlt (((|c| + 1) / ℓ x) • x)
        rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hx] at h1
        linarith [le_abs_self c]
      have := hB z hzD
      rw [hl0 z] at this
      have hc : 0 < c := by simpa [hl0 0] using hlt 0
      linarith
    · -- lam > 0 : unbounded above on S
      set t0 := max (φ z - φ z - inner ℝ u (z - z) + e) ((c - ℓ z) / lam) + 1 with ht0
      have h1 := hA z t0 (by
        have := le_max_left (φ z - φ z - inner ℝ u (z - z) + e) ((c - ℓ z) / lam)
        linarith)
      have h2 : (c - ℓ z) / lam < t0 := by
        have := le_max_right (φ z - φ z - inner ℝ u (z - z) + e) ((c - ℓ z) / lam)
        linarith
      rw [div_lt_iff₀ hpos] at h2
      linarith
  -- normalise
  have hm : 0 < -lam := neg_pos.2 hlam
  obtain ⟨q, hq⟩ : ∃ q : Y, ∀ x, inner ℝ q x = ℓ x :=
    ⟨(InnerProductSpace.toDual ℝ Y).symm ℓ, fun x => InnerProductSpace.toDual_symm_apply⟩
  set p : Y := (-lam)⁻¹ • q with hp
  set c' : ℝ := c / (-lam) with hc'
  have hpx : ∀ x, inner ℝ p x = ℓ x / (-lam) := by
    intro x
    rw [hp, real_inner_smul_left, hq]; ring
  have hF : ∀ x, inner ℝ p x - c' ≤ φ x - φ z - inner ℝ u (x - z) + e := by
    intro x
    by_contra hcon
    push Not at hcon
    rw [hpx] at hcon
    have hmul : ℓ x = (ℓ x / (-lam)) * (-lam) := (div_mul_cancel₀ _ hm.ne').symm
    have hcm : c = c' * (-lam) := by rw [hc']; exact (div_mul_cancel₀ _ hm.ne').symm
    generalize ℓ x / (-lam) = A at hcon hmul
    generalize hFdef : φ x - φ z - inner ℝ u (x - z) + e = F at hcon
    have h1 := hA x (F + (A - c' - F) / 2) (by rw [hFdef]; linarith)
    have hh : 0 < (A - c' - F) / 2 := by linarith
    have := mul_pos hm hh
    nlinarith
  have hG : ∀ y ∈ D, c' - inner ℝ p y ≤ g y - g z := by
    intro y hy
    have h := hB y hy
    rw [hpx, hc']
    have : c / (-lam) - ℓ y / (-lam) = (c - ℓ y) / (-lam) := by ring
    rw [this, div_le_iff₀ hm]
    nlinarith
  have hFz := hF z
  have hGz := hG z hzD
  simp only [sub_self, inner_zero_right, zero_add] at hFz hGz
  refine ⟨e - (inner ℝ p z - c'), inner ℝ p z - c', u + p, -p, by linarith, by linarith, by ring, ?_, ?_, ?_⟩
  · refine ⟨mem_univ _, fun x _ => ?_⟩
    have := hF x
    simp only [inner_add_left, inner_sub_right] at *
    linarith
  · refine ⟨hzD, fun y hy => ?_⟩
    have := hG y hy
    rw [inner_neg_left, inner_sub_right]
    linarith
  · abel

end OCF.P

#print axioms OCF.P.epsSumRule_of_convex_continuous

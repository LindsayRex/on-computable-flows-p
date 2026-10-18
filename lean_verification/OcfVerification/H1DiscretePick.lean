/-
H1 (A certified discrete pick composed with certified continuous solves) — the novel
assembly of the unit: Lemma H1.1 (pruning by a margin), Lemma H1.2 (smooth block bracket),
the algebraic part of Lemma H1.3 (prox block bracket, with its convex-analytic inputs as
hypotheses), Theorem H1.4 (certified pick and hybrid certificate), Corollary H1.5
(surrogate margin, 2ε̄ threshold and its sharpness), Proposition H1.6 (weak coupling over a
product, osc = max − min over the whole product, with its sharpness) and Corollary H1.7.

Source of truth: project_plan/done/proof_audits/H1_discrete_pick/01_derivation.md (stage-1 dossier,
2026-10-10; Lemma H1.1, Lemma H1.2, Lemma H1.3, Theorem H1.4, Corollary H1.5,
Proposition H1.6, Corollary H1.7, Remark H1.4.R2, §8 "Formalisation notes").
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised: 7113e63510f94367.

STRENGTHENINGS (none weakens a dossier statement): Theorem H1.4 is proved for every pick ẑ,
not only ẑ ∈ argmin U (Remark H1.4.R2 says the results hold for every ẑ); the "moreover"
bound of H1.4(d) is proved without 𝔪 > 0; Lemma H1.1(d) uses only v(ẑ) ≤ U_ẑ of HB.
Proposition H1.6 / Corollary H1.7 carry `[∀ a, Nonempty (Zs a)]`, which is implied by
|𝒵_a| ≥ 2 (needed only to elaborate osc), and `[Nonempty A]` (𝒜 nonempty, as stated).

DEFINITIONAL MAP (dossier symbol — Lean name):
* 𝒵 (finite, nonempty choices) — a `Fintype Z` with `DecidableEq Z` (and `Nonempty Z`
  where min_z is taken); |𝒵| ≥ 2 — hypothesis `hZ : 1 < Fintype.card Z`.
* min_{z∈𝒵} f(z) — `minOver f` (= `Finset.univ.inf' _ f`).
* min_{z≠ẑ} L_z — `rivalMin hZ L ẑ` (= `(univ.erase ẑ).inf' _ L`, nonempty since |𝒵| ≥ 2).
* 𝔪(ẑ) = min_{z≠ẑ} L_z − U_ẑ — `margin hZ L U ẑ`.
* ℝ^{d_z} — an arbitrary real inner product space `X z` per choice (ℝ^{d_z} with the
  Euclidean inner product is the dossier's case; Lemma H1.2's existence step uses
  `ProperSpace`, which ℝ^{d} = `EuclideanSpace ℝ (Fin d)` is).
* E_z — `E z : X z → ℝ` (real-valued: both block types of Theorem H1.4 have the bracket
  point in dom E_z, and the bracket structure below only evaluates E_z at real points;
  for prox blocks the extended-value E_z = f_z + g_z enters through hypotheses
  `StrongSubgrad`, see "NOT FORMALISED").
* v(z) = inf E_z — `blockVal E z` (= `⨅ x, E z x`); E_hyb — `hyb E` on the sigma type
  `Σ z, X z` (the disjoint union of the blocks); v* = inf E_hyb — `hybVal E`
  (= `⨅ p, hyb E p`); `hybVal_eq` proves v* = min_z v(z) (S0.1).
* C(E, σ) (E − (σ/2)‖·‖² convex) — G3's `ModC E σ`; ∇E — Mathlib `gradient E`.
* The quadratic minorant (Q) at (y, w): E(x') ≥ E(y) + ⟨w, x' − y⟩ + (σ/2)‖x' − y‖² for
  all x' — `StrongSubgrad E σ y w`.
* A block bracket (x̂_z, L_z) with distance radius ρ_z, i.e. the per-block conclusions of
  Lemmas H1.2/H1.3 that Theorem H1.4(a),(b) consumes: E_z has exactly one minimiser x*_z,
  L_z ≤ E_z(x*_z) = v(z), ‖x̂_z − x*_z‖ ≤ ρ_z — `BlockBracket (E z) (x̂ z) (L z) (ρ z)`;
  U_z = E_z(x̂_z) is `E z (xhat z)` throughout.
* Surrogate ṽ, ε̄, 𝔪_sur — `vt`, `ε`, `rivalMin hZ vt ẑ − vt ẑ`.
* Product 𝒵 = ∏_a 𝒵_a — the pi type `(a : A) → Zs a`; v_a — `va a`; χ — `χ`;
  𝔪_a — `groupMargin`; osc(χ) = max χ − min χ over the whole product — `osc χ`.

COVERAGE (target → Lean name):
* Lemma H1.1: H1.1.1 `rival_ge`; (a) `pruning_optimal`; (b) `pruning_unique`;
  (c) `pruning_gap` and `minOver_L_eq_of_margin`; (d) `pruning_of_lower`.
  Remark H1.4.R2 (𝔪(ẑ) > 0 ⇒ ẑ is the unique argmin of U): `margin_pos_unique_argminU`.
* Lemma H1.2: `lemma_H1_2` (unique minimiser, v = E(x*) = inf, (i), (ii)) and
  `lemma_H1_2_equality` (equality in (i) for (σ/2)‖· − c‖² + k₀). Ingredients:
  `complete_square` (CS), `strongSubgrad_of_modC` (Q from C(E, σ) for C¹ E),
  `exists_isMinOn_of_modC` (existence), `smooth_bracket` (the bracket for Theorem H1.4).
* Lemma H1.3 (hypothesis level): (i) norm bound `prox_u_norm`; (ii)+(iv) from (Q) at
  (p, u) and at (x*, 0) — `bracket_of_strongSubgrad`; (iii) `prox_bracket` (both brackets
  L♯ and L, and L ≤ L♯).
* Theorem H1.4: (a) `thm_H1_4_a`; (b) `thm_H1_4_b`; (c) `thm_H1_4_c`; (d) `thm_H1_4_d` and
  the "moreover" bound `thm_H1_4_d_bound` (proved for every margin, i.e. without the
  hypothesis 𝔪 > 0 — a strengthening); (e) `thm_H1_4_e` (𝔪 = 0 instance with a second
  optimal pick); S0.1 `hybVal_eq`. The all-smooth instance: `thm_H1_4_smooth`.
* Corollary H1.5: (a) `cor_H1_5_a`; (b) `cor_H1_5_b`; (c) `cor_H1_5_sharp_tie`,
  `cor_H1_5_sharp_wrong`.
* Proposition H1.6: (a) `prop_H1_6_a`; (b) `prop_H1_6_b`; core inequality
  `prop_H1_6_core`; (c) `prop_H1_6_sharp` (osc = D, both margins = 𝔪₀, and the three
  regimes D < 𝔪₀, D = 𝔪₀, D > 𝔪₀). Corollary H1.7: `cor_H1_7`.

NOT FORMALISED (hypotheses, per the formaliser brief and dossier §8): the convex-analytic
inputs of Lemma H1.3 — existence of prox_{αg}, g ∈ Γ₀, the inclusion u_z ∈ ∂E_z(p_z)
(H1.3.2–H1.3.4), the strongly convex minorant (Q) for a non-differentiable E_z (H1.2.2 in
subgradient form), existence of a minimiser of E_z (B&C Cor. 11.17) and Fermat's rule
(H1.3.6). They enter `prox_bracket` as the two hypotheses `StrongSubgrad E μ p u` and
`StrongSubgrad E μ xs 0`. Lemma H1.3(v) (sharpness family, needs prox) is not formalised.
Remark H1.8 and H1.d/H1.e are not targets.

Status tier: FORMALISED (statement + proof, no sorry) for Lemma H1.1, Lemma H1.2,
Theorem H1.4 (with block brackets as the interface; all-smooth instance fully proved),
Corollary H1.5, Proposition H1.6, Corollary H1.7; Lemma H1.3: algebraic content
FORMALISED, convex-analytic inputs taken as hypotheses (STATEMENT-level). Axioms: only
propext, Classical.choice, Quot.sound (see #print axioms at the end).
-/
import Mathlib
import OcfVerification.A1DescentLemma
import OcfVerification.G3SoundnessQuadratic

namespace OCF.H1

open Set Filter Topology Finset OCF.A1 OCF.G3

set_option linter.unusedSectionVars false

/-! ## Lemma H1.1 (pruning by a margin) -/

section Pruning

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

lemma erase_nonempty (hZ : 1 < Fintype.card Z) (zh : Z) : (univ.erase zh).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  omega

/-- min_{z ≠ ẑ} L_z (|𝒵| ≥ 2). -/
noncomputable def rivalMin (hZ : 1 < Fintype.card Z) (L : Z → ℝ) (zh : Z) : ℝ :=
  (univ.erase zh).inf' (erase_nonempty hZ zh) L

/-- The margin 𝔪(ẑ) := min_{z≠ẑ} L_z − U_ẑ. -/
noncomputable def margin (hZ : 1 < Fintype.card Z) (L U : Z → ℝ) (zh : Z) : ℝ :=
  rivalMin hZ L zh - U zh

/-- min_{z∈𝒵} f(z). -/
noncomputable def minOver [Nonempty Z] (f : Z → ℝ) : ℝ := univ.inf' univ_nonempty f

lemma rivalMin_le (hZ : 1 < Fintype.card Z) (L : Z → ℝ) {zh z : Z} (hz : z ≠ zh) :
    rivalMin hZ L zh ≤ L z :=
  Finset.inf'_le L (Finset.mem_erase.2 ⟨hz, Finset.mem_univ z⟩)

lemma minOver_le [Nonempty Z] (f : Z → ℝ) (z : Z) : minOver f ≤ f z :=
  Finset.inf'_le f (Finset.mem_univ z)

lemma le_minOver [Nonempty Z] {f : Z → ℝ} {c : ℝ} (h : ∀ z, c ≤ f z) : c ≤ minOver f :=
  Finset.le_inf' _ _ fun z _ => h z

lemma minOver_eq_of_forall_le [Nonempty Z] {f : Z → ℝ} {zh : Z} (h : ∀ z, f zh ≤ f z) :
    minOver f = f zh :=
  le_antisymm (minOver_le f zh) (le_minOver h)

lemma exists_minOver_eq [Nonempty Z] (f : Z → ℝ) : ∃ z, minOver f = f z := by
  obtain ⟨z, -, hz⟩ := Finset.exists_mem_eq_inf' (univ_nonempty (α := Z)) f
  exact ⟨z, hz⟩

/-- **Lemma H1.1(d)** (and the engine of (a), (b)): any ℓ ≤ v(z) for all z ≠ ẑ, with
v(ẑ) ≤ U_ẑ, gives optimality if ℓ − U_ẑ ≥ 0 and uniqueness with the gap ℓ − U_ẑ if
ℓ − U_ẑ > 0. (Only the upper half of HB at ẑ is used.) -/
theorem pruning_of_lower [Nonempty Z] {v U : Z → ℝ} {zh : Z} {ℓ : ℝ}
    (hℓ : ∀ z, z ≠ zh → ℓ ≤ v z) (hU : v zh ≤ U zh) :
    (0 ≤ ℓ - U zh → v zh = minOver v) ∧
    (0 < ℓ - U zh → v zh = minOver v ∧ (∀ z, z ≠ zh → v zh < v z) ∧
      ∀ z, z ≠ zh → v zh + (ℓ - U zh) ≤ v z) := by
  have key : ∀ z, z ≠ zh → v zh + (ℓ - U zh) ≤ v z := fun z hz => by
    have := hℓ z hz; linarith
  have opt : 0 ≤ ℓ - U zh → v zh = minOver v := fun h =>
    (minOver_eq_of_forall_le fun z => by
      by_cases hz : z = zh
      · rw [hz]
      · have := key z hz; linarith).symm
  refine ⟨opt, fun h => ⟨opt h.le, fun z hz => ?_, key⟩⟩
  have := key z hz; linarith

/-- H1.1.1: every rival's value is at least v(ẑ) + 𝔪. -/
theorem rival_ge (hZ : 1 < Fintype.card Z) {v U L : Z → ℝ} {zh : Z}
    (hHB : ∀ z, L z ≤ v z ∧ v z ≤ U z) :
    ∀ z, z ≠ zh → v zh + margin hZ L U zh ≤ v z := by
  intro z hz
  have h1 := rivalMin_le hZ L hz
  have h2 := hHB z
  have h3 := hHB zh
  unfold margin; linarith

/-- **Lemma H1.1(a).** 𝔪 ≥ 0 ⇒ v(ẑ) = min_z v(z). -/
theorem pruning_optimal [Nonempty Z] (hZ : 1 < Fintype.card Z) {v U L : Z → ℝ} {zh : Z}
    (hHB : ∀ z, L z ≤ v z ∧ v z ≤ U z) (hm : 0 ≤ margin hZ L U zh) :
    v zh = minOver v :=
  (pruning_of_lower (ℓ := rivalMin hZ L zh)
    (fun z hz => (rivalMin_le hZ L hz).trans (hHB z).1) (hHB zh).2).1 hm

/-- **Lemma H1.1(b).** 𝔪 > 0 ⇒ ẑ is the unique optimal pick, and v(z) ≥ v(ẑ) + 𝔪 for
z ≠ ẑ. -/
theorem pruning_unique [Nonempty Z] (hZ : 1 < Fintype.card Z) {v U L : Z → ℝ} {zh : Z}
    (hHB : ∀ z, L z ≤ v z ∧ v z ≤ U z) (hm : 0 < margin hZ L U zh) :
    v zh = minOver v ∧ (∀ z, z ≠ zh → minOver v < v z) ∧
      ∀ z, z ≠ zh → v zh + margin hZ L U zh ≤ v z := by
  obtain ⟨h1, h2, h3⟩ := (pruning_of_lower (ℓ := rivalMin hZ L zh)
    (fun z hz => (rivalMin_le hZ L hz).trans (hHB z).1) (hHB zh).2).2 hm
  exact ⟨h1, fun z hz => h1 ▸ h2 z hz, h3⟩

/-- **Lemma H1.1(c), first part** (no margin needed):
0 ≤ v(ẑ) − min v ≤ U_ẑ − min L. -/
theorem pruning_gap [Nonempty Z] {v U L : Z → ℝ} (zh : Z)
    (hHB : ∀ z, L z ≤ v z ∧ v z ≤ U z) :
    0 ≤ v zh - minOver v ∧ v zh - minOver v ≤ U zh - minOver L := by
  have h1 := minOver_le v zh
  have h2 : minOver L ≤ minOver v :=
    le_minOver fun z => (minOver_le L z).trans (hHB z).1
  have h3 := (hHB zh).2
  constructor <;> linarith

/-- **Lemma H1.1(c), second part.** 𝔪 ≥ 0 ⇒ min_z L_z = L_ẑ (so the bound is U_ẑ − L_ẑ). -/
theorem minOver_L_eq_of_margin [Nonempty Z] (hZ : 1 < Fintype.card Z) {v U L : Z → ℝ}
    {zh : Z} (hHB : ∀ z, L z ≤ v z ∧ v z ≤ U z) (hm : 0 ≤ margin hZ L U zh) :
    minOver L = L zh := by
  apply minOver_eq_of_forall_le
  intro z
  by_cases hz : z = zh
  · rw [hz]
  · have := rivalMin_le hZ L hz
    have := hHB zh
    unfold margin at hm
    linarith

/-- **Remark H1.4.R2.** 𝔪(ẑ) > 0 ⇒ U_ẑ < U_z for every z ≠ ẑ (so only argmin U can carry a
positive margin). -/
theorem margin_pos_unique_argminU (hZ : 1 < Fintype.card Z) {v U L : Z → ℝ} {zh : Z}
    (hHB : ∀ z, L z ≤ v z ∧ v z ≤ U z) (hm : 0 < margin hZ L U zh) :
    ∀ z, z ≠ zh → U zh < U z := by
  intro z hz
  have := rivalMin_le hZ L hz
  have := hHB z
  unfold margin at hm
  linarith

end Pruning

/-! ## Block brackets: Lemmas H1.2 and H1.3 -/

section Blocks

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The quadratic minorant (Q) of a σ-strongly convex function at the pair (y, w):
E(x') ≥ E(y) + ⟨w, x' − y⟩ + (σ/2)‖x' − y‖² for every x'. -/
def StrongSubgrad (E : X → ℝ) (σ : ℝ) (y w : X) : Prop :=
  ∀ x', E y + inner ℝ w (x' - y) + σ / 2 * ‖x' - y‖ ^ 2 ≤ E x'

/-- A block bracket with distance radius: E has exactly one minimiser x*, L ≤ E(x*) and
‖x̂ − x*‖ ≤ ρ. (U = E(x̂) ≥ E(x*) is automatic.) -/
def BlockBracket (E : X → ℝ) (xhat : X) (L ρ : ℝ) : Prop :=
  ∃ xs, (∀ y, IsMinOn E univ y ↔ y = xs) ∧ L ≤ E xs ∧ ‖xhat - xs‖ ≤ ρ

/-- (CS) H1.2.4: ⟨w, h⟩ + (s/2)‖h‖² ≥ −‖w‖²/(2s) for s > 0. -/
lemma complete_square (w h : X) {s : ℝ} (hs : 0 < s) :
    -(‖w‖ ^ 2 / (2 * s)) ≤ inner ℝ w h + s / 2 * ‖h‖ ^ 2 := by
  have hcs : -(‖w‖ * ‖h‖) ≤ inner ℝ w h := neg_le_of_abs_le (abs_real_inner_le_norm w h)
  have hsq : 0 ≤ (s * ‖h‖ - ‖w‖) ^ 2 / (2 * s) := by positivity
  have e : -(‖w‖ ^ 2 / (2 * s)) + (s * ‖h‖ - ‖w‖) ^ 2 / (2 * s)
      = -(‖w‖ * ‖h‖) + s / 2 * ‖h‖ ^ 2 := by
    field_simp; ring
  linarith

/-- The value of the infimum at a minimiser. -/
lemma iInf_eq_of_isMinOn {α : Type*} {E : α → ℝ} {xs : α} (h : IsMinOn E univ xs) : (⨅ x, E x) = E xs :=
  haveI : Nonempty α := ⟨xs⟩
  le_antisymm (ciInf_le ⟨E xs, by rintro _ ⟨y, rfl⟩; exact h (mem_univ y)⟩ xs)
    (le_ciInf fun y => h (mem_univ y))

/-- From (Q) at (p, u) and at (x*, 0) (σ > 0): x* is the unique minimiser,
E(p) − ‖u‖²/(2σ) ≤ E(x*), and ‖p − x*‖ ≤ ‖u‖/σ (Lemma H1.3(ii),(iv); Lemma H1.2(i),(ii)). -/
theorem bracket_of_strongSubgrad {E : X → ℝ} {σ : ℝ} (hσ : 0 < σ) {p u xs : X}
    (hp : StrongSubgrad E σ p u) (hxs : StrongSubgrad E σ xs 0) :
    BlockBracket E p (E p - ‖u‖ ^ 2 / (2 * σ)) (‖u‖ / σ) := by
  refine ⟨xs, fun y => ⟨fun hy => ?_, ?_⟩, ?_, ?_⟩
  · have h1 := hxs y
    have h2 : E y ≤ E xs := hy (mem_univ xs)
    simp only [inner_zero_left, add_zero] at h1
    have : ‖y - xs‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖y - xs‖ = 0 := by nlinarith [norm_nonneg (y - xs)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · intro hy
    rw [hy]
    intro z _
    have h1 := hxs z
    simp only [inner_zero_left, add_zero] at h1
    change E xs ≤ E z
    nlinarith [norm_nonneg (z - xs)]
  · have h1 := hp xs
    have h2 := complete_square u (xs - p) hσ
    linarith
  · have h1 := hp xs
    have h2 := hxs p
    simp only [inner_zero_left, add_zero] at h2
    rw [norm_sub_rev] at h1
    have e : inner ℝ u (xs - p) = -inner ℝ u (p - xs) := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at h1
    have h3 := real_inner_le_norm u (p - xs)
    rw [le_div_iff₀ hσ]
    rcases eq_or_lt_of_le (norm_nonneg (p - xs)) with h0 | hpos
    · rw [← h0]; simp
    · have : σ * ‖p - xs‖ * ‖p - xs‖ ≤ ‖u‖ * ‖p - xs‖ := by nlinarith
      have := le_of_mul_le_mul_right this hpos
      linarith

/-- Weakening a bracket: a smaller lower bound and a larger radius. -/
lemma BlockBracket.mono {E : X → ℝ} {xhat : X} {L L' ρ ρ' : ℝ} (h : BlockBracket E xhat L ρ)
    (hL : L' ≤ L) (hρ : ρ ≤ ρ') : BlockBracket E xhat L' ρ' := by
  obtain ⟨xs, h1, h2, h3⟩ := h
  exact ⟨xs, h1, hL.trans h2, h3.trans hρ⟩

/-- **Lemma H1.3(i), norm part** (H1.3.5): for any x, p and r := (x − p)/α with α > 0,
u := r − ∇f(x) + ∇f(p) satisfies ‖u‖ ≤ (1 + αβ)‖r‖ when ∇f is β-Lipschitz. -/
theorem prox_u_norm [CompleteSpace X] {f : X → ℝ} {α β : ℝ} (hα : 0 < α) (hL : LipGrad f β)
    (x p : X) :
    ‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ ≤ (1 + α * β) * ‖α⁻¹ • (x - p)‖ := by
  have hpx : ‖p - x‖ = α * ‖α⁻¹ • (x - p)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hα), ← mul_assoc,
      mul_inv_cancel₀ hα.ne', one_mul, norm_sub_rev]
  have e : α⁻¹ • (x - p) - gradient f x + gradient f p
      = α⁻¹ • (x - p) + (gradient f p - gradient f x) := by abel
  rw [e]
  calc ‖α⁻¹ • (x - p) + (gradient f p - gradient f x)‖
        ≤ ‖α⁻¹ • (x - p)‖ + ‖gradient f p - gradient f x‖ := norm_add_le _ _
    _ ≤ ‖α⁻¹ • (x - p)‖ + β * ‖p - x‖ := by linarith [hL p x]
    _ = (1 + α * β) * ‖α⁻¹ • (x - p)‖ := by rw [hpx]; ring

/-- **Lemma H1.3 (hypothesis level).** f with β-Lipschitz gradient, α > 0, μ > 0,
any x and p, r := (x − p)/α (= R_α(x) when p = T_α x), u := r − ∇f(x) + ∇f(p). Assume the
convex-analytic inputs (Q) at (p, u) (i.e. u ∈ ∂E(p), H1.3.2–H1.3.4 with H1.2.2) and (Q)
at (x*, 0) (existence of x* and Fermat's rule, H1.3.1, H1.3.6). Then:
(i) ‖u‖ ≤ (1 + αβ)‖r‖; (ii)+(iv) the bracket (p, L♯ = E(p) − ‖u‖²/(2μ)) with radius
‖u‖/μ; (iii) L := E(p) − (1 + αβ)²‖r‖²/(2μ) ≤ L♯, and the bracket (p, L) with radius
(1 + αβ)‖r‖/μ. -/
theorem prox_bracket [CompleteSpace X] {f E : X → ℝ} {α β μ : ℝ} (hα : 0 < α) (hμ : 0 < μ)
    (hL : LipGrad f β) (x p xs : X)
    (hQp : StrongSubgrad E μ p (α⁻¹ • (x - p) - gradient f x + gradient f p))
    (hQs : StrongSubgrad E μ xs 0) :
    ‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ ≤ (1 + α * β) * ‖α⁻¹ • (x - p)‖ ∧
    BlockBracket E p (E p - ‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ ^ 2 / (2 * μ))
      (‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ / μ) ∧
    E p - (1 + α * β) ^ 2 * ‖α⁻¹ • (x - p)‖ ^ 2 / (2 * μ)
      ≤ E p - ‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ ^ 2 / (2 * μ) ∧
    BlockBracket E p (E p - (1 + α * β) ^ 2 * ‖α⁻¹ • (x - p)‖ ^ 2 / (2 * μ))
      ((1 + α * β) * ‖α⁻¹ • (x - p)‖ / μ) := by
  have hn := prox_u_norm hα hL x p
  have hbr := bracket_of_strongSubgrad hμ hQp hQs
  have hsq : ‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ ^ 2
      ≤ (1 + α * β) ^ 2 * ‖α⁻¹ • (x - p)‖ ^ 2 := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hle : E p - (1 + α * β) ^ 2 * ‖α⁻¹ • (x - p)‖ ^ 2 / (2 * μ)
      ≤ E p - ‖α⁻¹ • (x - p) - gradient f x + gradient f p‖ ^ 2 / (2 * μ) := by
    have := div_le_div_of_nonneg_right hsq (by positivity : (0 : ℝ) ≤ 2 * μ)
    linarith
  exact ⟨hn, hbr, hle, hbr.mono hle (div_le_div_of_nonneg_right hn hμ.le)⟩

/-- (Q) from C(E, σ) for differentiable E (H1.2.2 + H1.2.3, smooth case). -/
theorem strongSubgrad_of_modC [CompleteSpace X] {E : X → ℝ} {σ : ℝ}
    (hE : Differentiable ℝ E) (hC : ModC E σ) (x : X) : StrongSubgrad E σ x (gradient E x) := by
  intro y
  have h := firstOrder_of_convexOn (differentiable_sub_sq hE σ) hC x y
  rw [gradient_sub_sq hE σ x] at h
  have e1 : ‖y - x‖ ^ 2 = ‖y‖ ^ 2 - 2 * inner ℝ x y + ‖x‖ ^ 2 := by
    rw [norm_sub_sq_real, real_inner_comm]
  rw [inner_sub_left, real_inner_smul_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq] at h
  rw [e1, inner_sub_right]
  nlinarith

/-- Existence of a minimiser of a C¹ function with C(E, σ), σ > 0, on a proper space
(B&C Cor. 11.17 in finite dimension), and ∇E = 0 there (Fermat). -/
theorem exists_isMinOn_of_modC [ProperSpace X] {E : X → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hE : Differentiable ℝ E) (hC : ModC E σ) :
    ∃ xs, IsMinOn E univ xs ∧ gradient E xs = 0 := by
  have hQ := strongSubgrad_of_modC hE hC 0
  set g := gradient E 0
  obtain ⟨xs, hxs⟩ : ∃ xs, ∀ y, E xs ≤ E y := by
    refine hE.continuous.exists_forall_le' 0 ?_
    have hc := (ProperSpace.isCompact_closedBall (0 : X) (2 * ‖g‖ / σ)).compl_mem_cocompact
    filter_upwards [hc] with y hy
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hy
    have h1 := hQ y
    simp only [sub_zero] at h1
    have h2 : -(‖g‖ * ‖y‖) ≤ inner ℝ g y := neg_le_of_abs_le (abs_real_inner_le_norm g y)
    rw [div_lt_iff₀ hσ] at hy
    nlinarith [norm_nonneg y, norm_nonneg g]
  have hmin : IsMinOn E univ xs := fun y _ => hxs y
  refine ⟨xs, hmin, ?_⟩
  have := (hmin.isLocalMin Filter.univ_mem).fderiv_eq_zero
  simp [gradient, this]

/-- **Lemma H1.2.** E C¹ on a proper real inner product space (e.g. ℝ^d), C(E, σ), σ > 0.
Then E has exactly one minimiser x*, v := inf E = E(x*), and for every x:
(i) E(x) − ‖∇E(x)‖²/(2σ) ≤ v ≤ E(x); (ii) ‖x − x*‖ ≤ ‖∇E(x)‖/σ. -/
theorem lemma_H1_2 [ProperSpace X] {E : X → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hE : Differentiable ℝ E) (hC : ModC E σ) :
    ∃ xs, (∀ y, IsMinOn E univ y ↔ y = xs) ∧ (⨅ x, E x) = E xs ∧
      ∀ x, (E x - ‖gradient E x‖ ^ 2 / (2 * σ) ≤ ⨅ y, E y) ∧ (⨅ y, E y) ≤ E x ∧
        ‖x - xs‖ ≤ ‖gradient E x‖ / σ := by
  obtain ⟨xs, hmin, hg⟩ := exists_isMinOn_of_modC hσ hE hC
  have hQs : StrongSubgrad E σ xs 0 := hg ▸ strongSubgrad_of_modC hE hC xs
  have hinf := iInf_eq_of_isMinOn hmin
  obtain ⟨xs', huniq, -, -⟩ := bracket_of_strongSubgrad hσ (strongSubgrad_of_modC hE hC xs) hQs
  have hxs' : xs = xs' := (huniq xs).1 hmin
  subst hxs'
  refine ⟨xs, huniq, hinf, fun x => ?_⟩
  obtain ⟨xs'', huniq'', hL, hd⟩ :=
    bracket_of_strongSubgrad hσ (strongSubgrad_of_modC hE hC x) hQs
  have : xs = xs'' := (huniq'' xs).1 hmin
  subst this
  rw [hinf]
  exact ⟨hL, hmin (mem_univ x), hd⟩

/-- The block bracket of Lemma H1.2 at any point x (the smooth-block input of Theorem
H1.4): (x, E(x) − ‖∇E(x)‖²/(2σ)) with radius ‖∇E(x)‖/σ. -/
theorem smooth_bracket [ProperSpace X] {E : X → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hE : Differentiable ℝ E) (hC : ModC E σ) (x : X) :
    BlockBracket E x (E x - ‖gradient E x‖ ^ 2 / (2 * σ)) (‖gradient E x‖ / σ) := by
  obtain ⟨xs, hmin, hg⟩ := exists_isMinOn_of_modC hσ hE hC
  exact bracket_of_strongSubgrad hσ (strongSubgrad_of_modC hE hC x)
    (hg ▸ strongSubgrad_of_modC hE hC xs)

/-- ∇((σ/2)‖· − c‖² + k₀)(x) = σ(x − c). -/
lemma hasGradientAt_quadc [CompleteSpace X] (σ k : ℝ) (c x : X) :
    HasGradientAt (fun x => σ / 2 * ‖x - c‖ ^ 2 + k) (σ • (x - c)) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h := (((hasFDerivAt_id x).sub_const c).norm_sq.const_mul (σ / 2)).add_const k
  refine h.congr_fderiv ?_
  ext y
  simp
  ring

/-- **Lemma H1.2, equality clause** (H1.2.7): for E = (σ/2)‖· − c‖² + k₀, σ > 0, the lower
bound of (i) is attained at every x: E(x) − ‖∇E(x)‖²/(2σ) = inf E (= k₀). -/
theorem lemma_H1_2_equality [CompleteSpace X] {σ : ℝ} (hσ : 0 < σ) (c : X) (k : ℝ) (x : X) :
    (σ / 2 * ‖x - c‖ ^ 2 + k) - ‖gradient (fun y => σ / 2 * ‖y - c‖ ^ 2 + k) x‖ ^ 2 / (2 * σ)
      = ⨅ y, (σ / 2 * ‖y - c‖ ^ 2 + k) ∧ (⨅ y, (σ / 2 * ‖y - c‖ ^ 2 + k)) = k := by
  have hmin : IsMinOn (fun y => σ / 2 * ‖y - c‖ ^ 2 + k) univ c := by
    intro y _
    change σ / 2 * ‖c - c‖ ^ 2 + k ≤ σ / 2 * ‖y - c‖ ^ 2 + k
    simp only [sub_self, norm_zero]
    nlinarith [sq_nonneg ‖y - c‖]
  have hinf : (⨅ y, (σ / 2 * ‖y - c‖ ^ 2 + k)) = k := by
    rw [iInf_eq_of_isMinOn hmin]; simp
  refine ⟨?_, hinf⟩
  rw [hinf, (hasGradientAt_quadc σ k c x).gradient, norm_smul, Real.norm_eq_abs,
    abs_of_pos hσ]
  field_simp
  ring

end Blocks

/-! ## Theorem H1.4 (certified pick and hybrid certificate) -/

section Hybrid

variable {Z : Type*} [Fintype Z] [DecidableEq Z] {X : Z → Type*}
  [∀ z, NormedAddCommGroup (X z)] [∀ z, InnerProductSpace ℝ (X z)]

/-- Block value v(z) = inf E_z. -/
noncomputable def blockVal (E : ∀ z, X z → ℝ) (z : Z) : ℝ := ⨅ x, E z x

/-- The hybrid energy E_hyb(z, x) = E_z(x) on the disjoint union Σ z, X z. -/
def hyb (E : ∀ z, X z → ℝ) (p : Σ z, X z) : ℝ := E p.1 p.2

/-- v* = inf E_hyb. -/
noncomputable def hybVal (E : ∀ z, X z → ℝ) : ℝ := ⨅ p, hyb E p

lemma blockVal_eq {E : ∀ z, X z → ℝ} {z : Z} {xs : X z} (h : IsMinOn (E z) univ xs) :
    blockVal E z = E z xs := iInf_eq_of_isMinOn h

lemma blockVal_le {E : ∀ z, X z → ℝ} {z : Z} {xs : X z} (h : IsMinOn (E z) univ xs)
    (x : X z) : blockVal E z ≤ E z x := by
  rw [blockVal_eq h]; exact h (mem_univ x)

/-- S0.1: v* = min_z v(z) when every block attains its infimum. -/
theorem hybVal_eq [Nonempty Z] {E : ∀ z, X z → ℝ} (hex : ∀ z, ∃ xs, IsMinOn (E z) univ xs) :
    hybVal E = minOver (blockVal E) ∧
      ∀ z₀ (xs : X z₀), IsMinOn (E z₀) univ xs → blockVal E z₀ = minOver (blockVal E) →
        IsMinOn (hyb E) univ ⟨z₀, xs⟩ := by
  have hall : ∀ p : Σ z, X z, minOver (blockVal E) ≤ hyb E p := by
    rintro ⟨z, x⟩
    obtain ⟨xs, hxs⟩ := hex z
    exact (minOver_le _ z).trans (blockVal_le hxs x)
  have hmin : ∀ z₀ (xs : X z₀), IsMinOn (E z₀) univ xs →
      blockVal E z₀ = minOver (blockVal E) → IsMinOn (hyb E) univ ⟨z₀, xs⟩ := by
    intro z₀ xs hxs hz₀ q _
    change E z₀ xs ≤ hyb E q
    rw [← blockVal_eq hxs, hz₀]; exact hall q
  refine ⟨?_, hmin⟩
  obtain ⟨z₀, hz₀⟩ := exists_minOver_eq (blockVal E)
  obtain ⟨xs, hxs⟩ := hex z₀
  have := iInf_eq_of_isMinOn (hmin z₀ xs hxs hz₀.symm)
  unfold hybVal
  rw [this]
  change E z₀ xs = _
  rw [← blockVal_eq hxs, hz₀]

variable (E : ∀ z, X z → ℝ) (xhat : ∀ z, X z) (L ρ : Z → ℝ)

/-- U_z = E_z(x̂_z). -/
def Uof (z : Z) : ℝ := E z (xhat z)

/-- **Theorem H1.4(a).** Each v(z) is finite and attained at a unique x*_z, and
L_z ≤ v(z) ≤ U_z. -/
theorem thm_H1_4_a (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) (z : Z) :
    (∃ xs, (∀ y, IsMinOn (E z) univ y ↔ y = xs) ∧ blockVal E z = E z xs) ∧
      L z ≤ blockVal E z ∧ blockVal E z ≤ Uof E xhat z := by
  obtain ⟨xs, hu, hL, -⟩ := hB z
  have hm : IsMinOn (E z) univ xs := (hu xs).2 rfl
  exact ⟨⟨xs, hu, blockVal_eq hm⟩, (blockVal_eq hm) ▸ hL, blockVal_le hm _⟩

lemma hB_HB (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) :
    ∀ z, L z ≤ blockVal E z ∧ blockVal E z ≤ Uof E xhat z :=
  fun z => (thm_H1_4_a E xhat L ρ hB z).2

lemma hB_ex (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) :
    ∀ z, ∃ xs, IsMinOn (E z) univ xs := fun z => by
  obtain ⟨xs, hu, -, -⟩ := hB z; exact ⟨xs, (hu xs).2 rfl⟩

lemma hB_dist (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) (z : Z) (xs : X z)
    (hxs : IsMinOn (E z) univ xs) : ‖xhat z - xs‖ ≤ ρ z := by
  obtain ⟨xs', hu, -, hd⟩ := hB z
  rwa [(hu xs).1 hxs]

/-- **Theorem H1.4(b)** (always issued): E_hyb(ẑ, x̂_ẑ) − v* ≤ U_ẑ − min_z L_z, and
‖x̂_ẑ − x*_ẑ‖ ≤ ρ_ẑ. -/
theorem thm_H1_4_b [Nonempty Z] (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) (zh : Z) :
    hyb E ⟨zh, xhat zh⟩ - hybVal E ≤ Uof E xhat zh - minOver L ∧
      ∀ xs, IsMinOn (E zh) univ xs → ‖xhat zh - xs‖ ≤ ρ zh := by
  refine ⟨?_, hB_dist E xhat L ρ hB zh⟩
  rw [(hybVal_eq (hB_ex E xhat L ρ hB)).1]
  have h2 : minOver L ≤ minOver (blockVal E) :=
    le_minOver fun z => (minOver_le L z).trans (hB_HB E xhat L ρ hB z).1
  change Uof E xhat zh - _ ≤ _
  linarith

/-- The hypothesis "|𝒵| = 1 or 𝔪 ≥ 0" of Theorem H1.4(c) (𝔪 only defined for |𝒵| ≥ 2). -/
def MarginNonneg (U : Z → ℝ) (zh : Z) : Prop :=
  Fintype.card Z = 1 ∨ ∃ hZ : 1 < Fintype.card Z, 0 ≤ margin hZ L U zh

/-- The hypothesis "|𝒵| = 1 or 𝔪 > 0" of Theorem H1.4(d). -/
def MarginPos (U : Z → ℝ) (zh : Z) : Prop :=
  Fintype.card Z = 1 ∨ ∃ hZ : 1 < Fintype.card Z, 0 < margin hZ L U zh

lemma eq_of_card_one (h : Fintype.card Z = 1) (z zh : Z) : z = zh :=
  Fintype.card_le_one_iff.1 h.le z zh

/-- **Theorem H1.4(c).** If |𝒵| = 1 or 𝔪 ≥ 0: ẑ is an optimal pick (v(ẑ) = v*), (ẑ, x*_ẑ) is
a minimiser of the hybrid problem, and E_hyb(ẑ, x̂_ẑ) − v* ≤ U_ẑ − L_ẑ. -/
theorem thm_H1_4_c [Nonempty Z] (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) (zh : Z)
    (hm : MarginNonneg L (Uof E xhat) zh) :
    blockVal E zh = hybVal E ∧
      (∀ xs, IsMinOn (E zh) univ xs → IsMinOn (hyb E) univ ⟨zh, xs⟩) ∧
      hyb E ⟨zh, xhat zh⟩ - hybVal E ≤ Uof E xhat zh - L zh := by
  have HB := hB_HB E xhat L ρ hB
  have hopt : blockVal E zh = minOver (blockVal E) := by
    rcases hm with h1 | ⟨hZ, hm⟩
    · exact (minOver_eq_of_forall_le fun z => by rw [eq_of_card_one h1 z zh]).symm
    · exact pruning_optimal hZ HB hm
  have hv := hybVal_eq (hB_ex E xhat L ρ hB)
  refine ⟨hopt.trans hv.1.symm, fun xs hxs => hv.2 zh xs hxs hopt, ?_⟩
  rw [hv.1, ← hopt]
  change Uof E xhat zh - _ ≤ _
  linarith [(HB zh).1]

/-- **Theorem H1.4(d).** If |𝒵| = 1 or 𝔪 > 0: ẑ is the unique optimal pick (v(z) > v* for
z ≠ ẑ), argmin E_hyb = {(ẑ, x*_ẑ)}, and ‖x̂_ẑ − x*_ẑ‖ ≤ ρ_ẑ. -/
theorem thm_H1_4_d [Nonempty Z] (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z)) (zh : Z)
    (hm : MarginPos L (Uof E xhat) zh) :
    blockVal E zh = hybVal E ∧ (∀ z, z ≠ zh → hybVal E < blockVal E z) ∧
      ∀ xs, IsMinOn (E zh) univ xs →
        {p | IsMinOn (hyb E) univ p} = {⟨zh, xs⟩} ∧ ‖xhat zh - xs‖ ≤ ρ zh := by
  have HB := hB_HB E xhat L ρ hB
  have hv := hybVal_eq (hB_ex E xhat L ρ hB)
  have hc := thm_H1_4_c E xhat L ρ hB zh (by
    rcases hm with h1 | ⟨hZ, hm⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hZ, hm.le⟩)
  have hstrict : ∀ z, z ≠ zh → hybVal E < blockVal E z := by
    intro z hz
    rcases hm with h1 | ⟨hZ, hm⟩
    · exact absurd (eq_of_card_one h1 z zh) hz
    · rw [hv.1]; exact (pruning_unique hZ HB hm).2.1 z hz
  refine ⟨hc.1, hstrict, fun xs hxs => ⟨?_, hB_dist E xhat L ρ hB zh xs hxs⟩⟩
  ext ⟨z, x⟩
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro hp
    have hle : E z x ≤ E zh xs := hp (mem_univ ⟨zh, xs⟩)
    have hval : E zh xs = hybVal E := (blockVal_eq hxs).symm.trans hc.1
    by_cases hz : z = zh
    · subst hz
      obtain ⟨xs', hu, -, -⟩ := hB z
      have h1 : x = xs' := (hu x).1 (fun y _ => hle.trans (hxs (mem_univ y)))
      have h2 : xs = xs' := (hu xs).1 hxs
      rw [h1, h2]
    · obtain ⟨xz, hxz⟩ := hB_ex E xhat L ρ hB z
      have := blockVal_le hxz x
      have := hstrict z hz
      linarith
  · intro hp
    rw [hp]
    exact hc.2.1 xs hxs

/-- **Theorem H1.4(d), "moreover".** Every (z, x) with z ≠ ẑ has E_hyb(z, x) ≥ v* + 𝔪.
(Proved for every value of 𝔪; the dossier states it under 𝔪 > 0.) -/
theorem thm_H1_4_d_bound [Nonempty Z] (hB : ∀ z, BlockBracket (E z) (xhat z) (L z) (ρ z))
    (hZ : 1 < Fintype.card Z) (zh : Z) :
    ∀ z, z ≠ zh → ∀ x : X z, hybVal E + margin hZ L (Uof E xhat) zh ≤ hyb E ⟨z, x⟩ := by
  intro z hz x
  have HB := hB_HB E xhat L ρ hB
  have hv := hybVal_eq (hB_ex E xhat L ρ hB)
  have h1 := rival_ge hZ HB z hz
  have h2 := minOver_le (blockVal E) zh
  obtain ⟨xz, hxz⟩ := hB_ex E xhat L ρ hB z
  have h3 := blockVal_le hxz x
  change _ ≤ E z x
  rw [hv.1]
  linarith

/-- **Theorem H1.4, all-smooth instance.** Every block C¹ on a proper space with C(E_z, σ_z),
σ_z > 0, x̂_z arbitrary, L_z := E_z(x̂_z) − ‖∇E_z(x̂_z)‖²/(2σ_z), ρ_z := ‖∇E_z(x̂_z)‖/σ_z:
the bracket hypothesis of (a)–(d) holds (Lemma H1.2), so (a)–(d) apply verbatim. -/
theorem thm_H1_4_smooth [∀ z, ProperSpace (X z)] {σ : Z → ℝ} (hσ : ∀ z, 0 < σ z)
    (hE : ∀ z, Differentiable ℝ (E z)) (hC : ∀ z, ModC (E z) (σ z)) :
    ∀ z, BlockBracket (E z) (xhat z)
      (E z (xhat z) - ‖gradient (E z) (xhat z)‖ ^ 2 / (2 * σ z))
      (‖gradient (E z) (xhat z)‖ / σ z) :=
  fun z => smooth_bracket (hσ z) (hE z) (hC z) (xhat z)

end Hybrid

/-- **Theorem H1.4(e).** 𝔪 = 0 does not give (d): two copies of E = ½x² on ℝ with points 0
(U = L = 0, valid smooth brackets with σ = 1) have 𝔪 = 0, both picks optimal, and the hybrid
argmin contains (1, 0) as well as (0, 0). -/
theorem thm_H1_4_e :
    let E : Fin 2 → ℝ → ℝ := fun _ x => 1 / 2 * x ^ 2
    (∀ z, BlockBracket (E z) 0 (E z 0 - ‖gradient (E z) 0‖ ^ 2 / (2 * 1))
      (‖gradient (E z) 0‖ / 1)) ∧
    (∀ z, E z 0 - ‖gradient (E z) 0‖ ^ 2 / (2 * 1) = 0 ∧ E z 0 = 0) ∧
    margin (by simp : 1 < Fintype.card (Fin 2)) (fun _ => (0 : ℝ)) (fun _ => (0 : ℝ)) 0 = 0 ∧
    IsMinOn (hyb (X := fun _ => ℝ) E) univ ⟨0, 0⟩ ∧
    IsMinOn (hyb (X := fun _ => ℝ) E) univ ⟨1, 0⟩ := by
  intro E
  have hg : ∀ z, gradient (E z) 0 = 0 := by
    intro z
    have := (hasGradientAt_quadc (X := ℝ) 1 0 0 0)
    have e : (fun x : ℝ => 1 / 2 * ‖x - 0‖ ^ 2 + 0) = E z := by
      funext x; simp [E, sq_abs]
    rw [e] at this
    rw [this.gradient]; simp
  have hmin : ∀ z (q : Σ _ : Fin 2, ℝ), hyb (X := fun _ => ℝ) E ⟨z, 0⟩ ≤ hyb E q := by
    intro z q
    change 1 / 2 * (0 : ℝ) ^ 2 ≤ 1 / 2 * q.2 ^ 2
    nlinarith [sq_nonneg q.2]
  refine ⟨fun z => smooth_bracket one_pos ?_ ?_ 0, fun z => ?_, ?_,
    fun q _ => hmin 0 q, fun q _ => hmin 1 q⟩
  · exact (hasGradientAt_quadc (X := ℝ) 1 0 0 · |>.differentiableAt) |> fun h => by
      intro x
      have e : (fun x : ℝ => 1 / 2 * ‖x - 0‖ ^ 2 + 0) = E z := by
        funext x; simp [E, sq_abs]
      rw [← e]; exact h x
  · unfold ModC
    have : (fun x : ℝ => E z x - 1 / 2 * ‖x‖ ^ 2) = fun _ => 0 := by
      funext x; simp [E, sq_abs]
    rw [this]; exact convexOn_const 0 convex_univ
  · rw [hg z]; simp [E]
  · simp [margin, rivalMin]

/-! ## Corollary H1.5 (surrogate margin) -/

section Surrogate

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- **Corollary H1.5(a).** |ṽ − v| ≤ ε̄ pointwise, 𝔪_sur := min_{z≠ẑ} ṽ(z) − ṽ(ẑ) > 2ε̄ ⇒ ẑ is
the unique minimiser of v, and v(z) ≥ v(ẑ) + 𝔪_sur − 2ε̄ for z ≠ ẑ. -/
theorem cor_H1_5_a (hZ : 1 < Fintype.card Z) {v vt : Z → ℝ} {ε : ℝ}
    (hsur : ∀ z, |vt z - v z| ≤ ε) (zh : Z) (h : 2 * ε < rivalMin hZ vt zh - vt zh) :
    (∀ z, z ≠ zh → v zh < v z) ∧
      ∀ z, z ≠ zh → v zh + (rivalMin hZ vt zh - vt zh - 2 * ε) ≤ v z := by
  haveI : Nonempty Z := ⟨zh⟩
  have hl : ∀ z, z ≠ zh → rivalMin hZ vt zh - ε ≤ v z := fun z hz => by
    have := rivalMin_le hZ vt hz
    have := (abs_le.1 (hsur z)).2
    linarith
  have hU : v zh ≤ vt zh + ε := by have := (abs_le.1 (hsur zh)).1; linarith
  obtain ⟨-, h2, h3⟩ := (pruning_of_lower (U := fun z => vt z + ε) hl hU).2 (by linarith)
  refine ⟨h2, fun z hz => ?_⟩
  have := h3 z hz
  linarith

/-- **Corollary H1.5(b).** 𝔪_sur ≥ 2ε̄ ⇒ ẑ minimises v. -/
theorem cor_H1_5_b (hZ : 1 < Fintype.card Z) {v vt : Z → ℝ} {ε : ℝ}
    (hsur : ∀ z, |vt z - v z| ≤ ε) (zh : Z) (h : 2 * ε ≤ rivalMin hZ vt zh - vt zh) :
    ∀ z, v zh ≤ v z := by
  haveI : Nonempty Z := ⟨zh⟩
  have hl : ∀ z, z ≠ zh → rivalMin hZ vt zh - ε ≤ v z := fun z hz => by
    have := rivalMin_le hZ vt hz
    have := (abs_le.1 (hsur z)).2
    linarith
  have hU : v zh ≤ vt zh + ε := by have := (abs_le.1 (hsur zh)).1; linarith
  have hopt := (pruning_of_lower (U := fun z => vt z + ε) hl hU).1 (by linarith)
  intro z
  rw [hopt]; exact minOver_le v z

end Surrogate

lemma card_fin_two : 1 < Fintype.card (Fin 2) := by simp

lemma rivalMin_fin2 (f : Fin 2 → ℝ) : rivalMin card_fin_two f 0 = f 1 := by
  apply le_antisymm (rivalMin_le card_fin_two f (by decide))
  apply Finset.le_inf'
  intro b hb
  have : b ≠ 0 := (Finset.mem_erase.1 hb).1
  have : b = 1 := by omega
  rw [this]

/-- **Corollary H1.5(c), tie.** 𝒵 = {0, 1}, ṽ = (0, 2ε̄), v = (ε̄, ε̄): (H-sur) holds,
𝔪_sur(0) = 2ε̄, and the minimiser of v is not unique (v(1) ≤ v(0)). -/
theorem cor_H1_5_sharp_tie {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ z, |(![0, 2 * ε] : Fin 2 → ℝ) z - (![ε, ε] : Fin 2 → ℝ) z| ≤ ε) ∧
    rivalMin card_fin_two (![0, 2 * ε] : Fin 2 → ℝ) 0 - (![0, 2 * ε] : Fin 2 → ℝ) 0 = 2 * ε ∧
    (![ε, ε] : Fin 2 → ℝ) 1 ≤ (![ε, ε] : Fin 2 → ℝ) 0 := by
  refine ⟨fun z => ?_, by rw [rivalMin_fin2]; simp, by simp⟩
  fin_cases z
  · simp [abs_of_nonneg hε]
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show 2 * ε - ε = ε by ring, abs_of_nonneg hε]

/-- **Corollary H1.5(c), wrong pick.** For t ∈ (0, 2ε̄]: v = (ε̄, ε̄ − t), ṽ = (0, 2ε̄ − t):
(H-sur) holds, 𝔪_sur(0) = 2ε̄ − t < 2ε̄, and the pick 0 is wrong (v(1) < v(0)). -/
theorem cor_H1_5_sharp_wrong {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 < t) (_ht2 : t ≤ 2 * ε) :
    (∀ z, |(![0, 2 * ε - t] : Fin 2 → ℝ) z - (![ε, ε - t] : Fin 2 → ℝ) z| ≤ ε) ∧
    rivalMin card_fin_two (![0, 2 * ε - t] : Fin 2 → ℝ) 0 - (![0, 2 * ε - t] : Fin 2 → ℝ) 0
      = 2 * ε - t ∧
    2 * ε - t < 2 * ε ∧
    (![ε, ε - t] : Fin 2 → ℝ) 1 < (![ε, ε - t] : Fin 2 → ℝ) 0 := by
  refine ⟨fun z => ?_, by rw [rivalMin_fin2]; simp, by linarith, by simp; linarith⟩
  fin_cases z
  · simp [abs_of_nonneg hε]
  · simp only [Fin.isValue, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    rw [show 2 * ε - t - (ε - t) = ε by ring, abs_of_nonneg hε]

/-! ## Proposition H1.6 (weak coupling over a product) and Corollary H1.7 -/

section Coupling

variable {A : Type*} [Fintype A] [DecidableEq A] {Zs : A → Type*} [∀ a, Fintype (Zs a)]
  [∀ a, DecidableEq (Zs a)]

/-- max_{z} χ(z) over a finite nonempty type. -/
noncomputable def maxOver {W : Type*} [Fintype W] [Nonempty W] (f : W → ℝ) : ℝ :=
  univ.sup' univ_nonempty f

/-- osc(χ) = max χ − min χ over the whole (finite) product. -/
noncomputable def osc {W : Type*} [Fintype W] [Nonempty W] (χ : W → ℝ) : ℝ :=
  maxOver χ - minOver χ

/-- v(z) = Σ_a v_a(z_a) + χ(z)  (H-sep). -/
def sepVal (va : ∀ a, Zs a → ℝ) (χ : ((a : A) → Zs a) → ℝ) (z : (a : A) → Zs a) : ℝ :=
  ∑ a, va a (z a) + χ z

/-- The per-group margin 𝔪_a = min_{y≠ẑ_a} v_a(y) − v_a(ẑ_a). -/
noncomputable def groupMargin (hZa : ∀ a, 1 < Fintype.card (Zs a)) (va : ∀ a, Zs a → ℝ)
    (zh : (a : A) → Zs a) (a : A) : ℝ :=
  rivalMin (hZa a) (va a) (zh a) - va a (zh a)

/-- The core inequality (H1.6.1–H1.6.4 with certified per-group margins 𝔪̲_a ≥ 0):
v(z) ≥ v(ẑ) + min_a 𝔪̲_a − osc(χ) for every z ≠ ẑ. -/
theorem coupling_core [Nonempty A] [∀ a, Nonempty (Zs a)] (va : ∀ a, Zs a → ℝ)
    (χ : ((a : A) → Zs a) → ℝ) (zh : (a : A) → Zs a) (ml : A → ℝ) (hml0 : ∀ a, 0 ≤ ml a)
    (hml : ∀ a y, y ≠ zh a → ml a ≤ va a y - va a (zh a)) :
    ∀ z, z ≠ zh → sepVal va χ zh + (minOver ml - osc χ) ≤ sepVal va χ z := by
  intro z hz
  obtain ⟨a₀, ha₀⟩ := Function.ne_iff.1 hz
  have hterm : ∀ a, 0 ≤ va a (z a) - va a (zh a) := fun a => by
    by_cases h : z a = zh a
    · rw [h, sub_self]
    · exact (hml0 a).trans (hml a (z a) h)
  have hsum : va a₀ (z a₀) - va a₀ (zh a₀) ≤ ∑ a, (va a (z a) - va a (zh a)) :=
    Finset.single_le_sum (fun a _ => hterm a) (Finset.mem_univ a₀)
  have h1 := hml a₀ (z a₀) ha₀
  have h2 := minOver_le ml a₀
  have h3 := minOver_le χ z
  have h4 : χ zh ≤ maxOver χ := Finset.le_sup' χ (Finset.mem_univ zh)
  rw [Finset.sum_sub_distrib] at hsum
  unfold sepVal osc
  linarith

lemma groupMargin_nonneg (hZa : ∀ a, 1 < Fintype.card (Zs a)) {va : ∀ a, Zs a → ℝ}
    {zh : (a : A) → Zs a} (hargmin : ∀ a y, va a (zh a) ≤ va a y) (a : A) :
    0 ≤ groupMargin hZa va zh a := by
  unfold groupMargin rivalMin
  have : va a (zh a) ≤ (univ.erase (zh a)).inf' (erase_nonempty (hZa a) (zh a)) (va a) :=
    Finset.le_inf' _ _ fun y _ => hargmin a y
  linarith

/-- H1.6.1–H1.6.4: v(z) ≥ v(ẑ) + min_a 𝔪_a − osc(χ) for every z ≠ ẑ. -/
theorem prop_H1_6_core [Nonempty A] [∀ a, Nonempty (Zs a)]
    (hZa : ∀ a, 1 < Fintype.card (Zs a)) (va : ∀ a, Zs a → ℝ) (χ : ((a : A) → Zs a) → ℝ)
    (zh : (a : A) → Zs a) (hargmin : ∀ a y, va a (zh a) ≤ va a y) :
    ∀ z, z ≠ zh →
      sepVal va χ zh + (minOver (groupMargin hZa va zh) - osc χ) ≤ sepVal va χ z :=
  coupling_core va χ zh _ (groupMargin_nonneg hZa hargmin) fun a y hy => by
    have := rivalMin_le (hZa a) (va a) hy
    unfold groupMargin; linarith

/-- **Proposition H1.6(a).** min_a 𝔪_a > osc(χ) ⇒ ẑ is the unique minimiser of v, and
v(z) ≥ v(ẑ) + min_a 𝔪_a − osc(χ) for z ≠ ẑ. -/
theorem prop_H1_6_a [Nonempty A] [∀ a, Nonempty (Zs a)]
    (hZa : ∀ a, 1 < Fintype.card (Zs a)) (va : ∀ a, Zs a → ℝ) (χ : ((a : A) → Zs a) → ℝ)
    (zh : (a : A) → Zs a) (hargmin : ∀ a y, va a (zh a) ≤ va a y)
    (h : osc χ < minOver (groupMargin hZa va zh)) :
    (∀ z, z ≠ zh → sepVal va χ zh < sepVal va χ z) ∧
      ∀ z, z ≠ zh →
        sepVal va χ zh + (minOver (groupMargin hZa va zh) - osc χ) ≤ sepVal va χ z := by
  have hc := prop_H1_6_core hZa va χ zh hargmin
  exact ⟨fun z hz => by have := hc z hz; linarith, hc⟩

/-- **Proposition H1.6(b).** min_a 𝔪_a ≥ osc(χ) ⇒ ẑ minimises v. -/
theorem prop_H1_6_b [Nonempty A] [∀ a, Nonempty (Zs a)]
    (hZa : ∀ a, 1 < Fintype.card (Zs a)) (va : ∀ a, Zs a → ℝ) (χ : ((a : A) → Zs a) → ℝ)
    (zh : (a : A) → Zs a) (hargmin : ∀ a y, va a (zh a) ≤ va a y)
    (h : osc χ ≤ minOver (groupMargin hZa va zh)) :
    ∀ z, sepVal va χ zh ≤ sepVal va χ z := by
  intro z
  by_cases hz : z = zh
  · rw [hz]
  · have := prop_H1_6_core hZa va χ zh hargmin z hz; linarith

/-- **Corollary H1.7.** Certified per-group margins 𝔪̲_a ≥ 0 (v_a(y) − v_a(ẑ_a) ≥ 𝔪̲_a for
y ≠ ẑ_a) and Ω ≥ osc(χ) with min_a 𝔪̲_a > Ω ⇒ ẑ is the unique minimiser of v. -/
theorem cor_H1_7 [Nonempty A] [∀ a, Nonempty (Zs a)] (va : ∀ a, Zs a → ℝ)
    (χ : ((a : A) → Zs a) → ℝ) (zh : (a : A) → Zs a) (ml : A → ℝ) (hml0 : ∀ a, 0 ≤ ml a)
    (hml : ∀ a y, y ≠ zh a → ml a ≤ va a y - va a (zh a)) {Ω : ℝ} (hΩ : osc χ ≤ Ω)
    (h : Ω < minOver ml) :
    ∀ z, z ≠ zh → sepVal va χ zh < sepVal va χ z := by
  intro z hz
  have := coupling_core va χ zh ml hml0 hml z hz
  linarith

end Coupling

/-- The sharpness instance of Proposition H1.6(c): 𝒵 = {0,1}², v_1 = v_2 = (0, 𝔪₀),
χ = −D at (1, 0) and 0 elsewhere. -/
def shVa (m₀ : ℝ) : Fin 2 → Fin 2 → ℝ := fun _ => ![0, m₀]

def shChi (D : ℝ) (z : Fin 2 → Fin 2) : ℝ := if z = ![1, 0] then -D else 0

lemma card_fin_two' : ∀ _ : Fin 2, 1 < Fintype.card (Fin 2) := fun _ => card_fin_two

/-- **Proposition H1.6(c) (sharpness).** With 𝔪₀ ≥ 0 and D ≥ 0: ẑ = (0, 0) is the per-group
argmin, both per-group margins equal 𝔪₀, osc(χ) = D, and v(0,0) = 0, v(0,1) = 𝔪₀,
v(1,0) = 𝔪₀ − D, v(1,1) = 2𝔪₀. Hence D < 𝔪₀: ẑ is the unique minimiser; D = 𝔪₀: (1, 0)
is a second minimiser; D > 𝔪₀: the joint pick ẑ is not optimal. -/
theorem prop_H1_6_sharp {m₀ D : ℝ} (hm : 0 ≤ m₀) (hD : 0 ≤ D) :
    (∀ a y, shVa m₀ a ((fun _ => 0 : Fin 2 → Fin 2) a) ≤ shVa m₀ a y) ∧
    (∀ a, groupMargin card_fin_two' (shVa m₀) (fun _ => 0) a = m₀) ∧
    minOver (groupMargin card_fin_two' (shVa m₀) (fun _ => 0)) = m₀ ∧
    osc (shChi D) = D ∧
    sepVal (shVa m₀) (shChi D) ![0, 0] = 0 ∧ sepVal (shVa m₀) (shChi D) ![0, 1] = m₀ ∧
    sepVal (shVa m₀) (shChi D) ![1, 0] = m₀ - D ∧ sepVal (shVa m₀) (shChi D) ![1, 1] = 2 * m₀ ∧
    (D < m₀ → ∀ z, z ≠ (fun _ => 0) →
      sepVal (shVa m₀) (shChi D) (fun _ => 0) < sepVal (shVa m₀) (shChi D) z) ∧
    (D = m₀ → ∀ z, sepVal (shVa m₀) (shChi D) ![1, 0] ≤ sepVal (shVa m₀) (shChi D) z) ∧
    (m₀ < D → sepVal (shVa m₀) (shChi D) ![1, 0] < sepVal (shVa m₀) (shChi D) (fun _ => 0)) := by
  have hargmin : ∀ a y, shVa m₀ a ((fun _ => 0 : Fin 2 → Fin 2) a) ≤ shVa m₀ a y := by
    intro a y; fin_cases y <;> simp [shVa, hm]
  have hgm : ∀ a, groupMargin card_fin_two' (shVa m₀) (fun _ => 0) a = m₀ := by
    intro a; unfold groupMargin
    rw [show card_fin_two' a = card_fin_two from rfl, rivalMin_fin2]; simp [shVa]
  have hmin : minOver (groupMargin card_fin_two' (shVa m₀) (fun _ => 0)) = m₀ := by
    rw [minOver_eq_of_forall_le (zh := 0) (fun z => by rw [hgm, hgm]), hgm]
  have h10 : (![1, 0] : Fin 2 → Fin 2) ≠ ![0, 0] := by decide
  have hmax : maxOver (shChi D) = 0 := by
    apply le_antisymm
    · apply Finset.sup'_le; intro z _; unfold shChi; split_ifs <;> linarith
    · have := Finset.le_sup' (shChi D) (Finset.mem_univ ![0, 0])
      simp only [shChi, if_neg h10.symm] at this
      exact this
  have hmn : minOver (shChi D) = -D := by
    have e : shChi D ![1, 0] = -D := by simp [shChi]
    rw [minOver_eq_of_forall_le (zh := ![1, 0]), e]
    intro z; rw [e]; unfold shChi; split_ifs <;> linarith
  have hosc : osc (shChi D) = D := by unfold osc; rw [hmax, hmn]; ring
  have hv : ∀ z : Fin 2 → Fin 2, sepVal (shVa m₀) (shChi D) z
      = ![0, m₀] (z 0) + ![0, m₀] (z 1) + shChi D z := by
    intro z; simp [sepVal, shVa, Fin.sum_univ_two]
  have v00 : sepVal (shVa m₀) (shChi D) ![0, 0] = 0 := by
    rw [hv]; simp [shChi]
  have v01 : sepVal (shVa m₀) (shChi D) ![0, 1] = m₀ := by
    rw [hv]; simp [shChi, show (![0, 1] : Fin 2 → Fin 2) ≠ ![1, 0] by decide]
  have v10 : sepVal (shVa m₀) (shChi D) ![1, 0] = m₀ - D := by
    rw [hv]; simp [shChi]; ring
  have v11 : sepVal (shVa m₀) (shChi D) ![1, 1] = 2 * m₀ := by
    rw [hv]; simp [shChi, show (![1, 1] : Fin 2 → Fin 2) ≠ ![1, 0] by decide]; ring
  have hall : ∀ z : Fin 2 → Fin 2, z = ![0, 0] ∨ z = ![0, 1] ∨ z = ![1, 0] ∨ z = ![1, 1] := by
    decide
  have h0 : (fun _ => 0 : Fin 2 → Fin 2) = ![0, 0] := by decide
  refine ⟨hargmin, hgm, hmin, hosc, v00, v01, v10, v11, fun hlt => ?_, fun heq z => ?_,
    fun hgt => ?_⟩
  · exact (prop_H1_6_a card_fin_two' (shVa m₀) (shChi D) (fun _ => 0) hargmin
      (by rw [hosc, hmin]; exact hlt)).1
  · rcases hall z with rfl | rfl | rfl | rfl <;> simp only [v00, v01, v10, v11] <;>
      [linarith; linarith; linarith; linarith]
  · rw [h0, v00, v10]; linarith

end OCF.H1

#print axioms OCF.H1.pruning_of_lower
#print axioms OCF.H1.rival_ge
#print axioms OCF.H1.pruning_optimal
#print axioms OCF.H1.pruning_unique
#print axioms OCF.H1.pruning_gap
#print axioms OCF.H1.minOver_L_eq_of_margin
#print axioms OCF.H1.margin_pos_unique_argminU
#print axioms OCF.H1.complete_square
#print axioms OCF.H1.bracket_of_strongSubgrad
#print axioms OCF.H1.prox_u_norm
#print axioms OCF.H1.prox_bracket
#print axioms OCF.H1.strongSubgrad_of_modC
#print axioms OCF.H1.exists_isMinOn_of_modC
#print axioms OCF.H1.lemma_H1_2
#print axioms OCF.H1.lemma_H1_2_equality
#print axioms OCF.H1.smooth_bracket
#print axioms OCF.H1.hybVal_eq
#print axioms OCF.H1.thm_H1_4_a
#print axioms OCF.H1.thm_H1_4_b
#print axioms OCF.H1.thm_H1_4_c
#print axioms OCF.H1.thm_H1_4_d
#print axioms OCF.H1.thm_H1_4_d_bound
#print axioms OCF.H1.thm_H1_4_smooth
#print axioms OCF.H1.thm_H1_4_e
#print axioms OCF.H1.cor_H1_5_a
#print axioms OCF.H1.cor_H1_5_b
#print axioms OCF.H1.cor_H1_5_sharp_tie
#print axioms OCF.H1.cor_H1_5_sharp_wrong
#print axioms OCF.H1.coupling_core
#print axioms OCF.H1.prop_H1_6_core
#print axioms OCF.H1.prop_H1_6_a
#print axioms OCF.H1.prop_H1_6_b
#print axioms OCF.H1.cor_H1_7
#print axioms OCF.H1.prop_H1_6_sharp

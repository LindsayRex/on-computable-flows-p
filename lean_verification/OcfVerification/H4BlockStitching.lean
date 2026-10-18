/-
H4 (Block stitching of coupled blocks solved by different solvers) — the novel results of
the unit: Definition H4.0 (block report, stitched run), Lemma H4.1(a)–(c) (declared constants
σ, τ_l, L_{jl} and the derived Λ, ρ, c_θ, ρ_θ), Lemma H4.2 (one block step, with its equality
cases), Lemma H4.3(a)–(d) (reports from other accuracy senses), Lemma H4.4 (separable
assembly), Lemma H4.5 (value and distance from an ε-subgradient, with equality instances),
Lemma H4.6 (one sweep), Theorem H4.7 (exact rate ρ, the θ-recursion, accumulation (c1)–(c3),
distance and declared-bound monotonicity), Corollary H4.8 (a priori form, K_θ and K'_θ),
Proposition H4.9 (certificate of any stitched output: report form, zero-trust form, run
form) and Proposition H4.10(a),(b),(d) in full, (c) as a limit.

Source of truth: project_plan/done/proof_audits/H4_block_stitching/01_derivation.md (stage-1 dossier,
2026-10-10; §§0–11), landing draft 04_landing_draft.tex (h4-lem:constants, h4-def:report,
h4-lem:block, h4-lem:reports, h4-lem:assembly, h4-thm:stitch, h4-cor:gaps, h4-prop:cert,
h4-prop:needed).
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised: ccb45c24781fa002.

MODELLING CHOICES (none weakens a dossier statement):
* SD1: blocks indexed by `Fin m` (Gauss–Seidel order = the order of `Fin m`; the dossier's
  1-based block l is the Lean block l − 1); block spaces `X l` — arbitrary complete real inner
  product spaces (ℝ^{d_l} is the dossier's case); ℝ^d = `PiLp 2 X` (‖x‖² = Σ‖x_l‖²);
  U_l — `U l` (a continuous linear map, ‖U_l h‖ = ‖h‖); x + U_l(y − x_l) — `upd x l y`;
  d_l ≥ 1 — `[Nontrivial (X l)]` / `[Nontrivial (PiLp 2 X)]`, only where used.
* SD2: F ∈ C¹ — `Differentiable ℝ F`; ∇_l F(x) — `gradient F x l` (`gradient_slice` proves
  ∇φ_{x,l}(y) = ∇_l F(x + U_l(y − x_l)), the chain rule of (K)).
* SD3: g_l ∈ Γ₀ — the pair (D l, g l) of H2 (g_l on D l, +∞ off it), convex:
  `ModCD (D l) (g l) 0` (lower semicontinuity is never used); g_l = 0 is (univ, 0).
  dom g — `domG D`; g — `gsum g`; E = F + g — `Efun F g`; ∂_ε — H2's `EpsSubgrad`.
* SD4 C(F, σ) — G3's `ModC F σ`; SD5 — `SliceMod F τ`; SD6 — `CrossConst F L`; SD2–SD6
  bundled — `SD F D g σ τ L`. Λ² = Σ_{j<l}L_{jl}²/τ_l — `Lam2` (= Σ_j c_j², `cj2`),
  Λ — `Lam`; ρ, c_θ, ρ_θ — `rho`, `cth`, `rhoth`.
* Definition H4.0: block report — `Report D g l z v ε`; stitched run — `Run D g` (iterates
  x k i = x^{k,i}, i ≤ m, step l of sweep k produces x k (l + 1), x (k + 1) 0 = x k m);
  h_{k,l}, η_{k,l}, γ_{k,l}, Γ_k, ε_k, ‖η_k‖, D_k, Q_k, B_k(θ), a_k, v_k, u_k — `Run.hm`,
  `Run.eta`, `Run.gam`, `Run.Gam`, `Run.epsk`, `Run.etan`, `Run.Dk`, `Run.Qk`, `Run.Bk`,
  `Run.ak`, `Run.vk`, `Run.uk`; B as a function of (η, ε) — `Bfun`. Def. H4.0(d) — `Run.mem`;
  Def. H4.0(e) (existence suffices) is how Corollary H4.8(a) is proved (reports chosen).
* Φ_{x,l} — `PhiB F g x l`; value gap e of z — `∀ w ∈ D l, Φ z ≤ Φ w + e`.
* x* a minimiser of E — `IsMinE F D g xs` (existence (E-min) is classical, a hypothesis).
* ℝ² with two scalar blocks — `E2` (= PiLp 2 (fun _ : Fin 2 => ℝ)); one exact cyclic sweep
  — `ExactSweep2 E x x'`; ∂E(x) — `subdiff E x`; dist(0, ∂E) — `Metric.infDist 0 (subdiff ..)`.

STRENGTHENINGS: Lemma H4.2 needs only x_l ∈ dom g_l (not x ∈ dom g) and no minimiser for
(b),(c) (the proof of (c) goes through (b), not through y*); Lemma H4.1(a) holds for m ≥ 1;
Lemma H4.3(a)–(c) need no minimiser of Φ; Lemma H4.5(i) needs no convexity of g.

COVERAGE (dossier target → Lean name):
* Lemma H4.1: (a) `decl_sigma`; (b) `decl_tau` (τ_l = s_l + σ_C^{(l)}), `slice_modC`
  (σ_C^{(l)} := σ_C), `decl_tau_sigma` (τ_l := σ); (c) `decl_cross`, `decl_cross_default`
  (L^C_{jl} := β_C); constants: `Lam_sq`, `Lam2_nonneg`, `rho_mem`, `rhoth_mem`,
  `one_sub_rhoth`, `rhoth_tendsto` (Remark H4.7(i)).
* Lemma H4.2: block form `key_K` (K), `block_gap` (a), `block_descent` (b), `block_move` (c),
  `block_min` (a: unique minimiser, Φ(z) − Φ(y*) ≤ γ), `block_equality` (d); block setting
  `lemma_H4_2` ((a) in the E-form, (b), (c)), `lemma_H4_2_min`.
* Lemma H4.3: (a) `report_smooth`; (b) `report_polish`, `report_polish_L` (M = L_l);
  (c) `report_H2`; (d) `report_valuegap` (with `epsSubgrad_smooth`, `tau_le_L`).
* Lemma H4.4: (a) `Run.H4_4_a` (via `Run.sep_assembly`); (b) `Run.H4_4_b`; (c) `Run.H4_4_c`.
* Lemma H4.5: (i) `value_bracket`; (ii) `dist_bracket`; (E-grow) `growth`, `dist_of_growth`;
  (iii) `bracket_value_sharp`, `bracket_dist_sharp`.
* Lemma H4.6: `Run.H4_6` ((i) and (ii)).
* Theorem H4.7: (a) `Run.H4_7_a`, `Run.H4_7_a_iter`, `Run.H4_7_a_zero`; (b) `Run.H4_7_b`;
  (c) `Run.H4_7_c`, (c1) `Run.H4_7_c1`, (c2) `Run.H4_7_c2`, (c3) `Run.H4_7_c3`,
  `Run.H4_7_c3_limsup`; (d) `Run.H4_7_d_dist`, `Bfun_mono`, `Run.H4_7_d_declared`
  (scalar cores: `accum`, `accum_const`, `accum_geom`, `accum_tendsto`, `accum_limsup`).
* Corollary H4.8: (a) `H4_8_a` (K_θ — `Kth`, `Bfun_valuegap`); (b) `H4_8_b` (K'_θ — `Kth'`,
  `Bfun_polish`); geometric schedule `H4_8_geom`.
* Proposition H4.9: (a) `H4_9_a` (equality instances `bracket_value_sharp`,
  `bracket_dist_sharp`); (b) `H4_9_b` (separable prox `sep_prox`; distance, value bracket,
  inexact form); (c) `H4_9_c`.
* Proposition H4.10: (a) `H4_10_a_basic` (C(E_σ, σ), x* = 0, E* = 0, unique block minimisers),
  `H4_10_a_stall` (block maps, the sweep (x₁, 3t) ↦ x̄_t, fixed point, E − E* = 10t + 25σt²/2),
  `H4_10_a_dist` (dist(0, ∂E_σ(x̄_t)) = 2 + 5σt); (b) `H4_10_b_energy` (convex, smooth,
  x* = 0, L₁₂ = L₂₁ = 1 valid, no σ > 0), `Equart_blocks`, `cubic_root`, `qseq`/`qseq_spec`
  (the sequence exists), `H4_10_b_run` (x^k = (s_k, s_k), a_k = s_k⁴/4, s_k ↓ 0, ratio
  (1 + s_{k+1}²)^{−4} → 1, no linear rate); (c) `H4_10_c_decl` (C(E^μ, σ), τ₂ = σ, E^μ* = 0,
  ρ = 144/(144 + μ²σ²) → 1), `H4_10_c` (a_K^μ/a_0^μ → 1 as μ → 0⁺ for every K),
  `H4_10_c_exists` (such runs exist); (d) `H4_10_d` (ρ = 0 claimed, a₁ = c²(1 − c²)/2 > 0),
  `H4_10_d_cross` (L = |c| valid, L₁₂ = 0 invalid).

CLASSICAL INPUTS TAKEN AS HYPOTHESES (as in H1–H3): existence of a minimiser x* of E
((E-min), B&C Cor. 11.17) — `IsMinE`; existence of a block minimiser y* in Lemma H4.2(a)
(minimiser form only); the prox characterisation (P) (B&C Prop. 16.44) for the polishing
step (H4.3(b), H4.8(b)) and the block prox maps of H4.9(b) — `ProxEps … 0` hypotheses; the
ε-subdifferential sum rule (Hiriart-Urruty–Lemaréchal vol. II, Ch. XI, Thm 3.1.1) in
H4.3(d) and H4.8(a) — `EpsSumRule`. Fermat's rule, (Q), (CS), (E-grow), uniqueness of
minimisers, the separable prox assembly, the subgradient computations of H4.10 and the
existence of minimisers on ℝ needed in H4.10(a) are PROVED here.

NOT FORMALISED: Lemma H4.1(d) (least constants of a quadratic coupling: λ_min, operator norms
of blocks — classical, landed prop:spec-moduli) and (e) (the same number through the landed
calculus rules lem:rule-sum, lem:rule-affine, lem:flat-minorant); in H4.10(a) the remark that
no cross constant exists for the non-smooth coupling, and in H4.10(c) the validity of the
cross constant L₁₂ = 12/μ for the Huber energy (needs the derivative of the Huber function;
the convexity C(E^μ, σ), τ₂ = σ and the limit are formalised); Remark H4.11.

Status tier: FORMALISED (statement + proof, no sorry) for every Lean name listed under
COVERAGE. Axioms: only propext, Classical.choice, Quot.sound (see #print axioms at the end).
-/
import Mathlib
import OcfVerification.A1DescentLemma
import OcfVerification.G3SoundnessQuadratic
import OcfVerification.H1DiscretePick
import OcfVerification.H2InexactOracles

namespace OCF.H4

open Set Filter Topology Finset OCF.A1 OCF.G3 OCF.H1 OCF.H2

set_option linter.unusedSectionVars false

/-! ## Scalar helpers -/

/-- Cauchy–Schwarz for finite sums: Σ a b ≤ √(Σ a²) √(Σ b²). -/
lemma sum_mul_le_sqrt {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    ∑ i ∈ s, a i * b i ≤ √(∑ i ∈ s, a i ^ 2) * √(∑ i ∈ s, b i ^ 2) := by
  rw [← Real.sqrt_mul (sum_nonneg fun i _ => sq_nonneg _)]
  apply Real.le_sqrt_of_sq_le
  exact sum_mul_sq_le_sq_mul_sq s a b

/-- Minkowski for finite sums: √(Σ (a + b)²) ≤ √(Σ a²) + √(Σ b²). -/
lemma sqrt_sum_add_sq_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) :
    √(∑ i ∈ s, (a i + b i) ^ 2) ≤ √(∑ i ∈ s, a i ^ 2) + √(∑ i ∈ s, b i ^ 2) := by
  have hA := sum_nonneg (s := s) fun i _ => sq_nonneg (a i)
  have hB := sum_nonneg (s := s) fun i _ => sq_nonneg (b i)
  rw [Real.sqrt_le_left (by positivity)]
  have hcs := sum_mul_le_sqrt s a b
  have e : ∑ i ∈ s, (a i + b i) ^ 2
      = ∑ i ∈ s, a i ^ 2 + 2 * ∑ i ∈ s, a i * b i + ∑ i ∈ s, b i ^ 2 := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e, add_sq, Real.sq_sqrt hA, Real.sq_sqrt hB]
  linarith

/-- Monotonicity of √(Σ a²) for 0 ≤ a ≤ b. -/
lemma sqrt_sum_sq_mono {ι : Type*} (s : Finset ι) {a b : ι → ℝ} (h0 : ∀ i ∈ s, 0 ≤ a i)
    (h : ∀ i ∈ s, a i ≤ b i) : √(∑ i ∈ s, a i ^ 2) ≤ √(∑ i ∈ s, b i ^ 2) :=
  Real.sqrt_le_sqrt (sum_le_sum fun i hi => pow_le_pow_left₀ (h0 i hi) (h i hi) 2)

/-! ## Block structure (SD1–SD3) -/

section Blocks

variable {m : ℕ} {X : Fin m → Type*} [∀ l, NormedAddCommGroup (X l)]
  [∀ l, InnerProductSpace ℝ (X l)] [∀ l, CompleteSpace (X l)]

/-- The embedding U_l : ℝ^{d_l} → ℝ^d of block l (zero elsewhere). -/
noncomputable def U (l : Fin m) : X l →L[ℝ] PiLp 2 X :=
  (PiLp.continuousLinearEquiv 2 ℝ X).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.single ℝ X l)

lemma U_apply (l : Fin m) (y : X l) : U l y = PiLp.single 2 l y := rfl

lemma U_same (l : Fin m) (y : X l) : (U l y) l = y := by
  rw [U_apply, PiLp.single_eq_same]

lemma U_ne {l j : Fin m} (h : j ≠ l) (y : X l) : (U l y) j = 0 := by
  rw [U_apply, PiLp.single_eq_of_ne 2 h]

lemma norm_U (l : Fin m) (y : X l) : ‖U l y‖ = ‖y‖ := by
  rw [U_apply, PiLp.norm_single]

lemma inner_U (w : PiLp 2 X) (l : Fin m) (k : X l) :
    inner ℝ w (U l k) = inner ℝ (w l) k := by
  rw [PiLp.inner_apply, sum_eq_single l]
  · rw [U_same]
  · intro j _ hj; rw [U_ne hj, inner_zero_right]
  · intro h; exact absurd (Finset.mem_univ l) h

/-- The block update x + U_l(y − x_l). -/
noncomputable def upd (x : PiLp 2 X) (l : Fin m) (y : X l) : PiLp 2 X := x + U l (y - x l)

lemma upd_same (x : PiLp 2 X) (l : Fin m) (y : X l) : (upd x l y) l = y := by
  simp [upd, U_same]

lemma upd_ne (x : PiLp 2 X) {l j : Fin m} (h : j ≠ l) (y : X l) : (upd x l y) j = x j := by
  simp [upd, U_ne h]

lemma upd_self (x : PiLp 2 X) (l : Fin m) : upd x l (x l) = x := by
  simp [upd]

lemma upd_sub (x : PiLp 2 X) (l : Fin m) (y : X l) : upd x l y - x = U l (y - x l) := by
  simp [upd]

lemma norm_upd_sub (x : PiLp 2 X) (l : Fin m) (y : X l) : ‖upd x l y - x‖ = ‖y - x l‖ := by
  rw [upd_sub, norm_U]

/-- The slice φ_{x,l}(y) := F(x + U_l(y − x_l)). -/
noncomputable def slice (F : PiLp 2 X → ℝ) (x : PiLp 2 X) (l : Fin m) : X l → ℝ := fun y => F (upd x l y)

/-- dom g = dom g₁ × ⋯ × dom g_m. -/
def domG (D : ∀ l, Set (X l)) : Set (PiLp 2 X) := {x | ∀ l, x l ∈ D l}

/-- g(x) := Σ_l g_l(x_l). -/
def gsum (g : ∀ l, X l → ℝ) (x : PiLp 2 X) : ℝ := ∑ l, g l (x l)

/-- E := F + g (on dom g). -/
noncomputable def Efun (F : PiLp 2 X → ℝ) (g : ∀ l, X l → ℝ) (x : PiLp 2 X) : ℝ := F x + gsum g x

lemma upd_mem {D : ∀ l, Set (X l)} {x : PiLp 2 X} (hx : x ∈ domG D) {l : Fin m} {y : X l}
    (hy : y ∈ D l) : upd x l y ∈ domG D := by
  intro j
  by_cases h : j = l
  · subst h; rw [upd_same]; exact hy
  · rw [upd_ne x h]; exact hx j

/-- g(x + U_l(y − x_l)) = g_l(y) + Σ_{j ≠ l} g_j(x_j). -/
lemma gsum_upd (g : ∀ l, X l → ℝ) (x : PiLp 2 X) (l : Fin m) (y : X l) :
    gsum g (upd x l y) = g l y + ∑ j ∈ univ.erase l, g j (x j) := by
  unfold gsum
  rw [← add_sum_erase _ _ (Finset.mem_univ l), upd_same]
  congr 1
  exact sum_congr rfl fun j hj => by rw [upd_ne x (ne_of_mem_erase hj)]

lemma gsum_eq (g : ∀ l, X l → ℝ) (x : PiLp 2 X) (l : Fin m) :
    gsum g x = g l (x l) + ∑ j ∈ univ.erase l, g j (x j) := by
  conv_lhs => rw [← upd_self x l]
  exact gsum_upd g x l (x l)

/-- E(x + U_l(y − x_l)) = Φ_{x,l}(y) + const, Φ_{x,l} := φ_{x,l} + g_l. -/
lemma Efun_upd (F : PiLp 2 X → ℝ) (g : ∀ l, X l → ℝ) (x : PiLp 2 X) (l : Fin m) (y : X l) :
    Efun F g (upd x l y) = slice F x l y + g l y + ∑ j ∈ univ.erase l, g j (x j) := by
  unfold Efun slice; rw [gsum_upd]; ring

lemma Efun_eq (F : PiLp 2 X → ℝ) (g : ∀ l, X l → ℝ) (x : PiLp 2 X) (l : Fin m) :
    Efun F g x = slice F x l (x l) + g l (x l) + ∑ j ∈ univ.erase l, g j (x j) := by
  conv_lhs => rw [← upd_self x l]
  exact Efun_upd F g x l (x l)

/-- Chain rule for the slice: ∇φ_{x,l}(y) = ∇_l F(x + U_l(y − x_l)). -/
lemma hasGradientAt_slice {F : PiLp 2 X → ℝ} (hF : Differentiable ℝ F) (x : PiLp 2 X)
    (l : Fin m) (y : X l) : HasGradientAt (slice F x l) (gradient F (upd x l y) l) y := by
  have hA : HasFDerivAt (fun y : X l => upd x l y) (U l) y := by
    have e : (fun y : X l => upd x l y) = fun y => x + (U l y - U l (x l)) := by
      funext y; simp [upd, map_sub]
    rw [e]
    exact ((U l).hasFDerivAt.sub_const _).const_add x
  have hc := (hF (upd x l y)).hasFDerivAt.comp y hA
  have hL : InnerProductSpace.toDual ℝ (X l) (gradient F (upd x l y) l)
      = (fderiv ℝ F (upd x l y)).comp (U l) := by
    ext k
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    rw [← inner_U, ← InnerProductSpace.toDual_apply_apply (𝕜 := ℝ), gradient,
      LinearIsometryEquiv.apply_symm_apply]
  rw [hasGradientAt_iff_hasFDerivAt, hL]
  exact hc

lemma gradient_slice {F : PiLp 2 X → ℝ} (hF : Differentiable ℝ F) (x : PiLp 2 X)
    (l : Fin m) (y : X l) : gradient (slice F x l) y = gradient F (upd x l y) l :=
  (hasGradientAt_slice hF x l y).gradient

lemma differentiable_slice {F : PiLp 2 X → ℝ} (hF : Differentiable ℝ F) (x : PiLp 2 X)
    (l : Fin m) : Differentiable ℝ (slice F x l) :=
  fun y => (hasGradientAt_slice hF x l y).differentiableAt


/-! ## Standing data SD4–SD6 and the derived constants -/

/-- SD5 (slice moduli): C(φ_{x,l}, τ_l) for every x and every block l. -/
def SliceMod (F : PiLp 2 X → ℝ) (τ : Fin m → ℝ) : Prop :=
  ∀ (x : PiLp 2 X) (l : Fin m), ModC (slice F x l) (τ l)

/-- SD6 (cross constants): ‖∇_j F(x + U_l h) − ∇_j F(x)‖ ≤ L_{jl}‖h‖ for j ≠ l, all x, h. -/
def CrossConst (F : PiLp 2 X → ℝ) (L : Fin m → Fin m → ℝ) : Prop :=
  ∀ (x : PiLp 2 X) (l j : Fin m), j ≠ l → ∀ h : X l,
    ‖gradient F (x + U l h) j - gradient F x j‖ ≤ L j l * ‖h‖

/-- ∇_l F(x) = ∇φ_{x,l}(x_l). -/
lemma gradient_block_eq {F : PiLp 2 X → ℝ} (hF : Differentiable ℝ F) (x : PiLp 2 X)
    (l : Fin m) : gradient F x l = gradient (slice F x l) (x l) := by
  rw [gradient_slice hF, upd_self]

/-- Convexity is preserved by the affine block update y ↦ x + U_l(y − x_l). -/
lemma convexOn_comp_upd {G : PiLp 2 X → ℝ} (hG : ConvexOn ℝ univ G) (x : PiLp 2 X)
    (l : Fin m) : ConvexOn ℝ univ (fun y : X l => G (upd x l y)) := by
  refine ⟨convex_univ, fun y₁ _ y₂ _ a b ha hb hab => ?_⟩
  have e : upd x l (a • y₁ + b • y₂) = a • upd x l y₁ + b • upd x l y₂ := by
    have hb' : b = 1 - a := by linarith
    subst hb'
    simp only [upd, map_sub, map_add, map_smul, smul_add, smul_sub, sub_smul, one_smul]
    abel
  simp only [smul_eq_mul]
  rw [e]
  exact hG.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

/-- ‖x + U_l(y − x_l)‖² = ‖y‖² + Σ_{j ≠ l} ‖x_j‖². -/
lemma norm_sq_upd (x : PiLp 2 X) (l : Fin m) (y : X l) :
    ‖upd x l y‖ ^ 2 = ‖y‖ ^ 2 + ∑ j ∈ univ.erase l, ‖x j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  exact gsum_upd (fun j (v : X j) => ‖v‖ ^ 2) x l y

/-- **Lemma H4.1(b), default slice modulus.** C(G, s) ⇒ C(φ^G_{x,l}, s) for every x, l
(so σ_C^{(l)} := σ_C is valid, and τ_l := σ is valid given C(F, σ)). -/
theorem slice_modC {G : PiLp 2 X → ℝ} {s : ℝ} (hG : ModC G s) : SliceMod G (fun _ => s) := by
  intro x l
  unfold ModC slice
  have h := convexOn_comp_upd hG x l
  have e : (fun y : X l => G (upd x l y) - s / 2 * ‖y‖ ^ 2)
      = fun y => (G (upd x l y) - s / 2 * ‖upd x l y‖ ^ 2)
          + s / 2 * ∑ j ∈ univ.erase l, ‖x j‖ ^ 2 := by
    funext y; rw [norm_sq_upd]; ring
  rw [e]
  exact h.add_const _

/-- Finite sums of convex functions are convex. -/
lemma convexOn_sum {E ι : Type*} [AddCommGroup E] [Module ℝ E] {S : Set E} (hS : Convex ℝ S)
    (t : Finset ι) (f : ι → E → ℝ) (h : ∀ i ∈ t, ConvexOn ℝ S (f i)) :
    ConvexOn ℝ S (fun x => ∑ i ∈ t, f i x) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using convexOn_const (0 : ℝ) hS
  | insert a t ha ih =>
    simp only [sum_insert ha]
    exact (h a (mem_insert_self a t)).add (ih fun i hi => h i (mem_insert_of_mem hi))

lemma convexOn_norm_sq {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y] :
    ConvexOn ℝ univ (fun y : Y => ‖y‖ ^ 2) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have h1 : ‖a • x + b • y‖ ≤ a * ‖x‖ + b * ‖y‖ := by
    calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
      _ = a * ‖x‖ + b * ‖y‖ := by
        rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
  have h2 : ‖a • x + b • y‖ ^ 2 ≤ (a * ‖x‖ + b * ‖y‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  simp only [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), mul_nonneg ha hb]

/-- The block projection x ↦ x_l as a linear map. -/
def projL (l : Fin m) : PiLp 2 X →ₗ[ℝ] X l where
  toFun x := x l
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma convexOn_comp_proj {l : Fin m} {φ : X l → ℝ} (h : ConvexOn ℝ univ φ) :
    ConvexOn ℝ univ (fun x : PiLp 2 X => φ (x l)) := by
  exact h.comp_linearMap (projL l)

/-- F(x) = Σ_l f_l(x_l) + C(x) (Lemma H4.1). -/
noncomputable def Fblk (f : ∀ l, X l → ℝ) (C : PiLp 2 X → ℝ) (x : PiLp 2 X) : ℝ :=
  gsum f x + C x

/-- **Lemma H4.1(a).** C(f_l, s_l) for every l and C(C, σ_C) ⇒ C(F, min_l s_l + σ_C). -/
theorem decl_sigma [Nonempty (Fin m)] {f : ∀ l, X l → ℝ} {C : PiLp 2 X → ℝ} {s : Fin m → ℝ}
    {σC : ℝ} (hf : ∀ l, ModC (f l) (s l)) (hC : ModC C σC) :
    ModC (Fblk f C) (univ.inf' univ_nonempty s + σC) := by
  set smin := univ.inf' univ_nonempty s
  unfold ModC
  have e : (fun x : PiLp 2 X => Fblk f C x - (smin + σC) / 2 * ‖x‖ ^ 2)
      = fun x => (∑ l, (f l (x l) - s l / 2 * ‖x l‖ ^ 2)
          + ∑ l, (s l - smin) / 2 * ‖x l‖ ^ 2) + (C x - σC / 2 * ‖x‖ ^ 2) := by
    funext x
    unfold Fblk gsum
    rw [PiLp.norm_sq_eq_of_L2]
    have key : ∀ i, f i (x i) - (smin + σC) / 2 * ‖x i‖ ^ 2
        = (f i (x i) - s i / 2 * ‖x i‖ ^ 2) + (s i - smin) / 2 * ‖x i‖ ^ 2
          - σC / 2 * ‖x i‖ ^ 2 := fun i => by ring
    calc ∑ l, f l (x l) + C x - (smin + σC) / 2 * ∑ i, ‖x i‖ ^ 2
          = ∑ i, (f i (x i) - (smin + σC) / 2 * ‖x i‖ ^ 2) + C x := by
            rw [sum_sub_distrib, ← mul_sum]; ring
      _ = ∑ i, ((f i (x i) - s i / 2 * ‖x i‖ ^ 2) + (s i - smin) / 2 * ‖x i‖ ^ 2
          - σC / 2 * ‖x i‖ ^ 2) + C x := by rw [sum_congr rfl fun i _ => key i]
      _ = _ := by rw [sum_sub_distrib, sum_add_distrib, ← mul_sum]; ring
  rw [e]
  refine ConvexOn.add (ConvexOn.add ?_ ?_) hC
  · exact convexOn_sum convex_univ _ _ fun l _ => convexOn_comp_proj (hf l)
  · refine convexOn_sum convex_univ _ _ fun l _ => ?_
    have hl : 0 ≤ (s l - smin) / 2 := by
      have := inf'_le (s := univ) s (Finset.mem_univ l); linarith
    have := (convexOn_comp_proj (l := l) (convexOn_norm_sq (Y := X l))).smul hl
    simpa [smul_eq_mul] using this

lemma slice_Fblk (f : ∀ l, X l → ℝ) (C : PiLp 2 X → ℝ) (x : PiLp 2 X) (l : Fin m) :
    slice (Fblk f C) x l = fun y => f l y + slice C x l y + ∑ j ∈ univ.erase l, f j (x j) := by
  funext y; unfold slice Fblk; rw [gsum_upd]; ring

/-- **Lemma H4.1(b).** C(f_l, s_l) and declared slice moduli σ_C^{(l)} of C ⇒ SD5 with
τ_l := s_l + σ_C^{(l)}. -/
theorem decl_tau {f : ∀ l, X l → ℝ} {C : PiLp 2 X → ℝ} {s σCl : Fin m → ℝ}
    (hf : ∀ l, ModC (f l) (s l)) (hCl : SliceMod C σCl) :
    SliceMod (Fblk f C) (fun l => s l + σCl l) := by
  intro x l
  unfold ModC
  rw [slice_Fblk]
  have e : (fun y : X l => f l y + slice C x l y + ∑ j ∈ univ.erase l, f j (x j)
        - (s l + σCl l) / 2 * ‖y‖ ^ 2)
      = fun y => ((f l y - s l / 2 * ‖y‖ ^ 2) + (slice C x l y - σCl l / 2 * ‖y‖ ^ 2))
          + ∑ j ∈ univ.erase l, f j (x j) := by
    funext y; ring
  rw [e]
  exact ((hf l).add (hCl x l)).add_const _

/-- **Lemma H4.1(b), τ_l := σ.** C(F, σ) ⇒ SD5 with τ_l := σ. -/
theorem decl_tau_sigma {F : PiLp 2 X → ℝ} {σ : ℝ} (hF : ModC F σ) : SliceMod F (fun _ => σ) :=
  slice_modC hF

/-- ∇_j F(x) = ∇f_j(x_j) + ∇_j C(x) for F = Σ_l f_l(x_l) + C. -/
lemma gradient_Fblk {f : ∀ l, X l → ℝ} {C : PiLp 2 X → ℝ} (hf : ∀ l, Differentiable ℝ (f l))
    (hC : Differentiable ℝ C) (x : PiLp 2 X) (j : Fin m) :
    gradient (Fblk f C) x j = gradient (f j) (x j) + gradient C x j := by
  have hF : Differentiable ℝ (Fblk f C) := by
    unfold Fblk gsum
    refine Differentiable.add (Differentiable.fun_sum fun l _ => ?_) hC
    exact (hf l).comp (PiLp.proj 2 (𝕜 := ℝ) X l).differentiable
  rw [gradient_block_eq hF, slice_Fblk]
  have h1 := ((hf j) (x j)).hasGradientAt
  have h2 := hasGradientAt_slice hC x j (x j)
  rw [upd_self] at h2
  have h3 := (h1.hasFDerivAt.add h2.hasFDerivAt).add_const (∑ i ∈ univ.erase j, f i (x i))
  rw [← map_add] at h3
  exact (hasGradientAt_iff_hasFDerivAt.2 h3).gradient

/-- **Lemma H4.1(c).** F = Σ_l f_l(x_l) + C with f_l, C differentiable: cross constants of C
are cross constants of F (L_{jl} := L^C_{jl}). -/
theorem decl_cross {f : ∀ l, X l → ℝ} {C : PiLp 2 X → ℝ} {LC : Fin m → Fin m → ℝ}
    (hf : ∀ l, Differentiable ℝ (f l)) (hC : Differentiable ℝ C) (hL : CrossConst C LC) :
    CrossConst (Fblk f C) LC := by
  intro x l j hjl h
  rw [gradient_Fblk hf hC, gradient_Fblk hf hC]
  have hx : (x + U l h) j = x j := by
    change x j + (U l h) j = x j; rw [U_ne hjl, add_zero]
  rw [hx, add_sub_add_left_eq_sub]
  exact hL x l j hjl h

/-- **Lemma H4.1(c), default.** ∇C β_C-Lipschitz ⇒ L^C_{jl} := β_C is valid. -/
theorem decl_cross_default {C : PiLp 2 X → ℝ} {βC : ℝ} (hL : LipGrad C βC) :
    CrossConst C (fun _ _ => βC) := by
  intro x l j _ h
  calc ‖gradient C (x + U l h) j - gradient C x j‖
        = ‖(gradient C (x + U l h) - gradient C x) j‖ := rfl
    _ ≤ ‖gradient C (x + U l h) - gradient C x‖ := PiLp.norm_apply_le _ _
    _ ≤ βC * ‖x + U l h - x‖ := hL _ _
    _ = βC * ‖h‖ := by rw [add_sub_cancel_left, norm_U]

/-- c_j² := Σ_{l > j} L_{jl}²/τ_l. -/
noncomputable def cj2 (L : Fin m → Fin m → ℝ) (τ : Fin m → ℝ) (j : Fin m) : ℝ :=
  ∑ l, if j < l then L j l ^ 2 / τ l else 0

/-- Λ² := Σ_{j<l} L_{jl}²/τ_l (sum over ordered pairs j < l; 0 if m = 1). -/
noncomputable def Lam2 (L : Fin m → Fin m → ℝ) (τ : Fin m → ℝ) : ℝ := ∑ j, cj2 L τ j

/-- Λ := (Σ_{j<l} L_{jl}²/τ_l)^{1/2}. -/
noncomputable def Lam (L : Fin m → Fin m → ℝ) (τ : Fin m → ℝ) : ℝ := √(Lam2 L τ)

lemma cj2_nonneg {L : Fin m → Fin m → ℝ} {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) (j : Fin m) :
    0 ≤ cj2 L τ j :=
  sum_nonneg fun l _ => by split_ifs <;> [exact div_nonneg (sq_nonneg _) (hτ l).le; exact le_rfl]

lemma Lam2_nonneg {L : Fin m → Fin m → ℝ} {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) :
    0 ≤ Lam2 L τ := sum_nonneg fun j _ => cj2_nonneg hτ j

lemma Lam_sq {L : Fin m → Fin m → ℝ} {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) :
    Lam L τ ^ 2 = Lam2 L τ := Real.sq_sqrt (Lam2_nonneg hτ)

end Blocks

/-! ## Lemma H4.2 at the level of one block function Φ = φ + g_l -/

section OneBlock

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- C(φ, τ) on the whole space and g convex on D ⇒ C(φ + g, τ) on D. -/
lemma modCD_add {φ : Y → ℝ} {τ : ℝ} (hC : ModC φ τ) {D : Set Y} {g : Y → ℝ}
    (hg : ModCD D g 0) : ModCD D (fun y => φ y + g y) τ := by
  have h1 : ConvexOn ℝ D (fun y => φ y - τ / 2 * ‖y‖ ^ 2) := hC.subset (subset_univ D) hg.1
  have := h1.add hg
  unfold ModCD
  exact this.congr fun y _ => by simp only [Pi.add_apply]; ring

/-- Growth at a minimiser: C(Ψ, τ) on D and y* minimising Ψ on D ⇒
Ψ(w) ≥ Ψ(y*) + (τ/2)‖w − y*‖² on D. -/
lemma growth_of_minD {D : Set Y} {Ψ : Y → ℝ} {τ : ℝ} (hC : ModCD D Ψ τ) {ys : Y} (hys : ys ∈ D)
    (hmin : ∀ w ∈ D, Ψ ys ≤ Ψ w) {w : Y} (hw : w ∈ D) : Ψ ys + τ / 2 * ‖w - ys‖ ^ 2 ≤ Ψ w := by
  have h0 : EpsSubgrad D Ψ 0 ys 0 := ⟨hys, fun w hw => by simpa using hmin w hw⟩
  have := strong_of_subgrad hC h0 hw
  simpa using this

/-- Uniqueness of a minimiser under C(Ψ, τ), τ > 0. -/
lemma unique_of_minD {D : Set Y} {Ψ : Y → ℝ} {τ : ℝ} (hτ : 0 < τ) (hC : ModCD D Ψ τ) {ys : Y}
    (hys : ys ∈ D) (hmin : ∀ w ∈ D, Ψ ys ≤ Ψ w) {y : Y} (hy : y ∈ D)
    (hymin : ∀ w ∈ D, Ψ y ≤ Ψ w) : y = ys := by
  have h1 := growth_of_minD hC hys hmin hy
  have h2 := hymin ys hys
  have : ‖y - ys‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖y - ys‖ = 0 := by nlinarith [norm_nonneg (y - ys)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **(K)** of Lemma H4.2: Φ(w) ≥ Φ(z) + ⟨e, w − z⟩ + (τ/2)‖w − z‖² − ε, e := ∇φ(z) + v. -/
lemma key_K {φ : Y → ℝ} {τ : ℝ} (hφ : Differentiable ℝ φ) (hC : ModC φ τ) {D : Set Y}
    {g : Y → ℝ} {ε : ℝ} {z v : Y} (hv : EpsSubgrad D g ε z v) {w : Y} (hw : w ∈ D) :
    φ z + g z + inner ℝ (gradient φ z + v) (w - z) + τ / 2 * ‖w - z‖ ^ 2 - ε ≤ φ w + g w := by
  have h1 := strongSubgrad_of_modC hφ hC z w
  have h2 := hv.2 w hw
  rw [inner_add_left]; linarith

/-- **Lemma H4.2(a), block form.** Φ(z) − Φ(w) ≤ γ := η²/(2τ) + ε for every w ∈ dom g_l. -/
theorem block_gap {φ : Y → ℝ} {τ : ℝ} (hτ : 0 < τ) (hφ : Differentiable ℝ φ) (hC : ModC φ τ)
    {D : Set Y} {g : Y → ℝ} {ε : ℝ} {z v : Y} (hv : EpsSubgrad D g ε z v) {w : Y}
    (hw : w ∈ D) :
    φ z + g z ≤ φ w + g w + (‖gradient φ z + v‖ ^ 2 / (2 * τ) + ε) := by
  have h1 := key_K hφ hC hv hw
  have h2 := complete_square (gradient φ z + v) (w - z) hτ
  linarith

/-- **Lemma H4.2(b), block form.** Φ(x_l) − Φ(z) ≥ (τ/2)‖h‖² − η‖h‖ − ε, h := z − x_l. -/
theorem block_descent {φ : Y → ℝ} {τ : ℝ} (hφ : Differentiable ℝ φ) (hC : ModC φ τ)
    {D : Set Y} {g : Y → ℝ} {ε : ℝ} {z v : Y} (hv : EpsSubgrad D g ε z v) {xl : Y}
    (hxl : xl ∈ D) :
    τ / 2 * ‖z - xl‖ ^ 2 - ‖gradient φ z + v‖ * ‖z - xl‖ - ε
      ≤ (φ xl + g xl) - (φ z + g z) := by
  have h1 := key_K hφ hC hv hxl
  have h2 : -(‖gradient φ z + v‖ * ‖xl - z‖) ≤ inner ℝ (gradient φ z + v) (xl - z) :=
    neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  rw [norm_sub_rev xl z] at h1 h2
  linarith

/-- The scalar step of Lemma H4.2(c): from Δ ≥ (τ/2)t² − ηt − ε (t, η, ε ≥ 0, τ > 0) and
γ := η²/(2τ) + ε: Δ + γ ≥ 0 and √τ t ≤ √(2(Δ + γ)) + √(2γ). -/
lemma scalar_c {τ t η ε Δ : ℝ} (hτ : 0 < τ) (hε : 0 ≤ ε)
    (hΔ : τ / 2 * t ^ 2 - η * t - ε ≤ Δ) :
    0 ≤ Δ + (η ^ 2 / (2 * τ) + ε) ∧
      √τ * t ≤ √(2 * (Δ + (η ^ 2 / (2 * τ) + ε))) + √(2 * (η ^ 2 / (2 * τ) + ε)) := by
  set r := √τ with hr
  have hr0 : 0 < r := Real.sqrt_pos.2 hτ
  have hr2 : r ^ 2 = τ := Real.sq_sqrt hτ.le
  have hsq : (r * t - η / r) ^ 2 ≤ 2 * (Δ + (η ^ 2 / (2 * τ) + ε)) := by
    have e : (r * t - η / r) ^ 2 = τ * t ^ 2 - 2 * η * t + η ^ 2 / τ := by
      field_simp; rw [← hr2]; ring
    rw [e]
    have : η ^ 2 / (2 * τ) = η ^ 2 / τ / 2 := by ring
    rw [this]; linarith
  refine ⟨by nlinarith [sq_nonneg (r * t - η / r)], ?_⟩
  have h1 : r * t - η / r ≤ √(2 * (Δ + (η ^ 2 / (2 * τ) + ε))) :=
    (le_abs_self _).trans (Real.abs_le_sqrt hsq)
  have h2 : η / r ≤ √(2 * (η ^ 2 / (2 * τ) + ε)) := by
    apply Real.le_sqrt_of_sq_le
    have e : (η / r) ^ 2 = η ^ 2 / τ := by rw [div_pow, hr2]
    rw [e]
    have : 2 * (η ^ 2 / (2 * τ)) = η ^ 2 / τ := by field_simp
    nlinarith
  linarith

/-- **Lemma H4.2(c), block form.** Δ + γ ≥ 0 and √τ‖h‖ ≤ √(2(Δ + γ)) + √(2γ), with
Δ := Φ(x_l) − Φ(z), γ := η²/(2τ) + ε (ε ≥ 0). -/
theorem block_move {φ : Y → ℝ} {τ : ℝ} (hτ : 0 < τ) (hφ : Differentiable ℝ φ) (hC : ModC φ τ)
    {D : Set Y} {g : Y → ℝ} {ε : ℝ} (hε : 0 ≤ ε) {z v : Y} (hv : EpsSubgrad D g ε z v) {xl : Y}
    (hxl : xl ∈ D) :
    0 ≤ (φ xl + g xl) - (φ z + g z) + (‖gradient φ z + v‖ ^ 2 / (2 * τ) + ε) ∧
      √τ * ‖z - xl‖ ≤ √(2 * ((φ xl + g xl) - (φ z + g z) + (‖gradient φ z + v‖ ^ 2 / (2 * τ) + ε)))
        + √(2 * (‖gradient φ z + v‖ ^ 2 / (2 * τ) + ε)) :=
  scalar_c hτ hε (block_descent hφ hC hv hxl)

/-- **Lemma H4.2(a), minimiser form.** If Φ = φ + g has a minimiser y* on dom g (classical
(EX), taken as a hypothesis), it is the only one and Φ(z) − Φ(y*) ≤ γ. -/
theorem block_min {φ : Y → ℝ} {τ : ℝ} (hτ : 0 < τ) (hφ : Differentiable ℝ φ) (hC : ModC φ τ)
    {D : Set Y} {g : Y → ℝ} (hg : ModCD D g 0) {ε : ℝ} {z v : Y} (hv : EpsSubgrad D g ε z v)
    {ys : Y} (hys : ys ∈ D) (hmin : ∀ w ∈ D, φ ys + g ys ≤ φ w + g w) :
    (∀ y ∈ D, (∀ w ∈ D, φ y + g y ≤ φ w + g w) → y = ys) ∧
      (φ z + g z) - (φ ys + g ys) ≤ ‖gradient φ z + v‖ ^ 2 / (2 * τ) + ε := by
  refine ⟨fun y hy hymin => unique_of_minD hτ (modCD_add hC hg) hys hmin hy hymin, ?_⟩
  have := block_gap hτ hφ hC hv hys
  linarith

/-- **Lemma H4.2(d)** (equality cases) for the smooth block Φ(y) = (τ/2)‖y − c‖² (g_l = 0,
v = 0, ε = 0; minimiser y* = c): (a) holds with equality for every z; the expansion
Φ(x_l) = Φ(z) + ⟨e, x_l − z⟩ + (τ/2)‖x_l − z‖² is exact, so (b) is an equality iff
⟨e, x_l − z⟩ = −η‖h‖; at z = c, (c) is an equality. -/
theorem block_equality {τ : ℝ} (hτ : 0 < τ) (c : Y) :
    (∀ z, (τ / 2 * ‖z - c‖ ^ 2) - τ / 2 * ‖c - c‖ ^ 2
        = ‖gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) z‖ ^ 2 / (2 * τ)) ∧
    (∀ z xl, τ / 2 * ‖xl - c‖ ^ 2 = τ / 2 * ‖z - c‖ ^ 2
        + inner ℝ (gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) z) (xl - z) + τ / 2 * ‖xl - z‖ ^ 2) ∧
    (∀ z xl, (τ / 2 * ‖xl - c‖ ^ 2 - τ / 2 * ‖z - c‖ ^ 2
          = τ / 2 * ‖z - xl‖ ^ 2 - ‖gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) z‖ * ‖z - xl‖) ↔
        inner ℝ (gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) z) (xl - z)
          = -(‖gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) z‖ * ‖z - xl‖)) ∧
    (∀ xl, ‖gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) c‖ = 0 ∧
      √τ * ‖c - xl‖ = √(2 * ((τ / 2 * ‖xl - c‖ ^ 2 - τ / 2 * ‖c - c‖ ^ 2)
          + (‖gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) c‖ ^ 2 / (2 * τ) + 0)))
        + √(2 * (‖gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) c‖ ^ 2 / (2 * τ) + 0))) := by
  have hg : ∀ z, gradient (fun y => τ / 2 * ‖y - c‖ ^ 2) z = τ • (z - c) := by
    intro z
    have := (hasGradientAt_quadc τ 0 c z).gradient
    simpa using this
  have hexp : ∀ z xl : Y, τ / 2 * ‖xl - c‖ ^ 2 = τ / 2 * ‖z - c‖ ^ 2
      + inner ℝ (τ • (z - c)) (xl - z) + τ / 2 * ‖xl - z‖ ^ 2 := by
    intro z xl
    have e : xl - c = (z - c) + (xl - z) := by abel
    rw [e, norm_add_sq_real, real_inner_smul_left]; ring
  refine ⟨fun z => ?_, fun z xl => by rw [hg]; exact hexp z xl, fun z xl => ?_, fun xl => ?_⟩
  · rw [hg, norm_smul, Real.norm_of_nonneg hτ.le, sub_self, norm_zero]
    field_simp; ring
  · rw [hg, hexp z xl, norm_sub_rev xl z]
    constructor <;> intro h <;> linarith
  · rw [hg, sub_self, smul_zero, norm_zero]
    refine ⟨rfl, ?_⟩
    have e : 2 * (τ / 2 * ‖xl - c‖ ^ 2 - τ / 2 * 0 ^ 2 + (0 ^ 2 / (2 * τ) + 0))
        = (√τ * ‖c - xl‖) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt hτ.le, norm_sub_rev]; ring
    rw [e, Real.sqrt_sq (by positivity)]
    simp

end OneBlock

/-! ## Lemma H4.3 (reports from other accuracy senses), block form -/

section Reports

variable {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [CompleteSpace Y]

/-- **Lemma H4.3(a).** Smooth block (g_l = 0): if φ(z) ≤ inf φ + e (∇φ L-Lipschitz, L > 0),
then (z, 0, 0) is a block report (0 ∈ ∂_0 0(z)) and η = ‖∇φ(z)‖ ≤ √(2Le). -/
theorem report_smooth {φ : Y → ℝ} {L e : ℝ} (hL0 : 0 < L) (hφ : Differentiable ℝ φ)
    (hL : LipGrad φ L) {z : Y} (hgap : ∀ w, φ z ≤ φ w + e) :
    EpsSubgrad univ (fun _ => (0 : ℝ)) 0 z 0 ∧ ‖gradient φ z + 0‖ ≤ √(2 * L * e) := by
  refine ⟨⟨mem_univ z, fun w _ => by simp⟩, ?_⟩
  rw [add_zero]
  have h1 := upper_bound hφ hL z (z - L⁻¹ • gradient φ z)
  have h2 := hgap (z - L⁻¹ • gradient φ z)
  rw [sub_sub_cancel_left, inner_neg_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
    norm_neg, norm_smul, Real.norm_of_nonneg (inv_pos.2 hL0).le] at h1
  apply Real.le_sqrt_of_sq_le
  have : ‖gradient φ z‖ ^ 2 / (2 * L) ≤ e := by
    have e1 : L / 2 * (L⁻¹ * ‖gradient φ z‖) ^ 2 = ‖gradient φ z‖ ^ 2 / (2 * L) := by
      field_simp
    have e2 : L⁻¹ * ‖gradient φ z‖ ^ 2 = ‖gradient φ z‖ ^ 2 / L := by field_simp
    rw [e1, e2] at h1
    have : ‖gradient φ z‖ ^ 2 / L = 2 * (‖gradient φ z‖ ^ 2 / (2 * L)) := by field_simp
    linarith
  rw [div_le_iff₀ (by positivity)] at this
  linarith

/-- **Lemma H4.3(b)** (one polishing prox-gradient step). Φ = φ + g, ∇φ L-Lipschitz,
0 < L ≤ M, Φ(z) ≤ inf Φ + e (z ∈ dom g), p := prox_{g/M}(z − ∇φ(z)/M) (given by its
characterisation (P), a classical input), v := M(z − p) − ∇φ(z). Then (p, v, 0) is a block
report, Φ(p) ≤ Φ(z), and η = ‖∇φ(p) + v‖ ≤ (1 + L/M)√(2Me). -/
theorem report_polish {φ : Y → ℝ} {L M e : ℝ} (hL0 : 0 < L) (hLM : L ≤ M)
    (hφ : Differentiable ℝ φ) (hL : LipGrad φ L) {D : Set Y} {g : Y → ℝ} {z p : Y}
    (hz : z ∈ D) (hgap : ∀ w ∈ D, φ z + g z ≤ φ w + g w + e)
    (hp : ProxEps D g M⁻¹ 0 (z - M⁻¹ • gradient φ z) p) :
    EpsSubgrad D g 0 p (M • (z - p) - gradient φ z) ∧ φ p + g p ≤ φ z + g z ∧
      ‖gradient φ p + (M • (z - p) - gradient φ z)‖ ≤ (1 + L / M) * √(2 * M * e) := by
  have hM : 0 < M := lt_of_lt_of_le hL0 hLM
  have hv : (M⁻¹)⁻¹ • (z - M⁻¹ • gradient φ z - p) = M • (z - p) - gradient φ z := by
    simp only [inv_inv, smul_sub, smul_smul, mul_inv_cancel₀ hM.ne', one_smul]; abel
  unfold ProxEps at hp
  rw [hv] at hp
  set v := M • (z - p) - gradient φ z with hvdef
  -- sufficient decrease Φ(p) ≤ Φ(z) − (M/2)‖z − p‖²
  have h1 := upper_bound hφ hL z p
  have h2 := hp.2 z hz
  have hin : inner ℝ v (z - p) = M * ‖z - p‖ ^ 2 - inner ℝ (gradient φ z) (z - p) := by
    rw [hvdef, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hpz : inner ℝ (gradient φ z) (p - z) = -inner ℝ (gradient φ z) (z - p) := by
    rw [← inner_neg_right, neg_sub]
  rw [hpz, norm_sub_rev p z] at h1
  have hdec : φ p + g p ≤ φ z + g z - M / 2 * ‖z - p‖ ^ 2 := by
    nlinarith [sq_nonneg ‖z - p‖]
  refine ⟨hp, by nlinarith [sq_nonneg ‖z - p‖], ?_⟩
  have hgp := hgap p hp.1
  have hzp : M / 2 * ‖z - p‖ ^ 2 ≤ e := by linarith
  have he : 0 ≤ e := le_trans (by positivity) hzp
  -- ‖∇φ(p) + v‖ ≤ (M + L)‖z − p‖
  have hn : ‖gradient φ p + v‖ ≤ (M + L) * ‖z - p‖ := by
    have e' : gradient φ p + v = M • (z - p) + (gradient φ p - gradient φ z) := by
      rw [hvdef]; abel
    rw [e']
    calc ‖M • (z - p) + (gradient φ p - gradient φ z)‖
          ≤ ‖M • (z - p)‖ + ‖gradient φ p - gradient φ z‖ := norm_add_le _ _
      _ ≤ M * ‖z - p‖ + L * ‖p - z‖ := by
          rw [norm_smul, Real.norm_of_nonneg hM.le]; linarith [hL p z]
      _ = (M + L) * ‖z - p‖ := by rw [norm_sub_rev p z]; ring
  have hzp' : M * ‖z - p‖ ≤ √(2 * M * e) := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  calc ‖gradient φ p + v‖ ≤ (M + L) * ‖z - p‖ := hn
    _ = (1 + L / M) * (M * ‖z - p‖) := by field_simp
    _ ≤ (1 + L / M) * √(2 * M * e) := by
        apply mul_le_mul_of_nonneg_left hzp'; positivity

/-- **Lemma H4.3(b) at M = L:** η ≤ 2√(2Le). -/
theorem report_polish_L {φ : Y → ℝ} {L e : ℝ} (hL0 : 0 < L)
    (hφ : Differentiable ℝ φ) (hL : LipGrad φ L) {D : Set Y} {g : Y → ℝ} {z p : Y}
    (hz : z ∈ D) (hgap : ∀ w ∈ D, φ z + g z ≤ φ w + g w + e)
    (hp : ProxEps D g L⁻¹ 0 (z - L⁻¹ • gradient φ z) p) :
    EpsSubgrad D g 0 p (L • (z - p) - gradient φ z) ∧ φ p + g p ≤ φ z + g z ∧
      ‖gradient φ p + (L • (z - p) - gradient φ z)‖ ≤ 2 * √(2 * L * e) := by
  obtain ⟨h1, h2, h3⟩ := report_polish hL0 le_rfl hφ hL hz hgap hp
  refine ⟨h1, h2, ?_⟩
  rw [div_self hL0.ne'] at h3
  linarith

/-- **Lemma H4.3(c)** (H2 inexact forward–backward step, α = 1/L): if
z ∈ prox^ε_{αg}(y − α∇φ(y)), then with v := (y − z)/α − ∇φ(y), (z, v, ε) is a block report
and η = ‖∇φ(z) + v‖ ≤ 2‖y − z‖/α. -/
theorem report_H2 {φ : Y → ℝ} {L α ε : ℝ} (hα : 0 < α) (hαL : α * L = 1)
    (hL : LipGrad φ L) {D : Set Y} {g : Y → ℝ} {y z : Y}
    (hz : ProxEps D g α ε (y - α • gradient φ y) z) :
    EpsSubgrad D g ε z (α⁻¹ • (y - z) - gradient φ y) ∧
      ‖gradient φ z + (α⁻¹ • (y - z) - gradient φ y)‖ ≤ 2 * ‖y - z‖ / α := by
  have hv : α⁻¹ • (y - α • gradient φ y - z) = α⁻¹ • (y - z) - gradient φ y := by
    rw [show y - α • gradient φ y - z = (y - z) - α • gradient φ y by abel, smul_sub, smul_smul,
      inv_mul_cancel₀ hα.ne', one_smul]
  unfold ProxEps at hz
  rw [hv] at hz
  refine ⟨hz, ?_⟩
  have hL' : L = α⁻¹ := by field_simp; linarith
  have e : gradient φ z + (α⁻¹ • (y - z) - gradient φ y)
      = α⁻¹ • (y - z) + (gradient φ z - gradient φ y) := by abel
  rw [e]
  calc ‖α⁻¹ • (y - z) + (gradient φ z - gradient φ y)‖
        ≤ ‖α⁻¹ • (y - z)‖ + ‖gradient φ z - gradient φ y‖ := norm_add_le _ _
    _ ≤ α⁻¹ * ‖y - z‖ + L * ‖z - y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le]; linarith [hL z y]
    _ = 2 * ‖y - z‖ / α := by rw [hL', norm_sub_rev z y]; field_simp; ring

/-- The ε-subdifferential sum rule at a point, as a hypothesis (classical:
Hiriart-Urruty–Lemaréchal 1993, vol. II, Ch. XI, Thm 3.1.1, for φ convex finite and g ∈ Γ₀):
every u ∈ ∂_e(φ + g)(z) splits as u = w + v with w ∈ ∂_{e₁}φ(z), v ∈ ∂_{e₂}g(z),
e₁ + e₂ = e, e₁, e₂ ≥ 0. -/
def EpsSumRule (D : Set Y) (φ g : Y → ℝ) : Prop :=
  ∀ (e : ℝ) (z u : Y), 0 ≤ e → EpsSubgrad D (fun y => φ y + g y) e z u →
    ∃ e₁ e₂ : ℝ, ∃ w v : Y, 0 ≤ e₁ ∧ 0 ≤ e₂ ∧ e₁ + e₂ = e ∧ EpsSubgrad univ φ e₁ z w ∧
      EpsSubgrad D g e₂ z v ∧ u = w + v

/-- [CLASSICAL?, derived in place] For φ with L-Lipschitz gradient (L > 0),
w ∈ ∂_{e₁}φ(z) ⇒ ‖w − ∇φ(z)‖ ≤ √(2Le₁). -/
theorem epsSubgrad_smooth {φ : Y → ℝ} {L e₁ : ℝ} (hL0 : 0 < L) (hφ : Differentiable ℝ φ)
    (hL : LipGrad φ L) {z w : Y} (hw : EpsSubgrad univ φ e₁ z w) :
    ‖w - gradient φ z‖ ≤ √(2 * L * e₁) := by
  set d := w - gradient φ z
  have h1 := hw.2 (z + L⁻¹ • d) (mem_univ _)
  have h2 := upper_bound hφ hL z (z + L⁻¹ • d)
  rw [add_sub_cancel_left] at h1 h2
  rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hL0).le] at h2
  have hin : inner ℝ w (L⁻¹ • d) - inner ℝ (gradient φ z) (L⁻¹ • d) = L⁻¹ * ‖d‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  apply Real.le_sqrt_of_sq_le
  have key : L⁻¹ * ‖d‖ ^ 2 ≤ e₁ + L / 2 * (L⁻¹ * ‖d‖) ^ 2 := by linarith
  have e2 : L / 2 * (L⁻¹ * ‖d‖) ^ 2 = L⁻¹ * ‖d‖ ^ 2 / 2 := by field_simp
  rw [e2] at key
  have : L⁻¹ * ‖d‖ ^ 2 ≤ 2 * e₁ := by linarith
  have h3 : ‖d‖ ^ 2 = L * (L⁻¹ * ‖d‖ ^ 2) := by field_simp
  rw [h3]
  nlinarith

/-- C(φ, τ) and ∇φ L-Lipschitz on a nontrivial space (d_l ≥ 1) ⇒ τ ≤ L. -/
theorem tau_le_L [Nontrivial Y] {φ : Y → ℝ} {τ L : ℝ} (hφ : Differentiable ℝ φ)
    (hC : ModC φ τ) (hL : LipGrad φ L) : τ ≤ L := by
  obtain ⟨y, hy⟩ := exists_ne (0 : Y)
  have h1 := (modC_iff_strongMono hφ τ).1 hC y 0
  have h2 := real_inner_le_norm (gradient φ y - gradient φ 0) (y - 0)
  have h3 := hL y 0
  have hpos : 0 < ‖y - 0‖ := by rw [sub_zero]; exact norm_pos_iff.2 hy
  have : τ * ‖y - 0‖ ^ 2 ≤ L * ‖y - 0‖ ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right h3 hpos.le]
  exact le_of_mul_le_mul_right this (by positivity)

/-- **Lemma H4.3(d)** (bare value gap; existence). φ with L-Lipschitz gradient (L > 0) and
C(φ, τ), τ > 0 (SD5), on a nontrivial block space; the ε-sum rule for (φ, g) at hand (a
classical input). If z ∈ dom g and Φ(z) ≤ inf Φ + e, then there are e₁, e₂ ≥ 0, e₁ + e₂ = e,
and v ∈ ∂_{e₂}g(z) with ‖∇φ(z) + v‖ ≤ √(2Le₁). So (z, v, e₂) is a block report with
η ≤ √(2Le), ε ≤ e and γ = η²/(2τ) + ε ≤ Le₁/τ + e₂ ≤ (L/τ)e. -/
theorem report_valuegap [Nontrivial Y] {φ : Y → ℝ} {L τ e : ℝ} (hL0 : 0 < L) (hτ : 0 < τ)
    (hφ : Differentiable ℝ φ) (hL : LipGrad φ L) (hC : ModC φ τ) {D : Set Y} {g : Y → ℝ}
    (hsum : EpsSumRule D φ g) (he : 0 ≤ e) {z : Y} (hz : z ∈ D)
    (hgap : ∀ w ∈ D, φ z + g z ≤ φ w + g w + e) :
    ∃ e₁ e₂ : ℝ, ∃ v : Y, 0 ≤ e₁ ∧ 0 ≤ e₂ ∧ e₁ + e₂ = e ∧ EpsSubgrad D g e₂ z v ∧
      ‖gradient φ z + v‖ ≤ √(2 * L * e₁) ∧ ‖gradient φ z + v‖ ≤ √(2 * L * e) ∧ e₂ ≤ e ∧
      ‖gradient φ z + v‖ ^ 2 / (2 * τ) + e₂ ≤ L * e₁ / τ + e₂ ∧
      L * e₁ / τ + e₂ ≤ L / τ * e := by
  have h0 : EpsSubgrad D (fun y => φ y + g y) e z 0 :=
    ⟨hz, fun w hw => by simpa using hgap w hw⟩
  obtain ⟨e₁, e₂, w, v, he₁, he₂, hsum', hw, hv, huv⟩ := hsum e z 0 he h0
  have hwv : gradient φ z + v = -(w - gradient φ z) := by
    have : v = -w := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact huv.symm
    rw [this]; abel
  have hn : ‖gradient φ z + v‖ ≤ √(2 * L * e₁) := by
    rw [hwv, norm_neg]; exact epsSubgrad_smooth hL0 hφ hL hw
  have hτL := tau_le_L hφ hC hL
  have hsq : ‖gradient φ z + v‖ ^ 2 ≤ 2 * L * e₁ := by
    have := pow_le_pow_left₀ (norm_nonneg _) hn 2
    rwa [Real.sq_sqrt (by positivity)] at this
  refine ⟨e₁, e₂, v, he₁, he₂, hsum', hv, hn, hn.trans (Real.sqrt_le_sqrt (by nlinarith)),
    by linarith, ?_, ?_⟩
  · have : ‖gradient φ z + v‖ ^ 2 / (2 * τ) ≤ L * e₁ / τ := by
      rw [div_le_div_iff₀ (by positivity) hτ]; nlinarith
    linarith
  · have h1 : 1 ≤ L / τ := by rw [le_div_iff₀ hτ]; linarith
    have : e₂ ≤ L / τ * e₂ := by nlinarith
    calc L * e₁ / τ + e₂ ≤ L / τ * e₁ + L / τ * e₂ := by rw [mul_div_right_comm]; linarith
      _ = L / τ * e := by rw [← mul_add, hsum']

end Reports

/-! ## Lemma H4.5 (value and distance from an ε-subgradient), any space -/

section Bracket

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z] [CompleteSpace Z]

/-- **Lemma H4.5(i).** C(F, σ), σ > 0, F differentiable, x* a minimiser of E = F + g on
dom g, v ∈ ∂_ε g(x), u := ∇F(x) + v: E(x) − ‖u‖²/(2σ) − ε ≤ E* ≤ E(x). -/
theorem value_bracket {F : Z → ℝ} {D : Set Z} {g : Z → ℝ} {σ : ℝ} (hF : Differentiable ℝ F)
    (hC : ModC F σ) (hσ : 0 < σ) {xs : Z} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, F xs + g xs ≤ F w + g w) {x v : Z} {ε : ℝ} (hv : EpsSubgrad D g ε x v) :
    F x + g x - ‖gradient F x + v‖ ^ 2 / (2 * σ) - ε ≤ F xs + g xs ∧
      F xs + g xs ≤ F x + g x := by
  refine ⟨?_, hmin x hv.1⟩
  have h1 := strongSubgrad_of_modC hF hC x xs
  have h2 := hv.2 xs hxs
  have h3 := complete_square (gradient F x + v) (xs - x) hσ
  rw [inner_add_left] at h3
  linarith

/-- (E-grow): E(x) − E* ≥ (σ/2)‖x − x*‖² on dom g (g convex). -/
theorem growth {F : Z → ℝ} {D : Set Z} {g : Z → ℝ} {σ : ℝ} (hC : ModC F σ) (hg : ModCD D g 0)
    {xs : Z} (hxs : xs ∈ D) (hmin : ∀ w ∈ D, F xs + g xs ≤ F w + g w) {x : Z} (hx : x ∈ D) :
    F xs + g xs + σ / 2 * ‖x - xs‖ ^ 2 ≤ F x + g x :=
  growth_of_minD (Ψ := fun y => F y + g y) (modCD_add hC hg) hxs hmin hx

/-- The distance from the growth bound: ‖x − x*‖ ≤ (2(E(x) − E*)/σ)^{1/2}. -/
theorem dist_of_growth {F : Z → ℝ} {D : Set Z} {g : Z → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hC : ModC F σ) (hg : ModCD D g 0) {xs : Z} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, F xs + g xs ≤ F w + g w) {x : Z} (hx : x ∈ D) :
    ‖x - xs‖ ≤ √(2 * ((F x + g x) - (F xs + g xs)) / σ) := by
  have h := growth hC hg hxs hmin hx
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ hσ]; linarith

/-- **Lemma H4.5(ii).** Under (i)'s hypotheses and g convex:
‖x − x*‖ ≤ (‖u‖ + (‖u‖² + 4σε)^{1/2})/(2σ). -/
theorem dist_bracket {F : Z → ℝ} {D : Set Z} {g : Z → ℝ} {σ : ℝ} (hF : Differentiable ℝ F)
    (hC : ModC F σ) (hσ : 0 < σ) (hg : ModCD D g 0) {xs : Z} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, F xs + g xs ≤ F w + g w) {x v : Z} {ε : ℝ} (hv : EpsSubgrad D g ε x v) :
    ‖x - xs‖ ≤ (‖gradient F x + v‖ + √(‖gradient F x + v‖ ^ 2 + 4 * σ * ε)) / (2 * σ) := by
  set u := gradient F x + v
  set t := ‖x - xs‖
  have h1 := strongSubgrad_of_modC hF hC x xs
  have h2 := hv.2 xs hxs
  have h3 := growth hC hg hxs hmin hv.1
  have hin : inner ℝ u (xs - x) = inner ℝ (gradient F x) (xs - x) + inner ℝ v (xs - x) := by
    rw [inner_add_left]
  have hcs : -(‖u‖ * ‖xs - x‖) ≤ inner ℝ u (xs - x) := neg_le_of_abs_le (abs_real_inner_le_norm _ _)
  rw [norm_sub_rev xs x] at hcs h1
  have key : σ * t ^ 2 - ‖u‖ * t - ε ≤ 0 := by nlinarith
  have hq : (2 * σ * t - ‖u‖) ^ 2 ≤ ‖u‖ ^ 2 + 4 * σ * ε := by nlinarith
  have := (le_abs_self _).trans (Real.abs_le_sqrt hq)
  rw [le_div_iff₀ (by positivity)]
  linarith

end Bracket

/-- **Lemma H4.5(iii), value equality instance** (d = 1, σ, ε, t > 0): F = (σ/2)x²,
g = (ε/t)|·|, x = t, v = 0: v ∈ ∂_ε g(t), x* = 0 minimises E, and
E(t) − ‖u‖²/(2σ) − ε = E*. -/
theorem bracket_value_sharp {σ ε t : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (ht : 0 < t) :
    EpsSubgrad univ (fun x : ℝ => ε / t * |x|) ε t 0 ∧
      (∀ w : ℝ, sqf σ (0 : ℝ) + ε / t * |(0 : ℝ)| ≤ sqf σ w + ε / t * |w|) ∧
      sqf σ t + ε / t * |t| - ‖gradient (sqf σ) t + 0‖ ^ 2 / (2 * σ) - ε
        = sqf σ (0 : ℝ) + ε / t * |(0 : ℝ)| := by
  have hg : gradient (sqf σ) t = σ * t := by rw [gradient_sqf]; rfl
  refine ⟨⟨mem_univ _, fun w _ => ?_⟩, fun w => ?_, ?_⟩
  · simp only [inner_zero_left, add_zero, abs_of_pos ht]
    have : ε / t * t = ε := by field_simp
    rw [this]; simp only [sub_self]; positivity
  · simp only [sqf, norm_zero, abs_zero, mul_zero, add_zero, Real.norm_eq_abs]
    nlinarith [mul_nonneg (div_pos hε ht).le (abs_nonneg w), sq_nonneg |w|]
  · rw [hg, add_zero]
    simp only [sqf, Real.norm_eq_abs, sq_abs, abs_zero, mul_zero, add_zero, abs_of_pos ht,
      ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    field_simp; ring

/-- **Lemma H4.5(iii), distance equality instance** (d = 1, σ, ε > 0): F = (σ/2)x²,
g = ι_{[0,∞)}, x = √(ε/σ), v = −√(σε): v ∈ ∂_ε g(x), u = 0, x* = 0 minimises E, and
‖x − x*‖ = (‖u‖ + √(‖u‖² + 4σε))/(2σ). -/
theorem bracket_dist_sharp {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    EpsSubgrad (Ici (0 : ℝ)) (fun _ => (0 : ℝ)) ε √(ε / σ) (-√(σ * ε)) ∧
      gradient (sqf σ) √(ε / σ) + -√(σ * ε) = 0 ∧
      (∀ w ∈ Ici (0 : ℝ), sqf σ (0 : ℝ) + 0 ≤ sqf σ w + 0) ∧
      ‖√(ε / σ) - 0‖ = (‖gradient (sqf σ) √(ε / σ) + -√(σ * ε)‖
        + √(‖gradient (sqf σ) √(ε / σ) + -√(σ * ε)‖ ^ 2 + 4 * σ * ε)) / (2 * σ) := by
  have hprod : √(σ * ε) = σ * √(ε / σ) := by
    rw [show σ * ε = σ ^ 2 * (ε / σ) by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hσ.le]
  have hu : gradient (sqf σ) √(ε / σ) + -√(σ * ε) = 0 := by
    rw [gradient_sqf, hprod]; simp [smul_eq_mul]
  refine ⟨⟨Real.sqrt_nonneg _, fun w hw => ?_⟩, hu, fun w _ => ?_, ?_⟩
  · simp only [Set.mem_Ici] at hw
    have hs : √(σ * ε) * √(ε / σ) = ε := by
      rw [← Real.sqrt_mul (by positivity), show σ * ε * (ε / σ) = ε ^ 2 by field_simp,
        Real.sqrt_sq hε.le]
    rw [real_inner_eq_re_inner, RCLike.inner_apply, conj_trivial, RCLike.re_to_real]
    nlinarith [Real.sqrt_nonneg (σ * ε)]
  · simp only [sqf, norm_zero, add_zero]; nlinarith [sq_nonneg ‖w‖]
  · rw [hu, norm_zero, sub_zero, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [show (0 : ℝ) + √((0 : ℝ) ^ 2 + 4 * σ * ε) = 2 * √(σ * ε) by
      rw [zero_add, show (0 : ℝ) ^ 2 + 4 * σ * ε = 2 ^ 2 * (σ * ε) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by norm_num)], hprod]
    field_simp

/-- ρ := Λ²/(Λ² + σ). -/
noncomputable def rho (Λ σ : ℝ) : ℝ := Λ ^ 2 / (Λ ^ 2 + σ)

/-- c_θ := (1 + θ)Λ²/σ. -/
noncomputable def cth (θ Λ σ : ℝ) : ℝ := (1 + θ) * Λ ^ 2 / σ

/-- ρ_θ := c_θ/(1 + c_θ). -/
noncomputable def rhoth (θ Λ σ : ℝ) : ℝ := cth θ Λ σ / (1 + cth θ Λ σ)

lemma rho_mem {Λ σ : ℝ} (hσ : 0 < σ) : 0 ≤ rho Λ σ ∧ rho Λ σ < 1 := by
  unfold rho
  have h : 0 < Λ ^ 2 + σ := by positivity
  exact ⟨div_nonneg (sq_nonneg _) h.le, (div_lt_one h).2 (by linarith)⟩

lemma cth_nonneg {θ Λ σ : ℝ} (hθ : 0 < θ) (hσ : 0 < σ) : 0 ≤ cth θ Λ σ := by
  unfold cth; positivity

lemma rhoth_mem {θ Λ σ : ℝ} (hθ : 0 < θ) (hσ : 0 < σ) : 0 ≤ rhoth θ Λ σ ∧ rhoth θ Λ σ < 1 := by
  have hc := cth_nonneg (Λ := Λ) hθ hσ
  unfold rhoth
  exact ⟨div_nonneg hc (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

lemma one_sub_rhoth {θ Λ σ : ℝ} (hθ : 0 < θ) (hσ : 0 < σ) :
    1 - rhoth θ Λ σ = 1 / (1 + cth θ Λ σ) := by
  have hc := cth_nonneg (Λ := Λ) hθ hσ
  unfold rhoth; field_simp; ring

/-- Remark H4.7(i): ρ_θ → ρ as θ → 0⁺. -/
lemma rhoth_tendsto {Λ σ : ℝ} (hσ : 0 < σ) :
    Tendsto (fun θ => rhoth θ Λ σ) (𝓝[>] 0) (𝓝 (rho Λ σ)) := by
  have hc : Tendsto (fun θ => cth θ Λ σ) (𝓝[>] 0) (𝓝 (Λ ^ 2 / σ)) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    have : Tendsto (fun θ : ℝ => (1 + θ) * Λ ^ 2 / σ) (𝓝 0) (𝓝 ((1 + 0) * Λ ^ 2 / σ)) := by
      apply Tendsto.div_const; apply Tendsto.mul_const
      exact tendsto_const_nhds.add tendsto_id
    simpa [cth] using this
  have hpos : (1 + Λ ^ 2 / σ) ≠ 0 := by positivity
  have := hc.div (tendsto_const_nhds.add hc) hpos
  have e : Λ ^ 2 / σ / (1 + Λ ^ 2 / σ) = rho Λ σ := by
    have : Λ ^ 2 + σ ≠ 0 := by positivity
    unfold rho; field_simp; ring
  rw [e] at this
  exact this

/-! ## Scalar error accumulation (Theorem H4.7(c)) -/

/-- Unrolled recursion a_{k+1} ≤ r a_k + (1 − r)B_k:
a_k ≤ r^k a₀ + (1 − r) Σ_{i<k} r^{k−1−i} B_i. -/
lemma accum {a B : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (h : ∀ k, a (k + 1) ≤ r * a k + (1 - r) * B k)
    (k : ℕ) : a k ≤ r ^ k * a 0 + (1 - r) * ∑ i ∈ range k, r ^ (k - 1 - i) * B i := by
  have := unroll (b := fun k => (1 - r) * B k) hr0 h k
  rw [mul_sum]
  refine this.trans (le_of_eq ?_)
  congr 1
  exact sum_congr rfl fun i _ => by ring

lemma geom_sum_rev {r : ℝ} (hr1 : r < 1) (k : ℕ) :
    (1 - r) * ∑ i ∈ range k, r ^ (k - 1 - i) = 1 - r ^ k := by
  rw [sum_range_reflect (fun j => r ^ j) k, geom_sum_eq hr1.ne]
  field_simp [show r - 1 ≠ 0 by linarith]
  ring

/-- (c1) constant bound B_i ≤ B̄ (i < k): a_k ≤ r^k a₀ + (1 − r^k)B̄. -/
lemma accum_const {a B : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, a (k + 1) ≤ r * a k + (1 - r) * B k) {k : ℕ} {Bbar : ℝ}
    (hB : ∀ i < k, B i ≤ Bbar) : a k ≤ r ^ k * a 0 + (1 - r ^ k) * Bbar := by
  have h1 := accum hr0 h k
  have hs : ∑ i ∈ range k, r ^ (k - 1 - i) * B i ≤ ∑ i ∈ range k, r ^ (k - 1 - i) * Bbar :=
    sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hB i (mem_range.1 hi)) (pow_nonneg hr0 _)
  have h2 : (1 - r) * ∑ i ∈ range k, r ^ (k - 1 - i) * Bbar = (1 - r ^ k) * Bbar := by
    rw [← sum_mul, ← mul_assoc, geom_sum_rev hr1]
  have h3 := mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 1 - r)
  linarith

/-- (c2) geometric bound B_i ≤ B̄₀qⁱ, q ∈ [0, 1), q ≠ r (B ≥ 0, a₀ ≥ 0):
a_k ≤ max{r, q}^k (a₀ + (1 − r)B̄₀/|r − q|). -/
lemma accum_geom {a B : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, a (k + 1) ≤ r * a k + (1 - r) * B k) (ha0 : 0 ≤ a 0) (hBn : ∀ i, 0 ≤ B i)
    {B0 q : ℝ} (hq0 : 0 ≤ q) (hne : q ≠ r) (hB : ∀ i, B i ≤ B0 * q ^ i) (k : ℕ) :
    a k ≤ max r q ^ k * (a 0 + (1 - r) * B0 / |r - q|) := by
  have h1 := accum hr0 h k
  have hB0 : 0 ≤ B0 := by have := hB 0; have := hBn 0; simp at *; linarith
  have hs : ∑ i ∈ range k, r ^ (k - 1 - i) * B i ≤ B0 * sk r q k := by
    rw [← sum_eq_sk, mul_sum]
    exact sum_le_sum fun i _ => by
      have := mul_le_mul_of_nonneg_left (hB i) (pow_nonneg hr0 (k - 1 - i)); linarith
  set M := max r q
  have hrM : r ^ k ≤ M ^ k := pow_le_pow_left₀ hr0 (le_max_left _ _) k
  have hqM : q ^ k ≤ M ^ k := pow_le_pow_left₀ hq0 (le_max_right _ _) k
  have hab : |r ^ k - q ^ k| ≤ M ^ k := by
    rw [abs_sub_le_iff]; constructor <;> nlinarith [pow_nonneg hr0 k, pow_nonneg hq0 k]
  have hpos : 0 < |r - q| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  have hskle : sk r q k ≤ M ^ k / |r - q| := by
    unfold sk; rw [if_neg hne]
    calc (r ^ k - q ^ k) / (r - q) ≤ |(r ^ k - q ^ k) / (r - q)| := le_abs_self _
      _ = |r ^ k - q ^ k| / |r - q| := abs_div _ _
      _ ≤ M ^ k / |r - q| := div_le_div_of_nonneg_right hab hpos.le
  have h1r : 0 ≤ 1 - r := by linarith
  calc a k ≤ r ^ k * a 0 + (1 - r) * ∑ i ∈ range k, r ^ (k - 1 - i) * B i := h1
    _ ≤ M ^ k * a 0 + (1 - r) * (B0 * (M ^ k / |r - q|)) := by
        gcongr
        exact hs.trans (mul_le_mul_of_nonneg_left hskle hB0)
    _ = M ^ k * (a 0 + (1 - r) * B0 / |r - q|) := by ring

/-- (c3) B_k → 0 (B ≥ 0, a ≥ 0) ⇒ a_k → 0. -/
lemma accum_tendsto {a B : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, a (k + 1) ≤ r * a k + (1 - r) * B k) (ha : ∀ k, 0 ≤ a k) (hBn : ∀ k, 0 ≤ B k)
    (hB : Tendsto B atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  rw [tendsto_order]
  refine ⟨fun a' ha' => Eventually.of_forall fun k => ha'.trans_le (ha k), fun η hη => ?_⟩
  have hδ : 0 < η / 4 := by positivity
  have hev := (tendsto_order.1 hB).2 (η / 4) hδ
  have hb := eventual_bound (b := fun k => (1 - r) * B k) hr0 hr1
    (fun k => mul_nonneg (by linarith) (hBn k)) h
    (hev.mono fun k hk => mul_le_mul_of_nonneg_left hk.le (by linarith : (0 : ℝ) ≤ 1 - r)) hδ
  filter_upwards [hb] with k hk
  have : (1 - r) * (η / 4) / (1 - r) = η / 4 := by field_simp [show 1 - r ≠ 0 by linarith]
  rw [this] at hk
  linarith

/-- (c3) in general: limsup a_k ≤ limsup B_k (B bounded above, a ≥ 0, B ≥ 0). -/
lemma accum_limsup {a B : ℕ → ℝ} {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ k, a (k + 1) ≤ r * a k + (1 - r) * B k) (ha : ∀ k, 0 ≤ a k) (hBn : ∀ k, 0 ≤ B k)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop B) : limsup a atTop ≤ limsup B atTop := by
  set Lb := limsup B atTop
  apply le_of_forall_pos_le_add
  intro δ hδ
  have hev : ∀ᶠ k in atTop, B k ≤ Lb + δ / 2 :=
    (eventually_lt_of_limsup_lt (lt_add_of_pos_right Lb (by positivity)) hbdd).mono
      fun k hk => hk.le
  have hb := eventual_bound (b := fun k => (1 - r) * B k) hr0 hr1
    (fun k => mul_nonneg (by linarith) (hBn k)) h
    (hev.mono fun k hk => mul_le_mul_of_nonneg_left hk (by linarith : (0 : ℝ) ≤ 1 - r))
    (by positivity : (0 : ℝ) < δ / 2)
  have : (1 - r) * (Lb + δ / 2) / (1 - r) + δ / 2 = Lb + δ := by
    field_simp [show 1 - r ≠ 0 by linarith]; ring
  rw [this] at hb
  exact limsup_le_of_le (isCoboundedUnder_le_of_le atTop ha) hb

/-! ## The stitched run (Definition H4.0), Lemmas H4.2 (block setting), H4.4, H4.6 -/

section Run

variable {m : ℕ} {X : Fin m → Type*} [∀ l, NormedAddCommGroup (X l)]
  [∀ l, InnerProductSpace ℝ (X l)] [∀ l, CompleteSpace (X l)]

/-- Φ_{x,l} := φ_{x,l} + g_l (the block subproblem). -/
noncomputable def PhiB (F : PiLp 2 X → ℝ) (g : ∀ l, X l → ℝ) (x : PiLp 2 X) (l : Fin m)
    (y : X l) : ℝ := slice F x l y + g l y

/-- **Definition H4.0(a).** A block report (z, v, ε) for block l: ε ≥ 0 and v ∈ ∂_ε g_l(z)
(so z ∈ dom g_l). -/
def Report (D : ∀ l, Set (X l)) (g : ∀ l, X l → ℝ) (l : Fin m) (z v : X l) (ε : ℝ) : Prop :=
  0 ≤ ε ∧ EpsSubgrad (D l) (g l) ε z v

/-- **Lemma H4.2** (one block step, block setting). SD5 at block l, x_l ∈ dom g_l, (z, v, ε)
a block report, x' := x + U_l(z − x_l), h := z − x_l, η := ‖∇_l F(x') + v‖,
γ := η²/(2τ_l) + ε, Δ := E(x) − E(x'). Then
(a) E(x') ≤ E(x + U_l(y − x_l)) + γ for every y ∈ dom g_l;
(b) Δ ≥ (τ_l/2)‖h‖² − η‖h‖ − ε;
(c) Δ + γ ≥ 0 and √τ_l ‖h‖ ≤ √(2(Δ + γ)) + √(2γ). -/
theorem lemma_H4_2 {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ}
    {τ : Fin m → ℝ} (hF : Differentiable ℝ F) (hS : SliceMod F τ) (hτ : ∀ l, 0 < τ l)
    {x : PiLp 2 X} {l : Fin m} {z v : X l} {ε : ℝ} (hrep : Report D g l z v ε)
    (hxl : x l ∈ D l) :
    (∀ y ∈ D l, Efun F g (upd x l z) ≤ Efun F g (upd x l y)
        + (‖gradient F (upd x l z) l + v‖ ^ 2 / (2 * τ l) + ε)) ∧
    τ l / 2 * ‖z - x l‖ ^ 2 - ‖gradient F (upd x l z) l + v‖ * ‖z - x l‖ - ε
        ≤ Efun F g x - Efun F g (upd x l z) ∧
    0 ≤ Efun F g x - Efun F g (upd x l z)
        + (‖gradient F (upd x l z) l + v‖ ^ 2 / (2 * τ l) + ε) ∧
    √(τ l) * ‖z - x l‖ ≤ √(2 * (Efun F g x - Efun F g (upd x l z)
        + (‖gradient F (upd x l z) l + v‖ ^ 2 / (2 * τ l) + ε)))
        + √(2 * (‖gradient F (upd x l z) l + v‖ ^ 2 / (2 * τ l) + ε)) := by
  obtain ⟨hε, hv⟩ := hrep
  have hφ := differentiable_slice hF x l
  have hC := hS x l
  rw [← gradient_slice hF x l z]
  have hΔ : Efun F g x - Efun F g (upd x l z)
      = (slice F x l (x l) + g l (x l)) - (slice F x l z + g l z) := by
    rw [Efun_upd, Efun_eq F g x l]; ring
  rw [hΔ]
  refine ⟨fun y hy => ?_, ?_, block_move (hτ l) hφ hC hε hv hxl⟩
  · rw [Efun_upd, Efun_upd]
    have := block_gap (hτ l) hφ hC hv hy
    linarith
  · exact block_descent hφ hC hv hxl

/-- **Lemma H4.2(a), minimiser form, block setting.** If Φ_{x,l} has a minimiser y* on
dom g_l (classical (EX), a hypothesis), it is unique and Φ(z) − Φ(y*) ≤ γ. -/
theorem lemma_H4_2_min {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ}
    {τ : Fin m → ℝ} (hF : Differentiable ℝ F) (hS : SliceMod F τ) (hτ : ∀ l, 0 < τ l)
    (hg : ∀ l, ModCD (D l) (g l) 0) {x : PiLp 2 X} {l : Fin m} {z v : X l} {ε : ℝ}
    (hrep : Report D g l z v ε) {ys : X l} (hys : ys ∈ D l)
    (hmin : ∀ w ∈ D l, PhiB F g x l ys ≤ PhiB F g x l w) :
    (∀ y ∈ D l, (∀ w ∈ D l, PhiB F g x l y ≤ PhiB F g x l w) → y = ys) ∧
      PhiB F g x l z - PhiB F g x l ys ≤ ‖gradient F (upd x l z) l + v‖ ^ 2 / (2 * τ l) + ε := by
  rw [← gradient_slice hF x l z]
  exact block_min (hτ l) (differentiable_slice hF x l) (hS x l) (hg l) hrep.2 hys hmin

/-- **Definition H4.0(b).** A stitched run (cyclic Gauss–Seidel order): iterates
x k i = x^{k,i} (i = 0, …, m), block reports (z_{k,l}, v_{k,l}, ε_{k,l}) returned by block l's
own solver at x^{k,l}, x^{k,l+1} = x^{k,l} + U_l(z_{k,l} − x^{k,l}_l), x^{k+1,0} = x^{k,m};
x^{0,0} ∈ dom g. (Blocks are 0-indexed: step l of sweep k produces x k (l + 1).) -/
structure Run (D : ∀ l, Set (X l)) (g : ∀ l, X l → ℝ) where
  x : ℕ → ℕ → PiLp 2 X
  z : ℕ → (l : Fin m) → X l
  v : ℕ → (l : Fin m) → X l
  ε : ℕ → Fin m → ℝ
  start : x 0 0 ∈ domG D
  step : ∀ k (l : Fin m), x k (l.val + 1) = upd (x k l.val) l (z k l)
  next : ∀ k, x (k + 1) 0 = x k m
  report : ∀ k l, Report D g l (z k l) (v k l) (ε k l)

/-- The standing data SD2–SD6 (SD1 is the type of the blocks): F ∈ C¹ (differentiable),
C(F, σ) with σ > 0 (SD4), g_l convex on dom g_l (SD3; lower semicontinuity is never used),
slice moduli τ_l > 0 (SD5), cross constants L_{jl} ≥ 0 (SD6). -/
structure SD (F : PiLp 2 X → ℝ) (D : ∀ l, Set (X l)) (g : ∀ l, X l → ℝ) (σ : ℝ)
    (τ : Fin m → ℝ) (L : Fin m → Fin m → ℝ) : Prop where
  diff : Differentiable ℝ F
  modF : ModC F σ
  sigma_pos : 0 < σ
  convex_g : ∀ l, ModCD (D l) (g l) 0
  slice : SliceMod F τ
  tau_pos : ∀ l, 0 < τ l
  cross : CrossConst F L
  L_nonneg : ∀ j l, 0 ≤ L j l

/-- x* minimises E = F + g on dom g ((E-min); existence is classical, B&C Cor. 11.17, and
taken as a hypothesis). -/
def IsMinE (F : PiLp 2 X → ℝ) (D : ∀ l, Set (X l)) (g : ∀ l, X l → ℝ) (xs : PiLp 2 X) : Prop :=
  xs ∈ domG D ∧ ∀ w ∈ domG D, Efun F g xs ≤ Efun F g w

/-- g = Σ_l g_l(x_l) is convex on dom g = Π dom g_l. -/
lemma modCD_gsum {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} (hg : ∀ l, ModCD (D l) (g l) 0) :
    ModCD (domG D) (gsum g) 0 := by
  have hc : ∀ l, ConvexOn ℝ (D l) (g l) := fun l => by
    have := hg l; unfold ModCD at this; simpa using this
  have hD : Convex ℝ (domG D) := fun x hx y hy a b ha hb hab l =>
    (hc l).1 (hx l) (hy l) ha hb hab
  unfold ModCD
  simp only [zero_div, zero_mul, sub_zero]
  refine ⟨hD, fun x hx y hy a b ha hb hab => ?_⟩
  unfold gsum
  simp only [smul_eq_mul, mul_sum, ← sum_add_distrib]
  exact sum_le_sum fun l _ => (hc l).2 (hx l) (hy l) ha hb hab


namespace Run

variable {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} (R : Run D g)

/-- Def. H4.0(b) note: x^{k,i}_l = x^k_l for i ≤ l (block l not yet updated in sweep k). -/
lemma block_fixed (k : ℕ) (l : Fin m) : ∀ i, i ≤ l.val → R.x k i l = R.x k 0 l := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    have hi' : i < m := by omega
    have := R.step k ⟨i, hi'⟩
    simp only at this
    rw [this, upd_ne _ (fun h => by have := congrArg Fin.val h; simp at this; omega)]
    exact ih (by omega)

/-- After step l, block l keeps the value z_{k,l} for the rest of the sweep. -/
lemma block_final (k : ℕ) (l : Fin m) : ∀ i, l.val < i → i ≤ m → R.x k i l = R.z k l := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro hi him
    have hi' : i < m := by omega
    rw [R.step k ⟨i, hi'⟩]
    by_cases h : l.val = i
    · have hl : l = ⟨i, hi'⟩ := Fin.ext h
      subst hl
      exact upd_same _ _ _
    · rw [upd_ne _ (fun h' => h (by rw [h']))]
      exact ih (by omega) (by omega)

/-- The block of x^{k+1} = x^{k,m}: x^{k+1}_l = z_{k,l}. -/
lemma next_block (k : ℕ) (l : Fin m) : R.x (k + 1) 0 l = R.z k l := by
  rw [R.next]; exact R.block_final k l m l.isLt le_rfl

/-- Def. H4.0(d): every x^{k,i} (i ≤ m) lies in dom g. -/
lemma mem (k : ℕ) : ∀ i, i ≤ m → R.x k i ∈ domG D := by
  induction k with
  | zero =>
    intro i
    induction i with
    | zero => intro _; exact R.start
    | succ i ih =>
      intro hi
      rw [R.step 0 ⟨i, by omega⟩]
      exact upd_mem (ih (by omega)) (R.report 0 _).2.1
  | succ k ihk =>
    intro i
    induction i with
    | zero => intro _; rw [R.next]; exact ihk m le_rfl
    | succ i ih =>
      intro hi
      rw [R.step (k + 1) ⟨i, by omega⟩]
      exact upd_mem (ih (by omega)) (R.report (k + 1) _).2.1

/-- Step l of sweep k as a move: x^{k,l+1} = x^{k,l} + U_l h_{k,l}, h_{k,l} := z_{k,l} − x^k_l. -/
lemma step_move (k : ℕ) (l : Fin m) :
    R.x k (l.val + 1) = R.x k l.val + U l (R.z k l - R.x k 0 l) := by
  rw [R.step, upd, R.block_fixed k l l.val le_rfl]

/-- h_{k,l} := z_{k,l} − x^k_l. -/
noncomputable def hm (k : ℕ) (l : Fin m) : X l := R.z k l - R.x k 0 l

/-- η_{k,l} := ‖∇_l F(x^{k,l+1}) + v_{k,l}‖ (computed by the stitcher). -/
noncomputable def eta (F : PiLp 2 X → ℝ) (k : ℕ) (l : Fin m) : ℝ :=
  ‖gradient F (R.x k (l.val + 1)) l + R.v k l‖

/-- γ_{k,l} := η_{k,l}²/(2τ_l) + ε_{k,l}. -/
noncomputable def gam (F : PiLp 2 X → ℝ) (τ : Fin m → ℝ) (k : ℕ) (l : Fin m) : ℝ :=
  R.eta F k l ^ 2 / (2 * τ l) + R.ε k l

/-- Γ_k := Σ_l γ_{k,l}. -/
noncomputable def Gam (F : PiLp 2 X → ℝ) (τ : Fin m → ℝ) (k : ℕ) : ℝ := ∑ l, R.gam F τ k l

/-- ε_k := Σ_l ε_{k,l}. -/
noncomputable def epsk (k : ℕ) : ℝ := ∑ l, R.ε k l

/-- ‖η_k‖ := (Σ_l η_{k,l}²)^{1/2}. -/
noncomputable def etan (F : PiLp 2 X → ℝ) (k : ℕ) : ℝ := √(∑ l, R.eta F k l ^ 2)

/-- D_k := (Σ_l τ_l‖h_{k,l}‖²)^{1/2} (analysis only). -/
noncomputable def Dk (τ : Fin m → ℝ) (k : ℕ) : ℝ := √(∑ l, τ l * ‖R.hm k l‖ ^ 2)

/-- Q_k := ‖η_k‖ + Λ(2Γ_k)^{1/2}. -/
noncomputable def Qk (F : PiLp 2 X → ℝ) (τ : Fin m → ℝ) (Λ : ℝ) (k : ℕ) : ℝ :=
  R.etan F k + Λ * √(2 * R.Gam F τ k)

/-- B_k(θ) := c_θΓ_k + (1 + 1/θ)Q_k²/(2σ) + ε_k. -/
noncomputable def Bk (F : PiLp 2 X → ℝ) (τ : Fin m → ℝ) (Λ σ θ : ℝ) (k : ℕ) : ℝ :=
  cth θ Λ σ * R.Gam F τ k + (1 + 1 / θ) * R.Qk F τ Λ k ^ 2 / (2 * σ) + R.epsk k

/-- a_k := E(x^k) − E*. -/
noncomputable def ak (F : PiLp 2 X → ℝ) (xs : PiLp 2 X) (k : ℕ) : ℝ :=
  Efun F g (R.x k 0) - Efun F g xs

/-- v_k := (v_{k,1}, …, v_{k,m}). -/
noncomputable def vk (k : ℕ) : PiLp 2 X := WithLp.toLp 2 (fun l => R.v k l)

/-- u_k := ∇F(x^{k+1}) + v_k. -/
noncomputable def uk (F : PiLp 2 X → ℝ) (k : ℕ) : PiLp 2 X := gradient F (R.x (k + 1) 0) + R.vk k

lemma eta_nonneg (F : PiLp 2 X → ℝ) (k : ℕ) (l : Fin m) : 0 ≤ R.eta F k l := norm_nonneg _

lemma gam_nonneg (F : PiLp 2 X → ℝ) {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) (k : ℕ) (l : Fin m) :
    0 ≤ R.gam F τ k l := by
  have := (R.report k l).1
  have := hτ l
  unfold gam; positivity

lemma Gam_nonneg (F : PiLp 2 X → ℝ) {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) (k : ℕ) :
    0 ≤ R.Gam F τ k := sum_nonneg fun l _ => R.gam_nonneg F hτ k l

lemma epsk_nonneg (k : ℕ) : 0 ≤ R.epsk k := sum_nonneg fun l _ => (R.report k l).1

lemma Qk_nonneg (F : PiLp 2 X → ℝ) (τ : Fin m → ℝ) {Λ : ℝ} (hΛ : 0 ≤ Λ) (k : ℕ) :
    0 ≤ R.Qk F τ Λ k := by
  unfold Qk etan; positivity

lemma Bk_nonneg (F : PiLp 2 X → ℝ) {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) {Λ σ θ : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (k : ℕ) : 0 ≤ R.Bk F τ Λ σ θ k := by
  have h1 := cth_nonneg (Λ := Λ) hθ hσ
  have h2 := R.Gam_nonneg F hτ k
  have h3 := R.epsk_nonneg k
  unfold Bk; positivity

/-- Lemma H4.2 at step l of sweep k (x := x^{k,l}). -/
lemma step_H4_2 {F : PiLp 2 X → ℝ} {τ : Fin m → ℝ} (hF : Differentiable ℝ F)
    (hS : SliceMod F τ) (hτ : ∀ l, 0 < τ l) (k : ℕ) (l : Fin m) :
    τ l / 2 * ‖R.hm k l‖ ^ 2 - R.eta F k l * ‖R.hm k l‖ - R.ε k l
        ≤ Efun F g (R.x k l.val) - Efun F g (R.x k (l.val + 1)) ∧
    0 ≤ Efun F g (R.x k l.val) - Efun F g (R.x k (l.val + 1)) + R.gam F τ k l ∧
    √(τ l) * ‖R.hm k l‖ ≤ √(2 * (Efun F g (R.x k l.val) - Efun F g (R.x k (l.val + 1))
        + R.gam F τ k l)) + √(2 * R.gam F τ k l) := by
  have hxl : R.x k l.val l ∈ D l := R.mem k l.val l.isLt.le l
  obtain ⟨-, h2, h3, h4⟩ := lemma_H4_2 hF hS hτ (R.report k l) hxl
  have e1 : upd (R.x k l.val) l (R.z k l) = R.x k (l.val + 1) := (R.step k l).symm
  have e2 : R.z k l - R.x k l.val l = R.hm k l := by rw [hm, R.block_fixed k l l.val le_rfl]
  rw [e1] at h2 h3 h4
  rw [e2] at h2 h4
  exact ⟨h2, h3, h4⟩

/-- Telescoping of a sweep: Σ_l (f(l) − f(l+1)) = f(0) − f(m). -/
lemma sum_fin_telescope (f : ℕ → ℝ) : ∑ l : Fin m, (f l.val - f (l.val + 1)) = f 0 - f m := by
  rw [Fin.sum_univ_eq_sum_range (fun i => f i - f (i + 1)) m, sum_range_sub']

/-! ### Lemma H4.4 (separable assembly at the end of a sweep) -/

/-- **Separable assembly** (Lemma H4.4(a), Proposition H4.9(a)): v_l ∈ ∂_{ε_l} g_l(x̂_l) for
every l ⇒ (v_l)_l ∈ ∂_{Σε_l} g(x̂). -/
theorem sep_assembly {xh : PiLp 2 X} {v : ∀ l, X l} {ε : Fin m → ℝ}
    (h : ∀ l, EpsSubgrad (D l) (g l) (ε l) (xh l) (v l)) :
    EpsSubgrad (domG D) (gsum g) (∑ l, ε l) xh (WithLp.toLp 2 v) := by
  refine ⟨fun l => (h l).1, fun w hw => ?_⟩
  unfold gsum
  rw [PiLp.inner_apply]
  have : ∀ l, g l (xh l) + inner ℝ (v l) (w l - xh l) - ε l ≤ g l (w l) :=
    fun l => (h l).2 (w l) (hw l)
  have hs := sum_le_sum fun l (_ : l ∈ Finset.univ) => this l
  simp only [sum_sub_distrib, sum_add_distrib] at hs
  simpa using hs

/-- **Lemma H4.4(a).** v_k ∈ ∂_{ε_k} g(x^{k+1}). -/
theorem H4_4_a (k : ℕ) : EpsSubgrad (domG D) (gsum g) (R.epsk k) (R.x (k + 1) 0) (R.vk k) := by
  apply sep_assembly
  intro l
  rw [R.next_block]
  exact (R.report k l).2

/-- Partial telescoping of the block-j gradient over the later steps of the sweep. -/
lemma tele_bound {F : PiLp 2 X → ℝ} {L : Fin m → Fin m → ℝ} (hL : CrossConst F L)
    (hL0 : ∀ j l, 0 ≤ L j l) (k : ℕ) (j : Fin m) :
    ∀ n, j.val + 1 ≤ n → n ≤ m →
      ‖gradient F (R.x k n) j - gradient F (R.x k (j.val + 1)) j‖
        ≤ ∑ l : Fin m, if j < l ∧ l.val < n then L j l * ‖R.hm k l‖ else 0 := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro _
    rw [sub_self, norm_zero]
    exact sum_nonneg fun l _ => by
      split_ifs <;> [exact mul_nonneg (hL0 j l) (norm_nonneg _); exact le_rfl]
  | succ n hn ih =>
    intro hnm
    set l0 : Fin m := ⟨n, by omega⟩
    have hjl0 : j < l0 := by
      rw [Fin.lt_def]; simp [l0]; omega
    have hstep : R.x k (n + 1) = R.x k n + U l0 (R.hm k l0) := R.step_move k l0
    have h1 : ‖gradient F (R.x k (n + 1)) j - gradient F (R.x k n) j‖ ≤ L j l0 * ‖R.hm k l0‖ := by
      rw [hstep]; exact hL _ l0 j (ne_of_lt hjl0) _
    have hsum : (∑ l : Fin m, if j < l ∧ l.val < n + 1 then L j l * ‖R.hm k l‖ else 0)
        = (∑ l : Fin m, if j < l ∧ l.val < n then L j l * ‖R.hm k l‖ else 0)
          + L j l0 * ‖R.hm k l0‖ := by
      have : ∀ l : Fin m, (if j < l ∧ l.val < n + 1 then L j l * ‖R.hm k l‖ else 0)
          = (if j < l ∧ l.val < n then L j l * ‖R.hm k l‖ else 0)
            + (if l = l0 then L j l * ‖R.hm k l‖ else 0) := by
        intro l
        by_cases hl : l = l0
        · subst hl
          simp only [hjl0, true_and, if_true]
          simp [l0]
        · have hlv : l.val ≠ n := fun h => hl (Fin.ext h)
          by_cases hc : j < l ∧ l.val < n
          · rw [if_pos ⟨hc.1, by omega⟩, if_pos hc, if_neg hl, add_zero]
          · have : ¬ (j < l ∧ l.val < n + 1) := fun h' => hc ⟨h'.1, by omega⟩
            rw [if_neg this, if_neg hc, if_neg hl, add_zero]
      rw [sum_congr rfl fun l _ => this l, sum_add_distrib, sum_ite_eq']
      simp
    rw [hsum]
    calc ‖gradient F (R.x k (n + 1)) j - gradient F (R.x k (j.val + 1)) j‖
          ≤ ‖gradient F (R.x k (n + 1)) j - gradient F (R.x k n) j‖
            + ‖gradient F (R.x k n) j - gradient F (R.x k (j.val + 1)) j‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := by linarith [ih (by omega)]

/-- **Lemma H4.4(b).** Block j of u_k is e_{k,j} + ∇_jF(x^{k+1}) − ∇_jF(x^{k,j}) and
‖u_{k,j}‖ ≤ η_{k,j} + Σ_{l>j} L_{jl}‖h_{k,l}‖. -/
theorem H4_4_b {F : PiLp 2 X → ℝ} {L : Fin m → Fin m → ℝ} (hL : CrossConst F L)
    (hL0 : ∀ j l, 0 ≤ L j l) (k : ℕ) (j : Fin m) :
    R.uk F k j = (gradient F (R.x k (j.val + 1)) j + R.v k j)
        + (gradient F (R.x (k + 1) 0) j - gradient F (R.x k (j.val + 1)) j) ∧
    ‖R.uk F k j‖ ≤ R.eta F k j + ∑ l : Fin m, if j < l then L j l * ‖R.hm k l‖ else 0 := by
  have hid : R.uk F k j = (gradient F (R.x k (j.val + 1)) j + R.v k j)
      + (gradient F (R.x (k + 1) 0) j - gradient F (R.x k (j.val + 1)) j) := by
    change gradient F (R.x (k + 1) 0) j + R.v k j = _
    abel
  refine ⟨hid, ?_⟩
  have ht := R.tele_bound hL hL0 k j m (by omega) le_rfl
  rw [← R.next] at ht
  have hs : (∑ l : Fin m, if j < l ∧ l.val < m then L j l * ‖R.hm k l‖ else 0)
      = ∑ l : Fin m, if j < l then L j l * ‖R.hm k l‖ else 0 :=
    sum_congr rfl fun l _ => by simp [l.isLt]
  rw [hs] at ht
  rw [hid]
  exact (norm_add_le _ _).trans (by unfold eta; linarith)

/-- **Lemma H4.4(c).** ‖u_k‖ ≤ ‖η_k‖ + ΛD_k. -/
theorem H4_4_c {F : PiLp 2 X → ℝ} {L : Fin m → Fin m → ℝ} {τ : Fin m → ℝ}
    (hL : CrossConst F L) (hL0 : ∀ j l, 0 ≤ L j l) (hτ : ∀ l, 0 < τ l) (k : ℕ) :
    ‖R.uk F k‖ ≤ R.etan F k + Lam L τ * R.Dk τ k := by
  -- row bound: Σ_{l>j} L_{jl}‖h_l‖ ≤ c_j D_k
  have hrow : ∀ j : Fin m, (∑ l : Fin m, if j < l then L j l * ‖R.hm k l‖ else 0)
      ≤ √(cj2 L τ j) * R.Dk τ k := by
    intro j
    have e : ∀ l : Fin m, (if j < l then L j l * ‖R.hm k l‖ else 0)
        = (if j < l then L j l / √(τ l) else 0) * (√(τ l) * ‖R.hm k l‖) := by
      intro l
      split_ifs
      · have := Real.sqrt_pos.2 (hτ l); field_simp
      · simp
    rw [sum_congr rfl fun l _ => e l]
    refine (sum_mul_le_sqrt _ _ _).trans (le_of_eq ?_)
    congr 2
    · unfold cj2
      refine sum_congr rfl fun l _ => ?_
      split_ifs
      · rw [div_pow, Real.sq_sqrt (hτ l).le]
      · simp
    · refine sum_congr rfl fun l _ => ?_
      rw [mul_pow, Real.sq_sqrt (hτ l).le]
  have hj : ∀ j : Fin m, ‖R.uk F k j‖ ≤ R.eta F k j + √(cj2 L τ j) * R.Dk τ k :=
    fun j => (R.H4_4_b hL hL0 k j).2.trans (by linarith [hrow j])
  have hu : ‖R.uk F k‖ = √(∑ j, ‖R.uk F k j‖ ^ 2) := by
    rw [← Real.sqrt_sq (norm_nonneg _), PiLp.norm_sq_eq_of_L2]
  rw [hu]
  calc √(∑ j, ‖R.uk F k j‖ ^ 2)
        ≤ √(∑ j, (R.eta F k j + √(cj2 L τ j) * R.Dk τ k) ^ 2) :=
          sqrt_sum_sq_mono _ (fun j _ => norm_nonneg _) (fun j _ => hj j)
    _ ≤ √(∑ j, R.eta F k j ^ 2) + √(∑ j, (√(cj2 L τ j) * R.Dk τ k) ^ 2) :=
          sqrt_sum_add_sq_le _ _ _
    _ = R.etan F k + Lam L τ * R.Dk τ k := by
          congr 1
          have : ∑ j, (√(cj2 L τ j) * R.Dk τ k) ^ 2 = R.Dk τ k ^ 2 * Lam2 L τ := by
            rw [Lam2, mul_sum]
            exact sum_congr rfl fun j _ => by
              rw [mul_pow, Real.sq_sqrt (cj2_nonneg hτ j)]; ring
          rw [this, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by unfold Dk; positivity), Lam]
          ring

/-! ### Lemma H4.6 (one sweep) -/

/-- **Lemma H4.6.** Under SD, x* a minimiser of E:
(ii) E(x^{k,l+1}) ≤ E(x^{k,l}) − (τ_l/2)‖h_{k,l}‖² + η_{k,l}‖h_{k,l}‖ + ε_{k,l} for every l, and
E(x^{k+1}) ≤ E(x^k) + Γ_k; (i) a_k − a_{k+1} + Γ_k ≥ 0 and
a_{k+1} ≤ (Q_k + Λ(2(a_k − a_{k+1} + Γ_k))^{1/2})²/(2σ) + ε_k. -/
theorem H4_6 {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) (k : ℕ) :
    (∀ l : Fin m, Efun F g (R.x k (l.val + 1))
        ≤ Efun F g (R.x k l.val) - τ l / 2 * ‖R.hm k l‖ ^ 2 + R.eta F k l * ‖R.hm k l‖
          + R.ε k l) ∧
    Efun F g (R.x (k + 1) 0) ≤ Efun F g (R.x k 0) + R.Gam F τ k ∧
    0 ≤ R.ak F xs k - R.ak F xs (k + 1) + R.Gam F τ k ∧
    R.ak F xs (k + 1) ≤ (R.Qk F τ (Lam L τ) k
        + Lam L τ * √(2 * (R.ak F xs k - R.ak F xs (k + 1) + R.Gam F τ k))) ^ 2 / (2 * σ)
        + R.epsk k := by
  have hst := fun l => R.step_H4_2 hSD.diff hSD.slice hSD.tau_pos k l
  have hsum : ∑ l : Fin m, (Efun F g (R.x k l.val) - Efun F g (R.x k (l.val + 1))
      + R.gam F τ k l) = R.ak F xs k - R.ak F xs (k + 1) + R.Gam F τ k := by
    rw [sum_add_distrib, sum_fin_telescope (fun i => Efun F g (R.x k i)), Gam, ak, ak, R.next]
    ring
  have hfirst : 0 ≤ R.ak F xs k - R.ak F xs (k + 1) + R.Gam F τ k := by
    rw [← hsum]; exact sum_nonneg fun l _ => (hst l).2.1
  refine ⟨fun l => by linarith [(hst l).1], ?_, hfirst, ?_⟩
  · have : R.ak F xs k - R.ak F xs (k + 1) = Efun F g (R.x k 0) - Efun F g (R.x (k + 1) 0) := by
      unfold ak; ring
    linarith
  -- D_k ≤ √(2(a_k − a_{k+1} + Γ_k)) + √(2Γ_k)
  set S := R.ak F xs k - R.ak F xs (k + 1) + R.Gam F τ k
  have hτ := hSD.tau_pos
  have hD : R.Dk τ k ≤ √(2 * S) + √(2 * R.Gam F τ k) := by
    have e1 : R.Dk τ k = √(∑ l, (√(τ l) * ‖R.hm k l‖) ^ 2) := by
      unfold Dk; congr 1
      exact sum_congr rfl fun l _ => by rw [mul_pow, Real.sq_sqrt (hτ l).le]
    rw [e1]
    refine (sqrt_sum_sq_mono _ (fun l _ => by positivity) (fun l _ => (hst l).2.2)).trans
      ((sqrt_sum_add_sq_le _ _ _).trans (le_of_eq ?_))
    congr 2
    · rw [← hsum, mul_sum]
      exact sum_congr rfl fun l _ => Real.sq_sqrt (by linarith [(hst l).2.1])
    · rw [Gam, mul_sum]
      exact sum_congr rfl fun l _ =>
        Real.sq_sqrt (by have := R.gam_nonneg F hτ k l; linarith)
  -- ‖u_k‖ ≤ Q_k + Λ√(2S)
  have hΛ : 0 ≤ Lam L τ := Real.sqrt_nonneg _
  have hu : ‖R.uk F k‖ ≤ R.Qk F τ (Lam L τ) k + Lam L τ * √(2 * S) := by
    have := R.H4_4_c hSD.cross hSD.L_nonneg hτ k
    have h2 := mul_le_mul_of_nonneg_left hD hΛ
    unfold Qk
    nlinarith
  -- Lemma H4.5(i) at x^{k+1}
  have hval := (value_bracket (D := domG D) (g := gsum g) hSD.diff hSD.modF hSD.sigma_pos
    hxs.1 hxs.2 (R.H4_4_a k)).1
  have hak : R.ak F xs (k + 1) ≤ ‖R.uk F k‖ ^ 2 / (2 * σ) + R.epsk k := by
    unfold ak uk; unfold Efun at *; linarith
  have hsq : ‖R.uk F k‖ ^ 2 ≤ (R.Qk F τ (Lam L τ) k + Lam L τ * √(2 * S)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hu 2
  have := div_le_div_of_nonneg_right hsq (by linarith [hSD.sigma_pos] : (0 : ℝ) ≤ 2 * σ)
  linarith

/-! ### Theorem H4.7 (rate and error accumulation) -/

lemma ak_nonneg {F : PiLp 2 X → ℝ} {xs : PiLp 2 X} (hxs : IsMinE F D g xs) (k : ℕ) :
    0 ≤ R.ak F xs k := by
  unfold ak; linarith [hxs.2 _ (R.mem k 0 (Nat.zero_le _))]

/-- **Theorem H4.7(d), distance.** ‖x^k − x*‖ ≤ (2a_k/σ)^{1/2}. -/
theorem H4_7_d_dist {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) (k : ℕ) :
    ‖R.x k 0 - xs‖ ≤ √(2 * R.ak F xs k / σ) := by
  have := dist_of_growth (D := domG D) (g := gsum g) hSD.sigma_pos hSD.modF
    (modCD_gsum hSD.convex_g) hxs.1 hxs.2 (R.mem k 0 (Nat.zero_le _))
  simpa [ak, Efun, mul_div_assoc] using this

/-- **Theorem H4.7(a)** (exact block solves in sweep k): η_{k,l} = ε_{k,l} = 0 for all l ⇒
a_{k+1} ≤ ρa_k, ρ = Λ²/(Λ² + σ). -/
theorem H4_7_a {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {k : ℕ}
    (hex : ∀ l, R.eta F k l = 0 ∧ R.ε k l = 0) :
    R.ak F xs (k + 1) ≤ rho (Lam L τ) σ * R.ak F xs k := by
  obtain ⟨-, -, h1, h2⟩ := R.H4_6 hSD hxs k
  have hΓ : R.Gam F τ k = 0 := sum_eq_zero fun l _ => by
    unfold gam; rw [(hex l).1, (hex l).2]; ring
  have hε : R.epsk k = 0 := sum_eq_zero fun l _ => (hex l).2
  have hQ : R.Qk F τ (Lam L τ) k = 0 := by
    unfold Qk etan; rw [hΓ]; simp [(hex _).1]
  rw [hΓ, add_zero] at h1 h2
  rw [hQ, hε, zero_add, add_zero, mul_pow, Real.sq_sqrt (by linarith)] at h2
  have hσ := hSD.sigma_pos
  have hl : (Lam L τ ^ 2 + σ) * R.ak F xs (k + 1) ≤ Lam L τ ^ 2 * R.ak F xs k := by
    rw [le_div_iff₀ (by positivity)] at h2; nlinarith
  unfold rho
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Theorem H4.7(a), iterated.** If every sweep is exact: a_k ≤ ρ^k a₀ and
‖x^k − x*‖ ≤ ρ^{k/2}(2a₀/σ)^{1/2} (ρ^{k/2} = (√ρ)^k). -/
theorem H4_7_a_iter {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs)
    (hex : ∀ k l, R.eta F k l = 0 ∧ R.ε k l = 0) (k : ℕ) :
    R.ak F xs k ≤ rho (Lam L τ) σ ^ k * R.ak F xs 0 ∧
      ‖R.x k 0 - xs‖ ≤ √(rho (Lam L τ) σ) ^ k * √(2 * R.ak F xs 0 / σ) := by
  have hρ := rho_mem (Λ := Lam L τ) hSD.sigma_pos
  have hrec : ∀ k, R.ak F xs (k + 1) ≤ rho (Lam L τ) σ * R.ak F xs k + 0 :=
    fun k => by rw [add_zero]; exact R.H4_7_a hSD hxs (hex k)
  have h1 : R.ak F xs k ≤ rho (Lam L τ) σ ^ k * R.ak F xs 0 := by
    have := unroll (b := fun _ => 0) hρ.1 hrec k
    simpa using this
  refine ⟨h1, (R.H4_7_d_dist hSD hxs k).trans ?_⟩
  have hσ := hSD.sigma_pos
  set ρ := rho (Lam L τ) σ
  have e : √(ρ ^ k) = √ρ ^ k := by
    rw [show ρ ^ k = (√ρ ^ k) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hρ.1],
      Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg _) _)]
  calc √(2 * R.ak F xs k / σ) ≤ √(ρ ^ k * (2 * R.ak F xs 0 / σ)) := by
        apply Real.sqrt_le_sqrt
        rw [show ρ ^ k * (2 * R.ak F xs 0 / σ) = 2 * (ρ ^ k * R.ak F xs 0) / σ by ring]
        exact div_le_div_of_nonneg_right (by linarith) hσ.le
    _ = √ρ ^ k * √(2 * R.ak F xs 0 / σ) := by
        rw [Real.sqrt_mul (pow_nonneg hρ.1 k), e]


/-- **Theorem H4.7(a), Λ = 0** (no cross coupling in the sweep order): an exact sweep lands
on x*: x^{k+1} = x*. -/
theorem H4_7_a_zero {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) (hΛ : Lam L τ = 0) {k : ℕ}
    (hex : ∀ l, R.eta F k l = 0 ∧ R.ε k l = 0) : R.x (k + 1) 0 = xs := by
  have h1 := R.H4_7_a hSD hxs hex
  rw [hΛ, rho] at h1
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_add, zero_div,
    zero_mul] at h1
  have h0 := R.ak_nonneg hxs (k + 1)
  have hd := R.H4_7_d_dist hSD hxs (k + 1)
  rw [show R.ak F xs (k + 1) = 0 by linarith] at hd
  simp only [mul_zero, zero_div, Real.sqrt_zero] at hd
  exact sub_eq_zero.1 (norm_le_zero_iff.1 hd)

/-- **Theorem H4.7(b)** (inexact block solves). For every θ > 0 and every k:
a_{k+1} ≤ ρ_θ a_k + (1 − ρ_θ)B_k(θ). -/
theorem H4_7_b {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    (k : ℕ) :
    R.ak F xs (k + 1) ≤ rhoth θ (Lam L τ) σ * R.ak F xs k
      + (1 - rhoth θ (Lam L τ) σ) * R.Bk F τ (Lam L τ) σ θ k := by
  obtain ⟨-, -, hS, h2⟩ := R.H4_6 hSD hxs k
  have hσ := hSD.sigma_pos
  set Λ := Lam L τ
  set S := R.ak F xs k - R.ak F xs (k + 1) + R.Gam F τ k
  set Q := R.Qk F τ Λ k
  set P := Λ * √(2 * S)
  have hP2 : P ^ 2 = Λ ^ 2 * (2 * S) := by rw [mul_pow, Real.sq_sqrt (by linarith)]
  have hyoung : (Q + P) ^ 2 ≤ (1 + θ) * P ^ 2 + (1 + 1 / θ) * Q ^ 2 := by
    have : (1 + θ) * P ^ 2 + (1 + 1 / θ) * Q ^ 2 - (Q + P) ^ 2 = (θ * P - Q) ^ 2 / θ := by
      field_simp; ring
    have : 0 ≤ (θ * P - Q) ^ 2 / θ := by positivity
    linarith
  set c := cth θ Λ σ
  have hc : (1 + θ) * P ^ 2 / (2 * σ) = c * S := by
    rw [hP2]; unfold c cth; field_simp
  have hB : R.Bk F τ Λ σ θ k = c * R.Gam F τ k + (1 + 1 / θ) * Q ^ 2 / (2 * σ) + R.epsk k := rfl
  have key : R.ak F xs (k + 1) ≤ c * S + (1 + 1 / θ) * Q ^ 2 / (2 * σ) + R.epsk k := by
    have := div_le_div_of_nonneg_right hyoung (by linarith : (0 : ℝ) ≤ 2 * σ)
    rw [add_div, hc] at this
    linarith
  have key2 : (1 + c) * R.ak F xs (k + 1) ≤ c * R.ak F xs k + R.Bk F τ Λ σ θ k := by
    rw [hB]; simp only [S] at key; linarith
  have hc0 : 0 ≤ c := cth_nonneg hθ hσ
  rw [one_sub_rhoth hθ hσ]
  unfold rhoth
  rw [show c / (1 + c) * R.ak F xs k + 1 / (1 + c) * R.Bk F τ Λ σ θ k
      = (c * R.ak F xs k + R.Bk F τ Λ σ θ k) / (1 + c) by field_simp]
  rw [le_div_iff₀ (by linarith)]
  linarith

/-- **Theorem H4.7(c)** (accumulation): a_k ≤ ρ_θ^k a₀ + (1 − ρ_θ)Σ_{i<k} ρ_θ^{k−1−i}B_i(θ). -/
theorem H4_7_c {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    (k : ℕ) :
    R.ak F xs k ≤ rhoth θ (Lam L τ) σ ^ k * R.ak F xs 0
      + (1 - rhoth θ (Lam L τ) σ) * ∑ i ∈ range k,
          rhoth θ (Lam L τ) σ ^ (k - 1 - i) * R.Bk F τ (Lam L τ) σ θ i :=
  accum (rhoth_mem hθ hSD.sigma_pos).1 (R.H4_7_b hSD hxs hθ) k

/-- **Theorem H4.7(c1)** (constant errors): B_i(θ) ≤ B̄ for i < k ⇒
a_k ≤ ρ_θ^k a₀ + (1 − ρ_θ^k)B̄. -/
theorem H4_7_c1 {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    {k : ℕ} {Bbar : ℝ} (hB : ∀ i < k, R.Bk F τ (Lam L τ) σ θ i ≤ Bbar) :
    R.ak F xs k ≤ rhoth θ (Lam L τ) σ ^ k * R.ak F xs 0
      + (1 - rhoth θ (Lam L τ) σ ^ k) * Bbar :=
  accum_const (rhoth_mem hθ hSD.sigma_pos).1 (rhoth_mem hθ hSD.sigma_pos).2
    (R.H4_7_b hSD hxs hθ) hB

/-- **Theorem H4.7(c2)** (geometric errors): B_i(θ) ≤ B̄₀qⁱ, q ∈ [0, 1), q ≠ ρ_θ ⇒
a_k ≤ max{ρ_θ, q}^k (a₀ + (1 − ρ_θ)B̄₀/|ρ_θ − q|). -/
theorem H4_7_c2 {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    {B0 q : ℝ} (hq0 : 0 ≤ q) (_hq1 : q < 1) (hne : q ≠ rhoth θ (Lam L τ) σ)
    (hB : ∀ i, R.Bk F τ (Lam L τ) σ θ i ≤ B0 * q ^ i) (k : ℕ) :
    R.ak F xs k ≤ max (rhoth θ (Lam L τ) σ) q ^ k
      * (R.ak F xs 0 + (1 - rhoth θ (Lam L τ) σ) * B0 / |rhoth θ (Lam L τ) σ - q|) :=
  accum_geom (rhoth_mem hθ hSD.sigma_pos).1 (rhoth_mem hθ hSD.sigma_pos).2
    (R.H4_7_b hSD hxs hθ) (R.ak_nonneg hxs 0)
    (fun i => R.Bk_nonneg F hSD.tau_pos hSD.sigma_pos hθ i) hq0 hne hB k

/-- **Theorem H4.7(c3)** (vanishing errors): B_k(θ) → 0 ⇒ a_k → 0 and x^k → x*. -/
theorem H4_7_c3 {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    (hB : Tendsto (R.Bk F τ (Lam L τ) σ θ) atTop (𝓝 0)) :
    Tendsto (R.ak F xs) atTop (𝓝 0) ∧ Tendsto (fun k => R.x k 0) atTop (𝓝 xs) := by
  have ha := accum_tendsto (rhoth_mem hθ hSD.sigma_pos).1 (rhoth_mem hθ hSD.sigma_pos).2
    (R.H4_7_b hSD hxs hθ) (R.ak_nonneg hxs)
    (fun i => R.Bk_nonneg F hSD.tau_pos hSD.sigma_pos hθ i) hB
  refine ⟨ha, ?_⟩
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hs : Tendsto (fun k => √(2 * R.ak F xs k / σ)) atTop (𝓝 0) := by
    have h0 : Tendsto (fun k => 2 * R.ak F xs k / σ) atTop (𝓝 (2 * 0 / σ)) :=
      (ha.const_mul 2).div_const σ
    rw [mul_zero, zero_div] at h0
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def] using this
  exact squeeze_zero (fun k => norm_nonneg _) (fun k => R.H4_7_d_dist hSD hxs k) hs

/-- **Theorem H4.7(c3), general form:** limsup a_k ≤ limsup B_k(θ) (B bounded). -/
theorem H4_7_c3_limsup {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop (R.Bk F τ (Lam L τ) σ θ)) :
    limsup (R.ak F xs) atTop ≤ limsup (R.Bk F τ (Lam L τ) σ θ) atTop :=
  accum_limsup (rhoth_mem hθ hSD.sigma_pos).1 (rhoth_mem hθ hSD.sigma_pos).2
    (R.H4_7_b hSD hxs hθ) (R.ak_nonneg hxs)
    (fun i => R.Bk_nonneg F hSD.tau_pos hSD.sigma_pos hθ i) hbdd

end Run

/-- Γ as a function of per-block residuals η and accuracies ε: Σ_l (η_l²/(2τ_l) + ε_l). -/
noncomputable def Gfun (τ : Fin m → ℝ) (η ε : Fin m → ℝ) : ℝ := ∑ l, (η l ^ 2 / (2 * τ l) + ε l)

/-- B(θ) as a function of per-block residuals η and accuracies ε (Def. H4.0(c)). -/
noncomputable def Bfun (τ : Fin m → ℝ) (Λ σ θ : ℝ) (η ε : Fin m → ℝ) : ℝ :=
  cth θ Λ σ * Gfun τ η ε + (1 + 1 / θ) * (√(∑ l, η l ^ 2) + Λ * √(2 * Gfun τ η ε)) ^ 2 / (2 * σ)
    + ∑ l, ε l

lemma Run.Bk_eq {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} (R : Run D g) (F : PiLp 2 X → ℝ)
    (τ : Fin m → ℝ) (Λ σ θ : ℝ) (k : ℕ) :
    R.Bk F τ Λ σ θ k = Bfun τ Λ σ θ (R.eta F k) (R.ε k) := rfl

/-- **Theorem H4.7(d), monotonicity.** B(θ) is nondecreasing in every η_l ≥ 0 and ε_l ≥ 0. -/
theorem Bfun_mono {τ : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) {Λ σ θ : ℝ} (hΛ : 0 ≤ Λ) (hσ : 0 < σ)
    (hθ : 0 < θ) {η η' ε ε' : Fin m → ℝ} (hη0 : ∀ l, 0 ≤ η l) (hη : ∀ l, η l ≤ η' l)
    (hε0 : ∀ l, 0 ≤ ε l) (hε : ∀ l, ε l ≤ ε' l) : Bfun τ Λ σ θ η ε ≤ Bfun τ Λ σ θ η' ε' := by
  have hsq : ∀ l, η l ^ 2 ≤ η' l ^ 2 := fun l => pow_le_pow_left₀ (hη0 l) (hη l) 2
  have hG : Gfun τ η ε ≤ Gfun τ η' ε' := sum_le_sum fun l _ => by
    have := div_le_div_of_nonneg_right (hsq l) (by linarith [hτ l] : (0 : ℝ) ≤ 2 * τ l)
    linarith [hε l]
  have hG0 : 0 ≤ Gfun τ η ε := sum_nonneg fun l _ => by
    have := hτ l; have := hε0 l; positivity
  have h1 : √(∑ l, η l ^ 2) ≤ √(∑ l, η' l ^ 2) := Real.sqrt_le_sqrt (sum_le_sum fun l _ => hsq l)
  have h2 : √(2 * Gfun τ η ε) ≤ √(2 * Gfun τ η' ε') := Real.sqrt_le_sqrt (by linarith)
  have hQ : √(∑ l, η l ^ 2) + Λ * √(2 * Gfun τ η ε)
      ≤ √(∑ l, η' l ^ 2) + Λ * √(2 * Gfun τ η' ε') :=
    add_le_add h1 (mul_le_mul_of_nonneg_left h2 hΛ)
  have hQ0 : 0 ≤ √(∑ l, η l ^ 2) + Λ * √(2 * Gfun τ η ε) := by positivity
  have hc := cth_nonneg (Λ := Λ) hθ hσ
  unfold Bfun
  refine add_le_add (add_le_add (mul_le_mul_of_nonneg_left hG hc) ?_)
    (sum_le_sum fun l _ => hε l)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQ 2) (by positivity)

namespace Run

variable {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} (R : Run D g)

/-- **Theorem H4.7(d), declared bounds.** If η_{k,l} ≤ η̄_l and ε_{k,l} ≤ ε̄_l (declared
schedules), then a_{k+1} ≤ ρ_θa_k + (1 − ρ_θ)B̄ with B̄ := B(θ) at the declared bounds. -/
theorem H4_7_d_declared {F : PiLp 2 X → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {θ : ℝ} (hθ : 0 < θ)
    {k : ℕ} {ηbar εbar : Fin m → ℝ} (hη : ∀ l, R.eta F k l ≤ ηbar l)
    (hε : ∀ l, R.ε k l ≤ εbar l) :
    R.ak F xs (k + 1) ≤ rhoth θ (Lam L τ) σ * R.ak F xs k
      + (1 - rhoth θ (Lam L τ) σ) * Bfun τ (Lam L τ) σ θ ηbar εbar := by
  have h := R.H4_7_b hSD hxs hθ k
  have hm := Bfun_mono (Λ := Lam L τ) hSD.tau_pos (Real.sqrt_nonneg _) hSD.sigma_pos hθ
    (fun l => R.eta_nonneg F k l) hη (fun l => (R.report k l).1) hε
  rw [R.Bk_eq] at h
  have h1 : 0 ≤ 1 - rhoth θ (Lam L τ) σ := by linarith [(rhoth_mem (Λ := Lam L τ) hθ hSD.sigma_pos).2]
  nlinarith

end Run

/-! ## Corollary H4.8 (a priori form from declared value-gap schedules) -/

/-- K_θ := c_θ(S₁ + m) + (1 + 1/θ)(S₂^{1/2} + Λ(S₁ + m)^{1/2})²/σ + m,
S₁ := Σ_l L_l/τ_l, S₂ := Σ_l L_l. -/
noncomputable def Kth (τ Ld : Fin m → ℝ) (Λ σ θ : ℝ) : ℝ :=
  cth θ Λ σ * (∑ l, Ld l / τ l + m)
    + (1 + 1 / θ) * (√(∑ l, Ld l) + Λ * √(∑ l, Ld l / τ l + m)) ^ 2 / σ + m

/-- K'_θ := 4c_θS₁ + 4(1 + 1/θ)(S₂^{1/2} + ΛS₁^{1/2})²/σ. -/
noncomputable def Kth' (τ Ld : Fin m → ℝ) (Λ σ θ : ℝ) : ℝ :=
  4 * cth θ Λ σ * (∑ l, Ld l / τ l)
    + 4 * (1 + 1 / θ) * (√(∑ l, Ld l) + Λ * √(∑ l, Ld l / τ l)) ^ 2 / σ

/-- B(θ) at η̄_l = √(2L_l ē), ε̄_l = ē equals K_θē. -/
lemma Bfun_valuegap {τ Ld : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) (hLd : ∀ l, 0 < Ld l) {Λ σ θ e : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (he : 0 ≤ e) :
    Bfun τ Λ σ θ (fun l => √(2 * Ld l * e)) (fun _ => e) = Kth τ Ld Λ σ θ * e := by
  have hS1 : 0 ≤ ∑ l, Ld l / τ l := sum_nonneg fun l _ => (div_pos (hLd l) (hτ l)).le
  have hS2 : 0 ≤ ∑ l, Ld l := sum_nonneg fun l _ => (hLd l).le
  have hG : Gfun τ (fun l => √(2 * Ld l * e)) (fun _ => e) = (∑ l, Ld l / τ l + m) * e := by
    unfold Gfun
    rw [add_mul, sum_mul]
    have : ∑ l, (√(2 * Ld l * e) ^ 2 / (2 * τ l) + e) = ∑ l, (Ld l / τ l * e + e) := by
      refine sum_congr rfl fun l _ => ?_
      rw [Real.sq_sqrt (by have := hLd l; positivity)]
      have := hτ l; field_simp
    rw [this, sum_add_distrib]; simp
  have hE : ∑ l, √(2 * Ld l * e) ^ 2 = 2 * e * ∑ l, Ld l := by
    rw [mul_sum]; refine sum_congr rfl fun l _ => ?_
    rw [Real.sq_sqrt (by have := hLd l; positivity)]; ring
  unfold Bfun
  rw [hG, hE]
  have h1 : √(2 * e * ∑ l, Ld l) = √(2 * e) * √(∑ l, Ld l) := Real.sqrt_mul (by positivity) _
  have h2 : √(2 * ((∑ l, Ld l / τ l + m) * e)) = √(2 * e) * √(∑ l, Ld l / τ l + m) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  rw [h1, h2]
  have h3 : (√(2 * e) * √(∑ l, Ld l) + Λ * (√(2 * e) * √(∑ l, Ld l / τ l + m))) ^ 2
      = 2 * e * (√(∑ l, Ld l) + Λ * √(∑ l, Ld l / τ l + m)) ^ 2 := by
    rw [show √(2 * e) * √(∑ l, Ld l) + Λ * (√(2 * e) * √(∑ l, Ld l / τ l + m))
        = √(2 * e) * (√(∑ l, Ld l) + Λ * √(∑ l, Ld l / τ l + m)) by ring, mul_pow,
      Real.sq_sqrt (by positivity)]
  rw [h3]
  unfold Kth
  simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp

/-- B(θ) at η̄_l = 2√(2L_l ē), ε̄_l = 0 equals K'_θē. -/
lemma Bfun_polish {τ Ld : Fin m → ℝ} (hτ : ∀ l, 0 < τ l) (hLd : ∀ l, 0 < Ld l) {Λ σ θ e : ℝ}
    (hσ : 0 < σ) (hθ : 0 < θ) (he : 0 ≤ e) :
    Bfun τ Λ σ θ (fun l => 2 * √(2 * Ld l * e)) (fun _ => 0) = Kth' τ Ld Λ σ θ * e := by
  have hS1 : 0 ≤ ∑ l, Ld l / τ l := sum_nonneg fun l _ => (div_pos (hLd l) (hτ l)).le
  have hS2 : 0 ≤ ∑ l, Ld l := sum_nonneg fun l _ => (hLd l).le
  have hG : Gfun τ (fun l => 2 * √(2 * Ld l * e)) (fun _ => 0) = 4 * (∑ l, Ld l / τ l) * e := by
    unfold Gfun
    rw [mul_assoc, sum_mul, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    rw [mul_pow, Real.sq_sqrt (by have := hLd l; positivity)]
    have := hτ l; field_simp; ring
  have hE : ∑ l, (2 * √(2 * Ld l * e)) ^ 2 = 8 * e * ∑ l, Ld l := by
    rw [mul_sum]; refine sum_congr rfl fun l _ => ?_
    rw [mul_pow, Real.sq_sqrt (by have := hLd l; positivity)]; ring
  unfold Bfun
  rw [hG, hE]
  have h1 : √(8 * e * ∑ l, Ld l) = √(8 * e) * √(∑ l, Ld l) := Real.sqrt_mul (by positivity) _
  have h2 : √(2 * (4 * (∑ l, Ld l / τ l) * e)) = √(8 * e) * √(∑ l, Ld l / τ l) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  rw [h1, h2]
  have h3 : (√(8 * e) * √(∑ l, Ld l) + Λ * (√(8 * e) * √(∑ l, Ld l / τ l))) ^ 2
      = 8 * e * (√(∑ l, Ld l) + Λ * √(∑ l, Ld l / τ l)) ^ 2 := by
    rw [show √(8 * e) * √(∑ l, Ld l) + Λ * (√(8 * e) * √(∑ l, Ld l / τ l))
        = √(8 * e) * (√(∑ l, Ld l) + Λ * √(∑ l, Ld l / τ l)) by ring, mul_pow,
      Real.sq_sqrt (by positivity)]
  rw [h3]
  unfold Kth'
  simp only [sum_const_zero, add_zero]
  field_simp
  ring

/-- **Corollary H4.8(a)** (bare value gaps; existence of reports, Def. H4.0(e)). SD, x* a
minimiser; diagonal block constants L_l > 0 (∇φ_{x,l} L_l-Lipschitz for every x); nontrivial
blocks; the ε-sum rule for every block subproblem (classical input). A sweep sequence
x^{k,l+1} = x^{k,l} + U_l(z_{k,l} − x^{k,l}_l), x^{k+1,0} = x^{k,m}, x^{0,0} ∈ dom g, in which every
block output has value gap at most ē_k in its block subproblem (any solver):
then a_{k+1} ≤ ρ_θa_k + (1 − ρ_θ)K_θē_k for every k (a_k := E(x^k) − E*). -/
theorem H4_8_a [∀ l, Nontrivial (X l)] {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)}
    {g : ∀ l, X l → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {Ld : Fin m → ℝ}
    (hLd : ∀ l, 0 < Ld l) (hLip : ∀ x l, LipGrad (slice F x l) (Ld l))
    (hsum : ∀ x l, EpsSumRule (D l) (slice F x l) (g l))
    (x : ℕ → ℕ → PiLp 2 X) (z : ℕ → (l : Fin m) → X l) (hstart : x 0 0 ∈ domG D)
    (hstep : ∀ k (l : Fin m), x k (l.val + 1) = upd (x k l.val) l (z k l))
    (hnext : ∀ k, x (k + 1) 0 = x k m) (hz : ∀ k l, z k l ∈ D l) {ebar : ℕ → ℝ}
    (he : ∀ k, 0 ≤ ebar k)
    (hgap : ∀ k l, ∀ w ∈ D l, PhiB F g (x k l.val) l (z k l) ≤ PhiB F g (x k l.val) l w + ebar k)
    {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    Efun F g (x (k + 1) 0) - Efun F g xs ≤ rhoth θ (Lam L τ) σ * (Efun F g (x k 0) - Efun F g xs)
      + (1 - rhoth θ (Lam L τ) σ) * (Kth τ Ld (Lam L τ) σ θ * ebar k) := by
  -- choose reports by Lemma H4.3(d)
  have hex : ∀ k (l : Fin m), ∃ e₁ e₂ : ℝ, ∃ v : X l, 0 ≤ e₁ ∧ 0 ≤ e₂ ∧ e₁ + e₂ = ebar k ∧
      EpsSubgrad (D l) (g l) e₂ (z k l) v ∧
      ‖gradient (slice F (x k l.val) l) (z k l) + v‖ ≤ √(2 * Ld l * e₁) ∧
      ‖gradient (slice F (x k l.val) l) (z k l) + v‖ ≤ √(2 * Ld l * ebar k) ∧ e₂ ≤ ebar k ∧
      ‖gradient (slice F (x k l.val) l) (z k l) + v‖ ^ 2 / (2 * τ l) + e₂ ≤ Ld l * e₁ / τ l + e₂ ∧
      Ld l * e₁ / τ l + e₂ ≤ Ld l / τ l * ebar k := fun k l =>
    report_valuegap (hLd l) (hSD.tau_pos l) (differentiable_slice hSD.diff _ l) (hLip _ l)
      (hSD.slice _ l) (hsum _ l) (he k) (hz k l) (hgap k l)
  choose e₁ e₂ v he₁ he₂ hsum' hv hn1 hn hle _ _ using hex
  let R : Run D g := ⟨x, z, v, e₂, hstart, hstep, hnext, fun k l => ⟨he₂ k l, hv k l⟩⟩
  have hη : ∀ l, R.eta F k l ≤ √(2 * Ld l * ebar k) := by
    intro l
    have := hn k l
    rw [gradient_slice hSD.diff, ← hstep] at this
    exact this
  have h := R.H4_7_d_declared hSD hxs hθ hη (fun l => hle k l)
  rw [Bfun_valuegap hSD.tau_pos hLd hSD.sigma_pos hθ (he k)] at h
  exact h

/-- **Corollary H4.8(b)** (polished outputs, Lemma H4.3(b) with M_l = L_l; the run
continues from the polished points p_{k,l}, whose reports are in hand). Pre-polish points
z'_{k,l} ∈ dom g_l with value gap ≤ ē_k; p_{k,l} = prox_{g_l/L_l}(z' − ∇φ(z')/L_l) (given by
(P), classical input): a_{k+1} ≤ ρ_θa_k + (1 − ρ_θ)K'_θē_k. -/
theorem H4_8_b {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)}
    {g : ∀ l, X l → ℝ} {σ : ℝ} {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ}
    (hSD : SD F D g σ τ L) {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {Ld : Fin m → ℝ}
    (hLd : ∀ l, 0 < Ld l) (hLip : ∀ x l, LipGrad (slice F x l) (Ld l))
    (x : ℕ → ℕ → PiLp 2 X) (z' p : ℕ → (l : Fin m) → X l) (hstart : x 0 0 ∈ domG D)
    (hstep : ∀ k (l : Fin m), x k (l.val + 1) = upd (x k l.val) l (p k l))
    (hnext : ∀ k, x (k + 1) 0 = x k m) (hz : ∀ k l, z' k l ∈ D l) {ebar : ℕ → ℝ}
    (he : ∀ k, 0 ≤ ebar k)
    (hgap : ∀ k l, ∀ w ∈ D l, PhiB F g (x k l.val) l (z' k l) ≤ PhiB F g (x k l.val) l w + ebar k)
    (hprox : ∀ k l, ProxEps (D l) (g l) (Ld l)⁻¹ 0
      (z' k l - (Ld l)⁻¹ • gradient (slice F (x k l.val) l) (z' k l)) (p k l))
    {θ : ℝ} (hθ : 0 < θ) (k : ℕ) :
    (∀ l, EpsSubgrad (D l) (g l) 0 (p k l)
      (Ld l • (z' k l - p k l) - gradient (slice F (x k l.val) l) (z' k l))) ∧
    Efun F g (x (k + 1) 0) - Efun F g xs ≤ rhoth θ (Lam L τ) σ * (Efun F g (x k 0) - Efun F g xs)
      + (1 - rhoth θ (Lam L τ) σ) * (Kth' τ Ld (Lam L τ) σ θ * ebar k) := by
  have hpol := fun k (l : Fin m) => report_polish_L (hLd l)
    (differentiable_slice hSD.diff (x k l.val) l) (hLip _ l) (hz k l) (hgap k l) (hprox k l)
  let R : Run D g := ⟨x, p, fun k l => Ld l • (z' k l - p k l)
      - gradient (slice F (x k l.val) l) (z' k l), fun _ _ => 0, hstart, hstep, hnext,
      fun k l => ⟨le_rfl, (hpol k l).1⟩⟩
  refine ⟨fun l => (hpol k l).1, ?_⟩
  have hη : ∀ l, R.eta F k l ≤ 2 * √(2 * Ld l * ebar k) := by
    intro l
    have := (hpol k l).2.2
    rw [gradient_slice hSD.diff, ← hstep] at this
    exact this
  have h := R.H4_7_d_declared hSD hxs hθ hη (fun l => le_rfl)
  rw [Bfun_polish hSD.tau_pos hLd hSD.sigma_pos hθ (he k)] at h
  exact h

/-- **Corollary H4.8**, geometric schedule: with B_i := Kē_i (K = K_θ or K'_θ) and
ē_i = ē₀qⁱ, q ∈ [0, 1), q ≠ ρ_θ: a_k ≤ max{ρ_θ, q}^k(a₀ + (1 − ρ_θ)Kē₀/|ρ_θ − q|). -/
theorem H4_8_geom {a ebar : ℕ → ℝ} {r K e0 q : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hK : 0 ≤ K)
    (h : ∀ k, a (k + 1) ≤ r * a k + (1 - r) * (K * ebar k)) (ha0 : 0 ≤ a 0)
    (he : ∀ i, 0 ≤ ebar i) (hq0 : 0 ≤ q) (hne : q ≠ r) (hgeo : ∀ i, ebar i ≤ e0 * q ^ i)
    (k : ℕ) : a k ≤ max r q ^ k * (a 0 + (1 - r) * (K * e0) / |r - q|) :=
  accum_geom hr0 hr1 h ha0 (fun i => mul_nonneg hK (he i)) hq0 hne
    (fun i => by have := mul_le_mul_of_nonneg_left (hgeo i) hK; linarith) k

/-! ## Proposition H4.9 (pointwise certificate of a stitched output, any provenance) -/

/-- **Proposition H4.9(a)** (report form). SD2–SD4 (g_l convex), x* a minimiser of E,
x̂ ∈ dom g arbitrary (any solvers, any stitching), block reports v_l ∈ ∂_{ε_l} g_l(x̂_l) at the
output; u := ∇F(x̂) + (v_l)_l, ε := Σ_l ε_l. Then (v_l)_l ∈ ∂_ε g(x̂),
E(x̂) − ‖u‖²/(2σ) − ε ≤ E* ≤ E(x̂) and ‖x̂ − x*‖ ≤ (‖u‖ + (‖u‖² + 4σε)^{1/2})/(2σ).
(Both bounds are attained: `bracket_value_sharp`, `bracket_dist_sharp`.) -/
theorem H4_9_a {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} {σ : ℝ}
    (hF : Differentiable ℝ F) (hC : ModC F σ) (hσ : 0 < σ) (hg : ∀ l, ModCD (D l) (g l) 0)
    {xs : PiLp 2 X} (hxs : IsMinE F D g xs) {xh : PiLp 2 X} {v : ∀ l, X l} {ε : Fin m → ℝ}
    (hv : ∀ l, EpsSubgrad (D l) (g l) (ε l) (xh l) (v l)) :
    EpsSubgrad (domG D) (gsum g) (∑ l, ε l) xh (WithLp.toLp 2 v) ∧
    Efun F g xh - ‖gradient F xh + WithLp.toLp 2 v‖ ^ 2 / (2 * σ) - ∑ l, ε l ≤ Efun F g xs ∧
    Efun F g xs ≤ Efun F g xh ∧
    ‖xh - xs‖ ≤ (‖gradient F xh + WithLp.toLp 2 v‖
      + √(‖gradient F xh + WithLp.toLp 2 v‖ ^ 2 + 4 * σ * ∑ l, ε l)) / (2 * σ) := by
  have hsub := Run.sep_assembly (D := D) (g := g) hv
  have hb := value_bracket (D := domG D) (g := gsum g) hF hC hσ hxs.1 hxs.2 hsub
  have hd := dist_bracket (D := domG D) (g := gsum g) hF hC hσ (modCD_gsum hg) hxs.1 hxs.2 hsub
  exact ⟨hsub, hb.1, hb.2, hd⟩

/-- **Proposition H4.9(c).** For a stitched run, (a) at x̂ := x^{k+1} with the run's own reports
is exactly u_k, ε_k of Lemma H4.4: the run certifies itself at every sweep end. -/
theorem H4_9_c {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} {σ : ℝ}
    {τ : Fin m → ℝ} {L : Fin m → Fin m → ℝ} (hSD : SD F D g σ τ L) {xs : PiLp 2 X}
    (hxs : IsMinE F D g xs) (R : Run D g) (k : ℕ) :
    Efun F g (R.x (k + 1) 0) - ‖R.uk F k‖ ^ 2 / (2 * σ) - R.epsk k ≤ Efun F g xs ∧
    Efun F g xs ≤ Efun F g (R.x (k + 1) 0) ∧
    ‖R.x (k + 1) 0 - xs‖ ≤ (‖R.uk F k‖ + √(‖R.uk F k‖ ^ 2 + 4 * σ * R.epsk k)) / (2 * σ) := by
  have hsub := R.H4_4_a k
  have hb := value_bracket (D := domG D) (g := gsum g) hSD.diff hSD.modF hSD.sigma_pos
    hxs.1 hxs.2 hsub
  have hd := dist_bracket (D := domG D) (g := gsum g) hSD.diff hSD.modF hSD.sigma_pos
    (modCD_gsum hSD.convex_g) hxs.1 hxs.2 hsub
  exact ⟨hb.1, hb.2, hd⟩

/-- The separable proximal map: block proximal maps P_l (each given by its characterisation
(P), a classical input) assemble into the proximal map of g = Σ_l g_l:
x̂ ↦ (P_l(y_l))_l satisfies (y − P y)/α ∈ ∂g(P y). -/
theorem sep_prox {D : ∀ l, Set (X l)} {g : ∀ l, X l → ℝ} {α : ℝ} {P : ∀ l, X l → X l}
    (hP : ∀ l y, ProxEps (D l) (g l) α 0 y (P l y)) (y : PiLp 2 X) :
    ProxEps (domG D) (gsum g) α 0 y (WithLp.toLp 2 (fun l => P l (y l))) := by
  have := Run.sep_assembly (D := D) (g := g) (xh := WithLp.toLp 2 (fun l => P l (y l)))
    (v := fun l => α⁻¹ • (y l - P l (y l))) (ε := fun _ => 0) (fun l => hP l (y l))
  simp only [sum_const_zero] at this
  exact this

/-- **Proposition H4.9(b)** (zero-trust form). ∇F β-Lipschitz, C(F, σ), σ > 0, α = 1/β, every
g_l convex with an exact block prox P_l (given by (P)); T_αx̂ := (P_l(x̂_l − α∇_lF(x̂)))_l,
R_α(x̂) := (x̂ − T_αx̂)/α, p := T_αx̂, u := R_α(x̂) − ∇F(x̂) + ∇F(p). Then
‖x̂ − x*‖ ≤ ‖R_α(x̂)‖/σ and E(p) − ‖u‖²/(2σ) ≤ E* ≤ E(p). With inexact block outputs
z_l ∈ prox^{ε'_l}_{αg_l}(x̂_l − α∇_lF(x̂)) and r := (x̂ − z)/α:
‖x̂ − x*‖ ≤ (‖r‖ + (βΣ_lε'_l)^{1/2})/σ. -/
theorem H4_9_b [Nontrivial (PiLp 2 X)] {F : PiLp 2 X → ℝ} {D : ∀ l, Set (X l)}
    {g : ∀ l, X l → ℝ} {σ α β : ℝ} (hF : Differentiable ℝ F) (hL : LipGrad F β)
    (hC : ModC F σ) (hσ : 0 < σ) (hα : 0 < α) (hαβ : α * β = 1) (hg : ∀ l, ModCD (D l) (g l) 0)
    {P : ∀ l, X l → X l} (hP : ∀ l y, ProxEps (D l) (g l) α 0 y (P l y))
    {xs : PiLp 2 X} (hxs : IsMinE F D g xs) (xh : PiLp 2 X) :
    let p : PiLp 2 X := WithLp.toLp 2 (fun l => P l (step F α xh l))
    ‖xh - xs‖ ≤ ‖α⁻¹ • (xh - p)‖ / σ ∧
    Efun F g p - ‖α⁻¹ • (xh - p) - gradient F xh + gradient F p‖ ^ 2 / (2 * σ) ≤ Efun F g xs ∧
    Efun F g xs ≤ Efun F g p ∧
    (∀ (zt : ∀ l, X l) (ε' : Fin m → ℝ),
      (∀ l, ProxEps (D l) (g l) α (ε' l) (step F α xh l) (zt l)) →
      ‖xh - xs‖ ≤ (‖α⁻¹ • (xh - WithLp.toLp 2 zt)‖ + √(β * ∑ l, ε' l)) / σ) := by
  intro p
  set Pf : PiLp 2 X → PiLp 2 X := fun y => WithLp.toLp 2 (fun l => P l (y l)) with hPf
  have hPf' : ∀ y, ProxEps (domG D) (gsum g) α 0 y (Pf y) := sep_prox hP
  have hgs := modCD_gsum hg
  obtain ⟨hcon, -, hq1⟩ := regime_contract (D := domG D) (g := gsum g) hF hL hα hαβ hC hgs
    le_rfl hPf' hxs.1 hxs.2 (Or.inl ⟨hσ, rfl⟩)
  have hdist : ∀ y, ‖y - xs‖ ≤ ‖α⁻¹ • (y - Pf (step F α y))‖ / σ := by
    intro y
    have h1 := dist_le_of_contract hα hq1 hcon y
    have e : α / (1 - qA β σ) = 1 / σ := by
      rw [show 1 - qA β σ = σ / β by unfold qA; ring, div_div_eq_mul_div, hαβ]
    rw [e] at h1
    rw [div_eq_mul_one_div, mul_comm]; exact h1
  have hp : p = Pf (step F α xh) := rfl
  refine ⟨hp ▸ hdist xh, ?_, ?_, ?_⟩
  · have hsub := hPf' (step F α xh)
    rw [← hp] at hsub
    unfold ProxEps at hsub
    have hv : α⁻¹ • (step F α xh - p) = α⁻¹ • (xh - p) - gradient F xh := by
      unfold step
      rw [show xh - α • gradient F xh - p = (xh - p) - α • gradient F xh by abel, smul_sub,
        smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
    rw [hv] at hsub
    have := (value_bracket (D := domG D) (g := gsum g) hF hC hσ hxs.1 hxs.2 hsub).1
    have e : gradient F p + (α⁻¹ • (xh - p) - gradient F xh)
        = α⁻¹ • (xh - p) - gradient F xh + gradient F p := by abel
    rw [e] at this
    unfold Efun; linarith
  · exact hxs.2 p (hPf' _).1
  · intro zt ε' hzt
    have hz : ProxEps (domG D) (gsum g) α (∑ l, ε' l) (step F α xh) (WithLp.toLp 2 zt) := by
      have := Run.sep_assembly (D := D) (g := g) (xh := WithLp.toLp 2 zt)
        (v := fun l => α⁻¹ • (step F α xh l - zt l)) (ε := ε') hzt
      exact this
    have hce := comparison_e hα hαβ hz (hPf' (step F α xh))
    have h1 := hdist xh
    have h2 : ‖α⁻¹ • (xh - Pf (step F α xh))‖ ≤ ‖α⁻¹ • (xh - WithLp.toLp 2 zt)‖
        + √(β * ∑ l, ε' l) := by
      have := norm_le_insert' (α⁻¹ • (xh - Pf (step F α xh))) (α⁻¹ • (xh - WithLp.toLp 2 zt))
      linarith
    calc ‖xh - xs‖ ≤ ‖α⁻¹ • (xh - Pf (step F α xh))‖ / σ := h1
      _ ≤ _ := div_le_div_of_nonneg_right h2 hσ.le

end Run

/-! ## Proposition H4.10 (the hypotheses are needed): two scalar blocks on ℝ² -/

section Examples

/-- ℝ² with two scalar blocks (PiLp 2 (fun _ : Fin 2 => ℝ)). -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

lemma E2_norm_sq (x : E2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]

lemma E2_inner (u x : E2) : inner ℝ u x = u 0 * x 0 + u 1 * x 1 := by
  rw [PiLp.inner_apply, Fin.sum_univ_two]; simp [mul_comm]

lemma v2_0 (a b : ℝ) : (!₂[a, b] : E2) 0 = a := by simp
lemma v2_1 (a b : ℝ) : (!₂[a, b] : E2) 1 = b := by simp

lemma norm_v2 (a b : ℝ) : ‖(!₂[a, b] : E2)‖ = √(a ^ 2 + b ^ 2) := by
  rw [← Real.sqrt_sq (norm_nonneg _), E2_norm_sq, v2_0, v2_1]

lemma upd00 (x : E2) (y : ℝ) : upd x 0 y 0 = y := upd_same (X := fun _ => ℝ) x 0 y
lemma upd01 (x : E2) (y : ℝ) : upd x 0 y 1 = x 1 := upd_ne (X := fun _ => ℝ) x (by decide) y
lemma upd10 (x : E2) (y : ℝ) : upd x 1 y 0 = x 0 := upd_ne (X := fun _ => ℝ) x (by decide) y
lemma upd11 (x : E2) (y : ℝ) : upd x 1 y 1 = y := upd_same (X := fun _ => ℝ) x 1 y

lemma E2_ext {x y : E2} (h0 : x 0 = y 0) (h1 : y 1 = x 1 ∨ x 1 = y 1) : x = y := by
  have h1' : x 1 = y 1 := h1.elim Eq.symm id
  ext i; fin_cases i <;> simp [h0, h1']

/-- One exact cyclic sweep for two scalar blocks: x'₀ minimises w ↦ E(w, x₁), then
x'₁ minimises w ↦ E(x'₀, w) (Definition H4.0(b) with η = ε = 0). -/
def ExactSweep2 (E : E2 → ℝ) (x x' : E2) : Prop :=
  (∀ w, E (upd x 0 (x' 0)) ≤ E (upd x 0 w)) ∧
    (∀ w, E (upd (upd x 0 (x' 0)) 1 (x' 1)) ≤ E (upd (upd x 0 (x' 0)) 1 w))

lemma ExactSweep2.eq {E : E2 → ℝ} {x x' : E2} (_h : ExactSweep2 E x x') :
    upd (upd x 0 (x' 0)) 1 (x' 1) = x' :=
  E2_ext (by rw [upd10, upd00]) (Or.inr (by rw [upd11]))

/-- The (exact) subdifferential of a real-valued function. -/
def subdiff (E : E2 → ℝ) (x : E2) : Set E2 := {u | ∀ y, E x + inner ℝ u (y - x) ≤ E y}

/-- Existence of a minimiser on ℝ for a continuous function with a quadratic minorant. -/
lemma exists_min_real {ψ : ℝ → ℝ} (hc : Continuous ψ) {a K : ℝ} (ha : 0 < a)
    (hlow : ∀ y, a * y ^ 2 - K ≤ ψ y) : ∃ y, ∀ w, ψ y ≤ ψ w := by
  refine hc.exists_forall_le' 0 ?_
  set R := (|ψ 0| + |K|) / a + 1
  have hR1 : 1 ≤ R := by have : 0 ≤ (|ψ 0| + |K|) / a := by positivity
                         linarith
  have hc' := (ProperSpace.isCompact_closedBall (0 : ℝ) R).compl_mem_cocompact
  filter_upwards [hc'] with y hy
  simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le,
    Real.norm_eq_abs] at hy
  have h1 := hlow y
  have hy2 : R ^ 2 < y ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg y]) hy
    simpa [sq_abs] using this
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hkey : |ψ 0| + |K| ≤ a * R := by
    have : a * R = |ψ 0| + |K| + a := by simp only [R]; field_simp
    linarith
  nlinarith [le_abs_self (ψ 0), le_abs_self K, neg_abs_le K]


/-- x + U_l h = x + U_l((x_l + h) − x_l). -/
lemma add_U_eq_upd (x : E2) (l : Fin 2) (h : ℝ) : x + U (X := fun _ => ℝ) l h = upd x l (x l + h) := by
  simp [upd]

/-- Block gradient of a C¹ function on ℝ² from the derivative of its slice. -/
lemma gradient_E2 {E : E2 → ℝ} (hE : Differentiable ℝ E) (x : E2) (j : Fin 2) {d : ℝ}
    (h : HasDerivAt (slice E x j) d (x j)) : gradient E x j = d := by
  rw [gradient_block_eq (X := fun _ => ℝ) hE, gradient_eq_deriv, h.deriv]; simp

/-! ### H4.10(a): a non-smooth coupling stalls even under strong convexity -/

/-- E_σ(x) := |3x₁ + 4x₂| + |x₁ − 2x₂| + (σ/2)‖x‖². -/
noncomputable def Eabs (σ : ℝ) (x : E2) : ℝ := |3 * x 0 + 4 * x 1| + |x 0 - 2 * x 1| + σ / 2 * ‖x‖ ^ 2

lemma convexOn_abs_lin (a b : ℝ) : ConvexOn ℝ univ (fun x : E2 => |a * x 0 + b * x 1|) := by
  refine ⟨convex_univ, fun x _ y _ p q hp hq _ => ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  calc |a * (p * x 0 + q * y 0) + b * (p * x 1 + q * y 1)|
        = |p * (a * x 0 + b * x 1) + q * (a * y 0 + b * y 1)| := by ring_nf
    _ ≤ |p * (a * x 0 + b * x 1)| + |q * (a * y 0 + b * y 1)| := abs_add_le _ _
    _ = p * |a * x 0 + b * x 1| + q * |a * y 0 + b * y 1| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hp, abs_of_nonneg hq]

lemma Eabs_v2 (σ a b : ℝ) :
    Eabs σ !₂[a, b] = |3 * a + 4 * b| + |a - 2 * b| + σ / 2 * (a ^ 2 + b ^ 2) := by
  rw [Eabs, E2_norm_sq, v2_0, v2_1]

lemma Eabs_zero (σ : ℝ) : Eabs σ 0 = 0 := by simp [Eabs]

lemma continuous_Eabs (σ : ℝ) : Continuous (Eabs σ) := by
  unfold Eabs; fun_prop

lemma continuous_upd2 (x : E2) (l : Fin 2) : Continuous (fun y : ℝ => upd x l y) :=
  continuous_const.add ((U (X := fun _ => ℝ) l).continuous.comp (continuous_id.sub continuous_const))

/-- **Proposition H4.10(a)**, strong convexity, minimiser, block subproblems: C(E_σ, σ);
E_σ ≥ 0 = E_σ(0) with 0 the unique minimiser; every block subproblem has exactly one
minimiser. -/
theorem H4_10_a_basic {σ : ℝ} (hσ : 0 < σ) :
    ModC (Eabs σ) σ ∧ (∀ x, Eabs σ 0 ≤ Eabs σ x) ∧ Eabs σ 0 = 0 ∧
      (∀ x, (∀ y, Eabs σ x ≤ Eabs σ y) → x = 0) ∧
      (∀ (x : E2) (l : Fin 2), ∃! y : ℝ, ∀ w, Eabs σ (upd x l y) ≤ Eabs σ (upd x l w)) := by
  have hC : ModC (Eabs σ) σ := by
    unfold ModC Eabs
    have := (convexOn_abs_lin 3 4).add (convexOn_abs_lin 1 (-2))
    refine this.congr fun x _ => ?_
    simp only [Pi.add_apply]; ring_nf
  have h0 : Eabs σ 0 = 0 := by simp [Eabs]
  have hnn : ∀ x, 0 ≤ Eabs σ x := fun x => by unfold Eabs; positivity
  refine ⟨hC, fun x => h0 ▸ hnn x, h0, fun x hx => ?_, fun x l => ?_⟩
  · have := hx 0
    rw [h0] at this
    have h2 : σ / 2 * ‖x‖ ^ 2 ≤ 0 := by
      unfold Eabs at this; nlinarith [abs_nonneg (3 * x 0 + 4 * x 1), abs_nonneg (x 0 - 2 * x 1)]
    have : ‖x‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg x])
  · have hS := slice_modC hC x l
    have hcont : Continuous (fun y : ℝ => Eabs σ (upd x l y)) :=
      (continuous_Eabs σ).comp (continuous_upd2 x l)
    obtain ⟨y, hy⟩ := exists_min_real hcont (a := σ / 2) (K := 0) (by positivity) (fun y => by
      have h1 := norm_sq_upd (X := fun _ => ℝ) x l y
      have h2 : 0 ≤ ∑ j ∈ Finset.univ.erase l, ‖x j‖ ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
      unfold Eabs
      rw [Real.norm_eq_abs, sq_abs] at h1
      nlinarith [abs_nonneg (3 * upd x l y 0 + 4 * upd x l y 1),
        abs_nonneg (upd x l y 0 - 2 * upd x l y 1)])
    refine ⟨y, hy, fun y' hy' => ?_⟩
    exact unique_of_minD (D := univ) (Ψ := slice (Eabs σ) x l) hσ hS (mem_univ y)
      (fun w _ => hy w) (mem_univ y') (fun w _ => hy' w)

/-- The fixed point x̄_t := (−4t, 3t). -/
noncomputable def xbar (t : ℝ) : E2 := !₂[-4 * t, 3 * t]

/-- **Proposition H4.10(a)**, the stall. For t ∈ (0, 1/(2σ)]: block 1 at x₂ = 3t has the
unique minimiser −4t (from any x₁), block 2 at x₁ = −4t has the unique minimiser 3t; so the
exact sweep maps every (x₁, 3t) to x̄_t and fixes x̄_t. Yet E_σ(x̄_t) − E* = 10t + 25σt²/2 > 0. -/
theorem H4_10_a_stall {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hst : σ * t ≤ 1 / 2) :
    (∀ x : E2, x 1 = 3 * t → ∀ w, Eabs σ (upd x 0 (-4 * t)) + σ / 2 * (w + 4 * t) ^ 2
        ≤ Eabs σ (upd x 0 w)) ∧
    (∀ x : E2, x 0 = -4 * t → ∀ w, Eabs σ (upd x 1 (3 * t)) + σ / 2 * (w - 3 * t) ^ 2
        ≤ Eabs σ (upd x 1 w)) ∧
    (∀ x x' : E2, x 1 = 3 * t → ExactSweep2 (Eabs σ) x x' → x' = xbar t) ∧
    ExactSweep2 (Eabs σ) (xbar t) (xbar t) ∧
    Eabs σ (xbar t) - Eabs σ 0 = 10 * t + 25 * σ * t ^ 2 / 2 ∧ 0 < Eabs σ (xbar t) - Eabs σ 0 := by
  have hb1 : ∀ x : E2, x 1 = 3 * t → ∀ w, Eabs σ (upd x 0 (-4 * t)) + σ / 2 * (w + 4 * t) ^ 2
      ≤ Eabs σ (upd x 0 w) := by
    intro x hx w
    simp only [Eabs, E2_norm_sq, upd00, upd01, hx]
    have hs : |(1 + 4 * σ * t) / 3| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have h1 : (1 + 4 * σ * t) / 3 * (3 * w + 4 * (3 * t)) ≤ |3 * w + 4 * (3 * t)| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs
    have h2 : -(w - 2 * (3 * t)) ≤ |w - 2 * (3 * t)| := neg_le_abs _
    have e1 : |3 * (-4 * t) + 4 * (3 * t)| = 0 := by ring_nf; simp
    have e2 : |-4 * t - 2 * (3 * t)| = 10 * t := by
      rw [show -4 * t - 2 * (3 * t) = -(10 * t) by ring, abs_neg, abs_of_pos (by linarith)]
    rw [e1, e2]
    nlinarith
  have hb2 : ∀ x : E2, x 0 = -4 * t → ∀ w, Eabs σ (upd x 1 (3 * t)) + σ / 2 * (w - 3 * t) ^ 2
      ≤ Eabs σ (upd x 1 w) := by
    intro x hx w
    simp only [Eabs, E2_norm_sq, upd10, upd11, hx]
    have hs : |-(2 + 3 * σ * t) / 4| ≤ 1 := by
      rw [abs_le]; constructor <;> nlinarith
    have h1 : -(2 + 3 * σ * t) / 4 * (3 * (-4 * t) + 4 * w) ≤ |3 * (-4 * t) + 4 * w| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hs
    have h2 : -(-4 * t - 2 * w) ≤ |-4 * t - 2 * w| := neg_le_abs _
    have e1 : |3 * (-4 * t) + 4 * (3 * t)| = 0 := by ring_nf; simp
    have e2 : |-4 * t - 2 * (3 * t)| = 10 * t := by
      rw [show -4 * t - 2 * (3 * t) = -(10 * t) by ring, abs_neg, abs_of_pos (by linarith)]
    rw [e1, e2]
    nlinarith
  -- uniqueness from the quadratic growth
  have hsweep : ∀ x x' : E2, x 1 = 3 * t → ExactSweep2 (Eabs σ) x x' → x' = xbar t := by
    intro x x' hx hsw
    have h0 : x' 0 = -4 * t := by
      have h1 := hb1 x hx (x' 0)
      have h2 := hsw.1 (-4 * t)
      have : (x' 0 + 4 * t) ^ 2 ≤ 0 := by nlinarith
      nlinarith [sq_nonneg (x' 0 + 4 * t)]
    have hx0 : (upd x 0 (x' 0)) 0 = -4 * t := by rw [upd00, h0]
    have h1' : x' 1 = 3 * t := by
      have h1 := hb2 _ hx0 (x' 1)
      have h2 := hsw.2 (3 * t)
      have : (x' 1 - 3 * t) ^ 2 ≤ 0 := by nlinarith
      nlinarith [sq_nonneg (x' 1 - 3 * t)]
    exact E2_ext (by rw [h0, xbar, v2_0]) (Or.inr (by rw [h1', xbar, v2_1]))
  have hx1 : xbar t 1 = 3 * t := v2_1 _ _
  have hx0 : xbar t 0 = -4 * t := v2_0 _ _
  have hfix : ExactSweep2 (Eabs σ) (xbar t) (xbar t) := by
    refine ⟨fun w => ?_, fun w => ?_⟩
    · rw [hx0]; have := hb1 (xbar t) hx1 w; nlinarith [sq_nonneg (w + 4 * t)]
    · rw [hx0]
      have hy : upd (xbar t) 0 (-4 * t) = xbar t := by rw [← hx0]; exact upd_self _ _
      rw [hy, hx1]
      have := hb2 (xbar t) hx0 w; nlinarith [sq_nonneg (w - 3 * t)]
  have hval : Eabs σ (xbar t) - Eabs σ 0 = 10 * t + 25 * σ * t ^ 2 / 2 := by
    rw [xbar, Eabs_v2, Eabs_zero, show 3 * (-4 * t) + 4 * (3 * t) = 0 by ring,
      show -4 * t - 2 * (3 * t) = -(10 * t) by ring, abs_zero, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < 10 * t)]
    ring
  refine ⟨hb1, hb2, hsweep, hfix, hval, by rw [hval]; positivity⟩

/-- **Proposition H4.10(a)**, the residual: dist(0, ∂E_σ(x̄_t)) = 2 + 5σt ≥ 2, attained at
u* = (−8/5 − 4σt, 6/5 + 3σt). -/
theorem H4_10_a_dist {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) :
    !₂[-8 / 5 - 4 * σ * t, 6 / 5 + 3 * σ * t] ∈ subdiff (Eabs σ) (xbar t) ∧
    ‖(!₂[-8 / 5 - 4 * σ * t, 6 / 5 + 3 * σ * t] : E2)‖ = 2 + 5 * σ * t ∧
    (∀ u ∈ subdiff (Eabs σ) (xbar t), 2 + 5 * σ * t ≤ ‖u‖) ∧
    Metric.infDist (0 : E2) (subdiff (Eabs σ) (xbar t)) = 2 + 5 * σ * t := by
  have hx0 : xbar t 0 = -4 * t := v2_0 _ _
  have hx1 : xbar t 1 = 3 * t := v2_1 _ _
  have hEx : Eabs σ (xbar t) = 10 * t + σ / 2 * (16 * t ^ 2 + 9 * t ^ 2) := by
    rw [xbar, Eabs_v2, show 3 * (-4 * t) + 4 * (3 * t) = 0 by ring,
      show -4 * t - 2 * (3 * t) = -(10 * t) by ring, abs_zero, abs_neg,
      abs_of_pos (by linarith : (0 : ℝ) < 10 * t)]
    ring
  have hmem : (!₂[-8 / 5 - 4 * σ * t, 6 / 5 + 3 * σ * t] : E2) ∈ subdiff (Eabs σ) (xbar t) := by
    intro y
    rw [hEx, E2_inner, PiLp.sub_apply, PiLp.sub_apply, v2_0, v2_1, hx0, hx1]
    simp only [Eabs, E2_norm_sq]
    have h1 : -(1 / 5) * (3 * y 0 + 4 * y 1) ≤ |3 * y 0 + 4 * y 1| := by
      refine (le_abs_self _).trans ?_
      rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) (by norm_num [abs_of_pos])
    have h2 : -(y 0 - 2 * y 1) ≤ |y 0 - 2 * y 1| := neg_le_abs _
    nlinarith [mul_nonneg hσ.le (sq_nonneg (y 0 + 4 * t)),
      mul_nonneg hσ.le (sq_nonneg (y 1 - 3 * t))]
  have hnorm : ‖(!₂[-8 / 5 - 4 * σ * t, 6 / 5 + 3 * σ * t] : E2)‖ = 2 + 5 * σ * t := by
    rw [norm_v2, show (-8 / 5 - 4 * σ * t) ^ 2 + (6 / 5 + 3 * σ * t) ^ 2 = (2 + 5 * σ * t) ^ 2 by
      ring]
    exact Real.sqrt_sq (by positivity)
  have hlow : ∀ u ∈ subdiff (Eabs σ) (xbar t), 2 + 5 * σ * t ≤ ‖u‖ := by
    intro u hu
    -- direction d = (4, −3)/5
    have key : ∀ r : ℝ, 0 < r → r ≤ 5 * t →
        r * ((4 / 5) * u 0 - (3 / 5) * u 1) ≤ r * (-(2 + 5 * σ * t)) + σ / 2 * r ^ 2 := by
      intro r hr hr5
      have h := hu !₂[-4 * t + 4 / 5 * r, 3 * t - 3 / 5 * r]
      rw [hEx, E2_inner, PiLp.sub_apply, PiLp.sub_apply, v2_0, v2_1, hx0, hx1, Eabs_v2,
        show 3 * (-4 * t + 4 / 5 * r) + 4 * (3 * t - 3 / 5 * r) = 0 by ring,
        show -4 * t + 4 / 5 * r - 2 * (3 * t - 3 / 5 * r) = -(10 * t - 2 * r) by ring,
        abs_zero, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 10 * t - 2 * r)] at h
      nlinarith
    have hdir : (4 / 5) * u 0 - (3 / 5) * u 1 ≤ -(2 + 5 * σ * t) := by
      apply le_of_forall_small (b := σ / 2 * (5 * t))
      intro s hs0 hs1
      have h := key (s * (5 * t)) (by positivity) (by nlinarith)
      have hpos : 0 < s * (5 * t) := by positivity
      have : s * (5 * t) * ((4 / 5) * u 0 - (3 / 5) * u 1)
          ≤ s * (5 * t) * (-(2 + 5 * σ * t) + s * (σ / 2 * (5 * t))) := by nlinarith
      exact le_of_mul_le_mul_left this hpos
    have hcs := real_inner_le_norm u (!₂[-(4 / 5), 3 / 5] : E2)
    rw [E2_inner, v2_0, v2_1, norm_v2,
      show (-(4 / 5) : ℝ) ^ 2 + (3 / 5) ^ 2 = 1 by norm_num, Real.sqrt_one] at hcs
    linarith
  refine ⟨hmem, hnorm, hlow, le_antisymm ?_ ?_⟩
  · have := Metric.infDist_le_dist_of_mem (x := (0 : E2)) hmem
    rwa [dist_comm, dist_zero_right, hnorm] at this
  · rw [Metric.le_infDist ⟨_, hmem⟩]
    intro u hu
    rw [dist_comm, dist_zero_right]; exact hlow u hu

/-! ### H4.10(d): an under-declared coupling constant gives a false rate -/

/-- E_c(x) := (x₁² + x₂²)/2 + c x₁x₂. -/
noncomputable def Eq2 (c : ℝ) (x : E2) : ℝ := (x 0 ^ 2 + x 1 ^ 2) / 2 + c * x 0 * x 1

/-- **Proposition H4.10(d).** 0 < |c| < 1: E_c ≥ 0 = E_c(0) (so E* = 0); the declaration
L₁₂ = 0 gives Λ = 0 and ρ = 0 (a claimed one-sweep solve); the exact sweep from (0, 1) is
(−c, c²) (unique), with a₁ = c²(1 − c²)/2 > 0 = ρa₀. -/
theorem H4_10_d {c : ℝ} (hc0 : c ≠ 0) (hc1 : |c| < 1) (τ : Fin 2 → ℝ) (σ : ℝ) :
    (∀ x, Eq2 c 0 ≤ Eq2 c x) ∧ Eq2 c 0 = 0 ∧
    Lam (fun _ _ => (0 : ℝ)) τ = 0 ∧ rho (Lam (fun _ _ => (0 : ℝ)) τ) σ = 0 ∧
    ExactSweep2 (Eq2 c) !₂[0, 1] !₂[-c, c ^ 2] ∧
    (∀ x', ExactSweep2 (Eq2 c) !₂[0, 1] x' → x' = !₂[-c, c ^ 2]) ∧
    Eq2 c !₂[-c, c ^ 2] - Eq2 c 0 = c ^ 2 * (1 - c ^ 2) / 2 ∧
    rho (Lam (fun _ _ => (0 : ℝ)) τ) σ * (Eq2 c !₂[0, 1] - Eq2 c 0)
      < Eq2 c !₂[-c, c ^ 2] - Eq2 c 0 := by
  have hc2 : c ^ 2 < 1 := by
    have := sq_lt_sq' (by linarith [neg_abs_le c, abs_nonneg c]) hc1
    simpa [sq_abs] using this
  have hcp : 0 < c ^ 2 := by positivity
  have hnn : ∀ x, 0 ≤ Eq2 c x := fun x => by
    unfold Eq2
    nlinarith [sq_nonneg (x 0 + c * x 1), sq_nonneg (x 1), mul_nonneg (sq_nonneg (x 1))
      (by linarith : (0 : ℝ) ≤ 1 - c ^ 2)]
  have h0 : Eq2 c 0 = 0 := by simp [Eq2]
  have hL : Lam (fun _ _ => (0 : ℝ)) τ = 0 := by simp [Lam, Lam2, cj2]
  have hρ : rho (Lam (fun _ _ => (0 : ℝ)) τ) σ = 0 := by rw [hL]; simp [rho]
  -- the two block problems
  have hb1 : ∀ w, Eq2 c (upd (!₂[0, 1] : E2) 0 (-c)) + (w + c) ^ 2 / 2
      ≤ Eq2 c (upd (!₂[0, 1] : E2) 0 w) := by
    intro w; simp [Eq2, upd00, upd01]; nlinarith
  have hb2 : ∀ w, Eq2 c (upd (upd (!₂[0, 1] : E2) 0 (-c)) 1 (c ^ 2)) + (w - c ^ 2) ^ 2 / 2
      ≤ Eq2 c (upd (upd (!₂[0, 1] : E2) 0 (-c)) 1 w) := by
    intro w; simp only [Eq2, upd10, upd11, upd00]; nlinarith
  have hsw : ExactSweep2 (Eq2 c) !₂[0, 1] !₂[-c, c ^ 2] := by
    refine ⟨fun w => ?_, fun w => ?_⟩
    · rw [v2_0]; have := hb1 w; nlinarith [sq_nonneg (w + c)]
    · rw [v2_0, v2_1]; have := hb2 w; nlinarith [sq_nonneg (w - c ^ 2)]
  have huniq : ∀ x', ExactSweep2 (Eq2 c) !₂[0, 1] x' → x' = !₂[-c, c ^ 2] := by
    intro x' h
    have e0 : x' 0 = -c := by
      have h1 := hb1 (x' 0); have h2 := h.1 (-c)
      nlinarith [sq_nonneg (x' 0 + c)]
    have e1 : x' 1 = c ^ 2 := by
      have h1 := hb2 (x' 1); have h2 := h.2 (c ^ 2); rw [e0] at h2
      nlinarith [sq_nonneg (x' 1 - c ^ 2)]
    exact E2_ext (by rw [e0, v2_0]) (Or.inr (by rw [e1, v2_1]))
  have hval : Eq2 c !₂[-c, c ^ 2] - Eq2 c 0 = c ^ 2 * (1 - c ^ 2) / 2 := by
    rw [h0, Eq2, v2_0, v2_1]; ring
  refine ⟨fun x => h0 ▸ hnn x, h0, hL, hρ, hsw, huniq, hval, ?_⟩
  rw [hρ, zero_mul, hval]
  have : 0 < 1 - c ^ 2 := by linarith
  positivity

lemma differentiable_Eq2 (c : ℝ) : Differentiable ℝ (Eq2 c) := by unfold Eq2; fun_prop

lemma gradient_Eq2 (c : ℝ) (x : E2) :
    gradient (Eq2 c) x 0 = x 0 + c * x 1 ∧ gradient (Eq2 c) x 1 = x 1 + c * x 0 := by
  constructor
  · apply gradient_E2 (differentiable_Eq2 c)
    have e : slice (Eq2 c) x 0 = fun y => (y ^ 2 + x 1 ^ 2) / 2 + c * y * x 1 := by
      funext y; simp only [slice, Eq2, upd00, upd01]
    rw [e]
    have h := (((hasDerivAt_pow 2 (x 0)).add_const (x 1 ^ 2)).div_const 2).add
      (((hasDerivAt_id (x 0)).const_mul c).mul_const (x 1))
    exact h.congr_deriv (by norm_num)
  · apply gradient_E2 (differentiable_Eq2 c)
    have e : slice (Eq2 c) x 1 = fun y => (x 0 ^ 2 + y ^ 2) / 2 + c * x 0 * y := by
      funext y; simp only [slice, Eq2, upd10, upd11]
    rw [e]
    have h := (((hasDerivAt_pow 2 (x 1)).const_add (x 0 ^ 2)).div_const 2).add
      ((hasDerivAt_id (x 1)).const_mul (c * x 0))
    exact h.congr_deriv (by norm_num)

/-- **Proposition H4.10(d)**, the declarations: L_{jl} := |c| is a valid (SD6) cross constant
for E_c, and the declaration L₁₂ = 0 is not (it under-declares the coupling). -/
theorem H4_10_d_cross {c : ℝ} (hc0 : c ≠ 0) :
    CrossConst (Eq2 c) (fun _ _ => |c|) ∧ ¬ CrossConst (Eq2 c) (fun _ _ => 0) := by
  have key : ∀ (x : E2) (l j : Fin 2), j ≠ l → ∀ h : ℝ,
      ‖gradient (Eq2 c) (x + U (X := fun _ => ℝ) l h) j - gradient (Eq2 c) x j‖ = |c| * ‖h‖ := by
    intro x l j hjl h
    rw [add_U_eq_upd]
    fin_cases l <;> fin_cases j
    · exact absurd rfl hjl
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [(gradient_Eq2 c _).2, (gradient_Eq2 c _).2, upd00, upd01]
      rw [show x 1 + c * (x 0 + h) - (x 1 + c * x 0) = c * h by ring, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul]
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [(gradient_Eq2 c _).1, (gradient_Eq2 c _).1, upd10, upd11]
      rw [show x 0 + c * (x 1 + h) - (x 0 + c * x 1) = c * h by ring, Real.norm_eq_abs,
        Real.norm_eq_abs, abs_mul]
    · exact absurd rfl hjl
  refine ⟨fun x l j hjl h => (key x l j hjl h).le, fun hL => ?_⟩
  have h1 := hL 0 1 0 (by decide) 1
  rw [key 0 1 0 (by decide) 1] at h1
  simp at h1
  exact hc0 h1

/-! ### H4.10(b): without strong convexity, no linear rate -/

/-- E(x) := (x₁ − x₂)²/2 + x₁⁴/4. -/
noncomputable def Equart (x : E2) : ℝ := (x 0 - x 1) ^ 2 / 2 + x 0 ^ 4 / 4

lemma differentiable_Equart : Differentiable ℝ Equart := by unfold Equart; fun_prop

lemma gradient_Equart (x : E2) :
    gradient Equart x 0 = x 0 - x 1 + x 0 ^ 3 ∧ gradient Equart x 1 = x 1 - x 0 := by
  constructor
  · apply gradient_E2 differentiable_Equart
    have e : slice Equart x 0 = fun y => (y - x 1) ^ 2 / 2 + y ^ 4 / 4 := by
      funext y; simp only [slice, Equart, upd00, upd01]
    rw [e]
    have h := ((((hasDerivAt_id (x 0)).sub_const (x 1)).pow 2).div_const 2).add
      ((hasDerivAt_pow 4 (x 0)).div_const 4)
    exact h.congr_deriv (by norm_num)
  · apply gradient_E2 differentiable_Equart
    have e : slice Equart x 1 = fun y => (x 0 - y) ^ 2 / 2 + x 0 ^ 4 / 4 := by
      funext y; simp only [slice, Equart, upd10, upd11]
    rw [e]
    have h := ((((hasDerivAt_id (x 1)).const_sub (x 0)).pow 2).div_const 2).add_const
      (x 0 ^ 4 / 4)
    exact h.congr_deriv (by norm_num; ring)

/-- The quartic step t ↦ t + t³ is a bijection of ℝ: every block-1 problem has exactly one
stationary point. -/
lemma cubic_root (c : ℝ) : ∃! t : ℝ, t + t ^ 3 = c := by
  have hmono : StrictMono (fun t : ℝ => t + t ^ 3) :=
    strictMono_id.add (Odd.strictMono_pow (by decide))
  refine existsUnique_of_exists_of_unique ?_ fun a b ha hb => hmono.injective (ha.trans hb.symm)
  have hcont : Continuous (fun t : ℝ => t + t ^ 3) := by fun_prop
  have hlo : (-(|c| + 1)) + (-(|c| + 1)) ^ 3 ≤ c := by
    nlinarith [abs_nonneg c, neg_abs_le c, sq_nonneg (|c| + 1)]
  have hhi : c ≤ (|c| + 1) + (|c| + 1) ^ 3 := by
    nlinarith [abs_nonneg c, le_abs_self c, sq_nonneg (|c| + 1)]
  obtain ⟨t, -, ht⟩ := intermediate_value_Icc (by linarith [abs_nonneg c]) hcont.continuousOn
    ⟨hlo, hhi⟩
  exact ⟨t, ht⟩

/-- **Proposition H4.10(b)**, the energy: E is convex and smooth, E ≥ 0 = E(0) with 0 the
unique minimiser, the cross constants L₁₂ = L₂₁ = 1 are valid, but no σ > 0 satisfies
C(E, σ) (σ = 0 is the best modulus). -/
theorem H4_10_b_energy :
    ModC Equart 0 ∧ Differentiable ℝ Equart ∧ (∀ x, Equart 0 ≤ Equart x) ∧ Equart 0 = 0 ∧
      (∀ x, Equart x = 0 → x = 0) ∧ CrossConst Equart (fun _ _ => 1) ∧
      (∀ σ : ℝ, 0 < σ → ¬ ModC Equart σ) := by
  have h0 : Equart 0 = 0 := by simp [Equart]
  have hconv : ModC Equart 0 := by
    unfold ModC
    have h1 : ConvexOn ℝ univ (fun x : E2 => (x 0 - x 1) ^ 2 / 2) := by
      have := ((Even.convexOn_pow (𝕜 := ℝ) (n := 2) (by decide)).comp_linearMap
        ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0 - LinearMap.proj 1).comp
          (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
      refine this.congr fun x _ => ?_
      simp; ring
    have h2 : ConvexOn ℝ univ (fun x : E2 => x 0 ^ 4 / 4) := by
      have := ((Even.convexOn_pow (𝕜 := ℝ) (n := 4) (by decide)).comp_linearMap
        ((LinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 0).comp
          (WithLp.linearEquiv 2 ℝ (Fin 2 → ℝ)).toLinearMap)).smul (by norm_num : (0 : ℝ) ≤ 1 / 4)
      refine this.congr fun x _ => ?_
      simp; ring
    refine (h1.add h2).congr fun x _ => ?_
    simp [Equart]
  have hnn : ∀ x, 0 ≤ Equart x := fun x => by unfold Equart; positivity
  refine ⟨hconv, differentiable_Equart, fun x => h0 ▸ hnn x, h0, fun x hx => ?_, ?_, ?_⟩
  · unfold Equart at hx
    have ha : x 0 = 0 := by
      have h4 : x 0 ^ 4 ≤ 0 := by nlinarith [sq_nonneg (x 0 - x 1)]
      exact pow_eq_zero_iff (by norm_num) |>.1 (le_antisymm h4 (by positivity))
    have hb : x 1 = 0 := by rw [ha] at hx; nlinarith [sq_nonneg (x 1)]
    exact E2_ext (by rw [ha]; rfl) (Or.inr (by rw [hb]; rfl))
  · intro x l j hjl h
    rw [add_U_eq_upd]
    fin_cases l <;> fin_cases j
    · exact absurd rfl hjl
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [(gradient_Equart _).2, (gradient_Equart _).2, upd00, upd01,
        show x 1 - (x 0 + h) - (x 1 - x 0) = -h by ring, norm_neg, one_mul]
    · simp only [Fin.zero_eta, Fin.mk_one]
      rw [(gradient_Equart _).1, (gradient_Equart _).1, upd10, upd11,
        show x 0 - (x 1 + h) + x 0 ^ 3 - (x 0 - x 1 + x 0 ^ 3) = -h by ring, norm_neg, one_mul]
    · exact absurd rfl hjl
  · intro σ hσ hC
    set r := √σ
    have hr2 : r ^ 2 = σ := Real.sq_sqrt hσ.le
    have hr0 : 0 < r := Real.sqrt_pos.2 hσ
    have h := hC.2 (mem_univ (!₂[r, r] : E2)) (mem_univ (!₂[-r, -r] : E2))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hmid : (1 / 2 : ℝ) • (!₂[r, r] : E2) + (1 / 2 : ℝ) • (!₂[-r, -r] : E2) = 0 := by
      ext i; fin_cases i <;> simp
    rw [hmid] at h
    simp only [smul_eq_mul, Equart, E2_norm_sq] at h
    simp at h
    nlinarith [pow_pos hr0 2, pow_pos hr0 4]

/-- **Proposition H4.10(b)**, the block problems. Block 1 at x₂ = c: the root t of
t + t³ = c is the unique minimiser of w ↦ E(w, c) (with quadratic growth); block 2 at x₁ = d:
w = d is the unique minimiser of w ↦ E(d, w). -/
lemma Equart_blocks :
    (∀ (x : E2) (t : ℝ), t + t ^ 3 = x 1 → ∀ w,
      Equart (upd x 0 t) + (w - t) ^ 2 / 2 ≤ Equart (upd x 0 w)) ∧
    (∀ (x : E2) w, Equart (upd x 1 (x 0)) + (w - x 0) ^ 2 / 2 ≤ Equart (upd x 1 w)) := by
  constructor
  · intro x t ht w
    simp only [Equart, upd00, upd01]
    rw [← ht]
    nlinarith [mul_nonneg (sq_nonneg (w - t)) (add_nonneg (sq_nonneg (w + t)) (sq_nonneg t)),
      sq_nonneg (w - t)]
  · intro x w
    simp only [Equart, upd10, upd11]
    nlinarith [sq_nonneg (w - x 0)]

/-- **Proposition H4.10(b)**, the run. Let s₀ > 0 and s_{k+1} + s_{k+1}³ = s_k (such a sequence
exists and is unique by `cubic_root`). Then exact cyclic minimisation from (s₀, s₀) is
x^k = (s_k, s_k) (the exact sweep from (s_k, s_k) is (s_{k+1}, s_{k+1}), uniquely);
a_k = s_k⁴/4; 0 < s_{k+1} < s_k, s_k → 0; a_{k+1}/a_k = (1 + s_{k+1}²)^{−4} → 1; and no ρ' < 1
satisfies a_{k+1} ≤ ρ'a_k for all k. -/
theorem H4_10_b_run {s : ℕ → ℝ} (hs0 : 0 < s 0) (hs : ∀ k, s (k + 1) + s (k + 1) ^ 3 = s k) :
    (∀ k, ExactSweep2 Equart !₂[s k, s k] !₂[s (k + 1), s (k + 1)]) ∧
    (∀ k x', ExactSweep2 Equart !₂[s k, s k] x' → x' = !₂[s (k + 1), s (k + 1)]) ∧
    (∀ k, Equart !₂[s k, s k] - Equart 0 = s k ^ 4 / 4) ∧
    (∀ k, 0 < s (k + 1) ∧ s (k + 1) < s k) ∧ Tendsto s atTop (𝓝 0) ∧
    (∀ k, (Equart !₂[s (k + 1), s (k + 1)] - Equart 0) / (Equart !₂[s k, s k] - Equart 0)
        = ((1 + s (k + 1) ^ 2) ^ 4)⁻¹) ∧
    Tendsto (fun k => (Equart !₂[s (k + 1), s (k + 1)] - Equart 0)
        / (Equart !₂[s k, s k] - Equart 0)) atTop (𝓝 1) ∧
    ¬ ∃ ρ' < 1, ∀ k, Equart !₂[s (k + 1), s (k + 1)] - Equart 0
        ≤ ρ' * (Equart !₂[s k, s k] - Equart 0) := by
  obtain ⟨hb1, hb2⟩ := Equart_blocks
  have h0 : Equart 0 = 0 := by simp [Equart]
  have hval : ∀ k, Equart !₂[s k, s k] - Equart 0 = s k ^ 4 / 4 := by
    intro k; rw [h0, Equart, v2_0, v2_1]; ring
  have hpos : ∀ k, 0 < s k := by
    intro k
    induction k with
    | zero => exact hs0
    | succ k ih =>
      by_contra hneg'
      have hneg := not_lt.1 hneg'
      have := hs k
      nlinarith [pow_two_nonneg (s (k + 1)), mul_nonneg (pow_two_nonneg (s (k + 1)))
        (by linarith : (0 : ℝ) ≤ -s (k + 1))]
  have hdec : ∀ k, s (k + 1) < s k := by
    intro k; have := hs k; have := hpos (k + 1); nlinarith [pow_pos (hpos (k + 1)) 3]
  -- the sweep
  have hsweep : ∀ k, ExactSweep2 Equart !₂[s k, s k] !₂[s (k + 1), s (k + 1)] := by
    intro k
    refine ⟨fun w => ?_, fun w => ?_⟩
    · rw [v2_0]
      have := hb1 !₂[s k, s k] (s (k + 1)) (by rw [v2_1]; exact hs k) w
      nlinarith [sq_nonneg (w - s (k + 1))]
    · rw [v2_0, v2_1]
      have h := hb2 (upd !₂[s k, s k] 0 (s (k + 1))) w
      rw [upd00] at h
      nlinarith [sq_nonneg (w - s (k + 1))]
  have huniq : ∀ k x', ExactSweep2 Equart !₂[s k, s k] x' → x' = !₂[s (k + 1), s (k + 1)] := by
    intro k x' h
    have e0 : x' 0 = s (k + 1) := by
      have h1 := hb1 !₂[s k, s k] (s (k + 1)) (by rw [v2_1]; exact hs k) (x' 0)
      have h2 := h.1 (s (k + 1))
      nlinarith [sq_nonneg (x' 0 - s (k + 1))]
    have e1 : x' 1 = s (k + 1) := by
      have h1 := hb2 (upd !₂[s k, s k] 0 (x' 0)) (x' 1)
      have h2 := h.2 (upd !₂[s k, s k] 0 (x' 0) 0)
      rw [upd00] at h1 h2
      rw [e0] at h1 h2
      nlinarith [sq_nonneg (x' 1 - s (k + 1))]
    exact E2_ext (by rw [e0, v2_0]) (Or.inr (by rw [e1, v2_1]))
  -- convergence s_k → 0
  have hanti : Antitone s := antitone_nat_of_succ_le fun k => (hdec k).le
  have hbdd : BddBelow (Set.range s) := ⟨0, by rintro _ ⟨k, rfl⟩; exact (hpos k).le⟩
  have hlim := tendsto_atTop_ciInf hanti hbdd
  set Ls := ⨅ i, s i
  have hlim1 : Tendsto (fun k => s (k + 1)) atTop (𝓝 Ls) := hlim.comp (tendsto_add_atTop_nat 1)
  have hL : Ls + Ls ^ 3 = Ls := by
    have h1 : Tendsto (fun k => s (k + 1) + s (k + 1) ^ 3) atTop (𝓝 (Ls + Ls ^ 3)) :=
      hlim1.add (hlim1.pow 3)
    have h2 : (fun k => s (k + 1) + s (k + 1) ^ 3) = s := funext hs
    rw [h2] at h1
    exact tendsto_nhds_unique h1 hlim
  have hL0 : Ls = 0 := by
    have : Ls ^ 3 = 0 := by linarith
    exact pow_eq_zero_iff (by norm_num) |>.1 this
  rw [hL0] at hlim hlim1
  -- the ratio
  have hratio : ∀ k, (Equart !₂[s (k + 1), s (k + 1)] - Equart 0) / (Equart !₂[s k, s k] - Equart 0)
      = ((1 + s (k + 1) ^ 2) ^ 4)⁻¹ := by
    intro k
    rw [hval, hval, ← hs k]
    have := hpos (k + 1)
    have : 0 < 1 + s (k + 1) ^ 2 := by positivity
    field_simp
  have hrt : Tendsto (fun k => ((1 + s (k + 1) ^ 2) ^ 4)⁻¹) atTop (𝓝 1) := by
    have h1 : Tendsto (fun k => ((1 + s (k + 1) ^ 2) ^ 4)⁻¹) atTop (𝓝 (((1 + 0 ^ 2) ^ 4)⁻¹)) :=
      ((tendsto_const_nhds.add (hlim1.pow 2)).pow 4).inv₀ (by norm_num)
    simpa using h1
  have hrt' : Tendsto (fun k => (Equart !₂[s (k + 1), s (k + 1)] - Equart 0)
      / (Equart !₂[s k, s k] - Equart 0)) atTop (𝓝 1) := by
    simp only [hratio]; exact hrt
  refine ⟨hsweep, huniq, hval, fun k => ⟨hpos (k + 1), hdec k⟩, hlim, hratio, hrt', ?_⟩
  rintro ⟨ρ', hρ', hrate⟩
  have hle : ∀ k, (Equart !₂[s (k + 1), s (k + 1)] - Equart 0)
      / (Equart !₂[s k, s k] - Equart 0) ≤ ρ' := by
    intro k
    have hak : 0 < Equart !₂[s k, s k] - Equart 0 := by rw [hval]; have := hpos k; positivity
    rw [div_le_iff₀ hak]; exact hrate k
  have := le_of_tendsto' hrt' hle
  linarith

/-- The sequence of H4.10(b): s₀ given, s_{k+1} the root of t + t³ = s_k. -/
noncomputable def qseq (s0 : ℝ) : ℕ → ℝ
  | 0 => s0
  | k + 1 => Classical.choose (cubic_root (qseq s0 k)).exists

lemma qseq_spec (s0 : ℝ) (k : ℕ) : qseq s0 (k + 1) + qseq s0 (k + 1) ^ 3 = qseq s0 k :=
  Classical.choose_spec (cubic_root (qseq s0 k)).exists

/-! ### H4.10(c): the declared coupling constant is load-bearing (Huber smoothing, as a limit) -/

/-- The Huber function h_μ(s) = s²/(2μ) for |s| ≤ μ, |s| − μ/2 otherwise. -/
noncomputable def hub (μ w : ℝ) : ℝ := if |w| ≤ μ then w ^ 2 / (2 * μ) else |w| - μ / 2

/-- Its slope (a subgradient): clamp(a/μ, −1, 1). -/
noncomputable def hubd (μ a : ℝ) : ℝ := max (-1) (min 1 (a / μ))

lemma hub_close {μ : ℝ} (hμ : 0 < μ) (w : ℝ) : 0 ≤ |w| - hub μ w ∧ |w| - hub μ w ≤ μ / 2 := by
  unfold hub
  split_ifs with h
  · have ha := abs_nonneg w
    have e : |w| - w ^ 2 / (2 * μ) = |w| * (2 * μ - |w|) / (2 * μ) := by
      rw [← sq_abs w]; field_simp
    rw [e]
    constructor
    · apply div_nonneg _ (by positivity); nlinarith
    · rw [div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (μ - |w|)]
  · constructor <;> linarith

lemma hub_nonneg {μ : ℝ} (hμ : 0 < μ) (w : ℝ) : 0 ≤ hub μ w := by
  unfold hub; split_ifs with h
  · positivity
  · push Not at h; linarith

/-- The supporting line of h_μ at every a: h_μ(w) ≥ h_μ(a) + clamp(a/μ)(w − a). -/
lemma hub_support {μ : ℝ} (hμ : 0 < μ) (a w : ℝ) : hub μ a + hubd μ a * (w - a) ≤ hub μ w := by
  unfold hub hubd
  have hμ' : μ ≠ 0 := hμ.ne'
  rcases le_or_gt (|a|) μ with ha | ha
  · have h1 : -1 ≤ a / μ := by rw [le_div_iff₀ hμ]; linarith [neg_abs_le a]
    have h2 : a / μ ≤ 1 := by rw [div_le_iff₀ hμ]; linarith [le_abs_self a]
    rw [min_eq_right h2, max_eq_right h1, if_pos ha]
    split_ifs with hw
    · rw [show w ^ 2 / (2 * μ) = a ^ 2 / (2 * μ) + a / μ * (w - a) + (w - a) ^ 2 / (2 * μ) by
        field_simp; ring]
      have : 0 ≤ (w - a) ^ 2 / (2 * μ) := by positivity
      linarith
    · -- |w| > μ ≥ |a|: the quadratic minorant is below |w| − μ/2
      push Not at hw
      have key : a ^ 2 / (2 * μ) + a / μ * (w - a) ≤ |w| - μ / 2 := by
        have e : a ^ 2 / (2 * μ) + a / μ * (w - a) = (2 * a * w - a ^ 2) / (2 * μ) := by
          field_simp; ring
        rw [e, div_le_iff₀ (by positivity)]
        have hw' : a * w ≤ |a| * |w| := by rw [← abs_mul]; exact le_abs_self _
        nlinarith [sq_nonneg (|a| - μ), abs_nonneg a, sq_abs a]
      exact key
  · rcases lt_or_ge a 0 with ha0 | ha0
    · have hab : a < -μ := by rw [abs_of_neg ha0] at ha; linarith
      have h1 : a / μ < -1 := by rw [div_lt_iff₀ hμ]; linarith
      rw [min_eq_right (by linarith), max_eq_left h1.le, if_neg (not_le.2 ha), abs_of_neg ha0]
      split_ifs with hw
      · have : w ^ 2 / (2 * μ) - (-a - μ / 2 + -1 * (w - a)) = (w + μ) ^ 2 / (2 * μ) := by
          field_simp; ring
        have : 0 ≤ (w + μ) ^ 2 / (2 * μ) := by positivity
        linarith
      · linarith [neg_le_abs w]
    · have hab : μ < a := by rw [abs_of_nonneg ha0] at ha; exact ha
      have h1 : 1 < a / μ := by rw [lt_div_iff₀ hμ]; linarith
      rw [min_eq_left h1.le, max_eq_right (by norm_num), if_neg (not_le.2 ha), abs_of_nonneg ha0]
      split_ifs with hw
      · have : w ^ 2 / (2 * μ) - (a - μ / 2 + 1 * (w - a)) = (w - μ) ^ 2 / (2 * μ) := by
          field_simp; ring
        have : 0 ≤ (w - μ) ^ 2 / (2 * μ) := by positivity
        linarith
      · linarith [le_abs_self w]

lemma hubd_of_abs_le {μ a : ℝ} (hμ : 0 < μ) (ha : |a| ≤ μ) : hubd μ a = a / μ := by
  have h1 : -1 ≤ a / μ := by rw [le_div_iff₀ hμ]; linarith [neg_abs_le a]
  have h2 : a / μ ≤ 1 := by rw [div_le_iff₀ hμ]; linarith [le_abs_self a]
  unfold hubd; rw [min_eq_right h2, max_eq_right h1]

lemma hubd_of_le {μ a : ℝ} (hμ : 0 < μ) (ha : a ≤ -μ) : hubd μ a = -1 := by
  have h1 : a / μ ≤ -1 := by rw [div_le_iff₀ hμ]; linarith
  unfold hubd; rw [min_eq_right (by linarith), max_eq_left h1]

lemma convexOn_hub_lin {μ : ℝ} (hμ : 0 < μ) (a b : ℝ) :
    ConvexOn ℝ univ (fun x : E2 => hub μ (a * x 0 + b * x 1)) := by
  refine ⟨convex_univ, fun x _ y _ p q hp hq hpq => ?_⟩
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  set m := a * (p * x 0 + q * y 0) + b * (p * x 1 + q * y 1)
  have hm : m = p * (a * x 0 + b * x 1) + q * (a * y 0 + b * y 1) := by simp only [m]; ring
  have h1 := hub_support hμ m (a * x 0 + b * x 1)
  have h2 := hub_support hμ m (a * y 0 + b * y 1)
  have e : p * (hubd μ m * (a * x 0 + b * x 1 - m)) + q * (hubd μ m * (a * y 0 + b * y 1 - m))
      = 0 := by
    have : p * (a * x 0 + b * x 1 - m) + q * (a * y 0 + b * y 1 - m) = 0 := by
      rw [hm]; have : q = 1 - p := by linarith
      subst this; ring
    linear_combination hubd μ m * this
  have hs := add_le_add (mul_le_mul_of_nonneg_left h1 hp) (mul_le_mul_of_nonneg_left h2 hq)
  have hpq' : p * hub μ m + q * hub μ m = hub μ m := by rw [← add_mul, hpq, one_mul]
  rw [mul_add, mul_add] at hs
  linarith

/-- E^μ(x) := h_μ(3x₁ + 4x₂) + h_μ(x₁ − 2x₂) + (σ/2)‖x‖². -/
noncomputable def Ehub (μ σ : ℝ) (x : E2) : ℝ :=
  hub μ (3 * x 0 + 4 * x 1) + hub μ (x 0 - 2 * x 1) + σ / 2 * ‖x‖ ^ 2

lemma Ehub_close {μ σ : ℝ} (hμ : 0 < μ) (x : E2) : |Ehub μ σ x - Eabs σ x| ≤ μ := by
  have h1 := hub_close hμ (3 * x 0 + 4 * x 1)
  have h2 := hub_close hμ (x 0 - 2 * x 1)
  unfold Ehub Eabs
  rw [abs_le]; constructor <;> linarith

/-- **Proposition H4.10(c)**, the declared numbers. C(E^μ, σ) (SD4, σ_C = 0) and τ₂ = σ is a
valid slice modulus (SD5); E^μ ≥ 0 = E^μ(0). With L₁₂ = 12/μ (the cross constant of the
dossier) and τ₂ = σ: Λ² = 144/(μ²σ) and ρ = 144/(144 + μ²σ²) → 1 as μ → 0⁺. -/
theorem H4_10_c_decl {σ : ℝ} (hσ : 0 < σ) :
    (∀ μ, 0 < μ → ModC (Ehub μ σ) σ ∧ SliceMod (Ehub μ σ) (fun _ => σ) ∧
      (∀ x, Ehub μ σ 0 ≤ Ehub μ σ x) ∧ Ehub μ σ 0 = 0) ∧
    (∀ μ, 0 < μ → rho √((12 / μ) ^ 2 / σ) σ = 144 / (144 + μ ^ 2 * σ ^ 2)) ∧
    Tendsto (fun μ => 144 / (144 + μ ^ 2 * σ ^ 2)) (𝓝[>] 0) (𝓝 1) := by
  refine ⟨fun μ hμ => ?_, fun μ hμ => ?_, ?_⟩
  · have hC : ModC (Ehub μ σ) σ := by
      unfold ModC Ehub
      refine ((convexOn_hub_lin hμ 3 4).add (convexOn_hub_lin hμ 1 (-2))).congr fun x _ => ?_
      simp only [Pi.add_apply]; ring_nf
    have h0 : Ehub μ σ 0 = 0 := by simp [Ehub, hub, hμ.le]
    refine ⟨hC, slice_modC hC, fun x => ?_, h0⟩
    rw [h0]; unfold Ehub
    have := hub_nonneg hμ (3 * x 0 + 4 * x 1); have := hub_nonneg hμ (x 0 - 2 * x 1)
    positivity
  · unfold rho
    rw [Real.sq_sqrt (by positivity)]
    field_simp
    ring
  · have : Tendsto (fun μ : ℝ => 144 / (144 + μ ^ 2 * σ ^ 2)) (𝓝 0)
        (𝓝 (144 / (144 + 0 ^ 2 * σ ^ 2))) := by
      apply Tendsto.div tendsto_const_nhds _ (by norm_num)
      exact tendsto_const_nhds.add ((tendsto_id.pow 2).mul_const _)
    simpa using this.mono_left nhdsWithin_le_nhds

/-- The explicit exact block maps of E^μ near x̄_t: block 1 at x₂ = c returns
y(μ, c) = (μ − 12c)/(9 + μσ); block 2 at x₁ = y returns s(μ, y) = −(12y + 2μ)/(16 + μσ). -/
noncomputable def hy (μ σ c : ℝ) : ℝ := (μ - 12 * c) / (9 + μ * σ)
noncomputable def hs (μ σ y : ℝ) : ℝ := -(12 * y + 2 * μ) / (16 + μ * σ)

/-- The exact-sweep recursion for the second coordinate, from c₀ = 3t. -/
noncomputable def cseq (μ σ t : ℝ) : ℕ → ℝ
  | 0 => 3 * t
  | k + 1 => hs μ σ (hy μ σ (cseq μ σ t k))

/-- Block 1 of E^μ: for 0 < μ ≤ t, c ∈ [3t/2, 3t], σt ≤ 1/2, y(μ, c) minimises w ↦ E^μ(w, c)
with quadratic growth. -/
lemma Ehub_block0 {μ σ t c : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (ht : 0 < t) (hst : σ * t ≤ 1 / 2)
    (hμt : μ ≤ t) (hc1 : 3 * t / 2 ≤ c) (hc2 : c ≤ 3 * t) (x : E2) (hx : x 1 = c) (w : ℝ) :
    Ehub μ σ (upd x 0 (hy μ σ c)) + σ / 2 * (w - hy μ σ c) ^ 2 ≤ Ehub μ σ (upd x 0 w) := by
  set y := hy μ σ c with hydef
  have hd : 0 < 9 + μ * σ := by positivity
  have hμσ : μ * σ ≤ 1 / 2 := by nlinarith
  have e1 : 3 * y + 4 * c = μ * ((3 + 4 * c * σ) / (9 + μ * σ)) := by
    rw [hydef, hy]; field_simp; ring
  have hz1 : |3 * y + 4 * c| ≤ μ := by
    rw [e1, abs_mul, abs_of_pos hμ]
    have : |(3 + 4 * c * σ) / (9 + μ * σ)| ≤ 1 := by
      rw [abs_le]; constructor
      · rw [le_div_iff₀ hd]; nlinarith
      · rw [div_le_iff₀ hd]; nlinarith
    nlinarith [abs_nonneg ((3 + 4 * c * σ) / (9 + μ * σ))]
  have hz2 : y - 2 * c ≤ -μ := by
    rw [hydef, hy, div_sub' hd.ne', div_le_iff₀ hd]; nlinarith
  have hfoc : 3 * ((3 * y + 4 * c) / μ) - 1 + σ * y = 0 := by
    rw [e1, hydef, hy]; field_simp; ring
  have h1 := hub_support hμ (3 * y + 4 * c) (3 * w + 4 * c)
  have h2 := hub_support hμ (y - 2 * c) (w - 2 * c)
  rw [hubd_of_abs_le hμ hz1] at h1
  rw [hubd_of_le hμ hz2] at h2
  simp only [Ehub, E2_norm_sq, upd00, upd01, hx]
  have hprod : (w - y) * (3 * ((3 * y + 4 * c) / μ) - 1 + σ * y) = 0 := by rw [hfoc, mul_zero]
  nlinarith

/-- Block 2 of E^μ: with y = y(μ, c) as above, s(μ, y) minimises w ↦ E^μ(y, w). -/
lemma Ehub_block1 {μ σ t c : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) (ht : 0 < t) (hst : σ * t ≤ 1 / 2)
    (hμt : μ ≤ t) (hc1 : 3 * t / 2 ≤ c) (hc2 : c ≤ 3 * t) (x : E2) (hx : x 0 = hy μ σ c)
    (w : ℝ) :
    Ehub μ σ (upd x 1 (hs μ σ (hy μ σ c))) + σ / 2 * (w - hs μ σ (hy μ σ c)) ^ 2
      ≤ Ehub μ σ (upd x 1 w) := by
  set y := hy μ σ c with hydef
  set z := hs μ σ y with hzdef
  have hd : 0 < 9 + μ * σ := by positivity
  have hd' : 0 < 16 + μ * σ := by positivity
  have hμσ : μ * σ ≤ 1 / 2 := by nlinarith
  -- bounds on y
  have hyup : y ≤ (μ - 18 * t) / (9 + μ * σ) := by
    rw [hydef, hy]; exact div_le_div_of_nonneg_right (by linarith) hd.le
  have hylo : -4 * t ≤ y := by
    rw [hydef, hy, le_div_iff₀ hd]; nlinarith [mul_pos (mul_pos ht hμ) hσ]
  have hyneg : y < 0 := by
    have : (μ - 18 * t) / (9 + μ * σ) < 0 := div_neg_of_neg_of_pos (by linarith) hd
    linarith
  have e1 : 3 * y + 4 * z = μ * ((3 * σ * y - 8) / (16 + μ * σ)) := by
    rw [hzdef, hs]; field_simp; ring
  have hz1 : |3 * y + 4 * z| ≤ μ := by
    rw [e1, abs_mul, abs_of_pos hμ]
    have : |(3 * σ * y - 8) / (16 + μ * σ)| ≤ 1 := by
      rw [abs_le]; constructor
      · rw [le_div_iff₀ hd']; nlinarith
      · rw [div_le_iff₀ hd']; nlinarith
    nlinarith [abs_nonneg ((3 * σ * y - 8) / (16 + μ * σ))]
  have hz2 : y - 2 * z ≤ -μ := by
    have e2 : y - 2 * z = (40 * y + μ * σ * y + 4 * μ) / (16 + μ * σ) := by
      rw [hzdef, hs]; field_simp; ring
    rw [e2, div_le_iff₀ hd']
    have hy9 : y * (9 + μ * σ) ≤ μ - 18 * t := by rwa [le_div_iff₀ hd] at hyup
    nlinarith
  have hfoc : 4 * ((3 * y + 4 * z) / μ) + 2 + σ * z = 0 := by
    rw [e1, hzdef, hs]; field_simp; ring
  have h1 := hub_support hμ (3 * y + 4 * z) (3 * y + 4 * w)
  have h2 := hub_support hμ (y - 2 * z) (y - 2 * w)
  rw [hubd_of_abs_le hμ hz1] at h1
  rw [hubd_of_le hμ hz2] at h2
  simp only [Ehub, E2_norm_sq, upd10, upd11, hx]
  have hprod : (w - z) * (4 * ((3 * y + 4 * z) / μ) + 2 + σ * z) = 0 := by rw [hfoc, mul_zero]
  nlinarith

lemma cseq_le {μ σ t : ℝ} (hμ : 0 < μ) (hσ : 0 < σ) :
    ∀ k, 0 < cseq μ σ t k → cseq μ σ t (k + 1) ≤ cseq μ σ t k := by
  intro k hk
  change hs μ σ (hy μ σ (cseq μ σ t k)) ≤ cseq μ σ t k
  set c := cseq μ σ t k
  have hd : 0 < 9 + μ * σ := by positivity
  have hd' : 0 < 16 + μ * σ := by positivity
  unfold hs hy
  rw [div_le_iff₀ hd']
  have : 12 * ((μ - 12 * c) / (9 + μ * σ)) = (12 * μ - 144 * c) / (9 + μ * σ) := by ring
  rw [this, show -((12 * μ - 144 * c) / (9 + μ * σ) + 2 * μ)
      = (144 * c - 12 * μ - 2 * μ * (9 + μ * σ)) / (9 + μ * σ) by field_simp; ring,
    div_le_iff₀ hd]
  nlinarith [mul_pos hμ hσ, mul_pos hk (mul_pos hμ hσ)]

lemma cseq_tendsto {σ t : ℝ} (k : ℕ) :
    Tendsto (fun μ => cseq μ σ t k) (𝓝[>] 0) (𝓝 (3 * t)) := by
  induction k with
  | zero => exact tendsto_const_nhds
  | succ k ih =>
    change Tendsto (fun μ => hs μ σ (hy μ σ (cseq μ σ t k))) (𝓝[>] 0) (𝓝 (3 * t))
    have hμ : Tendsto (fun μ : ℝ => μ) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds
      tendsto_id
    have hY : Tendsto (fun μ => hy μ σ (cseq μ σ t k)) (𝓝[>] 0) (𝓝 ((0 - 12 * (3 * t)) / (9 + 0 * σ))) :=
      (hμ.sub (ih.const_mul 12)).div (tendsto_const_nhds.add (hμ.mul_const σ)) (by norm_num)
    have hS := ((hY.const_mul 12).add (hμ.const_mul 2)).neg.div
      (tendsto_const_nhds.add (hμ.mul_const σ)) (by norm_num : (16 : ℝ) + 0 * σ ≠ 0)
    have e : -(12 * ((0 - 12 * (3 * t)) / (9 + 0 * σ)) + 2 * 0) / (16 + 0 * σ) = 3 * t := by ring
    rw [e] at hS
    exact hS

/-- **Proposition H4.10(c)** (as a limit). σ > 0, t ∈ (0, 1/(2σ)], K ≥ 0: for any family of
exact cyclic minimisation runs x^μ of E^μ from x̄_t (required only for the first K sweeps and
only for small μ > 0), a_K^μ/a_0^μ → 1 as μ → 0⁺ (a_k^μ := E^μ(x^μ_k) − E^μ*, E^μ* = 0): no
rate holds uniformly in μ. Such families exist: `H4_10_c_exists`. -/
theorem H4_10_c {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hst : σ * t ≤ 1 / 2) (K : ℕ)
    (x : ℝ → ℕ → E2) (hx0 : ∀ μ, x μ 0 = xbar t)
    (hsw : ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ k < K, ExactSweep2 (Ehub μ σ) (x μ k) (x μ (k + 1))) :
    Tendsto (fun μ => (Ehub μ σ (x μ K) - Ehub μ σ 0) / (Ehub μ σ (x μ 0) - Ehub μ σ 0))
      (𝓝[>] 0) (𝓝 1) := by
  have hE0 : ∀ μ, 0 < μ → Ehub μ σ 0 = 0 := fun μ hμ => by simp [Ehub, hub, hμ.le]
  -- eventually: μ ∈ (0, t] and c_k ∈ [3t/2, 3t] for all k ≤ K
  have hev_pos : ∀ᶠ μ in 𝓝[>] (0 : ℝ), 0 < μ := eventually_mem_nhdsWithin
  have hev_t : ∀ᶠ μ in 𝓝[>] (0 : ℝ), μ ≤ t :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).eventually (ge_mem_nhds ht)
  have hev_c : ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ k ∈ Finset.range (K + 1), 3 * t / 2 ≤ cseq μ σ t k := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact (cseq_tendsto k).eventually (le_mem_nhds (by linarith))
  -- on that set, the runs are the explicit ones
  have hexp : ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ k ≤ K, x μ k 1 = cseq μ σ t k ∧
      (0 < k → x μ k 0 = hy μ σ (cseq μ σ t (k - 1))) := by
    filter_upwards [hev_pos, hev_t, hev_c, hsw] with μ hμ hμt hc hsw
    have hcu : ∀ k ≤ K, cseq μ σ t k ≤ 3 * t := by
      intro k hk
      induction k with
      | zero => exact le_rfl
      | succ k ih =>
        have hk' := ih (by omega)
        have hpos : 0 < cseq μ σ t k := by
          have := hc k (Finset.mem_range.2 (by omega)); linarith
        exact (cseq_le hμ hσ k hpos).trans hk'
    intro k hk
    induction k with
    | zero => exact ⟨by rw [hx0, xbar, v2_1]; rfl, fun h => absurd h (lt_irrefl 0)⟩
    | succ k ih =>
      obtain ⟨ih1, -⟩ := ih (by omega)
      have hc1 := hc k (Finset.mem_range.2 (by omega))
      have hc2 := hcu k (by omega)
      have hsw' := hsw k (by omega)
      have e0 : x μ (k + 1) 0 = hy μ σ (cseq μ σ t k) := by
        have h1 := Ehub_block0 hμ hσ ht hst hμt hc1 hc2 (x μ k) ih1 (x μ (k + 1) 0)
        have h2 := hsw'.1 (hy μ σ (cseq μ σ t k))
        have hq : (x μ (k + 1) 0 - hy μ σ (cseq μ σ t k)) ^ 2 ≤ 0 := by nlinarith
        nlinarith [sq_nonneg (x μ (k + 1) 0 - hy μ σ (cseq μ σ t k))]
      have e1 : x μ (k + 1) 1 = cseq μ σ t (k + 1) := by
        have hx' : upd (x μ k) 0 (x μ (k + 1) 0) 0 = hy μ σ (cseq μ σ t k) := by rw [upd00, e0]
        have h1 := Ehub_block1 hμ hσ ht hst hμt hc1 hc2 _ hx' (x μ (k + 1) 1)
        have h2 := hsw'.2 (hs μ σ (hy μ σ (cseq μ σ t k)))
        change x μ (k + 1) 1 = hs μ σ (hy μ σ (cseq μ σ t k))
        have hq : (x μ (k + 1) 1 - hs μ σ (hy μ σ (cseq μ σ t k))) ^ 2 ≤ 0 := by nlinarith
        nlinarith [sq_nonneg (x μ (k + 1) 1 - hs μ σ (hy μ σ (cseq μ σ t k)))]
      exact ⟨e1, fun _ => by rw [e0]; rfl⟩
  -- the limit of x^μ_K
  have hxK : Tendsto (fun μ => x μ K) (𝓝[>] 0) (𝓝 (xbar t)) := by
    rcases Nat.eq_zero_or_pos K with hK | hK
    · subst hK; simp only [hx0]; exact tendsto_const_nhds
    · have hμ : Tendsto (fun μ : ℝ => μ) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
      have hY : Tendsto (fun μ => hy μ σ (cseq μ σ t (K - 1))) (𝓝[>] 0)
          (𝓝 ((0 - 12 * (3 * t)) / (9 + 0 * σ))) :=
        (hμ.sub ((cseq_tendsto (K - 1)).const_mul 12)).div
          (tendsto_const_nhds.add (hμ.mul_const σ)) (by norm_num)
      rw [show (0 - 12 * (3 * t)) / (9 + 0 * σ) = -4 * t by ring] at hY
      have hexpl : Tendsto (fun μ => (!₂[hy μ σ (cseq μ σ t (K - 1)), cseq μ σ t K] : E2))
          (𝓝[>] 0) (𝓝 (xbar t)) := by
        rw [xbar]
        have hc : Continuous (fun p : ℝ × ℝ => (!₂[p.1, p.2] : E2)) := by
          apply (PiLp.continuous_toLp 2 _).comp
          exact continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop
        exact (hc.tendsto (-4 * t, 3 * t)).comp (hY.prodMk_nhds (cseq_tendsto K))
      refine hexpl.congr' ?_
      filter_upwards [hexp] with μ hμ
      obtain ⟨h1, h0⟩ := hμ K le_rfl
      exact (E2_ext (by rw [v2_0, h0 hK]) (Or.inl (by rw [v2_1, h1]))).symm
  -- values
  have hlimE : ∀ {z : ℝ → E2} {z0 : E2}, Tendsto z (𝓝[>] 0) (𝓝 z0) →
      Tendsto (fun μ => Ehub μ σ (z μ) - Ehub μ σ 0) (𝓝[>] 0) (𝓝 (Eabs σ z0)) := by
    intro z z0 hz
    have hA : Tendsto (fun μ => Eabs σ (z μ)) (𝓝[>] 0) (𝓝 (Eabs σ z0)) :=
      ((continuous_Eabs σ).tendsto z0).comp hz
    have hμ : Tendsto (fun μ : ℝ => μ) (𝓝[>] 0) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have hdiff : Tendsto (fun μ => Ehub μ σ (z μ) - Ehub μ σ 0 - Eabs σ (z μ)) (𝓝[>] 0) (𝓝 0) := by
      apply squeeze_zero_norm' _ hμ
      filter_upwards [eventually_mem_nhdsWithin] with μ (hμ0 : 0 < μ)
      rw [hE0 μ hμ0, sub_zero, Real.norm_eq_abs]
      exact Ehub_close hμ0 _
    have := hdiff.add hA
    simpa using this
  have hnum := hlimE hxK
  have hden := hlimE (z := fun μ => x μ 0) (z0 := xbar t) (by simp only [hx0]; exact tendsto_const_nhds)
  have hpos : Eabs σ (xbar t) ≠ 0 := by
    have := (H4_10_a_stall hσ ht hst).2.2.2.2.2
    rw [Eabs_zero, sub_zero] at this; exact this.ne'
  have := hnum.div hden hpos
  rwa [div_self hpos] at this

/-- Non-vacuity of `H4_10_c`: the explicit family x^μ_0 = x̄_t,
x^μ_{k+1} = (y(μ, c_k), c_{k+1}) is, for every K and all small μ > 0, an exact cyclic
minimisation run of E^μ for its first K sweeps. -/
theorem H4_10_c_exists {σ t : ℝ} (hσ : 0 < σ) (ht : 0 < t) (hst : σ * t ≤ 1 / 2) (K : ℕ) :
    ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ k < K, ExactSweep2 (Ehub μ σ)
      (if k = 0 then xbar t else !₂[hy μ σ (cseq μ σ t (k - 1)), cseq μ σ t k])
      !₂[hy μ σ (cseq μ σ t k), cseq μ σ t (k + 1)] := by
  have hev_pos : ∀ᶠ μ in 𝓝[>] (0 : ℝ), 0 < μ := eventually_mem_nhdsWithin
  have hev_t : ∀ᶠ μ in 𝓝[>] (0 : ℝ), μ ≤ t :=
    (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).eventually (ge_mem_nhds ht)
  have hev_c : ∀ᶠ μ in 𝓝[>] (0 : ℝ), ∀ k ∈ Finset.range (K + 1), 3 * t / 2 ≤ cseq μ σ t k := by
    rw [Filter.eventually_all_finset]
    intro k _
    exact (cseq_tendsto k).eventually (le_mem_nhds (by linarith))
  filter_upwards [hev_pos, hev_t, hev_c] with μ hμ hμt hc
  have hcu : ∀ k ≤ K, cseq μ σ t k ≤ 3 * t := by
    intro k hk
    induction k with
    | zero => exact le_rfl
    | succ k ih =>
      have hk' := ih (by omega)
      have hpos : 0 < cseq μ σ t k := by
        have := hc k (Finset.mem_range.2 (by omega)); linarith
      exact (cseq_le hμ hσ k hpos).trans hk'
  intro k hk
  set xk : E2 := if k = 0 then xbar t else !₂[hy μ σ (cseq μ σ t (k - 1)), cseq μ σ t k]
  have hxk : xk 1 = cseq μ σ t k := by
    simp only [xk]; split_ifs with h
    · subst h; rw [xbar, v2_1]; rfl
    · rw [v2_1]
  have hc1 := hc k (Finset.mem_range.2 (by omega))
  have hc2 := hcu k (by omega)
  refine ⟨fun w => ?_, fun w => ?_⟩
  · rw [v2_0]
    have := Ehub_block0 hμ hσ ht hst hμt hc1 hc2 xk hxk w
    nlinarith [sq_nonneg (w - hy μ σ (cseq μ σ t k))]
  · rw [v2_0, v2_1]
    have hx' : upd xk 0 (hy μ σ (cseq μ σ t k)) 0 = hy μ σ (cseq μ σ t k) := upd00 _ _
    have := Ehub_block1 hμ hσ ht hst hμt hc1 hc2 _ hx' w
    rw [show cseq μ σ t (k + 1) = hs μ σ (hy μ σ (cseq μ σ t k)) from rfl]
    nlinarith [sq_nonneg (w - hs μ σ (hy μ σ (cseq μ σ t k)))]

end Examples

end OCF.H4

#print axioms OCF.H4.decl_sigma
#print axioms OCF.H4.decl_tau
#print axioms OCF.H4.slice_modC
#print axioms OCF.H4.decl_tau_sigma
#print axioms OCF.H4.decl_cross
#print axioms OCF.H4.decl_cross_default
#print axioms OCF.H4.Lam_sq
#print axioms OCF.H4.rho_mem
#print axioms OCF.H4.rhoth_mem
#print axioms OCF.H4.one_sub_rhoth
#print axioms OCF.H4.rhoth_tendsto
#print axioms OCF.H4.key_K
#print axioms OCF.H4.block_gap
#print axioms OCF.H4.block_descent
#print axioms OCF.H4.block_move
#print axioms OCF.H4.block_min
#print axioms OCF.H4.block_equality
#print axioms OCF.H4.lemma_H4_2
#print axioms OCF.H4.lemma_H4_2_min
#print axioms OCF.H4.report_smooth
#print axioms OCF.H4.report_polish
#print axioms OCF.H4.report_polish_L
#print axioms OCF.H4.report_H2
#print axioms OCF.H4.report_valuegap
#print axioms OCF.H4.epsSubgrad_smooth
#print axioms OCF.H4.tau_le_L
#print axioms OCF.H4.Run.sep_assembly
#print axioms OCF.H4.Run.H4_4_a
#print axioms OCF.H4.Run.H4_4_b
#print axioms OCF.H4.Run.H4_4_c
#print axioms OCF.H4.value_bracket
#print axioms OCF.H4.dist_bracket
#print axioms OCF.H4.growth
#print axioms OCF.H4.dist_of_growth
#print axioms OCF.H4.bracket_value_sharp
#print axioms OCF.H4.bracket_dist_sharp
#print axioms OCF.H4.Run.H4_6
#print axioms OCF.H4.Run.H4_7_a
#print axioms OCF.H4.Run.H4_7_a_iter
#print axioms OCF.H4.Run.H4_7_a_zero
#print axioms OCF.H4.Run.H4_7_b
#print axioms OCF.H4.Run.H4_7_c
#print axioms OCF.H4.Run.H4_7_c1
#print axioms OCF.H4.Run.H4_7_c2
#print axioms OCF.H4.Run.H4_7_c3
#print axioms OCF.H4.Run.H4_7_c3_limsup
#print axioms OCF.H4.Run.H4_7_d_dist
#print axioms OCF.H4.Bfun_mono
#print axioms OCF.H4.Run.H4_7_d_declared
#print axioms OCF.H4.accum
#print axioms OCF.H4.accum_const
#print axioms OCF.H4.accum_geom
#print axioms OCF.H4.accum_tendsto
#print axioms OCF.H4.accum_limsup
#print axioms OCF.H4.H4_8_a
#print axioms OCF.H4.H4_8_b
#print axioms OCF.H4.H4_8_geom
#print axioms OCF.H4.Bfun_valuegap
#print axioms OCF.H4.Bfun_polish
#print axioms OCF.H4.H4_9_a
#print axioms OCF.H4.H4_9_b
#print axioms OCF.H4.H4_9_c
#print axioms OCF.H4.sep_prox
#print axioms OCF.H4.H4_10_a_basic
#print axioms OCF.H4.H4_10_a_stall
#print axioms OCF.H4.H4_10_a_dist
#print axioms OCF.H4.H4_10_b_energy
#print axioms OCF.H4.Equart_blocks
#print axioms OCF.H4.cubic_root
#print axioms OCF.H4.qseq_spec
#print axioms OCF.H4.H4_10_b_run
#print axioms OCF.H4.H4_10_c_decl
#print axioms OCF.H4.H4_10_c
#print axioms OCF.H4.H4_10_c_exists
#print axioms OCF.H4.H4_10_d
#print axioms OCF.H4.H4_10_d_cross

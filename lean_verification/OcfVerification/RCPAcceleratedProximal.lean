/-
R-CP (the accelerated proximal word and the heavy-ball-plus-prox refusal) -- the Lean targets assigned at the
stage 3.5 gate of the adjudicated dossier: the FISTA word for a FREE momentum number in [0, 1) with its read-out
point, the reallocation of curvature from g into the smooth part, the exact rational instances of the
step boundary, of the all-states failure of the Lyapunov function for the inertial proximal recursion, and of the
start outside dom g, the comparison inequality, the tuning lemma, and the two instantiated rows with their classical
cores as named hypotheses.

Source of truth: project_plan/doing/proof_audits/R_CP_accelerated_proximal/01_derivation.md (adjudicated stage 3,
2026-10-29; tiers in 03_adjudication.md, "Surviving statements and tiers" / section 3 and the table of section 9 of the
dossier). Dossier sha16 (first 16 hex of sha256sum of 01_derivation.md): ae1c503452692b52 (drift re-check 2026-10-29 after the
C4 rulings of 03_adjudication.md; formalised originally against 88665e5cba31fcc8; every formalised statement re-read
against the repaired text and found matching, see the drift note at the end of this header).
Reused, not restated: E0MethodWords.lean (`dstep`, `IsProx`, `M1inv`, `M2`, `M3inv`, `chiF`, `fista_posDef`,
`fista_beta`, `prox_M2`, `isGradPS_fst`, `isGradPS_kinS`, `hbStep`, `chiHB`), C1ConservativeWord.lean (`hbBeta`, `hbQ`,
`hbS`, `bW`, `Lam`, `LamW`, `lamW_chi`, `r0C`, `alphaL_le_one`, `beta_nonneg`, `rpow_half_sq`), R0StackingLimits.lean
(`EInst`, `pt`, `Cline`, `projC`, `prox_eq_projC`, `LamI`, `instance_params`, `grad_EInst`), G3 (`LipGrad`, `ModC`),
S1 (`Dal1a`, `Keps`, `Keps_mem`, `Keps_upward`, `modC_mono`).

DEFINITIONAL MAP (dossier symbol -- Lean name):
* R^d -- a real Hilbert space `E` (`[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`); the gradient --
  Mathlib's `gradient` (`∇`); phase space -- `E × E` with E0's `ip2`, `IsGradPS`.
* F, g, S -- `f : E → ℝ` (`Differentiable ℝ f`), and `g : E → ℝ` with `S : Set E` (E0's pair convention: g ∈ Γ0 is
  `(S = dom g, g on S)`, +∞ off S); "g ∈ Γ0" -- `InGamma0 g S` (S nonempty, `ConvexOn ℝ S g`, closed epigraph `Epi S g`);
  E = F + g -- `f x + g x` on `S`; `argmin E` -- `argminE f g S`.
* L, m, sg (sigma_g), bh -- reals `L`, `m`, `sg`; "grad F is L-Lipschitz" (bh <= L) -- G3's `LipGrad f L`; "F - (m/2)|.|^2
  convex" -- G3's `ModC f m`; `L > 0` is `hL`; `sg >= 0`, `m >= 0` are `hsg`, `hm`.
* mu~ = m + sg, kappa~ = (L + sg)/mu~, beta_star, rho -- `m + sg`, `kappaT L m sg`, `betaStar κ`, `rhoC κ`.
* Euclidean prox `prox_{alpha g}` -- E0's `IsProx (Qn E) α S g u p` (`Qn E w = ‖w‖²`); the prox letter on E × E is any map
  `P2` with `∀ w, IsProx qM2 (1/L) (S ×ˢ univ) (fun w => g w.1) w (P2 w)`.
* The word W_k = D^{1,M_{3,k}}_K ∘ prox^{M_2}_{L^{-1}(g+0)} ∘ D^{1,M_1}_{f+0} -- `wordStep L β G1 G3 P2`;
  chi(y, x') = (y, y - x') -- `chiF`; the data of the word (prox letter, gradients, z_1 = chi(x_0, x_0), z_{k+1} = W_k z_k) --
  `IsWord`; the iteration (y_1 = x_0, x_k = prox_{g/L}(y_k - grad F(y_k)/L), y_{k+1} = x_k + beta_k (x_k - x_{k-1})) -- `IsRun`;
  the certified point x_k = the second block of chi^{-1}(z_{k+1}) -- `outPt (z (k+1))` (= (z (k+1)).1 - (z (k+1)).2).
* F~, g~, L~ -- `Ftil f sg`, `gtil g sg`, `L + sg`.
* The recursion I of Ochs-Chen-Brox-Pock (4.6) in iterate coordinates -- `iStep (gradient F) P α β`
  ((x, x') ↦ (P (x - α ∇F x + β (x - x')), x)); Lambda_W in iterate coordinates -- `Lam E E⋆ (bW L α)`, related to the landed
  `LamI` by `lamI_chiHB` (Λ_W ∘ χ = Λ). The instance of r-cp-instance: `EInst`, `Cline`, `aI = 7/32`, `bI = 5/16`, `zS`.
  The 1-D instances: `Fq x = x²/2` (`grad_Fq`), indicator of [0, ∞) as `(Ici 0, 0)`.
* p(z) = z² - c(1+beta) z + c beta -- `charPoly c β z`; the constant-momentum recursion x_{k+1} = c(x_k + beta (x_k - x_{k-1}))
  from x_0 = x_{-1} = 1 -- `ctSeq c β` (offset: `ctSeq n = x_{n-1}`).
* K_val, K_eps -- `Kval L R ε` (least K >= 1 with (K+1)² ε >= 2 L R²), `OCF.S1.Keps (rhoC κ) ((2/μ̃) Ψ̄₀) (ε²)`.

NAMED HYPOTHESES (classical inputs, stated as the sources state them; never global axioms):
* `hsingle` -- the proximal map of g ∈ Γ0 is single-valued (E0's `hpLu`, Beck-Teboulle (2.6)); locator for the librarian,
  UNCHECKED here. `hP2` (existence of the prox letter, as in E0's `fista_word`).
* `hBeck : BeckFISTA f g S L` -- [CLASSICAL] Beck, First-Order Methods in Optimization (2017), Thm 10.34 (p. 292) under
  Assumption 10.31 (p. 291), VERIFIED in WANTED.md ("R-CP locators 2026-10-29"): for any optimal x*, k >= 1,
  F(x^k) - F_opt <= 2 L_f |x^0 - x*|²/(k+1)² for FISTA with t_0 = 1, y^0 = x^0. Stated with its Assumption 10.31 as the
  antecedent (f differentiable convex with L-Lipschitz gradient, g ∈ Γ0, optimal set nonempty).
* `hBeck : BeckVFISTA …` -- [CLASSICAL] Beck 2017 Thm 10.42 (p. 302), VERIFIED (same record): V-FISTA with
  beta = (√κ - 1)/(√κ + 1), κ = L_f/σ, f σ-strongly convex: F(x^k) - F_opt <= (1 - 1/√κ)^k (F(x^0) - F_opt + (σ/2)|x^0 - x*|²).
* `hQG` -- [CLASSICAL] Beck 2017 Thm 5.25(b) (p. 122), VERIFIED: quadratic growth of the (m + sg)-strongly convex E from x*.
* `hPsi` -- the inequality Psi_0 <= Psi-bar_0 of r-cp-start (PROSE-ONLY in the dossier; its gradient-dominance step carries one
  UNCHECKED locator): taken as a hypothesis on the number `Psi`, as the dossier's tier table assigns.
* The Bauschke-Combettes 2017 Prop. 24.8(i) identity (p. 415, VERIFIED) is PROVED here for the Euclidean prox
  (`prox_add_quad`, `prox_realloc`) from the defining minimisation, so it is not a hypothesis.

COVERAGE (dossier item -- Lean name):
* r-cp-word (a), the word with a free momentum beta_k ∈ [0, 1), z_k = chi(y_k, x_{k-1}), the read-out, the intermediate
  state, x_k ∈ dom g, positive definiteness of the three metrics -- `rcp_word_free` (with `word_step_free`). No t-schedule
  and no recursion on beta_k is assumed (the schedule hypotheses of E0's `fista_word` are unused in its proof).
  FORMALISED.
* r-cp-word (b), the reallocation -- `prox_add_quad` (= B-C 24.8(i) with z = u = 0, the Euclidean prox, `γσ+1` form),
  `prox_realloc` (the displayed identity of (b): prox_{g~/L~}(y - grad F~(y)/L~) = prox_{g/L}(y - grad F(y)/L), as an
  `IsProx` equivalence), `gradient_Ftil`, `rcp_realloc` (F~ + g~ = F + g, F~ differentiable with a (L+sg)-Lipschitz gradient,
  `ModC F~ (m+sg)`, F~ convex when m >= 0), `inGamma0_gtil` (g~ ∈ Γ0 given the declared curvature), `isRun_realloc` (the V-FISTA run
  for (F~, g~, L~) is the word's run), `argminE_realloc`. FORMALISED.
* r-cp-instance -- `rcp_instance`: the pair (1, 4) data, x_F = x* = 0 ∈ argmin F ∩ argmin g, alpha = 7/32, beta = 5/16, q = 25/32,
  the state z, Lambda_W(z) = 471/224, the image of I, Lambda_W = 2684971/917504, ratio 2684971/1929216 > 1 > q, the unconstrained
  heavy-ball value 375099/229376 <= q Lambda_W(z), the failure of the all-states inequality, for every prox letter of the
  indicator of C = span{(1,1)}; Lambda_W is the landed function (`lamI_chiHB`). It is an existence statement, as in the dossier.
  FORMALISED.
* r-cp-start-out -- `rcp_start_out` (with `prox_Ici`, `prox_Ici_exists`): the iterates -1, 0, 1/2, 1/2 for every prox letter, the
  instance data, and the failure of both landed distance forms at K = 3 (squared: 1/4 > q³ r_0² = 1/8; unsquared with
  (L/m)^{1/2} q^{K/2} |x_0 - x*|). FORMALISED.
* r-cp-step -- `rcp_step`: m = 1/150 <= sigma(F) = 1, L' = 2/3 < bh = 1, kappa~ = 100, beta_star = 9/11, c = -1/2,
  p(-1) = -7/22, p(1) = 3/2, real roots z_1 < -1 < z_2, the recursion from x_0 = x_{-1} = 1 unbounded, and every run of the
  word on this data unbounded; with the declared pair (1/100, 1): c = 0, p(-1) = 1, x_k = 0 for k >= 1. The unboundedness lemma
  is `ctSeq_unbounded` (REAL-ROOT case |z_1| > 1, |z_2| <= 1, z_2 ≠ 1, the case used here; the complex-pair and double-root
  cases of the earlier draft's Lemma B2 are NOT formalised and not needed: the repaired dossier deleted that prose lemma and
  cites `rcp_step` / `ctSeq_unbounded` for B2; the real roots are stated as z_1 < -1 < z_2 < 1, as in B1). The empirical schedule divergence of
  witness K4 is not formalised (EMPIRICAL in the dossier). FORMALISED.
* r-cp-compare -- `rcp_compare_u` (u ∈ (0, 1], sqrt(1 - u) < 1 - u² iff u < (√5 - 1)/2, endpoint u = 1 included), `rcp_compare`
  (kappa~ form: sqrt(rho) < 1 - 1/kappa~ iff kappa~ > (3 + √5)/2, and the converse for kappa~ <= (3 + √5)/2), `compare_identity`.
  FORMALISED.
* r-cp-amgm -- `rcp_amgm` (0 <= m <= L, 0 < alpha <= 1/L: beta ∈ [0, 1), beta <= 1 - alpha(L+m)/2, beta < 1 - alpha L/2,
  gamma >= m/2, gamma > 0, alpha < 2(1 - beta)/L, delta - gamma = beta/(2 alpha) >= 0). FORMALISED.
* r-cp-restrict, the identity Q3 only -- `rcp_restrict_factor`. FORMALISED (identity); the rest of r-cp-restrict is PROSE-ONLY.
* r-cp-momentum, the product identity only -- `rcp_momentum_product` (c beta = (beta + 1)/2 > 1, p(1) = lambda > 0).
  FORMALISED (identity); the divergence for every beta > 1 (the root-location argument M1 and the cited Gelfand
  formula M2, both PROSE-ONLY in the repaired dossier) is NOT formalised; `ctSeq_unbounded` does not apply here, since
  every root exceeds 1 in modulus.
* r-cp-convex (row CP-A, conditional on the user radius) -- `rcp_convex`: read-out, x_k ∈ dom g, E(x_k) - E(x*) <= 2 L R_in²/(k+1)²
  for every k >= 1 and every minimiser, the count `Kval`; the index shift between Beck's t_0 = 1 and t_1 = 1 is done in the proof.
  The classical core is the hypothesis `hBeck`. STATEMENT-FORMALISED in the adjudicator's sense (no sorry; assembly proved;
  Beck's theorem not proved).
* r-cp-strong (row CP-B) -- `rcp_strong`: (a) values, (b) squared distance, (c) the count via S1's `Keps`; cores `hBeck` (Thm 10.42,
  transported by `isRun_realloc`), `hQG` (Thm 5.25(b)); `hPsi` (r-cp-start). STATEMENT-FORMALISED in the same sense.

NOT FORMALISED (stated honestly): r-cp-pair, r-cp-start (the inequalities for general convex functions), r-cp-ipiano (a)-(c)
(the residual assembly I3b and I4 over the cited Lemmas 4.11 to 4.13 is prose), r-cp-fixed, r-cp-refuse (a status
statement, now scoped to non-constant g), the pipelines sentence, the rest of r-cp-restrict and r-cp-momentum, the
witness-level claims (including the empirical schedule divergence of witness K4), the classical cores (Beck 10.34,
10.42, 5.25(b), B-C 16.44, 17.26), the scheme-definition gap (IF-9).

DRIFT NOTE (2026-10-29, dossier sha16 88665e5cba31fcc8 -> ae1c503452692b52): the C4 rulings changed no formalised
statement. H-CP at m = 0 asks F convex: `rcp_convex` carries `ConvexOn ℝ univ f` and `rcp_strong` carries `0 ≤ m` with
`ModC f m` (convexity at m = 0), `rcp_realloc` gives F~ convex from `0 ≤ m`. One Lean statement was tightened to the
dossier's B1 text: `rcp_step` now states z_2 < 1 as well. Two points the dossier asserts that the Lean takes as
hypotheses: `hmL : m ≤ L` in `rcp_strong` (the dossier derives it from m <= bh <= L, which needs E nontrivial) and the
r-cp-start inequality as `hPsi`. Neither is changed.

Status tier: FORMALISED (statement + proof, no sorry) for r-cp-word (a) and (b), r-cp-instance, r-cp-start-out, r-cp-step,
r-cp-compare, r-cp-amgm and the identities of r-cp-restrict and r-cp-momentum; STATEMENT-FORMALISED (classical core as a named
hypothesis, assembly proved, no sorry) for the rows r-cp-convex and r-cp-strong. STATUS: COMPLETE.
-/
import Mathlib
import OcfVerification.R0StackingLimits

open scoped RealInnerProductSpace Gradient
open OCF.E0 OCF.G3 OCF.C1 Set

noncomputable section

namespace OCF.RCP

/-- The Euclidean metric `Q w = ‖w‖²` of `prox_{αg}` on `E` (E0's `IsProx` takes the metric as a function). -/
abbrev Qn (E : Type*) [NormedAddCommGroup E] : E → ℝ := fun w => ‖w‖ ^ 2

section Word

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The letter composition `W_k = D^{1,M_{3,k}}_K ∘ prox^{M₂}_{L⁻¹(g⊕0)} ∘ D^{1,M₁}_{f⊕0}` on `E × E`. -/
def wordStep (L β : ℝ) (G1 G3 : E × E → E × E) (P2 : E × E → E × E) (z : E × E) : E × E :=
  dstep 1 (M3inv β) G3 (P2 (dstep 1 (M1inv (1 / L)) G1 z))

/-- The certified point read out of a phase state: `χ⁻¹(z) = (z₁, z₁ − z₂)`, second block. -/
def outPt (z : E × E) : E := z.1 - z.2

/-- The iteration of r-cp-word (a). -/
def IsRun (f g : E → ℝ) (S : Set E) (L : ℝ) (β : ℕ → ℝ) (x y : ℕ → E) : Prop :=
  y 1 = x 0 ∧
  (∀ k ≥ 1, IsProx (Qn E) (1 / L) S g (y k - (1 / L) • ∇ f (y k)) (x k)) ∧
  ∀ k ≥ 1, y (k + 1) = x k + β k • (x k - x (k - 1))

theorem word_step_free (f g : E → ℝ) (S : Set E) {L : ℝ} (_hL : 0 < L) (hf : Differentiable ℝ f)
    (hsingle : ∀ u p p', IsProx (Qn E) (1 / L) S g u p → IsProx (Qn E) (1 / L) S g u p' → p = p')
    (β : ℝ) (xk xp yk yn : E)
    (hx : IsProx (Qn E) (1 / L) S g (yk - (1 / L) • ∇ f yk) xk) (hy : yn = xk + β • (xk - xp))
    (P2 : E × E → E × E)
    (hP2 : ∀ z, IsProx qM2 (1 / L) (S ×ˢ Set.univ) (fun w => g w.1) z (P2 z))
    (G1 G3 : E × E → E × E) (hG1 : IsGradPS (fun z : E × E => f z.1) G1)
    (hG3 : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ‖z.2‖ ^ 2) G3) :
    wordStep L β G1 G3 P2 (chiF (yk, xp)) = chiF (yn, xk) ∧
      (P2 (dstep 1 (M1inv (1 / L)) G1 (chiF (yk, xp)))).1 = xk := by
  have eG1 : G1 = fun z => (∇ f z.1, 0) := hG1.unique (isGradPS_fst hf)
  have eG3 : G3 = fun z => (0, (1 : ℝ) • z.2) := by
    refine hG3.unique ?_
    have := isGradPS_kinS (E := E) 1
    simpa using this
  subst eG1 eG3
  set u := yk - (1 / L) • ∇ f yk with hu
  have h1 : dstep 1 (M1inv (1 / L)) (fun z : E × E => (∇ f z.1, 0)) (chiF (yk, xp)) =
      (u, u - xp) := by
    refine Prod.ext ?_ ?_ <;> simp [dstep, M1inv, chiF, hu] <;> abel
  unfold wordStep
  rw [h1]
  obtain ⟨hzS, hzmin, hz2⟩ := prox_M2 (hP2 (u, u - xp))
  set z := P2 (u, u - xp) with hz
  have hz1 : z.1 = xk :=
    hsingle u z.1 xk ⟨hzS, fun c hc => by simpa using hzmin c hc⟩ hx
  have hzeq : z = (xk, xk - xp) := by
    refine Prod.ext hz1 ?_
    rw [hz2, hz1]; simp only; abel
  refine ⟨?_, hz1⟩
  rw [hzeq, hy]
  refine Prod.ext ?_ ?_ <;> simp [dstep, M3inv, chiF] <;> module

/-- **r-cp-word (a): the word with the momentum a free number in `[0, 1)`, and the read-out point.**
`z₁ = χ(x₀, x₀) = (x₀, 0)`, `z_{k+1} = W_k z_k`. Then `z_k = χ(y_k, x_{k−1})` for every `k ≥ 1`
(`y_{k+1} = x_k + β_k (x_k − x_{k−1})`, `y₁ = x₀`, `x_k = prox_{g/L}(y_k − ∇F(y_k)/L)`), the three
metrics are positive definite, the certified point is `x_k = (z_{k+1}).1 − (z_{k+1}).2`, it is the
first block of the intermediate state after the proximal letter, and it lies in `dom g = S`.
No schedule `t_k` and no recursion for `β_k` is assumed. -/
theorem rcp_word_free (f g : E → ℝ) (S : Set E) {L : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (hsingle : ∀ u p p', IsProx (Qn E) (1 / L) S g u p → IsProx (Qn E) (1 / L) S g u p' → p = p')
    (β : ℕ → ℝ) (hβ : ∀ k ≥ 1, 0 ≤ β k ∧ β k < 1) (x y : ℕ → E) (hrun : IsRun f g S L β x y)
    (P2 : E × E → E × E)
    (hP2 : ∀ z, IsProx qM2 (1 / L) (S ×ˢ Set.univ) (fun w => g w.1) z (P2 z))
    (G1 G3 : E × E → E × E) (hG1 : IsGradPS (fun z : E × E => f z.1) G1)
    (hG3 : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ‖z.2‖ ^ 2) G3)
    (z : ℕ → E × E) (hz1 : z 1 = chiF (x 0, x 0))
    (hz : ∀ k ≥ 1, z (k + 1) = wordStep L (β k) G1 G3 P2 (z k)) :
    z 1 = (x 0, 0) ∧
    (∀ k ≥ 1, z k = chiF (y k, x (k - 1))) ∧
    (∀ k, outPt (z (k + 1)) = x k) ∧
    (∀ k ≥ 1, (P2 (dstep 1 (M1inv (1 / L)) G1 (z k))).1 = x k ∧ x k ∈ S) ∧
    (∀ k ≥ 1, ∀ w : E × E, w ≠ 0 → 0 < ip2 (M1inv (1 / L) w) w ∧ 0 < ip2 (M2 w) w ∧
      0 < ip2 (M3inv (β k) w) w) := by
  obtain ⟨hy1, hx, hy⟩ := hrun
  have hzk : ∀ k ≥ 1, z k = chiF (y k, x (k - 1)) := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [hz1, hy1]
    | succ n hn ih =>
      rw [hz n hn, ih]
      exact (word_step_free f g S hL hf hsingle (β n) (x n) (x (n - 1)) (y n) (y (n + 1))
        (hx n hn) (hy n hn) P2 hP2 G1 G3 hG1 hG3).1
  have hz1' : z 1 = (x 0, 0) := by simp [hz1, chiF]
  refine ⟨hz1', hzk, fun k => ?_, fun k hk => ?_, fun k hk => ?_⟩
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [hz1', outPt]
    · rw [hzk (k + 1) (by omega)]
      simp [outPt, chiF]
  · refine ⟨?_, (hx k hk).1⟩
    rw [hzk k hk]
    exact (word_step_free f g S hL hf hsingle (β k) (x k) (x (k - 1)) (y k) (y (k + 1))
        (hx k hk) (hy k hk) P2 hP2 G1 G3 hG1 hG3).2
  · intro w hw
    obtain ⟨a, b, c⟩ := fista_posDef (E := E) hL (hβ k hk).2
    exact ⟨a w hw, b w hw, c w hw⟩
  
end Word

section Realloc

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- `F̃ = F + (σ/2)‖·‖²`. -/
def Ftil (f : E → ℝ) (sg : ℝ) : E → ℝ := fun x => f x + sg / 2 * ‖x‖ ^ 2

/-- `g̃ = g − (σ/2)‖·‖²`. -/
def gtil (g : E → ℝ) (sg : ℝ) : E → ℝ := fun x => g x - sg / 2 * ‖x‖ ^ 2

omit [CompleteSpace E] in
/-- **Bauschke–Combettes Prop. 24.8(i)** (z = u = 0, β = 0), in the defining-minimisation form:
`p = prox_{γ(g + (σ/2)‖·‖²)}(x)` iff `p = prox_{γ(γσ+1)⁻¹ g}((γσ+1)⁻¹ x)`. -/
theorem prox_add_quad (g : E → ℝ) (S : Set E) {γ σ : ℝ} (hγ : 0 < γ) (hσ : 0 ≤ σ) (x p : E) :
    IsProx (Qn E) γ S (fun w => g w + σ / 2 * ‖w‖ ^ 2) x p ↔
    IsProx (Qn E) (γ / (γ * σ + 1)) S g ((γ * σ + 1)⁻¹ • x) p := by
  have hc : 0 < γ * σ + 1 := by positivity
  set c := γ * σ + 1 with hcdef
  have key : ∀ q : E, c * (γ / c * g q + ‖q - c⁻¹ • x‖ ^ 2 / 2) =
      γ * (g q + σ / 2 * ‖q‖ ^ 2) + ‖q - x‖ ^ 2 / 2 - (‖x‖ ^ 2 / 2 - ‖x‖ ^ 2 / (2 * c)) := by
    intro q
    rw [norm_sub_sq_real, norm_sub_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hc), hcdef]
    field_simp
    ring
  unfold IsProx
  simp only [Qn]
  constructor
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun y hy => ?_⟩
    have h1 := h y hy
    have k1 := key p
    have k2 := key y
    have : c * (γ / c * g p + ‖p - c⁻¹ • x‖ ^ 2 / 2) ≤ c * (γ / c * g y + ‖y - c⁻¹ • x‖ ^ 2 / 2) := by
      rw [k1, k2]; linarith
    exact le_of_mul_le_mul_left this hc
  · rintro ⟨hp, h⟩
    refine ⟨hp, fun y hy => ?_⟩
    have h1 := h y hy
    have k1 := key p
    have k2 := key y
    have := mul_le_mul_of_nonneg_left h1 hc.le
    rw [k1, k2] at this
    linarith

/-- The gradient of the quadratic: `∇(‖·‖²)(x) = 2x`. -/
theorem hasGradientAt_normsq (x : E) : HasGradientAt (fun w : E => ‖w‖ ^ 2) ((2 : ℝ) • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  refine (hasStrictFDerivAt_norm_sq (F := E) x).hasFDerivAt.congr_fderiv ?_
  ext w
  simp

/-- `∇F̃(x) = ∇F(x) + σ x`. -/
theorem gradient_Ftil {f : E → ℝ} (hf : Differentiable ℝ f) (sg : ℝ) (x : E) :
    ∇ (Ftil f sg) x = ∇ f x + sg • x := by
  have h1 : HasGradientAt f (∇ f x) x := (hf x).hasGradientAt
  have hF := h1.hasFDerivAt
  have hq := (hasStrictFDerivAt_norm_sq (F := E) x).hasFDerivAt
  have h := hF.add (hq.const_mul (sg / 2))
  have : HasGradientAt (Ftil f sg) (∇ f x + sg • x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    refine h.congr_fderiv ?_
    ext w
    simp
    ring
  exact this.gradient

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- `g = g̃ + (σ/2)‖·‖²` (the moved curvature, pointwise). -/
theorem gtil_add (g : E → ℝ) (sg : ℝ) : (fun w => gtil g sg w + sg / 2 * ‖w‖ ^ 2) = g := by
  funext w; simp [gtil]

/-- The prox identity of r-cp-word (b): for `L > 0`, `σ ≥ 0`, every `y`, `p`,
`p = prox_{g̃/L̃}(y − ∇F̃(y)/L̃)  ⟺  p = prox_{g/L}(y − ∇F(y)/L)`, `L̃ = L + σ`. -/
theorem prox_realloc {f : E → ℝ} (hf : Differentiable ℝ f) (g : E → ℝ) (S : Set E) {L sg : ℝ}
    (hL : 0 < L) (hsg : 0 ≤ sg) (y p : E) :
    IsProx (Qn E) (1 / (L + sg)) S (gtil g sg) (y - (1 / (L + sg)) • ∇ (Ftil f sg) y) p ↔
    IsProx (Qn E) (1 / L) S g (y - (1 / L) • ∇ f y) p := by
  have hLs : 0 < L + sg := by linarith
  have h := prox_add_quad (gtil g sg) S (γ := 1 / L) (σ := sg) (by positivity) hsg
    (y - (1 / L) • ∇ f y) p
  rw [gtil_add] at h
  rw [h, gradient_Ftil hf]
  have e1 : (1 / L) / (1 / L * sg + 1) = 1 / (L + sg) := by field_simp; ring
  have e2 : (1 / L * sg + 1)⁻¹ • (y - (1 / L) • ∇ f y) =
      y - (1 / (L + sg)) • (∇ f y + sg • y) := by
    have : (1 / L * sg + 1)⁻¹ = L / (L + sg) := by field_simp; ring
    rw [this]
    have h1 : L / (L + sg) = 1 - sg / (L + sg) := by field_simp; ring
    have h2 : L / (L + sg) * (1 / L) = 1 / (L + sg) := by field_simp
    rw [smul_sub, smul_smul, h2, h1, sub_smul, one_smul, smul_add, smul_smul]
    have h3 : (1 / (L + sg)) * sg = sg / (L + sg) := by ring
    rw [h3]; abel
  rw [e1, e2]

/-- **r-cp-word (b), curvature moved into the smooth part.** For a smooth `F` (`C¹`, `L`-Lipschitz
gradient, `F − (m/2)‖·‖²` convex), `σ ≥ 0` and `g` with `g̃ = g − (σ/2)‖·‖²` convex on `S`:
`F̃ + g̃ = F + g`; `F̃` is `C¹` with `L̃ = L + σ`-Lipschitz gradient, `F̃ − ((m+σ)/2)‖·‖²` is convex
(so `F̃` is convex when `m ≥ 0`); and the proximal-gradient step of `(F̃, g̃)` at `L̃` is that of
`(F, g)` at `L`. -/
theorem rcp_realloc (f g : E → ℝ) (S : Set E) {m sg L : ℝ} (hL : 0 < L) (hsg : 0 ≤ sg)
    (hf : Differentiable ℝ f) (hLip : LipGrad f L) (hmod : ModC f m) :
    (∀ x, Ftil f sg x + gtil g sg x = f x + g x) ∧
    Differentiable ℝ (Ftil f sg) ∧
    LipGrad (Ftil f sg) (L + sg) ∧
    ModC (Ftil f sg) (m + sg) ∧
    (0 ≤ m → ConvexOn ℝ univ (Ftil f sg)) ∧
    (∀ y p, IsProx (Qn E) (1 / (L + sg)) S (gtil g sg) (y - (1 / (L + sg)) • ∇ (Ftil f sg) y) p ↔
      IsProx (Qn E) (1 / L) S g (y - (1 / L) • ∇ f y) p) := by
  refine ⟨fun x => by simp [Ftil, gtil], ?_, ?_, ?_, ?_, fun y p => prox_realloc hf g S hL hsg y p⟩
  · have hq : Differentiable ℝ (fun w : E => ‖w‖ ^ 2) :=
      fun w => (hasStrictFDerivAt_norm_sq w).hasFDerivAt.differentiableAt
    show Differentiable ℝ (fun x => f x + sg / 2 * ‖x‖ ^ 2)
    exact hf.add (hq.const_mul _)
  · intro u v
    rw [gradient_Ftil hf, gradient_Ftil hf]
    have e : ∇ f u + sg • u - (∇ f v + sg • v) = (∇ f u - ∇ f v) + sg • (u - v) := by module
    rw [e]
    calc _ ≤ ‖∇ f u - ∇ f v‖ + ‖sg • (u - v)‖ := norm_add_le _ _
      _ ≤ L * ‖u - v‖ + sg * ‖u - v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hsg]
          exact add_le_add (hLip u v) le_rfl
      _ = (L + sg) * ‖u - v‖ := by ring
  · unfold ModC at hmod ⊢
    have e : (fun x => Ftil f sg x - (m + sg) / 2 * ‖x‖ ^ 2) = fun x => f x - m / 2 * ‖x‖ ^ 2 := by
      funext x; simp only [Ftil]; ring
    rw [e]; exact hmod
  · intro hm
    have e : (fun x => Ftil f sg x - 0 / 2 * ‖x‖ ^ 2) = Ftil f sg := by funext x; simp
    have h0 : ModC (Ftil f sg) (m + sg) := by
      unfold ModC at hmod ⊢
      have e : (fun x => Ftil f sg x - (m + sg) / 2 * ‖x‖ ^ 2) = fun x => f x - m / 2 * ‖x‖ ^ 2 := by
        funext x; simp only [Ftil]; ring
      rw [e]; exact hmod
    have := OCF.S1.modC_mono h0 (show (0 : ℝ) ≤ m + sg by linarith)
    unfold ModC at this
    rwa [e] at this

end Realloc

/-- The constants of H-CP: `κ̃ = (L + σ_g)/(m + σ_g)`, `β⋆ = (√κ̃ − 1)/(√κ̃ + 1)`, `ρ = 1 − 1/√κ̃`. -/
def kappaT (L m sg : ℝ) : ℝ := (L + sg) / (m + sg)
def betaStar (κ : ℝ) : ℝ := (Real.sqrt κ - 1) / (Real.sqrt κ + 1)
def rhoC (κ : ℝ) : ℝ := 1 - 1 / Real.sqrt κ

/-! ## r-cp-step -/

section Step

/-- `p(z) = z² − c(1 + β) z + c β`, the characteristic polynomial of `x_{k+1} = c (x_k + β (x_k − x_{k−1}))`. -/
def charPoly (c β z : ℝ) : ℝ := z ^ 2 - c * (1 + β) * z + c * β

/-- The constant-momentum recursion `x_{k+1} = c (x_k + β (x_k − x_{k−1}))` from `x_0 = x_{−1} = 1`,
indexed with an offset: `ctSeq n = x_{n−1}`. -/
def ctSeq (c β : ℝ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | (n + 2) => c * (ctSeq c β (n + 1) + β * (ctSeq c β (n + 1) - ctSeq c β n))

/-- **The unboundedness lemma (B2), real-root case**: if the characteristic polynomial has the real
roots `z₁`, `z₂` with `|z₁| > 1`, `|z₂| ≤ 1` and `z₂ ≠ 1`, then the orbit from the start `(1, 1)` is unbounded. -/
theorem ctSeq_unbounded {c β z₁ z₂ : ℝ} (hs : z₁ + z₂ = c * (1 + β)) (hp : z₁ * z₂ = c * β)
    (h1 : 1 < |z₁|) (h2 : |z₂| ≤ 1) (h3 : z₂ ≠ 1) : ∀ M : ℝ, ∃ n, M < |ctSeq c β n| := by
  intro M
  by_contra hcon
  push Not at hcon
  have hrec : ∀ n, ctSeq c β (n + 2) = (z₁ + z₂) * ctSeq c β (n + 1) - z₁ * z₂ * ctSeq c β n := by
    intro n
    rw [ctSeq, hs, hp]; ring
  have hw : ∀ n, ctSeq c β (n + 1) - z₂ * ctSeq c β n = z₁ ^ n * (1 - z₂) := by
    intro n
    induction n with
    | zero => simp [ctSeq]
    | succ n ih =>
      have : ctSeq c β (n + 1 + 1) - z₂ * ctSeq c β (n + 1) =
          z₁ * (ctSeq c β (n + 1) - z₂ * ctSeq c β n) := by
        rw [hrec n]; ring
      rw [this, ih]; ring
  have hpos : 0 < |1 - z₂| := abs_pos.2 (sub_ne_zero.2 (Ne.symm h3))
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (2 * M / |1 - z₂|) h1
  have hb : |ctSeq c β (n + 1) - z₂ * ctSeq c β n| ≤ 2 * M := by
    calc _ ≤ |ctSeq c β (n + 1)| + |z₂ * ctSeq c β n| := abs_sub _ _
      _ ≤ M + |z₂| * |ctSeq c β n| := by rw [abs_mul]; linarith [hcon (n + 1)]
      _ ≤ M + 1 * M := by
          have := hcon n
          have h0 : 0 ≤ |ctSeq c β n| := abs_nonneg _
          gcongr
      _ = 2 * M := by ring
  rw [hw n, abs_mul, abs_pow] at hb
  have := (div_lt_iff₀ hpos).1 hn
  linarith

/-- The prox of `g = 0` on all of `E` is the identity. -/
theorem prox_zero_iff {E : Type*} [NormedAddCommGroup E] (α : ℝ) (u p : E) :
    IsProx (Qn E) α univ (fun _ => (0 : ℝ)) u p ↔ p = u := by
  unfold IsProx
  simp only [Qn, mul_zero, zero_add, mem_univ, true_and]
  constructor
  · intro h
    have h1 := h u (mem_univ u)
    simp only [sub_self, norm_zero] at h1
    have h2 : ‖p - u‖ ^ 2 ≤ 0 := by linarith
    have h3 : ‖p - u‖ = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h2 (sq_nonneg _))
    exact sub_eq_zero.1 (norm_eq_zero.1 h3)
  · rintro rfl y _
    simp
    positivity

/-- The 1-D quadratic `F(x) = x²/2` (pair `(1, 1)`), `∇F = id`. -/
def Fq (x : ℝ) : ℝ := x ^ 2 / 2

theorem grad_Fq (x : ℝ) : ∇ Fq x = x := by
  rw [gradient_eq_deriv']
  have h : HasDerivAt (fun x : ℝ => x ^ 2 / 2) x x := by
    simpa using ((hasDerivAt_id x).pow 2).div_const 2
  exact h.deriv

theorem Fq_dal1a : OCF.S1.Dal1a Fq 1 := by
  intro a b
  simp [grad_Fq, Fq]
  nlinarith [sq_nonneg (a - b)]

theorem Fq_lip : OCF.G3.LipGrad Fq 1 := by
  intro a b
  simp [grad_Fq]

/-- The run of the word on `F = x²/2`, `g = 0`, `S = ℝ`, step `1/L`, constant momentum `β`,
from `x₀ = 1`, is `ctSeq (1 − 1/L) β` (offset by one: `x_n = ctSeq (n+1)`). -/
theorem run_eq_ctSeq {L β : ℝ} {x y : ℕ → ℝ} (hrun : IsRun Fq (fun _ => (0 : ℝ)) univ L (fun _ => β) x y)
    (hx0 : x 0 = 1) : ∀ n, x n = ctSeq (1 - 1 / L) β (n + 1) := by
  obtain ⟨hy1, hx, hy⟩ := hrun
  have hxk : ∀ k ≥ 1, x k = (1 - 1 / L) * y k := by
    intro k hk
    have := (prox_zero_iff _ _ _).1 (hx k hk)
    rw [this, grad_Fq]; ring
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | n
    · simp [ctSeq, hx0]
    · rw [hxk 1 le_rfl, hy1, hx0]; simp [ctSeq]
    · rw [hxk (n + 2) (by omega), hy (n + 1) (by omega)]
      rw [show n + 1 + 1 = n + 2 by rfl, ctSeq]
      have h1 := ih (n + 1) (by omega)
      have h0 := ih n (by omega)
      simp only [Nat.add_sub_cancel] at *
      rw [h1, h0]; simp only [smul_eq_mul]

/-- **r-cp-step.** The instance `d = 1`, `E = F = x²/2` (declared smoothness `bh = 1`, pair data
`(m, L')` with `m = 1/150`, `L' = 2/3 < bh`), `κ̃ = L'/m = 100`, `β⋆ = 9/11`, `c = 1 − 1/L' = −1/2`.
(1) the data: `m = 1/150 ≤ 1 = σ(F)` (`Fq_dal1a`), `L' < 1 = bh` (`Fq_lip`), `κ̃ = 100`, `β⋆ = 9/11`,
`c = −1/2`; (2) `p(−1) = −7/22 < 0`, `p(1) = 3/2 ≠ 0`, and real roots `z₁ < −1 < z₂ < 1`;
(3) the recursion from `x_0 = x_{−1} = 1` is unbounded, and so is every run of the word on this data;
(4) with the declared pair `(1/100, 1)` (`c = 0`) every run has `x_k = 0` for `k ≥ 1`
and `p(−1) = 1`. -/
theorem rcp_step :
    ((1 : ℝ) / 150 ≤ 1 ∧ (2 : ℝ) / 3 < 1 ∧ OCF.S1.Dal1a Fq 1 ∧ OCF.G3.LipGrad Fq 1) ∧
    (kappaT (2 / 3) (1 / 150) 0 = 100 ∧ betaStar 100 = 9 / 11 ∧ (1 : ℝ) - 1 / (2 / 3) = -1 / 2) ∧
    (charPoly (-1 / 2) (9 / 11) (-1) = -7 / 22 ∧ charPoly (-1 / 2) (9 / 11) 1 = 3 / 2 ∧
      ∃ z₁ z₂ : ℝ, z₁ < -1 ∧ -1 < z₂ ∧ z₂ < 1 ∧ charPoly (-1 / 2) (9 / 11) z₁ = 0 ∧
        charPoly (-1 / 2) (9 / 11) z₂ = 0) ∧
    (∀ M : ℝ, ∃ n, M < |ctSeq (-1 / 2) (9 / 11) n|) ∧
    (∀ (x y : ℕ → ℝ), IsRun Fq (fun _ => (0 : ℝ)) univ (2 / 3) (fun _ => 9 / 11) x y → x 0 = 1 →
      ∀ M : ℝ, ∃ n, M < |x n|) ∧
    (charPoly 0 (9 / 11) (-1) = 1 ∧
      ∀ (x y : ℕ → ℝ), IsRun Fq (fun _ => (0 : ℝ)) univ 1 (fun _ => 9 / 11) x y → ∀ k ≥ 1, x k = 0) := by
  have hs298 : Real.sqrt 298 ^ 2 = 298 := Real.sq_sqrt (by norm_num)
  have h12 : 12 < Real.sqrt 298 := by
    rw [show (12 : ℝ) = Real.sqrt (12 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have h32 : Real.sqrt 298 < 32 := by
    rw [show (32 : ℝ) = Real.sqrt (32 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  set z₁ : ℝ := (-10 - Real.sqrt 298) / 22 with hz₁
  set z₂ : ℝ := (-10 + Real.sqrt 298) / 22 with hz₂
  have hsum : z₁ + z₂ = (-1 / 2) * (1 + 9 / 11) := by rw [hz₁, hz₂]; ring
  have hprod : z₁ * z₂ = (-1 / 2) * (9 / 11) := by rw [hz₁, hz₂]; nlinarith
  have hz1l : z₁ < -1 := by rw [hz₁]; linarith
  have hz2l : -1 < z₂ := by rw [hz₂]; linarith
  have hz2u : z₂ < 1 := by rw [hz₂]; linarith
  have hroot : ∀ z, z₁ + z₂ = (-1 / 2) * (1 + 9 / 11) → z₁ * z₂ = (-1 / 2) * (9 / 11) → (z = z₁ ∨ z = z₂) →
      charPoly (-1 / 2) (9 / 11) z = 0 := by
    intro z hs hp hz
    unfold charPoly
    rcases hz with rfl | rfl <;> nlinarith
  have hunb : ∀ M : ℝ, ∃ n, M < |ctSeq (-1 / 2) (9 / 11) n| :=
    ctSeq_unbounded hsum hprod (by rw [abs_of_neg (by linarith)]; linarith)
      (by rw [abs_le]; constructor <;> linarith) (by linarith)
  refine ⟨⟨by norm_num, by norm_num, Fq_dal1a, Fq_lip⟩, ⟨?_, ?_, by norm_num⟩,
    ⟨by unfold charPoly; norm_num, by unfold charPoly; norm_num,
      ⟨z₁, z₂, hz1l, hz2l, hz2u, hroot z₁ hsum hprod (Or.inl rfl), hroot z₂ hsum hprod (Or.inr rfl)⟩⟩,
    hunb, ?_, ⟨by unfold charPoly; norm_num, ?_⟩⟩
  · unfold kappaT; norm_num
  · unfold betaStar
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]; norm_num
  · intro x y hrun hx0 M
    have hc : (1 : ℝ) - 1 / (2 / 3) = -1 / 2 := by norm_num
    have := run_eq_ctSeq hrun hx0
    rw [hc] at this
    obtain ⟨N, hN⟩ := hunb (max M 1)
    rcases N with _ | n
    · simp [ctSeq] at hN
    · exact ⟨n, by rw [this n]; exact lt_of_le_of_lt (le_max_left _ _) hN⟩
  · intro x y hrun k hk
    obtain ⟨hy1, hx, hy⟩ := hrun
    have := (prox_zero_iff _ _ _).1 (hx k hk)
    rw [this, grad_Fq]; norm_num

end Step
/-! ## The inertial proximal recursion I and the exact instances of the refusal -/

section Refusal

/-- The recursion `I` of Ochs–Chen–Brox–Pock Alg. 2 (4.6), on iterate coordinates
`(x_n, x_{n−1}) ↦ (x_{n+1}, x_n)`, `x_{n+1} = P(x_n − α∇F(x_n) + β(x_n − x_{n−1}))`,
`P = prox_{αg}` any prox letter. -/
def iStep {X : Type*} [AddCommGroup X] [Module ℝ X] (G : X → X) (P : X → X) (α β : ℝ)
    (z : X × X) : X × X :=
  (P (z.1 - α • G z.1 + β • (z.1 - z.2)), z.1)

/-- The prox of the indicator of `[0, ∞)` (pair `(S, g) = ([0,∞), 0)`) at any weight is `max u 0`. -/
theorem prox_Ici {α : ℝ} {u p : ℝ}
    (h : IsProx (Qn ℝ) α (Ici 0) (fun _ => (0 : ℝ)) u p) : p = max u 0 := by
  obtain ⟨hp, hmin⟩ := h
  simp only [Qn, mul_zero, zero_add, Real.norm_eq_abs, sq_abs] at hmin
  have hp0 : 0 ≤ p := hp
  rcases le_total 0 u with hu | hu
  · have := hmin u hu
    simp at this
    rw [max_eq_left hu]
    nlinarith [sq_nonneg (p - u)]
  · have := hmin 0 (Set.mem_Ici.2 le_rfl)
    rw [max_eq_right hu]
    nlinarith [sq_nonneg (p - u)]

theorem prox_Ici_exists (α : ℝ) (u : ℝ) :
    IsProx (Qn ℝ) α (Ici 0) (fun _ => (0 : ℝ)) u (max u 0) := by
  refine ⟨Set.mem_Ici.2 (le_max_right _ _), fun y hy => ?_⟩
  have hy0 : 0 ≤ y := hy
  simp only [Qn, mul_zero, zero_add, Real.norm_eq_abs, sq_abs]
  rcases le_total 0 u with hu | hu
  · rw [max_eq_left hu]; simp; positivity
  · rw [max_eq_right hu]; nlinarith

/-- **r-cp-start-out.** `d = 1`, `F = x²/2` (pair `(1, 1)`), `α = β = 1/2`, `q = 1 − αm = 1/2`,
`g` the indicator of `[0, ∞)`, `x_0 = x_{−1} = −1 ∉ dom g`, `x⋆ = 0`. The iterates of `I` are
`−1, 0, 1/2, 1/2` (for every prox letter `P` of `g`), `|x_3|² = 1/4 > q³ r_0² = 1/8` with
`r_0 = |∇F(x_0)|/m = 1`, and also `|x_3| > (L/m)^{1/2} q^{3/2} |x_0 − x⋆|`: neither landed distance
form (`theoremC_b` of C1) holds for `I` from this start. -/
theorem rcp_start_out (P : ℝ → ℝ)
    (hP : ∀ u, IsProx (Qn ℝ) (1 / 2) (Ici 0) (fun _ => (0 : ℝ)) u (P u)) :
    -- the data of the instance
    (OCF.S1.Dal1a Fq 1 ∧ OCF.G3.LipGrad Fq 1 ∧ (0 : ℝ) ∈ Ici (0 : ℝ) ∧
      (∀ y ∈ Ici (0 : ℝ), Fq 0 + 0 ≤ Fq y + 0) ∧ (-1 : ℝ) ∉ Ici (0 : ℝ) ∧
      hbQ 1 (1 / 2) = 1 / 2 ∧ hbBeta 1 1 (1 / 2) = 1 / 2 ∧ r0C Fq 1 (-1) = 1) ∧
    -- the iterates
    (((iStep (gradient Fq) P (1 / 2) (1 / 2))^[0] (-1, -1)).1 = -1 ∧
      ((iStep (gradient Fq) P (1 / 2) (1 / 2))^[1] (-1, -1)).1 = 0 ∧
      ((iStep (gradient Fq) P (1 / 2) (1 / 2))^[2] (-1, -1)).1 = 1 / 2 ∧
      ((iStep (gradient Fq) P (1 / 2) (1 / 2))^[3] (-1, -1)).1 = 1 / 2) ∧
    -- both landed distance forms fail at K = 3
    (¬ ‖((iStep (gradient Fq) P (1 / 2) (1 / 2))^[3] (-1, -1)).1 - 0‖ ^ 2 ≤
        hbQ 1 (1 / 2) ^ 3 * r0C Fq 1 (-1) ^ 2) ∧
    (¬ ‖((iStep (gradient Fq) P (1 / 2) (1 / 2))^[3] (-1, -1)).1 - 0‖ ≤
        Real.sqrt (1 / 1) * hbQ 1 (1 / 2) ^ (((3 : ℕ) : ℝ) / 2) * ‖(-1 : ℝ) - 0‖) := by
  have hPv : ∀ u, P u = max u 0 := fun u => prox_Ici (hP u)
  have hq : hbQ 1 (1 / 2) = 1 / 2 := by unfold hbQ; norm_num
  have hb : hbBeta 1 1 (1 / 2) = 1 / 2 := by
    unfold hbBeta
    rw [show (1 - 1 / 2 * 1) * (1 - 1 / 2 * 1) = (1 / 2 : ℝ) ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have hr : r0C Fq 1 (-1) = 1 := by unfold r0C; rw [grad_Fq]; norm_num
  have i1 : (iStep (gradient Fq) P (1 / 2) (1 / 2))^[1] ((-1 : ℝ), (-1 : ℝ)) = (0, -1) := by
    simp [iStep, grad_Fq, hPv] <;> norm_num
  have i2 : (iStep (gradient Fq) P (1 / 2) (1 / 2))^[2] ((-1 : ℝ), (-1 : ℝ)) = (1 / 2, 0) := by
    rw [show 2 = 1 + 1 from rfl, Function.iterate_succ_apply', i1]
    simp [iStep, grad_Fq, hPv]
  have i3 : (iStep (gradient Fq) P (1 / 2) (1 / 2))^[3] ((-1 : ℝ), (-1 : ℝ)) = (1 / 2, 1 / 2) := by
    rw [show 3 = 2 + 1 from rfl, Function.iterate_succ_apply', i2]
    simp [iStep, grad_Fq, hPv]
  refine ⟨⟨Fq_dal1a, Fq_lip, Set.mem_Ici.2 le_rfl, fun y hy => by simp [Fq]; positivity, by simp, hq, hb, hr⟩,
    ⟨rfl, by rw [i1], by rw [i2], by rw [i3]⟩, ?_, ?_⟩
  · rw [i3, hq, hr]; norm_num
  · rw [i3, hq]
    intro h
    have h2 : (1 / 2 : ℝ) ≤ (1 / 2 : ℝ) ^ (((3 : ℕ) : ℝ) / 2) := by
      simpa using h
    have h3 := rpow_half_sq (q := (1 / 2 : ℝ)) (by norm_num) 3
    nlinarith [h3]

/-! ### r-cp-instance (two dimensions) -/

open OCF.R0 in
/-- `Λ_W` in iterate coordinates at the instance: `Λ(x, x') = E(x) − E⋆ + b‖x − x'‖²`, `b = (1 − αL)/(2α) = 2/7`. -/
theorem bW_inst : bW 4 aI = 2 / 7 := by unfold bW aI; norm_num

open OCF.R0 in
theorem lam_pt (a b u w : ℝ) :
    Lam EInst (EInst 0) (2 / 7) (pt a b) (pt u w) = (a ^ 2 + 4 * b ^ 2) / 2 + 2 / 7 * ((a - u) ^ 2 + (b - w) ^ 2) := by
  have h0 : EInst 0 = 0 := by simp [EInst]
  unfold Lam
  rw [h0, normsq2]
  simp only [PiLp.sub_apply, pt_zero, pt_one, EInst]
  ring

open OCF.R0 in
/-- The Lyapunov function of the landed theorem in iterate coordinates: `Λ_W ∘ χ = Λ`. -/
theorem lamI_chiHB (w : V2 × V2) :
    LamI (chiHB EInst (hbS aI bI) w) = Lam EInst (EInst 0) (2 / 7) w.1 w.2 := by
  have h := lamW_chi (E := EInst) (Es := EInst 0) (L := 4) (α := aI) (β := bI)
    (by unfold aI; norm_num) (by rw [bI_val]; norm_num) w
  rw [bW_inst] at h
  exact h

open OCF.R0 in
/-- The starting state of `r-cp-instance` (iterate coordinates): `x = (−7/4, 0)`, `x' = (−3/4, 1)`. -/
def zS : V2 × V2 := (pt (-7 / 4) 0, pt (-3 / 4) 1)

open OCF.R0 in
theorem iStep_pt (P : V2 → V2) (a b u w : ℝ) :
    iStep (gradient EInst) P aI bI (pt a b, pt u w) =
      (P (pt (a - 7 / 32 * a + 5 / 16 * (a - u)) (b - 7 / 32 * (4 * b) + 5 / 16 * (b - w))), pt a b) := by
  unfold iStep
  rw [grad_EInst, bI_val]
  simp only [aI]
  congr 2
  ext i; fin_cases i <;> simp [pt]

open OCF.R0 in
/-- **r-cp-instance.** For every prox letter `P` of `g = ι_C`, `C = span{(1,1)}` (every weight `α`):
the pair `(1, 4)` data of `F = (x₁² + 4x₂²)/2`, `x_F = x⋆ = 0 ∈ argmin F ∩ argmin g`, `α = 7/32`,
`β = 5/16`, `q = 25/32`; at the state `z = ((−7/4, 0), (−3/4, 1))`: `Λ_W(z) = 471/224`, the image of
`I` is `((−255/256, −255/256), (−7/4, 0))` with `Λ_W = 2684971/917504`, ratio `2684971/1929216
= 1.391742... > 1 > q`; the unconstrained heavy-ball step has `Λ_W = 375099/229376 ≤ q Λ_W(z)`;
hence the all-states inequality `Λ_W(I z) ≤ q Λ_W(z)` fails. `Λ_W` is the landed function, through
`Λ_W ∘ χ = Λ` (`lamI_chiHB`). It is an existence statement. -/
theorem rcp_instance {P : V2 → V2}
    (hP : ∀ x, IsProx (Qn V2) aI Cline (fun _ => (0 : ℝ)) x (P x)) :
    (OCF.S1.Dal1a EInst 1 ∧ OCF.G3.LipGrad EInst 4 ∧ (∀ y, EInst 0 ≤ EInst y) ∧ (0 : V2) ∈ Cline ∧
      aI = 7 / 32 ∧ aI < 1 / 4 ∧ bI = 5 / 16 ∧ hbQ 1 aI = 25 / 32) ∧
    (∀ w : V2 × V2, LamI (chiHB EInst (hbS aI bI) w) = Lam EInst (EInst 0) (2 / 7) w.1 w.2) ∧
    Lam EInst (EInst 0) (2 / 7) zS.1 zS.2 = 471 / 224 ∧
    iStep (gradient EInst) P aI bI zS = (pt (-255 / 256) (-255 / 256), pt (-7 / 4) 0) ∧
    Lam EInst (EInst 0) (2 / 7) (iStep (gradient EInst) P aI bI zS).1
      (iStep (gradient EInst) P aI bI zS).2 = 2684971 / 917504 ∧
    Lam EInst (EInst 0) (2 / 7) (iStep (gradient EInst) P aI bI zS).1 (iStep (gradient EInst) P aI bI zS).2 /
      Lam EInst (EInst 0) (2 / 7) zS.1 zS.2 = 2684971 / 1929216 ∧
    hbQ 1 aI * Lam EInst (EInst 0) (2 / 7) zS.1 zS.2 <
      Lam EInst (EInst 0) (2 / 7) (iStep (gradient EInst) P aI bI zS).1 (iStep (gradient EInst) P aI bI zS).2 ∧
    1 < (2684971 : ℝ) / 1929216 ∧
    OCF.E0.hbStep EInst aI bI zS = (pt (-215 / 128) (-5 / 16), pt (-7 / 4) 0) ∧
    Lam EInst (EInst 0) (2 / 7) (OCF.E0.hbStep EInst aI bI zS).1 (OCF.E0.hbStep EInst aI bI zS).2
      = 375099 / 229376 ∧
    Lam EInst (EInst 0) (2 / 7) (OCF.E0.hbStep EInst aI bI zS).1 (OCF.E0.hbStep EInst aI bI zS).2 ≤
      hbQ 1 aI * Lam EInst (EInst 0) (2 / 7) zS.1 zS.2 ∧
    ¬ (∀ z : V2 × V2, Lam EInst (EInst 0) (2 / 7) (iStep (gradient EInst) P aI bI z).1
        (iStep (gradient EInst) P aI bI z).2 ≤ hbQ 1 aI * Lam EInst (EInst 0) (2 / 7) z.1 z.2) := by
  have hq := qI_val
  have hz : zS = (pt (-7 / 4) 0, pt (-3 / 4) 1) := rfl
  have hproj : P (pt (-7 / 4 - 7 / 32 * (-7 / 4) + 5 / 16 * (-7 / 4 - -3 / 4)) (0 - 7 / 32 * (4 * 0) + 5 / 16 * (0 - 1))) =
      pt (-255 / 256) (-255 / 256) := by
    rw [prox_eq_projC (hP _)]; unfold projC; simp only [pt_zero, pt_one]
    congr 1 <;> norm_num
  have hI : iStep (gradient EInst) P aI bI zS = (pt (-255 / 256) (-255 / 256), pt (-7 / 4) 0) := by
    rw [hz, iStep_pt, hproj]
  have hH : OCF.E0.hbStep EInst aI bI zS = (pt (-215 / 128) (-5 / 16), pt (-7 / 4) 0) := by
    rw [hz]
    unfold OCF.E0.hbStep
    rw [grad_EInst, bI_val]
    simp only [aI]
    refine Prod.ext ?_ rfl
    simp only
    ext i; fin_cases i <;> simp [pt] <;> norm_num
  have e0 : Lam EInst (EInst 0) (2 / 7) zS.1 zS.2 = 471 / 224 := by
    rw [hz]; simp only; rw [lam_pt]; norm_num
  have e1 : Lam EInst (EInst 0) (2 / 7) (iStep (gradient EInst) P aI bI zS).1
      (iStep (gradient EInst) P aI bI zS).2 = 2684971 / 917504 := by
    rw [hI]; simp only; rw [lam_pt]; norm_num
  have e2 : Lam EInst (EInst 0) (2 / 7) (OCF.E0.hbStep EInst aI bI zS).1
      (OCF.E0.hbStep EInst aI bI zS).2 = 375099 / 229376 := by
    rw [hH]; simp only; rw [lam_pt]; norm_num
  refine ⟨?_, lamI_chiHB, e0, hI, e1, ?_, ?_,
    by norm_num, hH, e2, ?_, ?_⟩
  · obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩ := instance_params
    exact ⟨d1, d2, d3, d4, by unfold aI; rfl, d6, d7, d9⟩
  · rw [e1, e0]; norm_num
  · rw [e1, e0, hq]; norm_num
  · rw [e2, e0, hq]; norm_num
  · intro h
    have := h zS
    rw [e1, e0, hq] at this
    norm_num at this

end Refusal

/-! ## r-cp-compare, r-cp-amgm, r-cp-restrict identity, r-cp-momentum product identity -/

section Elementary

/-- `(1 − u)(1 + u)² − 1 = u (1 − u − u²)` (the identity of the proof of r-cp-compare). -/
theorem compare_identity (u : ℝ) : (1 - u) * (1 + u) ^ 2 - 1 = u * (1 - u - u ^ 2) := by ring

/-- **r-cp-compare, in `u = 1/√κ̃`.** For `u ∈ (0, 1]`: `√(1 − u) < 1 − u²` iff `u < (√5 − 1)/2`.
At `u = 1` both factors are `0`, the strict inequality fails, and `1 > (√5 − 1)/2`. -/
theorem rcp_compare_u {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    Real.sqrt (1 - u) < 1 - u ^ 2 ↔ u < (Real.sqrt 5 - 1) / 2 := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  rcases h1.lt_or_eq with hlt | rfl
  · have hpos : 0 < 1 - u ^ 2 := by nlinarith
    rw [Real.sqrt_lt' hpos]
    have key : (1 - u ^ 2) ^ 2 - (1 - u) = (1 - u) * (u * (1 - u - u ^ 2)) := by ring
    constructor
    · intro h
      have h2 : 0 < (1 - u) * (u * (1 - u - u ^ 2)) := by linarith
      have h3 : 0 < u * (1 - u - u ^ 2) := pos_of_mul_pos_right h2 (by linarith)
      have h4 : 0 < 1 - u - u ^ 2 := pos_of_mul_pos_right h3 h0.le
      nlinarith
    · intro h
      have h4 : 0 < 1 - u - u ^ 2 := by nlinarith
      have h3 : 0 < u * (1 - u - u ^ 2) := mul_pos h0 h4
      have h2 : 0 < (1 - u) * (u * (1 - u - u ^ 2)) := mul_pos (by linarith) h3
      linarith
  · have hs3 : Real.sqrt 5 < 3 := by nlinarith
    constructor
    · intro h; simp at h
    · intro h; linarith

/-- **r-cp-compare, in `κ̃`.** For `κ̃ ≥ 1` (`u = 1/√κ̃`): the distance factor `√ρ`, `ρ = 1 − 1/√κ̃`,
that CP-B certifies per step is smaller than the factor `1 − 1/κ̃` of CP-0 iff `κ̃ > (3 + √5)/2`;
for `κ̃ ≤ (3 + √5)/2` the CP-B factor is no smaller. -/
theorem rcp_compare {κ : ℝ} (hκ : 1 ≤ κ) :
    (Real.sqrt (rhoC κ) < 1 - 1 / κ ↔ (3 + Real.sqrt 5) / 2 < κ) ∧
    (κ ≤ (3 + Real.sqrt 5) / 2 → 1 - 1 / κ ≤ Real.sqrt (rhoC κ)) := by
  have hκ0 : 0 < κ := by linarith
  have hs : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ0
  have hs1 : 1 ≤ Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hκ
  have hsq : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ0.le
  set u : ℝ := 1 / Real.sqrt κ with hu
  have hu0 : 0 < u := by positivity
  have hu1 : u ≤ 1 := by rw [hu, div_le_one hs]; exact hs1
  have hu2 : u ^ 2 = 1 / κ := by rw [hu, div_pow, hsq]; simp
  have hrho : rhoC κ = 1 - u := rfl
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have hmain : Real.sqrt (rhoC κ) < 1 - 1 / κ ↔ (3 + Real.sqrt 5) / 2 < κ := by
    rw [hrho, ← hu2, rcp_compare_u hu0 hu1]
    -- u < r  ⟺  κ > (3+√5)/2, with r = (√5-1)/2, r (1+√5)/2 = 1
    have hr : (Real.sqrt 5 - 1) / 2 * ((1 + Real.sqrt 5) / 2) = 1 := by nlinarith
    have hrpos : 0 < (Real.sqrt 5 - 1) / 2 := by
      have : 1 < Real.sqrt 5 := by nlinarith
      linarith
    have e1 : u < (Real.sqrt 5 - 1) / 2 ↔ (1 + Real.sqrt 5) / 2 < Real.sqrt κ := by
      rw [hu, div_lt_iff₀ hs]
      constructor
      · intro h
        by_contra hc
        push Not at hc
        have := mul_le_mul_of_nonneg_left hc hrpos.le
        nlinarith
      · intro h
        have := mul_lt_mul_of_pos_left h hrpos
        nlinarith
    rw [e1, Real.lt_sqrt (by positivity)]
    constructor <;> intro h <;> nlinarith
  refine ⟨hmain, fun h => ?_⟩
  by_contra hc
  push Not at hc
  have := hmain.1 hc
  linarith

/-- **r-cp-amgm.** `0 ≤ m ≤ L`, `0 < α ≤ 1/L`, `β = √((1 − αm)(1 − αL))` (C1's `hbBeta`):
`β ∈ [0, 1)`, `β ≤ 1 − α(L + m)/2`, `β < 1 − αL/2`; `γ = (1/α)(1 − β − αL/2) ≥ m/2`, `γ > 0`,
equivalently `α < 2(1 − β)/L`; and `δ = 1/α − L/2 − β/(2α)` satisfies `δ − γ = β/(2α) ≥ 0`. -/
theorem rcp_amgm {m L α : ℝ} (hm : 0 ≤ m) (hmL : m ≤ L) (hα : 0 < α) (hαL : α ≤ 1 / L) :
    0 ≤ hbBeta m L α ∧ hbBeta m L α < 1 ∧ hbBeta m L α ≤ 1 - α * (L + m) / 2 ∧
    hbBeta m L α < 1 - α * L / 2 ∧
    (m / 2 ≤ (1 / α) * (1 - hbBeta m L α - α * L / 2) ∧ 0 < (1 / α) * (1 - hbBeta m L α - α * L / 2)) ∧
    α < 2 * (1 - hbBeta m L α) / L ∧
    ((1 / α) * (1 - hbBeta m L α - α * L / 2) ≤ 1 / α - L / 2 - hbBeta m L α / (2 * α) ∧
      (1 / α - L / 2 - hbBeta m L α / (2 * α)) - (1 / α) * (1 - hbBeta m L α - α * L / 2) =
        hbBeta m L α / (2 * α)) := by
  have hL : 0 < L := by
    by_contra h
    push Not at h
    have : 1 / L ≤ 0 := by
      rcases h.lt_or_eq with h | h
      · exact (one_div_neg.2 h).le
      · simp [h]
    linarith
  have haL : α * L ≤ 1 := alphaL_le_one hL hαL
  have haL0 : 0 < α * L := mul_pos hα hL
  have ham : α * m ≤ α * L := mul_le_mul_of_nonneg_left hmL hα.le
  have ham0 : 0 ≤ α * m := mul_nonneg hα.le hm
  have h1 : 0 ≤ 1 - α * m := by linarith
  have h2 : 0 ≤ 1 - α * L := by linarith
  have hb0 : 0 ≤ hbBeta m L α := beta_nonneg m L α
  have hb1 : hbBeta m L α ≤ 1 - α * (L + m) / 2 := by
    unfold hbBeta
    rw [Real.sqrt_le_iff]
    refine ⟨by nlinarith, by nlinarith [sq_nonneg (α * L - α * m)]⟩
  have hb2 : hbBeta m L α < 1 - α * L / 2 := by
    unfold hbBeta
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith [mul_nonneg h2 ham0, sq_nonneg (α * L)]
  have hb3 : hbBeta m L α < 1 := by linarith
  have hγ : m / 2 ≤ (1 / α) * (1 - hbBeta m L α - α * L / 2) := by
    rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hα]
    nlinarith
  have hγ0 : 0 < (1 / α) * (1 - hbBeta m L α - α * L / 2) := by
    apply mul_pos (by positivity); linarith
  refine ⟨hb0, hb3, hb1, hb2, ⟨hγ, hγ0⟩, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hL]; linarith
  · have : (1 / α) * (1 - hbBeta m L α - α * L / 2) = 1 / α - hbBeta m L α / α - L / 2 := by
      field_simp
    rw [this]
    have : hbBeta m L α / (2 * α) ≥ 0 := by positivity
    have e : hbBeta m L α / α = 2 * (hbBeta m L α / (2 * α)) := by field_simp
    rw [e]; linarith
  · field_simp
    ring

/-- **r-cp-restrict, the identity of Q3.** `(1 − m/L)/(1 + σ/L) = 1 − 1/κ̃` for `L > 0`, `σ ≥ 0`,
`m + σ > 0`, `κ̃ = (L + σ)/(m + σ)`. -/
theorem rcp_restrict_factor {m sg L : ℝ} (hL : 0 < L) (hsg : 0 ≤ sg) (_hmu : 0 < m + sg) :
    (1 - m / L) / (1 + sg / L) = 1 - 1 / kappaT L m sg := by
  unfold kappaT
  have : 0 < L + sg := by linarith
  field_simp
  ring

/-- **r-cp-momentum, the product identity.** For `β > 1`, `L = 1`, `λ = (1 − 1/β)/2`, `c = 1 − λ`:
the product of the roots `c β = (β + 1)/2` exceeds `1`, and `p(1) = λ > 0`. -/
theorem rcp_momentum_product {β : ℝ} (hβ : 1 < β) :
    (1 - (1 - 1 / β) / 2) * β = (β + 1) / 2 ∧ 1 < (β + 1) / 2 ∧
    charPoly (1 - (1 - 1 / β) / 2) β 1 = (1 - 1 / β) / 2 ∧ 0 < (1 - 1 / β) / 2 := by
  have hβ0 : 0 < β := by linarith
  refine ⟨by field_simp; ring, by linarith, by unfold charPoly; ring, ?_⟩
  have : 1 / β < 1 := (div_lt_one hβ0).2 hβ
  linarith

end Elementary


/-! ## The two instantiated rows: the classical cores enter as named hypotheses -/

section Rows

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Epigraph of the extended-valued function `(S, g)` (`g` on `S`, `+∞` off `S`). -/
def Epi (S : Set E) (g : E → ℝ) : Set (E × ℝ) := {p | p.1 ∈ S ∧ g p.1 ≤ p.2}

/-- `g ∈ Γ₀` in the pair convention of E0: proper (`S` nonempty), convex, closed (closed epigraph). -/
def InGamma0 (g : E → ℝ) (S : Set E) : Prop :=
  S.Nonempty ∧ ConvexOn ℝ S g ∧ IsClosed (Epi S g)

/-- `argmin E`, `E = F + g`, over `dom g = S`. -/
def argminE (f g : E → ℝ) (S : Set E) : Set E := {x | x ∈ S ∧ ∀ y ∈ S, f x + g x ≤ f y + g y}

omit [CompleteSpace E] in
/-- `g̃ = g − (σ/2)‖·‖²` is in `Γ₀` when `g` is and `g̃` is convex (the declared curvature):
closedness of the epigraph transfers along the homeomorphism `(x, r) ↦ (x, r + (σ/2)‖x‖²)`. -/
theorem inGamma0_gtil {g : E → ℝ} {S : Set E} {sg : ℝ} (hg : InGamma0 g S)
    (hc : ConvexOn ℝ S (gtil g sg)) : InGamma0 (gtil g sg) S := by
  refine ⟨hg.1, hc, ?_⟩
  have hφ : Continuous (fun p : E × ℝ => (p.1, p.2 + sg / 2 * ‖p.1‖ ^ 2)) := by fun_prop
  have : Epi S (gtil g sg) = (fun p : E × ℝ => (p.1, p.2 + sg / 2 * ‖p.1‖ ^ 2)) ⁻¹' Epi S g := by
    ext p
    simp only [Epi, gtil, mem_setOf_eq, mem_preimage, sub_le_iff_le_add]
  rw [this]
  exact hg.2.2.preimage hφ

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- `F̃ + g̃ = F + g`, so the two problems have the same minimisers. -/
theorem argminE_realloc (f g : E → ℝ) (S : Set E) (sg : ℝ) :
    argminE (Ftil f sg) (gtil g sg) S = argminE f g S := by
  have h : ∀ x, Ftil f sg x + gtil g sg x = f x + g x := fun x => by simp [Ftil, gtil]
  ext x
  simp only [argminE, mem_setOf_eq, h]

/-- The data of `r-cp-word (b)` seen as iterations: the V-FISTA run of `(F̃, g̃)` at `L̃ = L + σ` with
momentum `β` is the run of the word on `(F, g)` at `L`, with the same `β`. -/
theorem isRun_realloc {f : E → ℝ} (hf : Differentiable ℝ f) (g : E → ℝ) (S : Set E) {L sg : ℝ}
    (hL : 0 < L) (hsg : 0 ≤ sg) (β : ℕ → ℝ) (x y : ℕ → E) :
    IsRun (Ftil f sg) (gtil g sg) S (L + sg) β x y ↔ IsRun f g S L β x y := by
  unfold IsRun
  refine and_congr Iff.rfl (and_congr ?_ Iff.rfl)
  refine forall₂_congr fun k _ => ?_
  exact prox_realloc hf g S hL hsg (y k) (x k)

/-- Beck 2017, Theorem 10.34 (FISTA, constant stepsize `1/L_f`), p. 292, under Assumption 10.31
(p. 291), as the book states it, at the data `(f, g, S, L)`: the schedule is Beck's (`t₀ = 1`,
`y⁰ = x⁰`, `x^{k+1} = prox_{g/L}(y^k − ∇f(y^k)/L)`, `t_{k+1} = (1 + √(1 + 4t_k²))/2`,
`y^{k+1} = x^{k+1} + ((t_k − 1)/t_{k+1})(x^{k+1} − x^k)`); for any optimal `x⋆` and `k ≥ 1`:
`F(x^k) − F_opt ≤ 2 L_f ‖x⁰ − x⋆‖²/(k+1)²`. (Beck's `F` is our `E = f + g`, his `f` our `f`.) -/
def BeckFISTA (f g : E → ℝ) (S : Set E) (L : ℝ) : Prop :=
  (Differentiable ℝ f ∧ ConvexOn ℝ univ f ∧ LipGrad f L ∧ InGamma0 g S ∧
      (argminE f g S).Nonempty) →
  ∀ (x y : ℕ → E) (t : ℕ → ℝ) (xs : E), xs ∈ argminE f g S → t 0 = 1 → y 0 = x 0 →
    (∀ k, IsProx (Qn E) (1 / L) S g (y k - (1 / L) • ∇ f (y k)) (x (k + 1))) →
    (∀ k, t (k + 1) = (1 + Real.sqrt (1 + 4 * t k ^ 2)) / 2) →
    (∀ k, y (k + 1) = x (k + 1) + ((t k - 1) / t (k + 1)) • (x (k + 1) - x k)) →
    ∀ k ≥ 1, f (x k) + g (x k) - (f xs + g xs) ≤ 2 * L * ‖x 0 - xs‖ ^ 2 / ((k : ℝ) + 1) ^ 2

/-- Beck 2017, Theorem 10.42 (V-FISTA), p. 302, under Assumption 10.31 and `f` `σ`-strongly convex,
as the book states it, at the data `(f, g, S, L, σ)` (`κ = L/σ`): `y⁰ = x⁰`,
`x^{k+1} = prox_{g/L}(y^k − ∇f(y^k)/L)`, `y^{k+1} = x^{k+1} + ((√κ − 1)/(√κ + 1))(x^{k+1} − x^k)`; for
any optimal `x⋆` and `k ≥ 0`: `F(x^k) − F_opt ≤ (1 − 1/√κ)^k (F(x⁰) − F_opt + (σ/2)‖x⁰ − x⋆‖²)`.
(`x⁰ ∈ dom g` is assumed so that `F(x⁰)` is finite.) -/
def BeckVFISTA (f g : E → ℝ) (S : Set E) (L σ : ℝ) : Prop :=
  (Differentiable ℝ f ∧ ConvexOn ℝ univ f ∧ LipGrad f L ∧ InGamma0 g S ∧
      (argminE f g S).Nonempty ∧ 0 < σ ∧ ModC f σ) →
  ∀ (x y : ℕ → E) (xs : E), xs ∈ argminE f g S → x 0 ∈ S → y 0 = x 0 →
    (∀ k, IsProx (Qn E) (1 / L) S g (y k - (1 / L) • ∇ f (y k)) (x (k + 1))) →
    (∀ k, y (k + 1) = x (k + 1) + betaStar (L / σ) • (x (k + 1) - x k)) →
    ∀ k, f (x k) + g (x k) - (f xs + g xs) ≤
      rhoC (L / σ) ^ k * (f (x 0) + g (x 0) - (f xs + g xs) + σ / 2 * ‖x 0 - xs‖ ^ 2)

/-- The word data of `r-cp-word (a)`: the prox letter, the two phase-space gradients and the
state sequence `z₁ = χ(x₀, x₀)`, `z_{k+1} = W_k z_k`. -/
def IsWord (f g : E → ℝ) (S : Set E) (L : ℝ) (β : ℕ → ℝ) (x : ℕ → E) (P2 : E × E → E × E)
    (G1 G3 : E × E → E × E) (z : ℕ → E × E) : Prop :=
  (∀ w, IsProx qM2 (1 / L) (S ×ˢ Set.univ) (fun w => g w.1) w (P2 w)) ∧
  IsGradPS (fun z : E × E => f z.1) G1 ∧
  IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ‖z.2‖ ^ 2) G3 ∧
  z 1 = chiF (x 0, x 0) ∧
  ∀ k ≥ 1, z (k + 1) = wordStep L (β k) G1 G3 P2 (z k)

/-- The count `K_val`: the least `K ≥ 1` with `(K+1)² ε ≥ 2 L R²` (integer-style comparison). -/
def Kval (L R ε : ℝ) : ℕ := sInf {K : ℕ | 1 ≤ K ∧ 2 * L * R ^ 2 ≤ ((K : ℝ) + 1) ^ 2 * ε}

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem kval_spec (L R : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ K ≥ Kval L R ε, 1 ≤ K ∧ 2 * L * R ^ 2 ≤ ((K : ℝ) + 1) ^ 2 * ε := by
  have hne : {K : ℕ | 1 ≤ K ∧ 2 * L * R ^ 2 ≤ ((K : ℝ) + 1) ^ 2 * ε}.Nonempty := by
    refine ⟨⌈2 * L * R ^ 2 / ε⌉₊ + 1, by omega, ?_⟩
    have h1 : 2 * L * R ^ 2 / ε ≤ ⌈2 * L * R ^ 2 / ε⌉₊ := Nat.le_ceil _
    have h2 : 2 * L * R ^ 2 ≤ (⌈2 * L * R ^ 2 / ε⌉₊ : ℝ) * ε := by
      rwa [div_le_iff₀ hε] at h1
    push_cast
    have h3 : (0 : ℝ) ≤ (⌈2 * L * R ^ 2 / ε⌉₊ : ℝ) := Nat.cast_nonneg _
    have h4 : (⌈2 * L * R ^ 2 / ε⌉₊ : ℝ) ≤ ((⌈2 * L * R ^ 2 / ε⌉₊ : ℝ) + 1 + 1) ^ 2 := by nlinarith
    have h5 := mul_le_mul_of_nonneg_right h4 hε.le
    linarith
  obtain ⟨hK1, hK2⟩ := Nat.sInf_mem hne
  have hK2' : 2 * L * R ^ 2 ≤ (((Kval L R ε : ℕ) : ℝ) + 1) ^ 2 * ε := hK2
  intro K hK
  refine ⟨le_trans hK1 hK, ?_⟩
  have hKr : ((Kval L R ε : ℕ) : ℝ) ≤ K := by exact_mod_cast hK
  have : (((Kval L R ε : ℕ) : ℝ) + 1) ^ 2 ≤ ((K : ℝ) + 1) ^ 2 := by
    have := Nat.cast_nonneg (α := ℝ) (Kval L R ε)
    nlinarith
  have := mul_le_mul_of_nonneg_right this hε.le
  linarith

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- A bound for every point of a set transfers to the distance to the set: if
`G ≤ c ‖x₀ − a‖²` for every `a ∈ A` and `dist(x₀, A) ≤ R` then `G ≤ c R²` (`c ≥ 0`). -/
theorem le_of_infDist {A : Set E} {x₀ : E} {R G c : ℝ} (hc : 0 ≤ c) (hA : A.Nonempty)
    (hR : Metric.infDist x₀ A ≤ R) (h : ∀ a ∈ A, G ≤ c * ‖x₀ - a‖ ^ 2) : G ≤ c * R ^ 2 := by
  have hev : ∀ ε : ℝ, 0 < ε → G ≤ c * (R + ε) ^ 2 := by
    intro ε hε
    obtain ⟨a, haA, ha⟩ := (Metric.infDist_lt_iff hA).1 (show Metric.infDist x₀ A < R + ε by linarith)
    rw [dist_eq_norm] at ha
    refine (h a haA).trans ?_
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ha.le 2) hc
  have ht : Filter.Tendsto (fun ε : ℝ => c * (R + ε) ^ 2) (nhdsWithin 0 (Ioi 0)) (nhds (c * R ^ 2)) := by
    have : Continuous (fun ε : ℝ => c * (R + ε) ^ 2) := by fun_prop
    have h0 := this.tendsto 0
    simp only [add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun ε hε => hev ε hε)

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem kappaT_ge_one {L m sg : ℝ} (hmL : m ≤ L) (hmu : 0 < m + sg) :
    1 ≤ kappaT L m sg := by
  unfold kappaT
  rw [le_div_iff₀ hmu]; linarith

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem betaStar_mem {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ betaStar κ ∧ betaStar κ < 1 := by
  have hs1 : 1 ≤ Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hκ
  unfold betaStar
  exact ⟨div_nonneg (by linarith) (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] in
theorem rhoC_mem {κ : ℝ} (hκ : 1 ≤ κ) : 0 ≤ rhoC κ ∧ rhoC κ < 1 := by
  have hs1 : 1 ≤ Real.sqrt κ := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hκ
  have hs0 : 0 < Real.sqrt κ := by linarith
  unfold rhoC
  refine ⟨?_, by have : 0 < 1 / Real.sqrt κ := by positivity
                 linarith⟩
  have : 1 / Real.sqrt κ ≤ 1 := by rw [div_le_one hs0]; exact hs1
  linarith

/-- **r-cp-convex (row CP-A), CONDITIONAL on the user radius `R_in`.** `H-CP` with `m ≥ 0` (`F` convex),
`argmin E ≠ ∅`, `R_in ≥ dist(x₀, argmin E)` an input, `x₀` arbitrary (not required in `dom g`), step `1/L`,
momentum `β_k = (t_k − 1)/t_{k+1}`, `t₁ = 1`, `t_{k+1} = (1 + √(1 + 4t_k²))/2`; the word of r-cp-word
and its read-out `x_k = outPt (z_{k+1})`. Then `x_k ∈ dom g` and for every `k ≥ 1` and every minimiser
`x⋆`: `E(x_k) − E(x⋆) ≤ 2 L R_in²/(k+1)²`; and for `ε > 0` every `K ≥ K_val` has `E(x_K) − E_⋆ ≤ ε`.
The classical core is the named hypothesis `hBeck` (Beck 2017 Thm 10.34), transported by the index shift
`t'_j = t_{j+1}`, `y'_j = y_{j+1}` (Beck's `t₀ = 1`, the dossier's `t₁ = 1`). -/
theorem rcp_convex (f g : E → ℝ) (S : Set E) {L Rin : ℝ} (hL : 0 < L)
    (hf : Differentiable ℝ f) (hfc : ConvexOn ℝ univ f) (hLip : LipGrad f L)
    (hg : InGamma0 g S) (hopt : (argminE f g S).Nonempty)
    (x₀ : E) (hR : Metric.infDist x₀ (argminE f g S) ≤ Rin)
    (hsingle : ∀ u p p', IsProx (Qn E) (1 / L) S g u p → IsProx (Qn E) (1 / L) S g u p' → p = p')
    (hBeck : BeckFISTA f g S L)
    (t : ℕ → ℝ) (ht1 : t 1 = 1)
    (ht : ∀ k ≥ 1, t (k + 1) = (1 + Real.sqrt (1 + 4 * t k ^ 2)) / 2)
    (x y : ℕ → E) (hx0 : x 0 = x₀)
    (hrun : IsRun f g S L (fun k => (t k - 1) / t (k + 1)) x y)
    (P2 : E × E → E × E) (G1 G3 : E × E → E × E) (z : ℕ → E × E)
    (hW : IsWord f g S L (fun k => (t k - 1) / t (k + 1)) x P2 G1 G3 z) :
    (∀ k, outPt (z (k + 1)) = x k) ∧
    (∀ xs ∈ argminE f g S, ∀ k ≥ 1, outPt (z (k + 1)) ∈ S ∧
      f (outPt (z (k + 1))) + g (outPt (z (k + 1))) - (f xs + g xs) ≤
        2 * L * Rin ^ 2 / ((k : ℝ) + 1) ^ 2) ∧
    (∀ ε : ℝ, 0 < ε → ∀ K ≥ Kval L Rin ε, ∀ xs ∈ argminE f g S,
      f (outPt (z (K + 1))) + g (outPt (z (K + 1))) - (f xs + g xs) ≤ ε) := by
  obtain ⟨hP2, hG1, hG3, hz1, hz⟩ := hW
  have hβ : ∀ k ≥ 1, 0 ≤ (t k - 1) / t (k + 1) ∧ (t k - 1) / t (k + 1) < 1 :=
    fun k hk => fista_beta t ht1 ht k hk
  have hword := rcp_word_free f g S hL hf hsingle (fun k => (t k - 1) / t (k + 1)) hβ x y hrun
    P2 hP2 G1 G3 hG1 hG3 z hz1 hz
  have hout : ∀ k, outPt (z (k + 1)) = x k := hword.2.2.1
  have hxS : ∀ k ≥ 1, x k ∈ S := fun k hk => (hrun.2.1 k hk).1
  have hnonneg : 0 ≤ Rin := le_trans Metric.infDist_nonneg hR
  have main : ∀ xs ∈ argminE f g S, ∀ k ≥ 1,
      f (x k) + g (x k) - (f xs + g xs) ≤ 2 * L * Rin ^ 2 / ((k : ℝ) + 1) ^ 2 := by
    intro xs hxs k hk
    have hB := hBeck ⟨hf, hfc, hLip, hg, hopt⟩ x (fun j => y (j + 1)) (fun j => t (j + 1))
    have hall : ∀ xs' ∈ argminE f g S, f (x k) + g (x k) - (f xs + g xs) ≤
        2 * L / ((k : ℝ) + 1) ^ 2 * ‖x₀ - xs'‖ ^ 2 := by
      intro xs' hxs'
      have hval : f xs + g xs = f xs' + g xs' :=
        le_antisymm (hxs.2 xs' hxs'.1) (hxs'.2 xs hxs.1)
      have h1 := hB xs' hxs' ht1 (by simpa using hrun.1)
        (fun j => hrun.2.1 (j + 1) (by omega))
        (fun j => ht (j + 1) (by omega))
        (fun j => by
          have := hrun.2.2 (j + 1) (by omega)
          simpa using this) k hk
      rw [hval]
      rw [hx0] at h1
      calc _ ≤ _ := h1
        _ = _ := by ring
    have hc : 0 ≤ 2 * L / ((k : ℝ) + 1) ^ 2 := by positivity
    have := le_of_infDist hc hopt hR hall
    calc _ ≤ _ := this
      _ = _ := by ring
  refine ⟨hout, fun xs hxs k hk => ?_, fun ε hε K hK xs hxs => ?_⟩
  · rw [hout k]; exact ⟨hxS k hk, main xs hxs k hk⟩
  · obtain ⟨hK1, hK2⟩ := kval_spec L Rin hε K hK
    rw [hout K]
    refine (main xs hxs K hK1).trans ?_
    have hpos : (0 : ℝ) < ((K : ℝ) + 1) ^ 2 := by positivity
    rw [div_le_iff₀ hpos]; linarith

/-- **r-cp-strong (row CP-B).** `H-CP`, `μ̃ = m + σ > 0` (so `m = 0 < σ` and `m > 0 = σ` are both
included), `x₀ ∈ dom g`, step `1/L`, `β_k = β⋆` for every `k`, the word of r-cp-word with the read-out
`x_k = outPt (z_{k+1})`. With `Ψ̄₀` any number with `Ψ₀ ≤ Ψ̄₀` (r-cp-start, an input here) and `ρ = 1 − 1/√κ̃`:
(a) `E(x_k) − E(x⋆) ≤ ρ^k Ψ̄₀`; (b) `‖x_k − x⋆‖² ≤ (2/μ̃) ρ^k Ψ̄₀`; (c) every `K ≥ K_ε` has
`‖x_K − x⋆‖ ≤ ε`, `K_ε` the least `K` with `(2/μ̃) ρ^K Ψ̄₀ ≤ ε²` (S1's `Keps`). Classical cores as named
hypotheses: `hBeck` (Beck 2017 Thm 10.42 at `(F̃, g̃, L̃, μ̃)`, `r-cp-word (b)` carries the word's run to it)
and `hQG` (quadratic growth, Beck 2017 Thm 5.25(b), p. 122); `hPsi` is the r-cp-start inequality. -/
theorem rcp_strong (f g : E → ℝ) (S : Set E) {L m sg Psi : ℝ} (hL : 0 < L) (hsg : 0 ≤ sg)
    (hm : 0 ≤ m) (hmu : 0 < m + sg) (hmL : m ≤ L)
    (hf : Differentiable ℝ f) (hLip : LipGrad f L) (hmod : ModC f m)
    (hg : InGamma0 g S) (hgc : ConvexOn ℝ S (gtil g sg))
    (x₀ : E) (hx₀S : x₀ ∈ S)
    (hsingle : ∀ u p p', IsProx (Qn E) (1 / L) S g u p → IsProx (Qn E) (1 / L) S g u p' → p = p')
    (hBeck : BeckVFISTA (Ftil f sg) (gtil g sg) S (L + sg) (m + sg))
    (xs : E) (hxs : xs ∈ argminE f g S)
    (hQG : ∀ y ∈ S, (m + sg) / 2 * ‖y - xs‖ ^ 2 ≤ f y + g y - (f xs + g xs))
    (hPsi : f x₀ + g x₀ - (f xs + g xs) + (m + sg) / 2 * ‖x₀ - xs‖ ^ 2 ≤ Psi)
    (x y : ℕ → E) (hx0 : x 0 = x₀)
    (hrun : IsRun f g S L (fun _ => betaStar (kappaT L m sg)) x y)
    (P2 : E × E → E × E) (G1 G3 : E × E → E × E) (z : ℕ → E × E)
    (hW : IsWord f g S L (fun _ => betaStar (kappaT L m sg)) x P2 G1 G3 z) :
    (∀ k, outPt (z (k + 1)) = x k ∧ x k ∈ S) ∧
    (∀ k, f (outPt (z (k + 1))) + g (outPt (z (k + 1))) - (f xs + g xs) ≤
        rhoC (kappaT L m sg) ^ k * Psi) ∧
    (∀ k, ‖outPt (z (k + 1)) - xs‖ ^ 2 ≤ 2 / (m + sg) * rhoC (kappaT L m sg) ^ k * Psi) ∧
    (∀ ε : ℝ, 0 < ε → ∀ K ≥ OCF.S1.Keps (rhoC (kappaT L m sg)) (2 / (m + sg) * Psi) (ε ^ 2),
      ‖outPt (z (K + 1)) - xs‖ ≤ ε) := by
  obtain ⟨hP2, hG1, hG3, hz1, hz⟩ := hW
  have hκ : 1 ≤ kappaT L m sg := kappaT_ge_one hmL hmu
  obtain ⟨hb0, hb1⟩ := betaStar_mem hκ
  obtain ⟨hr0, hr1⟩ := rhoC_mem hκ
  have hword := rcp_word_free f g S hL hf hsingle (fun _ => betaStar (kappaT L m sg))
    (fun _ _ => ⟨hb0, hb1⟩) x y hrun P2 hP2 G1 G3 hG1 hG3 z hz1 hz
  have hout : ∀ k, outPt (z (k + 1)) = x k := hword.2.2.1
  have hxS : ∀ k, x k ∈ S := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · rw [hx0]; exact hx₀S
    · exact (hrun.2.1 k hk).1
  -- the reallocated problem
  obtain ⟨hFe, hFd, hFL, hFmod, hFc, _⟩ := rcp_realloc f g S hL hsg hf hLip hmod (m := m)
  have hgt : InGamma0 (gtil g sg) S := inGamma0_gtil hg hgc
  have hopt' : (argminE (Ftil f sg) (gtil g sg) S).Nonempty := by
    rw [argminE_realloc]; exact ⟨xs, hxs⟩
  have hxs' : xs ∈ argminE (Ftil f sg) (gtil g sg) S := by rw [argminE_realloc]; exact hxs
  have hrun' : IsRun (Ftil f sg) (gtil g sg) S (L + sg) (fun _ => betaStar (kappaT L m sg)) x y :=
    (isRun_realloc hf g S hL hsg _ x y).2 hrun
  obtain ⟨hy1, hxp, hyr⟩ := hrun'
  have hB := hBeck ⟨hFd, hFc hm, hFL, hgt, hopt', hmu, hFmod⟩ x (fun j => y (j + 1)) xs hxs'
    (by rw [hx0]; exact hx₀S) (by simpa using hy1)
    (fun j => hxp (j + 1) (by omega))
    (fun j => by
      have := hyr (j + 1) (by omega)
      simpa [kappaT] using this)
  have hsum : ∀ w, Ftil f sg w + gtil g sg w = f w + g w := fun w => by simp [Ftil, gtil]
  have hgap : ∀ k, f (x k) + g (x k) - (f xs + g xs) ≤ rhoC (kappaT L m sg) ^ k * Psi := by
    intro k
    have h := hB k
    simp only [hsum] at h
    have hρ : rhoC ((L + sg) / (m + sg)) = rhoC (kappaT L m sg) := rfl
    rw [hρ, hx0] at h
    exact h.trans (mul_le_mul_of_nonneg_left hPsi (pow_nonneg hr0 k))
  have hdist : ∀ k, ‖x k - xs‖ ^ 2 ≤ 2 / (m + sg) * rhoC (kappaT L m sg) ^ k * Psi := by
    intro k
    have h1 := hQG (x k) (hxS k)
    have h2 := h1.trans (hgap k)
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, le_div_iff₀ hmu]
    nlinarith
  refine ⟨fun k => ⟨hout k, hxS k⟩, fun k => by rw [hout k]; exact hgap k,
    fun k => by rw [hout k]; exact hdist k, fun ε hε K hK => ?_⟩
  rw [hout K]
  have hPsi0 : 0 ≤ Psi := by
    have h1 := hxs.2 x₀ hx₀S
    have h2 : 0 ≤ (m + sg) / 2 * ‖x₀ - xs‖ ^ 2 := by positivity
    linarith
  have hr : 0 ≤ 2 / (m + sg) * Psi := by positivity
  have hmem : rhoC (kappaT L m sg) ^ K * (2 / (m + sg) * Psi) ≤ ε ^ 2 := by
    rcases hr.eq_or_lt with h0 | hpos
    · rw [← h0]; simp; positivity
    · have hm0 := OCF.S1.Keps_mem hr1 hr0 hpos (by positivity : 0 < ε ^ 2)
      exact OCF.S1.Keps_upward hr0 hr1.le hr hm0 hK
  have : ‖x K - xs‖ ^ 2 ≤ ε ^ 2 := by
    refine (hdist K).trans ?_
    calc _ = rhoC (kappaT L m sg) ^ K * (2 / (m + sg) * Psi) := by ring
      _ ≤ _ := hmem
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) hε.le two_ne_zero).1 this

end Rows

#print axioms OCF.RCP.word_step_free
#print axioms OCF.RCP.rcp_word_free
#print axioms OCF.RCP.prox_add_quad
#print axioms OCF.RCP.gradient_Ftil
#print axioms OCF.RCP.prox_realloc
#print axioms OCF.RCP.rcp_realloc
#print axioms OCF.RCP.inGamma0_gtil
#print axioms OCF.RCP.isRun_realloc
#print axioms OCF.RCP.ctSeq_unbounded
#print axioms OCF.RCP.rcp_step
#print axioms OCF.RCP.rcp_start_out
#print axioms OCF.RCP.lamI_chiHB
#print axioms OCF.RCP.rcp_instance
#print axioms OCF.RCP.rcp_compare_u
#print axioms OCF.RCP.rcp_compare
#print axioms OCF.RCP.rcp_amgm
#print axioms OCF.RCP.rcp_restrict_factor
#print axioms OCF.RCP.rcp_momentum_product
#print axioms OCF.RCP.kval_spec
#print axioms OCF.RCP.rcp_convex
#print axioms OCF.RCP.rcp_strong

end OCF.RCP

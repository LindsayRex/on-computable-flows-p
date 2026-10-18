/-
E0 (the table of compositions: known methods as words in the five primitives; board issue 26,
author ruling 2026-10-10: keep the table, every row machine-checked). Each of the 13 rows is an
identity of maps (pathwise for the stochastic rows: the Gaussian draw is an explicit argument;
of vector fields, drift and diffusion coefficients for the continuous rows 5 and 6): the
method's update rule, as its source prints it, equals the row's word in the primitives. The two
conjugacy identities of Proposition prop:fista-word and Proposition prop:hb-word are proved in
full. No convergence statement of any method is formalised.

Source of truth (English; not edited): v3/manuscript/sections/10_known_methods/
01_table_of_compositions.tex (the 13-row table, notes, prop:fista-word, prop:hb-word);
v3/manuscript/sections/12_appendix/04_calculus_methods.tex (app:words, notes (b)-(g) and the
two proofs); dossier project_plan/done/proof_audits/E0_table_of_compositions/01_derivation.md
(sha16 of sha256 when formalised: 26b4633def92381a), SOURCES.md (locators); primitives:
v4/sections/05b_primitives.tex (def:primitives) and DEF2_primitives/04_landing_draft.tex.

DEFINITIONAL MAP (dossier symbol -- Lean name):
* The space R^d -- a real inner-product space `E` (complete where `gradient`/adjoint need it),
  or `EuclideanSpace ℝ (Fin n)` (row 1, coordinates), or `Fin d → ℝ` (rows 2, 11, matrices).
  Phase space R^d x R^d -- `E × E` with the L² inner product `ip2`; a phase-space gradient is a
  field `G` with `IsGradPS F G` (Fréchet derivative = `ip2 (G z) ·`), unique by
  `IsGradPS.unique`, so `D_F` on `E × E` is well defined.
* ∇f on `E` -- Mathlib's `gradient` (`∇ f`). On `Fin d → ℝ` (rows 2, 11) the gradient,
  partials and Hessian are coordinate oracles `gradf`, `dU`, `hess` (the identity holds for
  every such oracle, hence for the true ones).
* D^{α,M}_f -- `dstep α Minv G` (`x − α M⁻¹ G x`; the metric enters by its inverse; where
  the source prints `M` rather than `M⁻¹` the two-sided inverse is proved: `hb_inverses`,
  `Mt_inv`, `row12_metric_inv`, `row2_newton`, `row11_leapfrog`).
* prox^M_{αg} -- `IsProx Q α S g x p` (defining minimisation; `Q w = ‖w‖²_M`; a proper
  g ∈ Γ₀ is the pair (S = dom g, g on S), +∞ off S); a prox letter is any map `P` with
  `∀ x, IsProx … x (P x)`. Indicator ι_C -- `(S, g) = (C, 0)`.
* Φ^SV_h (V, M_p) -- `sv GV Npinv h` (Npinv = M_p⁻¹); identical to A3's `OCF.A3.svD` on
  `Fin d → ℝ` (`sv_eq_A3`, by rfl); row 11 uses `OCF.A3.svD` directly.
* (Ψ)_W = W⁺∘Ψ∘W, W⁺ = c⁻¹W* -- `conjW W c Ψ`.
* N_α (T, Σ) -- `nstep T α Shalf ξ` (`x + √(2Tα) Σ^{1/2} ξ`, ξ explicit; Shalf = Σ^{1/2});
  extension (N) -- `nstepP` (momentum factor only).
* Continuous objects: conservative field -- `consField`; dissipative field -- `dissField`;
  generator -- `genWord` (word) and `itoGen` (source, b·∇ + ½ a : D²).
* Block metrics on E×E: [[aI, bI],[bI, cI]] -- `blk a b c`; diag(A, B) -- `bdiag A B`.

ROW -> LEAN NAME:
 1 ISTA -- `row1_ista` (BT09 T_α -- `shrink`; the update -- `istaStep`).
 2 damped Newton -- `row2_newton` (`newtonStep`; mI ⪯ ∇²f(x) gives the inverse).
 3 FISTA -- `fista_word` (the identity), `fista_posDef` (M₁⁻¹, M₂, M_{3,k}⁻¹ ≻ 0),
   `fista_beta` (β_k ∈ [0,1)), `chiF_chiF` (χ⁻¹ = χ); discrete Nesterov -- `su_word`, `su_beta`.
 4 heavy ball -- `hb_word` (χ bijection both ways, Ψ∘χ = χ∘S), `hb_inverses`.
 5 Nesterov's ODE -- `row5_nesterov_ode`, `Mt_inv`.
 6 Langevin diffusion -- `row6_langevin` (drift, diffusion coefficient, generator).
 7 ULA -- `row7_ula`.  8 MYULA -- `row8_myula`.  9 SLA -- `row9_sla`.  10 PLMC -- `row10_plmc`
   (with `nearest_unique`).  11 leapfrog -- `row11_leapfrog`.  12 BABO -- `row12_babo`
   (with `damp_K`, `row12_metric_inv`); note (f), Neal's refreshment -- `row12_refresh`.
 13 iterative thresholding -- `row13_ddd` (with `hasGradient_Delta`; DDD S_{w,1}, S_w --
   `S1`, `Sw`; φ_w -- `phiW`; analysis operator W -- `Wop`; the frame identity W*W = 1·I is a
   conjunct).

HYPOTHESES (classical inputs, stated as the sources state them; never proved here):
* Row 1: every minimiser of BT09 (2.3), (1/2t)‖x − u‖² + λ‖x‖₁, is T_{λt}(u) (BT09 p. 188).
* Row 3: Q_L(·, y) "admits a unique minimizer" p_L(y) (BT09 (2.5)–(2.6), p. 189): `_hpL`
  (minimality) and `hpLu` (uniqueness); existence of a point of prox^{M₂} (`P2`, `hP2`).
* Row 8: ∇g^λ = λ⁻¹(Id − prox_{λg}) (Bauschke–Combettes Prop. 12.30, eq. (12.28)), `hMY`.
* Row 9: for convex f ∈ C¹, y + ε∇f(y) = x ⟺ y = prox_{εf}(x) (B&C Prop. 16.44 with
  Prop. 17.31(i); note (e)), `hres`; the source's (I + ε∇f)⁻¹ by its defining equation.
* Row 10: existence of the Euclidean projection and of the prox (maps `PK`, `P`); their
  equality is PROVED (`nearest_unique`, convexity of C, Mathlib's variational inequality).
* Row 13: the minimiser of ½φ_w + ½‖· − u‖² is the coefficientwise threshold S_{w_γ,1}
  (DDD (16) and Prop. 2.1; BT09 (1.5); B&C Prop. 24.11), `hsoft`.
* Every prox letter, everywhere: existence of the prox map (a map `P` with `IsProx`).
Unused-but-stated hypotheses (underscored) record the source's standing assumptions
(`_hconv`, `_hf`, `_hε` in row 9; `_hw` in row 13; `_hβ2` in prop:hb-word; `_ht` in row 5;
`_hP` in rows 8, 9; `_ht1`, `_ht`, `_hy1`, `_hpL` in prop:fista-word): each identity holds
without them.

COVERAGE: all 13 rows; both conjugacy propositions (including the positive definiteness of the
three FISTA matrices, β_k ∈ [0,1), and the discrete Nesterov clause); notes (b), (c), (d),
(e) (as hypothesis), (f) (including Neal's refreshment for every ϱ), (g).

NOT FORMALISED: any convergence, rate or invariance statement (by design); the backtracking
choice of t in Boyd's Algorithm 9.5 (the identity is for each value of t, as the row claims);
the remark of note (g) that the same map is also prox_{½g} ∘ D^{1/2,I}_Δ (lem:conj-lifted(ii));
the RT96 conventions of the dossier (conditional, not in the table); positive definiteness of
the metrics of rows 4, 5, 12 (immediate; only their inverses are checked); the classical
inputs listed under HYPOTHESES.

STATUS: FORMALISED (statement + proof, no sorry) for every theorem in this file.
-/
import Mathlib
import OcfVerification.A3StormerVerlet

open scoped RealInnerProductSpace Gradient
open InnerProductSpace

noncomputable section

namespace OCF.E0

/-! ## Part 0. The discrete members of the five primitives -/

section Letters

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

/-- Dissipative member `D^{α,M}_f(x) = x − α M⁻¹ ∇f(x)`. The metric enters through its
inverse `Minv = M⁻¹`; `G` is the gradient of the declared term (`∇f`, Mathlib's `gradient`
on an inner-product space; on the phase space a field `G` with `IsGradPS F G`). -/
def dstep (α : ℝ) (Minv : X →ₗ[ℝ] X) (G : X → X) (x : X) : X :=
  x - α • Minv (G x)

/-- Projective member, by its defining minimisation: `p = prox^M_{αg}(x)` means
`p ∈ dom g` and `α g(p) + ½‖p − x‖²_M ≤ α g(y) + ½‖y − x‖²_M` for every `y ∈ dom g`.
A proper extended-valued `g` is the pair `(S, g)`: `g` on `S = dom g`, `+∞` off `S`;
`Q w = ‖w‖²_M`. -/
def IsProx (Q : X → ℝ) (α : ℝ) (S : Set X) (g : X → ℝ) (x p : X) : Prop :=
  p ∈ S ∧ ∀ y ∈ S, α * g p + Q (p - x) / 2 ≤ α * g y + Q (y - x) / 2

/-- Stochastic member, pathwise: `N_α(x; ξ) = x + √(2Tα) Σ^{1/2} ξ`, the Gaussian sample `ξ`
an explicit argument; `Shalf = Σ^{1/2}`. -/
def nstep (T α : ℝ) (Shalf : X →ₗ[ℝ] X) (ξ x : X) : X :=
  x + Real.sqrt (2 * T * α) • Shalf ξ

/-- Conservative member: the Störmer–Verlet map for `𝓗 = ½pᵀM_p⁻¹p + V(q)`, force `GV = ∇V`,
`Npinv = M_p⁻¹`: half step in `p`, full step in `q`, half step in `p`. -/
def sv (GV : X → X) (Npinv : X →ₗ[ℝ] X) (h : ℝ) (z : X × X) : X × X :=
  (z.1 + h • Npinv (z.2 - (h / 2) • GV z.1),
   (z.2 - (h / 2) • GV z.1) - (h / 2) • GV (z.1 + h • Npinv (z.2 - (h / 2) • GV z.1)))

/-- Momentum-only noise (extension (N)): `(q, p) ↦ (q, p + √(2Tα) Σ_p^{1/2} ξ)`. -/
def nstepP (T α : ℝ) (Shalf : X →ₗ[ℝ] X) (ξ : X) (z : X × X) : X × X :=
  (z.1, nstep T α Shalf ξ z.2)

/-- Conservative vector field `(M_p⁻¹p, −∇V(q))`. -/
def consField (GV : X → X) (Npinv : X →ₗ[ℝ] X) (z : X × X) : X × X :=
  (Npinv z.2, -GV z.1)

/-- Dissipative vector field `−M⁻¹∇F`. -/
def dissField (Minv : X →ₗ[ℝ] X) (G : X → X) (x : X) : X :=
  -Minv (G x)

end Letters

/-- Multiscale member: for a tight frame `W` (`W*W = cI`, `c > 0`) and `W⁺ = c⁻¹W*`,
the map `Ψ` on the coefficient space becomes `W⁺ ∘ Ψ ∘ W`. -/
def conjW {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (W : E →L[ℝ] F) (c : ℝ) (Ψ : F → F) (x : E) : E :=
  (c⁻¹ • ContinuousLinearMap.adjoint W) (Ψ (W x))

/-- The Störmer–Verlet map of A3 (`OCF.A3.svD`, matrix inverse mass on `Fin d → ℝ`) is the
member `sv` above; A3's definition is reused through this identity. -/
theorem sv_eq_A3 {d : ℕ} (F : (Fin d → ℝ) → (Fin d → ℝ)) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ)
    (z : (Fin d → ℝ) × (Fin d → ℝ)) : sv F (Matrix.mulVecLin N) h z = OCF.A3.svD F N h z := rfl

/-! ## The phase space `E × E`: its inner product, gradients and block metrics -/

section Phase

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The inner product of `E × E` (the L² product): `⟨(a,b),(c,d)⟩ = ⟨a,c⟩ + ⟨b,d⟩`. -/
def ip2 (z w : E × E) : ℝ := ⟪z.1, w.1⟫ + ⟪z.2, w.2⟫

/-- `w ↦ ⟨v, w⟩` on `E × E` as a continuous linear functional. -/
def ip2L (v : E × E) : E × E →L[ℝ] ℝ :=
  (innerSL ℝ v.1).comp (ContinuousLinearMap.fst ℝ E E) +
    (innerSL ℝ v.2).comp (ContinuousLinearMap.snd ℝ E E)

@[simp] theorem ip2L_apply (v w : E × E) : ip2L v w = ip2 v w := by
  simp [ip2L, ip2]

/-- `G` is the gradient of `F : E × E → ℝ` for the L² product inner product. -/
def IsGradPS (F : E × E → ℝ) (G : E × E → E × E) : Prop :=
  ∀ z, HasFDerivAt F (ip2L (G z)) z

/-- The phase-space gradient is unique, so `D_F` on `E × E` is well defined. -/
theorem IsGradPS.unique {F : E × E → ℝ} {G G' : E × E → E × E} (h : IsGradPS F G)
    (h' : IsGradPS F G') : G = G' := by
  funext z
  have hL := (h z).unique (h' z)
  have h1 : ∀ e : E, ⟪(G z).1, e⟫ = ⟪(G' z).1, e⟫ := fun e => by
    have := congrArg (fun φ : E × E →L[ℝ] ℝ => φ (e, 0)) hL
    simpa [ip2] using this
  have h2 : ∀ e : E, ⟪(G z).2, e⟫ = ⟪(G' z).2, e⟫ := fun e => by
    have := congrArg (fun φ : E × E →L[ℝ] ℝ => φ (0, e)) hL
    simpa [ip2] using this
  exact Prod.ext (ext_inner_right ℝ h1) (ext_inner_right ℝ h2)

/-- The block operator `[[a I, b I], [b I, c I]]` on `E × E`. -/
def blk (a b c : ℝ) : E × E →ₗ[ℝ] E × E where
  toFun z := (a • z.1 + b • z.2, b • z.1 + c • z.2)
  map_add' x y := by
    ext <;> simp only [Prod.fst_add, Prod.snd_add, smul_add] <;> abel
  map_smul' r x := by
    ext <;> simp only [Prod.smul_fst, Prod.smul_snd, smul_add, smul_smul, RingHom.id_apply,
      mul_comm]

@[simp] theorem blk_apply (a b c : ℝ) (z : E × E) :
    blk a b c z = (a • z.1 + b • z.2, b • z.1 + c • z.2) := rfl

/-- The block-diagonal operator `diag(A, B)` on `E × E`. -/
def bdiag (A B : E →ₗ[ℝ] E) : E × E →ₗ[ℝ] E × E := A.prodMap B

@[simp] theorem bdiag_apply (A B : E →ₗ[ℝ] E) (z : E × E) : bdiag A B z = (A z.1, B z.2) := rfl

/-- The quadratic form of the block operator: `⟨blk a b c z, z⟩ = a‖u‖² + 2b⟨u,v⟩ + c‖v‖²`. -/
theorem ip2_blk (a b c : ℝ) (u v : E) :
    ip2 (blk a b c (u, v)) (u, v) = a * ‖u‖ ^ 2 + 2 * b * ⟪u, v⟫ + c * ‖v‖ ^ 2 := by
  simp only [ip2, blk_apply, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
    RCLike.conj_to_real, real_inner_comm u v]
  ring

/-- Positive definiteness of a block operator `[[aI, bI], [bI, cI]]` (symmetric by its form):
`a > 0` and `ac − b² > 0` give `⟨M z, z⟩ > 0` for every `z ≠ 0`. -/
theorem blk_posDef {a b c : ℝ} (ha : 0 < a) (hs : 0 < a * c - b ^ 2) (z : E × E) (hz : z ≠ 0) :
    0 < ip2 (blk a b c z) z := by
  obtain ⟨u, v⟩ := z
  rw [ip2_blk]
  have key : a * (a * ‖u‖ ^ 2 + 2 * b * ⟪u, v⟫ + c * ‖v‖ ^ 2) =
      ‖a • u + b • v‖ ^ 2 + (a * c - b ^ 2) * ‖v‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, inner_smul_left, inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
    simp only [RCLike.conj_to_real]; ring
  by_cases hv : v = 0
  · subst hv
    have hu : u ≠ 0 := by rintro rfl; exact hz rfl
    have : 0 < ‖u‖ := norm_pos_iff.mpr hu
    simp only [inner_zero_right, norm_zero]; nlinarith [mul_pos ha (pow_pos this 2)]
  · have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have h1 : 0 < a * (a * ‖u‖ ^ 2 + 2 * b * ⟪u, v⟫ + c * ‖v‖ ^ 2) := by
      rw [key]; positivity
    exact pos_of_mul_pos_right h1 ha.le

/-- The gradient of the position term `(f ⊕ 0)(q, p) = f(q)` is `(∇f(q), 0)`. -/
theorem isGradPS_fst [CompleteSpace E] {f : E → ℝ} (hf : Differentiable ℝ f) :
    IsGradPS (fun z : E × E => f z.1) (fun z => (∇ f z.1, 0)) := by
  intro z
  have h1 : HasFDerivAt f (toDual ℝ E (∇ f z.1)) z.1 := (hf z.1).hasGradientAt
  have h2 := h1.comp z (hasFDerivAt_fst (𝕜 := ℝ) (E := E) (F := E) (p := z))
  have e : ip2L ((∇ f z.1, 0) : E × E) =
      (toDual ℝ E (∇ f z.1)).comp (ContinuousLinearMap.fst ℝ E E) := by
    ext w <;> simp [ip2]
  rw [e]; exact h2

/-- The gradient of the kinetic energy `K(q,p) = ½⟨Np, p⟩` with `N` symmetric is `(0, Np)`. -/
theorem isGradPS_kin (N : E →L[ℝ] E) (hN : ∀ u v, ⟪N u, v⟫ = ⟪u, N v⟫) :
    IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ⟪N z.2, z.2⟫) (fun z => (0, N z.2)) := by
  intro z
  have hs := hasFDerivAt_snd (𝕜 := ℝ) (E := E) (F := E) (p := z)
  have h := ((N.hasFDerivAt.comp z hs).inner ℝ hs).const_mul (1 / 2 : ℝ)
  have e : ip2L ((0, N z.2) : E × E) = (1 / 2 : ℝ) • (fderivInnerCLM ℝ ((N ∘ Prod.snd) z, z.2)).comp
      ((N.comp (ContinuousLinearMap.snd ℝ E E)).prod (ContinuousLinearMap.snd ℝ E E)) := by
    ext w
    · simp [ip2, fderivInnerCLM_apply]
    · simp only [ip2L_apply, ip2, smul_apply, ContinuousLinearMap.comp_apply,
        fderivInnerCLM_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.inr_apply,
        ContinuousLinearMap.coe_snd', Function.comp_apply, inner_zero_left, zero_add, smul_eq_mul]
      rw [hN, real_inner_comm (N w)]; ring
  rw [e]; exact h

/-- The gradient of the scalar kinetic energy `K(q,p) = ½ s‖p‖²` is `(0, s p)`. -/
theorem isGradPS_kinS (s : ℝ) :
    IsGradPS (fun z : E × E => (1 / 2 : ℝ) * s * ‖z.2‖ ^ 2) (fun z => (0, s • z.2)) := by
  have h := isGradPS_kin (s • ContinuousLinearMap.id ℝ E)
    (fun u v => by simp [inner_smul_left, inner_smul_right])
  intro z
  convert h z using 1
  · funext w; simp [inner_smul_left]; ring
  · simp

end Phase

/-! ## Proposition prop:fista-word (FISTA as a word; row 3) and the discrete Nesterov scheme -/

section FISTA

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The conjugacy `χ(y, x') = (y, y − x')`. -/
def chiF (z : E × E) : E × E := (z.1, z.1 - z.2)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- `χ` is an involution, hence a bijection with `χ⁻¹ = χ`. -/
theorem chiF_chiF (z : E × E) : chiF (chiF z) = z := by
  refine Prod.ext rfl ?_; simp [chiF]

/-- `M₁⁻¹ = c [[I, I], [I, 2I]]` (`c = 1/L` for FISTA, `c = s` for the discrete Nesterov scheme). -/
def M1inv (c : ℝ) : E × E →ₗ[ℝ] E × E := blk c c (2 * c)

/-- `M₂ = [[2I, −I], [−I, I]]`. -/
def M2 : E × E →ₗ[ℝ] E × E := blk 2 (-1) 1

/-- `M_{3,k}⁻¹ = [[(1 + β²/(1−β))I, −βI], [−βI, (1−β)I]]`. -/
def M3inv (β : ℝ) : E × E →ₗ[ℝ] E × E := blk (1 + β ^ 2 / (1 - β)) (-β) (1 - β)

/-- `‖w‖²_{M₂} = ⟨M₂ w, w⟩`. -/
def qM2 (w : E × E) : ℝ := ip2 (M2 w) w

/-- Beck–Teboulle (2.5): `Q_L(x, y) = f(y) + ⟨x − y, ∇f(y)⟩ + (L/2)‖x − y‖² + g(x)`. -/
def QL (f g : E → ℝ) (L : ℝ) (x y : E) : ℝ :=
  f y + ⟪x - y, ∇ f y⟫ + L / 2 * ‖x - y‖ ^ 2 + g x

omit [CompleteSpace E] in
/-- The three matrices of the proposition are positive definite (for `L > 0`, `β < 1`). -/
theorem fista_posDef {L β : ℝ} (hL : 0 < L) (hβ : β < 1) :
    (∀ z : E × E, z ≠ 0 → 0 < ip2 (M1inv (1 / L) z) z) ∧
    (∀ z : E × E, z ≠ 0 → 0 < ip2 (M2 z) z) ∧
    (∀ z : E × E, z ≠ 0 → 0 < ip2 (M3inv β z) z) := by
  have h1b : 0 < 1 - β := by linarith
  refine ⟨fun z hz => blk_posDef (by positivity) ?_ z hz, fun z hz => blk_posDef (by norm_num)
    (by norm_num) z hz, fun z hz => blk_posDef ?_ ?_ z hz⟩
  · field_simp; norm_num
  · have : 0 ≤ β ^ 2 / (1 - β) := by positivity
    linarith
  · have : (1 + β ^ 2 / (1 - β)) * (1 - β) - (-β) ^ 2 = 1 - β := by field_simp; ring
    rw [this]; exact h1b

omit [CompleteSpace E] in
/-- `‖(a, b)‖²_{M₂} = ‖a‖² + ‖b − a‖²`. -/
theorem qM2_eq (a b : E) : qM2 ((a, b) : E × E) = ‖a‖ ^ 2 + ‖b - a‖ ^ 2 := by
  rw [qM2, M2, ip2_blk, norm_sub_sq_real, real_inner_comm b a]; ring

omit [CompleteSpace E] in
/-- The second letter, by its defining minimisation: every point `z` of
`prox^{M₂}_{α(g⊕0)}(u, v)` has `z.1` minimising `α g + ½‖· − u‖²` over `dom g`, and
`z.2 = v + z.1 − u`. -/
theorem prox_M2 {S : Set E} {g : E → ℝ} {α : ℝ} {u v : E} {z : E × E}
    (hz : IsProx qM2 α (S ×ˢ Set.univ) (fun w => g w.1) (u, v) z) :
    z.1 ∈ S ∧ (∀ c ∈ S, α * g z.1 + ‖z.1 - u‖ ^ 2 / 2 ≤ α * g c + ‖c - u‖ ^ 2 / 2) ∧
      z.2 = v + z.1 - u := by
  obtain ⟨hzS, hmin⟩ := hz
  refine ⟨hzS.1, fun c hc => ?_, ?_⟩
  · have h := hmin (c, v + c - u) ⟨hc, Set.mem_univ _⟩
    simp only [Prod.mk_sub_mk, qM2_eq] at h
    have e : v + c - u - v - (c - u) = 0 := by abel
    rw [e, norm_zero] at h
    have := sq_nonneg ‖z.2 - v - (z.1 - u)‖
    have e2 : z - (u, v) = (z.1 - u, z.2 - v) := rfl
    rw [e2, qM2_eq] at h
    nlinarith
  · have h := hmin (z.1, v + z.1 - u) ⟨hzS.1, Set.mem_univ _⟩
    have e2 : z - (u, v) = (z.1 - u, z.2 - v) := rfl
    simp only [Prod.mk_sub_mk, qM2_eq] at h
    rw [e2, qM2_eq] at h
    have e : v + z.1 - u - v - (z.1 - u) = 0 := by abel
    rw [e, norm_zero] at h
    have h0 : ‖z.2 - v - (z.1 - u)‖ ^ 2 ≤ 0 := by nlinarith
    have : z.2 - v - (z.1 - u) = 0 := by
      have := sq_nonneg ‖z.2 - v - (z.1 - u)‖
      have h00 : ‖z.2 - v - (z.1 - u)‖ = 0 := by nlinarith [norm_nonneg (z.2 - v - (z.1 - u))]
      exact norm_eq_zero.mp h00
    rw [sub_eq_zero, sub_eq_iff_eq_add] at this
    rw [this]; abel

/-- Beck–Teboulle (2.5)–(2.6) to the prox (dossier R3.3): with `u = y − L⁻¹∇f(y)`,
`Q_L(c, y) = L (L⁻¹ g(c) + ½‖c − u‖²) + (f(y) − ‖∇f(y)‖²/(2L))`. -/
theorem QL_eq (f g : E → ℝ) {L : ℝ} (hL : 0 < L) (c y : E) :
    QL f g L c y = L * (1 / L * g c + ‖c - (y - (1 / L) • ∇ f y)‖ ^ 2 / 2) +
      (f y - ‖∇ f y‖ ^ 2 / (2 * L)) := by
  have e : c - (y - (1 / L) • ∇ f y) = (c - y) + (1 / L) • ∇ f y := by abel
  rw [QL, e, norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0 : ℝ) < 1 / L)]
  field_simp; ring

/-- **Proposition prop:fista-word, the identity.** Beck–Teboulle's FISTA with constant
stepsize (eqs. (4.1)–(4.3), p. 193; `p_L` of (2.5)–(2.6), p. 189, as the unique minimiser of
`Q_L(·, y)`, uniqueness as the source states it) and the word
`D^{1,M_{3,k}}_K ∘ prox^{M₂}_{L⁻¹(g⊕0)} ∘ D^{1,M₁}_{f⊕0}`: for every `k ≥ 1` the word maps
`χ(y_k, x_{k−1})` to `χ(y_{k+1}, x_k)`. The prox letter `P2` is any map returning a point of
`prox^{M₂}_{L⁻¹(g⊕0)}`; `G1`, `G3` are the phase-space gradients of `f ⊕ 0` and of
`K = ½|p|²`. -/
theorem fista_word (f g : E → ℝ) (S : Set E) {L : ℝ} (hL : 0 < L) (hf : Differentiable ℝ f)
    (pL : E → E)
    (_hpL : ∀ y, pL y ∈ S ∧ ∀ c ∈ S, QL f g L (pL y) y ≤ QL f g L c y)
    (hpLu : ∀ y a, a ∈ S → (∀ c ∈ S, QL f g L a y ≤ QL f g L c y) → a = pL y)
    (t : ℕ → ℝ) (x y : ℕ → E) (_ht1 : t 1 = 1)
    (_ht : ∀ k ≥ 1, t (k + 1) = (1 + Real.sqrt (1 + 4 * t k ^ 2)) / 2) (_hy1 : y 1 = x 0)
    (hx : ∀ k ≥ 1, x k = pL (y k))
    (hy : ∀ k ≥ 1, y (k + 1) = x k + ((t k - 1) / t (k + 1)) • (x k - x (k - 1)))
    (P2 : E × E → E × E)
    (hP2 : ∀ z, IsProx qM2 (1 / L) (S ×ˢ Set.univ) (fun w => g w.1) z (P2 z))
    (G1 G3 : E × E → E × E) (hG1 : IsGradPS (fun z : E × E => f z.1) G1)
    (hG3 : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ‖z.2‖ ^ 2) G3) (k : ℕ) (hk : 1 ≤ k) :
    dstep 1 (M3inv ((t k - 1) / t (k + 1))) G3
        (P2 (dstep 1 (M1inv (1 / L)) G1 (chiF (y k, x (k - 1))))) =
      chiF (y (k + 1), x k) := by
  have eG1 : G1 = fun z => (∇ f z.1, 0) := hG1.unique (isGradPS_fst hf)
  have eG3 : G3 = fun z => (0, (1 : ℝ) • z.2) := by
    refine hG3.unique ?_
    have := isGradPS_kinS (E := E) 1
    simpa using this
  subst eG1 eG3
  set u := y k - (1 / L) • ∇ f (y k) with hu
  -- first letter
  have h1 : dstep 1 (M1inv (1 / L)) (fun z : E × E => (∇ f z.1, 0)) (chiF (y k, x (k - 1))) =
      (u, u - x (k - 1)) := by
    refine Prod.ext ?_ ?_ <;> simp [dstep, M1inv, chiF, hu] <;> abel
  rw [h1]
  -- second letter
  obtain ⟨hzS, hzmin, hz2⟩ := prox_M2 (hP2 (u, u - x (k - 1)))
  set z := P2 (u, u - x (k - 1)) with hz
  have hz1 : z.1 = x k := by
    rw [hx k hk]
    refine hpLu (y k) z.1 hzS (fun c hc => ?_)
    rw [QL_eq f g hL, QL_eq f g hL]
    have := hzmin c hc
    rw [← hu]
    nlinarith
  have hzeq : z = (x k, x k - x (k - 1)) := by
    refine Prod.ext hz1 ?_
    rw [hz2, hz1]; simp only; abel
  rw [hzeq]
  -- third letter
  rw [hy k hk]
  refine Prod.ext ?_ ?_ <;> simp [dstep, M3inv, chiF] <;> module

/-- The FISTA weight `β_k = (t_k − 1)/t_{k+1}` lies in `[0, 1)` for every `k ≥ 1`. -/
theorem fista_beta (t : ℕ → ℝ) (ht1 : t 1 = 1)
    (ht : ∀ k ≥ 1, t (k + 1) = (1 + Real.sqrt (1 + 4 * t k ^ 2)) / 2) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ (t k - 1) / t (k + 1) ∧ (t k - 1) / t (k + 1) < 1 := by
  have hge : ∀ k ≥ 1, 1 ≤ t k := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => rw [ht1]
    | succ n hn ih =>
      rw [ht n hn]
      have : 2 * t n ≤ Real.sqrt (1 + 4 * t n ^ 2) :=
        Real.le_sqrt_of_sq_le (by nlinarith)
      linarith
  have h1 := hge k hk
  have hs : 2 * t k ≤ Real.sqrt (1 + 4 * t k ^ 2) := Real.le_sqrt_of_sq_le (by nlinarith)
  have h2 : t k + 1 / 2 ≤ t (k + 1) := by rw [ht k hk]; linarith
  have hpos : 0 < t (k + 1) := by linarith
  refine ⟨div_nonneg (by linarith) hpos.le, (div_lt_one hpos).mpr (by linarith)⟩

/-- **Proposition prop:fista-word, the discrete Nesterov scheme.** Su–Boyd–Candès eq. (1),
p. 2: `x_k = y_{k−1} − s∇f(y_{k−1})`, `y_k = x_k + ((k−1)/(k+2))(x_k − x_{k−1})`. With the
projective letter omitted, `1/L` replaced by `s` in `M₁` and `β_k = (k−1)/(k+2)`, the word maps
`χ(y_{k−1}, x_{k−1})` to `χ(y_k, x_k)` for every `k ≥ 1`. -/
theorem su_word (f : E → ℝ) (hf : Differentiable ℝ f) (s : ℝ) (x y : ℕ → E)
    (hx : ∀ k ≥ 1, x k = y (k - 1) - s • ∇ f (y (k - 1)))
    (hy : ∀ k ≥ 1, y k = x k + (((k : ℝ) - 1) / ((k : ℝ) + 2)) • (x k - x (k - 1)))
    (G1 G3 : E × E → E × E) (hG1 : IsGradPS (fun z : E × E => f z.1) G1)
    (hG3 : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ‖z.2‖ ^ 2) G3) (k : ℕ) (hk : 1 ≤ k) :
    dstep 1 (M3inv (((k : ℝ) - 1) / ((k : ℝ) + 2))) G3
        (dstep 1 (M1inv s) G1 (chiF (y (k - 1), x (k - 1)))) = chiF (y k, x k) := by
  have eG1 : G1 = fun z => (∇ f z.1, 0) := hG1.unique (isGradPS_fst hf)
  have eG3 : G3 = fun z => (0, (1 : ℝ) • z.2) := by
    refine hG3.unique ?_
    have := isGradPS_kinS (E := E) 1
    simpa using this
  subst eG1 eG3
  rw [hy k hk, hx k hk]
  refine Prod.ext ?_ ?_ <;> simp [dstep, M1inv, M3inv, chiF] <;> module

/-- The Nesterov weight `(k−1)/(k+2)` lies in `[0, 1)` for `k ≥ 1`. -/
theorem su_beta (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ ((k : ℝ) - 1) / ((k : ℝ) + 2) ∧ ((k : ℝ) - 1) / ((k : ℝ) + 2) < 1 := by
  have : (1 : ℝ) ≤ k := by exact_mod_cast hk
  exact ⟨div_nonneg (by linarith) (by linarith), (div_lt_one (by linarith)).mpr (by linarith)⟩

end FISTA

/-! ## Proposition prop:hb-word (heavy ball as a word; row 4) -/

section HeavyBall

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- A Störmer–Verlet step with a known drift endpoint `w`. -/
theorem sv_of_drift {X : Type*} [AddCommGroup X] [Module ℝ X] (GV : X → X) (N : X →ₗ[ℝ] X)
    (h : ℝ) (z : X × X) (w : X) (hw : z.1 + h • N (z.2 - (h / 2) • GV z.1) = w) :
    sv GV N h z = (w, (z.2 - (h / 2) • GV z.1) - (h / 2) • GV w) := by
  subst hw; rfl

/-- The printed heavy-ball step on `(x_k, x_{k−1})` (Lessard–Recht–Packard §2, p. 5):
`S(x, x') = (x − α∇f(x) + β(x − x'), x)`. -/
def hbStep (f : E → ℝ) (α β : ℝ) (z : E × E) : E × E :=
  (z.1 - α • ∇ f z.1 + β • (z.1 - z.2), z.1)

/-- The conjugacy `χ(x, x') = (x, (x − x')/s − ½∇f(x))`. -/
def chiHB (f : E → ℝ) (s : ℝ) (z : E × E) : E × E :=
  (z.1, (1 / s) • (z.1 - z.2) - (1 / 2 : ℝ) • ∇ f z.1)

/-- Its inverse `(q, p) ↦ (q, q − s(p + ½∇f(q)))`. -/
def chiHBinv (f : E → ℝ) (s : ℝ) (z : E × E) : E × E :=
  (z.1, z.1 - s • (z.2 + (1 / 2 : ℝ) • ∇ f z.1))

/-- The printed metric `M' = diag(I, sI)` and the inverse used by the dissipative letter. -/
def Mpr (s : ℝ) : E × E →ₗ[ℝ] E × E := bdiag LinearMap.id (s • LinearMap.id)
def MprInv (s : ℝ) : E × E →ₗ[ℝ] E × E := bdiag LinearMap.id (s⁻¹ • LinearMap.id)

/-- The printed mass `M_p = s⁻¹I` and the inverse `M_p⁻¹ = sI` used by the Störmer–Verlet letter. -/
def MpHB (s : ℝ) : E →ₗ[ℝ] E := s⁻¹ • LinearMap.id
def MpHBinv (s : ℝ) : E →ₗ[ℝ] E := s • LinearMap.id

omit [CompleteSpace E] in
/-- The inverses are two-sided (`s ≠ 0`). -/
theorem hb_inverses {s : ℝ} (hs : s ≠ 0) :
    (∀ z : E × E, Mpr s (MprInv s z) = z ∧ MprInv s (Mpr s z) = z) ∧
    (∀ v : E, MpHB s (MpHBinv s v) = v ∧ MpHBinv s (MpHB s v) = v) := by
  refine ⟨fun z => ⟨?_, ?_⟩, fun v => ⟨?_, ?_⟩⟩ <;>
    simp [Mpr, MprInv, MpHB, MpHBinv, smul_smul, hs]

/-- **Proposition prop:hb-word.** Let `α > 0`, `β ∈ (−1, 1)`, `s = 2α/(1+β)`,
`K(q,p) = ½ s|p|²`, `M' = diag(I, sI)`, `Ψ = Φ^SV_1 ∘ D^{1−β,M'}_K` with `V = f`, `M_p = s⁻¹I`.
Then `χ` is a bijection and `Ψ ∘ χ = χ ∘ S`. `GK` is the phase-space gradient of `K`. -/
theorem hb_word (f : E → ℝ) {α β : ℝ} (hα : 0 < α) (hβ1 : -1 < β) (_hβ2 : β < 1)
    (GK : E × E → E × E)
    (hGK : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * (2 * α / (1 + β)) * ‖z.2‖ ^ 2) GK) :
    (∀ z, chiHBinv f (2 * α / (1 + β)) (chiHB f (2 * α / (1 + β)) z) = z) ∧
    (∀ z, chiHB f (2 * α / (1 + β)) (chiHBinv f (2 * α / (1 + β)) z) = z) ∧
    ∀ z, sv (∇ f) (MpHBinv (2 * α / (1 + β))) 1
        (dstep (1 - β) (MprInv (2 * α / (1 + β))) GK (chiHB f (2 * α / (1 + β)) z)) =
      chiHB f (2 * α / (1 + β)) (hbStep f α β z) := by
  set s := 2 * α / (1 + β) with hsdef
  have h1β : 0 < 1 + β := by linarith
  have hs : 0 < s := by positivity
  have hs0 : s ≠ 0 := hs.ne'
  have hαs : α = s * (1 + β) / 2 := by rw [hsdef]; field_simp
  have eGK : GK = fun z => (0, s • z.2) := hGK.unique (isGradPS_kinS s)
  subst eGK
  refine ⟨fun z => ?_, fun z => ?_, fun z => ?_⟩
  · refine Prod.ext rfl ?_
    simp only [chiHBinv, chiHB]
    match_scalars <;> field_simp <;> ring
  · refine Prod.ext rfl ?_
    simp only [chiHBinv, chiHB]
    match_scalars <;> field_simp <;> ring
  · obtain ⟨x, x'⟩ := z
    -- the damping letter: (q, p) ↦ (q, βp)
    have hD : dstep (1 - β) (MprInv s) (fun z : E × E => ((0 : E), s • z.2)) (chiHB f s (x, x')) =
        (x, β • ((1 / s) • (x - x') - (1 / 2 : ℝ) • ∇ f x)) := by
      refine Prod.ext ?_ ?_
      · simp [dstep, MprInv, chiHB]
      · simp only [dstep, MprInv, chiHB, bdiag_apply, LinearMap.smul_apply, LinearMap.id_apply,
          Prod.snd_sub, Prod.smul_snd, smul_smul]
        rw [inv_mul_cancel₀ hs0]
        module
    rw [hD]
    set xp := x - α • ∇ f x + β • (x - x') with hxp
    rw [sv_of_drift (∇ f) (MpHBinv s) 1 _ xp]
    · simp only [chiHB, hbStep, ← hxp]
      refine Prod.ext rfl ?_
      simp only [hxp, hαs]
      match_scalars <;> field_simp <;> ring
    · simp only [MpHBinv, LinearMap.smul_apply, LinearMap.id_apply, hxp, hαs]
      match_scalars <;> field_simp <;> ring

end HeavyBall

/-! ## The thirteen rows -/

/-! ### Row 1: ISTA (Beck–Teboulle eq. (1.5), p. 185; the display after (2.3), p. 188) -/

section Row1

variable {n : ℕ}

/-- `‖x‖₁ = Σ_i |x_i|`. -/
def l1 (x : EuclideanSpace ℝ (Fin n)) : ℝ := ∑ i, |x i|

/-- Beck–Teboulle (1.5): `T_α(x)_i = (|x_i| − α)₊ sgn(x_i)`. -/
def shrink (α : ℝ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => max (|x i| - α) 0 * Real.sign (x i))

/-- The printed ISTA update (p. 188): `x_k = T_{λt}(x_{k−1} − t∇f(x_{k−1}))`. -/
def istaStep (f : EuclideanSpace ℝ (Fin n) → ℝ) (lam t : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  shrink (lam * t) (x - t • ∇ f x)

/-- **Row 1.** `prox_{tg} ∘ D^{t,I}_f = ISTA`, `g = λ‖·‖₁`, for each step `t > 0` (so for `t`
constant or indexed by `k`). `P` is the prox letter of `tg`. Classical input, as the source
states it (BT09 p. 188, "by simple calculus produces"): every minimiser of (2.3),
`(1/2t)‖x − u‖² + λ‖x‖₁`, is `T_{λt}(u)`. -/
theorem row1_ista (f : EuclideanSpace ℝ (Fin n) → ℝ) (lam t : ℝ) (ht : 0 < t)
    (hT : ∀ u y : EuclideanSpace ℝ (Fin n),
      (∀ x, 1 / (2 * t) * ‖y - u‖ ^ 2 + lam * l1 y ≤ 1 / (2 * t) * ‖x - u‖ ^ 2 + lam * l1 x) →
        y = shrink (lam * t) u)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : ∀ u, IsProx (fun w => ‖w‖ ^ 2) t Set.univ (fun x => lam * l1 x) u (P u))
    (x : EuclideanSpace ℝ (Fin n)) :
    P (dstep t LinearMap.id (∇ f) x) = istaStep f lam t x := by
  rw [istaStep]
  have e : dstep t LinearMap.id (∇ f) x = x - t • ∇ f x := rfl
  rw [e]
  refine hT _ _ (fun y => ?_)
  have h := (hP (x - t • ∇ f x)).2 y (Set.mem_univ _)
  have h2 : 1 / (2 * t) * ‖P (x - t • ∇ f x) - (x - t • ∇ f x)‖ ^ 2 +
      lam * l1 (P (x - t • ∇ f x)) =
      (t * (lam * l1 (P (x - t • ∇ f x))) + ‖P (x - t • ∇ f x) - (x - t • ∇ f x)‖ ^ 2 / 2) / t := by
    field_simp; ring
  have h3 : 1 / (2 * t) * ‖y - (x - t • ∇ f x)‖ ^ 2 + lam * l1 y =
      (t * (lam * l1 y) + ‖y - (x - t • ∇ f x)‖ ^ 2 / 2) / t := by
    field_simp; ring
  rw [h2, h3]
  exact div_le_div_of_nonneg_right h ht.le

end Row1

/-! ### Row 2: damped Newton (Boyd–Vandenberghe §9.5.1, p. 484; Algorithm 9.5, p. 487) -/

section Row2

variable {d : ℕ}

/-- Boyd–Vandenberghe: `Δx_nt = −∇²f(x)⁻¹∇f(x)` and the update `x := x + tΔx_nt`
(`gradf`, `hess` are the gradient and Hessian of `f` in coordinates). -/
def newtonStep (gradf : (Fin d → ℝ) → (Fin d → ℝ)) (hess : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ :=
  x + t • (-((hess x)⁻¹.mulVec (gradf x)))

/-- **Row 2.** `D^{t,∇²f(x)}_f(x) = x + tΔx_nt` for every value of `t`, and the bound
`mI ⪯ ∇²f(x)` (`m > 0`) makes the metric invertible, so `M(x)⁻¹` is a two-sided inverse. -/
theorem row2_newton (gradf : (Fin d → ℝ) → (Fin d → ℝ))
    (hess : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ) (t m : ℝ) (hm : 0 < m)
    (x : Fin d → ℝ) (hlow : (hess x - m • (1 : Matrix (Fin d) (Fin d) ℝ)).PosSemidef) :
    dstep t (Matrix.mulVecLin (hess x)⁻¹) gradf x = newtonStep gradf hess t x ∧
      hess x * (hess x)⁻¹ = 1 ∧ (hess x)⁻¹ * hess x = 1 := by
  have hpd : (hess x).PosDef := by
    have := ((Matrix.PosDef.one (R := ℝ) (n := Fin d)).smul hm).add_posSemidef hlow
    simpa using this
  have hu : IsUnit (hess x).det := (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  refine ⟨?_, Matrix.mul_nonsing_inv _ hu, Matrix.nonsing_inv_mul _ hu⟩
  simp only [dstep, newtonStep, Matrix.mulVecLin_apply, smul_neg]
  abel

end Row2

section Rows

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Row 5: Nesterov's ODE (Su–Boyd–Candès eq. (3), p. 2) -/

/-- The printed metric `M_t = diag(I, (t/3)I)` and its inverse `diag(I, (3/t)I)`. -/
def Mt (t : ℝ) : E × E →ₗ[ℝ] E × E := bdiag LinearMap.id ((t / 3) • LinearMap.id)
def MtInv (t : ℝ) : E × E →ₗ[ℝ] E × E := bdiag LinearMap.id ((3 / t) • LinearMap.id)

omit [CompleteSpace E] in
theorem Mt_inv {t : ℝ} (ht : 0 < t) (z : E × E) : Mt t (MtInv t z) = z ∧ MtInv t (Mt t z) = z := by
  have : t ≠ 0 := ht.ne'
  constructor <;> refine Prod.ext rfl ?_ <;> simp [Mt, MtInv, smul_smul] <;> field_simp <;> simp

/-- **Row 5.** The conservative field (`V = f`, `M_p = I`) plus the dissipative field of
`K = ½|p|²` with metric `diag(I, (t/3)I)` is `(p, −∇f(q) − (3/t)p)`, and `(Ẋ, Ẍ)` equals
this field at `(X, Ẋ)` exactly when `Ẍ + (3/t)Ẋ + ∇f(X) = 0` (vector fields, not solutions). -/
theorem row5_nesterov_ode (f : E → ℝ) {t : ℝ} (_ht : 0 < t) (GK : E × E → E × E)
    (hGK : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ‖z.2‖ ^ 2) GK) :
    (∀ z : E × E, consField (∇ f) LinearMap.id z + dissField (MtInv t) GK z =
      (z.2, -∇ f z.1 - (3 / t) • z.2)) ∧
    (∀ X Xd Xdd : E, Xdd + (3 / t) • Xd + ∇ f X = 0 ↔
      (Xd, Xdd) = consField (∇ f) LinearMap.id (X, Xd) + dissField (MtInv t) GK (X, Xd)) := by
  have eGK : GK = fun z => (0, (1 : ℝ) • z.2) := by
    refine hGK.unique ?_
    simpa using isGradPS_kinS (E := E) 1
  subst eGK
  have hfield : ∀ z : E × E, consField (∇ f) LinearMap.id z + dissField (MtInv t) (fun z : E × E => ((0 : E), (1 : ℝ) • z.2)) z =
      (z.2, -∇ f z.1 - (3 / t) • z.2) := by
    intro z
    refine Prod.ext ?_ ?_ <;> simp [consField, dissField, MtInv] ; abel
  refine ⟨hfield, fun X Xd Xdd => ?_⟩
  rw [hfield]
  simp only [Prod.mk.injEq, true_and]
  constructor
  · intro h; rw [← sub_eq_zero]; rw [← h]; abel
  · intro h; rw [h]; abel

/-! ### Row 6: Langevin diffusion (Durmus–Moulines eq. (1), p. 1) -/

/-- The generator of a diffusion with drift `b` and diffusion matrix `a = σσᵀ`, at a point where
the test function has gradient `v` and Hessian `H` (Pavliotis eq. (3.47)): `b·v + ½ a : H`. -/
def itoGen [FiniteDimensional ℝ E] (b v : E) (a H : E →ₗ[ℝ] E) : ℝ :=
  ⟪b, v⟫ + (1 / 2 : ℝ) * LinearMap.trace ℝ E (a ∘ₗ H)

/-- The generator of the word's continuous object at a point where the test function has
gradient `v` and Hessian `H`: the dissipative field `−M⁻¹∇U` acting on `v`, plus the noise
generator `T Σ : D²` (Pavliotis eq. (3.47)). -/
def genWord [FiniteDimensional ℝ E] (Minv : E →ₗ[ℝ] E) (GU : E → E) (T : ℝ) (Sig : E →ₗ[ℝ] E)
    (y v : E) (H : E →ₗ[ℝ] E) : ℝ :=
  ⟪dissField Minv GU y, v⟫ + T * LinearMap.trace ℝ E (Sig ∘ₗ H)

/-- **Row 6.** Durmus–Moulines `dY = −∇U(Y)dt + √2 dB`: drift `−∇U`, diffusion coefficient
`σ = √2 I` (symmetric, so `σσᵀ = σ ∘ σ`). The word: dissipative field of `U` (`M = I`) plus the
noise of `T = 1`, `Σ = I` (coefficient `√(2T) Σ^{1/2}`). Drift, diffusion coefficient and
generator agree. -/
theorem row6_langevin [FiniteDimensional ℝ E] (U : E → ℝ) :
    (∀ y, dissField LinearMap.id (∇ U) y = -∇ U y) ∧
    (Real.sqrt (2 * 1) • (LinearMap.id : E →ₗ[ℝ] E) = Real.sqrt 2 • LinearMap.id) ∧
    (∀ (y v : E) (H : E →ₗ[ℝ] E),
      genWord LinearMap.id (∇ U) 1 LinearMap.id y v H =
        itoGen (-∇ U y) v ((Real.sqrt 2 • LinearMap.id) ∘ₗ (Real.sqrt 2 • LinearMap.id)) H) := by
  refine ⟨fun y => rfl, by norm_num, fun y v H => ?_⟩
  simp only [genWord, itoGen, dissField, LinearMap.id_apply, one_mul]
  congr 1
  have : (Real.sqrt 2 • (LinearMap.id : E →ₗ[ℝ] E)) ∘ₗ (Real.sqrt 2 • LinearMap.id) =
      (2 : ℝ) • LinearMap.id := by
    ext w; simp [smul_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  rw [this, LinearMap.smul_comp, map_smul, smul_eq_mul]; simp

/-! ### Row 7: unadjusted Langevin algorithm (Durmus–Moulines eq. (2), p. 2) -/

/-- **Row 7.** `X_{k+1} = X_k − γ_{k+1}∇U(X_k) + √(2γ_{k+1}) Z_{k+1}` is
`N_{γ_{k+1}} ∘ D^{γ_{k+1},I}_U` (`T = 1`, `Σ = I`), pathwise in the draw `Z_{k+1}`. -/
theorem row7_ula (U : E → ℝ) (γ : ℕ → ℝ) (Z : ℕ → E) (k : ℕ) (x : E) :
    nstep 1 (γ (k + 1)) LinearMap.id (Z (k + 1)) (dstep (γ (k + 1)) LinearMap.id (∇ U) x) =
      x - γ (k + 1) • ∇ U x + Real.sqrt (2 * γ (k + 1)) • Z (k + 1) := by
  simp [nstep, dstep]

/-! ### Row 8: MYULA (Durmus–Moulines–Pereyra eq. (12), p. 9; eq. (11), p. 7) -/

/-- The Moreau envelope `g^λ(x) = inf_y g(y) + ‖y − x‖²/(2λ)` (inf over `dom g`). -/
def moreau (lam : ℝ) (S : Set E) (g : E → ℝ) (x : E) : ℝ :=
  ⨅ y : S, g y + ‖(y : E) - x‖ ^ 2 / (2 * lam)

/-- **Row 8.** MYULA's printed update equals `N_γ ∘ D^{γ,I}_{f+g^λ}` (`T = 1`). Classical
input (Bauschke–Combettes Prop. 12.30, eq. (12.28)): `∇g^λ = λ⁻¹(Id − prox_{λg})`. -/
theorem row8_myula (f g : E → ℝ) (S : Set E) {lam γ : ℝ} (hlam : 0 < lam)
    (hf : Differentiable ℝ f) (P : E → E)
    (_hP : ∀ x, IsProx (fun w => ‖w‖ ^ 2) lam S g x (P x))
    (hMY : ∀ x, HasGradientAt (moreau lam S g) (lam⁻¹ • (x - P x)) x) (Z x : E) :
    nstep 1 γ LinearMap.id Z (dstep γ LinearMap.id (∇ (fun y => f y + moreau lam S g y)) x) =
      (1 - γ / lam) • x - γ • ∇ f x + (γ / lam) • P x + Real.sqrt (2 * γ) • Z := by
  have hg : ∇ (fun y => f y + moreau lam S g y) x = ∇ f x + lam⁻¹ • (x - P x) := by
    refine HasGradientAt.gradient ?_
    rw [hasGradientAt_iff_hasFDerivAt, map_add]
    exact (hf x).hasGradientAt.hasFDerivAt.add (hMY x).hasFDerivAt
  simp only [nstep, dstep, LinearMap.id_apply, hg, mul_one]
  have : lam ≠ 0 := hlam.ne'
  match_scalars <;> field_simp

/-! ### Row 9: symmetrised Langevin algorithm (Wibisono eq. (8), p. 7) -/

/-- **Row 9.** `x_{k+1} = (I + ε∇f)⁻¹(x_k − ε∇f(x_k) + √(4ε) z_k)` is
`prox_{εf} ∘ N_{2ε} ∘ D^{ε,I}_f` (`T = 1`). `R` is the source's `(I + ε∇f)⁻¹`
(`R(w) + ε∇f(R(w)) = w`); `P` is the prox letter. Classical input (note (e); Bauschke–Combettes
Prop. 16.44 with Prop. 17.31(i)), for convex `f ∈ C¹`: `y + ε∇f(y) = x ⟺ y = prox_{εf}(x)`. -/
theorem row9_sla (f : E → ℝ) (_hconv : ConvexOn ℝ Set.univ f) (_hf : Differentiable ℝ f)
    {ε : ℝ} (_hε : 0 < ε) (P : E → E)
    (_hP : ∀ x, IsProx (fun w => ‖w‖ ^ 2) ε Set.univ f x (P x))
    (hres : ∀ x y, y + ε • ∇ f y = x ↔ y = P x)
    (R : E → E) (hR : ∀ w, R w + ε • ∇ f (R w) = w) (z x : E) :
    P (nstep 1 (2 * ε) LinearMap.id z (dstep ε LinearMap.id (∇ f) x)) =
      R (x - ε • ∇ f x + Real.sqrt (4 * ε) • z) := by
  have e : nstep 1 (2 * ε) LinearMap.id z (dstep ε LinearMap.id (∇ f) x) =
      x - ε • ∇ f x + Real.sqrt (4 * ε) • z := by
    simp only [nstep, dstep, LinearMap.id_apply]
    congr 3; ring
  rw [e]
  exact ((hres _ _).mp (hR _)).symm

/-! ### Row 10: projected Langevin Monte Carlo (Bubeck–Eldan–Lehec eq. (1), p. 1) -/

omit [CompleteSpace E] in
/-- Nearest points of a convex set are unique. -/
theorem nearest_unique {C : Set E} (hC : Convex ℝ C) {w p₁ p₂ : E}
    (h₁ : p₁ ∈ C ∧ ∀ y ∈ C, ‖w - p₁‖ ≤ ‖w - y‖) (h₂ : p₂ ∈ C ∧ ∀ y ∈ C, ‖w - p₂‖ ≤ ‖w - y‖) :
    p₁ = p₂ := by
  have key : ∀ p, (p ∈ C ∧ ∀ y ∈ C, ‖w - p‖ ≤ ‖w - y‖) → ∀ y ∈ C, ⟪w - p, y - p⟫ ≤ 0 := by
    intro p hp
    have hne : Nonempty C := ⟨⟨p, hp.1⟩⟩
    refine (norm_eq_iInf_iff_real_inner_le_zero hC hp.1).mp ?_
    refine le_antisymm (le_ciInf fun y => hp.2 y y.2) ?_
    have hb : BddBelow (Set.range fun y : C => ‖w - (y : E)‖) :=
      ⟨0, by rintro _ ⟨y, rfl⟩; exact norm_nonneg _⟩
    exact ciInf_le hb ⟨p, hp.1⟩
  have a := key p₁ h₁ p₂ h₂.1
  have b := key p₂ h₂ p₁ h₁.1
  have : ‖p₂ - p₁‖ ^ 2 ≤ 0 := by
    have e : ⟪w - p₁, p₂ - p₁⟫ + ⟪w - p₂, p₁ - p₂⟫ = ‖p₂ - p₁‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq]
      have : p₁ - p₂ = -(p₂ - p₁) := by abel
      rw [this, inner_neg_right, ← sub_eq_add_neg, ← inner_sub_left]
      congr 1; abel
    linarith
  have : ‖p₂ - p₁‖ = 0 := by nlinarith [norm_nonneg (p₂ - p₁)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp this)).symm

/-- **Row 10.** `X_{k+1} = P_K(X_k − (η/2)∇f(X_k) + √η ξ_k)` is
`prox_{ι_C} ∘ N_{η/2} ∘ D^{η/2,I}_f` (`T = 1`), for `C` convex and `f` defined on the whole
space. `PK` is the Euclidean projection (nearest point); `P` the prox letter of `ι_C`
(`g = 0` on `dom = C`). -/
theorem row10_plmc (f : E → ℝ) (C : Set E) (hC : Convex ℝ C) (η : ℝ) (PK P : E → E)
    (hPK : ∀ w, PK w ∈ C ∧ ∀ y ∈ C, ‖w - PK w‖ ≤ ‖w - y‖)
    (hP : ∀ w, IsProx (fun v => ‖v‖ ^ 2) 1 C (fun _ => 0) w (P w)) (ξ x : E) :
    P (nstep 1 (η / 2) LinearMap.id ξ (dstep (η / 2) LinearMap.id (∇ f) x)) =
      PK (x - (η / 2) • ∇ f x + Real.sqrt η • ξ) := by
  have e : nstep 1 (η / 2) LinearMap.id ξ (dstep (η / 2) LinearMap.id (∇ f) x) =
      x - (η / 2) • ∇ f x + Real.sqrt η • ξ := by
    simp only [nstep, dstep, LinearMap.id_apply]
    congr 3; ring
  rw [e]
  set w := x - (η / 2) • ∇ f x + Real.sqrt η • ξ
  refine nearest_unique hC ⟨(hP w).1, fun y hy => ?_⟩ (hPK w)
  have h := (hP w).2 y hy
  simp only [mul_zero, zero_add] at h
  have h' : ‖P w - w‖ ^ 2 ≤ ‖y - w‖ ^ 2 := by linarith
  rw [norm_sub_rev w, norm_sub_rev w]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h'

/-! ### Row 12: underdamped Langevin, BABO (Leimkuhler–Matthews §2.1, p. 7; Appendix, p. 22) -/

/-- The printed BABO step: velocity Verlet with mass `M` (Neal (2.28)–(2.30)), then the
Ornstein–Uhlenbeck step `p̂ = c₁p + c₃M^{1/2}R` (LM13 Appendix). -/
def baboStep (GU : E → E) (Minv Mhalf : E →ₗ[ℝ] E) (δt c₁ c₃ : ℝ) (R : E) (z : E × E) : E × E :=
  let ph := z.2 - (δt / 2) • GU z.1
  let q' := z.1 + δt • Minv ph
  (q', c₁ • (ph - (δt / 2) • GU q') + c₃ • Mhalf R)

omit [CompleteSpace E] in
/-- The damping letter `D^{1−c,M'}_K` with `M' = diag(I, M⁻¹)` (inverse `diag(I, M)`) maps
`(q, p)` to `(q, c p)`, for the kinetic energy `K = ½pᵀM⁻¹p`. -/
theorem damp_K (M Minv : E →L[ℝ] E) (hinv : ∀ v, M (Minv v) = v)
    (hsym : ∀ u v, ⟪Minv u, v⟫ = ⟪u, Minv v⟫) (GK : E × E → E × E)
    (hGK : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ⟪Minv z.2, z.2⟫) GK) (c : ℝ) (z : E × E) :
    dstep (1 - c) (bdiag LinearMap.id (M : E →ₗ[ℝ] E)) GK z = (z.1, c • z.2) := by
  have eGK : GK = fun z => (0, Minv z.2) := hGK.unique (isGradPS_kin Minv hsym)
  subst eGK
  refine Prod.ext (by simp [dstep]) ?_
  simp only [dstep, bdiag_apply, Prod.snd_sub, Prod.smul_snd, ContinuousLinearMap.coe_coe, hinv]
  module

/-- **Row 12.** `ψ_BABO = N^{(p)}_{(1−c₁²)/2} ∘ D^{1−c₁,M'}_K ∘ Φ^SV_{δt}` with `V = U`,
`M_p = M`, `M' = diag(I, M⁻¹)`, `T = k_BT`, `Σ_p = M`, `c₁ = e^{−γδt}`,
`c₃ = √(k_BT(1 − c₁²))`, pathwise in the draw `R`. -/
theorem row12_babo (U : E → ℝ) (M Minv Mhalf : E →L[ℝ] E) (hinv : ∀ v, M (Minv v) = v)
    (hsym : ∀ u v, ⟪Minv u, v⟫ = ⟪u, Minv v⟫) (GK : E × E → E × E)
    (hGK : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ⟪Minv z.2, z.2⟫) GK)
    (γ δt kBT : ℝ) (R : E) (z : E × E) :
    nstepP kBT ((1 - Real.exp (-γ * δt) ^ 2) / 2) (Mhalf : E →ₗ[ℝ] E) R
        (dstep (1 - Real.exp (-γ * δt)) (bdiag LinearMap.id (M : E →ₗ[ℝ] E)) GK
          (sv (∇ U) (Minv : E →ₗ[ℝ] E) δt z)) =
      baboStep (∇ U) Minv Mhalf δt (Real.exp (-γ * δt))
        (Real.sqrt (kBT * (1 - Real.exp (-γ * δt) ^ 2))) R z := by
  rw [damp_K M Minv hinv hsym GK hGK]
  simp only [nstepP, nstep, sv, baboStep, ContinuousLinearMap.coe_coe]
  refine Prod.ext rfl ?_
  simp only
  congr 3; ring

omit [CompleteSpace E] in
/-- **Note (f), Neal's partial momentum refreshment (eq. (5.19), p. 39).** For `ϱ ∈ (−1, 1)` the
same two letters with `c₁ = ϱ`, `T = 1` give `p' = ϱp + (1 − ϱ²)^{1/2} n`, `n = M^{1/2}ξ`. -/
theorem row12_refresh (M Minv Mhalf : E →L[ℝ] E) (hinv : ∀ v, M (Minv v) = v)
    (hsym : ∀ u v, ⟪Minv u, v⟫ = ⟪u, Minv v⟫) (GK : E × E → E × E)
    (hGK : IsGradPS (fun z : E × E => (1 / 2 : ℝ) * ⟪Minv z.2, z.2⟫) GK)
    (ϱ : ℝ) (ξ : E) (z : E × E) :
    nstepP 1 ((1 - ϱ ^ 2) / 2) (Mhalf : E →ₗ[ℝ] E) ξ
        (dstep (1 - ϱ) (bdiag LinearMap.id (M : E →ₗ[ℝ] E)) GK z) =
      (z.1, ϱ • z.2 + Real.sqrt (1 - ϱ ^ 2) • Mhalf ξ) := by
  rw [damp_K M Minv hinv hsym GK hGK]
  simp only [nstepP, nstep, ContinuousLinearMap.coe_coe]
  refine Prod.ext rfl ?_
  simp only
  congr 3; ring

omit [CompleteSpace E] in
/-- The printed metric `M' = diag(I, M⁻¹)` has inverse `diag(I, M)`. -/
theorem row12_metric_inv (M Minv : E →L[ℝ] E) (hl : ∀ v, M (Minv v) = v)
    (hr : ∀ v, Minv (M v) = v) (z : E × E) :
    bdiag LinearMap.id (Minv : E →ₗ[ℝ] E) (bdiag LinearMap.id (M : E →ₗ[ℝ] E) z) = z ∧
      bdiag LinearMap.id (M : E →ₗ[ℝ] E) (bdiag LinearMap.id (Minv : E →ₗ[ℝ] E) z) = z := by
  constructor <;> refine Prod.ext rfl ?_ <;> simp [hl, hr]

end Rows

/-! ### Row 11: leapfrog (Neal eqs. (2.28)–(2.30), p. 8) -/

section Row11

variable {d : ℕ}

/-- Neal's printed leapfrog step, coordinatewise: `p_i(t+ε/2) = p_i − (ε/2)∂U/∂q_i(q)`,
`q_i(t+ε) = q_i + ε p_i(t+ε/2)/m_i`, `p_i(t+ε) = p_i(t+ε/2) − (ε/2)∂U/∂q_i(q(t+ε))`
(`dU q i = ∂U/∂q_i(q)`). -/
def leapfrog (dU : (Fin d → ℝ) → (Fin d → ℝ)) (m : Fin d → ℝ) (ε : ℝ)
    (z : (Fin d → ℝ) × (Fin d → ℝ)) : (Fin d → ℝ) × (Fin d → ℝ) :=
  let ph : Fin d → ℝ := fun i => z.2 i - ε / 2 * dU z.1 i
  let q' : Fin d → ℝ := fun i => z.1 i + ε * ph i / m i
  (q', fun i => ph i - ε / 2 * dU q' i)

/-- **Row 11.** The leapfrog step is `Φ^SV_ε` with `V = U`, `M_p = diag(m_i)` (A3's `svD` with
inverse mass `diag(1/m_i)`), and `diag(m_i)⁻¹ = diag(1/m_i)` for `m_i > 0`. -/
theorem row11_leapfrog (dU : (Fin d → ℝ) → (Fin d → ℝ)) (m : Fin d → ℝ) (hm : ∀ i, 0 < m i)
    (ε : ℝ) (z : (Fin d → ℝ) × (Fin d → ℝ)) :
    leapfrog dU m ε z = OCF.A3.svD dU (Matrix.diagonal fun i => (m i)⁻¹) ε z ∧
      (Matrix.diagonal m)⁻¹ = Matrix.diagonal fun i => (m i)⁻¹ := by
  refine ⟨?_, ?_⟩
  · have hq : (fun i => z.1 i + ε * (z.2 i - ε / 2 * dU z.1 i) / m i) =
        z.1 + ε • ((Matrix.diagonal (fun i => (m i)⁻¹)).mulVec (z.2 - (ε / 2) • dU z.1)) := by
      funext i; simp [Matrix.mulVec_diagonal]; ring
    simp only [leapfrog, OCF.A3.svD]
    rw [hq]
    refine Prod.ext rfl ?_
    funext i; simp
  · refine Matrix.inv_eq_right_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hm i).ne'

end Row11

/-! ### Row 13: iterative thresholding in an orthonormal basis (Daubechies–Defrise–De Mol
Cor. 2.3, eq. (19); eqs. (16)–(17)) -/

section Row13

variable {E F ι : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E] [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [Fintype ι]

/-- DDD (16): `S_{w,1}(x) = x − w/2` if `x ≥ w/2`, `0` if `|x| < w/2`, `x + w/2` if `x ≤ −w/2`. -/
def S1 (w x : ℝ) : ℝ := if w / 2 ≤ x then x - w / 2 else if x ≤ -(w / 2) then x + w / 2 else 0

/-- DDD (17): `S_w(h) = Σ_γ S_{w_γ,1}(⟨h, φ_γ⟩) φ_γ`. -/
def Sw (b : OrthonormalBasis ι ℝ E) (w : ι → ℝ) (h : E) : E := ∑ γ, S1 (w γ) ⟪h, b γ⟫ • b γ

/-- DDD Cor. 2.3, eq. (19): `f^n = S_w(f^{n−1} + K*(g − Kf^{n−1}))`. -/
def dddStep (b : OrthonormalBasis ι ℝ E) (w : ι → ℝ) (K : E →L[ℝ] F) (gd : F) (f : E) : E :=
  Sw b w (f + ContinuousLinearMap.adjoint K (gd - K f))

/-- `φ_w(u) = Σ_γ w_γ|u_γ|` on the coefficient space. -/
def phiW (w : ι → ℝ) (u : EuclideanSpace ℝ ι) : ℝ := ∑ γ, w γ * |u γ|

/-- The coefficientwise threshold `s(u)_γ = S_{w_γ,1}(u_γ)`. -/
def sThr (w : ι → ℝ) (u : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun γ => S1 (w γ) (u γ))

/-- The analysis operator `W` (rows `φ_γ`): `(W h)_γ = ⟨φ_γ, h⟩`. -/
def Wop (b : OrthonormalBasis ι ℝ E) : E →L[ℝ] EuclideanSpace ℝ ι :=
  (b.repr : E →L[ℝ] EuclideanSpace ℝ ι)

/-- The gradient of `Δ(f) = ‖Kf − g‖²` is `2K*(Kf − g)`. -/
theorem hasGradient_Delta (K : E →L[ℝ] F) (gd : F) (f : E) :
    HasGradientAt (fun x => ‖K x - gd‖ ^ 2) ((2 : ℝ) • ContinuousLinearMap.adjoint K (K f - gd)) f := by
  have h := ((K.hasFDerivAt (x := f)).sub_const gd).norm_sq
  rw [hasGradientAt_iff_hasFDerivAt]
  have e : toDual ℝ E ((2 : ℝ) • ContinuousLinearMap.adjoint K (K f - gd)) =
      (2 • (innerSL ℝ (K f - gd))).comp K := by
    ext v
    simp [ContinuousLinearMap.adjoint_inner_left]
  rw [e]; exact h

/-- **Row 13.** With `W` the analysis operator of the orthonormal basis (a tight frame, `c = 1`),
`g = φ_w ∘ W` and `Δ = ‖K· − g_data‖²`, the word `(prox_{½ g∘Wᵀ})_W ∘ D^{1/2,I}_Δ` is DDD's
eq. (19). `P` is the prox letter of `½ g∘Wᵀ` on the coefficient space. Classical input
(DDD (16) and Prop. 2.1; BT09 (1.5); Bauschke–Combettes Prop. 24.11): the minimiser of
`½φ_w(v) + ½‖v − u‖²` is the coefficientwise threshold `s(u)`. -/
theorem row13_ddd (b : OrthonormalBasis ι ℝ E) (w : ι → ℝ) (_hw : ∀ γ, 0 < w γ)
    (K : E →L[ℝ] F) (gd : F)
    (hsoft : ∀ u v : EuclideanSpace ℝ ι,
      IsProx (fun v => ‖v‖ ^ 2) (1 / 2) Set.univ (phiW w) u v → v = sThr w u)
    (P : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι)
    (hP : ∀ u, IsProx (fun v => ‖v‖ ^ 2) (1 / 2) Set.univ
      (fun u => phiW w (Wop b (ContinuousLinearMap.adjoint (Wop b) u))) u (P u))
    (f : E) :
    (ContinuousLinearMap.adjoint (Wop b) ∘L Wop b = (1 : ℝ) • ContinuousLinearMap.id ℝ E) ∧
    conjW (Wop b) 1 P (dstep (1 / 2) LinearMap.id (∇ (fun x => ‖K x - gd‖ ^ 2)) f) =
      dddStep b w K gd f := by
  have hadj : ContinuousLinearMap.adjoint (Wop b) = (b.repr.symm : EuclideanSpace ℝ ι →L[ℝ] E) :=
    LinearIsometryEquiv.adjoint_eq_symm b.repr
  refine ⟨?_, ?_⟩
  · rw [hadj]; ext x; simp [Wop]
  have hgW : (fun u => phiW w (Wop b (ContinuousLinearMap.adjoint (Wop b) u))) = phiW w := by
    funext u; rw [hadj]; simp [Wop]
  have hPs : ∀ u, P u = sThr w u := by
    intro u
    have h := hP u
    rw [hgW] at h
    exact hsoft u (P u) h
  have hD : dstep (1 / 2) LinearMap.id (∇ (fun x => ‖K x - gd‖ ^ 2)) f =
      f + ContinuousLinearMap.adjoint K (gd - K f) := by
    have hg : ∇ (fun x : E => ‖K x - gd‖ ^ 2) f =
        (2 : ℝ) • ContinuousLinearMap.adjoint K (K f - gd) := (hasGradient_Delta K gd f).gradient
    rw [dstep, LinearMap.id_apply, hg, smul_smul, map_sub, map_sub]
    norm_num
    abel
  rw [hD, conjW, inv_one, one_smul, hadj, dddStep, Sw, hPs]
  change b.repr.symm (sThr w (b.repr (f + ContinuousLinearMap.adjoint K (gd - K f)))) = _
  rw [← b.sum_repr_symm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [real_inner_comm]
  simp [sThr, b.repr_apply_apply, inner_add_right, inner_sub_right]

end Row13

end OCF.E0

#print axioms OCF.E0.IsGradPS.unique
#print axioms OCF.E0.blk_posDef
#print axioms OCF.E0.isGradPS_fst
#print axioms OCF.E0.isGradPS_kin
#print axioms OCF.E0.isGradPS_kinS
#print axioms OCF.E0.sv_eq_A3
#print axioms OCF.E0.chiF_chiF
#print axioms OCF.E0.fista_posDef
#print axioms OCF.E0.prox_M2
#print axioms OCF.E0.QL_eq
#print axioms OCF.E0.fista_word
#print axioms OCF.E0.fista_beta
#print axioms OCF.E0.su_word
#print axioms OCF.E0.su_beta
#print axioms OCF.E0.hb_inverses
#print axioms OCF.E0.hb_word
#print axioms OCF.E0.row1_ista
#print axioms OCF.E0.row2_newton
#print axioms OCF.E0.Mt_inv
#print axioms OCF.E0.row5_nesterov_ode
#print axioms OCF.E0.row6_langevin
#print axioms OCF.E0.row7_ula
#print axioms OCF.E0.row8_myula
#print axioms OCF.E0.row9_sla
#print axioms OCF.E0.nearest_unique
#print axioms OCF.E0.row10_plmc
#print axioms OCF.E0.damp_K
#print axioms OCF.E0.row12_babo
#print axioms OCF.E0.row12_refresh
#print axioms OCF.E0.row12_metric_inv
#print axioms OCF.E0.row11_leapfrog
#print axioms OCF.E0.hasGradient_Delta
#print axioms OCF.E0.row13_ddd

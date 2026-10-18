/-
H2 (Inexact proximal oracles with declared accuracy) — the novel results of the unit:
Lemma H2.2 (comparison with the exact proximal point, (a)–(e)), Lemma H2.3 (one inexact
step, f nonconvex), Theorem H2.4 clauses (E0)–(E5) in standing-data form, the sharpness
instances of Lemma H2.2(d), (E1), (E4)(b), (E5)(c) and Proposition H2.7(b),(c), and
Proposition H2.6 (returned-point certificate from the next gradient, with its sharpness).

Source of truth: project_plan/done/proof_audits/H2_inexact_oracles/01_derivation.md (stage-1 dossier,
2026-10-10; Definition H2.0, Lemmas H2.2, H2.3, Theorem H2.4, Proposition H2.6,
Proposition H2.7(b),(c)); landing draft 04_landing_draft.tex (Lemma h2-lem:comparison,
h2-lem:one-step, Theorem h2-thm:inexact-soundness (I0)–(I5) = dossier (E0)–(E5),
Proposition h2-prop:next-gradient).
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised: b5b9f19c054666be.

ENCODING OF THE EXTENDED-VALUED g (g ∈ Γ₀(ℝ^d)). g is the pair (D, g): D = dom g and
g : X → ℝ its values on D; the extended function is g on D and +∞ off D. This is exact:
every proper g : ℝ^d → (−∞, +∞] is such a pair and conversely. Under it:
* ∂_ε g(z) ∋ v — `EpsSubgrad D g ε z v`: z ∈ D and g(w) ≥ g(z) + ⟨v, w − z⟩ − ε for
  every w ∈ D (for w ∉ D the inequality is trivially true, g(w) = +∞). ∂_0 g = ∂g.
* z ∈ prox^ε_{αg}(y) — `ProxEps D g α ε y z` (Definition H2.0(b)).
* C(g, σ) (g − (σ/2)‖·‖² convex) — `ModCD D g σ` = `ConvexOn ℝ D (g − (σ/2)‖·‖²)`
  (convexity of an extended function = convex domain + convex on it).
* Lower semicontinuity of g — `LscExt D g`: every sublevel set {x ∈ D : g x ≤ c} is closed.
* E = f + g — `f w + g w` on D; argmin E ∋ x* — `xs ∈ D ∧ ∀ w ∈ D, E xs ≤ E w`;
  (O2) inf E > −∞ — a lower bound `Elow ≤ E` on D (`E2a_summed_inf`: Elow = inf E).
* The exact proximal map prox_{αg} — a function `P` with `∀ y, ProxEps D g α 0 y (P y)`
  (exact ε = 0 inclusion (P); unique by Lemma H2.2(c) `comparison_c`); T_α x =
  P(x − α∇f(x)), R_α(x) = (x − T_α x)/α.

DEFINITIONAL MAP (other symbols):
* ℝ^d, d ≥ 1 — any real Hilbert space X; `[Nontrivial X]` where d ≥ 1 is used (σ_f ≤ β);
  `[ProperSpace X]` (finite dimension) for (E3)(d) only.
* f ∈ C¹ with β-Lipschitz ∇f — `Differentiable ℝ f`, G3's `LipGrad f β`; C(f, σ) — G3's
  `ModC f σ`; α = 1/β — hypothesis `hαβ : α * β = 1` with `hα : 0 < α`.
* y = x − α∇f(x) — G3's `step f α x`; inexact run with accuracies (ε_k) (Def. H2.0(c),(d))
  — `InexactRun f D g α x ε` (ε_k ≥ 0, x_{k+1} ∈ prox^{ε_k}_{αg}(y_k)); r_k — `rres α x k`;
  k₀ — `k0 D x`.
* q_A, q_B — `qA β σf`, `qB β σf σg`; regimes A / B of (E4) — `Regime β σf σg q`;
  s_k of (E4)(c) — `sk q θ k`; Φ_y — `Phi g α y`.
* f = (σ/2)‖·‖² — `sqf σ`; the half-space [0, ∞) × ℝ^{d−1} = {w : ⟨e₁, w⟩ ≥ 0} — `halfSp e`
  for a unit vector e (e = e₁ is the dossier's case).

COVERAGE (target → Lean name):
* Lemma H2.2: (a) `comparison_a`; (b) `comparison_b` (‖z − p‖² ≤ αε, ‖z − p‖ ≤ √(αε),
  Φ_y(z) − Φ_y(p) ≤ αε − ½‖z − p‖² ≤ αε, Φ_y(p) = min Φ_y); (c) `comparison_c`;
  (d) `comparison_d`; (e) `comparison_e`.
* Lemma H2.3: `one_step`.
* (E0) `exact_case`. (E1) `E1_descent` (k ≥ k₀), `descent_of_mem` (x_k ∈ dom g); equality
  `halfspace_sharp`.
* (E2)(a) `E2a_summed`, `E2a_summed_inf`; (b) `E2b_limits` (r_k → 0, k_η exists, count);
  (c) `E2c_stationary`; (d) `E2d_u`, `E2d_convex`.
* (E3)(a) `E3a`; (b) `E3b_sum`, `E3b_min`; (c) `E3c_last`; (d) `E3d_converge`
  (via `quasi_fejer`, `min_of_stationary`, `E2b_limits`, `E2c_stationary`).
* (E4): contraction of the exact step `T_contract`, `regime_contract` (q-Lipschitz towards
  x*, 0 ≤ q < 1; via `prox_lip`, `fixed_point`, G3's `step_contract`); (a) `E4a`;
  (b) `E4b`, `E4b_regimeA_const`; (c) `E4c` (with `sum_eq_sk`); (d) `E4d_tendsto`,
  `E4d_limsup_of_le`, `E4d_limsup`; floor attained `halfspace_sharp`.
* (E5)(a) `E5a_resid` (‖R_α(x_k)‖ ≤ ‖r_k‖ + √(βε_k)), `E5a_regimeA` (κ = 1/σ_f),
  `E5a_regimeB` (κ_g), `E5a_regimeC` (κ_N = α + 2/μ); (b) `E5b_returned`;
  (c)(i) `quadratic_sharp`, (c)(ii) `halfspace_sharp`.
* Proposition H2.6: `prop_H2_6`, run form `prop_H2_6_run`, sharpness `prop_H2_6_sharp`.
* Proposition H2.7(b),(c): `halfspace_sharp` (last two conjuncts).

STRENGTHENINGS (none weakens a dossier statement): Lemma H2.3 and (E1)–(E2) need no
convexity of g; (E2)(a) holds for every m (also m = 0) and every lower bound E_low;
(E3)(a)–(c) need no convexity or lower semicontinuity of g; (E5)(b) is proved under
σ_g ≥ 0 and σ_f + σ_g > 0 without σ_f ≥ 0; (E5)(a) regime C needs no convexity of g
beyond C(f + g, μ); Proposition H2.6 needs neither LipGrad nor σ_g ≥ 0 nor that x* be a
minimiser (only stationarity); `fermat_strong` holds for every σ.

CLASSICAL INPUTS TAKEN AS HYPOTHESES (as in H1): existence of the exact proximal point
prox_{αg}(y) for g ∈ Γ₀ (B&C Prop. 12.15 / Def. 12.23) — the map `P` with the exact
inclusion; existence of a minimiser x* of E in (E3)–(E5) (the dossier's own hypothesis
(O3) / "x* the minimiser"). Fermat's rule, the strongly convex minorant, prox
contractivity, the fixed-point property and quasi-Fejér convergence are PROVED here from
the predicates, not assumed.

NOT FORMALISED: Lemma H2.1 (Fenchel conjugates; not a Lean target of this pass);
Corollary H2.5 (assembly with the declared numbers of Theorem G3.1; prose);
Proposition H2.7(a),(d); Remark H2.9; the frame-slot remark.

Status tier: FORMALISED (statement + proof, no sorry) for Lemma H2.2(a)–(e), Lemma H2.3,
Theorem H2.4 (E0)–(E5) including the sharpness instances, Proposition H2.6 (with its run
form and sharpness), Proposition H2.7(b),(c). Axioms: only propext, Classical.choice,
Quot.sound (see #print axioms at the end).
-/
import Mathlib
import OcfVerification.A1DescentLemma
import OcfVerification.G3SoundnessQuadratic
import OcfVerification.H1DiscretePick

namespace OCF.H2

open Set Filter Topology Finset OCF.A1 OCF.G3

set_option linter.unusedSectionVars false

section Generic

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-! ## Definitions (Definition H2.0) -/

/-- The ε-subgradient inequality, with g extended-valued encoded as the pair (D, g):
dom g = D and g = +∞ off D. `EpsSubgrad D g ε z v` is v ∈ ∂_ε g(z):
z ∈ dom g and g(w) ≥ g(z) + ⟨v, w − z⟩ − ε for every w ∈ dom g (for w ∉ dom g the
inequality holds trivially, g(w) = +∞). -/
def EpsSubgrad (D : Set X) (g : X → ℝ) (ε : ℝ) (z v : X) : Prop :=
  z ∈ D ∧ ∀ w ∈ D, g z + inner ℝ v (w - z) - ε ≤ g w

/-- z ∈ prox^ε_{αg}(y): (y − z)/α ∈ ∂_ε g(z). -/
def ProxEps (D : Set X) (g : X → ℝ) (α ε : ℝ) (y z : X) : Prop :=
  EpsSubgrad D g ε z (α⁻¹ • (y - z))

/-- An inexact run (x_k) with reported accuracies (ε_k): ε_k ≥ 0 and
x_{k+1} ∈ prox^{ε_k}_{αg}(x_k − α∇f(x_k)) for every k. -/
def InexactRun (f : X → ℝ) (D : Set X) (g : X → ℝ) (α : ℝ) (x : ℕ → X) (ε : ℕ → ℝ) : Prop :=
  ∀ k, 0 ≤ ε k ∧ ProxEps D g α (ε k) (step f α (x k)) (x (k + 1))

/-- The realised residual r_k = (x_k − x_{k+1})/α. -/
noncomputable def rres (α : ℝ) (x : ℕ → X) (k : ℕ) : X := α⁻¹ • (x k - x (k + 1))

open Classical in
/-- k₀ := 0 if x₀ ∈ dom g, 1 otherwise. -/
noncomputable def k0 (D : Set X) (x : ℕ → X) : ℕ := if x 0 ∈ D then 0 else 1

/-- C(g, σ) for an extended-valued g = (D, g): g − (σ/2)‖·‖² convex, i.e. D convex and
g − (σ/2)‖·‖² convex on D. -/
def ModCD (D : Set X) (g : X → ℝ) (σ : ℝ) : Prop :=
  ConvexOn ℝ D (fun x => g x - σ / 2 * ‖x‖ ^ 2)

/-- Lower semicontinuity of the extended-valued g = (D, g): every sublevel set
{x ∈ D : g x ≤ c} is closed. -/
def LscExt (D : Set X) (g : X → ℝ) : Prop :=
  ∀ c : ℝ, IsClosed {x | x ∈ D ∧ g x ≤ c}

/-! ## Basic algebra of a step -/

/-- v = (y − z)/α = r − ∇f(x) with y = x − α∇f(x), r = (x − z)/α. -/
lemma prox_vec_eq (f : X → ℝ) {α : ℝ} (hα : α ≠ 0) (x z : X) :
    α⁻¹ • (step f α x - z) = α⁻¹ • (x - z) - gradient f x := by
  simp only [step]
  rw [show x - α • gradient f x - z = (x - z) - α • gradient f x by abel, smul_sub, smul_smul,
    inv_mul_cancel₀ hα, one_smul]

lemma eq_sub_smul_res {α : ℝ} (hα : α ≠ 0) (x z : X) : z = x - α • (α⁻¹ • (x - z)) := by
  rw [smul_smul, mul_inv_cancel₀ hα, one_smul]; abel

lemma EpsSubgrad.mono {D : Set X} {g : X → ℝ} {ε ε' : ℝ} {z v : X} (h : EpsSubgrad D g ε z v)
    (hε : ε ≤ ε') : EpsSubgrad D g ε' z v :=
  ⟨h.1, fun w hw => by have := h.2 w hw; linarith⟩

/-! ## Lemma H2.3 (one inexact step) -/

/-- **Lemma H2.3.** f differentiable with β-Lipschitz gradient (f need not be convex),
α = 1/β, z ∈ prox^ε_{αg}(x − α∇f(x)), r = (x − z)/α. For every w ∈ dom g,
E(z) ≤ f(x) + ⟨∇f(x), w − x⟩ + g(w) + ⟨r, x − w⟩ − (α/2)‖r‖² + ε.
(For w ∉ dom g the right side is +∞.) -/
theorem one_step {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β ε : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x z : X} (hz : ProxEps D g α ε (step f α x) z) {w : X} (hw : w ∈ D) :
    f z + g z ≤ f x + inner ℝ (gradient f x) (w - x) + g w
      + inner ℝ (α⁻¹ • (x - z)) (x - w) - α / 2 * ‖α⁻¹ • (x - z)‖ ^ 2 + ε := by
  have hsub := hz.2 w hw
  rw [prox_vec_eq f hα.ne'] at hsub
  set r := α⁻¹ • (x - z) with hr
  have hzr : z = x - α • r := eq_sub_smul_res hα.ne' x z
  have hup := upper_bound hf hL x z
  clear_value r
  subst hzr
  have e1 : x - α • r - x = -(α • r) := by abel
  have e2 : w - (x - α • r) = (w - x) + α • r := by abel
  have e3 : x - w = -(w - x) := by abel
  rw [e1, norm_neg, norm_smul, Real.norm_of_nonneg hα.le, inner_neg_right,
    real_inner_smul_right] at hup
  rw [e2, inner_add_right, inner_sub_left, inner_sub_left, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq] at hsub
  rw [e3, inner_neg_right]
  have hb : β / 2 * (α * ‖r‖) ^ 2 = α / 2 * ‖r‖ ^ 2 := by
    have : β / 2 * (α * ‖r‖) ^ 2 = (α * β) * α / 2 * ‖r‖ ^ 2 := by ring
    rw [this, hαβ]; ring
  have hc : inner ℝ r (gradient f x) = inner ℝ (gradient f x) r := real_inner_comm _ _
  linarith


/-! ## Lemma H2.2 (comparison with the exact proximal point) -/

/-- The prox objective Φ_y(w) = αg(w) + ½‖w − y‖² (on dom g). -/
noncomputable def Phi (g : X → ℝ) (α : ℝ) (y w : X) : ℝ := α * g w + 1 / 2 * ‖w - y‖ ^ 2

/-- **Lemma H2.2(a).** z ∈ prox^ε_{αg}(y) ⇒ Φ_y(w) ≥ Φ_y(z) + ½‖w − z‖² − αε, w ∈ dom g. -/
theorem comparison_a {D : Set X} {g : X → ℝ} {α ε : ℝ} (hα : 0 < α) {y z : X}
    (hz : ProxEps D g α ε y z) {w : X} (hw : w ∈ D) :
    Phi g α y z + 1 / 2 * ‖w - z‖ ^ 2 - α * ε ≤ Phi g α y w := by
  have h := hz.2 w hw
  rw [real_inner_smul_left] at h
  have h2 := mul_le_mul_of_nonneg_left h hα.le
  have e : α * (g z + α⁻¹ * inner ℝ (y - z) (w - z) - ε)
      = α * g z + inner ℝ (y - z) (w - z) - α * ε := by
    field_simp
  rw [e] at h2
  have hn : ‖w - y‖ ^ 2 = ‖w - z‖ ^ 2 - 2 * inner ℝ (w - z) (y - z) + ‖y - z‖ ^ 2 := by
    rw [show w - y = (w - z) - (y - z) by abel, norm_sub_sq_real]
  have hn2 : ‖z - y‖ = ‖y - z‖ := norm_sub_rev _ _
  unfold Phi
  rw [hn, hn2]
  have := real_inner_comm (w - z) (y - z)
  linarith

/-- **Lemma H2.2(b).** With p ∈ prox^0_{αg}(y) (the exact proximal point): ‖z − p‖² ≤ αε,
‖z − p‖ ≤ √(αε), Φ_y(z) − Φ_y(p) ≤ αε − ½‖z − p‖² ≤ αε, and Φ_y(p) = min Φ_y. -/
theorem comparison_b {D : Set X} {g : X → ℝ} {α ε : ℝ} (hα : 0 < α) {y z p : X}
    (hz : ProxEps D g α ε y z) (hp : ProxEps D g α 0 y p) :
    ‖z - p‖ ^ 2 ≤ α * ε ∧ ‖z - p‖ ≤ √(α * ε) ∧
    Phi g α y z - Phi g α y p ≤ α * ε - 1 / 2 * ‖z - p‖ ^ 2 ∧
    α * ε - 1 / 2 * ‖z - p‖ ^ 2 ≤ α * ε ∧ (∀ w ∈ D, Phi g α y p ≤ Phi g α y w) := by
  have b1 := comparison_a hα hz hp.1
  have b2 := comparison_a hα hp hz.1
  rw [norm_sub_rev p z] at b1
  have hsq : ‖z - p‖ ^ 2 ≤ α * ε := by linarith
  refine ⟨hsq, Real.le_sqrt_of_sq_le hsq, by linarith, by nlinarith [sq_nonneg ‖z - p‖], ?_⟩
  intro w hw
  have := comparison_a hα hp hw
  nlinarith [sq_nonneg ‖w - p‖]

/-- **Lemma H2.2(c).** prox^0_{αg}(y) has at most one point: it is {p} for the exact
proximal point p. -/
theorem comparison_c {D : Set X} {g : X → ℝ} {α : ℝ} (hα : 0 < α) {y z p : X}
    (hz : ProxEps D g α 0 y z) (hp : ProxEps D g α 0 y p) : z = p := by
  have h := (comparison_b hα hz hp).1
  rw [mul_zero] at h
  have : ‖z - p‖ = 0 := by nlinarith [norm_nonneg (z - p)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Lemma H2.2(e).** At α = 1/β, for x, its exact proximal output p and an inexact output
z at accuracy ε (both at y = x − α∇f(x)): ‖R_α(x) − r‖ ≤ √(βε), where R_α(x) = (x − p)/α and
r = (x − z)/α. -/
theorem comparison_e {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β ε : ℝ} (hα : 0 < α)
    (hαβ : α * β = 1) {x z p : X}
    (hz : ProxEps D g α ε (step f α x) z) (hp : ProxEps D g α 0 (step f α x) p) :
    ‖α⁻¹ • (x - p) - α⁻¹ • (x - z)‖ ≤ √(β * ε) := by
  have h := (comparison_b hα hz hp).2.1
  have e : α⁻¹ • (x - p) - α⁻¹ • (x - z) = α⁻¹ • (z - p) := by
    rw [← smul_sub]; congr 1; abel
  have hβ : β = α⁻¹ := by field_simp; linarith
  rw [e, norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le, hβ]
  have : √(α⁻¹ * ε) = α⁻¹ * √(α * ε) := by
    rw [show α⁻¹ * ε = α⁻¹ ^ 2 * (α * ε) by field_simp, Real.sqrt_mul (by positivity) (α * ε),
      Real.sqrt_sq (by positivity)]
  rw [this]
  exact mul_le_mul_of_nonneg_left h (inv_pos.2 hα).le

/-! ## Theorem H2.4 (E0)–(E2) -/

lemma InexactRun.mem {f : X → ℝ} {D : Set X} {g : X → ℝ} {α : ℝ} {x : ℕ → X} {ε : ℕ → ℝ}
    (hr : InexactRun f D g α x ε) (k : ℕ) : x (k + 1) ∈ D := (hr k).2.1

lemma InexactRun.mem_of_k0_le {f : X → ℝ} {D : Set X} {g : X → ℝ} {α : ℝ} {x : ℕ → X}
    {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {k : ℕ} (hk : k0 D x ≤ k) : x k ∈ D := by
  rcases k with _ | k
  · unfold k0 at hk
    by_contra h
    simp [h] at hk
  · exact hr.mem k

lemma InexactRun.mem_k0 {f : X → ℝ} {D : Set X} {g : X → ℝ} {α : ℝ} {x : ℕ → X}
    {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) : x (k0 D x) ∈ D := hr.mem_of_k0_le le_rfl

/-- **(E0) Exact case.** If every reported accuracy is 0, the run is the forward–backward
iteration x_{k+1} = P(x_k − α∇f(x_k)) = T_α x_k, P the exact proximal map. -/
theorem exact_case {f : X → ℝ} {D : Set X} {g : X → ℝ} {α : ℝ} (hα : 0 < α) {x : ℕ → X}
    {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (h0 : ∀ k, ε k = 0) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) (k : ℕ) : x (k + 1) = P (step f α (x k)) := by
  have h := (hr k).2
  rw [h0 k] at h
  exact comparison_c hα h (hP _)

/-- **(E1) Descent up to ε_k** (f need not be convex): for x_k ∈ dom g,
E(x_{k+1}) ≤ E(x_k) − (α/2)‖r_k‖² + ε_k. -/
theorem descent_of_mem {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {k : ℕ} (hk : x k ∈ D) :
    f (x (k + 1)) + g (x (k + 1)) ≤ f (x k) + g (x k) - α / 2 * ‖rres α x k‖ ^ 2 + ε k := by
  have h := one_step hf hL hα hαβ (hr k).2 hk
  simp only [sub_self, inner_zero_right, add_zero] at h
  unfold rres; linarith

/-- **(E1)** in the dossier's form: for every k ≥ k₀. -/
theorem E1_descent {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {k : ℕ} (hk : k0 D x ≤ k) :
    f (x (k + 1)) + g (x (k + 1)) ≤ f (x k) + g (x k) - α / 2 * ‖rres α x k‖ ^ 2 + ε k :=
  descent_of_mem hf hL hα hαβ hr (hr.mem_of_k0_le hk)

/-- Telescoped (E1) from any start j with x_j ∈ dom g. -/
lemma telescoped {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {j : ℕ} (hj : x j ∈ D) (m : ℕ) :
    α / 2 * ∑ k ∈ range m, ‖rres α x (j + k)‖ ^ 2
      ≤ f (x j) + g (x j) - (f (x (j + m)) + g (x (j + m))) + ∑ k ∈ range m, ε (j + k) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm : x (j + m) ∈ D := by
      rcases m with _ | m
      · simpa using hj
      · exact hr.mem (j + m)
    have := descent_of_mem hf hL hα hαβ hr hm
    rw [sum_range_succ, sum_range_succ, mul_add, show j + (m + 1) = j + m + 1 by ring]
    linarith

/-- **(E2)(a) Summed residual.** Under (O2), with any lower bound E_low ≤ E on dom g
(e.g. E_low = inf E), for every m: Σ_{k₀≤k<k₀+m} ‖r_k‖² ≤ 2β(E(x_{k₀}) − E_low +
Σ_{k₀≤k<k₀+m} ε_k). -/
theorem E2a_summed {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {Elow : ℝ}
    (hlow : ∀ w ∈ D, Elow ≤ f w + g w) (m : ℕ) :
    ∑ k ∈ Ico (k0 D x) (k0 D x + m), ‖rres α x k‖ ^ 2
      ≤ 2 * β * (f (x (k0 D x)) + g (x (k0 D x)) - Elow
        + ∑ k ∈ Ico (k0 D x) (k0 D x + m), ε k) := by
  rw [sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  have h := telescoped hf hL hα hαβ hr hr.mem_k0 m
  have hl := hlow _ (hr.mem_of_k0_le (Nat.le_add_right (k0 D x) m))
  have hβ : 0 < β := by nlinarith
  have e : 2 * β * (α / 2) = 1 := by linarith [hαβ]
  have h2 := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 2 * β)
  rw [← mul_assoc, e, one_mul] at h2
  nlinarith

lemma run_next_eq {α : ℝ} (hα : α ≠ 0) (x : ℕ → X) (k : ℕ) :
    x (k + 1) = x k - α • rres α x k := eq_sub_smul_res hα _ _

/-- **(E2)(a)** with E_low = inf E literally (the infimum over dom g, finite under (O2)). -/
theorem E2a_summed_inf {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε)
    (hO2 : BddBelow (range fun w : D => f w + g w)) (m : ℕ) :
    ∑ k ∈ Ico (k0 D x) (k0 D x + m), ‖rres α x k‖ ^ 2
      ≤ 2 * β * (f (x (k0 D x)) + g (x (k0 D x)) - (⨅ w : D, f w + g w)
        + ∑ k ∈ Ico (k0 D x) (k0 D x + m), ε k) :=
  E2a_summed hf hL hα hαβ hr (fun w hw => ciInf_le hO2 (⟨w, hw⟩ : D)) m

/-- **(E2)(b).** Under (O2) (E_low ≤ E on dom g) and S = Σ_{k≥k₀} ε_k < ∞ (`Summable ε`):
r_k → 0; for every η > 0 the index k_η = min{k ≥ k₀ : ‖r_k‖ ≤ η} exists; and for a declared
S̄ ≥ S, k_η ≤ k₀ + ⌊2β(E(x_{k₀}) − E_low + S̄)/η²⌋. -/
theorem E2b_limits {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {Elow : ℝ}
    (hlow : ∀ w ∈ D, Elow ≤ f w + g w) (hS : Summable ε) :
    Tendsto (rres α x) atTop (𝓝 0) ∧
    (∀ η > 0, ∃ k, k0 D x ≤ k ∧ ‖rres α x k‖ ≤ η) ∧
    (∀ η > 0, ∀ Sbar : ℝ, ∑' k, ε (k + k0 D x) ≤ Sbar →
      sInf {k | k0 D x ≤ k ∧ ‖rres α x k‖ ≤ η}
        ≤ k0 D x + ⌊2 * β * (f (x (k0 D x)) + g (x (k0 D x)) - Elow + Sbar) / η ^ 2⌋₊) := by
  set j := k0 D x with hj
  have hβ : 0 < β := by nlinarith
  have hS' : Summable (fun k => ε (k + j)) := (summable_nat_add_iff j).2 hS
  have hpart : ∀ m, ∑ k ∈ range m, ε (j + k) ≤ ∑' k, ε (k + j) := by
    intro m
    have := hS'.sum_le_tsum (range m) (fun i _ => (hr (i + j)).1)
    simpa [add_comm] using this
  have hbound : ∀ m Sb, ∑' k, ε (k + j) ≤ Sb →
      ∑ k ∈ range m, ‖rres α x (k + j)‖ ^ 2 ≤ 2 * β * (f (x j) + g (x j) - Elow + Sb) := by
    intro m Sb hSb
    have h := E2a_summed hf hL hα hαβ hr hlow m
    rw [← hj, sum_Ico_eq_sum_range, sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] at h
    have h2 := (hpart m).trans hSb
    simp only [add_comm j] at h h2 ⊢
    nlinarith
  have hsum : Summable (fun k => ‖rres α x (k + j)‖ ^ 2) :=
    summable_of_sum_range_le (fun _ => sq_nonneg _) (fun m => hbound m _ le_rfl)
  have hsq : Tendsto (fun k => ‖rres α x k‖ ^ 2) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat j).1 hsum.tendsto_atTop_zero
  have hnorm : Tendsto (fun k => ‖rres α x k‖) atTop (𝓝 0) := by
    have := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this
  have hlim : Tendsto (rres α x) atTop (𝓝 0) := tendsto_zero_iff_norm_tendsto_zero.2 hnorm
  refine ⟨hlim, ?_, ?_⟩
  · intro η hη
    have h1 := (tendsto_order.1 hnorm).2 η hη
    obtain ⟨k, hk1, hk2⟩ := ((eventually_ge_atTop j).and h1).exists
    exact ⟨k, hk1, hk2.le⟩
  · intro η hη Sbar hSbar
    set M := ⌊2 * β * (f (x j) + g (x j) - Elow + Sbar) / η ^ 2⌋₊ with hM
    have hex : ∃ k, j ≤ k ∧ k ≤ j + M ∧ ‖rres α x k‖ ≤ η := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hlt : ∑ k ∈ range (M + 1), η ^ 2 < ∑ k ∈ range (M + 1), ‖rres α x (k + j)‖ ^ 2 := by
        apply sum_lt_sum_of_nonempty nonempty_range_add_one
        intro i hi
        have hi' := mem_range.1 hi
        have := hcon (i + j) (by omega) (by omega)
        nlinarith
      have hb := hbound (M + 1) Sbar hSbar
      rw [sum_const, card_range, nsmul_eq_mul] at hlt
      have hfl := Nat.lt_floor_add_one (2 * β * (f (x j) + g (x j) - Elow + Sbar) / η ^ 2)
      rw [← hM, div_lt_iff₀ (by positivity)] at hfl
      push_cast at hlt hfl
      linarith
    obtain ⟨k, hk1, hk2, hk3⟩ := hex
    exact (Nat.sInf_le (show k ∈ {k | j ≤ k ∧ ‖rres α x k‖ ≤ η} from ⟨hk1, hk3⟩)).trans hk2

/-- ∇f is continuous along convergent sequences when it is β-Lipschitz. -/
lemma tendsto_gradient {f : X → ℝ} {β : ℝ} (hL : LipGrad f β) {ι : Type*} {l : Filter ι}
    {u : ι → X} {a : X} (hu : Tendsto u l (𝓝 a)) :
    Tendsto (fun i => gradient f (u i)) l (𝓝 (gradient f a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero] at hu ⊢
  have := hu.const_mul β
  rw [mul_zero] at this
  exact squeeze_zero (fun _ => norm_nonneg _) (fun i => hL _ _) this

/-- **(E2)(c).** If ε_k → 0 and r_k → 0, every limit point x̄ = lim x_{φ(i)} of an inexact
run is stationary: −∇f(x̄) ∈ ∂g(x̄) (g lower semicontinuous). -/
theorem E2c_stationary {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hL : LipGrad f β) (hα : 0 < α) (hlsc : LscExt D g)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε)
    (hε0 : Tendsto ε atTop (𝓝 0)) (hr0 : Tendsto (rres α x) atTop (𝓝 0))
    {φ : ℕ → ℕ} (hφ : StrictMono φ) {xb : X} (hx : Tendsto (fun i => x (φ i)) atTop (𝓝 xb)) :
    EpsSubgrad D g 0 xb (-gradient f xb) := by
  have hφt := hφ.tendsto_atTop
  have hrφ : Tendsto (fun i => rres α x (φ i)) atTop (𝓝 0) := hr0.comp hφt
  have hεφ : Tendsto (fun i => ε (φ i)) atTop (𝓝 0) := hε0.comp hφt
  have hx1 : Tendsto (fun i => x (φ i + 1)) atTop (𝓝 xb) := by
    have : Tendsto (fun i => x (φ i) - α • rres α x (φ i)) atTop (𝓝 (xb - α • (0 : X))) :=
      hx.sub (hrφ.const_smul α)
    rw [smul_zero, sub_zero] at this
    exact this.congr (fun i => (run_next_eq hα.ne' x (φ i)).symm)
  have hv : Tendsto (fun i => α⁻¹ • (step f α (x (φ i)) - x (φ i + 1))) atTop
      (𝓝 (-gradient f xb)) := by
    have : Tendsto (fun i => rres α x (φ i) - gradient f (x (φ i))) atTop
        (𝓝 (0 - gradient f xb)) := hrφ.sub (tendsto_gradient hL hx)
    rw [zero_sub] at this
    refine this.congr (fun i => ?_)
    rw [prox_vec_eq f hα.ne']; rfl
  -- the key closedness step
  have key : ∀ w ∈ D, ∀ δ > 0, xb ∈ D ∧ g xb ≤ g w - inner ℝ (-gradient f xb) (w - xb) + δ := by
    intro w hw δ hδ
    have hR : Tendsto (fun i => g w - inner ℝ (α⁻¹ • (step f α (x (φ i)) - x (φ i + 1)))
        (w - x (φ i + 1)) + ε (φ i)) atTop
        (𝓝 (g w - inner ℝ (-gradient f xb) (w - xb) + 0)) :=
      (tendsto_const_nhds.sub (hv.inner (tendsto_const_nhds.sub hx1))).add hεφ
    rw [add_zero] at hR
    have hev := (tendsto_order.1 hR).2 _ (lt_add_of_pos_right _ hδ)
    have hmem : ∀ᶠ i in atTop, x (φ i + 1) ∈
        {y | y ∈ D ∧ g y ≤ g w - inner ℝ (-gradient f xb) (w - xb) + δ} := by
      filter_upwards [hev] with i hi
      have h := (hr (φ i)).2
      refine ⟨h.1, ?_⟩
      have := h.2 w hw
      linarith
    exact (hlsc _).mem_of_tendsto hx1 hmem
  have hxD : xb ∈ D := (key _ (hr.mem 0) 1 one_pos).1
  refine ⟨hxD, fun w hw => ?_⟩
  have : g xb ≤ g w - inner ℝ (-gradient f xb) (w - xb) :=
    le_of_forall_pos_le_add fun δ hδ => (key w hw δ hδ).2
  linarith

/-- **(E2)(d).** For every k, u_k := r_k + ∇f(x_{k+1}) − ∇f(x_k) satisfies
u_k − ∇f(x_{k+1}) ∈ ∂_{ε_k} g(x_{k+1}) and ‖u_k‖ ≤ 2‖r_k‖. -/
theorem E2d_u {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    EpsSubgrad D g (ε k) (x (k + 1))
      ((rres α x k + gradient f (x (k + 1)) - gradient f (x k)) - gradient f (x (k + 1))) ∧
    ‖rres α x k + gradient f (x (k + 1)) - gradient f (x k)‖ ≤ 2 * ‖rres α x k‖ := by
  constructor
  · have h := (hr k).2
    unfold ProxEps at h
    rw [prox_vec_eq f hα.ne'] at h
    convert h using 1
    unfold rres; abel
  · have h1 := hL (x (k + 1)) (x k)
    have hd : x (k + 1) - x k = -(α • rres α x k) := by
      rw [run_next_eq hα.ne' x k]; abel
    rw [hd, norm_neg, norm_smul, Real.norm_of_nonneg hα.le] at h1
    have e : rres α x k + gradient f (x (k + 1)) - gradient f (x k)
        = rres α x k + (gradient f (x (k + 1)) - gradient f (x k)) := by abel
    rw [e]
    calc _ ≤ ‖rres α x k‖ + ‖gradient f (x (k + 1)) - gradient f (x k)‖ := norm_add_le _ _
      _ ≤ ‖rres α x k‖ + β * (α * ‖rres α x k‖) := by linarith
      _ = 2 * ‖rres α x k‖ := by rw [← mul_assoc, mul_comm β α, hαβ]; ring

/-- **(E2)(d), last sentence.** If f is convex (C(f, 0)), ∇f(z) + ∂_ε g(z) ⊆ ∂_ε E(z),
E = f + g on dom g. -/
theorem E2d_convex {f : X → ℝ} {D : Set X} {g : X → ℝ} (hf : Differentiable ℝ f)
    (hc : ModC f 0) {ε : ℝ} {z v : X} (hv : EpsSubgrad D g ε z v) :
    EpsSubgrad D (fun w => f w + g w) ε z (gradient f z + v) := by
  refine ⟨hv.1, fun w hw => ?_⟩
  have h1 := OCF.H1.strongSubgrad_of_modC hf hc z w
  have h2 := hv.2 w hw
  simp only [zero_div, zero_mul, add_zero] at h1
  rw [inner_add_left]
  linarith


/-! ## Theorem H2.4 (E3): the convex case -/

/-- The convex one-step inequality behind (E3)(a), at a single step x ↦ z. -/
lemma convex_one_step {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β ε : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hc : ModC f 0) (hα : 0 < α)
    (hαβ : α * β = 1) {x z xs : X} (hz : ProxEps D g α ε (step f α x) z) (hxs : xs ∈ D) :
    f z + g z - (f xs + g xs) ≤ β / 2 * (‖x - xs‖ ^ 2 - ‖z - xs‖ ^ 2) + ε := by
  have h := one_step hf hL hα hαβ hz hxs
  have hcv := OCF.H1.strongSubgrad_of_modC hf hc x xs
  simp only [zero_div, zero_mul, add_zero] at hcv
  set r := α⁻¹ • (x - z) with hr
  have hzr : z = x - α • r := eq_sub_smul_res hα.ne' x z
  clear_value r
  subst hzr
  have hn : ‖x - α • r - xs‖ ^ 2 = ‖x - xs‖ ^ 2 - 2 * α * inner ℝ (x - xs) r + α ^ 2 * ‖r‖ ^ 2 := by
    rw [show x - α • r - xs = (x - xs) - α • r by abel, norm_sub_sq_real, real_inner_smul_right,
      norm_smul, Real.norm_of_nonneg hα.le]
    ring
  rw [hn]
  have hi : inner ℝ r (x - xs) = inner ℝ (x - xs) r := real_inner_comm _ _
  have e1 : β / 2 * (2 * α * inner ℝ (x - xs) r) = inner ℝ (x - xs) r := by
    rw [show β / 2 * (2 * α * inner ℝ (x - xs) r) = (α * β) * inner ℝ (x - xs) r by ring, hαβ,
      one_mul]
  have e2 : β / 2 * (α ^ 2 * ‖r‖ ^ 2) = α / 2 * ‖r‖ ^ 2 := by
    rw [show β / 2 * (α ^ 2 * ‖r‖ ^ 2) = (α * β) * α / 2 * ‖r‖ ^ 2 by ring, hαβ]; ring
  have e3 : β / 2 * (‖x - xs‖ ^ 2 - (‖x - xs‖ ^ 2 - 2 * α * inner ℝ (x - xs) r + α ^ 2 * ‖r‖ ^ 2))
      = β / 2 * (2 * α * inner ℝ (x - xs) r) - β / 2 * (α ^ 2 * ‖r‖ ^ 2) := by ring
  rw [e3, e1, e2]
  linarith

/-- **(E3)(a).** f convex, x* ∈ argmin E (on dom g). For every k ≥ 0:
E(x_{k+1}) − E* ≤ (β/2)(‖x_k − x*‖² − ‖x_{k+1} − x*‖²) + ε_k, and
‖x_{k+1} − x*‖² ≤ ‖x_k − x*‖² + 2αε_k. (x₀ ∉ dom g allowed.) -/
theorem E3a {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hc : ModC f 0) (hα : 0 < α)
    (hαβ : α * β = 1) {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {xs : X}
    (hxs : xs ∈ D) (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (k : ℕ) :
    f (x (k + 1)) + g (x (k + 1)) - (f xs + g xs)
      ≤ β / 2 * (‖x k - xs‖ ^ 2 - ‖x (k + 1) - xs‖ ^ 2) + ε k ∧
    ‖x (k + 1) - xs‖ ^ 2 ≤ ‖x k - xs‖ ^ 2 + 2 * α * ε k := by
  have h := convex_one_step hf hL hc hα hαβ (hr k).2 hxs
  refine ⟨h, ?_⟩
  have hm := hmin _ (hr.mem k)
  have h2 : 0 ≤ β / 2 * (‖x k - xs‖ ^ 2 - ‖x (k + 1) - xs‖ ^ 2) + ε k := by linarith
  have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * α)
  have e : 2 * α * (β / 2 * (‖x k - xs‖ ^ 2 - ‖x (k + 1) - xs‖ ^ 2) + ε k)
      = (α * β) * (‖x k - xs‖ ^ 2 - ‖x (k + 1) - xs‖ ^ 2) + 2 * α * ε k := by ring
  rw [e, hαβ] at h3
  linarith

/-- **(E3)(b), sum and distance.** For every m: Σ_{k<m} (E(x_{k+1}) − E*) ≤ (β/2)‖x₀ − x*‖²
+ Σ_{k<m} ε_k (this is Σ_{k=1}^{m} (E(x_k) − E*)), and ‖x_m − x*‖² ≤ ‖x₀ − x*‖² +
2αΣ_{k<m} ε_k. -/
theorem E3b_sum {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hc : ModC f 0) (hα : 0 < α)
    (hαβ : α * β = 1) {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {xs : X}
    (hxs : xs ∈ D) (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (m : ℕ) :
    ∑ k ∈ range m, (f (x (k + 1)) + g (x (k + 1)) - (f xs + g xs))
      ≤ β / 2 * ‖x 0 - xs‖ ^ 2 + ∑ k ∈ range m, ε k ∧
    ‖x m - xs‖ ^ 2 ≤ ‖x 0 - xs‖ ^ 2 + 2 * α * ∑ k ∈ range m, ε k := by
  have hβ : 0 < β := by nlinarith
  have dist : ∀ n, ‖x n - xs‖ ^ 2 ≤ ‖x 0 - xs‖ ^ 2 + 2 * α * ∑ k ∈ range n, ε k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have := (E3a hf hL hc hα hαβ hr hxs hmin n).2
      rw [sum_range_succ, mul_add]
      linarith
  have tel : ∑ k ∈ range m, (f (x (k + 1)) + g (x (k + 1)) - (f xs + g xs))
      ≤ β / 2 * (‖x 0 - xs‖ ^ 2 - ‖x m - xs‖ ^ 2) + ∑ k ∈ range m, ε k := by
    induction m with
    | zero => simp
    | succ m ih =>
      have := (E3a hf hL hc hα hαβ hr hxs hmin m).1
      rw [sum_range_succ, sum_range_succ]
      linarith
  exact ⟨by nlinarith [sq_nonneg ‖x m - xs‖], dist m⟩

/-- **(E3)(b), best iterate.** For every m ≥ 1:
min_{1≤k≤m} E(x_k) − E* ≤ ((β/2)‖x₀ − x*‖² + Σ_{k<m} ε_k)/m. -/
theorem E3b_min {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hc : ModC f 0) (hα : 0 < α)
    (hαβ : α * β = 1) {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {xs : X}
    (hxs : xs ∈ D) (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) {m : ℕ} (hm : 1 ≤ m) :
    (Finset.Icc 1 m).inf' (Finset.nonempty_Icc.2 hm) (fun k => f (x k) + g (x k)) - (f xs + g xs)
      ≤ (β / 2 * ‖x 0 - xs‖ ^ 2 + ∑ k ∈ range m, ε k) / m := by
  set I := (Finset.Icc 1 m).inf' (Finset.nonempty_Icc.2 hm) (fun k => f (x k) + g (x k))
  have hI : ∀ k ∈ range m, I - (f xs + g xs) ≤ f (x (k + 1)) + g (x (k + 1)) - (f xs + g xs) := by
    intro k hk
    have := inf'_le (fun k => f (x k) + g (x k))
      (show k + 1 ∈ Finset.Icc 1 m by rw [Finset.mem_Icc]; have := mem_range.1 hk; omega)
    linarith
  have hs := sum_le_sum hI
  rw [sum_const, card_range, nsmul_eq_mul] at hs
  have hb := (E3b_sum hf hL hc hα hαβ hr hxs hmin m).1
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  rw [le_div_iff₀ hm']
  linarith

/-- **(E3)(c), last iterate.** For every m ≥ 1:
E(x_m) − E* ≤ ((β/2)‖x₀ − x*‖² + Σ_{k<m} (k+1)ε_k)/m. -/
theorem E3c_last {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hc : ModC f 0) (hα : 0 < α)
    (hαβ : α * β = 1) {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {xs : X}
    (hxs : xs ∈ D) (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) {m : ℕ} (hm : 1 ≤ m) :
    f (x m) + g (x m) - (f xs + g xs)
      ≤ (β / 2 * ‖x 0 - xs‖ ^ 2 + ∑ k ∈ range m, ((k : ℝ) + 1) * ε k) / m := by
  have P : ∀ n : ℕ, ((n : ℝ) + 1) * (f (x (n + 1)) + g (x (n + 1)) - (f xs + g xs))
      ≤ ∑ k ∈ range (n + 1), (f (x (k + 1)) + g (x (k + 1)) - (f xs + g xs))
        + ∑ k ∈ range (n + 1), (k : ℝ) * ε k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hd := descent_of_mem hf hL hα hαβ hr (hr.mem n)
      have hdrop : f (x (n + 1 + 1)) + g (x (n + 1 + 1)) ≤ f (x (n + 1)) + g (x (n + 1)) + ε (n + 1) := by
        nlinarith [sq_nonneg ‖rres α x (n + 1)‖]
      rw [sum_range_succ _ (n + 1), sum_range_succ _ (n + 1)]
      push_cast
      have hn : (0 : ℝ) ≤ n + 1 := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hdrop hn]
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hP := P n
  have hb := (E3b_sum hf hL hc hα hαβ hr hxs hmin (n + 1)).1
  have hsplit : ∑ k ∈ range (n + 1), ((k : ℝ) + 1) * ε k
      = ∑ k ∈ range (n + 1), (k : ℝ) * ε k + ∑ k ∈ range (n + 1), ε k := by
    rw [← sum_add_distrib]; congr 1; ext k; ring
  have hm' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hm', hsplit]
  push_cast at hP ⊢
  linarith

/-! ## Convex-analytic lemmas from the predicates (segment, Fermat, strong subgradient) -/

/-- If a ≤ c + t·b for every t ∈ (0, 1], then a ≤ c. -/
lemma le_of_forall_small {a b c : ℝ} (h : ∀ t : ℝ, 0 < t → t ≤ 1 → a ≤ c + t * b) : a ≤ c := by
  by_contra hac
  push Not at hac
  rcases le_or_gt b 0 with hb | hb
  · have := h 1 one_pos le_rfl; nlinarith
  · set t := min 1 ((a - c) / (2 * b)) with ht
    have ht0 : 0 < t := lt_min one_pos (by apply div_pos <;> linarith)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ (a - c) / (2 * b) := min_le_right _ _
    have := h t ht0 ht1
    rw [le_div_iff₀ (by linarith)] at ht2
    nlinarith

/-- The segment inequality of C(g, σ) on dom g: for p, w ∈ D and t ∈ [0, 1],
p + t(w − p) ∈ D and g(p + t(w − p)) ≤ (1 − t)g(p) + t g(w) − (σ/2)t(1 − t)‖w − p‖². -/
lemma modCD_segment {D : Set X} {g : X → ℝ} {σ : ℝ} (hC : ModCD D g σ) {p w : X}
    (hp : p ∈ D) (hw : w ∈ D) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    p + t • (w - p) ∈ D ∧
    g (p + t • (w - p)) ≤ (1 - t) * g p + t * g w - σ / 2 * t * (1 - t) * ‖w - p‖ ^ 2 := by
  have e : (1 - t) • p + t • w = p + t • (w - p) := by
    rw [smul_sub, sub_smul, one_smul]; abel
  have hmem : p + t • (w - p) ∈ D := e ▸ hC.1 hp hw (by linarith) ht0 (by ring)
  refine ⟨hmem, ?_⟩
  have h := hC.2 hp hw (by linarith : 0 ≤ 1 - t) ht0 (by ring)
  rw [e] at h
  simp only [smul_eq_mul] at h
  have n1 : ‖p + t • (w - p)‖ ^ 2 = ‖p‖ ^ 2 + 2 * t * inner ℝ p (w - p) + t ^ 2 * ‖w - p‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0]; ring
  have n2 : ‖w‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p (w - p) + ‖w - p‖ ^ 2 := by
    rw [← norm_add_sq_real, add_sub_cancel]
  rw [n1, n2] at h
  nlinarith

/-- From an exact subgradient v ∈ ∂g(p) and C(g, σ): the quadratic minorant
g(w) ≥ g(p) + ⟨v, w − p⟩ + (σ/2)‖w − p‖² for w ∈ dom g. -/
lemma strong_of_subgrad {D : Set X} {g : X → ℝ} {σ : ℝ} (hC : ModCD D g σ) {p v : X}
    (hv : EpsSubgrad D g 0 p v) {w : X} (hw : w ∈ D) :
    g p + inner ℝ v (w - p) + σ / 2 * ‖w - p‖ ^ 2 ≤ g w := by
  apply le_of_forall_small (b := σ / 2 * ‖w - p‖ ^ 2)
  intro t ht0 ht1
  obtain ⟨hm, hseg⟩ := modCD_segment hC hv.1 hw ht0.le ht1
  have hs := hv.2 _ hm
  rw [add_sub_cancel_left, real_inner_smul_right] at hs
  have key : t * (g p + inner ℝ v (w - p) + σ / 2 * ‖w - p‖ ^ 2)
      ≤ t * (g w + t * (σ / 2 * ‖w - p‖ ^ 2)) := by nlinarith
  exact le_of_mul_le_mul_left key ht0

/-- Fermat's rule with a quadratic term: x* minimising E = f + g on dom g, f differentiable
with β-Lipschitz gradient, C(g, σ) (σ any real). Then
g(w) ≥ g(x*) + ⟨−∇f(x*), w − x*⟩ + (σ/2)‖w − x*‖² for w ∈ dom g; in particular
−∇f(x*) ∈ ∂g(x*). -/
lemma fermat_strong {f : X → ℝ} {D : Set X} {g : X → ℝ} {β σ : ℝ} (hf : Differentiable ℝ f)
    (hL : LipGrad f β) (hC : ModCD D g σ) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) {w : X} (hw : w ∈ D) :
    g xs + inner ℝ (-gradient f xs) (w - xs) + σ / 2 * ‖w - xs‖ ^ 2 ≤ g w := by
  apply le_of_forall_small (b := (β + σ) / 2 * ‖w - xs‖ ^ 2)
  intro t ht0 ht1
  obtain ⟨hm, hseg⟩ := modCD_segment hC hxs hw ht0.le ht1
  have hE := hmin _ hm
  have hup := upper_bound hf hL xs (xs + t • (w - xs))
  rw [add_sub_cancel_left, real_inner_smul_right, norm_smul, Real.norm_of_nonneg ht0.le] at hup
  rw [inner_neg_left]
  have key : t * (g xs + -inner ℝ (gradient f xs) (w - xs) + σ / 2 * ‖w - xs‖ ^ 2)
      ≤ t * (g w + t * ((β + σ) / 2 * ‖w - xs‖ ^ 2)) := by nlinarith
  exact le_of_mul_le_mul_left key ht0

lemma fermat {f : X → ℝ} {D : Set X} {g : X → ℝ} {β σ : ℝ} (hf : Differentiable ℝ f)
    (hL : LipGrad f β) (hC : ModCD D g σ) (hσ : 0 ≤ σ) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) : EpsSubgrad D g 0 xs (-gradient f xs) :=
  ⟨hxs, fun w hw => by
    have := fermat_strong hf hL hC hxs hmin hw
    nlinarith [sq_nonneg ‖w - xs‖]⟩

/-- A stationary point of E = f + g with f convex minimises E on dom g. -/
lemma min_of_stationary {f : X → ℝ} {D : Set X} {g : X → ℝ} (hf : Differentiable ℝ f)
    (hc : ModC f 0) {xb : X} (hs : EpsSubgrad D g 0 xb (-gradient f xb)) :
    ∀ w ∈ D, f xb + g xb ≤ f w + g w := by
  intro w hw
  have h1 := OCF.H1.strongSubgrad_of_modC hf hc xb w
  have h2 := hs.2 w hw
  simp only [zero_div, zero_mul, add_zero, inner_neg_left] at h1 h2
  linarith

/-- Quasi-Fejér lemma (scalar form): a_k ≥ 0, a_{k+1} ≤ a_k + η_k with Σ η_k < ∞, η ≥ 0,
and a subsequence of (a_k) tending to 0 ⇒ a_k → 0. -/
lemma quasi_fejer {a η : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (hη0 : ∀ k, 0 ≤ η k) (hη : Summable η)
    (hrec : ∀ k, a (k + 1) ≤ a k + η k) {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hsub : Tendsto (fun i => a (φ i)) atTop (𝓝 0)) : Tendsto a atTop (𝓝 0) := by
  set T : ℕ → ℝ := fun k => ∑' i, η (i + k) with hT
  have hTsplit : ∀ k, T k = η k + T (k + 1) := by
    intro k
    have hs : Summable (fun i => η (i + k)) := (summable_nat_add_iff k).2 hη
    simp only [hT]
    rw [hs.tsum_eq_zero_add]
    simp only [zero_add]
    congr 1
    apply tsum_congr; intro i; congr 1; ring
  have hT0 : ∀ k, 0 ≤ T k := fun k => tsum_nonneg fun i => hη0 _
  set b : ℕ → ℝ := fun k => a k + T k with hb
  have hanti : Antitone b := by
    apply antitone_nat_of_succ_le
    intro k
    simp only [hb]
    have := hrec k
    have := hTsplit k
    linarith
  have hbdd : BddBelow (range b) := ⟨0, by rintro _ ⟨k, rfl⟩; exact add_nonneg (ha k) (hT0 k)⟩
  have hbconv := tendsto_atTop_ciInf hanti hbdd
  have hTconv : Tendsto T atTop (𝓝 0) := tendsto_sum_nat_add η
  have haconv : Tendsto a atTop (𝓝 ((⨅ k, b k) - 0)) :=
    (hbconv.sub hTconv).congr (fun k => by simp [hb])
  have h2 := haconv.comp hφ.tendsto_atTop
  have := tendsto_nhds_unique h2 hsub
  rwa [this] at haconv

/-- **(E3)(d).** f convex, (O3) with x* ∈ argmin E, g lower semicontinuous, ℝ^d (any proper
space), Σ ε_k < ∞: x_k → x̂ for some x̂ ∈ argmin E. -/
theorem E3d_converge [ProperSpace X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hc : ModC f 0) (hα : 0 < α)
    (hαβ : α * β = 1) (hlsc : LscExt D g) {x : ℕ → X} {ε : ℕ → ℝ}
    (hr : InexactRun f D g α x ε) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hS : Summable ε) :
    ∃ xh, xh ∈ D ∧ (∀ w ∈ D, f xh + g xh ≤ f w + g w) ∧ Tendsto x atTop (𝓝 xh) := by
  -- boundedness
  set R := √(‖x 0 - xs‖ ^ 2 + 2 * α * ∑' k, ε k) with hR
  have hball : ∀ k, x k ∈ Metric.closedBall xs R := by
    intro k
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply Real.le_sqrt_of_sq_le
    have h1 := (E3b_sum hf hL hc hα hαβ hr hxs hmin k).2
    have h2 : ∑ i ∈ range k, ε i ≤ ∑' i, ε i := hS.sum_le_tsum _ (fun i _ => (hr i).1)
    nlinarith
  obtain ⟨xh, -, φ, hφ, hlim⟩ := (ProperSpace.isCompact_closedBall xs R).tendsto_subseq hball
  -- residuals and limit-point stationarity
  have hres := (E2b_limits hf hL hα hαβ hr hmin hS).1
  have hst := E2c_stationary hL hα hlsc hr hS.tendsto_atTop_zero hres hφ hlim
  have hxhD : xh ∈ D := hst.1
  have hxhmin := min_of_stationary hf hc hst
  refine ⟨xh, hxhD, hxhmin, ?_⟩
  -- quasi-Fejér with respect to xh
  have hrec : ∀ k, ‖x (k + 1) - xh‖ ^ 2 ≤ ‖x k - xh‖ ^ 2 + 2 * α * ε k :=
    fun k => (E3a hf hL hc hα hαβ hr hxhD hxhmin k).2
  have hsub : Tendsto (fun i => ‖x (φ i) - xh‖ ^ 2) atTop (𝓝 0) := by
    have := ((tendsto_iff_norm_sub_tendsto_zero.1 hlim).pow 2)
    simpa using this
  have hq := quasi_fejer (a := fun k => ‖x k - xh‖ ^ 2) (η := fun k => 2 * α * ε k)
    (fun k => sq_nonneg _) (fun k => mul_nonneg (by positivity) (hr k).1) (hS.mul_left _)
    hrec hφ hsub
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have := (Real.continuous_sqrt.tendsto 0).comp hq
  simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using this

/-! ## Theorem H2.4 (E4): regimes A and B, rate with error accumulation -/

/-- q_A := 1 − σ_f/β. -/
noncomputable def qA (β σf : ℝ) : ℝ := 1 - σf / β

/-- q_B := q_A/(1 + σ_g/β). -/
noncomputable def qB (β σf σg : ℝ) : ℝ := qA β σf / (1 + σg / β)

/-- The two contraction regimes of (E4): A (σ_f > 0, q = q_A) or B (σ_f ≥ 0 < σ_g,
q = q_B). -/
def Regime (β σf σg q : ℝ) : Prop :=
  (0 < σf ∧ q = qA β σf) ∨ (0 ≤ σf ∧ 0 < σg ∧ q = qB β σf σg)

/-- The exact proximal map of g with C(g, σ), σ ≥ 0, is (1 + ασ)⁻¹-Lipschitz:
(1 + ασ)‖p₁ − p₂‖ ≤ ‖y₁ − y₂‖. -/
lemma prox_lip {D : Set X} {g : X → ℝ} {α σ : ℝ} (hα : 0 < α) (hC : ModCD D g σ)
    {y₁ y₂ p₁ p₂ : X} (h₁ : ProxEps D g α 0 y₁ p₁) (h₂ : ProxEps D g α 0 y₂ p₂) :
    (1 + α * σ) * ‖p₁ - p₂‖ ≤ ‖y₁ - y₂‖ := by
  have s1 := strong_of_subgrad hC h₁ h₂.1
  have s2 := strong_of_subgrad hC h₂ h₁.1
  rw [norm_sub_rev p₂ p₁] at s1
  have e1 : inner ℝ (α⁻¹ • (y₁ - p₁)) (p₂ - p₁) + inner ℝ (α⁻¹ • (y₂ - p₂)) (p₁ - p₂)
      = -(α⁻¹ * (inner ℝ (y₁ - y₂) (p₁ - p₂) - ‖p₁ - p₂‖ ^ 2)) := by
    rw [real_inner_smul_left, real_inner_smul_left, ← real_inner_self_eq_norm_sq,
      show p₂ - p₁ = -(p₁ - p₂) by abel, inner_neg_right]
    have : inner ℝ (y₁ - y₂) (p₁ - p₂) - inner ℝ (p₁ - p₂) (p₁ - p₂)
        = inner ℝ (y₂ - p₂) (p₁ - p₂) * (-1) + inner ℝ (y₁ - p₁) (p₁ - p₂) := by
      rw [show y₁ - y₂ = (y₁ - p₁) - (y₂ - p₂) + (p₁ - p₂) by abel, inner_add_left,
        inner_sub_left]; ring
    rw [this]; ring
  have key : α * σ * ‖p₁ - p₂‖ ^ 2 + ‖p₁ - p₂‖ ^ 2 ≤ inner ℝ (y₁ - y₂) (p₁ - p₂) := by
    have h3 : σ * ‖p₁ - p₂‖ ^ 2 ≤ α⁻¹ * (inner ℝ (y₁ - y₂) (p₁ - p₂) - ‖p₁ - p₂‖ ^ 2) := by
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hα.le
    have e : α * (α⁻¹ * (inner ℝ (y₁ - y₂) (p₁ - p₂) - ‖p₁ - p₂‖ ^ 2))
        = inner ℝ (y₁ - y₂) (p₁ - p₂) - ‖p₁ - p₂‖ ^ 2 := by
      rw [← mul_assoc, mul_inv_cancel₀ hα.ne', one_mul]
    rw [e] at h4
    linarith
  have hcs := real_inner_le_norm (y₁ - y₂) (p₁ - p₂)
  rcases eq_or_lt_of_le (norm_nonneg (p₁ - p₂)) with h0 | hpos
  · rw [← h0]; simp
  · have : (1 + α * σ) * ‖p₁ - p₂‖ * ‖p₁ - p₂‖ ≤ ‖y₁ - y₂‖ * ‖p₁ - p₂‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

lemma step_eq_inv {f : X → ℝ} {α β : ℝ} (hαβ : α * β = 1) : step f α = step f (1 / β) := by
  have : α = 1 / β := by
    have hβ : β ≠ 0 := by rintro rfl; simp at hαβ
    field_simp; linarith
  rw [this]

/-- T_α = prox_{αg} ∘ (Id − α∇f) is q_B-Lipschitz under C(f, σ_f), C(g, σ_g), σ_g ≥ 0
(B3 thm:fb(b) at α = 1/β; d ≥ 1). -/
theorem T_contract [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) (x x' : X) :
    ‖P (step f α x) - P (step f α x')‖ ≤ qB β σf σg * ‖x - x'‖ := by
  have hβ : 0 < β := by nlinarith
  have hσβ : σf ≤ β := le_of_strongMono_lipGrad ((modC_iff_strongMono hf σf).1 hCf) hL
  have h1 := prox_lip hα hCg (hP (step f α x)) (hP (step f α x'))
  have h2 := step_contract hf hL hβ hCf hσβ x x'
  rw [← step_eq_inv hαβ] at h2
  have hασ : α * σg = σg / β := by
    rw [eq_div_iff hβ.ne']; linear_combination σg * hαβ
  rw [hασ] at h1
  unfold qB qA
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  nlinarith

lemma qA_nonneg [Nontrivial X] {f : X → ℝ} {β σf : ℝ} (hf : Differentiable ℝ f)
    (hL : LipGrad f β) (hβ : 0 < β) (hCf : ModC f σf) : 0 ≤ qA β σf := by
  have hσβ : σf ≤ β := le_of_strongMono_lipGrad ((modC_iff_strongMono hf σf).1 hCf) hL
  unfold qA; rw [sub_nonneg, div_le_one hβ]; exact hσβ

/-- A minimiser of E on dom g is the fixed point of T_α (C(g, σ_g), σ_g ≥ 0). -/
lemma fixed_point {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σg : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hCg : ModCD D g σg)
    (hσg : 0 ≤ σg) {P : X → X} (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) : P (step f α xs) = xs := by
  have hF := fermat hf hL hCg hσg hxs hmin
  have : ProxEps D g α 0 (step f α xs) xs := by
    unfold ProxEps; rw [prox_vec_eq f hα.ne', sub_self, smul_zero, zero_sub]; exact hF
  exact (comparison_c hα this (hP _)).symm

/-- In regime A or B: ‖T_α x − x*‖ ≤ q‖x − x*‖ for every x, and 0 ≤ q < 1. -/
theorem regime_contract [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q) :
    (∀ x, ‖P (step f α x) - xs‖ ≤ q * ‖x - xs‖) ∧ 0 ≤ q ∧ q < 1 := by
  have hβ : 0 < β := by nlinarith
  have hfix := fixed_point hf hL hα hCg hσg hP hxs hmin
  have hqA := qA_nonneg hf hL hβ hCf
  have hqBA : qB β σf σg ≤ qA β σf := by
    unfold qB; rw [div_le_iff₀ (by positivity)]
    nlinarith [div_nonneg hσg hβ.le]
  have hqB0 : 0 ≤ qB β σf σg := by unfold qB; positivity
  have hcon : ∀ x, ‖P (step f α x) - xs‖ ≤ qB β σf σg * ‖x - xs‖ := by
    intro x
    have := T_contract hf hL hα hαβ hCf hCg hσg hP x xs
    rwa [hfix] at this
  rcases hreg with ⟨hσf, rfl⟩ | ⟨hσf, hσg', rfl⟩
  · refine ⟨fun x => (hcon x).trans (mul_le_mul_of_nonneg_right hqBA (norm_nonneg _)), hqA, ?_⟩
    unfold qA; have : 0 < σf / β := div_pos hσf hβ; linarith
  · refine ⟨hcon, hqB0, ?_⟩
    unfold qB qA
    rw [div_lt_one (by positivity)]
    have : 0 ≤ σf / β := div_nonneg hσf hβ.le
    have : 0 < σg / β := div_pos hσg' hβ
    linarith

/-- Scalar unrolling: a_{k+1} ≤ q a_k + b_k (q ≥ 0) ⇒
a_k ≤ q^k a₀ + Σ_{i<k} q^{k−1−i} b_i. -/
lemma unroll {a b : ℕ → ℝ} {q : ℝ} (hq : 0 ≤ q) (h : ∀ k, a (k + 1) ≤ q * a k + b k) (k : ℕ) :
    a k ≤ q ^ k * a 0 + ∑ i ∈ range k, q ^ (k - 1 - i) * b i := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 := h k
    have h2 := mul_le_mul_of_nonneg_left ih hq
    rw [sum_range_succ, Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    have e : q * ∑ i ∈ range k, q ^ (k - 1 - i) * b i = ∑ i ∈ range k, q ^ (k - i) * b i := by
      rw [mul_sum]
      apply sum_congr rfl
      intro i hi
      have hi' := mem_range.1 hi
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [mul_add, e, ← mul_assoc, ← pow_succ'] at h2
    linarith

/-- **(E4)(a).** Regime A or B, x* the minimiser, P the exact proximal map:
‖x_{k+1} − x*‖ ≤ q‖x_k − x*‖ + √(αε_k), hence
‖x_k − x*‖ ≤ q^k‖x₀ − x*‖ + Σ_{i<k} q^{k−1−i}√(αε_i). -/
theorem E4a [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) :
    (∀ k, ‖x (k + 1) - xs‖ ≤ q * ‖x k - xs‖ + √(α * ε k)) ∧
    (∀ k, ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ + ∑ i ∈ range k, q ^ (k - 1 - i) * √(α * ε i)) := by
  obtain ⟨hcon, hq0, -⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg
  have one : ∀ k, ‖x (k + 1) - xs‖ ≤ q * ‖x k - xs‖ + √(α * ε k) := by
    intro k
    have h1 := (comparison_b hα (hr k).2 (hP (step f α (x k)))).2.1
    have h2 := hcon (x k)
    calc ‖x (k + 1) - xs‖ ≤ ‖x (k + 1) - P (step f α (x k))‖ + ‖P (step f α (x k)) - xs‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ q * ‖x k - xs‖ + √(α * ε k) := by linarith
  exact ⟨one, unroll hq0 one⟩

/-- **(E4)(b).** Constant accuracy ε_i ≤ ε̄: ‖x_k − x*‖ ≤ q^k‖x₀ − x*‖ +
(1 − q^k)√(αε̄)/(1 − q); in regime A, √(αε̄)/(1 − q_A) = √(βε̄)/σ_f. -/
theorem E4b [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {εbar : ℝ}
    (hbar : ∀ i, ε i ≤ εbar) (k : ℕ) :
    ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ + (1 - q ^ k) * √(α * εbar) / (1 - q) := by
  obtain ⟨-, hq0, hq1⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg
  have h := (E4a hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg hr).2 k
  have hs : ∑ i ∈ range k, q ^ (k - 1 - i) * √(α * ε i)
      ≤ ∑ i ∈ range k, q ^ (k - 1 - i) * √(α * εbar) := by
    apply sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 _)
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hbar i) hα.le)
  have hg : ∑ i ∈ range k, q ^ (k - 1 - i) * √(α * εbar) = (1 - q ^ k) * √(α * εbar) / (1 - q) := by
    rw [← sum_mul, sum_range_reflect (fun j => q ^ j) k, geom_sum_eq hq1.ne]
    have : (q ^ k - 1) / (q - 1) = (1 - q ^ k) / (1 - q) := by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]
    rw [this]; ring
  linarith

/-- (E4)(b), regime-A constant: √(αε̄)/(1 − q_A) = √(βε̄)/σ_f. -/
theorem E4b_regimeA_const {α β σf εbar : ℝ} (hα : 0 < α) (hαβ : α * β = 1) (hσf : 0 < σf) : √(α * εbar) / (1 - qA β σf) = √(β * εbar) / σf := by
  have hβ : 0 < β := by nlinarith
  have hb : β = α⁻¹ := by field_simp; linarith
  unfold qA
  rw [hb, show 1 - (1 - σf / α⁻¹) = α * σf by field_simp; ring]
  have : √(α⁻¹ * εbar) = α⁻¹ * √(α * εbar) := by
    rw [show α⁻¹ * εbar = α⁻¹ ^ 2 * (α * εbar) by field_simp, Real.sqrt_mul (by positivity) (α * εbar),
      Real.sqrt_sq (by positivity)]
  rw [this]
  field_simp

/-- The coefficient s_k of (E4)(c): (q^k − θ^k)/(q − θ) if θ ≠ q, k q^{k−1} if θ = q. -/
noncomputable def sk (q θ : ℝ) (k : ℕ) : ℝ :=
  if θ = q then k * q ^ (k - 1) else (q ^ k - θ ^ k) / (q - θ)

lemma sum_eq_sk (q θ : ℝ) (k : ℕ) : ∑ i ∈ range k, q ^ (k - 1 - i) * θ ^ i = sk q θ k := by
  unfold sk
  split_ifs with h
  · rw [h]
    rw [sum_congr rfl (g := fun _ => q ^ (k - 1)), sum_const, card_range, nsmul_eq_mul]
    intro i hi
    rw [← pow_add]; congr 1; have := mem_range.1 hi; omega
  · have hne : θ - q ≠ 0 := sub_ne_zero.2 h
    have := geom_sum₂_mul θ q k
    rw [eq_div_iff (sub_ne_zero.2 (Ne.symm h))]
    have e : ∑ i ∈ range k, q ^ (k - 1 - i) * θ ^ i = ∑ i ∈ range k, θ ^ i * q ^ (k - 1 - i) :=
      sum_congr rfl fun i _ => mul_comm _ _
    rw [e]
    linear_combination (-1 : ℝ) * this

/-- **(E4)(c).** Geometric accuracy ε_i ≤ ε̄₀θ^{2i}, θ ∈ [0, 1):
‖x_k − x*‖ ≤ q^k‖x₀ − x*‖ + √(αε̄₀)s_k, and for θ ≠ q,
‖x_k − x*‖ ≤ max{q, θ}^k(‖x₀ − x*‖ + √(αε̄₀)/|q − θ|). -/
theorem E4c [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {ε0 θ : ℝ} (hθ0 : 0 ≤ θ)
    (_hθ1 : θ < 1) (hgeo : ∀ i, ε i ≤ ε0 * θ ^ (2 * i)) (k : ℕ) :
    ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ + √(α * ε0) * sk q θ k ∧
    (θ ≠ q → ‖x k - xs‖ ≤ max q θ ^ k * (‖x 0 - xs‖ + √(α * ε0) / |q - θ|)) := by
  obtain ⟨-, hq0, -⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg
  have h := (E4a hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg hr).2 k
  have hs : ∑ i ∈ range k, q ^ (k - 1 - i) * √(α * ε i)
      ≤ ∑ i ∈ range k, q ^ (k - 1 - i) * (√(α * ε0) * θ ^ i) := by
    apply sum_le_sum; intro i _
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hq0 _)
    have e : α * (ε0 * θ ^ (2 * i)) = α * ε0 * (θ ^ i) ^ 2 := by ring
    calc √(α * ε i) ≤ √(α * (ε0 * θ ^ (2 * i))) :=
          Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (hgeo i) hα.le)
      _ = √(α * ε0) * θ ^ i := by
          rw [e, Real.sqrt_mul' _ (sq_nonneg _), Real.sqrt_sq (pow_nonneg hθ0 _)]
  have hsk : ∑ i ∈ range k, q ^ (k - 1 - i) * (√(α * ε0) * θ ^ i) = √(α * ε0) * sk q θ k := by
    rw [← sum_eq_sk, mul_sum]; apply sum_congr rfl; intro i _; ring
  have main : ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ + √(α * ε0) * sk q θ k := by linarith
  refine ⟨main, fun hne => ?_⟩
  set M := max q θ
  have hqM : q ^ k ≤ M ^ k := pow_le_pow_left₀ hq0 (le_max_left _ _) k
  have hθM : θ ^ k ≤ M ^ k := pow_le_pow_left₀ hθ0 (le_max_right _ _) k
  have hab : |q ^ k - θ ^ k| ≤ M ^ k := by
    rw [abs_sub_le_iff]
    constructor <;> nlinarith [pow_nonneg hq0 k, pow_nonneg hθ0 k]
  have hpos : 0 < |q - θ| := abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))
  have hskle : sk q θ k ≤ M ^ k / |q - θ| := by
    unfold sk; rw [if_neg hne]
    calc (q ^ k - θ ^ k) / (q - θ) ≤ |(q ^ k - θ ^ k) / (q - θ)| := le_abs_self _
      _ = |q ^ k - θ ^ k| / |q - θ| := abs_div _ _
      _ ≤ M ^ k / |q - θ| := div_le_div_of_nonneg_right hab hpos.le
  have hsq : 0 ≤ √(α * ε0) := Real.sqrt_nonneg _
  calc ‖x k - xs‖ ≤ q ^ k * ‖x 0 - xs‖ + √(α * ε0) * sk q θ k := main
    _ ≤ M ^ k * ‖x 0 - xs‖ + √(α * ε0) * (M ^ k / |q - θ|) := by
        gcongr
    _ = M ^ k * (‖x 0 - xs‖ + √(α * ε0) / |q - θ|) := by ring

/-- Eventual form of the unrolled recursion: if a_{k+1} ≤ q a_k + b_k with 0 ≤ q < 1,
b ≥ 0, and eventually b_k ≤ B, then for every δ > 0, eventually a_k ≤ B/(1 − q) + δ. -/
lemma eventual_bound {a b : ℕ → ℝ} {q B : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hb0 : ∀ k, 0 ≤ b k) (h : ∀ k, a (k + 1) ≤ q * a k + b k) (hB : ∀ᶠ k in atTop, b k ≤ B)
    {δ : ℝ} (hδ : 0 < δ) : ∀ᶠ k in atTop, a k ≤ B / (1 - q) + δ := by
  obtain ⟨K, hK⟩ := eventually_atTop.1 hB
  have hB0 : 0 ≤ B := (hb0 K).trans (hK K le_rfl)
  have h' : ∀ j, a (j + 1 + K) ≤ q * a (j + K) + b (j + K) := by
    intro j; rw [show j + 1 + K = j + K + 1 by ring]; exact h _
  have hu := unroll (a := fun j => a (j + K)) (b := fun j => b (j + K)) hq0 h'
  have hgeo : Tendsto (fun j => q ^ j * a K) atTop (𝓝 (0 * a K)) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _
  rw [zero_mul] at hgeo
  obtain ⟨J, hJ⟩ := eventually_atTop.1 ((tendsto_order.1 hgeo).2 δ hδ)
  rw [eventually_atTop]
  refine ⟨J + K, fun k hk => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + K := ⟨k - K, by omega⟩
  have h1 := hu j
  simp only [zero_add] at h1
  have hs : ∑ i ∈ range j, q ^ (j - 1 - i) * b (i + K) ≤ ∑ i ∈ range j, q ^ (j - 1 - i) * B :=
    sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hK _ (by omega)) (pow_nonneg hq0 _)
  have hg : ∑ i ∈ range j, q ^ (j - 1 - i) * B ≤ B / (1 - q) := by
    rw [← sum_mul, sum_range_reflect (fun i => q ^ i) j, geom_sum_eq hq1.ne]
    have : (q ^ j - 1) / (q - 1) = (1 - q ^ j) / (1 - q) := by
      rw [← neg_div_neg_eq, neg_sub, neg_sub]
    rw [this, div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ (by linarith)
    nlinarith [pow_nonneg hq0 j]
  have := hJ j (by omega)
  linarith

/-- **(E4)(d), first part.** In regime A or B, ε_k → 0 ⇒ x_k → x*. -/
theorem E4d_tendsto [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto x atTop (𝓝 xs) := by
  obtain ⟨-, hq0, hq1⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg
  have one := (E4a hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg hr).1
  have hs : Tendsto (fun k => √(α * ε k)) atTop (𝓝 0) := by
    have h0 := hε0.const_mul α
    rw [mul_zero] at h0
    have := (Real.continuous_sqrt.tendsto 0).comp h0
    simpa [Function.comp_def] using this
  rw [tendsto_iff_norm_sub_tendsto_zero, tendsto_order]
  refine ⟨fun a' ha' => Eventually.of_forall fun k => ha'.trans_le (norm_nonneg _), ?_⟩
  intro η hη
  have h1q : 0 < 1 - q := by linarith
  set δ := η * (1 - q) / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  have hev := (tendsto_order.1 hs).2 δ hδ0
  have hb := eventual_bound (a := fun k => ‖x k - xs‖) hq0 hq1 (fun k => Real.sqrt_nonneg _) one
    (hev.mono fun k hk => hk.le) hδ0
  filter_upwards [hb] with k hk
  have : δ / (1 - q) = η / 4 := by rw [hδ]; field_simp
  rw [this] at hk
  have : δ ≤ η / 4 := by
    rw [hδ, div_le_div_iff_of_pos_right (by norm_num)]; nlinarith
  linarith

/-- **(E4)(d), second part** (limsup bound): for every ℓ with ε_k ≤ ℓ eventually,
limsup ‖x_k − x*‖ ≤ √(αℓ)/(1 − q). -/
theorem E4d_limsup_of_le [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ}
    {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) {ℓ : ℝ}
    (hℓ : ∀ᶠ k in atTop, ε k ≤ ℓ) :
    limsup (fun k => ‖x k - xs‖) atTop ≤ √(α * ℓ) / (1 - q) := by
  obtain ⟨-, hq0, hq1⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg
  have one := (E4a hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg hr).1
  have hB : ∀ᶠ k in atTop, √(α * ε k) ≤ √(α * ℓ) :=
    hℓ.mono fun k hk => Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hk hα.le)
  apply le_of_forall_pos_le_add
  intro δ hδ
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop (fun k => norm_nonneg _))
  exact eventual_bound (a := fun k => ‖x k - xs‖) hq0 hq1 (fun k => Real.sqrt_nonneg _) one hB hδ

/-- **(E4)(d), second part** with limsup ε: if (ε_k) is bounded,
limsup ‖x_k − x*‖ ≤ √(α limsup ε_k)/(1 − q). -/
theorem E4d_limsup [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg q : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w) (hreg : Regime β σf σg q)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε)
    (hbdd : IsBoundedUnder (· ≤ ·) atTop ε) :
    limsup (fun k => ‖x k - xs‖) atTop ≤ √(α * limsup ε atTop) / (1 - q) := by
  obtain ⟨-, hq0, hq1⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg
  set L := limsup ε atTop
  have hδ : ∀ δ > 0, limsup (fun k => ‖x k - xs‖) atTop ≤ √(α * (L + δ)) / (1 - q) := by
    intro δ hδ
    apply E4d_limsup_of_le hf hL hα hαβ hCf hCg hσg hP hxs hmin hreg hr
    exact (eventually_lt_of_limsup_lt (lt_add_of_pos_right L hδ) hbdd).mono fun k hk => hk.le
  have hcont : Tendsto (fun δ => √(α * (L + δ)) / (1 - q)) (𝓝[>] 0)
      (𝓝 (√(α * (L + 0)) / (1 - q))) := by
    apply Tendsto.mono_left _ nhdsWithin_le_nhds
    apply Tendsto.div_const
    apply (Real.continuous_sqrt.tendsto _).comp
    exact (tendsto_const_nhds.add tendsto_id).const_mul α
  rw [add_zero] at hcont
  exact ge_of_tendsto hcont (eventually_nhdsWithin_of_forall fun δ hδ' => hδ δ hδ')

/-! ## Theorem H2.4 (E5): pointwise distance certificates with an ε-correction -/

/-- **(E5)(a), query-point residual.** ‖R_α(x_k)‖ ≤ ‖r_k‖ + √(βε_k), where
R_α(x_k) = (x_k − P(x_k − α∇f(x_k)))/α. -/
theorem E5a_resid {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ} (hα : 0 < α)
    (hαβ : α * β = 1) {P : X → X} (hP : ∀ y, ProxEps D g α 0 y (P y))
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖α⁻¹ • (x k - P (step f α (x k)))‖ ≤ ‖rres α x k‖ + √(β * ε k) := by
  have h := comparison_e hα hαβ (hr k).2 (hP (step f α (x k)))
  have e : α⁻¹ • (x k - P (step f α (x k)))
      = rres α x k + (α⁻¹ • (x k - P (step f α (x k))) - α⁻¹ • (x k - x (k + 1))) := by
    unfold rres; abel
  rw [e]
  exact (norm_add_le _ _).trans (by unfold rres; linarith)

/-- From a q-contraction towards x* (q < 1): ‖x − x*‖ ≤ (α/(1 − q))‖R_α(x)‖. -/
lemma dist_le_of_contract {f : X → ℝ} {α q : ℝ} (hα : 0 < α) (hq1 : q < 1) {P : X → X}
    {xs : X} (hcon : ∀ x, ‖P (step f α x) - xs‖ ≤ q * ‖x - xs‖) (x : X) :
    ‖x - xs‖ ≤ α / (1 - q) * ‖α⁻¹ • (x - P (step f α x))‖ := by
  have hn : ‖x - P (step f α x)‖ = α * ‖α⁻¹ • (x - P (step f α x))‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le, ← mul_assoc, mul_inv_cancel₀ hα.ne',
      one_mul]
  have h1 := norm_sub_le_norm_sub_add_norm_sub x (P (step f α x)) xs
  have h2 := hcon x
  rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
  nlinarith

/-- **(E5)(a), regime A** (σ_f > 0): ‖x_k − x*‖ ≤ (‖r_k‖ + √(βε_k))/σ_f. -/
theorem E5a_regimeA [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hσf : 0 < σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖x k - xs‖ ≤ (‖rres α x k‖ + √(β * ε k)) / σf := by
  have hβ : 0 < β := by nlinarith
  obtain ⟨hcon, -, hq1⟩ := regime_contract hf hL hα hαβ hCf hCg hσg hP hxs hmin
    (Or.inl ⟨hσf, rfl⟩)
  have h1 := dist_le_of_contract hα hq1 hcon (x k)
  have h2 := E5a_resid hα hαβ hP hr k
  have e : α / (1 - qA β σf) = 1 / σf := by
    rw [show 1 - qA β σf = σf / β by unfold qA; ring, div_div_eq_mul_div, hαβ]
  rw [e] at h1
  calc ‖x k - xs‖ ≤ 1 / σf * ‖α⁻¹ • (x k - P (step f α (x k)))‖ := h1
    _ ≤ 1 / σf * (‖rres α x k‖ + √(β * ε k)) := by gcongr
    _ = _ := by ring

/-- **(E5)(a), σ_f ≥ 0 < σ_g**: ‖x_k − x*‖ ≤ κ_g(‖r_k‖ + √(βε_k)),
κ_g = (1 + σ_g/β)/(σ_f + σ_g). -/
theorem E5a_regimeB [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hσf : 0 ≤ σf) (hCg : ModCD D g σg) (hσg : 0 < σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖x k - xs‖ ≤ (1 + σg / β) / (σf + σg) * (‖rres α x k‖ + √(β * ε k)) := by
  have hβ : 0 < β := by nlinarith
  obtain ⟨hcon, -, hq1⟩ := regime_contract hf hL hα hαβ hCf hCg hσg.le hP hxs hmin
    (Or.inr ⟨hσf, hσg, rfl⟩)
  have h1 := dist_le_of_contract hα hq1 hcon (x k)
  have h2 := E5a_resid hα hαβ hP hr k
  have e : α / (1 - qB β σf σg) = (1 + σg / β) / (σf + σg) := by
    have hne : β + σg ≠ 0 := by linarith
    have e1 : 1 - qB β σf σg = (σf + σg) / (β + σg) := by
      unfold qB qA; field_simp; ring
    rw [e1, div_div_eq_mul_div]
    congr 1
    rw [mul_add, hαβ]
    congr 1
    rw [eq_div_iff hβ.ne']
    linear_combination σg * hαβ
  rw [e] at h1
  calc ‖x k - xs‖ ≤ _ := h1
    _ ≤ (1 + σg / β) / (σf + σg) * (‖rres α x k‖ + √(β * ε k)) := by gcongr

/-- Quadratic minorant of a μ-strongly convex E = f + g (f possibly nonconvex) at a point
p with an exact subgradient v ∈ ∂g(p): E(w) ≥ E(p) + ⟨∇f(p) + v, w − p⟩ + (μ/2)‖w − p‖². -/
lemma strong_E_at {f : X → ℝ} {D : Set X} {g : X → ℝ} {β μ : ℝ} (hf : Differentiable ℝ f)
    (hL : LipGrad f β) (hCE : ModCD D (fun w => f w + g w) μ) {p v : X}
    (hv : EpsSubgrad D g 0 p v) {w : X} (hw : w ∈ D) :
    f p + g p + inner ℝ (gradient f p + v) (w - p) + μ / 2 * ‖w - p‖ ^ 2 ≤ f w + g w := by
  apply le_of_forall_small (b := (β + μ) / 2 * ‖w - p‖ ^ 2)
  intro t ht0 ht1
  obtain ⟨hm, hseg⟩ := modCD_segment hCE hv.1 hw ht0.le ht1
  have hfl := OCF.H1.strongSubgrad_of_modC hf (modC_neg_of_lipGrad hf hL) p (p + t • (w - p))
  have hg := hv.2 _ hm
  rw [add_sub_cancel_left] at hfl hg
  rw [real_inner_smul_right] at hfl hg
  rw [norm_smul, Real.norm_of_nonneg ht0.le] at hfl
  rw [inner_add_left]
  have key : t * (f p + g p + (inner ℝ (gradient f p) (w - p) + inner ℝ v (w - p))
      + μ / 2 * ‖w - p‖ ^ 2) ≤ t * (f w + g w + t * ((β + μ) / 2 * ‖w - p‖ ^ 2)) := by
    nlinarith
  exact le_of_mul_le_mul_left key ht0

/-- **(E5)(a), regime C** (C(f + g, μ), μ > 0, f possibly nonconvex):
‖x_k − x*‖ ≤ (α + 2/μ)(‖r_k‖ + √(βε_k)) (κ_N at α = 1/β). -/
theorem E5a_regimeC {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β μ : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCE : ModCD D (fun w => f w + g w) μ) (hμ : 0 < μ) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖x k - xs‖ ≤ (α + 2 / μ) * (‖rres α x k‖ + √(β * ε k)) := by
  -- the query-point distance bound ‖x − x*‖ ≤ (α + 2/μ)‖R_α(x)‖
  have hdist : ∀ y : X, ‖y - xs‖ ≤ (α + 2 / μ) * ‖α⁻¹ • (y - P (step f α y))‖ := by
    intro y
    set p := P (step f α y)
    set R := α⁻¹ • (y - p)
    have hv := hP (step f α y)
    unfold ProxEps at hv
    rw [prox_vec_eq f hα.ne'] at hv
    have s1 := strong_E_at hf hL hCE hv hxs
    have s2 := strong_of_subgrad (g := fun w => f w + g w) hCE
      (show EpsSubgrad D (fun w => f w + g w) 0 xs 0 from
        ⟨hxs, fun w hw => by simpa using hmin w hw⟩) hv.1
    simp only [inner_zero_left, add_zero] at s2
    have hu := OCF.H1.prox_u_norm hα hL y p
    rw [hαβ] at hu
    have hue : gradient f p + (R - gradient f y) = R - gradient f y + gradient f p := by abel
    rw [hue] at s1
    set u := R - gradient f y + gradient f p
    have hin : inner ℝ u (xs - p) = -inner ℝ u (p - xs) := by
      rw [← inner_neg_right, neg_sub]
    rw [hin, norm_sub_rev xs p] at s1
    have hcs := real_inner_le_norm u (p - xs)
    have hpx : μ * ‖p - xs‖ ≤ ‖u‖ := by
      rcases eq_or_lt_of_le (norm_nonneg (p - xs)) with h0 | hpos
      · rw [← h0, mul_zero]; exact norm_nonneg _
      · have : μ * ‖p - xs‖ * ‖p - xs‖ ≤ ‖u‖ * ‖p - xs‖ := by nlinarith
        exact le_of_mul_le_mul_right this hpos
    have hyp : ‖y - p‖ = α * ‖R‖ := by
      simp only [R]
      rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hα).le, ← mul_assoc,
        mul_inv_cancel₀ hα.ne', one_mul]
    have htri := norm_sub_le_norm_sub_add_norm_sub y p xs
    have hpx' : ‖p - xs‖ ≤ 2 / μ * ‖R‖ := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hμ]; linarith
    calc ‖y - xs‖ ≤ α * ‖R‖ + 2 / μ * ‖R‖ := by linarith
      _ = (α + 2 / μ) * ‖R‖ := by ring
  have h2 := E5a_resid hα hαβ hP hr k
  calc ‖x k - xs‖ ≤ (α + 2 / μ) * ‖α⁻¹ • (x k - P (step f α (x k)))‖ := hdist (x k)
    _ ≤ (α + 2 / μ) * (‖rres α x k‖ + √(β * ε k)) := by gcongr

/-- One inexact step against any q-contraction of the exact step towards x*:
‖x_{k+1} − x*‖ ≤ q‖x_k − x*‖ + √(αε_k). -/
lemma one_step_contract {f : X → ℝ} {D : Set X} {g : X → ℝ} {α q : ℝ} (hα : 0 < α)
    {P : X → X} (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X}
    (hcon : ∀ x, ‖P (step f α x) - xs‖ ≤ q * ‖x - xs‖)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖x (k + 1) - xs‖ ≤ q * ‖x k - xs‖ + √(α * ε k) := by
  have h1 := (comparison_b hα (hr k).2 (hP (step f α (x k)))).2.1
  have h2 := hcon (x k)
  calc ‖x (k + 1) - xs‖ ≤ ‖x (k + 1) - P (step f α (x k))‖ + ‖P (step f α (x k)) - xs‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ q * ‖x k - xs‖ + √(α * ε k) := by linarith

lemma sqrt_alpha {α β e : ℝ} (hα : 0 < α) (hαβ : α * β = 1) : √(α * e) = α * √(β * e) := by
  rw [show α * e = α ^ 2 * (β * e) by linear_combination (-(α * e)) * hαβ,
    Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq hα.le]

/-- **(E5)(b), returned point** (σ_f ≥ 0, σ_g ≥ 0, μ = σ_f + σ_g > 0, i.e. regimes A and B):
‖x_{k+1} − x*‖ ≤ (q_A‖r_k‖ + (1 + σ_g/β)√(βε_k))/μ. -/
theorem E5b_returned [Nontrivial X] {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hσg : 0 ≤ σg)
    (hμ : 0 < σf + σg) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {xs : X} (hxs : xs ∈ D)
    (hmin : ∀ w ∈ D, f xs + g xs ≤ f w + g w)
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖x (k + 1) - xs‖ ≤ (qA β σf * ‖rres α x k‖ + (1 + σg / β) * √(β * ε k)) / (σf + σg) := by
  have hβ : 0 < β := by nlinarith
  have hfix := fixed_point hf hL hα hCg hσg hP hxs hmin
  have hcon : ∀ y, ‖P (step f α y) - xs‖ ≤ qB β σf σg * ‖y - xs‖ := by
    intro y
    have := T_contract hf hL hα hαβ hCf hCg hσg hP y xs
    rwa [hfix] at this
  have hne : β + σg ≠ 0 := by linarith
  have e1 : 1 - qB β σf σg = (σf + σg) / (β + σg) := by
    unfold qB qA; field_simp; ring
  have hq1 : qB β σf σg < 1 := by
    have : 0 < (σf + σg) / (β + σg) := by positivity
    linarith
  have hqB0 : 0 ≤ qB β σf σg := by
    have := qA_nonneg hf hL hβ hCf
    unfold qB; positivity
  have h1 := one_step_contract hα hP hcon hr k
  have h2 := dist_le_of_contract hα hq1 hcon (x k)
  have h3 := E5a_resid hα hαβ hP hr k
  have hα' : α = 1 / β := by field_simp; linarith
  have hK : α / (1 - qB β σf σg) = (1 + σg / β) / (σf + σg) := by
    rw [e1, div_div_eq_mul_div, hα']; field_simp
  have hqK : qB β σf σg * ((1 + σg / β) / (σf + σg)) = qA β σf / (σf + σg) := by
    unfold qB; field_simp
  have hsum : α + qA β σf / (σf + σg) = (1 + σg / β) / (σf + σg) := by
    unfold qA; rw [hα']; field_simp; ring
  rw [hK] at h2
  rw [sqrt_alpha hα hαβ] at h1
  set s := √(β * ε k)
  set ρ := ‖rres α x k‖
  have hd : ‖x k - xs‖ ≤ (1 + σg / β) / (σf + σg) * (ρ + s) :=
    h2.trans (mul_le_mul_of_nonneg_left h3 (by positivity))
  calc ‖x (k + 1) - xs‖ ≤ qB β σf σg * ((1 + σg / β) / (σf + σg) * (ρ + s)) + α * s := by
        nlinarith [mul_le_mul_of_nonneg_left hd hqB0]
    _ = qA β σf / (σf + σg) * ρ + (α + qA β σf / (σf + σg)) * s := by
        rw [← mul_assoc, hqK]; ring
    _ = (qA β σf * ρ + (1 + σg / β) * s) / (σf + σg) := by
        rw [hsum]; ring

/-! ## Proposition H2.6 (returned-point certificate from the next gradient) -/

/-- **Proposition H2.6.** C(f, σ_f) (σ_f ∈ ℝ), C(g, σ_g), s := 2σ_f + σ_g > 0, x* stationary
(−∇f(x*) ∈ ∂g(x*)). For z ∈ dom g, v ∈ ∂_ε g(z), u := ∇f(z) + v:
‖z − x*‖ ≤ (‖u‖ + √(‖u‖² + 2sε))/s. -/
theorem prop_H2_6 {f : X → ℝ} {D : Set X} {g : X → ℝ} {σf σg : ℝ}
    (hf : Differentiable ℝ f) (hCf : ModC f σf) (hCg : ModCD D g σg)
    (hs : 0 < 2 * σf + σg) {xs : X} (hst : EpsSubgrad D g 0 xs (-gradient f xs))
    {z v : X} {ε : ℝ} (hv : EpsSubgrad D g ε z v) :
    ‖z - xs‖ ≤ (‖gradient f z + v‖ + √(‖gradient f z + v‖ ^ 2 + 2 * (2 * σf + σg) * ε))
      / (2 * σf + σg) := by
  set s := 2 * σf + σg
  set u := gradient f z + v
  set t := ‖z - xs‖
  have h1 := (modC_iff_strongMono hf σf).1 hCf z xs
  have h2 := strong_of_subgrad hCg hst hv.1
  have h3 := hv.2 xs hst.1
  have hin : inner ℝ u (z - xs) = inner ℝ (gradient f z - gradient f xs) (z - xs)
      + inner ℝ (-gradient f xs) (z - xs) * (-1) + inner ℝ v (z - xs) := by
    simp only [u, inner_add_left, inner_sub_left, inner_neg_left]; ring
  have hv' : inner ℝ v (xs - z) = -inner ℝ v (z - xs) := by
    rw [← inner_neg_right, neg_sub]
  rw [hv'] at h3
  have key : s / 2 * t ^ 2 - ε ≤ inner ℝ u (z - xs) := by
    simp only [s, t]; rw [hin]; nlinarith
  have hcs := real_inner_le_norm u (z - xs)
  have hq : (s * t - ‖u‖) ^ 2 ≤ ‖u‖ ^ 2 + 2 * s * ε := by nlinarith
  have := Real.abs_le_sqrt hq
  have h4 : s * t - ‖u‖ ≤ √(‖u‖ ^ 2 + 2 * s * ε) := (le_abs_self _).trans this
  rw [le_div_iff₀ hs]
  linarith

/-- **Proposition H2.6, run form.** In an inexact run (∇f β-Lipschitz, α = 1/β):
‖x_{k+1} − x*‖ ≤ (2‖r_k‖ + √(4‖r_k‖² + 2sε_k))/s, computable from the run alone. -/
theorem prop_H2_6_run {f : X → ℝ} {D : Set X} {g : X → ℝ} {α β σf σg : ℝ}
    (hf : Differentiable ℝ f) (hL : LipGrad f β) (hα : 0 < α) (hαβ : α * β = 1)
    (hCf : ModC f σf) (hCg : ModCD D g σg) (hs : 0 < 2 * σf + σg) {xs : X}
    (hst : EpsSubgrad D g 0 xs (-gradient f xs))
    {x : ℕ → X} {ε : ℕ → ℝ} (hr : InexactRun f D g α x ε) (k : ℕ) :
    ‖x (k + 1) - xs‖ ≤ (2 * ‖rres α x k‖ + √(4 * ‖rres α x k‖ ^ 2 + 2 * (2 * σf + σg) * ε k))
      / (2 * σf + σg) := by
  obtain ⟨hsub, hnorm⟩ := E2d_u hL hα hαβ hr k
  have h := prop_H2_6 hf hCf hCg hs hst hsub
  have e : gradient f (x (k + 1)) + (rres α x k + gradient f (x (k + 1)) - gradient f (x k)
      - gradient f (x (k + 1))) = rres α x k + gradient f (x (k + 1)) - gradient f (x k) := by abel
  rw [e] at h
  refine h.trans (div_le_div_of_nonneg_right ?_ hs.le)
  have hsq : ‖rres α x k + gradient f (x (k + 1)) - gradient f (x k)‖ ^ 2
      ≤ 4 * ‖rres α x k‖ ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    nlinarith
  gcongr

/-- **Proposition H2.6, sharpness of the ε-term.** f = 0, g = (σ_g/2)‖·‖² (dom g = whole
space), σ_g > 0, x* = 0, ε ≥ 0, a unit vector e, z = √(2ε/σ_g)e, v = 0: all hypotheses hold
(s = σ_g), u = 0, and the bound is attained: ‖z − x*‖ = (‖u‖ + √(‖u‖² + 2sε))/s. -/
theorem prop_H2_6_sharp {σg ε : ℝ} (hσg : 0 < σg) (hε : 0 ≤ ε) {e : X} (he : ‖e‖ = 1) :
    let f : X → ℝ := fun _ => 0
    let g : X → ℝ := fun w => σg / 2 * ‖w‖ ^ 2
    let z : X := √(2 * ε / σg) • e
    ModC f 0 ∧ ModCD univ g σg ∧ 0 < 2 * 0 + σg ∧
    EpsSubgrad univ g 0 0 (-gradient f 0) ∧ EpsSubgrad univ g ε z 0 ∧
    gradient f z + 0 = 0 ∧
    ‖z - 0‖ = (‖gradient f z + 0‖ + √(‖gradient f z + 0‖ ^ 2 + 2 * (2 * 0 + σg) * ε))
      / (2 * 0 + σg) := by
  intro f g z
  have hgrad : ∀ y, gradient f y = 0 := fun y => gradient_fun_const y 0
  refine ⟨?_, ?_, by linarith, ?_, ?_, ?_, ?_⟩
  · unfold ModC; simp only [f, zero_div, zero_mul, sub_zero]; exact convexOn_const 0 convex_univ
  · unfold ModCD; simp only [g, sub_self]; exact convexOn_const 0 convex_univ
  · refine ⟨mem_univ _, fun w _ => ?_⟩
    simp only [g, hgrad, neg_zero, inner_zero_left, norm_zero, sub_zero]
    norm_num; positivity
  · refine ⟨mem_univ _, fun w _ => ?_⟩
    simp only [g, z, inner_zero_left, add_zero, norm_smul, he, mul_one,
      Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [Real.sq_sqrt (by positivity)]
    have : σg / 2 * (2 * ε / σg) = ε := by field_simp
    rw [this]; simp only [sub_self]; positivity
  · rw [hgrad, add_zero]
  · rw [hgrad, add_zero, norm_zero, sub_zero]
    simp only [z, norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    rw [show (0 : ℝ) ^ 2 = 0 by norm_num, zero_add, zero_add, mul_zero, zero_add]
    rw [eq_div_iff hσg.ne']
    rw [show 2 * σg * ε = σg ^ 2 * (2 * ε / σg) by field_simp, Real.sqrt_mul (sq_nonneg _),
      Real.sqrt_sq hσg.le]
    ring

/-! ## Sharpness instances: the half-space indicator (Lemma H2.2(d), (E1), (E4)(b), (E5)(c)(ii),
Proposition H2.7(b),(c)) and the quadratic pair ((E5)(c)(i)) -/

/-- The quadratic (σ/2)‖·‖². -/
noncomputable def sqf (σ : ℝ) : X → ℝ := fun x => σ / 2 * ‖x‖ ^ 2

lemma hasGradientAt_sqf (σ : ℝ) (x : X) : HasGradientAt (sqf σ) (σ • x) x := by
  have h := hasGradientAt_sub_sq (f := fun _ : X => (0 : ℝ)) (x := x)
    (differentiableAt_const 0) (-σ)
  rw [gradient_fun_const, zero_sub, neg_smul, neg_neg] at h
  convert h using 1
  funext y; simp only [sqf]; ring

lemma gradient_sqf (σ : ℝ) (x : X) : gradient (sqf σ) x = σ • x := (hasGradientAt_sqf σ x).gradient

lemma differentiable_sqf (σ : ℝ) : Differentiable ℝ (sqf (X := X) σ) :=
  fun x => (hasGradientAt_sqf σ x).differentiableAt

lemma lipGrad_sqf {σ : ℝ} (hσ : 0 ≤ σ) : LipGrad (sqf (X := X) σ) σ := by
  intro u v
  rw [gradient_sqf, gradient_sqf, ← smul_sub, norm_smul, Real.norm_of_nonneg hσ]

lemma modC_sqf (σ : ℝ) : ModC (sqf (X := X) σ) σ := by
  unfold ModC sqf; simp only [sub_self]; exact convexOn_const 0 convex_univ

lemma modCD_sqf (D : Set X) (hD : Convex ℝ D) (σ : ℝ) : ModCD D (sqf σ) σ := by
  unfold ModCD sqf; simp only [sub_self]; exact convexOn_const 0 hD

/-- The half-space {w : ⟨e, w⟩ ≥ 0} (for e = e₁ in ℝ^d this is [0, ∞) × ℝ^{d−1}). -/
def halfSp (e : X) : Set X := {w | 0 ≤ inner ℝ e w}

/-- **Lemma H2.2(d).** g = ι_{halfspace} (pair (halfSp e, 0)), ‖e‖ = 1, y = 0: the exact
proximal point is p = 0, z = √(αε)e ∈ prox^ε_{αg}(0), and ‖z − p‖ = √(αε). -/
theorem comparison_d {α ε : ℝ} (hα : 0 < α) (hε : 0 ≤ ε) {e : X} (he : ‖e‖ = 1) :
    ProxEps (halfSp e) (fun _ => 0) α 0 0 0 ∧
    ProxEps (halfSp e) (fun _ => 0) α ε 0 (√(α * ε) • e) ∧
    ‖√(α * ε) • e - 0‖ = √(α * ε) := by
  have hee : inner ℝ e e = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, he, one_pow]
  refine ⟨⟨by simp [halfSp], fun w _ => by simp⟩, ⟨?_, fun w hw => ?_⟩, ?_⟩
  · simp only [halfSp, mem_setOf_eq, real_inner_smul_right, hee, mul_one]
    exact Real.sqrt_nonneg _
  · simp only [halfSp, mem_setOf_eq] at hw
    rw [zero_sub, inner_smul_left, inner_neg_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, hee]
    simp only [conj_trivial]
    have hs := Real.mul_self_sqrt (mul_nonneg hα.le hε)
    have h1 : α⁻¹ * (√(α * ε) * (√(α * ε) * 1)) = ε := by
      rw [mul_one, hs]; field_simp
    have h2 : 0 ≤ α⁻¹ * (√(α * ε) * inner ℝ e w) :=
      mul_nonneg (inv_pos.2 hα).le (mul_nonneg (Real.sqrt_nonneg _) hw)
    nlinarith
  · rw [sub_zero, norm_smul, he, mul_one, Real.norm_of_nonneg (Real.sqrt_nonneg _)]

/-- **Sharpness instance** (f = (β/2)‖·‖², g = ι of a half-space, x* = 0, q_A = 0):
* the exact-prox step from any point is 0, and the oracle may answer √(αε)e at accuracy ε;
* (E1) holds with equality at x_k = 0: E(x_{k+1}) = E(x_k) − (α/2)‖r_k‖² + ε;
* (E5)(c)(ii): ‖x_{k+1} − x*‖ = (q_A‖r_k‖ + (1 + 0/β)√(βε))/(β + 0);
* (E4)(b) floor / Proposition H2.7(b): the run x₀ arbitrary, x_k = √(αε)e (k ≥ 1) with
  ε_k ≡ ε is an inexact run, x* = 0 minimises E, and ‖x_k − x*‖ = √(αε) for every k ≥ 1,
  which is the (E4)(b) bound q^k‖x₀ − x*‖ + (1 − q^k)√(αε)/(1 − q) at q = q_A = 0;
* Proposition H2.7(c): an answer te, t > √(αε), reported at accuracy ε violates (E1). -/
theorem halfspace_sharp {α β ε : ℝ} (hα : 0 < α) (hαβ : α * β = 1) (hε : 0 ≤ ε) {e : X}
    (he : ‖e‖ = 1) (x0 : X) :
    let f : X → ℝ := sqf β
    let g : X → ℝ := fun _ => 0
    let D := halfSp e
    let z : X := √(α * ε) • e
    let x : ℕ → X := fun k => if k = 0 then x0 else z
    (∀ y, step f α y = 0) ∧
    ProxEps D g α ε (step f α 0) z ∧
    f z + g z = f 0 + g 0 - α / 2 * ‖α⁻¹ • (0 - z)‖ ^ 2 + ε ∧
    ‖z - 0‖ = (qA β β * ‖α⁻¹ • (0 - z)‖ + (1 + 0 / β) * √(β * ε)) / (β + 0) ∧
    InexactRun f D g α x (fun _ => ε) ∧ (0 : X) ∈ D ∧ (∀ w ∈ D, f 0 + g 0 ≤ f w + g w) ∧
    (∀ k, 1 ≤ k → ‖x k - 0‖ = qA β β ^ k * ‖x 0 - 0‖
        + (1 - qA β β ^ k) * √(α * ε) / (1 - qA β β)) ∧
    (∀ t : ℝ, √(α * ε) < t →
      f 0 + g 0 - α / 2 * ‖α⁻¹ • (0 - t • e)‖ ^ 2 + ε < f (t • e) + g (t • e)) := by
  intro f g D z x
  have hβ : 0 < β := by nlinarith
  have hb : β = α⁻¹ := by field_simp; linarith
  have hstep : ∀ y, step f α y = 0 := by
    intro y; simp only [step, f, gradient_sqf, smul_smul, hαβ, one_smul, sub_self]
  obtain ⟨hp0, hz, hzn⟩ := comparison_d hα hε he
  have hs := Real.mul_self_sqrt (mul_nonneg hα.le hε)
  have hzn' : ‖z‖ = √(α * ε) := by simpa using hzn
  have hzn2 : ‖z‖ ^ 2 = α * ε := by
    rw [hzn', Real.sq_sqrt (mul_nonneg hα.le hε)]
  have hr : ‖α⁻¹ • (0 - z)‖ ^ 2 = β * ε := by
    rw [zero_sub, smul_neg, norm_neg, norm_smul, mul_pow, hzn2,
      Real.norm_of_nonneg (inv_pos.2 hα).le, hb]
    field_simp
  have hqA : qA β β = 0 := by unfold qA; rw [div_self hβ.ne']; ring
  have hmin : ∀ w ∈ D, f 0 + g 0 ≤ f w + g w := by
    intro w _; simp only [f, g, sqf, norm_zero]; norm_num; positivity
  refine ⟨hstep, by rw [hstep]; exact hz, ?_, ?_, ?_, hp0.1, hmin, ?_, ?_⟩
  · simp only [f, g, sqf, norm_zero]
    rw [hzn2, hr]
    linear_combination ε * hαβ
  · rw [hqA, zero_mul, zero_add, zero_div, add_zero, add_zero, one_mul, sub_zero]
    rw [hzn', eq_div_iff hβ.ne', sqrt_alpha hα hαβ]
    linear_combination √(β * ε) * hαβ
  · intro k
    refine ⟨hε, ?_⟩
    rw [hstep]
    simp only [x, show k + 1 ≠ 0 from Nat.succ_ne_zero k, if_false]
    exact hz
  · intro k hk
    simp only [x, show k ≠ 0 by omega, if_false, hqA]
    rw [zero_pow (by omega), zero_mul, zero_add, sub_zero, sub_zero, one_mul, div_one, hzn']
  · intro t ht
    have ht0 : 0 < t := lt_of_le_of_lt (Real.sqrt_nonneg _) ht
    have htt : α * ε < t ^ 2 := by
      have := mul_self_lt_mul_self (Real.sqrt_nonneg _) ht
      rw [hs] at this; nlinarith
    simp only [f, g, sqf, norm_zero, zero_sub, norm_neg, norm_smul, he, mul_one,
      Real.norm_of_nonneg ht0.le, Real.norm_of_nonneg (inv_pos.2 hα).le]
    rw [hb]
    have hβt : ε < β * t ^ 2 := by
      have := mul_lt_mul_of_pos_left htt hβ
      rw [← mul_assoc, mul_comm β α, hαβ, one_mul] at this; exact this
    rw [hb] at hβt
    have : α / 2 * (α⁻¹ * t) ^ 2 = α⁻¹ / 2 * t ^ 2 := by field_simp
    rw [this]
    nlinarith

/-- **(E5)(c)(i).** Equality in (E5)(b) at ε_k = 0 for f = (σ_f/2)‖·‖², g = (σ_g/2)‖·‖²
(dom g the whole space), 0 < σ_f ≤ β, σ_g ≥ 0, every x_k: the hypotheses of (E5)(b) hold
(with P(y) = y/(1 + ασ_g) the exact proximal map and x* = 0), and
‖x_{k+1} − x*‖ = (q_A‖r_k‖ + (1 + σ_g/β)√(β·0))/(σ_f + σ_g) for x_{k+1} = P(x_k − α∇f(x_k)). -/
theorem quadratic_sharp {α β σf σg : ℝ} (hα : 0 < α) (hαβ : α * β = 1) (hσf : 0 < σf)
    (hσfβ : σf ≤ β) (hσg : 0 ≤ σg) (x : X) :
    let f : X → ℝ := sqf σf
    let g : X → ℝ := sqf σg
    let P : X → X := fun y => (1 + α * σg)⁻¹ • y
    LipGrad f β ∧ ModC f σf ∧ ModCD univ g σg ∧ (∀ y, ProxEps univ g α 0 y (P y)) ∧
    (∀ w, f 0 + g 0 ≤ f w + g w) ∧
    ‖P (step f α x) - 0‖
      = (qA β σf * ‖α⁻¹ • (x - P (step f α x))‖ + (1 + σg / β) * √(β * 0)) / (σf + σg) := by
  intro f g P
  have hβ : 0 < β := by nlinarith
  have hb : β = α⁻¹ := by field_simp; linarith
  have hc0 : 0 < 1 + α * σg := by positivity
  refine ⟨?_, modC_sqf σf, modCD_sqf univ convex_univ σg, ?_, ?_, ?_⟩
  · intro u v
    rw [gradient_sqf, gradient_sqf, ← smul_sub, norm_smul, Real.norm_of_nonneg hσf.le]
    exact mul_le_mul_of_nonneg_right hσfβ (norm_nonneg _)
  · intro y
    refine ⟨mem_univ _, fun w _ => ?_⟩
    have hv : α⁻¹ • (y - P y) = σg • P y := by
      simp only [P, smul_smul]
      rw [show y - (1 + α * σg)⁻¹ • y = (1 - (1 + α * σg)⁻¹) • y by rw [sub_smul, one_smul]]
      rw [smul_smul]; congr 1; field_simp; ring
    rw [hv, real_inner_smul_left]
    simp only [g, sqf, sub_zero]
    have hn : ‖w‖ ^ 2 = ‖P y‖ ^ 2 + 2 * inner ℝ (P y) (w - P y) + ‖w - P y‖ ^ 2 := by
      rw [← norm_add_sq_real, add_sub_cancel]
    rw [hn]
    nlinarith [sq_nonneg ‖w - P y‖]
  · intro w; simp only [f, g, sqf, norm_zero]; norm_num; positivity
  · have hstep : step f α x = (1 - α * σf) • x := by
      simp only [step, f, gradient_sqf, smul_smul, sub_smul, one_smul]
    have ha : 0 ≤ 1 - α * σf := by
      have : α * σf ≤ α * β := mul_le_mul_of_nonneg_left hσfβ hα.le
      linarith
    set c := (1 + α * σg)⁻¹ with hc
    have hcpos : 0 < c := inv_pos.2 hc0
    have hPx : P (step f α x) = (c * (1 - α * σf)) • x := by
      simp only [P, hstep, smul_smul, ← hc]
    have h1c : 1 - c * (1 - α * σf) = c * (α * (σf + σg)) := by
      rw [hc]; field_simp; ring
    have hdiff : x - P (step f α x) = (c * (α * (σf + σg))) • x := by
      rw [hPx, ← h1c, sub_smul, one_smul]
    rw [hdiff, hPx, sub_zero, norm_smul, norm_smul, norm_smul, mul_zero, Real.sqrt_zero, mul_zero,
      add_zero, Real.norm_of_nonneg (mul_nonneg hcpos.le ha),
      Real.norm_of_nonneg (inv_pos.2 hα).le,
      Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ c * (α * (σf + σg)))]
    have hqA : qA β σf = 1 - α * σf := by
      unfold qA; rw [hb]; field_simp
    rw [hqA]
    have hμ : σf + σg ≠ 0 := by linarith
    field_simp

end Generic

end OCF.H2

#print axioms OCF.H2.prox_vec_eq
#print axioms OCF.H2.one_step
#print axioms OCF.H2.comparison_a
#print axioms OCF.H2.comparison_b
#print axioms OCF.H2.comparison_c
#print axioms OCF.H2.comparison_d
#print axioms OCF.H2.comparison_e
#print axioms OCF.H2.exact_case
#print axioms OCF.H2.descent_of_mem
#print axioms OCF.H2.E1_descent
#print axioms OCF.H2.E2a_summed
#print axioms OCF.H2.E2a_summed_inf
#print axioms OCF.H2.E2b_limits
#print axioms OCF.H2.E2c_stationary
#print axioms OCF.H2.E2d_u
#print axioms OCF.H2.E2d_convex
#print axioms OCF.H2.E3a
#print axioms OCF.H2.E3b_sum
#print axioms OCF.H2.E3b_min
#print axioms OCF.H2.E3c_last
#print axioms OCF.H2.quasi_fejer
#print axioms OCF.H2.E3d_converge
#print axioms OCF.H2.strong_of_subgrad
#print axioms OCF.H2.fermat_strong
#print axioms OCF.H2.fermat
#print axioms OCF.H2.min_of_stationary
#print axioms OCF.H2.prox_lip
#print axioms OCF.H2.T_contract
#print axioms OCF.H2.regime_contract
#print axioms OCF.H2.unroll
#print axioms OCF.H2.E4a
#print axioms OCF.H2.E4b
#print axioms OCF.H2.E4b_regimeA_const
#print axioms OCF.H2.sum_eq_sk
#print axioms OCF.H2.E4c
#print axioms OCF.H2.eventual_bound
#print axioms OCF.H2.E4d_tendsto
#print axioms OCF.H2.E4d_limsup_of_le
#print axioms OCF.H2.E4d_limsup
#print axioms OCF.H2.E5a_resid
#print axioms OCF.H2.dist_le_of_contract
#print axioms OCF.H2.E5a_regimeA
#print axioms OCF.H2.E5a_regimeB
#print axioms OCF.H2.strong_E_at
#print axioms OCF.H2.E5a_regimeC
#print axioms OCF.H2.E5b_returned
#print axioms OCF.H2.prop_H2_6
#print axioms OCF.H2.prop_H2_6_run
#print axioms OCF.H2.prop_H2_6_sharp
#print axioms OCF.H2.halfspace_sharp
#print axioms OCF.H2.quadratic_sharp

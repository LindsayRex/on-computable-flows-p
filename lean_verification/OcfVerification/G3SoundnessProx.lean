/-
G3 (Soundness of forward–backward typing), one non-smooth term — Theorem G3.1 (landing
label thm:soundness) restricted to the fragment |N| = 1, c = 1 (no frame slot): the
forward–backward iteration x_{k+1} = prox_{αg}(x_k − α∇F(x_k)), α = 1/β̂, constructed from
a valid declaration with one prox term, and the clauses (S0), (S1), (S4) (both cases),
(S5A), (S5B) and (S7) for that case.

Source of truth: project_plan/done/proof_audits/G3_soundness/01_derivation.md (sha16 of
sha256 when formalised: 7f2348850770a5ad), §1 Definition G3.0 (S1.1, S1.4), §2 Theorem G3.1,
§3 (P0.1–P0.5, clause table, glue S1a, S4, S5a, S5b, S7); landing drafts
04_landing_draft_a.tex (def:fb-iteration, thm:soundness, glue (G1)–(G3)) and 03_adjudication.md.
Companion file: G3SoundnessQuadratic.lean (fragment N = ∅), whose definitions are reused.

FRAGMENT. N = {j}, W_j void, so c = 1, f = F = Σ w_if_i, g = g_j, E_c = E = F + g, β = β̂,
α = 1/β̂, σ_f = σ_𝔈^T, σ_g′ = σ_g, μ̂(T) = σ_𝔈^T + σ_g. The non-lift exclusion (H-nl) is not
needed: every statement holds for every non-smooth term meeting the hypotheses below.

DEFINITIONAL MAP (dossier symbol — Lean name):
* ℝᵈ — G3's `Vec d`; d ≥ 1 — `hd : 0 < d`. The generic results (section `Generic`) hold
  in any real Hilbert space `X` (`[Nontrivial X]` where d ≥ 1 is used).
* Smooth part: G3's `Decl`, `Decl.Valid`, `Decl.energy` (F), `Decl.betaHat` (β̂),
  `Decl.sigmaT` (σ_𝔈^T), `Decl.sigmaOf T Δ⁻` (σ_𝔈^{T,−}), `Decl.deltaW` (Δ_w(T)); β-smooth —
  G3's `LipGrad`; C(f, σ) — G3's `ModC`.
* g ∈ Γ₀(ℝᵈ) with dom g — the pair (`NDecl.Dg`, `NDecl.g`): g on Dg, +∞ off Dg (H3's
  convention). C(g, σ_g) — H3's `ExtModC Dg g σ_g` (includes convexity of Dg). v ∈ ∂g(p) —
  H3's `ExtSub Dg g 0 p v` (B&C (16.1)); the σ-strong form `ExtSub Dg g σ p v`.
  Lower semicontinuity and properness beyond dom g ≠ ∅ are never used, so not assumed;
  dom g ≠ ∅ ((O1)) is proved from the prox hypothesis (`O1_of_prox`).
* Non-smooth declaration (g_j, σ_j, π_j, void) — `NDecl` (Dg, g, σg, P); P a y is the output
  of the prox attribute π_j at step a and point y. Validity (landed def:declaration,
  non-smooth term) — `NDecl.Valid`: σ_g ≥ 0, C(g, σ_g), and the prox program returns
  prox_{ag}(y) for every a > 0 and y, entered through the classical characterisation
  [CLASSICAL, hypothesis: Bauschke–Combettes 2017, Def. 12.23 with Prop. 16.44:
  p = prox_{ag}(y) ⟺ (y − p)/a ∈ ∂g(p), for g ∈ Γ₀ — `ProxChar Dg g a (P a)`]. Firm
  nonexpansiveness (B&C Prop. 12.28) and its σ_g-strong version are not separate
  hypotheses: they follow from `ProxChar` and C(g, σ_g) by monotonicity of ∂g, which is the
  content of the cited unit B3 thm:fb(b) second case used by G3 (`prox_lip`).
* T_α, R_α, x_k, k_ε, k₀ — `fbStep F P α` (= P ∘ G3's gradient `step`), `residT T α`
  (= (x − T x)/α), `iterT T x₀ k`, `stopT T α ε x₀` (min{k : ‖R_α(x_k)‖ ≤ ε} as `sInf`; its
  existence is proved before use), `k0 Dg x₀` (0 if x₀ ∈ dom g, else 1).
* Stationary point of E_c (0 ∈ ∇f(x) + ∂g(x)) — `Stationary Dg g f x`.
  x ∈ argmin E_c — `IsArgminC Dg g f x` (x ∈ dom g and f x + g x ≤ f y + g y on dom g).
* q_A = 1 − σ/β̂, q_B = q_A/(1 + σ_g/β̂), κ_B = (1 + σ_g/β̂)/(σ + σ_g) (c = 1) — `qB`, `kappaB`.

COVERAGE (dossier clause — Lean name), all FORMALISED (statement + proof):
* Main theorem: `soundness_prox` (computed Δ⁻ under H-Δ, i.e. including (S7)) and
  `soundness_prox_exact` (Δ⁻ = Δ_w(T)), concluding `ProxConclusions`.
* Validity of β̂, σ_𝔈^T, σ_𝔈^{T,−} (P0.1 at c = 1): from G3's `Decl.betaHat_valid`,
  `Decl.sigmaT_valid`, `Decl.sigmaOf_valid`.
* (G1)/P0.5, modulus of E_c: C(E_c, μ̂⁻) — `extModC_energy` (convex on dom g).
* (S0): T_α single-valued (a function) and x_k ∈ dom g for k ≥ 1 (`fbStep_mem`); (O1)
  (`O1_of_prox`); Fix T_α = zer R_α (`fix_iff_resid_zero`) = stationary points
  (`fix_iff_stationary`); if σ_𝔈^{T,−} ≥ 0 they are exactly argmin E_c
  (`stationary_iff_argmin`); if μ̂⁻ > 0, argmin E_c has at most one point
  (`argmin_subsingleton`), and every minimiser is stationary (`stationary_of_argmin`).
* (S1): E_c(x_{k+1}) ≤ E_c(x_k) − (α/2)‖R_α(x_k)‖² for every k ≥ k₀ (`fb_descent`).
* (S4A)+(S5A): `RegimeAP` from `regimeAP_of` — σ ≤ β̂, argmin E_c = {x*}, ‖x_k − x*‖ ≤ q_A^k‖x₀ − x*‖,
  ‖x − x*‖ ≤ ‖R_α(x)‖/σ, k_ε exists, ‖x_{k_ε} − x*‖ ≤ ε/σ, k_ε = 0 if ‖R_α(x₀)‖ ≤ ε,
  k_ε ≤ 1 if σ = β̂, k_ε ≤ max{0, ⌈log((2β̂/σ − 1)‖R_α(x₀)‖/ε)/log(β̂/(β̂ − σ))⌉} if σ < β̂.
* (S4B)+(S5B): `RegimeBP` from `regimeBP_of` — for σ ≥ 0 and σ_g > 0: σ ≤ β̂, argmin E_c = {x*},
  ‖x_k − x*‖ ≤ q_B^k‖x₀ − x*‖, ‖x − x*‖ ≤ κ_B‖R_α(x)‖, k_ε exists and ‖x_{k_ε} − x*‖ ≤ κ_Bε.
* (S7): every clause above is stated with the computed σ_𝔈^{T,−} (and μ̂⁻ = σ_𝔈^{T,−} + σ_g),
  in the constants and the regime conditions alike, under H-Δ (Δ⁻ ≤ Δ_w(T)); plus downward
  closure (every σ′ below a valid number also certifies regimes A and B).
* Generic pieces: `prox_lip` ((1 + ασ_g)‖P u − P u′‖ ≤ ‖u − u′‖), `fb_contract` (T_α is
  q_B-Lipschitz at α = 1/β), `contr_core` (fixed point, rate, residual decay and bracket
  ‖x − x*‖ ≤ α/(1 − q)‖R_α(x)‖ for any q-Lipschitz map, q < 1), `extSub_strongMono`.
* Non-vacuity: `NDecl.zero_valid` (g = 0, dom g = ℝᵈ, prox = identity is a valid declaration).

STRENGTHENINGS (none weakens the dossier statement): (S1) is proved without (O2) (the
dossier carries (O2) only because B3 states thm:fb(c) under it; inconsistency X5); the prox
hypothesis is needed only at the step α = 1/β̂, but is stated for every a > 0 as validity
of the declared prox attribute requires; lower semicontinuity of g is not assumed; (H-nl)
is not assumed.

NOT FORMALISED (remain audited prose or classical): (S2) (summed residual, limit points,
k_ε and the count under (O-low), stationarity residual 2ε); (S3a) (convergence for σ ≥ 0
with (O3), value rate); (S3b) and (S5C) (κ_C bound and convergence in regime C; existence
of the minimiser there needs B&C Cor. 11.17 for the strongly convex Γ₀ function E_c, which
is not entered here — `argmin_subsingleton` gives the uniqueness half); (S5D); (S6)
instruction counts; the certificate packaging of (S5) (def:certificate); frame slots c ≠ 1
(lem:rule-frame(a), lem:conj-lifted) and non-lifted conjugates (Corollary G3.3);
Corollary G3.2 for N ≠ ∅; Proposition G3.4; Remarks G3.5–G3.9; |N| ≥ 2 (not typed).
(S0)'s phrase "argmin E_c = c⁻¹ argmin E" is trivial at c = 1 (E_c = E by definition).

STATUS: COMPLETE. Status tier: FORMALISED (statement + proof, no sorry) for the fragment
|N| = 1, c = 1: validity of β̂, σ_𝔈^T, σ_𝔈^{T,−}; (G1); (S0); (S1); (S4A); (S4B); (S5A);
(S5B); (S7). Classical input entered as hypothesis: the prox characterisation
(B&C Def. 12.23 + Prop. 16.44). Axioms: only propext, Classical.choice, Quot.sound.
-/
import Mathlib
import OcfVerification.G3SoundnessQuadratic
import OcfVerification.H3MultiNonsmooth

namespace OCF.G3P

open Set Filter Topology OCF.A1 OCF.G3 OCF.H3

set_option linter.unusedSectionVars false

section Generic

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The prox program `P` realises prox_{αg} for g (= `g` on `Dg`, +∞ off `Dg`), entered by
the classical characterisation [B&C Def. 12.23 with Prop. 16.44]:
`P y = q ⟺ (y − q)/α ∈ ∂g(q)`. -/
def ProxChar (Dg : Set X) (g : X → ℝ) (α : ℝ) (P : X → X) : Prop :=
  ∀ y q, P y = q ↔ ExtSub Dg g 0 q (α⁻¹ • (y - q))

/-- The forward–backward map T_α = prox_{αg} ∘ (Id − α∇f), the prox realised by `P`. -/
noncomputable def fbStep (f : X → ℝ) (P : X → X) (α : ℝ) (x : X) : X := P (step f α x)

/-- The residual of a map T at step α: R_α(x) = (x − T x)/α. -/
noncomputable def residT (T : X → X) (α : ℝ) (x : X) : X := α⁻¹ • (x - T x)

/-- The iterates x_k = T^k x₀. -/
noncomputable def iterT (T : X → X) (x₀ : X) (k : ℕ) : X := T^[k] x₀

/-- The stopping index k_ε = min{k ≥ 0 : ‖R_α(x_k)‖ ≤ ε} (used only once nonempty). -/
noncomputable def stopT (T : X → X) (α ε : ℝ) (x₀ : X) : ℕ :=
  sInf {k | ‖residT T α (iterT T x₀ k)‖ ≤ ε}

/-- The index shift k₀: 0 if x₀ ∈ dom g, 1 otherwise. -/
noncomputable def k0 (Dg : Set X) (x₀ : X) : ℕ := by
  classical exact if x₀ ∈ Dg then 0 else 1

/-- x is a stationary point of f + g: 0 ∈ ∇f(x) + ∂g(x). -/
def Stationary (Dg : Set X) (g f : X → ℝ) (x : X) : Prop :=
  ∃ v, ExtSub Dg g 0 x v ∧ gradient f x + v = 0

/-- x ∈ argmin (f + g), g = +∞ off `Dg`. -/
def IsArgminC (Dg : Set X) (g f : X → ℝ) (x : X) : Prop :=
  x ∈ Dg ∧ ∀ y ∈ Dg, f x + g x ≤ f y + g y

/-- q_B = q_A/(1 + σ_g/β), q_A = 1 − σ/β. -/
noncomputable def qB (β σ σg : ℝ) : ℝ := (1 - σ / β) / (1 + σg / β)

/-- κ_B = (1 + σ_g/β)/(σ + σ_g) (c = 1). -/
noncomputable def kappaB (β σ σg : ℝ) : ℝ := (1 + σg / β) / (σ + σg)

lemma iterT_succ (T : X → X) (x₀ : X) (k : ℕ) : iterT T x₀ (k + 1) = T (iterT T x₀ k) := by
  simp [iterT, Function.iterate_succ_apply']

variable {Dg : Set X} {g : X → ℝ} {f : X → ℝ} {P : X → X} {α : ℝ}

/-- Two σ-strong subgradients are σ-strongly monotone. -/
lemma extSub_strongMono {σ : ℝ} {p p' v v' : X} (h : ExtSub Dg g σ p v)
    (h' : ExtSub Dg g σ p' v') : σ * ‖p - p'‖ ^ 2 ≤ inner ℝ (v - v') (p - p') := by
  have a := h.2 p' h'.1
  have b := h'.2 p h.1
  rw [norm_sub_rev p' p] at a
  have e1 : inner ℝ v (p' - p) = - inner ℝ v (p - p') := by rw [← inner_neg_right, neg_sub]
  rw [e1] at a
  rw [inner_sub_left]
  linarith

/-- The prox output is a subgradient read-out: (x − α∇f x − T x)/α = R_α(x) − ∇f(x) ∈ ∂g(T x). -/
lemma fbStep_sub (hP : ProxChar Dg g α P) (hα : α ≠ 0) (x : X) :
    ExtSub Dg g 0 (fbStep f P α x) (residT (fbStep f P α) α x - gradient f x) := by
  have h := (hP (step f α x) (fbStep f P α x)).1 rfl
  have e : α⁻¹ • (step f α x - fbStep f P α x)
      = residT (fbStep f P α) α x - gradient f x := by
    simp only [residT, step, smul_sub, smul_smul, inv_mul_cancel₀ hα, one_smul]
    abel
  rwa [e] at h

/-- (S0): x_k ∈ dom g for k ≥ 1 — every value of T_α lies in dom g. -/
lemma fbStep_mem (hP : ProxChar Dg g α P) (hα : α ≠ 0) (x : X) : fbStep f P α x ∈ Dg :=
  (fbStep_sub hP hα x).1

/-- (S0), (O1): dom g ≠ ∅. -/
lemma O1_of_prox (hP : ProxChar Dg g α P) : Dg.Nonempty :=
  ⟨P 0, ((hP 0 (P 0)).1 rfl).1⟩

/-- (S0): Fix T_α = zer R_α. -/
lemma fix_iff_resid_zero (T : X → X) (hα : α ≠ 0) (x : X) : T x = x ↔ residT T α x = 0 := by
  rw [residT, smul_eq_zero, sub_eq_zero]
  constructor
  · intro h; right; exact h.symm
  · rintro (h | h)
    · exact absurd h (inv_ne_zero hα)
    · exact h.symm

/-- (S0): Fix T_α = the stationary points of f + g. -/
lemma fix_iff_stationary (hP : ProxChar Dg g α P) (hα : α ≠ 0) (x : X) :
    fbStep f P α x = x ↔ Stationary Dg g f x := by
  rw [fbStep, hP]
  have e : α⁻¹ • (step f α x - x) = -gradient f x := by
    simp only [step, sub_sub_cancel_left, smul_neg, smul_smul, inv_mul_cancel₀ hα, one_smul]
  rw [e]
  constructor
  · intro h; exact ⟨_, h, by abel⟩
  · rintro ⟨v, hv, hsum⟩
    have : v = -gradient f x := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
    rwa [this] at hv

/-- (S1) at α = 1/β: for x ∈ dom g, (f + g)(T x) ≤ (f + g)(x) − (α/2)‖R_α(x)‖²
(B3 thm:fb(c)(i) at α = 1/β; factor α(2 − αβ)/2 = α/2). No (O2) needed. -/
theorem fb_descent {β : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β) (hβ : 0 < β)
    (hP : ProxChar Dg g (1 / β) P) {x : X} (hx : x ∈ Dg) :
    f (fbStep f P (1 / β) x) + g (fbStep f P (1 / β) x)
      ≤ f x + g x - (1 / β) / 2 * ‖residT (fbStep f P (1 / β)) (1 / β) x‖ ^ 2 := by
  have hα : (1 / β) ≠ 0 := by positivity
  set p := fbStep f P (1 / β) x with hp
  set R := residT (fbStep f P (1 / β)) (1 / β) x with hR
  have hs := fbStep_sub (f := f) hP hα x
  rw [← hp, ← hR] at hs
  have h1 := hs.2 x hx
  have h2 := upper_bound hf hL x p
  have hRd : R = β • (x - p) := by
    rw [hR, hp, residT, one_div, inv_inv]
  have hn : ‖R‖ ^ 2 = β ^ 2 * ‖x - p‖ ^ 2 := by
    rw [hRd, norm_smul, Real.norm_of_nonneg hβ.le, mul_pow]
  have hi : inner ℝ (R - gradient f x) (x - p)
      = β * ‖x - p‖ ^ 2 - inner ℝ (gradient f x) (x - p) := by
    rw [inner_sub_left, hRd, real_inner_smul_left, real_inner_self_eq_norm_sq]
  have hi2 : inner ℝ (gradient f x) (p - x) = - inner ℝ (gradient f x) (x - p) := by
    rw [← inner_neg_right, neg_sub]
  have hn2 : ‖p - x‖ = ‖x - p‖ := norm_sub_rev p x
  rw [hi] at h1
  rw [hi2, hn2] at h2
  rw [hn]
  have : 1 / β / 2 * (β ^ 2 * ‖x - p‖ ^ 2) = β / 2 * ‖x - p‖ ^ 2 := by field_simp
  rw [this]
  simp only [zero_div, zero_mul, add_zero] at h1
  linarith

/-- The σ_g-strong prox bound: (1 + ασ_g)‖P u − P u′‖ ≤ ‖u − u′‖ (B3 thm:fb(b), second case,
its prox half; σ_g = 0 is nonexpansiveness). -/
theorem prox_lip (hP : ProxChar Dg g α P) (hα : 0 < α) {σg : ℝ} (hC : ExtModC Dg g σg)
    (u u' : X) : (1 + α * σg) * ‖P u - P u'‖ ≤ ‖u - u'‖ := by
  have h := extSub_strong hC ((hP u (P u)).1 rfl)
  have h' := extSub_strong hC ((hP u' (P u')).1 rfl)
  have hm := extSub_strongMono h h'
  set dp := P u - P u' with hdp
  have e : α⁻¹ • (u - P u) - α⁻¹ • (u' - P u') = α⁻¹ • ((u - u') - dp) := by
    rw [← smul_sub, hdp]; congr 1; abel
  rw [e, real_inner_smul_left, inner_sub_left, real_inner_self_eq_norm_sq] at hm
  have hcs := real_inner_le_norm (u - u') dp
  have hm' : α * σg * ‖dp‖ ^ 2 ≤ inner ℝ (u - u') dp - ‖dp‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_left hm hα.le
    have e2 : α * (α⁻¹ * (inner ℝ (u - u') dp - ‖dp‖ ^ 2)) = inner ℝ (u - u') dp - ‖dp‖ ^ 2 := by
      field_simp
    rw [e2] at this
    linarith
  rcases eq_or_lt_of_le (norm_nonneg dp) with h0 | hpos
  · rw [← h0, mul_zero]; exact norm_nonneg _
  · have : (1 + α * σg) * ‖dp‖ * ‖dp‖ ≤ ‖u - u'‖ * ‖dp‖ := by nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- T_α at α = 1/β is q_B-Lipschitz under C(f, σ), σ ≤ β, C(g, σ_g), σ_g ≥ 0
(B3 thm:fb(b) at α = 1/β: q = q_A/(1 + ασ_g′)). -/
theorem fb_contract {β σ σg : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β) (hβ : 0 < β)
    (hσ : ModC f σ) (hσβ : σ ≤ β) (hP : ProxChar Dg g (1 / β) P) (hσg : 0 ≤ σg)
    (hC : ExtModC Dg g σg) (x y : X) :
    ‖fbStep f P (1 / β) x - fbStep f P (1 / β) y‖ ≤ qB β σ σg * ‖x - y‖ := by
  have h1 := prox_lip hP (by positivity : (0 : ℝ) < 1 / β) hC (step f (1 / β) x)
    (step f (1 / β) y)
  have h2 := step_contract hf hL hβ hσ hσβ x y
  have hpos : 0 < 1 + σg / β := by positivity
  rw [qB, div_mul_eq_mul_div, le_div_iff₀ hpos]
  have e : 1 / β * σg = σg / β := by ring
  rw [e] at h1
  simp only [fbStep]
  nlinarith [norm_nonneg (P (step f (1 / β) x) - P (step f (1 / β) y))]

lemma qB_nonneg {β σ σg : ℝ} (hβ : 0 < β) (hσβ : σ ≤ β) (hσg : 0 ≤ σg) : 0 ≤ qB β σ σg := by
  unfold qB
  have : 0 ≤ 1 - σ / β := by rw [sub_nonneg, div_le_one hβ]; exact hσβ
  positivity

lemma qB_le_qA {β σ σg : ℝ} (hβ : 0 < β) (hσβ : σ ≤ β) (hσg : 0 ≤ σg) :
    qB β σ σg ≤ 1 - σ / β := by
  unfold qB
  have h0 : 0 ≤ 1 - σ / β := by rw [sub_nonneg, div_le_one hβ]; exact hσβ
  rw [div_le_iff₀ (by positivity)]
  have : 0 ≤ σg / β := by positivity
  nlinarith

lemma qB_lt_one {β σ σg : ℝ} (hβ : 0 < β) (hσ : 0 ≤ σ) (hσg : 0 < σg) : qB β σ σg < 1 := by
  unfold qB
  rw [div_lt_one (by positivity)]
  have : 0 ≤ σ / β := by positivity
  have : 0 < σg / β := by positivity
  linarith

/-- The facts every q-Lipschitz map with q < 1 provides: a unique fixed point x*, the rate
q^k, residual decay, and the bracket (1 − q)‖x − x*‖ ≤ α‖R_α(x)‖. -/
structure ContrData (T : X → X) (α q : ℝ) (xs : X) : Prop where
  fix : T xs = xs
  uniq : ∀ y, T y = y → y = xs
  rate : ∀ x₀ k, ‖iterT T x₀ k - xs‖ ≤ q ^ k * ‖x₀ - xs‖
  rdec : ∀ x₀ k, ‖residT T α (iterT T x₀ k)‖ ≤ q ^ k * ‖residT T α x₀‖
  bracket : ∀ x, (1 - q) * ‖x - xs‖ ≤ α * ‖residT T α x‖

theorem contr_core {T : X → X} {q : ℝ} (hα : 0 < α) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hT : ∀ x y, ‖T x - T y‖ ≤ q * ‖x - y‖) : ∃ xs, ContrData T α q xs := by
  have hlip : LipschitzWith (Real.toNNReal q) T := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hq0]
    exact hT x y
  have hK : Real.toNNReal q < 1 := by rw [Real.toNNReal_lt_one]; exact hq1
  have hcon : ContractingWith (Real.toNNReal q) T := ⟨hK, hlip⟩
  haveI : Nonempty X := ⟨0⟩
  set xs := ContractingWith.fixedPoint T hcon with hxs
  have hfix : T xs = xs := ContractingWith.fixedPoint_isFixedPt (f := T) hcon
  have hres : ∀ x, ‖residT T α (T x)‖ ≤ q * ‖residT T α x‖ := by
    intro x
    simp only [residT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hα.le)]
    have := hT x (T x)
    have hi : 0 ≤ α⁻¹ := inv_nonneg.2 hα.le
    calc α⁻¹ * ‖T x - T (T x)‖ ≤ α⁻¹ * (q * ‖x - T x‖) := mul_le_mul_of_nonneg_left this hi
      _ = q * (α⁻¹ * ‖x - T x‖) := by ring
  refine ⟨xs, ⟨hfix, fun y hy => ContractingWith.fixedPoint_unique hcon hy, ?_, ?_, ?_⟩⟩
  · intro x₀ k
    induction k with
    | zero => simp [iterT]
    | succ k ih =>
      rw [iterT_succ]
      calc ‖T (iterT T x₀ k) - xs‖ = ‖T (iterT T x₀ k) - T xs‖ := by rw [hfix]
        _ ≤ q * ‖iterT T x₀ k - xs‖ := hT _ _
        _ ≤ q * (q ^ k * ‖x₀ - xs‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * ‖x₀ - xs‖ := by ring
  · intro x₀ k
    induction k with
    | zero => simp [iterT]
    | succ k ih =>
      rw [iterT_succ]
      calc ‖residT T α (T (iterT T x₀ k))‖ ≤ q * ‖residT T α (iterT T x₀ k)‖ := hres _
        _ ≤ q * (q ^ k * ‖residT T α x₀‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * ‖residT T α x₀‖ := by ring
  · intro x
    have h1 : ‖x - xs‖ ≤ ‖x - T x‖ + ‖T x - T xs‖ := by
      rw [hfix]; exact norm_sub_le_norm_sub_add_norm_sub x (T x) xs
    have h2 := hT x xs
    have h3 : α * ‖residT T α x‖ = ‖x - T x‖ := by
      rw [residT, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hα.le), ← mul_assoc,
        mul_inv_cancel₀ hα.ne', one_mul]
    rw [h3]
    linarith

/-- The conclusions of regime A for the forward–backward map (clauses (S4A), (S5A) at c = 1,
α = 1/β, curvature number σ), with argmin of f + g on dom g. -/
def RegimeAP (Dg : Set X) (g f : X → ℝ) (P : X → X) (β σ : ℝ) : Prop :=
  σ ≤ β ∧ ∃ xs : X, {x | IsArgminC Dg g f x} = {xs} ∧
    (∀ x₀ : X, ∀ k : ℕ, ‖iterT (fbStep f P (1 / β)) x₀ k - xs‖ ≤ (1 - σ / β) ^ k * ‖x₀ - xs‖) ∧
    (∀ x : X, ‖x - xs‖ ≤ ‖residT (fbStep f P (1 / β)) (1 / β) x‖ / σ) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x₀ : X,
      (∃ k, ‖residT (fbStep f P (1 / β)) (1 / β) (iterT (fbStep f P (1 / β)) x₀ k)‖ ≤ ε) ∧
      ‖iterT (fbStep f P (1 / β)) x₀ (stopT (fbStep f P (1 / β)) (1 / β) ε x₀) - xs‖ ≤ ε / σ ∧
      (‖residT (fbStep f P (1 / β)) (1 / β) x₀‖ ≤ ε →
        stopT (fbStep f P (1 / β)) (1 / β) ε x₀ = 0) ∧
      (σ = β → stopT (fbStep f P (1 / β)) (1 / β) ε x₀ ≤ 1) ∧
      (σ < β → (stopT (fbStep f P (1 / β)) (1 / β) ε x₀ : ℤ) ≤
        max 0 ⌈Real.log ((2 * β / σ - 1) * ‖residT (fbStep f P (1 / β)) (1 / β) x₀‖ / ε)
          / Real.log (β / (β - σ))⌉))

/-- The conclusions of regime B for the forward–backward map (clauses (S4B), (S5B) at c = 1,
α = 1/β): rate q_B, bracket κ_B, existence of k_ε and the distance κ_Bε. -/
def RegimeBP (Dg : Set X) (g f : X → ℝ) (P : X → X) (β σ σg : ℝ) : Prop :=
  σ ≤ β ∧ ∃ xs : X, {x | IsArgminC Dg g f x} = {xs} ∧
    (∀ x₀ : X, ∀ k : ℕ, ‖iterT (fbStep f P (1 / β)) x₀ k - xs‖ ≤ qB β σ σg ^ k * ‖x₀ - xs‖) ∧
    (∀ x : X, ‖x - xs‖ ≤ kappaB β σ σg * ‖residT (fbStep f P (1 / β)) (1 / β) x‖) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x₀ : X,
      (∃ k, ‖residT (fbStep f P (1 / β)) (1 / β) (iterT (fbStep f P (1 / β)) x₀ k)‖ ≤ ε) ∧
      ‖iterT (fbStep f P (1 / β)) x₀ (stopT (fbStep f P (1 / β)) (1 / β) ε x₀) - xs‖
        ≤ kappaB β σ σg * ε)

/-- Stationary points are minimisers when f is convex (C(f, 0)). -/
lemma argmin_of_stationary (hf : Differentiable ℝ f) (hc : ConvexOn ℝ univ f) {x : X}
    (hs : Stationary Dg g f x) : IsArgminC Dg g f x := by
  obtain ⟨v, hv, hsum⟩ := hs
  refine ⟨hv.1, fun y hy => ?_⟩
  have h1 := hv.2 y hy
  have h2 := firstOrder_of_convexOn hf hc x y
  have hv' : v = -gradient f x := by rw [eq_neg_iff_add_eq_zero, add_comm]; exact hsum
  rw [hv', inner_neg_left] at h1
  simp only [zero_div, zero_mul, add_zero] at h1
  linarith

/-- Every minimiser of f + g is a fixed point of T_α at α = 1/β (by the descent (S1)). -/
lemma fix_of_argmin {β : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β) (hβ : 0 < β)
    (hP : ProxChar Dg g (1 / β) P) {y : X} (hy : IsArgminC Dg g f y) :
    fbStep f P (1 / β) y = y := by
  have hα : (1 / β) ≠ 0 := by positivity
  have hd := fb_descent hf hL hβ hP hy.1
  have hle := hy.2 _ (fbStep_mem (f := f) hP hα y)
  have hr0 : ‖residT (fbStep f P (1 / β)) (1 / β) y‖ ^ 2 ≤ 0 := by
    have : 0 < 1 / β / 2 := by positivity
    nlinarith
  have : residT (fbStep f P (1 / β)) (1 / β) y = 0 :=
    norm_eq_zero.1 (by nlinarith [norm_nonneg (residT (fbStep f P (1 / β)) (1 / β) y)])
  exact (fix_iff_resid_zero _ hα y).2 this

/-- (S0): every minimiser of E_c is stationary (no convexity of f needed). -/
lemma stationary_of_argmin {β : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β) (hβ : 0 < β)
    (hP : ProxChar Dg g (1 / β) P) {y : X} (hy : IsArgminC Dg g f y) : Stationary Dg g f y :=
  (fix_iff_stationary hP (by positivity) y).1 (fix_of_argmin hf hL hβ hP hy)

/-- (S0): if σ ≥ 0 (C(f, σ)), the stationary points are exactly argmin E_c. -/
lemma stationary_iff_argmin {β σ : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hP : ProxChar Dg g (1 / β) P) (hσ : ModC f σ) (hσ0 : 0 ≤ σ) (x : X) :
    Stationary Dg g f x ↔ IsArgminC Dg g f x := by
  have hconv : ConvexOn ℝ univ f := by
    have := modC_mono hf hσ hσ0
    unfold ModC at this
    simpa using this
  exact ⟨argmin_of_stationary hf hconv, stationary_of_argmin hf hL hβ hP⟩

/-- (S0)/(S3b) uniqueness half: if μ̂ = σ + σ_g > 0, E_c has at most one minimiser. -/
lemma argmin_subsingleton {β σ σg : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hP : ProxChar Dg g (1 / β) P) (hσ : ModC f σ) (hC : ExtModC Dg g σg)
    (hμ : 0 < σ + σg) {x y : X} (hx : IsArgminC Dg g f x) (hy : IsArgminC Dg g f y) :
    x = y := by
  obtain ⟨v, hv, hvs⟩ := stationary_of_argmin hf hL hβ hP hx
  obtain ⟨v', hv', hvs'⟩ := stationary_of_argmin hf hL hβ hP hy
  have hm := extSub_strongMono (extSub_strong hC hv) (extSub_strong hC hv')
  have hsm := (modC_iff_strongMono hf σ).1 hσ x y
  have e : v - v' = -(gradient f x - gradient f y) := by
    rw [eq_neg_iff_add_eq_zero]
    have : v - v' + (gradient f x - gradient f y) = (gradient f x + v) - (gradient f y + v') := by
      abel
    rw [this, hvs, hvs', sub_zero]
  rw [e, inner_neg_left] at hm
  have : (σ + σg) * ‖x - y‖ ^ 2 ≤ 0 := by linarith
  have h2 : ‖x - y‖ ^ 2 ≤ 0 := by
    by_contra hc
    push Not at hc
    have := mul_pos hμ hc
    linarith
  exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (x - y)]))

/-- argmin E_c = {x*} for the fixed point x* of a contraction T_α, f convex. -/
lemma argmin_eq_of_contr {β σ q : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hP : ProxChar Dg g (1 / β) P) (hσ : ModC f σ) (hσ0 : 0 ≤ σ) {xs : X}
    (hcd : ContrData (fbStep f P (1 / β)) (1 / β) q xs) :
    {x | IsArgminC Dg g f x} = {xs} := by
  ext y
  simp only [mem_setOf_eq, mem_singleton_iff]
  constructor
  · intro hy; exact hcd.uniq y (fix_of_argmin hf hL hβ hP hy)
  · rintro rfl
    exact (stationary_iff_argmin hf hL hβ hP hσ hσ0 _).1
      ((fix_iff_stationary hP (by positivity) _).1 hcd.fix)

/-- **Regime A for the forward–backward map ((S4A), (S5A) at c = 1).** -/
theorem regimeAP_of [Nontrivial X] {β σ σg : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hσ : ModC f σ) (hσpos : 0 < σ) (hP : ProxChar Dg g (1 / β) P)
    (hσg : 0 ≤ σg) (hC : ExtModC Dg g σg) : RegimeAP Dg g f P β σ := by
  have hsm : StrongMono f σ := (modC_iff_strongMono hf σ).1 hσ
  have hσβ : σ ≤ β := le_of_strongMono_lipGrad hsm hL
  set q := 1 - σ / β with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef, sub_nonneg, div_le_one hβ]; exact hσβ
  have hq1 : q < 1 := by rw [hqdef]; have : 0 < σ / β := div_pos hσpos hβ; linarith
  set T := fbStep f P (1 / β) with hT
  have hTl : ∀ x y, ‖T x - T y‖ ≤ q * ‖x - y‖ := fun x y =>
    (fb_contract hf hL hβ hσ hσβ hP hσg hC x y).trans
      (mul_le_mul_of_nonneg_right (qB_le_qA hβ hσβ hσg) (norm_nonneg _))
  obtain ⟨xs, hcd⟩ := contr_core (by positivity : (0 : ℝ) < 1 / β) hq0 hq1 hTl
  have hbr : ∀ x, ‖x - xs‖ ≤ ‖residT T (1 / β) x‖ / σ := by
    intro x
    have h := hcd.bracket x
    rw [hqdef, sub_sub_cancel] at h
    rw [le_div_iff₀ hσpos]
    have e : σ / β * ‖x - xs‖ = (1 / β) * (‖x - xs‖ * σ) := by ring
    rw [e] at h
    exact le_of_mul_le_mul_left h (by positivity)
  refine ⟨hσβ, xs, argmin_eq_of_contr hf hL hβ hP hσ hσpos.le hcd, hcd.rate, hbr, ?_⟩
  intro ε hε x₀
  set S := {k | ‖residT T (1 / β) (iterT T x₀ k)‖ ≤ ε} with hS
  set R₀ := ‖residT T (1 / β) x₀‖ with hR₀
  have h0 : R₀ ≤ ε → 0 ∈ S := fun h => by
    simp only [hS, Set.mem_setOf_eq, iterT, Function.iterate_zero, id]; exact h
  have hcase_eq : σ = β → 1 ∈ S := by
    intro he
    have hq : q = 0 := by rw [hqdef, he, div_self hβ.ne', sub_self]
    have := hcd.rdec x₀ 1
    rw [hq, pow_one, zero_mul] at this
    show ‖residT T (1 / β) (iterT T x₀ 1)‖ ≤ ε
    linarith
  have hcase_lt : σ < β → ε < R₀ → ∃ K : ℕ, (K : ℤ) = max 0
      ⌈Real.log ((2 * β / σ - 1) * R₀ / ε) / Real.log (β / (β - σ))⌉ ∧ K ∈ S := by
    intro hlt hR
    have hqpos : 0 < q := by
      rw [hqdef, sub_pos, div_lt_one hβ]; exact hlt
    have hC1 : 1 ≤ 2 * β / σ - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ hσpos]; linarith
    obtain ⟨K, hKeq, hKb⟩ := count_bound hqpos hq1 hC1 hε hR
    have h1q : 1 / q = β / (β - σ) := by
      rw [hqdef]; field_simp
    rw [h1q] at hKeq
    exact ⟨K, hKeq, (hcd.rdec x₀ K).trans hKb⟩
  have hne : S.Nonempty := by
    by_cases hR : R₀ ≤ ε
    · exact ⟨0, h0 hR⟩
    · rcases eq_or_lt_of_le hσβ with he | hlt
      · exact ⟨1, hcase_eq he⟩
      · obtain ⟨K, -, hK⟩ := hcase_lt hlt (lt_of_not_ge hR)
        exact ⟨K, hK⟩
  have hmem : stopT T (1 / β) ε x₀ ∈ S := Nat.sInf_mem hne
  refine ⟨hne, ?_, ?_, ?_, ?_⟩
  · have := hbr (iterT T x₀ (stopT T (1 / β) ε x₀))
    exact this.trans (div_le_div_of_nonneg_right hmem hσpos.le)
  · intro hR
    exact Nat.eq_zero_of_le_zero (Nat.sInf_le (h0 hR))
  · intro he
    exact Nat.sInf_le (hcase_eq he)
  · intro hlt
    by_cases hR : R₀ ≤ ε
    · have : stopT T (1 / β) ε x₀ = 0 := Nat.eq_zero_of_le_zero (Nat.sInf_le (h0 hR))
      rw [this]; exact le_max_left _ _
    · obtain ⟨K, hKeq, hK⟩ := hcase_lt hlt (lt_of_not_ge hR)
      rw [← hKeq]
      exact_mod_cast Nat.sInf_le hK

/-- **Regime B for the forward–backward map ((S4B), (S5B) at c = 1).** σ ≥ 0, σ_g > 0. -/
theorem regimeBP_of [Nontrivial X] {β σ σg : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hσ : ModC f σ) (hσ0 : 0 ≤ σ) (hP : ProxChar Dg g (1 / β) P)
    (hσg : 0 < σg) (hC : ExtModC Dg g σg) : RegimeBP Dg g f P β σ σg := by
  have hsm : StrongMono f σ := (modC_iff_strongMono hf σ).1 hσ
  have hσβ : σ ≤ β := le_of_strongMono_lipGrad hsm hL
  set q := qB β σ σg with hqdef
  have hq0 : 0 ≤ q := qB_nonneg hβ hσβ hσg.le
  have hq1 : q < 1 := qB_lt_one hβ hσ0 hσg
  set T := fbStep f P (1 / β) with hT
  have hTl : ∀ x y, ‖T x - T y‖ ≤ q * ‖x - y‖ := fb_contract hf hL hβ hσ hσβ hP hσg.le hC
  obtain ⟨xs, hcd⟩ := contr_core (by positivity : (0 : ℝ) < 1 / β) hq0 hq1 hTl
  have hκ : (1 / β) / (1 - q) = kappaB β σ σg := by
    rw [hqdef, qB, kappaB]
    have h1 : 0 < 1 + σg / β := by positivity
    have h2 : 0 < σ + σg := by linarith
    have e1 : 1 - (1 - σ / β) / (1 + σg / β) = ((σ + σg) / β) / (1 + σg / β) := by
      field_simp; ring
    rw [e1]
    field_simp
  have h1q : 0 < 1 - q := by linarith
  have hbr : ∀ x, ‖x - xs‖ ≤ kappaB β σ σg * ‖residT T (1 / β) x‖ := by
    intro x
    rw [← hκ, div_mul_eq_mul_div, le_div_iff₀ h1q]
    have := hcd.bracket x
    linarith
  have hκpos : 0 ≤ kappaB β σ σg := by rw [← hκ]; positivity
  refine ⟨hσβ, xs, argmin_eq_of_contr hf hL hβ hP hσ hσ0 hcd, hcd.rate, hbr, ?_⟩
  intro ε hε x₀
  set S := {k | ‖residT T (1 / β) (iterT T x₀ k)‖ ≤ ε} with hS
  have hne : S.Nonempty := by
    set R₀ := ‖residT T (1 / β) x₀‖
    by_cases hR : R₀ ≤ ε
    · refine ⟨0, ?_⟩
      simp only [hS, Set.mem_setOf_eq, iterT, Function.iterate_zero, id]; exact hR
    · have hR0 : 0 < R₀ := hε.trans (lt_of_not_ge hR)
      rcases eq_or_lt_of_le hq0 with hq | hq
      · refine ⟨1, ?_⟩
        have := hcd.rdec x₀ 1
        rw [← hq, pow_one, zero_mul] at this
        show ‖residT T (1 / β) (iterT T x₀ 1)‖ ≤ ε
        linarith
      · obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one (div_pos hε hR0) hq1
        refine ⟨K, ?_⟩
        have := hcd.rdec x₀ K
        show ‖residT T (1 / β) (iterT T x₀ K)‖ ≤ ε
        have : q ^ K * R₀ ≤ ε := by
          rw [lt_div_iff₀ hR0] at hK; exact hK.le
        linarith
  have hmem : stopT T (1 / β) ε x₀ ∈ S := Nat.sInf_mem hne
  refine ⟨hne, ?_⟩
  exact (hbr _).trans (mul_le_mul_of_nonneg_left hmem hκpos)

end Generic

/-! ### The declaration layer on ℝᵈ: one non-smooth term, c = 1 -/

variable {d n : ℕ}

/-- The non-smooth declaration (g_j, σ_j, π_j, void): g (`g` on `Dg`, +∞ off `Dg`), its
curvature attribute σ_g, and the prox attribute's output `P a y` at step a and point y. -/
structure NDecl (d : ℕ) where
  Dg : Set (Vec d)
  g : Vec d → ℝ
  σg : ℝ
  P : ℝ → Vec d → Vec d

/-- Validity of the non-smooth declaration (landed def:declaration): σ_g ∈ [0, ∞),
C(g, σ_g), and the prox attribute computes prox_{ag} for every a > 0, entered through the
classical characterisation [B&C Def. 12.23 + Prop. 16.44]. -/
structure NDecl.Valid (N : NDecl d) : Prop where
  σg_nonneg : 0 ≤ N.σg
  curv : ExtModC N.Dg N.g N.σg
  prox : ∀ a : ℝ, 0 < a → ProxChar N.Dg N.g a (N.P a)

/-- Non-vacuity: g = 0 on ℝᵈ with σ_g = 0 and the identity as prox is a valid declaration. -/
theorem NDecl.zero_valid :
    NDecl.Valid ({ Dg := univ, g := fun _ => 0, σg := 0, P := fun _ y => y } : NDecl d) := by
  refine ⟨le_rfl, ?_, ?_⟩
  · show ConvexOn ℝ univ (fun x : Vec d => (0 : ℝ) - 0 / 2 * ‖x‖ ^ 2)
    simpa using (convexOn_const (0 : ℝ) convex_univ : ConvexOn ℝ (univ : Set (Vec d)) _)
  · intro a ha y q
    refine proxChar_of_forall ha (P := fun y => y) (fun y => ?_) y q
    refine ⟨mem_univ _, fun z _ => ?_⟩
    simp

/-- The conclusions of Theorem G3.1 at |N| = 1, c = 1, for F = `Ef`, the term g (`g` on
`Dg`, curvature number σ_g = `σg`), the prox program `P` at the step α = 1/β̂, declared β̂,
exact σ_𝔈^T = `σex` and computed σ_𝔈^{T,−} = `σm` (with T = T_α = `fbStep Ef P (1/β̂)`):
* validity: ∇F is β̂-Lipschitz, C(F, σ_𝔈^T), and (S7) C(F, σ_𝔈^{T,−}), σ_𝔈^{T,−} ≤ σ_𝔈^T;
* (G1): C(E_c, μ̂⁻) on dom g, μ̂⁻ = σ_𝔈^{T,−} + σ_g;
* (S0): (O1) dom g ≠ ∅; T_α x ∈ dom g for every x; Fix T_α = zer R_α = stationary points;
  if σ_𝔈^{T,−} ≥ 0 these are exactly argmin E_c; if μ̂⁻ > 0, argmin E_c has at most one point;
* (S1): for every x₀ and every k ≥ k₀: x_k ∈ dom g and
  E_c(x_{k+1}) ≤ E_c(x_k) − (α/2)‖R_α(x_k)‖²;
* (S4A)+(S5A): σ_𝔈^{T,−} > 0 ⇒ `RegimeAP`; (S4B)+(S5B): σ_𝔈^{T,−} ≥ 0, σ_g > 0 ⇒ `RegimeBP`;
* downward closure: every σ′ ∈ (0, σ_𝔈^{T,−}] certifies regime A, every σ′ ∈ [0, σ_𝔈^{T,−}]
  with σ_g > 0 certifies regime B. -/
def ProxConclusions (Ef : Vec d → ℝ) (Dg : Set (Vec d)) (g : Vec d → ℝ) (σg : ℝ)
    (P : Vec d → Vec d) (βh σex σm : ℝ) : Prop :=
  LipGrad Ef βh ∧ ModC Ef σex ∧ ModC Ef σm ∧ σm ≤ σex ∧
  ExtModC Dg (fun x => Ef x + g x) (σm + σg) ∧
  -- (S0)
  Dg.Nonempty ∧
  (∀ x, fbStep Ef P (1 / βh) x ∈ Dg) ∧
  (∀ x, (fbStep Ef P (1 / βh) x = x ↔ residT (fbStep Ef P (1 / βh)) (1 / βh) x = 0) ∧
    (fbStep Ef P (1 / βh) x = x ↔ Stationary Dg g Ef x)) ∧
  (0 ≤ σm → ∀ x, Stationary Dg g Ef x ↔ IsArgminC Dg g Ef x) ∧
  (0 < σm + σg → ∀ x y, IsArgminC Dg g Ef x → IsArgminC Dg g Ef y → x = y) ∧
  -- (S1)
  (∀ x₀ : Vec d, ∀ k : ℕ, k0 Dg x₀ ≤ k →
    iterT (fbStep Ef P (1 / βh)) x₀ k ∈ Dg ∧
    Ef (iterT (fbStep Ef P (1 / βh)) x₀ (k + 1)) + g (iterT (fbStep Ef P (1 / βh)) x₀ (k + 1))
      ≤ Ef (iterT (fbStep Ef P (1 / βh)) x₀ k) + g (iterT (fbStep Ef P (1 / βh)) x₀ k)
        - (1 / βh) / 2 *
          ‖residT (fbStep Ef P (1 / βh)) (1 / βh) (iterT (fbStep Ef P (1 / βh)) x₀ k)‖ ^ 2) ∧
  -- (S4A), (S5A)
  (0 < σm → RegimeAP Dg g Ef P βh σm) ∧
  -- (S4B), (S5B)
  (0 ≤ σm → 0 < σg → RegimeBP Dg g Ef P βh σm σg) ∧
  -- downward closure
  (∀ σ' : ℝ, 0 < σ' → σ' ≤ σm → RegimeAP Dg g Ef P βh σ') ∧
  (∀ σ' : ℝ, 0 ≤ σ' → σ' ≤ σm → 0 < σg → RegimeBP Dg g Ef P βh σ' σg)

/-- (G1)/P0.5: C(F + g, σ + σ_g) on dom g from C(F, σ) and C(g, σ_g)
(sum of two convex functions, B&C Prop. 8.17). -/
lemma extModC_energy {Ef : Vec d → ℝ} {Dg : Set (Vec d)} {g : Vec d → ℝ} {σ σg : ℝ}
    (hF : ModC Ef σ) (hC : ExtModC Dg g σg) :
    ExtModC Dg (fun x => Ef x + g x) (σ + σg) := by
  have h1 : ConvexOn ℝ Dg (fun x => Ef x - σ / 2 * ‖x‖ ^ 2) := hF.subset (subset_univ _) hC.1
  have h2 := h1.add hC
  unfold ExtModC
  have e : (fun x => Ef x + g x - (σ + σg) / 2 * ‖x‖ ^ 2)
      = (fun x => Ef x - σ / 2 * ‖x‖ ^ 2) + (fun x => g x - σg / 2 * ‖x‖ ^ 2) := by
    funext x; simp only [Pi.add_apply]; ring
  rw [e]; exact h2

lemma iterT_mem_of_k0 {T : Vec d → Vec d} {Dg : Set (Vec d)} (hT : ∀ x, T x ∈ Dg)
    (x₀ : Vec d) (k : ℕ) (hk : k0 Dg x₀ ≤ k) : iterT T x₀ k ∈ Dg := by
  rcases k with _ | k
  · classical
    unfold k0 at hk
    split_ifs at hk with h
    · simpa [iterT] using h
    · omega
  · rw [iterT_succ]; exact hT _

/-- **Theorem G3.1, fragment |N| = 1, c = 1, including (S7).** H-dim (d ≥ 1), H-valid
(`D.Valid f`, `N.Valid`), H-FB (β̂ > 0), H-T (T ⊆ S_K), H-Δ (Δ⁻ ≤ Δ_w(T)). The iteration is
x_{k+1} = prox_{αg}(x_k − α∇F(x_k)) with α = 1/β̂, the prox computed by the declared program
`N.P α`. -/
theorem soundness_prox (hd : 0 < d) (D : Decl d n) (f : Fin n → Vec d → ℝ)
    (hv : D.Valid f) (N : NDecl d) (hN : N.Valid) (hFB : 0 < D.betaHat)
    {T : Finset (Fin n)} (hT : T ⊆ D.SK) (Δm : ℝ) (hΔ : Δm ≤ D.deltaW T) :
    ProxConclusions (D.energy f) N.Dg N.g N.σg (N.P (1 / D.betaHat)) D.betaHat
      (D.sigmaT T) (D.sigmaOf T Δm) := by
  haveI := nontrivial_vec hd
  have hE := D.energy_differentiable hv
  have hL := D.betaHat_valid hv
  have hσm := D.sigmaOf_valid hd hv hT hΔ
  have hP := hN.prox (1 / D.betaHat) (by positivity)
  have hα : (1 / D.betaHat) ≠ 0 := by positivity
  refine ⟨hL, D.sigmaT_valid hd hv hT, hσm, D.sigmaOf_le_sigmaT hΔ,
    extModC_energy hσm hN.curv, O1_of_prox hP, fun x => fbStep_mem hP hα x,
    fun x => ⟨fix_iff_resid_zero _ hα x, fix_iff_stationary hP hα x⟩,
    fun h0 x => stationary_iff_argmin hE hL hFB hP hσm h0 x,
    fun hμ x y hx hy => argmin_subsingleton hE hL hFB hP hσm hN.curv hμ hx hy, ?_, ?_, ?_, ?_, ?_⟩
  · intro x₀ k hk
    have hmem := iterT_mem_of_k0 (fun x => fbStep_mem (f := D.energy f) hP hα x) x₀ k hk
    refine ⟨hmem, ?_⟩
    rw [iterT_succ]
    exact fb_descent hE hL hFB hP hmem
  · intro hpos
    exact regimeAP_of hE hL hFB hσm hpos hP hN.σg_nonneg hN.curv
  · intro h0 hg
    exact regimeBP_of hE hL hFB hσm h0 hP hg hN.curv
  · intro σ' hpos hle
    exact regimeAP_of hE hL hFB (modC_mono hE hσm hle) hpos hP hN.σg_nonneg hN.curv
  · intro σ' h0 hle hg
    exact regimeBP_of hE hL hFB (modC_mono hE hσm hle) h0 hP hg hN.curv

/-- The exact form (Δ⁻ := Δ_w(T)) of `soundness_prox`. -/
theorem soundness_prox_exact (hd : 0 < d) (D : Decl d n) (f : Fin n → Vec d → ℝ)
    (hv : D.Valid f) (N : NDecl d) (hN : N.Valid) (hFB : 0 < D.betaHat)
    {T : Finset (Fin n)} (hT : T ⊆ D.SK) :
    ProxConclusions (D.energy f) N.Dg N.g N.σg (N.P (1 / D.betaHat)) D.betaHat
      (D.sigmaT T) (D.sigmaT T) :=
  soundness_prox hd D f hv N hN hFB hT (D.deltaW T) le_rfl

end OCF.G3P

#print axioms OCF.G3P.soundness_prox
#print axioms OCF.G3P.soundness_prox_exact
#print axioms OCF.G3P.regimeAP_of
#print axioms OCF.G3P.regimeBP_of
#print axioms OCF.G3P.fb_descent
#print axioms OCF.G3P.prox_lip
#print axioms OCF.G3P.fb_contract
#print axioms OCF.G3P.contr_core
#print axioms OCF.G3P.argmin_subsingleton
#print axioms OCF.G3P.stationary_iff_argmin
#print axioms OCF.G3P.extModC_energy
#print axioms OCF.G3P.NDecl.zero_valid

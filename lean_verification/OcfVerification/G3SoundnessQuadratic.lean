/-
G3 (Soundness of forward–backward typing) — Theorem G3.1 restricted to the fragment
N = ∅ (no non-smooth term), c = 1 (no frame slot), with energy a weighted sum of
(1) quadratic atoms f_i(x) = ½⟨H_i x, x⟩ − ⟨c_i, x⟩, H_i ⪰ 0 (the "R1 case" of the
spine: E(x) = ½xᵀHx − bᵀx, H = Σ w_iH_i, b = Σ w_ic_i), and, as the extension,
(2) arbitrary C¹ atoms with Lipschitz gradients; plus Corollary G3.2 (G5) for (1).

Source of truth: project_plan/done/proof_audits/G3_soundness/01_derivation.md (stage-1 dossier
edited at stage 3; sha16 7f2348850770a5ad at the time of formalisation, unchanged
by this pass), 03_adjudication.md (section 3 "Formalisation tier", recommendation:
STATEMENT-FORMALISE the N = ∅ fragment and prove (S1), (S4A), (S5A), (S7) for
quadratic atoms; the smooth non-quadratic fragment via Baillon–Haddad), and
01_derivation.md §11 [ADJ] (target fragment N = ∅, c = 1, T_α = gradient step,
R_α = ∇F).

FRAGMENT. N = ∅ gives g = 0, σ_g = 0, π_g = identity, c = 1, so f = F = E,
T_α = Id − α∇E, R_α = ∇E (`resid_eq`), μ̂(T′) = σ_𝔈^{T′}, k₀ = 0, and (O1), (O-x₀),
(O-∂) are automatic. Step α = 1/β̂.

DEFINITIONAL MAP:
* ℝᵈ — `Vec d = EuclideanSpace ℝ (Fin d)`; H-dim (d ≥ 1) — hypothesis `hd : 0 < d`.
  The gradient-step results (`Generic` section) hold in any real Hilbert space.
* β-smooth (landed def:moduli) — `LipGrad f β`: ‖∇f u − ∇f v‖ ≤ β‖u − v‖, with
  `Differentiable ℝ f` (equivalent to f ∈ C¹ with β-Lipschitz ∇f, as in A1).
* C(f, σ) (landed def:moduli) — `ModC f σ`: f − (σ/2)‖·‖² convex on ℝᵈ.
  `modC_iff_strongMono`: ⇔ ⟨∇f x − ∇f y, x − y⟩ ≥ σ‖x − y‖².
* Kernel attribute (K, ν) valid (landed def:kernel-attribute) — `KernelValid`,
  verbatim; K_i is declared through an orthonormal basis `basis i` spanning it
  (T1/B1p convention; every theorem holds for every such basis).
* Declaration (w_i, β_i, σ_i, A_i)_{i∈S}, S = Fin n, A_i = (K_i, ν_i) for i ∈ S_K and
  void otherwise — `Decl`; validity (landed def:energy-spec, smooth part:
  w_i > 0, β_i ∈ [0, ∞), each attribute true) — `Decl.Valid`.
  Representation note: σ_i is real; the "no claim" value σ_i = −∞ of def:energy-spec
  is not a separate value. This loses nothing: C(f_i, −β_i) always holds for a
  β_i-smooth f_i (`modC_neg_of_lipGrad`), and every regime-A certificate holds for every positive number
  below a valid one (last clause of `SoundnessConclusions`). β_i = ∞ is excluded by
  H-FB (β̂ finite).
* E = Σ w_if_i — `Decl.energy`; β̂ = Σ w_iβ_i — `Decl.betaHat`; σ̂_S — `sigmaHatS`.
* Δ_w(T) (exact transversality defect of the Kernel Gram certificate of
  (K_i, w_iν_i)_{i∈T}) — `Decl.deltaW T`: T1SharpBound's `deltaW` on the declared
  bases, T enumerated by `tIdx`; Δ_w(∅) = 0 (`deltaW_card_zero`).
* b(T) at a defect value Δ — `Decl.bOf T Δ` = Δ + Σ_{i∉T} w_iσ_i;
  σ_𝔈 at Δ — `Decl.sigmaOf T Δ` = max{σ̂_S, b}; exact σ_𝔈^T — `Decl.sigmaT T`
  (Δ = Δ_w(T)); computed σ_𝔈^{T,−} — `Decl.sigmaOf T Δ⁻` with H-Δ: Δ⁻ ≤ Δ_w(T).
* T_α, R_α, x_k, k_ε — `step`, `resid` (= (x − T_αx)/α), `iter`, `stopIdx`
  (k_ε = min{k ≥ 0 : ‖R_α(x_k)‖ ≤ ε}, as `sInf`; its existence is proved).
* argmin E = {x*} — `{x | IsMinOn E univ x} = {x*}`.

STATEMENTS FORMALISED:
* Validity of the declared numbers: `Decl.betaHat_valid` (∇E is β̂-Lipschitz),
  `Decl.sigmaT_valid` (C(E, σ_𝔈^T), via B1p's `uniform_composite_gap_of_restricted_monotone`
  on T plus C(f_i, σ_i) off T), `Decl.sigmaOf_valid` (C(E, σ_𝔈^{T,−}) under H-Δ: (S7)).
* Theorem G3.1, fragment, smooth atoms (target 3): `soundness_smooth` (with computed
  Δ⁻, i.e. including (S7)) and `soundness_smooth_exact` (Δ⁻ = Δ_w), concluding
  `SoundnessConclusions`: validity of β̂ and σ_𝔈^T; (S7) C(E, σ_𝔈^{T,−}) and
  σ_𝔈^{T,−} ≤ σ_𝔈^T; (S1) descent E(x_{k+1}) ≤ E(x_k) − (α/2)‖R_α(x_k)‖² for every k;
  in regime A read off the computed number (σ_𝔈^{T,−} > 0) all of `RegimeA`:
  (S4A) σ_𝔈^{T,−} ≤ β̂, argmin E = {x*}, ‖x_k − x*‖ ≤ (1 − σ_𝔈^{T,−}/β̂)^k‖x₀ − x*‖;
  (S5A) ‖x − x*‖ ≤ ‖R_α(x)‖/σ_𝔈^{T,−} for every x, k_ε exists, ‖x_{k_ε} − x*‖ ≤ ε/σ_𝔈^{T,−},
  k_ε = 0 if ‖R_α(x₀)‖ ≤ ε, k_ε ≤ 1 if σ_𝔈^{T,−} = β̂, and
  k_ε ≤ max{0, ⌈log((2β̂/σ − 1)‖R_α(x₀)‖/ε)/log(β̂/(β̂ − σ))⌉} if σ_𝔈^{T,−} < β̂.
* Theorem G3.1, fragment, quadratic atoms (target 1): `soundness_quadratic`, with
  validity in Loewner form (H_i ⪯ β_iI, H_i ⪰ σ_iI, ⟨H_iv, v⟩ ≥ ν_i‖P_{K_i^⊥}v‖²),
  each proved equivalent to the landed validity: `quad_lipGrad_iff` (given H_i ⪰ 0,
  β_i ≥ 0), `quad_modC_iff`, `quad_kernel_iff`; `energy_quad` (E = ½⟨Hx, x⟩ − ⟨b, x⟩,
  H = Σ w_iH_i) and `resid_quad` (R_α(x) = Hx − b).
* Corollary G3.2 (G5), fragment (quadratic atoms): `betaHat_pos_iff` (typed for every
  w > 0 or for none) and `weights_between_runs` (for every w ∈ (0, ∞)^S, every T ⊆ S_K
  and every Δ⁻ ≤ Δ_w(T)(w), all conclusions hold for 𝔈(w)).
* Supporting general lemmas: `cocoercive_of_upper` (Baillon–Haddad from the quadratic
  upper bound, L ≥ 0; B&C Thm 18.15), `step_contract` (the step 1/β is (1 − σ/β)-
  Lipschitz under C(f, σ), σ ≤ β; B3 thm:fb(b) first case at α = 1/β),
  `le_of_strongMono_lipGrad` (σ ≤ β on d ≥ 1), `descent_step` (A1 lem:descent-step
  (a),(c) at α = 1/β), `count_bound` (C2 cor:fb-stop(c) arithmetic).

NOT COVERED (remain audited prose): everything with N ≠ ∅ or c ≠ 1 (prox, Γ₀,
frame slots); (S0) beyond what `RegimeA` gives; (S2) (summed residual, limit points,
k_ε and its count under (O-low) in regime D); (S3a) (convergence for σ_𝔈^T ≥ 0 with
(O3) and the value rate); (S3b)/(S5C) κ_C distance bound (at N = ∅ μ̂(T′) = σ_𝔈^{T′},
so its hypothesis is regime A at T′, which `RegimeA` covers with the sharper 1/σ);
(S4B), (S5B) (vacuous at N = ∅: they need σ_g > 0); (S5D); (S6) instruction counts;
Corollary G3.2 (c)–(e) (prose consequences of (b)); Corollary G3.3; Proposition G3.4;
Remarks G3.5–G3.9 (incl. the Remark G3.6 inertia test).

Status tier: FORMALISED (statement + proof, no sorry) for the fragment N = ∅, c = 1:
validity of β̂ and σ_𝔈^T, (S1), (S4A), (S5A) (bracket, stopping index, distance and
count), (S7), for quadratic atoms and for C¹ atoms with Lipschitz gradients;
Corollary G3.2 (a)–(b) for quadratic atoms.
-/
import Mathlib
import OcfVerification.A1DescentLemma
import OcfVerification.B1pUniformGap

namespace OCF.G3
open Set Filter Topology OCF.A1

section Generic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- "f is β-smooth": ∇f is β-Lipschitz (landed def:moduli). -/
def LipGrad (f : E → ℝ) (β : ℝ) : Prop :=
  ∀ u v, ‖gradient f u - gradient f v‖ ≤ β * ‖u - v‖

/-- The curvature claim C(f, σ): f − (σ/2)‖·‖² is convex (landed def:moduli). -/
def ModC (f : E → ℝ) (σ : ℝ) : Prop :=
  ConvexOn ℝ univ (fun x => f x - σ / 2 * ‖x‖ ^ 2)

/-- σ-strong monotonicity of ∇f (σ any real). -/
def StrongMono (f : E → ℝ) (σ : ℝ) : Prop :=
  ∀ x y, σ * ‖x - y‖ ^ 2 ≤ inner ℝ (gradient f x - gradient f y) (x - y)

/-- The forward–backward map with g = 0: T_α x = x − α∇f(x) (D^{α,I}_f). -/
noncomputable def step (f : E → ℝ) (α : ℝ) (x : E) : E := x - α • gradient f x

/-- The residual R_α(x) = (x − T_α x)/α. -/
noncomputable def resid (f : E → ℝ) (α : ℝ) (x : E) : E := α⁻¹ • (x - step f α x)

/-- The iterates x_k = T_α^k x₀. -/
noncomputable def iter (f : E → ℝ) (α : ℝ) (x₀ : E) (k : ℕ) : E := (step f α)^[k] x₀

/-- The stopping index k_ε = min{k ≥ 0 : ‖R_α(x_k)‖ ≤ ε} (meaningful when the set is
nonempty, which the theorems prove before using it). -/
noncomputable def stopIdx (f : E → ℝ) (α ε : ℝ) (x₀ : E) : ℕ :=
  sInf {k | ‖resid f α (iter f α x₀ k)‖ ≤ ε}

lemma resid_eq (f : E → ℝ) {α : ℝ} (hα : α ≠ 0) (x : E) : resid f α x = gradient f x := by
  simp [resid, step, smul_smul, inv_mul_cancel₀ hα]

lemma iter_succ (f : E → ℝ) (α : ℝ) (x₀ : E) (k : ℕ) :
    iter f α x₀ (k + 1) = step f α (iter f α x₀ k) := by
  simp [iter, Function.iterate_succ_apply']

/-- ∇(f − (σ/2)‖·‖²)(x) = ∇f(x) − σx. -/
lemma hasGradientAt_sub_sq {f : E → ℝ} {x : E} (hf : DifferentiableAt ℝ f x) (σ : ℝ) :
    HasGradientAt (fun x => f x - σ / 2 * ‖x‖ ^ 2) (gradient f x - σ • x) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := hf.hasFDerivAt
  have h2 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (σ / 2)
  refine (h1.sub h2).congr_fderiv ?_
  ext y
  simp only [FunLike.coe_sub, Pi.sub_apply, FunLike.coe_smul, Pi.smul_apply,
    InnerProductSpace.toDual_apply_apply, inner_sub_left, inner_smul_left]
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  simp [innerSL_apply_apply]
  ring

lemma gradient_sub_sq {f : E → ℝ} (hf : Differentiable ℝ f) (σ : ℝ) (x : E) :
    gradient (fun x => f x - σ / 2 * ‖x‖ ^ 2) x = gradient f x - σ • x :=
  (hasGradientAt_sub_sq (hf x) σ).gradient

lemma differentiable_sub_sq {f : E → ℝ} (hf : Differentiable ℝ f) (σ : ℝ) :
    Differentiable ℝ (fun x => f x - σ / 2 * ‖x‖ ^ 2) :=
  fun x => (hasGradientAt_sub_sq (hf x) σ).differentiableAt

/-- C(f, σ) ⇔ σ-strong monotonicity of ∇f (B&C Prop. 17.7 applied to f − (σ/2)‖·‖²). -/
theorem modC_iff_strongMono {f : E → ℝ} (hf : Differentiable ℝ f) (σ : ℝ) :
    ModC f σ ↔ StrongMono f σ := by
  unfold ModC StrongMono
  rw [convexOn_iff_gradMonotone (differentiable_sub_sq hf σ)]
  unfold GradMonotone
  simp only [gradient_sub_sq hf σ]
  constructor
  · intro h x y
    have := h x y
    have e : gradient f x - σ • x - (gradient f y - σ • y)
        = (gradient f x - gradient f y) - σ • (x - y) := by module
    rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at this
    linarith
  · intro h x y
    have := h x y
    have e : gradient f x - σ • x - (gradient f y - σ • y)
        = (gradient f x - gradient f y) - σ • (x - y) := by module
    rw [e, inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    linarith

/-- Downward closure: C(f, σ) and σ' ≤ σ give C(f, σ') (G12 lem:decl-order(b)). -/
theorem modC_mono {f : E → ℝ} (hf : Differentiable ℝ f) {σ σ' : ℝ} (h : ModC f σ)
    (hle : σ' ≤ σ) : ModC f σ' := by
  rw [modC_iff_strongMono hf] at h ⊢
  intro x y
  have := h x y
  have : σ' * ‖x - y‖ ^ 2 ≤ σ * ‖x - y‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hle (by positivity)
  linarith

/-- The quadratic upper bound of a β-smooth function (B&C Lemma 2.64(i), upper half;
A1's `upper_bound_on_segment`). -/
theorem upper_bound {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (x y : E) :
    f y ≤ f x + inner ℝ (gradient f x) (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
  have h := upper_bound_on_segment (f := f) (x := x) (d := x - y) (β := β) (t := 1)
    zero_le_one (fun _ _ => hf _) (fun _ _ => hL _ _)
  simp only [one_smul, sub_sub_cancel, one_pow, one_mul] at h
  rw [show y - x = -(x - y) by abel, inner_neg_right, norm_neg]
  linarith

/-- Baillon–Haddad from the quadratic upper bound (B&C Thm 18.15, (iii)⇒(v)), with L > 0. -/
theorem cocoercive_of_upper_pos {G : E → ℝ} {L : ℝ} (hG : Differentiable ℝ G)
    (hc : ConvexOn ℝ univ G)
    (hU : ∀ x y, G y ≤ G x + inner ℝ (gradient G x) (y - x) + L / 2 * ‖y - x‖ ^ 2)
    (hL : 0 < L) (x y : E) :
    ‖gradient G x - gradient G y‖ ^ 2 ≤ L * inner ℝ (gradient G x - gradient G y) (x - y) := by
  -- half inequality: G a − G b + ⟪∇G a, b − a⟫ ≤ −‖∇G b − ∇G a‖²/(2L)
  have half : ∀ a b : E, G a - G b + inner ℝ (gradient G a) (b - a)
      ≤ -(‖gradient G b - gradient G a‖ ^ 2 / (2 * L)) := by
    intro a b
    set w := gradient G b - gradient G a with hw
    have hU' := hU b (b - L⁻¹ • w)
    have hF := firstOrder_of_convexOn hG hc a (b - L⁻¹ • w)
    rw [show b - L⁻¹ • w - b = -(L⁻¹ • w) by abel, inner_neg_right, norm_neg, norm_smul,
      inner_smul_right, mul_pow, Real.norm_of_nonneg (inv_nonneg.2 hL.le)] at hU'
    rw [show b - L⁻¹ • w - a = (b - a) - L⁻¹ • w by abel, inner_sub_right,
      inner_smul_right] at hF
    have hww : ‖w‖ ^ 2 = inner ℝ (gradient G b) w - inner ℝ (gradient G a) w := by
      rw [← real_inner_self_eq_norm_sq, hw, inner_sub_left]
    have hq : L / 2 * (L⁻¹ ^ 2 * ‖w‖ ^ 2) = ‖w‖ ^ 2 / (2 * L) := by
      field_simp
    have hq2 : L⁻¹ * inner ℝ (gradient G b) w - L⁻¹ * inner ℝ (gradient G a) w
        = ‖w‖ ^ 2 / L := by
      rw [hww]; field_simp
    have hq3 : ‖w‖ ^ 2 / L = 2 * (‖w‖ ^ 2 / (2 * L)) := by field_simp
    linarith
  have h1 := half x y
  have h2 := half y x
  rw [norm_sub_rev (gradient G y)] at h1
  have e1 : inner ℝ (gradient G x - gradient G y) (x - y)
      = -(inner ℝ (gradient G x) (y - x) + inner ℝ (gradient G y) (x - y)) := by
    rw [inner_sub_left, show y - x = -(x - y) by abel, inner_neg_right]; ring
  rw [e1]
  have : ‖gradient G x - gradient G y‖ ^ 2 / (2 * L) * (2 * L)
      = ‖gradient G x - gradient G y‖ ^ 2 := by field_simp
  nlinarith

/-- Baillon–Haddad from the quadratic upper bound, L ≥ 0 (limit L + η ↓ L). -/
theorem cocoercive_of_upper {G : E → ℝ} {L : ℝ} (hG : Differentiable ℝ G)
    (hc : ConvexOn ℝ univ G)
    (hU : ∀ x y, G y ≤ G x + inner ℝ (gradient G x) (y - x) + L / 2 * ‖y - x‖ ^ 2)
    (hL : 0 ≤ L) (x y : E) :
    ‖gradient G x - gradient G y‖ ^ 2 ≤ L * inner ℝ (gradient G x - gradient G y) (x - y) := by
  have hη : ∀ η > 0, ‖gradient G x - gradient G y‖ ^ 2
      ≤ (L + η) * inner ℝ (gradient G x - gradient G y) (x - y) := by
    intro η hη
    refine cocoercive_of_upper_pos hG hc (fun a b => ?_) (by linarith) x y
    have := hU a b
    have : L / 2 * ‖b - a‖ ^ 2 ≤ (L + η) / 2 * ‖b - a‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  set B := inner ℝ (gradient G x - gradient G y) (x - y)
  set C := ‖gradient G x - gradient G y‖ ^ 2
  have hC : 0 ≤ C := by positivity
  have hB : 0 ≤ B := by
    have := hη 1 one_pos
    nlinarith
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have := hη (ε / (B + 1)) (by positivity)
  have : ε / (B + 1) * B ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  nlinarith

/-- With d ≥ 1 (a nontrivial space), a valid curvature claim never exceeds a valid
smoothness bound: StrongMono f σ and LipGrad f β give σ ≤ β (B3 thm:fb(b), "σ_f ≤ β"). -/
theorem le_of_strongMono_lipGrad [Nontrivial E] {f : E → ℝ} {σ β : ℝ}
    (hσ : StrongMono f σ) (hL : LipGrad f β) : σ ≤ β := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have h1 := hσ v 0
  have h2 := hL v 0
  simp only [sub_zero] at h1 h2
  have h3 := real_inner_le_norm (gradient f v - gradient f 0) v
  have hpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  have : σ * ‖v‖ ^ 2 ≤ β * ‖v‖ ^ 2 := by
    have := mul_le_mul_of_nonneg_right h2 hpos.le
    nlinarith
  exact le_of_mul_le_mul_right this (by positivity)

/-- A β-smooth function always satisfies C(f, −β) (so σ_i = −β_i is a valid real
replacement for the "no claim" curvature attribute σ_i = −∞). -/
theorem modC_neg_of_lipGrad {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f)
    (hL : LipGrad f β) : ModC f (-β) := by
  rw [modC_iff_strongMono hf]
  intro x y
  have h1 := hL x y
  have h2 := neg_abs_le (inner ℝ (gradient f x - gradient f y) (x - y))
  have h3 := abs_real_inner_le_norm (gradient f x - gradient f y) (x - y)
  have h4 := mul_le_mul_of_nonneg_right h1 (norm_nonneg (x - y))
  nlinarith

/-- One gradient step at α = 1/β descends: f(T x) ≤ f x − (α/2)‖R_α x‖²
(A1 lem:descent-step(a),(c): θ(1/β) = 1/(2β) = α/2). -/
theorem descent_step {f : E → ℝ} {β : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (x : E) :
    f (step f (1 / β) x) ≤ f x - (1 / β) / 2 * ‖resid f (1 / β) x‖ ^ 2 := by
  have h := descent_global hf hL x (by positivity : (0 : ℝ) < 1 / β)
  rw [theta_inv hβ] at h
  rw [resid_eq f (by positivity), step]
  have : 1 / β / 2 = 1 / (2 * β) := by field_simp
  rw [this]
  exact h

/-- The gradient step at α = 1/β is (1 − σ/β)-Lipschitz under C(f, σ), σ ≤ β
(B3 thm:fb(b), first case, at α = 1/β; proof by Baillon–Haddad applied to
f − (σ/2)‖·‖²). -/
theorem step_contract {f : E → ℝ} {β σ : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hσ : ModC f σ) (hσβ : σ ≤ β) (x y : E) :
    ‖step f (1 / β) x - step f (1 / β) y‖ ≤ (1 - σ / β) * ‖x - y‖ := by
  set G : E → ℝ := fun x => f x - σ / 2 * ‖x‖ ^ 2 with hGdef
  have hGd : Differentiable ℝ G := differentiable_sub_sq hf σ
  have hgG : ∀ z, gradient G z = gradient f z - σ • z := gradient_sub_sq hf σ
  have hU : ∀ a b, G b ≤ G a + inner ℝ (gradient G a) (b - a) + (β - σ) / 2 * ‖b - a‖ ^ 2 := by
    intro a b
    have h := upper_bound hf hL a b
    have hn : ‖b‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a (b - a) + ‖b - a‖ ^ 2 := by
      have := norm_add_sq_real a (b - a)
      rwa [add_sub_cancel] at this
    rw [hgG, inner_sub_left, real_inner_smul_left]
    simp only [hGdef]
    nlinarith
  have hco := cocoercive_of_upper hGd hσ hU (by linarith) x y
  have hmono : 0 ≤ inner ℝ (gradient G x - gradient G y) (x - y) :=
    (convexOn_iff_gradMonotone hGd).1 hσ x y
  set v := x - y with hv
  set gG := gradient G x - gradient G y with hgGdef
  have hu : step f (1 / β) x - step f (1 / β) y = (1 - σ / β) • v - (1 / β) • gG := by
    simp only [step, hgGdef, hgG, hv]
    module
  rw [hu]
  have ha : 0 ≤ 1 - σ / β := by
    rw [sub_nonneg, div_le_one hβ]; exact hσβ
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg ha (norm_nonneg _)) two_ne_zero,
    norm_sub_sq_real, norm_smul, norm_smul, Real.norm_of_nonneg ha,
    Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / β), inner_smul_left, inner_smul_right]
  simp only [conj_trivial]
  rw [real_inner_comm] at hmono hco
  set A := ‖v‖
  set B := inner ℝ gG v
  set C := ‖gG‖
  have hp : (1 / β) * β = 1 := by field_simp
  have hap : 1 - σ / β = (β - σ) * (1 / β) := by field_simp
  have hpp : 0 < 1 / β := by positivity
  rw [hap]
  have key : 2 * ((β - σ) * (1 / β) * A) * (1 / β * C) * 0 ≤ 0 := by simp
  nlinarith [mul_nonneg (mul_nonneg hpp.le hpp.le) (mul_nonneg (by linarith : (0:ℝ) ≤ β - σ) hmono),
    mul_le_mul_of_nonneg_left hco (mul_nonneg hpp.le hpp.le)]

/-- The residual contracts with the map: ‖R(T x)‖ ≤ (1 − σ/β)‖R x‖. -/
theorem resid_contract {f : E → ℝ} {β σ : ℝ} (hf : Differentiable ℝ f) (hL : LipGrad f β)
    (hβ : 0 < β) (hσ : ModC f σ) (hσβ : σ ≤ β) (x : E) :
    ‖resid f (1 / β) (step f (1 / β) x)‖ ≤ (1 - σ / β) * ‖resid f (1 / β) x‖ := by
  have hc := step_contract hf hL hβ hσ hσβ x (step f (1 / β) x)
  simp only [resid, one_div, inv_inv, norm_smul, Real.norm_of_nonneg hβ.le]
  rw [one_div] at hc
  calc β * ‖step f β⁻¹ x - step f β⁻¹ (step f β⁻¹ x)‖
      ≤ β * ((1 - σ / β) * ‖x - step f β⁻¹ x‖) := mul_le_mul_of_nonneg_left hc hβ.le
    _ = (1 - σ / β) * (β * ‖x - step f β⁻¹ x‖) := by ring

/-- The conclusions of regime A (clauses (S4A) and (S5A) of Theorem G3.1 at N = ∅, c = 1,
step α = 1/β, curvature number σ):
* σ ≤ β;
* argmin f = {x*};
* ‖x_k − x*‖ ≤ (1 − σ/β)^k ‖x₀ − x*‖ for every x₀ and k (S4A);
* ‖x − x*‖ ≤ ‖R_α(x)‖/σ for every x (S5A bracket);
* for every ε > 0 and x₀: k_ε exists, ‖x_{k_ε} − x*‖ ≤ ε/σ, k_ε = 0 if ‖R_α(x₀)‖ ≤ ε,
  k_ε ≤ 1 if σ = β, and k_ε ≤ max{0, ⌈log((2β/σ − 1)‖R_α(x₀)‖/ε)/log(β/(β − σ))⌉}
  if σ < β (S5A stopping certificate and count). -/
def RegimeA (f : E → ℝ) (β σ : ℝ) : Prop :=
  σ ≤ β ∧ ∃ xs : E, {x | IsMinOn f univ x} = {xs} ∧
    (∀ x₀ : E, ∀ k : ℕ, ‖iter f (1 / β) x₀ k - xs‖ ≤ (1 - σ / β) ^ k * ‖x₀ - xs‖) ∧
    (∀ x : E, ‖x - xs‖ ≤ ‖resid f (1 / β) x‖ / σ) ∧
    (∀ ε : ℝ, 0 < ε → ∀ x₀ : E,
      (∃ k, ‖resid f (1 / β) (iter f (1 / β) x₀ k)‖ ≤ ε) ∧
      ‖iter f (1 / β) x₀ (stopIdx f (1 / β) ε x₀) - xs‖ ≤ ε / σ ∧
      (‖resid f (1 / β) x₀‖ ≤ ε → stopIdx f (1 / β) ε x₀ = 0) ∧
      (σ = β → stopIdx f (1 / β) ε x₀ ≤ 1) ∧
      (σ < β → (stopIdx f (1 / β) ε x₀ : ℤ) ≤
        max 0 ⌈Real.log ((2 * β / σ - 1) * ‖resid f (1 / β) x₀‖ / ε)
          / Real.log (β / (β - σ))⌉))

/-- The count arithmetic of C2 cor:fb-stop(c) / rem:fb-res-spec: with q ∈ (0, 1),
C ≥ 1 and R₀ > ε > 0, K := ⌈log(C R₀/ε)/log(1/q)⌉ satisfies q^K R₀ ≤ ε. -/
lemma count_bound {q C R₀ ε : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hC : 1 ≤ C) (hε : 0 < ε)
    (hR : ε < R₀) :
    ∃ K : ℕ, (K : ℤ) = max 0 ⌈Real.log (C * R₀ / ε) / Real.log (1 / q)⌉ ∧ q ^ K * R₀ ≤ ε := by
  set L := Real.log (C * R₀ / ε) / Real.log (1 / q) with hLdef
  have hR0 : 0 < R₀ := hε.trans hR
  have hlq : 0 < Real.log (1 / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  have hratio : 1 < C * R₀ / ε := by
    rw [lt_div_iff₀ hε]; nlinarith
  have hLpos : 0 < L := div_pos (Real.log_pos hratio) hlq
  have hceil : 0 ≤ ⌈L⌉ := Int.ceil_nonneg hLpos.le
  refine ⟨⌈L⌉.toNat, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hceil, max_eq_right hceil]
  · have hK : L ≤ (⌈L⌉.toNat : ℝ) := by
      have : ((⌈L⌉.toNat : ℤ) : ℝ) = (⌈L⌉ : ℝ) := by rw [Int.toNat_of_nonneg hceil]
      rw [show ((⌈L⌉.toNat : ℕ) : ℝ) = ((⌈L⌉.toNat : ℤ) : ℝ) by norm_cast, this]
      exact Int.le_ceil L
    set K := ⌈L⌉.toNat
    have hlog : Real.log (C * R₀ / ε) ≤ K * Real.log (1 / q) := by
      have := mul_le_mul_of_nonneg_right hK hlq.le
      rwa [hLdef, div_mul_cancel₀ _ hlq.ne'] at this
    rw [← Real.log_pow] at hlog
    have hle : C * R₀ / ε ≤ (1 / q) ^ K :=
      (Real.log_le_log_iff (by positivity) (by positivity)).1 hlog
    rw [div_le_iff₀ hε, one_div, inv_pow] at hle
    have hqK : 0 < q ^ K := pow_pos hq0 K
    have : C * R₀ * q ^ K ≤ ε := by
      have := mul_le_mul_of_nonneg_right hle hqK.le
      have e : (q ^ K)⁻¹ * ε * q ^ K = ε := by field_simp
      linarith
    nlinarith

/-- **Regime A for the gradient step (the N = ∅, c = 1 core of (S4A) and (S5A)).**
f differentiable with β-Lipschitz gradient, β > 0, C(f, σ) with σ > 0, on a nontrivial
space (d ≥ 1): all the conclusions of `RegimeA` hold at the step α = 1/β. -/
theorem regimeA_of_modC [Nontrivial E] {f : E → ℝ} {β σ : ℝ} (hf : Differentiable ℝ f)
    (hL : LipGrad f β) (hβ : 0 < β) (hσ : ModC f σ) (hσpos : 0 < σ) : RegimeA f β σ := by
  have hsm : StrongMono f σ := (modC_iff_strongMono hf σ).1 hσ
  have hσβ : σ ≤ β := le_of_strongMono_lipGrad hsm hL
  set q := 1 - σ / β with hqdef
  have hq0 : 0 ≤ q := by rw [hqdef, sub_nonneg, div_le_one hβ]; exact hσβ
  have hq1 : q < 1 := by rw [hqdef]; have : 0 < σ / β := div_pos hσpos hβ; linarith
  set T := step f (1 / β) with hT
  -- Banach fixed point of the contraction T
  have hlip : LipschitzWith (Real.toNNReal q) T := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hq0]
    exact step_contract hf hL hβ hσ hσβ x y
  have hK : Real.toNNReal q < 1 := by
    rw [Real.toNNReal_lt_one]; exact hq1
  have hcon : ContractingWith (Real.toNNReal q) T := ⟨hK, hlip⟩
  haveI : Nonempty E := ⟨0⟩
  set xs := ContractingWith.fixedPoint T hcon with hxs
  have hfix : T xs = xs := ContractingWith.fixedPoint_isFixedPt (f := T) hcon
  have hgrad0 : gradient f xs = 0 := by
    have : (1 / β) • gradient f xs = 0 := by
      have h := hfix
      simp only [hT, step] at h
      have : xs - (xs - (1 / β) • gradient f xs) = 0 := by rw [h, sub_self]
      simpa using this
    rcases smul_eq_zero.1 this with h | h
    · exact absurd h (by positivity)
    · exact h
  -- f is convex (C(f, 0) by downward closure)
  have hconv : ConvexOn ℝ univ f := by
    have := modC_mono hf hσ hσpos.le
    unfold ModC at this
    simpa using this
  have hmin : IsMinOn f univ xs := by
    intro y _
    have := firstOrder_of_convexOn hf hconv xs y
    rw [hgrad0, inner_zero_left, add_zero] at this
    exact this
  -- residual equals gradient at α = 1/β
  have hres : ∀ x, resid f (1 / β) x = gradient f x := resid_eq f (by positivity)
  -- bracket (S5A)
  have hbr : ∀ x, ‖x - xs‖ ≤ ‖resid f (1 / β) x‖ / σ := by
    intro x
    rw [hres, le_div_iff₀ hσpos]
    have h1 := hsm x xs
    rw [hgrad0, sub_zero] at h1
    have h2 := real_inner_le_norm (gradient f x) (x - xs)
    rcases eq_or_lt_of_le (norm_nonneg (x - xs)) with h0 | hpos
    · rw [← h0]; simp
    · have : σ * ‖x - xs‖ * ‖x - xs‖ ≤ ‖gradient f x‖ * ‖x - xs‖ := by nlinarith
      have := le_of_mul_le_mul_right this hpos
      linarith
  -- rate (S4A)
  have hrate : ∀ x₀ k, ‖iter f (1 / β) x₀ k - xs‖ ≤ q ^ k * ‖x₀ - xs‖ := by
    intro x₀ k
    induction k with
    | zero => simp [iter]
    | succ k ih =>
      rw [iter_succ]
      calc ‖T (iter f (1 / β) x₀ k) - xs‖ = ‖T (iter f (1 / β) x₀ k) - T xs‖ := by rw [hfix]
        _ ≤ q * ‖iter f (1 / β) x₀ k - xs‖ := step_contract hf hL hβ hσ hσβ _ _
        _ ≤ q * (q ^ k * ‖x₀ - xs‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * ‖x₀ - xs‖ := by ring
  -- residual decay
  have hrd : ∀ x₀ k, ‖resid f (1 / β) (iter f (1 / β) x₀ k)‖
      ≤ q ^ k * ‖resid f (1 / β) x₀‖ := by
    intro x₀ k
    induction k with
    | zero => simp [iter]
    | succ k ih =>
      rw [iter_succ]
      calc ‖resid f (1 / β) (T (iter f (1 / β) x₀ k))‖
          ≤ q * ‖resid f (1 / β) (iter f (1 / β) x₀ k)‖ :=
            resid_contract hf hL hβ hσ hσβ _
        _ ≤ q * (q ^ k * ‖resid f (1 / β) x₀‖) := mul_le_mul_of_nonneg_left ih hq0
        _ = q ^ (k + 1) * ‖resid f (1 / β) x₀‖ := by ring
  refine ⟨hσβ, xs, ?_, hrate, hbr, ?_⟩
  · -- argmin = {xs}
    ext y
    simp only [mem_setOf_eq, mem_singleton_iff]
    constructor
    · intro hy
      have hd := descent_step hf hL hβ y
      have hle : f y ≤ f (step f (1 / β) y) := hy (mem_univ _)
      have hr0 : ‖resid f (1 / β) y‖ ^ 2 ≤ 0 := by
        have : 0 < 1 / β / 2 := by positivity
        nlinarith
      have hg0 : gradient f y = 0 := by
        rw [← hres]; exact norm_eq_zero.1 (by nlinarith [norm_nonneg (resid f (1 / β) y)])
      have h1 := hsm y xs
      rw [hg0, hgrad0, sub_zero, inner_zero_left] at h1
      have : ‖y - xs‖ ^ 2 ≤ 0 := by nlinarith
      exact sub_eq_zero.1 (norm_eq_zero.1 (by nlinarith [norm_nonneg (y - xs)]))
    · rintro rfl; exact hmin
  · intro ε hε x₀
    set S := {k | ‖resid f (1 / β) (iter f (1 / β) x₀ k)‖ ≤ ε} with hS
    set R₀ := ‖resid f (1 / β) x₀‖ with hR₀
    -- membership certificates
    have h0 : R₀ ≤ ε → 0 ∈ S := fun h => by
      simp only [hS, Set.mem_setOf_eq, iter, Function.iterate_zero, id]; exact h
    have hcase_eq : σ = β → 1 ∈ S := by
      intro he
      have : q = 0 := by rw [hqdef, he, div_self hβ.ne', sub_self]
      have := hrd x₀ 1
      rw [‹q = 0›, pow_one, zero_mul] at this
      show ‖resid f (1 / β) (iter f (1 / β) x₀ 1)‖ ≤ ε
      linarith
    have hcase_lt : σ < β → ε < R₀ → ∃ K : ℕ, (K : ℤ) = max 0
        ⌈Real.log ((2 * β / σ - 1) * R₀ / ε) / Real.log (β / (β - σ))⌉ ∧ K ∈ S := by
      intro hlt hR
      have hqpos : 0 < q := by
        rw [hqdef, sub_pos, div_lt_one hβ]; exact hlt
      have hC : 1 ≤ 2 * β / σ - 1 := by
        rw [le_sub_iff_add_le, le_div_iff₀ hσpos]; linarith
      obtain ⟨K, hKeq, hKb⟩ := count_bound hqpos hq1 hC hε hR
      have h1q : 1 / q = β / (β - σ) := by
        rw [hqdef]; field_simp
      rw [h1q] at hKeq
      exact ⟨K, hKeq, (hrd x₀ K).trans hKb⟩
    have hne : S.Nonempty := by
      by_cases hR : R₀ ≤ ε
      · exact ⟨0, h0 hR⟩
      · rcases eq_or_lt_of_le hσβ with he | hlt
        · exact ⟨1, hcase_eq he⟩
        · obtain ⟨K, -, hK⟩ := hcase_lt hlt (lt_of_not_ge hR)
          exact ⟨K, hK⟩
    have hmem : stopIdx f (1 / β) ε x₀ ∈ S := Nat.sInf_mem hne
    refine ⟨hne, ?_, ?_, ?_, ?_⟩
    · have := hbr (iter f (1 / β) x₀ (stopIdx f (1 / β) ε x₀))
      exact this.trans (div_le_div_of_nonneg_right hmem hσpos.le)
    · intro hR
      exact Nat.eq_zero_of_le_zero (Nat.sInf_le (h0 hR))
    · intro he
      exact Nat.sInf_le (hcase_eq he)
    · intro hlt
      by_cases hR : R₀ ≤ ε
      · have : stopIdx f (1 / β) ε x₀ = 0 := Nat.eq_zero_of_le_zero (Nat.sInf_le (h0 hR))
        rw [this]; exact le_max_left _ _
      · obtain ⟨K, hKeq, hK⟩ := hcase_lt hlt (lt_of_not_ge hR)
        rw [← hKeq]
        exact_mod_cast Nat.sInf_le hK

/-- Gradient of a quadratic ½⟨Hx, x⟩ − ⟨c, x⟩ with H symmetric: ∇ = Hx − c. -/
lemma hasGradientAt_quad (H : E →L[ℝ] E) (c : E)
    (hsym : ∀ x y, inner ℝ (H x) y = inner ℝ x (H y)) (x : E) :
    HasGradientAt (fun x => 1 / 2 * inner ℝ (H x) x - inner ℝ c x) (H x - c) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 := (H.hasFDerivAt (x := x)).inner ℝ (hasFDerivAt_id x)
  have h2 := (hasFDerivAt_const c x).inner ℝ (hasFDerivAt_id x)
  refine ((h1.const_mul (1 / 2)).sub h2).congr_fderiv ?_
  ext y
  simp [fderivInnerCLM_apply, hsym y x, real_inner_comm]
  ring

end Generic

/-! ### The declaration layer on ℝᵈ (N = ∅, c = 1) -/

/-- ℝᵈ. -/
abbrev Vec (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d n : ℕ}

/-- The declared numbers of the smooth part of an energy specification with N = ∅:
weights w_i, smoothness attributes β_i, curvature attributes σ_i, the kernel-carrying
index set S_K, and for i ∈ S_K the kernel attribute (K_i, ν_i), K_i given by an
orthonormal basis (`basis i`, of length `kdim i`). Fields with i ∉ S_K are unused
(A_i void). -/
structure Decl (d n : ℕ) where
  w : Fin n → ℝ
  β : Fin n → ℝ
  σ : Fin n → ℝ
  SK : Finset (Fin n)
  K : Fin n → Submodule ℝ (Vec d)
  ν : Fin n → ℝ
  kdim : Fin n → ℕ
  basis : (i : Fin n) → Fin (kdim i) → Vec d

/-- Validity of a kernel attribute (K, ν) for f (landed def:kernel-attribute). -/
def KernelValid (f : Vec d → ℝ) (K : Submodule ℝ (Vec d)) (ν : ℝ) : Prop :=
  ∀ x y, ν * ‖Kᗮ.starProjection (x - y)‖ ^ 2 ≤ inner ℝ (gradient f x - gradient f y) (x - y)

/-- Validity of the declaration for the terms f_i (landed def:energy-spec, smooth part):
w_i > 0, β_i ∈ [0, ∞), f_i ∈ C¹ with ∇f_i β_i-Lipschitz, C(f_i, σ_i), and for i ∈ S_K
ν_i > 0, the basis orthonormal and spanning K_i, and (K_i, ν_i) valid. -/
structure Decl.Valid (D : Decl d n) (f : Fin n → Vec d → ℝ) : Prop where
  w_pos : ∀ i, 0 < D.w i
  β_nonneg : ∀ i, 0 ≤ D.β i
  diff : ∀ i, Differentiable ℝ (f i)
  smooth : ∀ i, LipGrad (f i) (D.β i)
  curv : ∀ i, ModC (f i) (D.σ i)
  ν_pos : ∀ i ∈ D.SK, 0 < D.ν i
  basis_orth : ∀ i ∈ D.SK, Orthonormal ℝ (D.basis i)
  basis_span : ∀ i ∈ D.SK, Submodule.span ℝ (Set.range (D.basis i)) = D.K i
  kernel : ∀ i ∈ D.SK, KernelValid (f i) (D.K i) (D.ν i)

namespace Decl

/-- The energy (= smooth part, N = ∅) E = Σ_i w_i f_i. -/
noncomputable def energy (D : Decl d n) (f : Fin n → Vec d → ℝ) : Vec d → ℝ :=
  fun x => ∑ i, D.w i * f i x

/-- β̂ = Σ_i w_i β_i. -/
def betaHat (D : Decl d n) : ℝ := ∑ i, D.w i * D.β i

/-- σ̂_S = Σ_i w_i σ_i. -/
def sigmaHatS (D : Decl d n) : ℝ := ∑ i, D.w i * D.σ i

/-- Enumeration of a subset T of the index set (any fixed one; Δ_w does not depend on it
for the purposes of every theorem below, which hold for each enumeration). -/
noncomputable def tIdx (T : Finset (Fin n)) (j : Fin T.card) : Fin n := (T.equivFin.symm j : Fin n)

/-- The exact transversality defect Δ_w(T) of the Kernel Gram certificate of
(K_i, w_iν_i)_{i∈T} (T1/B1p's `deltaW` on the declared bases; Δ_w(∅) = 0). -/
noncomputable def deltaW (D : Decl d n) (T : Finset (Fin n)) : ℝ :=
  OCF.deltaW (k := fun j => D.kdim (tIdx T j)) (fun j p => (D.basis (tIdx T j) p).ofLp)
    (fun j => D.w (tIdx T j) * D.ν (tIdx T j))

/-- b(T) evaluated at a defect value Δ: Δ + Σ_{i∉T} w_iσ_i. With Δ = Δ_w(T) this is the
exact b(T); with a computed Δ⁻(T) it is b⁻(T). -/
def bOf (D : Decl d n) (T : Finset (Fin n)) (Δ : ℝ) : ℝ := Δ + ∑ i ∈ Tᶜ, D.w i * D.σ i

/-- σ_𝔈 at a defect value Δ: max{σ̂_S, b}. With Δ = Δ_w(T) this is σ_𝔈^T; with a computed
Δ⁻(T) it is σ_𝔈^{T,−}. -/
def sigmaOf (D : Decl d n) (T : Finset (Fin n)) (Δ : ℝ) : ℝ := max D.sigmaHatS (D.bOf T Δ)

/-- The exact σ_𝔈^T. -/
noncomputable def sigmaT (D : Decl d n) (T : Finset (Fin n)) : ℝ := D.sigmaOf T (D.deltaW T)

end Decl

lemma deltaW_card_zero {m : ℕ} (hm : m = 0) {k : Fin m → ℕ}
    (b : (i : Fin m) → Fin (k i) → (Fin d → ℝ)) (a : Fin m → ℝ) : OCF.deltaW b a = 0 := by
  subst hm
  simp only [OCF.deltaW, Finset.univ_eq_empty, Finset.sum_empty, zero_sub, neg_eq_zero]
  unfold lambdaMax
  split_ifs <;> simp

lemma sum_tIdx (T : Finset (Fin n)) (h : Fin n → ℝ) :
    ∑ j : Fin T.card, h (Decl.tIdx T j) = ∑ i ∈ T, h i := by
  rw [← Finset.sum_coe_sort T h]
  exact Equiv.sum_comp T.equivFin.symm (fun i : T => h i)

lemma tIdx_mem (T : Finset (Fin n)) (j : Fin T.card) : Decl.tIdx T j ∈ T :=
  (T.equivFin.symm j).2

namespace Decl

variable (D : Decl d n) {f : Fin n → Vec d → ℝ}

lemma energy_differentiable (hv : D.Valid f) : Differentiable ℝ (D.energy f) := by
  have := hv.diff
  unfold energy
  fun_prop

lemma gradient_energy (hv : D.Valid f) (x : Vec d) :
    gradient (D.energy f) x = ∑ i, D.w i • gradient (f i) x := by
  show gradient (fun z => ∑ i, D.w i * f i z) x = _
  rw [OCF.gradient_weighted_sum f D.w hv.diff x, Finset.sum_apply]
  rfl

lemma inner_gradient_energy (hv : D.Valid f) (x y : Vec d) :
    inner ℝ (gradient (D.energy f) x - gradient (D.energy f) y) (x - y)
      = ∑ i, D.w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y) := by
  rw [gradient_energy D hv, gradient_energy D hv, ← Finset.sum_sub_distrib, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← smul_sub, real_inner_smul_left]

/-- **Validity of β̂** (landed prop:spec-moduli(a), β(F) ≤ Σ w_iβ_i): ∇E is β̂-Lipschitz. -/
theorem betaHat_valid (hv : D.Valid f) : LipGrad (D.energy f) D.betaHat := by
  intro u v
  rw [gradient_energy D hv, gradient_energy D hv, ← Finset.sum_sub_distrib, betaHat,
    Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hv.w_pos i).le, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hv.smooth i u v) (hv.w_pos i).le

/-- Strong monotonicity of ∇E with σ̂_S. -/
lemma strongMono_sigmaHatS (hv : D.Valid f) : StrongMono (D.energy f) D.sigmaHatS := by
  intro x y
  rw [inner_gradient_energy D hv, sigmaHatS, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have := (modC_iff_strongMono (hv.diff i) _).1 (hv.curv i) x y
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left this (hv.w_pos i).le

/-- The T-part of ∇E is Δ_w(T)-strongly monotone (B1p Theorem (a), reindexed to T). -/
lemma strongMono_T (hd : 0 < d) (hv : D.Valid f) {T : Finset (Fin n)} (hT : T ⊆ D.SK)
    (x y : Vec d) :
    D.deltaW T * ‖x - y‖ ^ 2
      ≤ ∑ i ∈ T, D.w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y) := by
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · rw [deltaW, deltaW_card_zero h0, zero_mul, Finset.card_eq_zero.1 h0, Finset.sum_empty]
  · have hm := OCF.uniform_composite_gap_of_restricted_monotone hpos hd
      (fun j => gradient (f (tIdx T j))) (fun j => D.w (tIdx T j))
      (fun j => hv.w_pos _) (fun j => D.K (tIdx T j)) (fun j => D.ν (tIdx T j))
      (fun j => hv.ν_pos _ (hT (tIdx_mem T j)))
      (fun j x y => hv.kernel _ (hT (tIdx_mem T j)) x y)
      (k := fun j => D.kdim (tIdx T j)) (fun j => D.basis (tIdx T j))
      (fun j => hv.basis_orth _ (hT (tIdx_mem T j)))
      (fun j => hv.basis_span _ (hT (tIdx_mem T j))) x y
    have hexp : inner ℝ ((∑ j, D.w (tIdx T j) • (fun j => gradient (f (tIdx T j))) j) x
        - (∑ j, D.w (tIdx T j) • (fun j => gradient (f (tIdx T j))) j) y) (x - y)
        = ∑ j : Fin T.card, D.w (tIdx T j)
            * inner ℝ (gradient (f (tIdx T j)) x - gradient (f (tIdx T j)) y) (x - y) := by
      simp only [Finset.sum_apply, Pi.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub,
        sum_inner, real_inner_smul_left]
    rw [hexp, sum_tIdx T
      (fun i => D.w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y))] at hm
    exact hm

/-- Strong monotonicity of ∇E with b(T) at any Δ ≤ Δ_w(T). -/
lemma strongMono_bOf (hd : 0 < d) (hv : D.Valid f) {T : Finset (Fin n)} (hT : T ⊆ D.SK)
    {Δ : ℝ} (hΔ : Δ ≤ D.deltaW T) : StrongMono (D.energy f) (D.bOf T Δ) := by
  intro x y
  rw [inner_gradient_energy D hv, ← Finset.sum_add_sum_compl T, bOf, add_mul,
    Finset.sum_mul]
  have h1 := D.strongMono_T hd hv hT x y
  have h1' : Δ * ‖x - y‖ ^ 2 ≤ D.deltaW T * ‖x - y‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hΔ (by positivity)
  have h2 : ∑ i ∈ Tᶜ, D.w i * D.σ i * ‖x - y‖ ^ 2
      ≤ ∑ i ∈ Tᶜ, D.w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y) := by
    refine Finset.sum_le_sum fun i _ => ?_
    have := (modC_iff_strongMono (hv.diff i) _).1 (hv.curv i) x y
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left this (hv.w_pos i).le
  linarith

/-- **Validity of σ_𝔈^T, and (S7) downward closure** (G12 lem:rule-sum(b) with B1p,
G12 lem:decl-order(b)): for T ⊆ S_K and any Δ ≤ Δ_w(T) (in particular Δ = Δ_w(T)),
C(E, max{σ̂_S, Δ + Σ_{i∉T} w_iσ_i}) holds. -/
theorem sigmaOf_valid (hd : 0 < d) (hv : D.Valid f) {T : Finset (Fin n)} (hT : T ⊆ D.SK)
    {Δ : ℝ} (hΔ : Δ ≤ D.deltaW T) : ModC (D.energy f) (D.sigmaOf T Δ) := by
  rw [modC_iff_strongMono (D.energy_differentiable hv), sigmaOf]
  rcases le_total D.sigmaHatS (D.bOf T Δ) with h | h
  · rw [max_eq_right h]; exact D.strongMono_bOf hd hv hT hΔ
  · rw [max_eq_left h]; exact D.strongMono_sigmaHatS hv

/-- The exact σ_𝔈^T is valid. -/
theorem sigmaT_valid (hd : 0 < d) (hv : D.Valid f) {T : Finset (Fin n)} (hT : T ⊆ D.SK) :
    ModC (D.energy f) (D.sigmaT T) :=
  D.sigmaOf_valid hd hv hT le_rfl

/-- The computed σ_𝔈^{T,−} never exceeds the exact σ_𝔈^T when Δ⁻ ≤ Δ_w(T). -/
lemma sigmaOf_le_sigmaT {T : Finset (Fin n)} {Δ : ℝ} (hΔ : Δ ≤ D.deltaW T) :
    D.sigmaOf T Δ ≤ D.sigmaT T := by
  unfold sigmaT sigmaOf bOf
  exact max_le_max le_rfl (by linarith)

end Decl

lemma nontrivial_vec (hd : 0 < d) : Nontrivial (Vec d) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  infer_instance

/-! ### Theorem G3.1 restricted to N = ∅, c = 1 (smooth atoms) -/

/-- The conclusions of Theorem G3.1 at N = ∅, c = 1, for the energy `Ef`, declared β̂,
exact σ_𝔈^T = `σex` and computed σ_𝔈^{T,−} = `σm`, at the step α = 1/β̂:
* validity of β̂ (∇E is β̂-Lipschitz) and of σ_𝔈^T (C(E, σ_𝔈^T));
* (S7) validity of the computed number, C(E, σ_𝔈^{T,−}), and σ_𝔈^{T,−} ≤ σ_𝔈^T;
* (S1) E(x_{k+1}) ≤ E(x_k) − (α/2)‖R_α(x_k)‖² for every start x₀ and every k (k₀ = 0);
* (S4A)+(S5A) in regime A, read off the computed number: if σ_𝔈^{T,−} > 0 then
  `RegimeA Ef β̂ σ_𝔈^{T,−}` (σ_𝔈^{T,−} ≤ β̂, unique minimiser x*, rate (1 − σ_𝔈^{T,−}/β̂)^k,
  bracket ‖x − x*‖ ≤ ‖R_α(x)‖/σ_𝔈^{T,−}, stopping index, distance ε/σ_𝔈^{T,−}, count);
* downward closure of the certificates (the mechanism of (S7)): every positive σ′ ≤ σ_𝔈^{T,−}
  also certifies `RegimeA Ef β̂ σ′`.
With σm = σex (Δ⁻ = Δ_w) these are the exact clauses. -/
def SoundnessConclusions (Ef : Vec d → ℝ) (βh σex σm : ℝ) : Prop :=
  LipGrad Ef βh ∧ ModC Ef σex ∧ ModC Ef σm ∧ σm ≤ σex ∧
  (∀ x₀ : Vec d, ∀ k : ℕ, Ef (iter Ef (1 / βh) x₀ (k + 1))
      ≤ Ef (iter Ef (1 / βh) x₀ k) - (1 / βh) / 2 * ‖resid Ef (1 / βh) (iter Ef (1 / βh) x₀ k)‖ ^ 2) ∧
  (0 < σm → RegimeA Ef βh σm) ∧
  (∀ σ' : ℝ, 0 < σ' → σ' ≤ σm → RegimeA Ef βh σ')

/-- **Theorem G3.1, fragment N = ∅, c = 1, C¹ atoms with Lipschitz gradients (target 3),
including (S7).** H-dim (d ≥ 1), H-valid (`D.Valid f`), H-FB (β̂ > 0), H-T (T ⊆ S_K),
H-Δ (Δ⁻ ≤ Δ_w(T)). -/
theorem soundness_smooth (hd : 0 < d) (D : Decl d n) (f : Fin n → Vec d → ℝ)
    (hv : D.Valid f) (hFB : 0 < D.betaHat) {T : Finset (Fin n)} (hT : T ⊆ D.SK)
    (Δm : ℝ) (hΔ : Δm ≤ D.deltaW T) :
    SoundnessConclusions (D.energy f) D.betaHat (D.sigmaT T) (D.sigmaOf T Δm) := by
  haveI := nontrivial_vec hd
  have hE := D.energy_differentiable hv
  have hL := D.betaHat_valid hv
  have hσm := D.sigmaOf_valid hd hv hT hΔ
  refine ⟨hL, D.sigmaT_valid hd hv hT, hσm, D.sigmaOf_le_sigmaT hΔ, ?_, ?_, ?_⟩
  · intro x₀ k
    rw [iter_succ]
    exact descent_step hE hL hFB _
  · intro hpos
    exact regimeA_of_modC hE hL hFB hσm hpos
  · intro σ' hpos hle
    exact regimeA_of_modC hE hL hFB (modC_mono hE hσm hle) hpos

/-- The exact form (Δ⁻ := Δ_w(T)) of `soundness_smooth`. -/
theorem soundness_smooth_exact (hd : 0 < d) (D : Decl d n) (f : Fin n → Vec d → ℝ)
    (hv : D.Valid f) (hFB : 0 < D.betaHat) {T : Finset (Fin n)} (hT : T ⊆ D.SK) :
    SoundnessConclusions (D.energy f) D.betaHat (D.sigmaT T) (D.sigmaT T) :=
  soundness_smooth hd D f hv hFB hT (D.deltaW T) le_rfl

/-! ### Quadratic atoms (target 1): f_i(x) = ½⟨H_i x, x⟩ − ⟨c_i, x⟩ -/

/-- Quadratic atoms f_i(x) = ½⟨H_i x, x⟩ − ⟨c_i, x⟩ (H_i a self-adjoint operator on ℝᵈ,
i.e. a symmetric d × d matrix). -/
noncomputable def quadAtom (H : Fin n → Vec d →L[ℝ] Vec d) (c : Fin n → Vec d) (i : Fin n)
    (x : Vec d) : ℝ :=
  1 / 2 * inner ℝ (H i x) x - inner ℝ (c i) x

section Quad

variable {H : Fin n → Vec d →L[ℝ] Vec d} {c : Fin n → Vec d}

lemma gradient_quadAtom (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y)) (i : Fin n)
    (x : Vec d) : gradient (quadAtom H c i) x = H i x - c i :=
  (hasGradientAt_quad (H i) (c i) (hsym i) x).gradient

lemma differentiable_quadAtom (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y))
    (i : Fin n) : Differentiable ℝ (quadAtom H c i) :=
  fun x => (hasGradientAt_quad (H i) (c i) (hsym i) x).differentiableAt

lemma inner_gradient_quadAtom (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y))
    (i : Fin n) (x y : Vec d) :
    inner ℝ (gradient (quadAtom H c i) x - gradient (quadAtom H c i) y) (x - y)
      = inner ℝ (H i (x - y)) (x - y) := by
  rw [gradient_quadAtom hsym, gradient_quadAtom hsym, map_sub]
  congr 1; abel

/-- C(f_i, σ) ⇔ H_i ⪰ σI. -/
theorem quad_modC_iff (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y)) (i : Fin n)
    (σ : ℝ) : ModC (quadAtom H c i) σ ↔ ∀ v, σ * ‖v‖ ^ 2 ≤ inner ℝ (H i v) v := by
  rw [modC_iff_strongMono (differentiable_quadAtom hsym i)]
  constructor
  · intro h v
    have := h v 0
    rwa [inner_gradient_quadAtom hsym, sub_zero] at this
  · intro h x y
    rw [inner_gradient_quadAtom hsym]
    exact h _

/-- (K, ν) valid for f_i ⇔ ⟨H_i v, v⟩ ≥ ν‖P_{K^⊥}v‖² (landed rem:kernel-attribute(iii)). -/
theorem quad_kernel_iff (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y)) (i : Fin n)
    (K : Submodule ℝ (Vec d)) (ν : ℝ) :
    KernelValid (quadAtom H c i) K ν ↔
      ∀ v, ν * ‖Kᗮ.starProjection v‖ ^ 2 ≤ inner ℝ (H i v) v := by
  constructor
  · intro h v
    have := h v 0
    rwa [inner_gradient_quadAtom hsym, sub_zero] at this
  · intro h x y
    rw [inner_gradient_quadAtom hsym]
    exact h _

/-- For H_i ⪰ 0: ∇f_i is β-Lipschitz ⇔ H_i ⪯ βI (β ≥ 0). The direction ⇐ is Baillon–Haddad
from the quadratic upper bound (`cocoercive_of_upper`): ‖H v‖² ≤ β⟨Hv, v⟩ ≤ β²‖v‖². -/
theorem quad_lipGrad_iff (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y))
    (hpsd : ∀ i v, 0 ≤ inner ℝ (H i v) v) (i : Fin n) {β : ℝ} (hβ : 0 ≤ β) :
    LipGrad (quadAtom H c i) β ↔ ∀ v, inner ℝ (H i v) v ≤ β * ‖v‖ ^ 2 := by
  have hgd : ∀ u v, gradient (quadAtom H c i) u - gradient (quadAtom H c i) v = H i (u - v) := by
    intro u v; rw [gradient_quadAtom hsym, gradient_quadAtom hsym, map_sub]; abel
  constructor
  · intro h v
    have h1 := h v 0
    rw [hgd, sub_zero] at h1
    have h2 := real_inner_le_norm (H i v) v
    nlinarith [norm_nonneg v]
  · intro h u v
    rw [hgd]
    have hd := differentiable_quadAtom (c := c) hsym i
    have hconv : ConvexOn ℝ univ (quadAtom H c i) := by
      rw [convexOn_iff_gradMonotone hd]
      intro x y
      rw [inner_gradient_quadAtom hsym]
      exact hpsd i _
    have hU : ∀ x y, quadAtom H c i y ≤ quadAtom H c i x
        + inner ℝ (gradient (quadAtom H c i) x) (y - x) + β / 2 * ‖y - x‖ ^ 2 := by
      intro x y
      have hq := h (y - x)
      rw [gradient_quadAtom hsym]
      simp only [quadAtom]
      have e : inner ℝ (H i (y - x)) (y - x)
          = inner ℝ (H i y) y - 2 * inner ℝ (H i x) y + inner ℝ (H i x) x := by
        rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right, hsym i y x,
          real_inner_comm (H i x) y]
        ring
      rw [inner_sub_left, inner_sub_right, inner_sub_right]
      nlinarith
    have hco := cocoercive_of_upper hd hconv hU hβ u v
    rw [hgd] at hco
    have hq := h (u - v)
    have hsq : ‖H i (u - v)‖ ^ 2 ≤ (β * ‖u - v‖) ^ 2 := by
      have := mul_le_mul_of_nonneg_left hq hβ
      nlinarith
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hsq

end Quad

/-- The energy of quadratic atoms is E(x) = ½⟨Hx, x⟩ − ⟨b, x⟩ with H = Σ w_iH_i and
b = Σ w_ic_i. -/
lemma energy_quad (D : Decl d n) (H : Fin n → Vec d →L[ℝ] Vec d) (c : Fin n → Vec d)
    (x : Vec d) :
    D.energy (quadAtom H c) x
      = 1 / 2 * inner ℝ ((∑ i, D.w i • H i) x) x - inner ℝ (∑ i, D.w i • c i) x := by
  simp only [Decl.energy, quadAtom, _root_.sum_apply,
    _root_.smul_apply, sum_inner, real_inner_smul_left, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

/-- With g = 0 the residual is the gradient: R_α(x) = Hx − b at α = 1/β̂. -/
lemma resid_quad (D : Decl d n) (H : Fin n → Vec d →L[ℝ] Vec d) (c : Fin n → Vec d)
    (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y)) (hFB : 0 < D.betaHat)
    (x : Vec d) :
    resid (D.energy (quadAtom H c)) (1 / D.betaHat) x
      = (∑ i, D.w i • H i) x - ∑ i, D.w i • c i := by
  rw [resid_eq _ (by positivity)]
  have : ∀ z, HasGradientAt (fun x => 1 / 2 * inner ℝ ((∑ i, D.w i • H i) x) x
      - inner ℝ (∑ i, D.w i • c i) x) ((∑ i, D.w i • H i) z - ∑ i, D.w i • c i) z := by
    refine hasGradientAt_quad _ _ (fun x y => ?_)
    simp only [_root_.sum_apply, _root_.smul_apply, sum_inner,
      inner_sum, real_inner_smul_left, real_inner_smul_right, hsym]
  have he : D.energy (quadAtom H c) = fun x => 1 / 2 * inner ℝ ((∑ i, D.w i • H i) x) x
      - inner ℝ (∑ i, D.w i • c i) x := funext (energy_quad D H c)
  rw [he]
  exact (this x).gradient

/-- **Theorem G3.1, quadratic fragment (target 1): N = ∅, c = 1,
E(x) = ½xᵀHx − bᵀx, H = Σ w_iH_i, H_i ⪰ 0, declared (w_i, β_i, σ_i, (K_i, ν_i)),
step α = 1/β̂, including (S7).** Hypotheses: H-dim (d ≥ 1); H_i symmetric and ⪰ 0;
H-valid in Loewner form (w_i > 0, β_i ≥ 0, H_i ⪯ β_iI, H_i ⪰ σ_iI, and for i ∈ S_K:
ν_i > 0, orthonormal basis of K_i, ⟨H_iv, v⟩ ≥ ν_i‖P_{K_i^⊥}v‖² — each equivalent to the
landed validity of that attribute by `quad_lipGrad_iff`, `quad_modC_iff`, `quad_kernel_iff`);
H-FB (β̂ > 0); H-T (T ⊆ S_K); H-Δ (Δ⁻ ≤ Δ_w(T)). -/
theorem soundness_quadratic (hd : 0 < d) (D : Decl d n) (H : Fin n → Vec d →L[ℝ] Vec d)
    (c : Fin n → Vec d)
    (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y))
    (hpsd : ∀ i v, 0 ≤ inner ℝ (H i v) v)
    (hw : ∀ i, 0 < D.w i) (hβ0 : ∀ i, 0 ≤ D.β i)
    (hβ : ∀ i v, inner ℝ (H i v) v ≤ D.β i * ‖v‖ ^ 2)
    (hσ : ∀ i v, D.σ i * ‖v‖ ^ 2 ≤ inner ℝ (H i v) v)
    (hν : ∀ i ∈ D.SK, 0 < D.ν i)
    (horth : ∀ i ∈ D.SK, Orthonormal ℝ (D.basis i))
    (hspan : ∀ i ∈ D.SK, Submodule.span ℝ (Set.range (D.basis i)) = D.K i)
    (hker : ∀ i ∈ D.SK, ∀ v, D.ν i * ‖(D.K i)ᗮ.starProjection v‖ ^ 2 ≤ inner ℝ (H i v) v)
    (hFB : 0 < D.betaHat) {T : Finset (Fin n)} (hT : T ⊆ D.SK)
    (Δm : ℝ) (hΔ : Δm ≤ D.deltaW T) :
    SoundnessConclusions (D.energy (quadAtom H c)) D.betaHat (D.sigmaT T) (D.sigmaOf T Δm) := by
  have hv : D.Valid (quadAtom H c) :=
    { w_pos := hw
      β_nonneg := hβ0
      diff := differentiable_quadAtom hsym
      smooth := fun i => (quad_lipGrad_iff hsym hpsd i (hβ0 i)).2 (hβ i)
      curv := fun i => (quad_modC_iff hsym i _).2 (hσ i)
      ν_pos := hν
      basis_orth := horth
      basis_span := hspan
      kernel := fun i hi => (quad_kernel_iff hsym i _ _).2 (hker i hi) }
  exact soundness_smooth hd D _ hv hFB hT Δm hΔ

/-- **Corollary G3.2(a), H-FB part.** With β_i ≥ 0, the specification with weights w > 0
is forward–backward typed (β̂(w) > 0) iff some β_i > 0 — for every w or for none. -/
theorem betaHat_pos_iff (D : Decl d n) (hw : ∀ i, 0 < D.w i) (hβ0 : ∀ i, 0 ≤ D.β i) :
    0 < D.betaHat ↔ ∃ i, 0 < D.β i := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : D.betaHat ≤ 0 := by
      unfold Decl.betaHat
      exact Finset.sum_nonpos fun i _ => by
        have := le_antisymm (hc i) (hβ0 i); rw [this, mul_zero]
    linarith
  · rintro ⟨i, hi⟩
    unfold Decl.betaHat
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hw j).le (hβ0 j))
      ⟨i, Finset.mem_univ _, mul_pos (hw i) hi⟩

/-- **Corollary G3.2 (G5), quadratic fragment: weights selected between runs.** Fix the
terms (H_i, c_i) and their attributes (β_i, σ_i, (K_i, ν_i)) validly, with some β_i > 0.
Then for EVERY weight vector w ∈ (0, ∞)^S the specification 𝔈(w) is forward–backward typed
and every conclusion of Theorem G3.1 (fragment) holds for 𝔈(w), with β̂(w), Δ_w(T)(w) and
σ_𝔈^T(w) recomputed at w, for every T ⊆ S_K and every Δ⁻ ≤ Δ_w(T)(w). -/
theorem weights_between_runs (hd : 0 < d) (D : Decl d n) (H : Fin n → Vec d →L[ℝ] Vec d)
    (c : Fin n → Vec d)
    (hsym : ∀ i x y, inner ℝ (H i x) y = inner ℝ x (H i y))
    (hpsd : ∀ i v, 0 ≤ inner ℝ (H i v) v)
    (hβ0 : ∀ i, 0 ≤ D.β i)
    (hβ : ∀ i v, inner ℝ (H i v) v ≤ D.β i * ‖v‖ ^ 2)
    (hσ : ∀ i v, D.σ i * ‖v‖ ^ 2 ≤ inner ℝ (H i v) v)
    (hν : ∀ i ∈ D.SK, 0 < D.ν i)
    (horth : ∀ i ∈ D.SK, Orthonormal ℝ (D.basis i))
    (hspan : ∀ i ∈ D.SK, Submodule.span ℝ (Set.range (D.basis i)) = D.K i)
    (hker : ∀ i ∈ D.SK, ∀ v, D.ν i * ‖(D.K i)ᗮ.starProjection v‖ ^ 2 ≤ inner ℝ (H i v) v)
    (hβpos : ∃ i, 0 < D.β i) :
    ∀ w : Fin n → ℝ, (∀ i, 0 < w i) →
      0 < ({ D with w := w } : Decl d n).betaHat ∧
      ∀ T : Finset (Fin n), T ⊆ D.SK → ∀ Δm : ℝ, Δm ≤ ({ D with w := w } : Decl d n).deltaW T →
        SoundnessConclusions (({ D with w := w } : Decl d n).energy (quadAtom H c))
          ({ D with w := w } : Decl d n).betaHat
          (({ D with w := w } : Decl d n).sigmaT T)
          (({ D with w := w } : Decl d n).sigmaOf T Δm) := by
  intro w hw
  have hFB := (betaHat_pos_iff ({ D with w := w } : Decl d n) hw hβ0).2 hβpos
  exact ⟨hFB, fun T hT Δm hΔ => soundness_quadratic hd { D with w := w } H c hsym hpsd hw hβ0
    hβ hσ hν horth hspan hker hFB hT Δm hΔ⟩

end OCF.G3

#print axioms OCF.G3.soundness_quadratic
#print axioms OCF.G3.soundness_smooth
#print axioms OCF.G3.soundness_smooth_exact
#print axioms OCF.G3.weights_between_runs
#print axioms OCF.G3.betaHat_pos_iff
#print axioms OCF.G3.regimeA_of_modC
#print axioms OCF.G3.Decl.betaHat_valid
#print axioms OCF.G3.Decl.sigmaT_valid
#print axioms OCF.G3.Decl.sigmaOf_valid
#print axioms OCF.G3.quad_lipGrad_iff
#print axioms OCF.G3.quad_modC_iff
#print axioms OCF.G3.quad_kernel_iff
#print axioms OCF.G3.energy_quad
#print axioms OCF.G3.resid_quad
#print axioms OCF.G3.cocoercive_of_upper
#print axioms OCF.G3.step_contract
#print axioms OCF.G3.modC_neg_of_lipGrad

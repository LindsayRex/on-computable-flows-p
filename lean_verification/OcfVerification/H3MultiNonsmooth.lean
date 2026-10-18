/-
H3 (Two or more non-smooth terms: consensus typing) — the novel mathematics of the unit:
Lemma L0 (the Lipschitz attribute forces σ = 0; weighting rule), the elementary core of
Lemma L1(ii) (parallel-axis identity), Lemma L2 (read-out identities), Lemma L3(a),(b)
(fixed points; explicit fixed point), Lemma L4 (consensus minorant), Theorem T1 (the
consensus-gap certificate) and Corollary T1-it, Proposition P1 (i)–(iv) (necessity and
sharpness), Proposition P2 (no linear rate from declared numbers), Theorem T2(c)/(d)
(a-priori rate assembly and step count).

Source of truth: project_plan/done/proof_audits/H3_multi_nonsmooth/01_derivation.md (stage-1 dossier,
2026-10-10; §§0–4 and §6 "Lean targets"), landing draft 04_landing_draft.tex
(def:h3-consensus, lem:h3-lipschitz, lem:h3-readout, thm:h3-certificate,
prop:h3-necessity, thm:h3-soundness, prop:h3-nolinear).
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised: 4ee4d42cad893b61.

MODELLING CHOICES (none weakens a dossier statement):
* ℝ^d — an arbitrary real inner product space `X` (complete where ∇ is used); d ≥ 1 —
  `[Nontrivial X]` (`lip_modC_nonpos_vec` states L0(a) literally on `Vec d`, 1 ≤ d).
* An extended-valued g ∈ Γ₀ — a pair (`D : Set X`, `g : X → ℝ`): g on D, +∞ off D.
  `ExtSub D g σ p v`: p ∈ D and the σ-strong subgradient inequality on D (σ = 0 is
  v ∈ ∂g(p), B&C (16.1)). `ExtModC D g σ`: C(g, σ) (g − (σ/2)‖·‖² convex on D); with
  D = univ it is G3's `ModC`. `LipAttr g L`: 0 ≤ L and |g x − g y| ≤ L‖x − y‖ on all of X.
  Lower semicontinuity/properness are never used, so they are not assumed.
* Prox outputs are hypotheses (Mathlib has no prox theory): `ConsIter.Realises` states
  B&C Prop. 16.44 + 16.6(i), prox_{ag}(y) = q ⟺ (y − q)/a ∈ ∂g(q), for the two prox
  programs. For the concrete instances (P2) the programs are explicit and this
  characterisation is PROVED (`P2.realises`, via `proxChar_of_forall`: existence of the
  inclusion + uniqueness by monotonicity).
* F ∈ C¹ — `Differentiable ℝ F` (weaker); ∇F — Mathlib `gradient F`.
* (C2) (Beck Thm 5.24, classical) is proved for extended-valued terms (`extSub_strong`);
  convexity of E − (μ̂/2)‖·‖² on dom E is proved (`HCert.extModC_E`); the growth
  inequality and uniqueness of x* in T1(a) are proved from minimality (`growth_of_min`,
  `argmin_unique`).
* The product space (ℝ^d)^{N'} — `ι → X` with the product norm `ConsIter.pnorm`
  (= (Σ_j‖·‖²)^{1/2}; the Pi type's own norm is the sup norm and is not used).
* N = {j₀} ⊔ N' — `Option ι` (j₀ = `none`) when the iteration is fed to §2.
* μ̂ — `muHat σF σ`; ε — `epsC` (sum over J₀ᶜ, `epsC_eq_sum`: = sum over all j);
  τ — `tauC ‖r‖ ε μ̂`.
* dist(·, U_θ) — Mathlib `Metric.infDist` to `span{u_θ}`; `P2.infDist_eq` proves it is
  |⟨n_θ, ·⟩|.

STRENGTHENINGS: `quad_root` does not use t ≥ 0; T2(c) (`apriori_rate`) is proved for any
step α > 0 and without σ_𝔈^T ≥ 0 (both enter only through the classical hypotheses);
L3(a) (`fixed_argmin`) needs no Lipschitz attribute and allows every g_j extended-valued.

COVERAGE (dossier target → Lean name):
1. L0(a): `lip_modC_nonpos`, `lip_modC_nonpos_vec`, `lipAttr_sigma_eq_zero` (σ = 0 for a
   valid declaration); L0(b): `lipAttr_smul`, `extModC_smul`.
   L1(ii) first identity, elementary core: `parallel_axis`, `diag_prox_objective`.
2. L4: `consensus_minorant` (under the hypothesis bundle `HCert` = (H-cert)).
3. Quadratic-root step: `quad_root` (t ≤ τ ≤ b/μ + √(ε/μ)), `sqrt_add_le`.
4. T1(a) growth/uniqueness/convexity: `growth_of_min`, `argmin_unique`,
   `HCert.extModC_E`; T1(b),(c),(d): `consensus_certificate`; ε ≥ 0: `HCert.eps_nonneg`.
   Corollary T1-it: `ConsIter.cert_iter` (with `Typed.hcert`, `epsIt_le`).
5. L2(a): `ConsIter.readout_subgrad`; L2(b): `ConsIter.r_eq`; L2(c):
   `ConsIter.readout_bounds`; L2(d): `norm_subgrad_le`.
6. L3(a): `ConsIter.fixed_readouts` (p_j = x, r = 0), `ConsIter.fixed_argmin`;
   L3(b): `ConsIter.explicit_fixed_point`; L3(c) bound ‖u*_j‖ ≤ L_j: `norm_subgrad_le`.
7. P2: (a) `P2.valid`, `P2.typed` (same declared numbers for every θ), `P2.realises`;
   x* = 0: `P2.argmin_zero`; (b) `P2.step`, `P2.orbit` (z_k = cos^{2k}θ z₀,
   x_k = (−s sin θ cos^{2k}θ, 0), ‖x_k − x*‖ = cos^{2k}θ‖x₀ − x*‖), `P2.orbit_z`;
   (c) `P2.no_linear_rate`.
8. P1(i): `P1i.prop_P1_i`, `P1i.prop_P1_i_unbounded`; P1(ii): `P1ii.prop_P1_ii`;
   P1(iii): `P1iii.prop_P1_iii` (∂E(x) = {δ + 2L}); P1(iv): `P1iv.prop_P1_iv`,
   `P1iv.prop_P1_iv_ratio_tendsto` (τ/t → √2), `P1iv.prop_P1_iv_exponent` (exponent ½
   sharp).
9. T2(c) (dossier T2(d)): `ConsIter.apriori_rate`; the step count:
   `ConsIter.apriori_count`, `ConsIter.ebar_le_of_count`.

NOT FORMALISED (classical, cited; enter as hypotheses where used): existence of a
minimiser of E ((O3); B&C Cor. 11.17) — hypothesis of T1/T1-it/T2(c); the prox
characterisation B&C Prop. 16.44 for abstract g (hypothesis `Realises`); L1 (Davis–Yin
identification, ⅔-averagedness: Ryu–Yin Thm 28, Baillon–Haddad); L3(c) existence of u*
(Fermat + sum rule, B&C Thm 16.3, Cor. 16.48(iii)) — hypothesis of T2(c); T2(b) classical
convergence and the Krasnosel'skiĭ–Mann rate e_k² ≤ (2/(k+1))‖z₀ − z*‖² — hypothesis
`hKM` of T2(c); the instruction counts (Step 1.1, T1(e)) and the certificate-program
packaging (T1(e)); B&C Ex. 24.28 as a general formula (only the instance used in P2 is
checked); the scope remark R.

Status tier: FORMALISED (statement + proof, no sorry) for L0, L1(ii) elementary core, L2,
L3(a),(b), L4, T1(a) growth/uniqueness and T1(b)–(d) (given a minimiser), T1-it, P1(i)–(iv),
P2(a)–(c), T2(c)/(d) assembly (classical inputs as hypotheses). Axioms: only propext,
Classical.choice, Quot.sound (see #print axioms at the end).
-/
import Mathlib
import OcfVerification.A1DescentLemma
import OcfVerification.G3SoundnessQuadratic
import OcfVerification.H1DiscretePick

namespace OCF.H3

open Set Filter Topology Finset OCF.A1 OCF.G3

set_option linter.unusedSectionVars false

/-! ## Extended-valued terms, subgradients, the Lipschitz attribute -/

section Generic

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- The (σ-strong) subgradient inequality for the extended-valued function equal to `g` on
`D` and `+∞` off `D`: `p ∈ dom` and `g p + ⟨v, y − p⟩ + (σ/2)‖y − p‖² ≤ g y` for every
`y ∈ dom`. With `σ = 0` this is `v ∈ ∂g(p)` (B&C (16.1)). -/
def ExtSub (D : Set X) (g : X → ℝ) (σ : ℝ) (p v : X) : Prop :=
  p ∈ D ∧ ∀ y ∈ D, g p + inner ℝ v (y - p) + σ / 2 * ‖y - p‖ ^ 2 ≤ g y

/-- C(g, σ) for the extended-valued function (`g` on `D`, `+∞` off `D`):
`g − (σ/2)‖·‖²` is convex (on its convex domain). With `D = univ` this is G3's `ModC`. -/
def ExtModC (D : Set X) (g : X → ℝ) (σ : ℝ) : Prop :=
  ConvexOn ℝ D (fun x => g x - σ / 2 * ‖x‖ ^ 2)

/-- The Lipschitz attribute `L ∈ [0, ∞)` (Step 0.1): `g` real-valued on the whole space
and `|g x − g y| ≤ L‖x − y‖`. -/
def LipAttr (g : X → ℝ) (L : ℝ) : Prop :=
  0 ≤ L ∧ ∀ x y, |g x - g y| ≤ L * ‖x - y‖

lemma extModC_univ_iff [CompleteSpace X] (g : X → ℝ) (σ : ℝ) :
    ExtModC univ g σ ↔ ModC g σ := Iff.rfl

/-- **Lemma L0(a).** On a nontrivial space (d ≥ 1), a finite Lipschitz attribute and
C(g, σ) force σ ≤ 0. -/
theorem lip_modC_nonpos [Nontrivial X] {g : X → ℝ} {L σ : ℝ}
    (hL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖)
    (hC : ConvexOn ℝ univ (fun x => g x - σ / 2 * ‖x‖ ^ 2)) : σ ≤ 0 := by
  obtain ⟨u0, hu0⟩ := exists_ne (0 : X)
  set u : X := ‖u0‖⁻¹ • u0 with hu
  have hun : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hu0)]
  -- key inequality: σ t ≤ 2L for every t > 0
  have key : ∀ t : ℝ, 0 < t → σ * t ≤ 2 * L := by
    intro t ht
    have hconv := hC.2 (mem_univ (0 : X)) (mem_univ ((2 * t) • u))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hm : (1 / 2 : ℝ) • (0 : X) + (1 / 2 : ℝ) • ((2 * t) • u) = t • u := by
      rw [smul_zero, zero_add, smul_smul]; congr 1; ring
    simp only [smul_eq_mul] at hconv
    rw [hm] at hconv
    have n1 : ‖t • u‖ = t := by rw [norm_smul, hun, Real.norm_eq_abs, abs_of_pos ht, mul_one]
    have n2 : ‖(2 * t) • u‖ = 2 * t := by
      rw [norm_smul, hun, Real.norm_eq_abs, abs_of_pos (by linarith), mul_one]
    rw [n1, n2, norm_zero] at hconv
    have l1 := hL 0 (t • u)
    have l2 := hL ((2 * t) • u) (t • u)
    rw [zero_sub, norm_neg, n1] at l1
    have e : (2 * t) • u - t • u = t • u := by rw [← sub_smul]; congr 1; ring
    rw [e, n1] at l2
    have a1 := le_abs_self (g 0 - g (t • u))
    have a2 := le_abs_self (g ((2 * t) • u) - g (t • u))
    have : σ / 2 * t ^ 2 ≤ L * t := by nlinarith
    nlinarith
  by_contra hσ
  push Not at hσ
  have h := key ((2 * |L| + 1) / σ) (by positivity)
  rw [mul_div_cancel₀ _ hσ.ne'] at h
  linarith [le_abs_self L]

/-- **Lemma L0(a), consequence.** A valid declaration (σ ≥ 0) with a finite Lipschitz
attribute has σ = 0. -/
theorem lipAttr_sigma_eq_zero [Nontrivial X] [CompleteSpace X] {g : X → ℝ} {L σ : ℝ}
    (hL : LipAttr g L) (hC : ModC g σ) (hσ : 0 ≤ σ) : σ = 0 :=
  le_antisymm (lip_modC_nonpos hL.2 hC) hσ

/-- **Lemma L0(a)** on ℝ^d, d ≥ 1. -/
theorem lip_modC_nonpos_vec {d : ℕ} (hd : 1 ≤ d) {g : Vec d → ℝ} {L σ : ℝ}
    (hL : ∀ x y, |g x - g y| ≤ L * ‖x - y‖) (hC : ModC g σ) : σ ≤ 0 :=
  haveI := nontrivial_vec (d := d) (by omega)
  lip_modC_nonpos hL hC

/-- **Lemma L0(b)** (weighting rule, Lipschitz and curvature components): if `(σ, L)` is
valid for `g` and `w > 0`, then `(wσ, wL)` is valid for `wg`. (The domain component is
unchanged; the prox component is lem:rule-sum(d), landed.) -/
theorem lipAttr_smul {g : X → ℝ} {L w : ℝ} (hw : 0 < w) (hL : LipAttr g L) :
    LipAttr (fun x => w * g x) (w * L) := by
  refine ⟨mul_nonneg hw.le hL.1, fun x y => ?_⟩
  rw [← mul_sub, abs_mul, abs_of_pos hw, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hL.2 x y) hw.le

theorem extModC_smul {D : Set X} {g : X → ℝ} {σ w : ℝ} (hw : 0 < w) (hC : ExtModC D g σ) :
    ExtModC D (fun x => w * g x) (w * σ) := by
  have h := hC.smul hw.le
  refine h.congr fun x _ => ?_
  simp only [smul_eq_mul]
  ring

/-- (C2) for extended-valued terms (Beck Thm 5.24 (i)⇒(ii), classical; proved here):
C(g, σ) and `v ∈ ∂g(p)` give the σ-strong subgradient inequality at `(p, v)`. -/
theorem extSub_strong {D : Set X} {g : X → ℝ} {σ : ℝ} {p v : X}
    (hC : ExtModC D g σ) (hs : ExtSub D g 0 p v) : ExtSub D g σ p v := by
  refine ⟨hs.1, fun y hy => ?_⟩
  set u := y - p with hu
  -- for every t ∈ (0, 1]: A ≤ B + c t
  have hgen : ∀ t : ℝ, 0 < t → t ≤ 1 →
      g p + inner ℝ v u + σ / 2 * ‖u‖ ^ 2 ≤ g y + σ / 2 * ‖u‖ ^ 2 * t := by
    intro t ht0 ht1
    have hconv := hC.2 hs.1 hy (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
    have hpt : (1 - t) • p + t • y = p + t • u := by rw [hu, smul_sub, sub_smul, one_smul]; abel
    rw [hpt] at hconv
    simp only [smul_eq_mul] at hconv
    have hmem : p + t • u ∈ D := by
      rw [← hpt]; exact hC.1 hs.1 hy (by linarith) ht0.le (by ring)
    have hsub := hs.2 _ hmem
    rw [add_sub_cancel_left, inner_smul_right] at hsub
    have ny : ‖y‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p u + ‖u‖ ^ 2 := by
      have : y = p + u := by rw [hu]; abel
      rw [this, norm_add_sq_real]
    have npt : ‖p + t • u‖ ^ 2 = ‖p‖ ^ 2 + 2 * (t * inner ℝ p u) + t ^ 2 * ‖u‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    rw [npt] at hconv
    rw [ny] at hconv
    -- hsub: g p + t ⟨v,u⟩ ≤ g(p + t u); hconv: g(p+tu) − … ≤ …
    have hlin : t * (g p + inner ℝ v u + σ / 2 * ‖u‖ ^ 2)
        ≤ t * (g y + σ / 2 * ‖u‖ ^ 2 * t) := by nlinarith
    exact le_of_mul_le_mul_left hlin ht0
  -- conclude A ≤ B
  have hfin : g p + inner ℝ v u + σ / 2 * ‖u‖ ^ 2 ≤ g y := by
    refine le_of_forall_pos_lt_add fun ε hε => ?_
    set c := σ / 2 * ‖u‖ ^ 2
    set t := min 1 (ε / (|c| + 1)) with ht
    have ht0 : 0 < t := lt_min one_pos (by positivity)
    have ht1 : t ≤ 1 := min_le_left _ _
    have h := hgen t ht0 ht1
    have hct : c * t ≤ |c| * t := mul_le_mul_of_nonneg_right (le_abs_self c) ht0.le
    have htε : t ≤ ε / (|c| + 1) := min_le_right _ _
    have : |c| * t < ε := by
      have h1 : |c| * t ≤ |c| * (ε / (|c| + 1)) := mul_le_mul_of_nonneg_left htε (abs_nonneg c)
      have h2 : |c| * (ε / (|c| + 1)) < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]; nlinarith [abs_nonneg c]
      linarith
    linarith
  simpa [hu] using hfin

/-- Monotonicity of the subgradient: if `v ∈ ∂g(p)` and `v' ∈ ∂g(p')` then
`⟨v − v', p − p'⟩ ≥ 0`. -/
lemma extSub_monotone {D : Set X} {g : X → ℝ} {p p' v v' : X}
    (h : ExtSub D g 0 p v) (h' : ExtSub D g 0 p' v') : 0 ≤ inner ℝ (v - v') (p - p') := by
  have a := h.2 p' h'.1
  have b := h'.2 p h.1
  simp only [zero_div, zero_mul, add_zero] at a b
  have e1 : inner ℝ v (p' - p) = - inner ℝ v (p - p') := by rw [← inner_neg_right, neg_sub]
  rw [e1] at a
  rw [inner_sub_left]
  linarith

/-- Prox characterisation from a realising map (B&C Prop. 16.44 shape): if `P y` satisfies
`(y − P y)/a ∈ ∂g(P y)` for every `y`, then `P y = q ⟺ (y − q)/a ∈ ∂g(q)`
(uniqueness by monotonicity). -/
theorem proxChar_of_forall {D : Set X} {g : X → ℝ} {a : ℝ} (ha : 0 < a) {P : X → X}
    (hP : ∀ y, ExtSub D g 0 (P y) (a⁻¹ • (y - P y))) :
    ∀ y q, P y = q ↔ ExtSub D g 0 q (a⁻¹ • (y - q)) := by
  intro y q
  refine ⟨fun h => h ▸ hP y, fun hq => ?_⟩
  have hm := extSub_monotone (hP y) hq
  have e : a⁻¹ • (y - P y) - a⁻¹ • (y - q) = -(a⁻¹ • (P y - q)) := by
    rw [← smul_sub, ← smul_neg]; congr 1; abel
  rw [e, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hm
  have : ‖P y - q‖ ^ 2 ≤ 0 := by
    have hpos : 0 < a⁻¹ := inv_pos.2 ha
    nlinarith [sq_nonneg ‖P y - q‖]
  have : ‖P y - q‖ = 0 := by nlinarith [norm_nonneg (P y - q)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Lemma L2(d)** (one direction of Beck Thm 3.61(b), proved): a subgradient of an
`L`-Lipschitz real-valued function has norm at most `L`. -/
theorem norm_subgrad_le {g : X → ℝ} {L : ℝ} {p v : X} (hL : LipAttr g L)
    (hs : ExtSub univ g 0 p v) : ‖v‖ ≤ L := by
  have h := hs.2 (p + v) (mem_univ _)
  simp only [add_sub_cancel_left, real_inner_self_eq_norm_sq, zero_div, zero_mul,
    add_zero] at h
  have hl := hL.2 (p + v) p
  rw [add_sub_cancel_left] at hl
  have h2 : ‖v‖ ^ 2 ≤ L * ‖v‖ := by linarith [le_abs_self (g (p + v) - g p)]
  rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
  · rw [← h0]; exact hL.1
  · nlinarith

/-- ∇((σ/2)‖·‖²)(x) = σx. -/
lemma gradient_halfSq [CompleteSpace X] (σ : ℝ) (x : X) :
    gradient (fun y : X => σ / 2 * ‖y‖ ^ 2) x = σ • x := by
  have h := hasGradientAt_sub_sq (f := fun _ : X => (0 : ℝ)) (differentiableAt_const 0) (-σ)
    (x := x)
  have e : (fun y : X => (fun _ : X => (0 : ℝ)) y - -σ / 2 * ‖y‖ ^ 2)
      = fun y : X => σ / 2 * ‖y‖ ^ 2 := by funext y; ring
  rw [e] at h
  rw [h.gradient]
  have : gradient (fun _ : X => (0 : ℝ)) x = 0 := gradient_const x (0 : ℝ)
  rw [this, zero_sub, neg_smul, neg_neg]

lemma differentiable_halfSq [CompleteSpace X] (σ : ℝ) :
    Differentiable ℝ (fun y : X => σ / 2 * ‖y‖ ^ 2) := by
  have h := differentiable_sub_sq (f := fun _ : X => (0 : ℝ)) (differentiable_const 0) (-σ)
  have e : (fun y : X => (fun _ : X => (0 : ℝ)) y - -σ / 2 * ‖y‖ ^ 2)
      = fun y : X => σ / 2 * ‖y‖ ^ 2 := by funext y; ring
  rwa [e] at h

lemma modC_halfSq [CompleteSpace X] (σ : ℝ) : ModC (fun y : X => σ / 2 * ‖y‖ ^ 2) σ := by
  unfold ModC
  have : (fun x : X => σ / 2 * ‖x‖ ^ 2 - σ / 2 * ‖x‖ ^ 2) = fun _ => (0 : ℝ) := by
    funext x; ring
  rw [this]; exact convexOn_const 0 convex_univ

end Generic

/-! ## The quadratic-root step (target 3) -/

lemma sqrt_add_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : √(a + b) ≤ √a + √b := by
  have h : a + b ≤ (√a + √b) ^ 2 := by
    have := Real.sq_sqrt ha; have := Real.sq_sqrt hb
    nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b]
  calc √(a + b) ≤ √((√a + √b) ^ 2) := Real.sqrt_le_sqrt h
    _ = √a + √b := Real.sqrt_sq (by positivity)

/-- τ := (b + √(b² + 4με))/(2μ), the larger root of μs² − bs − ε. -/
noncomputable def tauC (b ε μ : ℝ) : ℝ := (b + √(b ^ 2 + 4 * μ * ε)) / (2 * μ)

/-- **Target 3.** μ > 0, t ≥ 0, ε ≥ 0, b ≥ 0, μt² ≤ bt + ε ⇒ t ≤ τ ≤ b/μ + √(ε/μ). -/
theorem quad_root {μ b ε t : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hε : 0 ≤ ε) (_ht : 0 ≤ t)
    (h : μ * t ^ 2 ≤ b * t + ε) : t ≤ tauC b ε μ ∧ tauC b ε μ ≤ b / μ + √(ε / μ) := by
  have hS := Real.sqrt_nonneg (b ^ 2 + 4 * μ * ε)
  have hSS := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ b ^ 2 + 4 * μ * ε)
  constructor
  · unfold tauC
    rw [le_div_iff₀ (by positivity)]
    have h1 : (2 * μ * t - b) ^ 2 ≤ (√(b ^ 2 + 4 * μ * ε)) ^ 2 := by rw [hSS]; nlinarith
    have h2 := (abs_le_of_sq_le_sq' h1 hS).2
    linarith
  · unfold tauC
    have hsq : √(b ^ 2 + 4 * μ * ε) ≤ b + 2 * μ * √(ε / μ) := by
      calc √(b ^ 2 + 4 * μ * ε) ≤ √(b ^ 2) + √(4 * μ * ε) :=
            sqrt_add_le _ _ (sq_nonneg b) (by positivity)
        _ = b + 2 * μ * √(ε / μ) := by
            rw [Real.sqrt_sq hb]
            congr 1
            have : 4 * μ * ε = (2 * μ) ^ 2 * (ε / μ) := by field_simp; ring
            rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [div_le_iff₀ (by positivity)]
    have : (b / μ + √(ε / μ)) * (2 * μ) = 2 * b + 2 * μ * √(ε / μ) := by
      field_simp
    rw [this]; linarith

/-! ## §2: the consensus minorant (L4) and the consensus-gap certificate (T1) -/

section Cert

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {N : Type*} [Fintype N]

/-- dom E = ⋂_j dom g_j (F is real-valued). -/
def domE (D : N → Set X) : Set X := {y | ∀ j, y ∈ D j}

/-- E = F + Σ_j g_j on dom E (finite parts). -/
def Eval (F : X → ℝ) (g : N → X → ℝ) (y : X) : ℝ := F y + ∑ j, g j y

/-- r := ∇F(x) + Σ_j v_j. -/
noncomputable def resid (F : X → ℝ) (v : N → X) (x : X) : X := gradient F x + ∑ j, v j

open Classical in
/-- ε := Σ_{j ∉ J₀} (‖v_j‖ + L_j) δ_j, J₀ = {j : p_j = x}, δ_j = ‖p_j − x‖. -/
noncomputable def epsC (x : X) (p v : N → X) (L : N → ℝ) : ℝ :=
  ∑ j ∈ univ.filter (fun j => p j ≠ x), (‖v j‖ + L j) * ‖p j - x‖

/-- The terms with `p_j = x` contribute zero, so ε is also the sum over all j. -/
lemma epsC_eq_sum (x : X) (p v : N → X) (L : N → ℝ) :
    epsC x p v L = ∑ j, (‖v j‖ + L j) * ‖p j - x‖ := by
  classical
  unfold epsC
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with h
  · rfl
  · push Not at h; rw [h, sub_self, norm_zero, mul_zero]

/-- μ̂ := σ_F + Σ_j σ_j. -/
def muHat (σF : ℝ) (σ : N → ℝ) : ℝ := σF + ∑ j, σ j

/-- The standing hypotheses (H-cert) of §2, with the convex-analytic inputs in inequality
form: F is C¹ (differentiable suffices) with C(F, σ_F), σ_F ∈ ℝ; each g_j is the
extended-valued function (`g j` on `D j`, `+∞` off it) with C(g_j, σ_j), σ_j ≥ 0;
`v_j ∈ ∂g_j(p_j)`; (H-Lip) each g_j with `p_j ≠ x` is real-valued (`D j = univ`) and
carries a finite Lipschitz attribute `L_j`. -/
structure HCert (F : X → ℝ) (σF : ℝ) (D : N → Set X) (g : N → X → ℝ) (σ L : N → ℝ)
    (x : X) (p v : N → X) : Prop where
  diffF : Differentiable ℝ F
  curvF : ModC F σF
  curv : ∀ j, ExtModC (D j) (g j) (σ j)
  sigma_nonneg : ∀ j, 0 ≤ σ j
  subgrad : ∀ j, ExtSub (D j) (g j) 0 (p j) (v j)
  lip : ∀ j, p j ≠ x → D j = univ ∧ LipAttr (g j) (L j)

variable {F : X → ℝ} {σF : ℝ} {D : N → Set X} {g : N → X → ℝ} {σ L : N → ℝ} {x : X}
  {p v : N → X}

lemma HCert.eps_nonneg (h : HCert F σF D g σ L x p v) : 0 ≤ epsC x p v L := by
  classical
  unfold epsC
  refine Finset.sum_nonneg fun j hj => ?_
  have hj' : p j ≠ x := (Finset.mem_filter.1 hj).2
  have := (h.lip j hj').2.1
  positivity

/-- Per-term bound used in (M). -/
lemma HCert.term [Nontrivial X] (h : HCert F σF D g σ L x p v) (j : N) {y : X}
    (hy : y ∈ D j) :
    g j x + inner ℝ (v j) (y - x) + σ j / 2 * ‖y - x‖ ^ 2
      - (‖v j‖ + L j) * ‖p j - x‖ ≤ g j y := by
  by_cases hj : p j = x
  · have hs := extSub_strong (h.curv j) (h.subgrad j)
    rw [hj] at hs
    have := hs.2 y hy
    rw [hj, sub_self, norm_zero, mul_zero, sub_zero]
    exact this
  · obtain ⟨hD, hL⟩ := h.lip j hj
    have hC : ModC (g j) (σ j) := by have := h.curv j; rwa [hD] at this
    have hσ0 := lipAttr_sigma_eq_zero hL hC (h.sigma_nonneg j)
    have hs := (h.subgrad j).2 y (hD ▸ mem_univ y)
    simp only [zero_div, zero_mul, add_zero] at hs
    rw [hσ0, zero_div, zero_mul, add_zero]
    have e : inner ℝ (v j) (y - p j) = inner ℝ (v j) (y - x) + inner ℝ (v j) (x - p j) := by
      rw [← inner_add_right]; congr 1; abel
    rw [e] at hs
    have c1 : -(‖v j‖ * ‖p j - x‖) ≤ inner ℝ (v j) (x - p j) := by
      have := abs_real_inner_le_norm (v j) (x - p j)
      rw [norm_sub_rev] at this; exact neg_le_of_abs_le this
    have c2 := hL.2 (p j) x
    have c3 := neg_abs_le (g j (p j) - g j x)
    nlinarith

/-- **Lemma L4 (consensus minorant).** Under (H-cert): `x ∈ dom E` and, for every
`y ∈ dom E` (off dom E, E(y) = +∞ and (M) is trivial),
E(y) ≥ E(x) + ⟨r, y − x⟩ + (μ̂/2)‖y − x‖² − ε. -/
theorem consensus_minorant [Nontrivial X] (h : HCert F σF D g σ L x p v) :
    x ∈ domE D ∧ ∀ y ∈ domE D,
      Eval F g x + inner ℝ (resid F v x) (y - x) + muHat σF σ / 2 * ‖y - x‖ ^ 2
        - epsC x p v L ≤ Eval F g y := by
  refine ⟨fun j => ?_, fun y hy => ?_⟩
  · by_cases hj : p j = x
    · rw [← hj]; exact (h.subgrad j).1
    · rw [(h.lip j hj).1]; exact mem_univ x
  · have hF := OCF.H1.strongSubgrad_of_modC h.diffF h.curvF x y
    have hsum : ∑ j, (g j x + inner ℝ (v j) (y - x) + σ j / 2 * ‖y - x‖ ^ 2
        - (‖v j‖ + L j) * ‖p j - x‖) ≤ ∑ j, g j y :=
      Finset.sum_le_sum fun j _ => h.term j (hy j)
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← sum_inner, ← Finset.sum_mul, ← Finset.sum_div] at hsum
    rw [epsC_eq_sum]
    unfold Eval resid muHat
    rw [inner_add_left]
    linarith

/-- E − (μ̂/2)‖·‖² is convex on dom E (B&C Prop. 8.17; proved). -/
lemma HCert.extModC_E (h : HCert F σF D g σ L x p v) :
    ExtModC (domE D) (Eval F g) (muHat σF σ) := by
  classical
  have hconv : Convex ℝ (domE D) := by
    have : domE D = ⋂ j, D j := by ext y; simp [domE]
    rw [this]; exact convex_iInter fun j => (h.curv j).1
  have hsum : ∀ s : Finset N, ConvexOn ℝ (domE D)
      (fun y => ∑ j ∈ s, (g j y - σ j / 2 * ‖y‖ ^ 2)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) hconv
    | insert a s ha ih =>
      have ha' : ConvexOn ℝ (domE D) (fun y => g a y - σ a / 2 * ‖y‖ ^ 2) :=
        (h.curv a).subset (fun y hy => hy a) hconv
      refine (ha'.add ih).congr fun y _ => ?_
      rw [Pi.add_apply, Finset.sum_insert ha]
  have hF : ConvexOn ℝ (domE D) (fun y => F y - σF / 2 * ‖y‖ ^ 2) :=
    h.curvF.subset (subset_univ _) hconv
  refine ((hF.add (hsum univ))).congr fun y _ => ?_
  rw [Pi.add_apply]
  simp only [Eval, muHat, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  ring

/-- **Theorem T1(a), growth part.** If x* minimises E over dom E and μ̂ is the modulus,
then E(y) ≥ E(x*) + (μ̂/2)‖y − x*‖² on dom E (Fermat + (C2) for E). With μ̂ > 0 the
minimiser is unique: argmin E = {x*}. -/
theorem growth_of_min (h : HCert F σF D g σ L x p v) {xs : X} (hxs : xs ∈ domE D)
    (hmin : ∀ y ∈ domE D, Eval F g xs ≤ Eval F g y) :
    ∀ y ∈ domE D, Eval F g xs + muHat σF σ / 2 * ‖y - xs‖ ^ 2 ≤ Eval F g y := by
  have h0 : ExtSub (domE D) (Eval F g) 0 xs 0 :=
    ⟨hxs, fun y hy => by simpa using hmin y hy⟩
  have hs := extSub_strong h.extModC_E h0
  intro y hy
  simpa using hs.2 y hy

theorem argmin_unique (h : HCert F σF D g σ L x p v) (hμ : 0 < muHat σF σ) {xs : X}
    (hxs : xs ∈ domE D) (hmin : ∀ y ∈ domE D, Eval F g xs ≤ Eval F g y) :
    ∀ y ∈ domE D, ((∀ y' ∈ domE D, Eval F g y ≤ Eval F g y') ↔ y = xs) := by
  intro y hy
  refine ⟨fun hy' => ?_, fun e => e ▸ hmin⟩
  have h1 := growth_of_min h hxs hmin y hy
  have h2 := hy' xs hxs
  have : ‖y - xs‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖y - xs‖ = 0 := by nlinarith [norm_nonneg (y - xs)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- **Theorem T1(b),(c),(d) (consensus-gap certificate).** Under (H-cert) with μ̂ > 0, let
x* be a minimiser of E (existence: B&C Cor. 11.17, classical, hypothesis). Then
(b) ‖x − x*‖ ≤ τ ≤ ‖r‖/μ̂ + √(ε/μ̂) and ‖p_j − x*‖ ≤ τ + δ_j for every j;
(c) E(x) − E(x*) ≤ ‖r‖²/(2μ̂) + ε;
(d) if J₀ = N (every p_j = x) then ε = 0 and τ = ‖r‖/μ̂. -/
theorem consensus_certificate [Nontrivial X] (h : HCert F σF D g σ L x p v)
    (hμ : 0 < muHat σF σ) {xs : X} (hxs : xs ∈ domE D)
    (hmin : ∀ y ∈ domE D, Eval F g xs ≤ Eval F g y) :
    (‖x - xs‖ ≤ tauC ‖resid F v x‖ (epsC x p v L) (muHat σF σ) ∧
      tauC ‖resid F v x‖ (epsC x p v L) (muHat σF σ)
        ≤ ‖resid F v x‖ / muHat σF σ + √(epsC x p v L / muHat σF σ) ∧
      ∀ j, ‖p j - xs‖ ≤ tauC ‖resid F v x‖ (epsC x p v L) (muHat σF σ) + ‖p j - x‖) ∧
    Eval F g x - Eval F g xs ≤ ‖resid F v x‖ ^ 2 / (2 * muHat σF σ) + epsC x p v L ∧
    ((∀ j, p j = x) → epsC x p v L = 0 ∧
      tauC ‖resid F v x‖ (epsC x p v L) (muHat σF σ) = ‖resid F v x‖ / muHat σF σ) := by
  obtain ⟨hx, hM⟩ := consensus_minorant h
  have hε := h.eps_nonneg
  set r := resid F v x
  set ε := epsC x p v L
  set μ := muHat σF σ
  have hgr := growth_of_min h hxs hmin x hx
  have hMs := hM xs hxs
  have hcs : -(‖r‖ * ‖xs - x‖) ≤ inner ℝ r (xs - x) :=
    neg_le_of_abs_le (abs_real_inner_le_norm r (xs - x))
  rw [norm_sub_rev xs x] at hcs hMs
  have hq : μ * ‖x - xs‖ ^ 2 ≤ ‖r‖ * ‖x - xs‖ + ε := by nlinarith
  obtain ⟨h1, h2⟩ := quad_root hμ (norm_nonneg r) hε (norm_nonneg _) hq
  refine ⟨⟨h1, h2, fun j => ?_⟩, ?_, fun hJ => ?_⟩
  · have := norm_sub_le_norm_sub_add_norm_sub (p j) x xs
    linarith
  · have := OCF.H1.complete_square r (xs - x) hμ
    have hMs' := hM xs hxs
    linarith
  · have hε0 : ε = 0 := by
      simp only [ε, epsC_eq_sum, hJ, sub_self, norm_zero, mul_zero, Finset.sum_const_zero]
    refine ⟨hε0, ?_⟩
    unfold tauC
    rw [hε0, mul_zero, add_zero, Real.sqrt_sq (norm_nonneg r)]
    field_simp
    ring

end Cert

/-! ## D2: the constructed consensus iteration; L2 read-outs; L3 fixed points -/

section Iteration

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {ι : Type*} [Fintype ι]

/-- The data the constructed iteration reads (D2), on the state space (ℝ^d)^{N'} with
`N' = ι`, `m' = |ι|`: the smooth part `F` (through ∇F), the step `α`, and the two prox
programs `prox0 = prox_{α g_{j₀}}` and `prox j = prox_{m'α g_j}` (any maps; their
meaning enters through `Realises`). -/
structure ConsIter (X : Type*) [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (ι : Type*) where
  F : X → ℝ
  α : ℝ
  prox0 : X → X
  prox : ι → X → X

namespace ConsIter

variable (C : ConsIter X ι)

/-- m' = |N'|. -/
def mP (ι : Type*) [Fintype ι] : ℝ := (Fintype.card ι : ℝ)

/-- z̄ = (1/m') Σ_j z_j. -/
noncomputable def zbar (z : ι → X) : X := (mP ι)⁻¹ • ∑ j, z j
/-- x_k = prox_{α g_{j₀}}(z̄_k). -/
noncomputable def x (z : ι → X) : X := C.prox0 (zbar z)
/-- w_{j,k} = 2x_k − z_{j,k} − α∇F(x_k). -/
noncomputable def w (z : ι → X) (j : ι) : X := (2 : ℝ) • C.x z - z j - C.α • gradient C.F (C.x z)
/-- p_{j,k} = prox_{m'α g_j}(w_{j,k}). -/
noncomputable def p (z : ι → X) (j : ι) : X := C.prox j (C.w z j)
/-- z_{j,k+1} = z_{j,k} + p_{j,k} − x_k. -/
noncomputable def T (z : ι → X) : ι → X := fun j => z j + C.p z j - C.x z
/-- v_{j₀,k} = (z̄_k − x_k)/α. -/
noncomputable def v0 (z : ι → X) : X := C.α⁻¹ • (zbar z - C.x z)
/-- v_{j,k} = (w_{j,k} − p_{j,k})/(m'α). -/
noncomputable def v (z : ι → X) (j : ι) : X := (mP ι * C.α)⁻¹ • (C.w z j - C.p z j)
/-- r_k = ∇F(x_k) + v_{j₀,k} + Σ_{N'} v_{j,k}. -/
noncomputable def r (z : ι → X) : X := gradient C.F (C.x z) + C.v0 z + ∑ j, C.v z j
/-- p̄_k = (1/m') Σ_j p_{j,k}. -/
noncomputable def pbar (z : ι → X) : X := (mP ι)⁻¹ • ∑ j, C.p z j
/-- The product norm on (ℝ^d)^{N'}: (Σ_j ‖y_j‖²)^{1/2}. -/
noncomputable def pnorm (y : ι → X) : ℝ := √(∑ j, ‖y j‖ ^ 2)
/-- e_k = ‖z_{k+1} − z_k‖ (product norm). -/
noncomputable def e (z : ι → X) : ℝ := pnorm (fun j => C.T z j - z j)
/-- ε_k = Σ_{N'} (ρ_{j,k} + L_j) δ_{j,k}. -/
noncomputable def epsIt (L : ι → ℝ) (z : ι → X) : ℝ :=
  ∑ j, (‖C.v z j‖ + L j) * ‖C.p z j - C.x z‖
/-- The iterates z_k = T^k z₀. -/
noncomputable def iter (z0 : ι → X) (k : ℕ) : ι → X := C.T^[k] z0

/-- The prox programs realise the declared terms (B&C Prop. 16.44 with Prop. 16.6(i),
classical, as hypotheses): `prox_{ag}(y) = q ⟺ (y − q)/a ∈ ∂g(q)`, for `g_{j₀}` (`g0` on
`D0`) with `a = α` and for `g_j` (`gj j` on `Dj j`) with `a = m'α`. -/
structure Realises (D0 : Set X) (g0 : X → ℝ) (Dj : ι → Set X) (gj : ι → X → ℝ) : Prop where
  prox0 : ∀ y q, C.prox0 y = q ↔ ExtSub D0 g0 0 q (C.α⁻¹ • (y - q))
  prox : ∀ j y q, C.prox j y = q ↔ ExtSub (Dj j) (gj j) 0 q ((mP ι * C.α)⁻¹ • (y - q))

variable {C}

/-- **Lemma L2(a).** The read-outs are subgradients: v_{j₀,k} ∈ ∂g_{j₀}(x_k) (so
x_k ∈ dom g_{j₀}) and v_{j,k} ∈ ∂g_j(p_{j,k}). -/
theorem readout_subgrad {D0 : Set X} {g0 : X → ℝ} {Dj : ι → Set X} {gj : ι → X → ℝ}
    (hR : C.Realises D0 g0 Dj gj) (z : ι → X) :
    ExtSub D0 g0 0 (C.x z) (C.v0 z) ∧ ∀ j, ExtSub (Dj j) (gj j) 0 (C.p z j) (C.v z j) :=
  ⟨(hR.prox0 _ _).1 rfl, fun j => (hR.prox j _ _).1 rfl⟩

lemma mP_pos [Nonempty ι] : 0 < mP ι := by unfold mP; exact_mod_cast Fintype.card_pos

lemma sum_eq_mP_smul_zbar [Nonempty ι] (z : ι → X) : ∑ j, z j = mP ι • zbar z := by
  unfold zbar; rw [smul_smul, mul_inv_cancel₀ mP_pos.ne', one_smul]

/-- **Lemma L1(ii), first identity (novel glue), elementary core.** The parallel-axis
identity Σ_j ‖u − z_j‖² = m'‖u − z̄‖² + Σ_j ‖z_j − z̄‖². -/
theorem parallel_axis [Nonempty ι] (u : X) (z : ι → X) :
    ∑ j, ‖u - z j‖ ^ 2 = mP ι * ‖u - zbar z‖ ^ 2 + ∑ j, ‖z j - zbar z‖ ^ 2 := by
  have hm := (mP_pos (ι := ι)).ne'
  have hsum : ∑ j, (z j - zbar z) = 0 := by
    rw [Finset.sum_sub_distrib, sum_eq_mP_smul_zbar, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ]
    simp [mP]
  have e : ∀ j, ‖u - z j‖ ^ 2 = ‖u - zbar z‖ ^ 2 - 2 * inner ℝ (u - zbar z) (z j - zbar z)
      + ‖z j - zbar z‖ ^ 2 := by
    intro j
    rw [show u - z j = (u - zbar z) - (z j - zbar z) by abel, norm_sub_sq_real]
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    ← inner_sum, hsum, inner_zero_right, mul_zero, sub_zero, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mP]

/-- **Lemma L1(ii), first identity.** Consequently, on the diagonal, the objective of
prox_{γΨ} at z, g(u) + (1/(2γ))Σ_j‖u − z_j‖² with γ = m'α, differs from that of
prox_{αg}(z̄), g(u) + (1/(2α))‖u − z̄‖², by a constant independent of u; so the two
minimisation problems have the same minimisers. -/
theorem diag_prox_objective [Nonempty ι] (g : X → ℝ) {α : ℝ} (hα : α ≠ 0) (z : ι → X) :
    ∃ c : ℝ, ∀ u : X, g u + 1 / (2 * (mP ι * α)) * ∑ j, ‖u - z j‖ ^ 2
      = g u + 1 / (2 * α) * ‖u - zbar z‖ ^ 2 + c := by
  have hm := (mP_pos (ι := ι)).ne'
  refine ⟨1 / (2 * (mP ι * α)) * ∑ j, ‖z j - zbar z‖ ^ 2, fun u => ?_⟩
  rw [parallel_axis]
  field_simp
  ring

/-- **Lemma L2(b).** r_k = (x_k − p̄_k)/α. -/
theorem r_eq [Nonempty ι] (hα : C.α ≠ 0) (z : ι → X) :
    C.r z = C.α⁻¹ • (C.x z - C.pbar z) := by
  have hm := (mP_pos (ι := ι)).ne'
  have hsw : ∑ j, C.v z j = (mP ι * C.α)⁻¹ • (mP ι • ((2 : ℝ) • C.x z
      - C.α • gradient C.F (C.x z)) - ∑ j, z j - ∑ j, C.p z j) := by
    unfold v w
    rw [← Finset.smul_sum]
    congr 1
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, mP]
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ, smul_sub]
    abel
  have hz := sum_eq_mP_smul_zbar z
  have hp : ∑ j, C.p z j = mP ι • C.pbar z := by
    unfold pbar; rw [smul_smul, mul_inv_cancel₀ hm, one_smul]
  unfold r v0
  rw [hsw, hz, hp]
  set G := gradient C.F (C.x z)
  set a := C.α
  set m := mP ι
  rw [← smul_sub, ← smul_sub, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ hm, mul_one]
  rw [smul_sub, smul_sub, smul_sub, smul_sub, smul_sub, smul_smul a⁻¹ a, inv_mul_cancel₀ hα,
    one_smul]
  module

/-- **Lemma L2(c).** z_{j,k+1} − z_{j,k} = p_{j,k} − x_k, so δ_{j,k} = ‖z_{j,k+1} − z_{j,k}‖,
Σ_j δ_{j,k}² = e_k², and ‖r_k‖ ≤ e_k/(α√m'). -/
theorem readout_bounds [Nonempty ι] (hα : 0 < C.α) (z : ι → X) :
    (∀ j, C.T z j - z j = C.p z j - C.x z) ∧
    ∑ j, ‖C.p z j - C.x z‖ ^ 2 = C.e z ^ 2 ∧
    ‖C.r z‖ ≤ C.e z / (C.α * √(mP ι)) := by
  have hT : ∀ j, C.T z j - z j = C.p z j - C.x z := fun j => by unfold T; abel
  have hsq : ∑ j, ‖C.p z j - C.x z‖ ^ 2 = C.e z ^ 2 := by
    unfold e pnorm
    rw [Real.sq_sqrt (Finset.sum_nonneg fun j _ => by positivity)]
    simp only [hT]
  refine ⟨hT, hsq, ?_⟩
  have hm := mP_pos (ι := ι)
  have hsm : 0 < √(mP ι) := Real.sqrt_pos.2 hm
  rw [r_eq hα.ne' z, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hα)]
  -- ‖x − p̄‖ ≤ e/√m'
  have h1 : C.x z - C.pbar z = (mP ι)⁻¹ • ∑ j, (C.x z - C.p z j) := by
    unfold pbar
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, smul_sub,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp only [mP]
    rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  have h2 : ‖∑ j, (C.x z - C.p z j)‖ ≤ ∑ j, ‖C.p z j - C.x z‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    simp only [norm_sub_rev]
  have h3 : ∑ j, ‖C.p z j - C.x z‖ ≤ √(mP ι) * C.e z := by
    have := Real.sum_mul_le_sqrt_mul_sqrt univ (fun _ => (1 : ℝ)) (fun j => ‖C.p z j - C.x z‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at this
    have he : 0 ≤ C.e z := Real.sqrt_nonneg _
    rw [hsq, Real.sqrt_sq he] at this
    simpa [mP] using this
  have hx : ‖C.x z - C.pbar z‖ ≤ C.e z / √(mP ι) := by
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hm)]
    rw [le_div_iff₀ hsm]
    have hmm : (mP ι)⁻¹ * √(mP ι) * √(mP ι) = 1 := by
      rw [mul_assoc, Real.mul_self_sqrt hm.le, inv_mul_cancel₀ hm.ne']
    calc (mP ι)⁻¹ * ‖∑ j, (C.x z - C.p z j)‖ * √(mP ι)
        ≤ (mP ι)⁻¹ * (√(mP ι) * C.e z) * √(mP ι) := by gcongr; exact h2.trans h3
      _ = C.e z := by rw [show (mP ι)⁻¹ * (√(mP ι) * C.e z) * √(mP ι)
            = (mP ι)⁻¹ * √(mP ι) * √(mP ι) * C.e z by ring, hmm, one_mul]
  calc C.α⁻¹ * ‖C.x z - C.pbar z‖ ≤ C.α⁻¹ * (C.e z / √(mP ι)) := by gcongr
    _ = C.e z / (C.α * √(mP ι)) := by field_simp

/-- **Lemma L3(a), algebraic part.** At a fixed point, p_j = x for every j and r = 0. -/
theorem fixed_readouts [Nonempty ι] (hα : C.α ≠ 0) {z : ι → X} (hz : C.T z = z) :
    (∀ j, C.p z j = C.x z) ∧ C.r z = 0 := by
  have hp : ∀ j, C.p z j = C.x z := fun j => by
    have := congrFun hz j
    unfold T at this
    have h2 : C.p z j - C.x z = 0 := by
      rw [← sub_eq_zero] at this; rw [← this]; abel
    exact sub_eq_zero.1 h2
  refine ⟨hp, ?_⟩
  rw [r_eq hα]
  have : C.pbar z = C.x z := by
    unfold pbar
    simp only [hp, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp only [mP]
    rw [inv_mul_cancel₀ (by exact_mod_cast Fintype.card_ne_zero), one_smul]
  rw [this, sub_self, smul_zero]

/-- **Lemma L3(b) (explicit fixed point).** If u*_j ∈ ∂g_j(x*) for j ∈ N (here `u0` for j₀,
`u j` for j ∈ N') and ∇F(x*) + Σ_N u*_j = 0, then z*_j := x* − α∇F(x*) − m'α u*_j is a
fixed point of T, with x(z*) = x* and p_j(z*) = x*. -/
theorem explicit_fixed_point [Nonempty ι] (hα : C.α ≠ 0) {D0 : Set X} {g0 : X → ℝ}
    {Dj : ι → Set X} {gj : ι → X → ℝ} (hR : C.Realises D0 g0 Dj gj) {xs u0 : X}
    {u : ι → X} (hu0 : ExtSub D0 g0 0 xs u0) (hu : ∀ j, ExtSub (Dj j) (gj j) 0 xs (u j))
    (hsum : gradient C.F xs + u0 + ∑ j, u j = 0) :
    let zs : ι → X := fun j => xs - C.α • gradient C.F xs - (mP ι * C.α) • u j
    C.x zs = xs ∧ (∀ j, C.p zs j = xs) ∧ C.T zs = zs := by
  intro zs
  have hm := (mP_pos (ι := ι)).ne'
  have hzbar : zbar zs = xs + C.α • u0 := by
    have hu0' : u0 = -(gradient C.F xs) - ∑ j, u j := by
      rw [← sub_eq_zero, ← hsum]; abel
    unfold zbar
    simp only [zs, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      ← Finset.smul_sum]
    rw [← Nat.cast_smul_eq_nsmul ℝ, ← Nat.cast_smul_eq_nsmul ℝ]
    change (mP ι)⁻¹ • (mP ι • xs - mP ι • (C.α • gradient C.F xs)
      - (mP ι * C.α) • ∑ j, u j) = xs + C.α • u0
    have e1 : mP ι • xs - mP ι • (C.α • gradient C.F xs) - (mP ι * C.α) • ∑ j, u j
        = mP ι • (xs - C.α • gradient C.F xs - C.α • ∑ j, u j) := by module
    rw [e1, smul_smul, inv_mul_cancel₀ hm, one_smul, hu0']
    module
  have hx : C.x zs = xs := by
    unfold x
    rw [hR.prox0, hzbar, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hα, one_smul]
    exact hu0
  have hp : ∀ j, C.p zs j = xs := fun j => by
    unfold p
    rw [hR.prox]
    have hw : C.w zs j - xs = (mP ι * C.α) • u j := by
      unfold w; rw [hx]; simp only [zs]; module
    rw [hw, smul_smul, inv_mul_cancel₀ (mul_ne_zero hm hα), one_smul]
    exact hu j
  refine ⟨hx, hp, ?_⟩
  funext j
  unfold T
  rw [hp j, hx, add_sub_cancel_right]

end ConsIter

end Iteration

/-! ## Corollary T1-it and Theorem T2(c) (a-priori rate) -/

section Assembly

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {ι : Type*} [Fintype ι]

namespace ConsIter

variable {C : ConsIter X ι}

/-- E = F + g_{j₀} + Σ_{N'} g_j (finite part; dom E = dom g_{j₀} since the g_j, j ∈ N',
are real-valued). -/
def EIt (F g0 : X → ℝ) (gj : ι → X → ℝ) (y : X) : ℝ := F y + g0 y + ∑ j, gj j y

/-- ‖L‖ := (Σ_{N'} L_j²)^{1/2}. -/
noncomputable def normL (L : ι → ℝ) : ℝ := √(∑ j, L j ^ 2)

/-- Standing hypotheses of Corollary T1-it / Theorem T2 for the consensus-typed data:
F C¹ with C(F, σ_F) (σ_F = σ_𝔈^T, any sign); g_{j₀} (`g0` on `D0`) with C(g_{j₀}, σ₀),
σ₀ ≥ 0; every g_j, j ∈ N', real-valued with C(g_j, σ_j), σ_j ≥ 0 and a finite Lipschitz
attribute L_j; the prox programs realise the terms. -/
structure Typed (C : ConsIter X ι) (σF σ0 : ℝ) (D0 : Set X) (g0 : X → ℝ)
    (gj : ι → X → ℝ) (σj Lj : ι → ℝ) : Prop where
  diffF : Differentiable ℝ C.F
  curvF : ModC C.F σF
  curv0 : ExtModC D0 g0 σ0
  sigma0 : 0 ≤ σ0
  curv : ∀ j, ModC (gj j) (σj j)
  sigma : ∀ j, 0 ≤ σj j
  lip : ∀ j, LipAttr (gj j) (Lj j)
  real : C.Realises D0 g0 (fun _ => univ) gj

variable {σF σ0 : ℝ} {D0 : Set X} {g0 : X → ℝ} {gj : ι → X → ℝ} {σj Lj : ι → ℝ}

/-- The data of the iteration at z, as data (x, (p_j, v_j)_{j∈N}) of §2 on N = {j₀} ⊔ N'
(`Option ι`, j₀ = `none`): they satisfy (H-cert) with j₀ ∈ J₀. -/
theorem Typed.hcert (h : C.Typed σF σ0 D0 g0 gj σj Lj) (z : ι → X) :
    HCert C.F σF (fun o : Option ι => o.elim D0 (fun _ => univ)) (fun o : Option ι => o.elim g0 gj)
      (fun o : Option ι => o.elim σ0 σj) (fun o : Option ι => o.elim 0 Lj) (C.x z)
      (fun o : Option ι => o.elim (C.x z) (C.p z)) (fun o : Option ι => o.elim (C.v0 z) (C.v z)) where
  diffF := h.diffF
  curvF := h.curvF
  curv o := by cases o with | none => exact h.curv0 | some j => exact h.curv j
  sigma_nonneg o := by cases o with | none => exact h.sigma0 | some j => exact h.sigma j
  subgrad o := by
    cases o with
    | none => exact (readout_subgrad h.real z).1
    | some j => exact (readout_subgrad h.real z).2 j
  lip o ho := by
    cases o with
    | none => exact absurd rfl ho
    | some j => exact ⟨rfl, h.lip j⟩

lemma resid_opt (z : ι → X) :
    resid C.F (fun o : Option ι => o.elim (C.v0 z) (C.v z)) (C.x z) = C.r z := by
  unfold resid r; rw [Fintype.sum_option]; simp only [Option.elim]; abel

lemma muHat_opt : muHat σF (fun o : Option ι => o.elim σ0 σj) = σF + σ0 + ∑ j, σj j := by
  unfold muHat; rw [Fintype.sum_option]; simp only [Option.elim]; ring

lemma epsC_opt (z : ι → X) :
    epsC (C.x z) (fun o : Option ι => o.elim (C.x z) (C.p z)) (fun o : Option ι => o.elim (C.v0 z) (C.v z))
      (fun o : Option ι => o.elim 0 Lj) = C.epsIt Lj z := by
  rw [epsC_eq_sum, Fintype.sum_option]; simp [Option.elim, epsIt]

lemma domE_opt : domE (fun o : Option ι => o.elim D0 (fun _ => (univ : Set X))) = D0 := by
  ext y; simp [domE, Option.forall]

lemma Eval_opt (y : X) : Eval C.F (fun o : Option ι => o.elim g0 gj) y = EIt C.F g0 gj y := by
  unfold Eval EIt; rw [Fintype.sum_option]; simp only [Option.elim]; ring

/-- ε_k ≤ 2‖L‖e_k (L2(c),(d) and Cauchy–Schwarz). -/
theorem epsIt_le [Nonempty ι] (h : C.Typed σF σ0 D0 g0 gj σj Lj) (hα : 0 < C.α)
    (z : ι → X) : C.epsIt Lj z ≤ 2 * normL Lj * C.e z := by
  have hρ : ∀ j, ‖C.v z j‖ ≤ Lj j := fun j =>
    norm_subgrad_le (h.lip j) ((readout_subgrad h.real z).2 j)
  have h1 : C.epsIt Lj z ≤ ∑ j, 2 * (Lj j * ‖C.p z j - C.x z‖) := by
    unfold epsIt
    refine Finset.sum_le_sum fun j _ => ?_
    have := hρ j
    nlinarith [norm_nonneg (C.p z j - C.x z)]
  rw [← Finset.mul_sum] at h1
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt univ Lj (fun j => ‖C.p z j - C.x z‖)
  have he0 : 0 ≤ C.e z := Real.sqrt_nonneg _
  rw [(readout_bounds hα z).2.1, Real.sqrt_sq he0] at h2
  unfold normL
  linarith

/-- **Corollary T1-it.** For consensus-typed data with L_j < ∞ on N' and μ̂ > 0, at every
state z (every iterate), with x* a minimiser of E (existence classical, hypothesis):
‖x − x*‖ ≤ τ ≤ ‖r‖/μ̂ + √(ε/μ̂), ‖p_j − x*‖ ≤ τ + δ_j, E(x) − E(x*) ≤ ‖r‖²/(2μ̂) + ε,
‖r‖ = ‖x − p̄‖/α ≤ e/(α√m') and ε ≤ 2‖L‖e. No convexity of F is assumed. -/
theorem cert_iter [Nontrivial X] [Nonempty ι] (h : C.Typed σF σ0 D0 g0 gj σj Lj)
    (hα : 0 < C.α) (hμ : 0 < σF + σ0 + ∑ j, σj j) {xs : X} (hxs : xs ∈ D0)
    (hmin : ∀ y ∈ D0, EIt C.F g0 gj xs ≤ EIt C.F g0 gj y) (z : ι → X) :
    ‖C.x z - xs‖ ≤ tauC ‖C.r z‖ (C.epsIt Lj z) (σF + σ0 + ∑ j, σj j) ∧
    tauC ‖C.r z‖ (C.epsIt Lj z) (σF + σ0 + ∑ j, σj j)
      ≤ ‖C.r z‖ / (σF + σ0 + ∑ j, σj j) + √(C.epsIt Lj z / (σF + σ0 + ∑ j, σj j)) ∧
    (∀ j, ‖C.p z j - xs‖
      ≤ tauC ‖C.r z‖ (C.epsIt Lj z) (σF + σ0 + ∑ j, σj j) + ‖C.p z j - C.x z‖) ∧
    EIt C.F g0 gj (C.x z) - EIt C.F g0 gj xs
      ≤ ‖C.r z‖ ^ 2 / (2 * (σF + σ0 + ∑ j, σj j)) + C.epsIt Lj z ∧
    ‖C.r z‖ = ‖C.x z - C.pbar z‖ / C.α ∧
    ‖C.r z‖ ≤ C.e z / (C.α * √(mP ι)) ∧
    C.epsIt Lj z ≤ 2 * normL Lj * C.e z := by
  have hc := h.hcert z
  have hmin' : ∀ y ∈ domE (fun o : Option ι => o.elim D0 (fun _ => (univ : Set X))),
      Eval C.F (fun o : Option ι => o.elim g0 gj) xs ≤ Eval C.F (fun o : Option ι => o.elim g0 gj) y := by
    rw [domE_opt]; intro y hy; rw [Eval_opt, Eval_opt]; exact hmin y hy
  have hxs' : xs ∈ domE (fun o : Option ι => o.elim D0 (fun _ => (univ : Set X))) := by
    rw [domE_opt]; exact hxs
  have hμ' : 0 < muHat σF (fun o : Option ι => o.elim σ0 σj) := by rw [muHat_opt]; exact hμ
  obtain ⟨⟨h1, h2, h3⟩, h4, -⟩ := consensus_certificate hc hμ' hxs' hmin'
  rw [resid_opt, epsC_opt, muHat_opt] at h1 h2 h3 h4
  rw [Eval_opt, Eval_opt] at h4
  refine ⟨h1, h2, fun j => h3 (some j), h4, ?_, (readout_bounds hα z).2.2, epsIt_le h hα z⟩
  rw [r_eq hα.ne', norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hα), inv_mul_eq_div]

/-- The constants of Theorem T2(c): c_b = 1/(α√m'), τ₀ (the T1 bound at x₀),
D̄₀ = (Σ_{N'} (‖z_{j,0} − x₀‖ + (1 + αβ̂)τ₀ + α‖∇F(x₀)‖ + m'αL_j)²)^{1/2},
ē_k = √(2/(k+1)) D̄₀. -/
noncomputable def cb (C : ConsIter X ι) : ℝ := 1 / (C.α * √(mP ι))

noncomputable def tau0 (C : ConsIter X ι) (μ : ℝ) (Lj : ι → ℝ) (z0 : ι → X) : ℝ :=
  tauC ‖C.r z0‖ (C.epsIt Lj z0) μ

noncomputable def Dbar0 (C : ConsIter X ι) (βh μ : ℝ) (Lj : ι → ℝ) (z0 : ι → X) : ℝ :=
  √(∑ j, (‖z0 j - C.x z0‖ + (1 + C.α * βh) * C.tau0 μ Lj z0
    + C.α * ‖gradient C.F (C.x z0)‖ + mP ι * C.α * Lj j) ^ 2)

noncomputable def ebar (C : ConsIter X ι) (βh μ : ℝ) (Lj : ι → ℝ) (z0 : ι → X) (k : ℕ) : ℝ :=
  √(2 / (k + 1)) * C.Dbar0 βh μ Lj z0

lemma pnorm_le_of_le {a : ι → X} {b : ι → ℝ} (h : ∀ j, ‖a j‖ ≤ b j) :
    pnorm a ≤ √(∑ j, b j ^ 2) := by
  unfold pnorm
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun j _ => ?_)
  exact pow_le_pow_left₀ (norm_nonneg _) (h j) 2

/-- **Theorem T2(c) (a-priori rate from declared data).** Consensus-typed data, μ̂ > 0,
L_j < ∞ on N', step α > 0, β̂ ≥ 0 with ∇F β̂-Lipschitz. Classical inputs as hypotheses:
x* a minimiser of E ((O3), B&C Cor. 11.17); u*_j ∈ ∂g_j(x*), j ∈ N, with
∇F(x*) + Σ_N u*_j = 0 (Lemma L3(c): Fermat + sum rule, B&C Thm 16.3, Cor. 16.48(iii));
and the Krasnosel'skiĭ–Mann fixed-point-residual bound e_k² ≤ (2/(k+1))‖z₀ − z*‖² for
every fixed point z* (Ryu–Yin §2.4 Thm 1 with θ = 2/3, L1(iv)). Then for every k,
‖x_k − x*‖ ≤ c_b ē_k/μ̂ + (2‖L‖ē_k/μ̂)^{1/2}. -/
theorem apriori_rate [Nontrivial X] [Nonempty ι] (h : C.Typed σF σ0 D0 g0 gj σj Lj)
    (hα : 0 < C.α) {βh : ℝ} (hβ : 0 ≤ βh) (hFL : LipGrad C.F βh)
    (hμ : 0 < σF + σ0 + ∑ j, σj j) {xs : X} (hxs : xs ∈ D0)
    (hmin : ∀ y ∈ D0, EIt C.F g0 gj xs ≤ EIt C.F g0 gj y)
    {u0 : X} {u : ι → X} (hu0 : ExtSub D0 g0 0 xs u0) (hu : ∀ j, ExtSub univ (gj j) 0 xs (u j))
    (hsum : gradient C.F xs + u0 + ∑ j, u j = 0) (z0 : ι → X)
    (hKM : ∀ zs : ι → X, C.T zs = zs → ∀ k : ℕ,
      C.e (C.iter z0 k) ^ 2 ≤ 2 / (k + 1) * pnorm (z0 - zs) ^ 2) :
    ∀ k : ℕ, ‖C.x (C.iter z0 k) - xs‖
      ≤ C.cb * C.ebar βh (σF + σ0 + ∑ j, σj j) Lj z0 k / (σF + σ0 + ∑ j, σj j)
        + √(2 * normL Lj * C.ebar βh (σF + σ0 + ∑ j, σj j) Lj z0 k
            / (σF + σ0 + ∑ j, σj j)) := by
  set μ := σF + σ0 + ∑ j, σj j with hμdef
  have hm := mP_pos (ι := ι)
  -- the explicit fixed point (L3(b))
  obtain ⟨-, -, hfix⟩ := explicit_fixed_point hα.ne' h.real hu0 hu hsum
  set zs : ι → X := fun j => xs - C.α • gradient C.F xs - (mP ι * C.α) • u j with hzs
  have hcert0 := cert_iter h hα hμ hxs hmin z0
  have hτ0 : ‖C.x z0 - xs‖ ≤ C.tau0 μ Lj z0 := hcert0.1
  -- ‖z₀ − z*‖ ≤ D̄₀
  have hD : pnorm (z0 - zs) ≤ C.Dbar0 βh μ Lj z0 := by
    apply pnorm_le_of_le
    intro j
    have hgrad : ‖gradient C.F xs‖ ≤ ‖gradient C.F (C.x z0)‖ + βh * C.tau0 μ Lj z0 := by
      have h1 := hFL xs (C.x z0)
      have h2 := norm_le_insert' (gradient C.F xs) (gradient C.F (C.x z0))
      rw [norm_sub_rev xs] at h1
      have h3 : βh * ‖C.x z0 - xs‖ ≤ βh * C.tau0 μ Lj z0 := mul_le_mul_of_nonneg_left hτ0 hβ
      linarith
    have hu' : ‖u j‖ ≤ Lj j := norm_subgrad_le (h.lip j) (hu j)
    have e : (z0 - zs) j = (z0 j - C.x z0) + (C.x z0 - xs) + C.α • gradient C.F xs
        + (mP ι * C.α) • u j := by
      simp only [Pi.sub_apply, hzs]; abel
    rw [e]
    have n1 := norm_add_le ((z0 j - C.x z0) + (C.x z0 - xs) + C.α • gradient C.F xs)
      ((mP ι * C.α) • u j)
    have n2 := norm_add_le ((z0 j - C.x z0) + (C.x z0 - xs)) (C.α • gradient C.F xs)
    have n3 := norm_add_le (z0 j - C.x z0) (C.x z0 - xs)
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hα] at n2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (mul_pos hm hα)] at n1
    have a1 : C.α * ‖gradient C.F xs‖
        ≤ C.α * (‖gradient C.F (C.x z0)‖ + βh * C.tau0 μ Lj z0) :=
      mul_le_mul_of_nonneg_left hgrad hα.le
    have a2 : mP ι * C.α * ‖u j‖ ≤ mP ι * C.α * Lj j :=
      mul_le_mul_of_nonneg_left hu' (mul_pos hm hα).le
    nlinarith
  intro k
  -- e_k ≤ ē_k
  have he : C.e (C.iter z0 k) ≤ C.ebar βh μ Lj z0 k := by
    have h1 := hKM zs hfix k
    have hDn : 0 ≤ pnorm (z0 - zs) := Real.sqrt_nonneg _
    have h2 : C.e (C.iter z0 k) ^ 2 ≤ 2 / (k + 1) * C.Dbar0 βh μ Lj z0 ^ 2 := by
      refine h1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
      exact pow_le_pow_left₀ hDn hD 2
    have h3 := Real.sqrt_le_sqrt h2
    have he0 : 0 ≤ C.e (C.iter z0 k) := Real.sqrt_nonneg _
    have hD0 : 0 ≤ C.Dbar0 βh μ Lj z0 := Real.sqrt_nonneg _
    rw [Real.sqrt_sq he0, Real.sqrt_mul (by positivity), Real.sqrt_sq hD0] at h3
    exact h3
  -- the certificate at x_k
  obtain ⟨c1, c2, -, -, -, c6, c7⟩ := cert_iter h hα hμ hxs hmin (C.iter z0 k)
  have hμ0 := hμ
  have hcb : ‖C.r (C.iter z0 k)‖ ≤ C.cb * C.ebar βh μ Lj z0 k := by
    refine c6.trans ?_
    unfold cb
    rw [div_eq_mul_inv, one_div, mul_comm]
    exact mul_le_mul_of_nonneg_left he (by positivity)
  have hεb : C.epsIt Lj (C.iter z0 k) ≤ 2 * normL Lj * C.ebar βh μ Lj z0 k :=
    c7.trans (mul_le_mul_of_nonneg_left he (by unfold normL; positivity))
  calc ‖C.x (C.iter z0 k) - xs‖
      ≤ ‖C.r (C.iter z0 k)‖ / μ + √(C.epsIt Lj (C.iter z0 k) / μ) := c1.trans c2
    _ ≤ C.cb * C.ebar βh μ Lj z0 k / μ + √(2 * normL Lj * C.ebar βh μ Lj z0 k / μ) := by
      gcongr

/-- **Lemma L3(a), minimiser part.** If σ_F = σ_𝔈^T ≥ 0, the x-read-out of a fixed point
minimises E = F + g_{j₀} + Σ_{N'} g_j over dom E (via the minorant (M) with r = 0, ε = 0:
Fermat's rule). No Lipschitz attribute is needed; every g_j may be extended-valued. -/
theorem fixed_argmin [Nontrivial X] [Nonempty ι] {Dj : ι → Set X}
    (hFd : Differentiable ℝ C.F) (hFC : ModC C.F σF) (hσF : 0 ≤ σF)
    (h0 : ExtModC D0 g0 σ0) (hσ0 : 0 ≤ σ0) (hj : ∀ j, ExtModC (Dj j) (gj j) (σj j))
    (hσj : ∀ j, 0 ≤ σj j) (hR : C.Realises D0 g0 Dj gj) (hα : C.α ≠ 0) {z : ι → X}
    (hz : C.T z = z) :
    C.x z ∈ domE (fun o : Option ι => o.elim D0 Dj) ∧
      ∀ y ∈ domE (fun o : Option ι => o.elim D0 Dj),
        Eval C.F (fun o : Option ι => o.elim g0 gj) (C.x z)
          ≤ Eval C.F (fun o : Option ι => o.elim g0 gj) y := by
  obtain ⟨hp, hr⟩ := fixed_readouts hα hz
  have hc : HCert C.F σF (fun o : Option ι => o.elim D0 Dj) (fun o : Option ι => o.elim g0 gj)
      (fun o : Option ι => o.elim σ0 σj) (fun _ => 0) (C.x z)
      (fun o : Option ι => o.elim (C.x z) (C.p z))
      (fun o : Option ι => o.elim (C.v0 z) (C.v z)) :=
    { diffF := hFd
      curvF := hFC
      curv := fun o => by cases o with | none => exact h0 | some j => exact hj j
      sigma_nonneg := fun o => by cases o with | none => exact hσ0 | some j => exact hσj j
      subgrad := fun o => by
        cases o with
        | none => exact (readout_subgrad hR z).1
        | some j => exact (readout_subgrad hR z).2 j
      lip := fun o ho => by
        cases o with
        | none => exact absurd rfl ho
        | some j => exact absurd (hp j) ho }
  obtain ⟨hx, hM⟩ := consensus_minorant hc
  refine ⟨hx, fun y hy => ?_⟩
  have := hM y hy
  have he : epsC (C.x z) (fun o : Option ι => o.elim (C.x z) (C.p z))
      (fun o : Option ι => o.elim (C.v0 z) (C.v z)) (fun _ => 0) = 0 := by
    rw [epsC_eq_sum, Fintype.sum_option]; simp [hp]
  rw [resid_opt, he, muHat_opt, hr, inner_zero_left] at this
  have hμ : 0 ≤ σF + σ0 + ∑ j, σj j :=
    add_nonneg (add_nonneg hσF hσ0) (Finset.sum_nonneg fun j _ => hσj j)
  nlinarith [sq_nonneg ‖y - C.x z‖]

/-- The step-count corollary of T2(c): if u* > 0 solves (c_b/μ̂)u² + √(2‖L‖/μ̂)u = ε_acc
and ē_k ≤ u*², the a-priori bound is at most ε_acc. -/
theorem apriori_count {cb μ nL ebk ustar εacc : ℝ} (hcb : 0 ≤ cb) (hμ : 0 < μ) (hnL : 0 ≤ nL)
    (hu : 0 < ustar) (hsol : cb / μ * ustar ^ 2 + √(2 * nL / μ) * ustar = εacc)
    (he : ebk ≤ ustar ^ 2) :
    cb * ebk / μ + √(2 * nL * ebk / μ) ≤ εacc := by
  rw [← hsol]
  have h1 : cb * ebk / μ ≤ cb / μ * ustar ^ 2 := by
    rw [mul_div_right_comm]; exact mul_le_mul_of_nonneg_left he (div_nonneg hcb hμ.le)
  have h2 : √(2 * nL * ebk / μ) ≤ √(2 * nL / μ) * ustar := by
    rw [show 2 * nL * ebk / μ = 2 * nL / μ * ebk by ring, Real.sqrt_mul (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
    calc √ebk ≤ √(ustar ^ 2) := Real.sqrt_le_sqrt he
      _ = ustar := Real.sqrt_sq hu.le
  linarith

/-- ē_k ≤ u*² once k + 1 ≥ 2D̄₀²/u*⁴ (the count k ≥ 2D̄₀²/u*⁴ − 1 of T2(d)). -/
theorem ebar_le_of_count {D ustar : ℝ} (hD : 0 ≤ D) (hu : 0 < ustar) {k : ℕ}
    (hk : 2 * D ^ 2 / ustar ^ 4 ≤ k + 1) : √(2 / (k + 1)) * D ≤ ustar ^ 2 := by
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have h1 : 2 / (k + 1) * D ^ 2 ≤ (ustar ^ 2) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hk1]; nlinarith
  calc √(2 / (k + 1)) * D = √(2 / (k + 1) * D ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hD]
    _ ≤ √((ustar ^ 2) ^ 2) := Real.sqrt_le_sqrt h1
    _ = ustar ^ 2 := Real.sqrt_sq (by positivity)

end ConsIter

end Assembly

/-! ## Coordinates on ℝ² and convexity helpers for the instances -/

section Coords

/-- ℝ² with the Euclidean inner product. -/
abbrev V2 := EuclideanSpace ℝ (Fin 2)

lemma inner_v2 (y z : V2) : inner ℝ y z = y 0 * z 0 + y 1 * z 1 := by
  simp [EuclideanSpace.inner_eq_star_dotProduct, Fin.sum_univ_two, dotProduct]; ring

lemma normsq_v2 (y : V2) : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 := by
  simp [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two]

lemma norm_v2 (y : V2) : ‖y‖ = √(y 0 ^ 2 + y 1 ^ 2) := by
  rw [← normsq_v2, Real.sqrt_sq (norm_nonneg _)]

lemma v2_ext {y z : V2} (h0 : y 0 = z 0) (h1 : y 1 = z 1) : y = z := by
  ext i; fin_cases i <;> simp [h0, h1]

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- y ↦ L|ℓ(y)| is convex for an affine functional ℓ and L ≥ 0. -/
lemma convexOn_abs_affine {ℓ : X → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hℓ : ∀ x y : X, ∀ a b : ℝ, a + b = 1 → ℓ (a • x + b • y) = a * ℓ x + b * ℓ y) :
    ConvexOn ℝ univ (fun y => L * |ℓ y|) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rw [hℓ x y a b hab]
  have := abs_add_le (a * ℓ x) (b * ℓ y)
  rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] at this
  nlinarith

/-- The zero set of an affine functional is convex. -/
lemma convex_affine_zero {ℓ : X → ℝ}
    (hℓ : ∀ x y : X, ∀ a b : ℝ, a + b = 1 → ℓ (a • x + b • y) = a * ℓ x + b * ℓ y) :
    Convex ℝ {y | ℓ y = 0} := by
  intro x hx y hy a b _ _ hab
  simp only [mem_setOf_eq] at hx hy ⊢
  rw [hℓ x y a b hab, hx, hy]; ring

lemma modC_zero_iff [CompleteSpace X] (g : X → ℝ) : ModC g 0 ↔ ConvexOn ℝ univ g := by
  unfold ModC; simp

lemma lipGrad_halfSq [CompleteSpace X] (σ : ℝ) (hσ : 0 ≤ σ) :
    LipGrad (fun y : X => σ / 2 * ‖y‖ ^ 2) σ := by
  intro a b
  rw [gradient_halfSq, gradient_halfSq, ← smul_sub, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hσ]

end Coords

/-! ## Proposition P2 (no linear rate from declared numbers) -/

namespace P2

/-- n_θ = (−sin θ, cos θ). -/
noncomputable def nθ (θ : ℝ) : V2 := !₂[-Real.sin θ, Real.cos θ]
/-- u_θ = (cos θ, sin θ), spanning U_θ. -/
noncomputable def uθ (θ : ℝ) : V2 := !₂[Real.cos θ, Real.sin θ]
/-- U₁ = span e₁ = dom g₁ (g₁ = ι_{U₁}). -/
def U1 : Set V2 := {y | y 1 = 0}
/-- f = ½‖·‖² (declared (1, 1, void)). -/
noncomputable def F : V2 → ℝ := fun y => 1 / 2 * ‖y‖ ^ 2
/-- g₂ = L dist(·, U_θ) (declared (0, explicit, void, L)). -/
noncomputable def g2 (θ L : ℝ) : V2 → ℝ :=
  fun y => L * Metric.infDist y (Submodule.span ℝ {uθ θ} : Set V2)
/-- The explicit program for prox_{α g₁} = P_{U₁} (B&C Ex. 12.25). -/
def proxU1 (y : V2) : V2 := !₂[y 0, 0]
/-- The explicit program for prox_{γ L dist(·,U_θ)} at γ = m'α = 1 (B&C Ex. 24.28): with
c = ⟨n_θ, w⟩, P_{U_θ}w = w − c n_θ if |c| ≤ L, else w ∓ L n_θ. -/
noncomputable def proxDist (θ L : ℝ) (w : V2) : V2 :=
  if |inner ℝ (nθ θ) w| ≤ L then w - (inner ℝ (nθ θ) w) • nθ θ
  else if 0 < inner ℝ (nθ θ) w then w - L • nθ θ else w + L • nθ θ

/-- The constructed iteration of the P2 specification: N' = {2} (`Unit`, m' = 1),
j₀ = 1, α = 1/β̂ = 1. -/
noncomputable def inst (θ L : ℝ) : ConsIter V2 Unit := ⟨F, 1, proxU1, fun _ => proxDist θ L⟩

lemma inner_n (θ : ℝ) (y : V2) : inner ℝ (nθ θ) y = -Real.sin θ * y 0 + Real.cos θ * y 1 := by
  rw [inner_v2]; simp [nθ]

lemma norm_n (θ : ℝ) : ‖nθ θ‖ = 1 := by
  rw [norm_v2]; simp [nθ, Real.sin_sq_add_cos_sq]

/-- dist(y, U_θ) = |⟨n_θ, y⟩|. -/
lemma infDist_eq (θ : ℝ) (y : V2) :
    Metric.infDist y (Submodule.span ℝ {uθ θ} : Set V2) = |inner ℝ (nθ θ) y| := by
  have hsc := Real.sin_sq_add_cos_sq θ
  apply le_antisymm
  · have hmem : (inner ℝ (uθ θ) y) • uθ θ ∈ (Submodule.span ℝ {uθ θ} : Set V2) :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    refine (Metric.infDist_le_dist_of_mem hmem).trans (le_of_eq ?_)
    rw [dist_eq_norm]
    have e : y - (inner ℝ (uθ θ) y) • uθ θ = (inner ℝ (nθ θ) y) • nθ θ := by
      apply v2_ext <;> simp [inner_v2, uθ, nθ] <;>
        first
        | linear_combination (-(y 0)) * hsc | linear_combination (y 0) * hsc
        | linear_combination (-(y 1)) * hsc
    rw [e, norm_smul, norm_n, mul_one, Real.norm_eq_abs]
  · rw [Metric.le_infDist ⟨0, Submodule.zero_mem _⟩]
    intro q hq
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hq
    rw [dist_eq_norm]
    have e : inner ℝ (nθ θ) (y - a • uθ θ) = inner ℝ (nθ θ) y := by
      rw [inner_sub_right, inner_smul_right]
      have : inner ℝ (nθ θ) (uθ θ) = 0 := by rw [inner_v2]; simp [nθ, uθ]; ring
      rw [this, mul_zero, sub_zero]
    rw [← e]
    have := abs_real_inner_le_norm (nθ θ) (y - a • uθ θ)
    rwa [norm_n, one_mul] at this

lemma g2_eq (θ L : ℝ) : g2 θ L = fun y => L * |inner ℝ (nθ θ) y| := by
  funext y; rw [g2, infDist_eq]

lemma mP_unit : ConsIter.mP Unit = 1 := by simp [ConsIter.mP]

lemma gradF (y : V2) : gradient F y = y := by
  have := gradient_halfSq (X := V2) 1 y
  rw [one_smul] at this
  exact this

/-- Validity of the declarations, uniformly in θ: f is 1-smooth with C(f, 1); ι_{U₁} has
convex domain (σ₁ = 0); g₂ is convex (σ₂ = 0) with Lipschitz attribute L. -/
theorem valid {θ L : ℝ} (hL : 0 ≤ L) :
    LipGrad F 1 ∧ ModC F 1 ∧ ExtModC U1 (fun _ => 0) 0 ∧ ModC (g2 θ L) 0 ∧
      LipAttr (g2 θ L) L := by
  have hF : F = fun y : V2 => (1 : ℝ) / 2 * ‖y‖ ^ 2 := rfl
  have haff : ∀ x y : V2, ∀ a b : ℝ, a + b = 1 →
      inner ℝ (nθ θ) (a • x + b • y) = a * inner ℝ (nθ θ) x + b * inner ℝ (nθ θ) y := by
    intro x y a b _
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  refine ⟨hF ▸ lipGrad_halfSq 1 zero_le_one, hF ▸ modC_halfSq 1, ?_, ?_, ⟨hL, fun x y => ?_⟩⟩
  · have hc : Convex ℝ U1 := by
      have := convex_affine_zero (X := V2) (ℓ := fun y => y 1) (by
        intro x y a b _; simp)
      exact this
    unfold ExtModC
    simpa using convexOn_const (0 : ℝ) hc
  · rw [modC_zero_iff, g2_eq]
    exact convexOn_abs_affine hL haff
  · rw [g2_eq]
    simp only
    rw [← mul_sub, abs_mul, abs_of_nonneg hL]
    refine mul_le_mul_of_nonneg_left ?_ hL
    calc |(|inner ℝ (nθ θ) x| - |inner ℝ (nθ θ) y|)| ≤ |inner ℝ (nθ θ) x - inner ℝ (nθ θ) y| :=
          abs_abs_sub_abs_le_abs_sub _ _
      _ = |inner ℝ (nθ θ) (x - y)| := by rw [inner_sub_right]
      _ ≤ ‖nθ θ‖ * ‖x - y‖ := abs_real_inner_le_norm _ _
      _ = ‖x - y‖ := by rw [norm_n, one_mul]

/-- The two programs realise the proxes: P_{U₁} = prox_{ι_{U₁}} and `proxDist` =
prox_{L dist(·,U_θ)} (checked against the subgradient inequality, uniqueness by
monotonicity). -/
theorem realises {θ L : ℝ} (hL : 0 ≤ L) :
    (inst θ L).Realises U1 (fun _ => 0) (fun _ => univ) (fun _ => g2 θ L) := by
  constructor
  · have hα : (inst θ L).α = 1 := rfl
    rw [hα]
    refine proxChar_of_forall one_pos fun y => ⟨by simp [inst, proxU1, U1], fun y' hy' => ?_⟩
    simp only [U1, mem_setOf_eq] at hy'
    rw [inner_v2]; simp [inst, proxU1, hy']
  · intro j
    have hα : (inst θ L).α = 1 := rfl
    rw [hα, mP_unit, mul_one]
    refine proxChar_of_forall one_pos fun w => ⟨mem_univ _, fun y _ => ?_⟩
    have hn := norm_n θ
    have hnn : inner ℝ (nθ θ) (nθ θ) = 1 := by rw [real_inner_self_eq_norm_sq, hn]; norm_num
    rw [g2_eq]
    simp only [inv_one, one_smul, zero_div, zero_mul, add_zero]
    set c := inner ℝ (nθ θ) w with hc
    rw [show (inst θ L).prox j = proxDist θ L from rfl]
    unfold proxDist
    rw [← hc]
    split_ifs with h1 h2
    · -- |c| ≤ L: p = w − c n, v = c n
      have hp : inner ℝ (nθ θ) (w - c • nθ θ) = 0 := by
        rw [inner_sub_right, inner_smul_right, hnn, ← hc]; ring
      have hv : w - (w - c • nθ θ) = c • nθ θ := by abel
      rw [hp, hv, abs_zero, mul_zero, zero_add, real_inner_smul_left, inner_sub_right, hp,
        sub_zero]
      have := le_abs_self (c * inner ℝ (nθ θ) y)
      rw [abs_mul] at this
      nlinarith [abs_nonneg (inner ℝ (nθ θ) y)]
    · -- c > L
      have hp : inner ℝ (nθ θ) (w - L • nθ θ) = c - L := by
        rw [inner_sub_right, inner_smul_right, hnn, ← hc]; ring
      have hv : w - (w - L • nθ θ) = L • nθ θ := by abel
      push Not at h1
      have hcL : L < c := by
        rcases le_or_gt 0 c with h | h
        · rwa [abs_of_nonneg h] at h1
        · linarith
      rw [hp, hv, real_inner_smul_left, inner_sub_right, hp, abs_of_pos (by linarith)]
      nlinarith [le_abs_self (inner ℝ (nθ θ) y)]
    · -- c < −L
      have hp : inner ℝ (nθ θ) (w + L • nθ θ) = c + L := by
        rw [inner_add_right, inner_smul_right, hnn, ← hc]; ring
      have hv : w - (w + L • nθ θ) = -(L • nθ θ) := by abel
      push Not at h1 h2
      have hcL : c < -L := by
        rcases le_or_gt 0 c with h | h
        · have := le_antisymm h2 h; rw [this, abs_zero] at h1; linarith
        · rw [abs_of_neg h] at h1; linarith
      rw [hp, hv, inner_neg_left, real_inner_smul_left, inner_sub_right, hp,
        abs_of_neg (by linarith)]
      nlinarith [neg_abs_le (inner ℝ (nθ θ) y)]

/-- The P2 specification is consensus typed with the same declared numbers for every θ:
σ_F = σ_𝔈^∅ = 1, σ₁ = σ₂ = 0, L₂ = L (so μ̂ = 1, α = 1, m' = 1). -/
theorem typed {θ L : ℝ} (hL : 0 ≤ L) :
    (inst θ L).Typed 1 0 U1 (fun _ => 0) (fun _ => g2 θ L) (fun _ => 0) (fun _ => L) := by
  obtain ⟨-, hFC, hU, hg, hgL⟩ := valid (θ := θ) hL
  exact ⟨differentiable_halfSq 1, hFC, hU, le_rfl, fun _ => hg, fun _ => le_rfl, fun _ => hgL,
    realises hL⟩

/-- x* = 0 is the unique minimiser of E = f + ι_{U₁} + L dist(·, U_θ). -/
theorem argmin_zero {θ L : ℝ} (hL : 0 ≤ L) :
    (0 : V2) ∈ U1 ∧ ∀ y ∈ U1,
      ((∀ y' ∈ U1, ConsIter.EIt F (fun _ => 0) (fun _ : Unit => g2 θ L) y
        ≤ ConsIter.EIt F (fun _ => 0) (fun _ : Unit => g2 θ L) y') ↔ y = 0) := by
  have hE : ∀ y, ConsIter.EIt F (fun _ => 0) (fun _ : Unit => g2 θ L) y
      = 1 / 2 * ‖y‖ ^ 2 + L * |inner ℝ (nθ θ) y| := by
    intro y; simp [ConsIter.EIt, F, g2_eq]
  refine ⟨by simp [U1], fun y _ => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have := h 0 (by simp [U1])
    rw [hE, hE] at this
    simp only [norm_zero, inner_zero_right, abs_zero, mul_zero] at this
    have h2 : 0 ≤ L * |inner ℝ (nθ θ) y| := by positivity
    have : ‖y‖ ^ 2 ≤ 0 := by nlinarith
    exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])
  · subst h
    intro y' _
    rw [hE, hE]
    simp only [norm_zero, inner_zero_right, abs_zero, mul_zero]
    nlinarith [sq_nonneg ‖y'‖, mul_nonneg hL (abs_nonneg (inner ℝ (nθ θ) y'))]

/-- One step of the orbit: for 0 ≤ c ≤ L, T(c n_θ) = c cos²θ n_θ, and
x(c n_θ) = (−c sin θ, 0). -/
lemma step {θ L c : ℝ} (hc0 : 0 ≤ c) (hcL : c ≤ L) :
    (inst θ L).x (fun _ => c • nθ θ) = !₂[-(c * Real.sin θ), 0] ∧
    (inst θ L).T (fun _ => c • nθ θ) = fun _ => (c * Real.cos θ ^ 2) • nθ θ := by
  have hzbar : ConsIter.zbar (fun _ : Unit => c • nθ θ) = c • nθ θ := by
    simp [ConsIter.zbar, ConsIter.mP]
  have hx : (inst θ L).x (fun _ => c • nθ θ) = !₂[-(c * Real.sin θ), 0] := by
    simp only [ConsIter.x, hzbar]
    apply v2_ext <;> simp [inst, proxU1, nθ]
  refine ⟨hx, ?_⟩
  have hw : (inst θ L).w (fun _ => c • nθ θ) () = !₂[0, -(c * Real.cos θ)] := by
    simp only [ConsIter.w, hx]
    have : (inst θ L).F = F := rfl
    rw [this, gradF]
    apply v2_ext <;> simp [inst, nθ]
    ring
  have hcw : inner ℝ (nθ θ) (!₂[0, -(c * Real.cos θ)] : V2) = -(c * Real.cos θ ^ 2) := by
    rw [inner_n]; simp; ring
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hle : |inner ℝ (nθ θ) (!₂[0, -(c * Real.cos θ)] : V2)| ≤ L := by
    rw [hcw, abs_neg, abs_of_nonneg (by positivity)]
    nlinarith [sq_nonneg (Real.cos θ)]
  have hp : (inst θ L).p (fun _ => c • nθ θ) () =
      !₂[-(c * Real.cos θ ^ 2 * Real.sin θ), -(c * Real.cos θ) + c * Real.cos θ ^ 3] := by
    simp only [ConsIter.p, hw]
    change proxDist θ L _ = _
    unfold proxDist
    rw [if_pos hle, hcw]
    apply v2_ext <;> simp [nθ]
    ring
  funext j
  simp only [ConsIter.T, hp, hx]
  apply v2_ext <;> simp [nθ]
  ring

/-- **Proposition P2(b) (the orbit).** For θ ∈ (0, π/2), 0 < s ≤ L and z₀ = s n_θ:
z_k = cos^{2k}θ z₀, x_k = (−s sin θ cos^{2k}θ, 0), and ‖x_k − x*‖ = cos^{2k}θ ‖x₀ − x*‖
with x* = 0. -/
theorem orbit {θ L s : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hs : 0 < s) (hsL : s ≤ L) (k : ℕ) :
    (inst θ L).iter (fun _ => s • nθ θ) k = (fun _ => ((Real.cos θ ^ 2) ^ k * s) • nθ θ) ∧
    (inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) k)
      = !₂[-(s * Real.sin θ * (Real.cos θ ^ 2) ^ k), 0] ∧
    ‖(inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) k) - 0‖
      = (Real.cos θ ^ 2) ^ k * ‖(inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) 0) - 0‖ := by
  have hcos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hcos2 : Real.cos θ ^ 2 ≤ 1 := by nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.sin θ)]
  have hz : ∀ k : ℕ, (inst θ L).iter (fun _ => s • nθ θ) k
      = (fun _ => ((Real.cos θ ^ 2) ^ k * s) • nθ θ) := by
    intro k
    induction k with
    | zero => simp [ConsIter.iter]
    | succ k ih =>
      have hck : (Real.cos θ ^ 2) ^ k * s ≤ L := by
        have : (Real.cos θ ^ 2) ^ k ≤ 1 := pow_le_one₀ (by positivity) hcos2
        nlinarith
      have hit : (inst θ L).iter (fun _ => s • nθ θ) (k + 1)
          = (inst θ L).T ((inst θ L).iter (fun _ => s • nθ θ) k) := by
        simp [ConsIter.iter, Function.iterate_succ_apply']
      rw [hit, ih, (step (by positivity) hck).2]
      funext j; congr 1; ring
  have hx : ∀ k : ℕ, (inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) k)
      = !₂[-(s * Real.sin θ * (Real.cos θ ^ 2) ^ k), 0] := by
    intro k
    have hck : (Real.cos θ ^ 2) ^ k * s ≤ L := by
      have : (Real.cos θ ^ 2) ^ k ≤ 1 := pow_le_one₀ (by positivity) hcos2
      nlinarith
    rw [hz k, (step (by positivity) hck).1]
    congr 2; ring
  refine ⟨hz k, hx k, ?_⟩
  rw [hx k, hx 0, sub_zero, sub_zero, norm_v2, norm_v2]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pow_zero, mul_one]
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero]
  rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs, abs_neg, abs_neg,
    abs_of_pos (by positivity), abs_of_pos (by positivity)]
  ring

/-- **Proposition P2(c) (no linear rate from declared numbers).** The declared numbers of
the P2 specification do not depend on θ (`typed`, `valid`), so a pair (K, q) that is a
function of them is one fixed pair for the whole family. No such pair, with 0 ≤ q < 1,
bounds ‖x_k − x*‖ ≤ K qᵏ ‖x₀ − x*‖ for every θ ∈ (0, π/2) and every k. -/
theorem no_linear_rate {L s : ℝ} (hs : 0 < s) (hsL : s ≤ L) :
    ¬ ∃ K q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), ∀ k : ℕ,
      ‖(inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) k) - 0‖
        ≤ K * q ^ k * ‖(inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) 0) - 0‖ := by
  rintro ⟨K, q, hq0, hq1, hbd⟩
  -- θ := arccos √((1+q)/2): cos²θ = (1+q)/2 ∈ (q, 1)
  set a := (1 + q) / 2 with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have ha1 : a < 1 := by rw [ha]; linarith
  set θ := Real.arccos (√a) with hθ
  have hsa : 0 < √a := Real.sqrt_pos.2 ha0
  have hsa1 : √a < 1 := by rw [Real.sqrt_lt' one_pos]; simpa using ha1
  have hθmem : θ ∈ Set.Ioo 0 (Real.pi / 2) :=
    ⟨Real.arccos_pos.2 hsa1, Real.arccos_lt_pi_div_two.2 hsa⟩
  have hc2 : Real.cos θ ^ 2 = a := by
    rw [hθ, Real.cos_arccos (by linarith) hsa1.le, Real.sq_sqrt ha0.le]
  have hsin : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθmem.1 (by linarith [hθmem.2, Real.pi_pos])
  -- ‖x₀‖ > 0
  have hx0 : 0 < ‖(inst θ L).x ((inst θ L).iter (fun _ => s • nθ θ) 0) - 0‖ := by
    rw [(orbit hθmem hs hsL 0).2.1, sub_zero, norm_pos_iff]
    intro h
    have := congrArg (fun y : V2 => y 0) h
    simp at this
    rcases this with h1 | h1 <;> linarith
  -- (q/a)^k → 0, so eventually K (q/a)^k < 1
  have hqa0 : 0 ≤ q / a := div_nonneg hq0 ha0.le
  have hqa1 : q / a < 1 := by rw [div_lt_one ha0, ha]; linarith
  have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one hqa0 hqa1).const_mul K
  rw [mul_zero] at ht
  obtain ⟨k, hk⟩ := (ht.eventually (gt_mem_nhds one_pos)).exists
  have hb := hbd θ hθmem k
  rw [(orbit hθmem hs hsL k).2.2, hc2] at hb
  have hak : 0 < a ^ k := pow_pos ha0 k
  have hb' : a ^ k ≤ K * q ^ k := le_of_mul_le_mul_right (by linarith) hx0
  have : K * (q / a) ^ k = K * q ^ k / a ^ k := by rw [div_pow]; ring
  rw [this, div_lt_one hak] at hk
  linarith

/-- The same in the z-variable: z* = 0 is a fixed point and ‖z_k − z*‖ = cos^{2k}θ‖z₀ − z*‖
(product norm). -/
theorem orbit_z {θ L s : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hs : 0 < s) (hsL : s ≤ L) (hL : 0 ≤ L)
    (k : ℕ) :
    (inst θ L).T (fun _ => 0) = (fun _ => 0) ∧
    ConsIter.pnorm ((inst θ L).iter (fun _ => s • nθ θ) k - fun _ => 0)
      = (Real.cos θ ^ 2) ^ k * ConsIter.pnorm ((fun _ : Unit => s • nθ θ) - fun _ => 0) := by
  refine ⟨?_, ?_⟩
  · have := (step (θ := θ) (L := L) (c := 0) le_rfl hL).2
    simpa using this
  · rw [(orbit hθ hs hsL k).1]
    simp only [ConsIter.pnorm, Pi.sub_apply, sub_zero, Finset.univ_unique,
      Finset.sum_singleton, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, mul_pow, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
      Real.sqrt_sq (abs_nonneg _), Real.sqrt_sq (abs_nonneg _), abs_mul,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (Real.cos θ ^ 2) ^ k)]
    ring

end P2

/-! ## Proposition P1 (what the certificate needs) -/

section P1helpers

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

lemma lipAttr_mono {g : X → ℝ} {L L' : ℝ} (h : LipAttr g L) (hL : L ≤ L') : LipAttr g L' :=
  ⟨h.1.trans hL, fun x y => (h.2 x y).trans (mul_le_mul_of_nonneg_right hL (norm_nonneg _))⟩

/-- |ℓ_c(a) − ℓ_c(b)| ≤ √(1 + c²)‖a − b‖ for ℓ_c(y) = y₂ + c y₁ on ℝ². -/
lemma abs_lin_le (c : ℝ) (a b : V2) :
    |(a 1 + c * a 0) - (b 1 + c * b 0)| ≤ √(1 + c ^ 2) * ‖a - b‖ := by
  rw [norm_v2, ← Real.sqrt_mul (by positivity)]
  apply Real.abs_le_sqrt
  simp only [PiLp.sub_apply]
  nlinarith [sq_nonneg (c * (a 1 - b 1) - (a 0 - b 0))]

lemma lipAttr_absLin {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    LipAttr (fun y : V2 => L * |y 1 + c * y 0|) (L * √(1 + c ^ 2)) := by
  refine ⟨by positivity, fun a b => ?_⟩
  simp only
  rw [← mul_sub, abs_mul, abs_of_nonneg hL, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hL
  exact (abs_abs_sub_abs_le_abs_sub _ _).trans (abs_lin_le c a b)

lemma convexOn_absLin {L : ℝ} (hL : 0 ≤ L) (c : ℝ) :
    ConvexOn ℝ univ (fun y : V2 => L * |y 1 + c * y 0|) :=
  convexOn_abs_affine hL (ℓ := fun y : V2 => y 1 + c * y 0) (by
    intro x y a b hab; simp; ring)

end P1helpers

namespace P1i

/-- s = η/(2R). -/
noncomputable def sl (η R : ℝ) : ℝ := η / (2 * R)
/-- C₁ = {y₂ = s(y₁ − R)}, C₂ = {y₂ = −s(y₁ − R)} (g_j = ι_{C_j}: `0` on `C_j`). -/
def C1 (s R : ℝ) : Set V2 := {y | y 1 - s * (y 0 - R) = 0}
def C2 (s R : ℝ) : Set V2 := {y | y 1 + s * (y 0 - R) = 0}
noncomputable def F : V2 → ℝ := fun y => 1 / 2 * ‖y‖ ^ 2
/-- The data: x = p₁ = (0, −sR), p₂ = (0, sR), v₁ = (sR/2)(−s, 1), v₂ = (sR/2)(s, 1). -/
noncomputable def x (η R : ℝ) : V2 := !₂[0, -(sl η R * R)]
noncomputable def p (η R : ℝ) : Fin 2 → V2 := ![x η R, !₂[0, sl η R * R]]
noncomputable def v (η R : ℝ) : Fin 2 → V2 :=
  ![!₂[-(sl η R * R / 2 * sl η R), sl η R * R / 2], !₂[sl η R * R / 2 * sl η R, sl η R * R / 2]]
noncomputable def D (η R : ℝ) : Fin 2 → Set V2 := ![C1 (sl η R) R, C2 (sl η R) R]
/-- x* = (R, 0). -/
noncomputable def xs (R : ℝ) : V2 := !₂[R, 0]

/-- **Proposition P1(i).** For R > 0 and η ∈ (0, R] (s = η/(2R)): the instance is valid
(f is 1-smooth with C(f, 1); the C_j are convex; each g_j is 0-Lipschitz relative to its
domain); v_j ∈ ∂g_j(p_j); r = 0; J₀ = {1} (p₁ = x, p₂ ≠ x); δ₂ = η; ‖v₂‖ ≤ η; μ̂ = 1;
dom E = C₁ ∩ C₂ = {(R, 0)} = argmin E; and ‖x − x*‖ ≥ R. -/
theorem prop_P1_i {η R : ℝ} (hη : 0 < η) (hηR : η ≤ R) :
    (LipGrad F 1 ∧ ModC F 1 ∧ (∀ j, ExtModC (D η R j) (fun _ => 0) 0) ∧
      ∀ j, ∀ a ∈ D η R j, ∀ b ∈ D η R j, |(0 : ℝ) - 0| ≤ 0 * ‖a - b‖) ∧
    (∀ j, ExtSub (D η R j) (fun _ => 0) 0 (p η R j) (v η R j)) ∧
    resid F (v η R) (x η R) = 0 ∧
    p η R 0 = x η R ∧ p η R 1 ≠ x η R ∧ ‖p η R 1 - x η R‖ = η ∧ ‖v η R 1‖ ≤ η ∧
    muHat 1 (fun _ : Fin 2 => (0 : ℝ)) = 1 ∧
    domE (D η R) = {xs R} ∧
    (∀ y ∈ domE (D η R), ((∀ y' ∈ domE (D η R), Eval F (fun _ : Fin 2 => fun _ => (0 : ℝ)) y
        ≤ Eval F (fun _ : Fin 2 => fun _ => (0 : ℝ)) y') ↔ y = xs R)) ∧
    R ≤ ‖x η R - xs R‖ := by
  have hR : 0 < R := lt_of_lt_of_le hη hηR
  have hs : 0 < sl η R := by unfold sl; positivity
  have hsR : sl η R * R = η / 2 := by unfold sl; field_simp
  have hs1 : sl η R ≤ 1 / 2 := by
    unfold sl; rw [div_le_iff₀ (by positivity)]; linarith
  have hF : F = fun y : V2 => (1 : ℝ) / 2 * ‖y‖ ^ 2 := rfl
  have hdom : domE (D η R) = {xs R} := by
    ext y
    simp only [domE, Fin.forall_fin_two, D, Matrix.cons_val_zero, Matrix.cons_val_one,
      C1, C2, mem_setOf_eq, mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      have h0 : y 0 = R := by
        have : sl η R * (y 0 - R) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · linarith
      apply v2_ext <;> simp [xs] <;> [exact h0; (rw [h0] at h1; linarith)]
    · rintro rfl; simp [xs]
  refine ⟨⟨hF ▸ lipGrad_halfSq 1 zero_le_one, hF ▸ modC_halfSq 1, fun j => ?_,
    fun j a _ b _ => by simp⟩, fun j => ?_, ?_, rfl, ?_, ?_, ?_, ?_, hdom, ?_, ?_⟩
  · -- the C_j are convex
    unfold ExtModC
    have hc : ∀ c : ℝ, Convex ℝ {y : V2 | y 1 + c * (y 0 - R) = 0} := fun c =>
      convex_affine_zero (ℓ := fun y : V2 => y 1 + c * (y 0 - R)) (by
        intro x y a b hab; obtain rfl : b = 1 - a := by linarith
        simp; ring)
    fin_cases j
    · have := hc (-sl η R)
      simp only [neg_mul, ← sub_eq_add_neg] at this
      simpa [D, C1] using convexOn_const (0 : ℝ) this
    · simpa [D, C2] using convexOn_const (0 : ℝ) (hc (sl η R))
  · -- subgradients
    fin_cases j
    · refine ⟨by simp [p, D, C1, x], fun y hy => ?_⟩
      have hy' : y 1 - sl η R * (y 0 - R) = 0 := by simpa [D, C1] using hy
      have h2 : sl η R * R / 2 * (y 1 - sl η R * (y 0 - R)) = 0 := by rw [hy', mul_zero]
      simp only [Fin.zero_eta, Matrix.cons_val_zero, p, v, x, inner_v2]
      simp
      linarith
    · refine ⟨by simp [p, D, C2], fun y hy => ?_⟩
      have hy' : y 1 + sl η R * (y 0 - R) = 0 := by simpa [D, C2] using hy
      have h2 : sl η R * R / 2 * (y 1 + sl η R * (y 0 - R)) = 0 := by rw [hy', mul_zero]
      simp only [Fin.mk_one, Matrix.cons_val_one, p, v, inner_v2]
      simp
      linarith
  · -- r = 0
    unfold resid
    rw [show F = fun y : V2 => (1 : ℝ) / 2 * ‖y‖ ^ 2 from rfl, gradient_halfSq, one_smul,
      Fin.sum_univ_two]
    apply v2_ext <;> simp [v, x]
  · intro h
    have := congrArg (fun y : V2 => y 1) h
    simp [p, x] at this
    linarith
  · simp only [p, x, Matrix.cons_val_one]
    rw [norm_v2]
    simp only [PiLp.sub_apply]
    simp
    rw [show (sl η R * R + sl η R * R) ^ 2 = η ^ 2 by rw [hsR]; ring, Real.sqrt_sq hη.le]
  · have hsq : ‖v η R 1‖ ^ 2 ≤ η ^ 2 := by
      rw [normsq_v2]
      simp only [v, Matrix.cons_val_one]
      simp
      rw [hsR]
      have hs2 : sl η R ^ 2 ≤ 1 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left hs2 (sq_nonneg η)]
    nlinarith [norm_nonneg (v η R 1)]
  · simp [muHat]
  · intro y hy
    rw [hdom] at hy
    rw [mem_singleton_iff.1 hy]
    refine ⟨fun _ => rfl, fun _ y' hy' => ?_⟩
    rw [hdom, mem_singleton_iff] at hy'
    rw [hy']
  · rw [norm_v2]
    apply Real.le_sqrt_of_sq_le
    simp [x, xs]
    nlinarith [sq_nonneg (sl η R * R)]

/-- **P1(i), the unboundedness.** For fixed η > 0 the instances (with the same r = 0,
δ₂ = η, ‖v₂‖ ≤ η and declared numbers) have ‖x − x*‖ unbounded as R → ∞. -/
theorem prop_P1_i_unbounded {η : ℝ} (hη : 0 < η) (M : ℝ) :
    ∃ R, η ≤ R ∧ M < ‖x η R - xs R‖ := by
  refine ⟨max η (M + 1), le_max_left _ _, ?_⟩
  have := (prop_P1_i hη (le_max_left η (M + 1))).2.2.2.2.2.2.2.2.2
  linarith [le_max_right η (M + 1)]

end P1i

namespace P1ii

noncomputable def g (η R : ℝ) : Fin 2 → ℝ → ℝ := ![fun y => η * |y - R|, fun _ => 0]
noncomputable def v (η : ℝ) : Fin 2 → ℝ := ![-η, 0]
noncomputable def L (η : ℝ) : Fin 2 → ℝ := ![η, 0]

/-- **Proposition P1(ii).** On ℝ, F = 0, g₁ = η|· − R| (Lipschitz attribute η), g₂ = 0
(attribute 0), x = p₁ = p₂ = 0, v₁ = −η, v₂ = 0: valid; v_j ∈ ∂g_j(p_j); J₀ = N; ε = 0;
r = −η; μ̂ = 0; argmin E = {R}; |x − x*| = R. -/
theorem prop_P1_ii {η R : ℝ} (hη : 0 < η) (hR : 0 < R) :
    (LipAttr (g η R 0) η ∧ LipAttr (g η R 1) 0 ∧ ModC (g η R 0) 0 ∧ ModC (g η R 1) 0 ∧
      ModC (fun _ : ℝ => (0 : ℝ)) 0 ∧ LipGrad (fun _ : ℝ => (0 : ℝ)) 0) ∧
    (∀ j, ExtSub univ (g η R j) 0 0 (v η j)) ∧
    epsC (0 : ℝ) (fun _ => 0) (v η) (L η) = 0 ∧
    resid (fun _ : ℝ => (0 : ℝ)) (v η) 0 = -η ∧
    muHat 0 (fun _ : Fin 2 => (0 : ℝ)) = 0 ∧
    (∀ y : ℝ, (∀ y', Eval (fun _ => 0) (g η R) y ≤ Eval (fun _ => 0) (g η R) y') ↔ y = R) ∧
    ‖(0 : ℝ) - R‖ = R := by
  have hE : ∀ y, Eval (fun _ => 0) (g η R) y = η * |y - R| := by
    intro y; simp [Eval, g]
  have hgrad : ∀ y : ℝ, gradient (fun _ : ℝ => (0 : ℝ)) y = 0 := fun y => gradient_const y 0
  refine ⟨⟨⟨hη.le, fun a b => ?_⟩, ⟨le_rfl, fun a b => by simp [g]⟩, ?_, ?_, ?_, ?_⟩,
    fun j => ?_, ?_, ?_, by simp [muHat], fun y => ?_, ?_⟩
  · simp only [g, Matrix.cons_val_zero]
    rw [← mul_sub, abs_mul, abs_of_pos hη, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ hη.le
    calc |(|a - R| - |b - R|)| ≤ |(a - R) - (b - R)| := abs_abs_sub_abs_le_abs_sub _ _
      _ = |a - b| := by ring_nf
  · rw [modC_zero_iff]
    simp only [g, Matrix.cons_val_zero]
    exact convexOn_abs_affine hη.le (ℓ := fun y : ℝ => y - R) (by
      intro x y a b hab; obtain rfl : b = 1 - a := by linarith
      simp; ring)
  · rw [modC_zero_iff]; simpa [g] using convexOn_const (0 : ℝ) convex_univ
  · rw [modC_zero_iff]; exact convexOn_const 0 convex_univ
  · intro a b; rw [hgrad, hgrad]; simp
  · fin_cases j
    · refine ⟨mem_univ _, fun y _ => ?_⟩
      simp [g, v]
      have := neg_abs_le (y - R)
      rw [abs_of_pos hR]
      nlinarith
    · exact ⟨mem_univ _, fun y _ => by simp [g, v]⟩
  · rw [epsC_eq_sum]; simp
  · unfold resid; rw [hgrad, Fin.sum_univ_two]; simp [v]
  · rw [hE]
    constructor
    · intro h
      have h1 := h R
      rw [hE, sub_self, abs_zero, mul_zero] at h1
      have : |y - R| = 0 := by
        have := abs_nonneg (y - R)
        nlinarith
      linarith [abs_eq_zero.1 this]
    · rintro rfl y'
      rw [hE, sub_self, abs_zero, mul_zero]
      positivity
  · rw [zero_sub, norm_neg, Real.norm_eq_abs, abs_of_pos hR]

end P1ii

namespace P1iii

noncomputable def F : ℝ → ℝ := fun y => 1 / 2 * ‖y‖ ^ 2
noncomputable def g (L : ℝ) : Fin 2 → ℝ → ℝ := fun _ y => L * |y|

lemma gradF (y : ℝ) : gradient F y = y := by
  have := gradient_halfSq (X := ℝ) 1 y
  rw [one_smul] at this; exact this

lemma E_eq (L y : ℝ) : Eval F (g L) y = 1 / 2 * y ^ 2 + 2 * L * |y| := by
  simp [Eval, F, g]; ring

/-- **Proposition P1(iii).** On ℝ, f = ½y² (declared (1, 1, void)), g₁ = g₂ = L|y|
(attribute L), δ ∈ (0, 2L], x = δ, p_j = 0, v_j = −δ/2: valid; v_j ∈ ∂g_j(0); r = 0;
δ_j = δ; ∂E(x) = {δ + 2L}, so every element of ∂E(x) has modulus δ + 2L > 2L; and T1 still
holds: ε = δ(δ + 2L), μ̂ = 1, τ = √(δ(δ + 2L)) ≥ δ = |x − x*| with argmin E = {0}. -/
theorem prop_P1_iii {L δ : ℝ} (hδ : 0 < δ) (hδL : δ ≤ 2 * L) :
    (LipGrad F 1 ∧ ModC F 1 ∧ ∀ j, LipAttr (g L j) L ∧ ModC (g L j) 0) ∧
    (∀ j, ExtSub univ (g L j) 0 0 (-(δ / 2))) ∧
    resid F (fun _ : Fin 2 => -(δ / 2)) δ = 0 ∧
    (∀ j : Fin 2, ‖(fun _ => (0 : ℝ)) j - δ‖ = δ) ∧
    (∀ u, ExtSub univ (Eval F (g L)) 0 δ u ↔ u = δ + 2 * L) ∧
    (∀ u, ExtSub univ (Eval F (g L)) 0 δ u → 2 * L < |u|) ∧
    epsC δ (fun _ : Fin 2 => (0 : ℝ)) (fun _ => -(δ / 2)) (fun _ => L) = δ * (δ + 2 * L) ∧
    muHat 1 (fun _ : Fin 2 => (0 : ℝ)) = 1 ∧
    tauC ‖resid F (fun _ : Fin 2 => -(δ / 2)) δ‖
      (epsC δ (fun _ : Fin 2 => (0 : ℝ)) (fun _ => -(δ / 2)) (fun _ => L)) 1
        = √(δ * (δ + 2 * L)) ∧
    (∀ y, (∀ y', Eval F (g L) y ≤ Eval F (g L) y') ↔ y = 0) ∧
    ‖δ - 0‖ ≤ √(δ * (δ + 2 * L)) := by
  have hL : 0 < L := by linarith
  have hF : F = fun y : ℝ => (1 : ℝ) / 2 * ‖y‖ ^ 2 := rfl
  have hr : resid F (fun _ : Fin 2 => -(δ / 2)) δ = 0 := by
    unfold resid; rw [gradF, Fin.sum_univ_two]; ring
  have heps : epsC δ (fun _ => (0 : ℝ)) (fun _ : Fin 2 => -(δ / 2)) (fun _ => L)
      = δ * (δ + 2 * L) := by
    rw [epsC_eq_sum, Fin.sum_univ_two]
    simp only [Real.norm_eq_abs, zero_sub, abs_neg, abs_of_pos hδ, abs_div,
      abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  have hsub : ∀ u, ExtSub univ (Eval F (g L)) 0 δ u ↔ u = δ + 2 * L := by
    intro u
    constructor
    · rintro ⟨-, hu⟩
      have key : ∀ h : ℝ, 0 < h → h < δ → |u - (δ + 2 * L)| ≤ h / 2 := by
        intro h h0 hlt
        have a1 := hu (δ + h) (mem_univ _)
        have a2 := hu (δ - h) (mem_univ _)
        simp only [E_eq, zero_div, zero_mul, add_zero] at a1 a2
        simp at a1 a2
        rw [abs_of_pos hδ, abs_of_pos (by linarith : 0 < δ + h)] at a1
        rw [abs_of_pos hδ, abs_of_pos (by linarith : 0 < δ - h)] at a2
        have b1 : h * u ≤ h * (δ + 2 * L + h / 2) := by nlinarith
        have b2 : h * (δ + 2 * L - h / 2) ≤ h * u := by nlinarith
        have c1 := le_of_mul_le_mul_left b1 h0
        have c2 := le_of_mul_le_mul_left b2 h0
        rw [abs_le]; constructor <;> linarith
      by_contra hne
      have hd : 0 < |u - (δ + 2 * L)| := abs_pos.2 (sub_ne_zero.2 hne)
      have := key (min (δ / 2) |u - (δ + 2 * L)|) (lt_min (by linarith) hd)
        (lt_of_le_of_lt (min_le_left _ _) (by linarith))
      have := min_le_right (δ / 2) |u - (δ + 2 * L)|
      linarith
    · rintro rfl
      refine ⟨mem_univ _, fun y _ => ?_⟩
      simp only [E_eq, zero_div, zero_mul, add_zero]
      simp
      rw [abs_of_pos hδ]
      nlinarith [sq_nonneg (y - δ), le_abs_self y]
  have hE0 : Eval F (g L) 0 = 0 := by rw [E_eq]; simp
  refine ⟨⟨hF ▸ lipGrad_halfSq 1 zero_le_one, hF ▸ modC_halfSq 1, fun j =>
    ⟨⟨hL.le, fun a b => ?_⟩, ?_⟩⟩, fun j => ⟨mem_univ _, fun y _ => ?_⟩, hr,
    fun j => ?_, hsub, fun u hu => ?_, heps, by simp [muHat], ?_, fun y => ?_, ?_⟩
  · simp only [g]
    rw [← mul_sub, abs_mul, abs_of_pos hL, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (abs_abs_sub_abs_le_abs_sub _ _) hL.le
  · rw [modC_zero_iff]
    exact convexOn_abs_affine hL.le (ℓ := fun y : ℝ => y) (by intro x y a b _; simp)
  · simp [g]
    have := neg_abs_le y
    have := le_abs_self y
    nlinarith [abs_nonneg y]
  · simp [abs_of_pos hδ]
  · rw [(hsub u).1 hu, abs_of_pos (by linarith)]; linarith
  · rw [hr, norm_zero, heps]
    unfold tauC
    rw [show (0 : ℝ) ^ 2 + 4 * 1 * (δ * (δ + 2 * L)) = 2 ^ 2 * (δ * (δ + 2 * L)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]
    ring
  · constructor
    · intro h
      have h1 := h 0
      rw [hE0, E_eq] at h1
      have : y ^ 2 ≤ 0 := by nlinarith [abs_nonneg y]
      nlinarith [sq_nonneg y]
    · rintro rfl y'
      rw [hE0, E_eq]
      nlinarith [sq_nonneg y', abs_nonneg y']
  · rw [sub_zero, Real.norm_eq_abs, abs_of_pos hδ]
    apply Real.le_sqrt_of_sq_le
    nlinarith

end P1iii

namespace P1iv

/-- s = σt/(2L). -/
noncomputable def sl (σ L t : ℝ) : ℝ := σ * t / (2 * L)
noncomputable def F (σ : ℝ) : V2 → ℝ := fun y => σ / 2 * ‖y‖ ^ 2
/-- g₁ = L|y₂ − s y₁|, g₂ = L|y₂ + s y₁|. -/
noncomputable def g (L s : ℝ) : Fin 2 → V2 → ℝ :=
  ![fun y => L * |y 1 - s * y 0|, fun y => L * |y 1 + s * y 0|]
noncomputable def x (t : ℝ) : V2 := !₂[t, 0]
noncomputable def p (s t : ℝ) : Fin 2 → V2 := ![!₂[t, s * t], !₂[t, -(s * t)]]
noncomputable def v (L s : ℝ) : Fin 2 → V2 := ![!₂[-(L * s), L], !₂[-(L * s), -L]]

lemma g_eq (L s : ℝ) (j : Fin 2) :
    g L s j = fun y => L * |y 1 + (if j = 0 then -s else s) * y 0| := by
  fin_cases j
  · funext y; simp [g, sub_eq_add_neg]
  · funext y; simp [g]

/-- **Proposition P1(iv).** On ℝ², f = (σ/2)‖y‖² (declared (σ, σ, void)), L > 0,
t ∈ (0, 2L/σ], s = σt/(2L) ∈ (0, 1], g₁,₂ = L|y₂ ∓ s y₁|, x = (t, 0), p₁,₂ = (t, ±st),
v₁ = L(−s, 1), v₂ = −L(s, 1): valid (g_j convex, L√(1+s²)- and L√2-Lipschitz);
v_j ∈ ∂g_j(p_j); r = 0; δ₁ = δ₂ = st =: δ (both p_j ≠ x); argmin E = {0};
‖x − x*‖ = t = √(2Lδ/σ); with L_j = L√(1+s²): ε = 4L√(1+s²)δ, μ̂ = σ and
τ = t·√(2√(1+s²)) (so τ/t = √2(1+s²)^{1/4}). -/
theorem prop_P1_iv {σ L t : ℝ} (hσ : 0 < σ) (hL : 0 < L) (ht : 0 < t) (htL : t ≤ 2 * L / σ) :
    (LipGrad (F σ) σ ∧ ModC (F σ) σ ∧
      ∀ j, ModC (g L (sl σ L t) j) 0 ∧ LipAttr (g L (sl σ L t) j) (L * √(1 + sl σ L t ^ 2)) ∧
        LipAttr (g L (sl σ L t) j) (L * √2)) ∧
    (∀ j, ExtSub univ (g L (sl σ L t) j) 0 (p (sl σ L t) t j) (v L (sl σ L t) j)) ∧
    resid (F σ) (v L (sl σ L t)) (x t) = 0 ∧
    (∀ j, p (sl σ L t) t j ≠ x t ∧ ‖p (sl σ L t) t j - x t‖ = sl σ L t * t) ∧
    (∀ y, (∀ y', Eval (F σ) (g L (sl σ L t)) y ≤ Eval (F σ) (g L (sl σ L t)) y') ↔ y = 0) ∧
    ‖x t - 0‖ = t ∧ t = √(2 * L * (sl σ L t * t) / σ) ∧
    epsC (x t) (p (sl σ L t) t) (v L (sl σ L t)) (fun _ => L * √(1 + sl σ L t ^ 2))
      = 4 * L * √(1 + sl σ L t ^ 2) * (sl σ L t * t) ∧
    muHat σ (fun _ : Fin 2 => (0 : ℝ)) = σ ∧
    tauC ‖resid (F σ) (v L (sl σ L t)) (x t)‖
      (epsC (x t) (p (sl σ L t) t) (v L (sl σ L t)) (fun _ => L * √(1 + sl σ L t ^ 2))) σ
      = t * √(2 * √(1 + sl σ L t ^ 2)) := by
  set s := sl σ L t with hsdef
  have hs : 0 < s := by rw [hsdef]; unfold sl; positivity
  have hs1 : s ≤ 1 := by
    rw [hsdef]; unfold sl; rw [div_le_one (by positivity)]
    rw [le_div_iff₀ hσ] at htL; linarith
  have hσt : σ * t = 2 * L * s := by rw [hsdef]; unfold sl; field_simp
  have hF : F σ = fun y : V2 => σ / 2 * ‖y‖ ^ 2 := rfl
  have hr : resid (F σ) (v L s) (x t) = 0 := by
    unfold resid
    rw [hF, gradient_halfSq, Fin.sum_univ_two]
    apply v2_ext <;> simp [v, x]
    linarith
  have hδ : ∀ j, ‖p s t j - x t‖ = s * t := by
    intro j
    rw [norm_v2]
    fin_cases j <;> simp [p, x] <;> rw [Real.sqrt_sq (by positivity)]
  have hpx : ∀ j, p s t j ≠ x t := by
    intro j h
    have := hδ j
    rw [h, sub_self, norm_zero] at this
    have : 0 < s * t := by positivity
    linarith
  have hv : ∀ j, ‖v L s j‖ = L * √(1 + s ^ 2) := by
    intro j
    rw [norm_v2]
    have e : ∀ a : ℝ, a ^ 2 = L ^ 2 → (-(L * s)) ^ 2 + a ^ 2 = L ^ 2 * (1 + s ^ 2) := by
      intro a ha; rw [ha]; ring
    fin_cases j <;> simp [v] <;>
      rw [show (L * s) ^ 2 + L ^ 2 = L ^ 2 * (1 + s ^ 2) by ring, Real.sqrt_mul (by positivity),
        Real.sqrt_sq hL.le]
  have heps : epsC (x t) (p s t) (v L s) (fun _ => L * √(1 + s ^ 2))
      = 4 * L * √(1 + s ^ 2) * (s * t) := by
    rw [epsC_eq_sum, Fin.sum_univ_two, hv, hv, hδ, hδ]; ring
  have hEge : ∀ y, σ / 2 * ‖y‖ ^ 2 ≤ Eval (F σ) (g L s) y := by
    intro y
    simp only [Eval, Fin.sum_univ_two, g, F, Matrix.cons_val_zero, Matrix.cons_val_one]
    nlinarith [mul_nonneg hL.le (abs_nonneg (y 1 - s * y 0)),
      mul_nonneg hL.le (abs_nonneg (y 1 + s * y 0))]
  have hE0 : Eval (F σ) (g L s) 0 = 0 := by simp [Eval, F, g]
  refine ⟨⟨hF ▸ lipGrad_halfSq σ hσ.le, hF ▸ modC_halfSq σ, fun j => ?_⟩, fun j => ?_, hr,
    fun j => ⟨hpx j, hδ j⟩, fun y => ?_, ?_, ?_, heps, by simp [muHat], ?_⟩
  · have hc : (if j = 0 then -s else s) ^ 2 = s ^ 2 := by split_ifs <;> ring
    have hlip := lipAttr_absLin hL.le (if j = 0 then -s else s)
    rw [hc] at hlip
    rw [g_eq, modC_zero_iff]
    refine ⟨convexOn_absLin hL.le _, hlip, lipAttr_mono hlip ?_⟩
    refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) hL.le
    nlinarith
  · refine ⟨mem_univ _, fun y _ => ?_⟩
    fin_cases j
    · simp [g, p, v, inner_v2]
      nlinarith [le_abs_self (y 1 - s * y 0)]
    · simp [g, p, v, inner_v2]
      nlinarith [neg_abs_le (y 1 + s * y 0)]
  · constructor
    · intro h
      have h1 := h 0
      rw [hE0] at h1
      have := hEge y
      have : ‖y‖ ^ 2 ≤ 0 := by nlinarith
      exact norm_eq_zero.1 (by nlinarith [norm_nonneg y])
    · rintro rfl y'
      rw [hE0]
      have := hEge y'
      nlinarith [sq_nonneg ‖y'‖]
  · rw [sub_zero, norm_v2]; simp [x]; rw [Real.sqrt_sq ht.le]
  · rw [show 2 * L * (s * t) / σ = t ^ 2 by
      field_simp; nlinarith [hσt], Real.sqrt_sq ht.le]
  · rw [hr, norm_zero, heps]
    unfold tauC
    have hq : (0 : ℝ) ^ 2 + 4 * σ * (4 * L * √(1 + s ^ 2) * (s * t))
        = (2 * σ * t) ^ 2 * (2 * √(1 + s ^ 2)) := by
      have : 2 * L * s = σ * t := hσt.symm
      linear_combination (8 * σ * t * √(1 + s ^ 2)) * this
    rw [hq, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), zero_add]
    field_simp

/-- **P1(iv), the constant.** τ/t = √(2√(1+s²)) → √2 as t → 0. -/
theorem prop_P1_iv_ratio_tendsto {σ L : ℝ} :
    Tendsto (fun t : ℝ => √(2 * √(1 + sl σ L t ^ 2))) (𝓝 0) (𝓝 (√2)) := by
  have hc : Continuous (fun t : ℝ => √(2 * √(1 + sl σ L t ^ 2))) := by
    unfold sl; fun_prop
  have := hc.tendsto 0
  simpa [sl] using this

/-- **P1(iv), the exponent ½ is sharp.** With σ, L (hence the declared numbers, e.g.
L_j = L√2) fixed: for every C and every exponent q > ½ there is t ∈ (0, 2L/σ] with
‖x − x*‖ = t > C·max(‖r‖, max_j δ_j)^q = C·(st)^q (r = 0, δ_j = st). -/
theorem prop_P1_iv_exponent {σ L : ℝ} (hσ : 0 < σ) (hL : 0 < L) (C q : ℝ) (hq : 1 / 2 < q) :
    ∃ t : ℝ, 0 < t ∧ t ≤ 2 * L / σ ∧
      C * (max ‖resid (F σ) (v L (sl σ L t)) (x t)‖ (sl σ L t * t)) ^ q < ‖x t - 0‖ := by
  set a := σ / (2 * L) with ha
  have ha0 : 0 < a := by positivity
  have he : 0 < 2 * q - 1 := by linarith
  have hcont : Tendsto (fun t : ℝ => C * a ^ q * t ^ (2 * q - 1)) (𝓝 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => t ^ (2 * q - 1)) (𝓝 0) (𝓝 ((0 : ℝ) ^ (2 * q - 1))) :=
      (Real.continuousAt_rpow_const 0 (2 * q - 1) (Or.inr he.le)).tendsto
    rw [Real.zero_rpow he.ne'] at h1
    simpa using h1.const_mul (C * a ^ q)
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 (hcont.eventually (gt_mem_nhds one_pos))
  set t := min (ε / 2) (2 * L / σ) with htdef
  have ht0 : 0 < t := lt_min (by positivity) (by positivity)
  have htL : t ≤ 2 * L / σ := min_le_right _ _
  have htε : dist t 0 < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht0]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hlt := hball htε
  refine ⟨t, ht0, htL, ?_⟩
  obtain ⟨-, -, hr, -⟩ := prop_P1_iv hσ hL ht0 htL
  rw [hr, norm_zero]
  have hst : sl σ L t * t = a * t ^ 2 := by unfold sl; rw [ha]; ring
  rw [hst, max_eq_right (by positivity), sub_zero, norm_v2]
  simp only [x]
  simp
  rw [Real.sqrt_sq ht0.le]
  -- (a t²)^q = a^q t^{2q} = a^q t^{2q−1} t
  have hrp : (a * t ^ 2) ^ q = a ^ q * t ^ (2 * q - 1) * t := by
    rw [Real.mul_rpow ha0.le (by positivity), ← Real.rpow_natCast t 2, ← Real.rpow_mul ht0.le]
    rw [mul_assoc]
    congr 1
    rw [show ((2 : ℕ) : ℝ) * q = (2 * q - 1) + 1 by push_cast; ring, Real.rpow_add ht0,
      Real.rpow_one]
  rw [hrp]
  have : C * a ^ q * t ^ (2 * q - 1) * t < 1 * t := mul_lt_mul_of_pos_right hlt ht0
  linarith

end P1iv

end OCF.H3

#print axioms OCF.H3.lip_modC_nonpos
#print axioms OCF.H3.lip_modC_nonpos_vec
#print axioms OCF.H3.lipAttr_sigma_eq_zero
#print axioms OCF.H3.lipAttr_smul
#print axioms OCF.H3.extModC_smul
#print axioms OCF.H3.extSub_strong
#print axioms OCF.H3.extSub_monotone
#print axioms OCF.H3.proxChar_of_forall
#print axioms OCF.H3.norm_subgrad_le
#print axioms OCF.H3.quad_root
#print axioms OCF.H3.consensus_minorant
#print axioms OCF.H3.HCert.extModC_E
#print axioms OCF.H3.growth_of_min
#print axioms OCF.H3.argmin_unique
#print axioms OCF.H3.consensus_certificate
#print axioms OCF.H3.ConsIter.readout_subgrad
#print axioms OCF.H3.ConsIter.parallel_axis
#print axioms OCF.H3.ConsIter.diag_prox_objective
#print axioms OCF.H3.ConsIter.r_eq
#print axioms OCF.H3.ConsIter.readout_bounds
#print axioms OCF.H3.ConsIter.fixed_readouts
#print axioms OCF.H3.ConsIter.explicit_fixed_point
#print axioms OCF.H3.ConsIter.Typed.hcert
#print axioms OCF.H3.ConsIter.epsIt_le
#print axioms OCF.H3.ConsIter.cert_iter
#print axioms OCF.H3.ConsIter.apriori_rate
#print axioms OCF.H3.ConsIter.fixed_argmin
#print axioms OCF.H3.ConsIter.apriori_count
#print axioms OCF.H3.ConsIter.ebar_le_of_count
#print axioms OCF.H3.P2.infDist_eq
#print axioms OCF.H3.P2.valid
#print axioms OCF.H3.P2.realises
#print axioms OCF.H3.P2.typed
#print axioms OCF.H3.P2.argmin_zero
#print axioms OCF.H3.P2.step
#print axioms OCF.H3.P2.orbit
#print axioms OCF.H3.P2.no_linear_rate
#print axioms OCF.H3.P2.orbit_z
#print axioms OCF.H3.P1i.prop_P1_i
#print axioms OCF.H3.P1i.prop_P1_i_unbounded
#print axioms OCF.H3.P1ii.prop_P1_ii
#print axioms OCF.H3.P1iii.prop_P1_iii
#print axioms OCF.H3.P1iv.prop_P1_iv
#print axioms OCF.H3.P1iv.prop_P1_iv_ratio_tendsto
#print axioms OCF.H3.P1iv.prop_P1_iv_exponent

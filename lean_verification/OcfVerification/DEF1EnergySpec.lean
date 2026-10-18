/-
DEF1 (energy specifications) — the landed Proposition "Moduli of a valid specification"
(prop:spec-moduli (a)–(c)), its sharpness remark (rem:spec-sharpness), and the small claims of
def:moduli and rem:sigma-infinite that it uses.

Source of truth: the landed text sections/03_energy_and_primitives/01_energy_specifications.tex
(def:moduli, rem:sigma-infinite, def:kernel-attribute, def:prox-attribute, def:frame-lift,
def:energy-spec, the obligations (O1)–(O3), prop:spec-moduli, rem:spec-sharpness);
project_plan/done/proof_audits/DEF1_energy_specification/01_derivation.md (F1–F4, D1.5, Remark R1;
sha256 prefix ddc990f3408c62fc, unchanged by this pass) and 03_adjudication.md (tier call
PROSE-ONLY recommended; this pass formalises the proposition anyway, as commissioned).

DEFINITIONAL MAP:
* ℝᵈ — G3's `Vec d = EuclideanSpace ℝ (Fin d)`; (−∞, +∞]-valued functions — `· → EReal`
  (never ⊥ is a hypothesis where used). Generic results hold in any real Hilbert space `E`.
* β-smooth — G3's `LipGrad`; C(f, σ) for real f — G3's `ModC`; for extended-valued h —
  `CurvClaim h σ` (convex epigraph of h − (σ/2)‖·‖², B&C Def. 8.1; on ℝᵈ it is G12's `NModC`
  verbatim, `curvClaim_iff_nmodC`); `curvClaim_toE_iff`: the two agree for real f.
* β(f) := inf{β ≥ 0 : f β-smooth} ∈ [0, ∞] — `betaMod` (ℝ≥0∞); σ(h) := sup{σ ∈ ℝ : C(h, σ)}
  ∈ [−∞, +∞] — `sigmaMod` (EReal, sup ∅ = −∞). dom, argmin — `dom`, `argmin`.
* Γ₀(ℝᵈ) — `Gamma0` (never −∞, somewhere finite, lsc, convex epigraph).
* Specification — `Spec` with S = Fin nS, N = Fin nN; smooth term (fᵢ, wᵢ, βᵢ, σᵢ, Aᵢ) —
  `SmoothTerm` whose attributes are G12's `SDecl` (β : [0, ∞], σ : [−∞, ∞), A : void or a kernel
  attribute (K, ν), ν > 0); non-smooth term (gⱼ, σⱼ, πⱼ, Wⱼ) — `NonsmoothTerm`, σⱼ : ℝ≥0, πⱼ —
  G12's `ProxAttr` (oracle | explicit(𝒫, κ)), Wⱼ — `FrameSlot` (void | W ∈ ℝ^{n×d}, any n).
  Validity — `Spec.Valid sem`: fᵢ ∈ C¹, wᵢ > 0, G12's `SDecl.Valid` (fᵢ βᵢ-smooth, C(fᵢ, σᵢ),
  (Kᵢ, νᵢ) valid; ∞ / −∞ make no claim), gⱼ ∈ Γ₀, C(gⱼ, σⱼ), explicit prox attributes valid in
  G12's abstract program semantics `ProgSem` (every result holds for every semantics), and
  WⱼᵀWⱼ = cⱼI, cⱼ > 0.
* E = Σwᵢfᵢ + Σgⱼ — `Spec.E`; F = Σwᵢfᵢ — `Spec.F` (G12's `sumF`); σ̂ — `Spec.sigmaHat` (−∞ if
  some σᵢ = −∞); Σwᵢβᵢ — `Spec.betaSum` (G12's `betaHatX`); (O1) — `Spec.O1`.
* ∇²f(x) — `hess f x := D(∇f)(x)` (symmetric for f ∈ C²: `hess_symm`); ∇²f(x) ⪰ σI —
  ∀ v, σ‖v‖² ≤ ⟨∇²f(x)v, v⟩; λ_min — `lamMinE` (inf of G12's eigenvalues `opEv` in EReal, = +∞ on
  the empty spectrum d = 0; equal to G12's `opLamMin` for d ≥ 1: `lamMinE_eq_opLamMin`);
  ‖·‖₂ — the operator norm (`‖hess f x‖₊` in ℝ≥0∞).
* "largest strong-convexity constant" — `IsGreatest {σ | 0 < σ ∧ C(E, σ)} μ`.

STATEMENTS FORMALISED (statement + proof, no sorry):
* prop:spec-moduli (a): `Spec.spec_moduli_a` (σ̂ ≤ σ(E) and β(F) ≤ Σwᵢβᵢ). The smooth part reuses
  G12's `rule_sum_a` (whose β clause is G3's `Decl.betaHat_valid`); the extended-valued sum rule
  is new here (`curvIneq_add`, `curvIneq_sum`, via the domain form `curvClaim_iff_curvIneq`).
* prop:spec-moduli (b): `spec_moduli_b` (C(f, σ) ⇔ ∇²f ⪰ σI everywhere; σ(f) = inf_x λ_min;
  β(f) = sup_x ‖∇²f(x)‖₂), any d; `spec_moduli_b_opLamMin` (d ≥ 1, real λ_min); components
  `modC_iff_hess`, `sigmaMod_eq_iInf_lamMin`, `lipGrad_iff_hess`, `betaMod_eq_iSup`.
* prop:spec-moduli (c): `Spec.spec_moduli_c` (C(E, σ(E)) for σ(E) ∈ ℝ; for σ(E) > 0 and (O1):
  μ = σ(E) is the largest strong-convexity constant, μ ≥ σ̂, argmin E is one point; for (O1) and
  σ(E) = +∞: dom E = argmin E = {x₀}). Generic pieces: `curvClaim_sigmaMod`,
  `exists_argmin_eq_singleton` (B&C Cor. 11.17, proved from lsc on compact balls),
  `sigmaMod_eq_top_iff`; `Spec.E_lsc`, `Spec.E_ne_bot`, `Spec.dom_E` (dom E = ⋂ dom gⱼ).
* The sentence after the proposition (N = ∅, F ∈ C²: E = F, σ(E) = inf_x γ(x)):
  `sigmaMod_E_of_N_empty`.
* def:moduli "β(f) attained when finite": `betaMod_attained`.
* rem:sigma-infinite: `sigmaMod_eq_top_iff`, `sigmaMod_toE_lt_top` (needs d ≥ 1, see below),
  `sigmaMod_indicator_zero` (σ(ι_{0}) = +∞).
* rem:spec-sharpness: `sharp_sigma_quadratics` (σ(½x₁²) = σ(½x₂²) = 0, σ(sum) = 1 on ℝ²),
  `sharp_sigma_quartics` (σ(x⁴) = σ((x−1)⁴) = 0, σ(sum) = 6; on ℝ as the model of ℝ¹),
  `sharp_beta` (fᵢ = (βᵢ/2)‖·‖², d ≥ 1: β(fᵢ) = βᵢ, β(Σwᵢfᵢ) = Σwᵢβ(fᵢ)).

GAPS EXPOSED IN THE LANDED TEXT (d = 0 edge cases; nothing for d ≥ 1):
* rem:sigma-infinite "σ(f) < ∞ for f ∈ C¹(ℝᵈ)" needs d ≥ 1 (ℝ⁰ is one point, σ = +∞).
* prop:spec-moduli (b) "σ(f) = inf_x λ_min(∇²f(x))" at d = 0 needs λ_min(empty spectrum) = +∞;
  formalised with that convention (`lamMinE`).
* rem:spec-sharpness "attained by fᵢ = (βᵢ/2)‖·‖²" needs d ≥ 1 (at d = 0, β(fᵢ) = 0).

NOT COVERED (remain PROSE-ONLY): def:real-ram and the operational content of explicit prox
attributes (abstracted by `ProgSem`), ex:l1-prox, rem:kernel-attribute, rem:lift (frame algebra),
the obligation witnesses after def:energy-spec.

Status tier: FORMALISED (statement + proof, no sorry) for prop:spec-moduli (a)–(c), the
sentence after it, rem:spec-sharpness, def:moduli (attainment of β) and rem:sigma-infinite.
-/
import Mathlib
import OcfVerification.G12TypingRules

open scoped ENNReal NNReal Gradient
open Set

set_option linter.unusedSectionVars false

namespace OCF.DEF1

open OCF.G3 (Vec LipGrad ModC StrongMono modC_iff_strongMono)

/-! ## §1. The curvature claim for extended-valued functions, the two moduli -/

section Moduli

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The curvature claim C(h, σ) for h : E → (−∞, +∞] (landed def:moduli): h − (σ/2)‖·‖² is
convex, i.e. its epigraph is convex (B&C Def. 8.1). On `Vec d` this is G12's `NModC` verbatim
(`curvClaim_iff_nmodC`). -/
def CurvClaim (h : E → EReal) (σ : ℝ) : Prop :=
  Convex ℝ {p : E × ℝ | h p.1 ≤ ((p.2 + σ / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)}

/-- The curvature modulus σ(h) := sup{σ ∈ ℝ : C(h, σ)} ∈ [−∞, +∞] (landed def:moduli). -/
noncomputable def sigmaMod (h : E → EReal) : EReal :=
  sSup {s : EReal | ∃ σ : ℝ, s = σ ∧ CurvClaim h σ}

/-- The smoothness modulus β(f) := inf{β ≥ 0 : f is β-smooth} ∈ [0, ∞] (landed def:moduli). -/
noncomputable def betaMod (f : E → ℝ) : ℝ≥0∞ :=
  ⨅ (β : ℝ≥0) (_ : LipGrad f β), (β : ℝ≥0∞)

/-- A real-valued function as a function into (−∞, +∞]. -/
def toE (f : E → ℝ) : E → EReal := fun x => (f x : EReal)

/-- The effective domain dom h = {h < +∞}. -/
def dom (h : E → EReal) : Set E := {x | h x ≠ ⊤}

/-- argmin h = {x : h(x) ≤ h(y) for all y}. -/
def argmin (h : E → EReal) : Set E := {x | ∀ y, h x ≤ h y}

/-- For real-valued f, C(f, σ) is G3's `ModC` (f − (σ/2)‖·‖² convex on E). -/
theorem curvClaim_toE_iff (f : E → ℝ) (σ : ℝ) : CurvClaim (toE f) σ ↔ ModC f σ := by
  unfold CurvClaim ModC toE
  rw [convexOn_iff_convex_epigraph]
  have : {p : E × ℝ | ((f p.1 : ℝ) : EReal) ≤ ((p.2 + σ / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)}
      = {p : E × ℝ | p.1 ∈ univ ∧ f p.1 - σ / 2 * ‖p.1‖ ^ 2 ≤ p.2} := by
    ext p
    simp only [mem_setOf_eq, EReal.coe_le_coe_iff, mem_univ, true_and]
    constructor <;> intro h <;> linarith
  rw [this]

/-- ‖a•x + b•y‖² = a‖x‖² + b‖y‖² − ab‖x − y‖² for a + b = 1. -/
lemma norm_comb_sq (x y : E) {a b : ℝ} (hab : a + b = 1) :
    ‖a • x + b • y‖ ^ 2 = a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2 - a * b * ‖x - y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    real_inner_smul_left, real_inner_smul_right]
  have hb : b = 1 - a := by linarith
  subst hb
  rw [real_inner_comm x y]
  ring

/-- The domain form of the curvature claim: for x, y ∈ dom h with h(x) = r, h(y) = s, and
a, b ≥ 0, a + b = 1, h(ax + by) ≤ ar + bs − (σ/2)ab‖x − y‖². -/
def CurvIneq (h : E → EReal) (σ : ℝ) : Prop :=
  ∀ (x y : E) (r s : ℝ), h x = r → h y = s → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    h (a • x + b • y) ≤ ((a * r + b * s - σ / 2 * (a * b * ‖x - y‖ ^ 2) : ℝ) : EReal)

lemma exists_coe_of_le {e : EReal} {c : ℝ} (hb : e ≠ ⊥) (hle : e ≤ (c : EReal)) :
    ∃ r : ℝ, e = r :=
  ⟨e.toReal, (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top c) hle) hb).symm⟩

/-- For h never −∞, C(h, σ) ⇔ the domain form. -/
theorem curvClaim_iff_curvIneq {h : E → EReal} (hb : ∀ x, h x ≠ ⊥) (σ : ℝ) :
    CurvClaim h σ ↔ CurvIneq h σ := by
  constructor
  · intro hc x y r s hx hy a b ha hb' hab
    have hp : (x, r - σ / 2 * ‖x‖ ^ 2) ∈
        {p : E × ℝ | h p.1 ≤ ((p.2 + σ / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)} := by
      simp only [mem_setOf_eq, hx, sub_add_cancel, le_refl]
    have hq : (y, s - σ / 2 * ‖y‖ ^ 2) ∈
        {p : E × ℝ | h p.1 ≤ ((p.2 + σ / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)} := by
      simp only [mem_setOf_eq, hy, sub_add_cancel, le_refl]
    have := hc hp hq ha hb' hab
    simp only [mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd,
      smul_eq_mul] at this
    refine this.trans (le_of_eq ?_)
    congr 1
    rw [norm_comb_sq x y hab]
    ring
  · intro hc p hp q hq a b ha hb' hab
    simp only [mem_setOf_eq] at hp hq ⊢
    obtain ⟨r, hr⟩ := exists_coe_of_le (hb _) hp
    obtain ⟨s, hs⟩ := exists_coe_of_le (hb _) hq
    rw [hr, EReal.coe_le_coe_iff] at hp
    rw [hs, EReal.coe_le_coe_iff] at hq
    have := hc p.1 q.1 r s hr hs a b ha hb' hab
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    refine this.trans (EReal.coe_le_coe_iff.2 ?_)
    rw [norm_comb_sq p.1 q.1 hab]
    nlinarith [mul_nonneg ha hb', sq_nonneg ‖p.1 - q.1‖]

/-- Downward closure of C(h, ·) (domain form). -/
lemma curvIneq_anti {h : E → EReal} {σ σ' : ℝ} (hc : CurvIneq h σ') (hle : σ ≤ σ') :
    CurvIneq h σ := by
  intro x y r s hx hy a b ha hb hab
  refine (hc x y r s hx hy a b ha hb hab).trans (EReal.coe_le_coe_iff.2 ?_)
  have : 0 ≤ a * b * ‖x - y‖ ^ 2 := by positivity
  nlinarith

/-- Sum rule (domain form): C(h₁, σ₁), C(h₂, σ₂) give C(h₁ + h₂, σ₁ + σ₂), for h₁, h₂ never −∞. -/
lemma curvIneq_add {h₁ h₂ : E → EReal} {σ₁ σ₂ : ℝ} (hb₁ : ∀ x, h₁ x ≠ ⊥) (hb₂ : ∀ x, h₂ x ≠ ⊥)
    (c₁ : CurvIneq h₁ σ₁) (c₂ : CurvIneq h₂ σ₂) :
    CurvIneq (fun x => h₁ x + h₂ x) (σ₁ + σ₂) := by
  have split : ∀ x (r : ℝ), h₁ x + h₂ x = r → ∃ r₁ r₂ : ℝ, h₁ x = r₁ ∧ h₂ x = r₂ ∧ r = r₁ + r₂ := by
    intro x r hx
    have t1 : h₁ x ≠ ⊤ := by
      intro ht; rw [ht, EReal.top_add_of_ne_bot (hb₂ x)] at hx; exact EReal.coe_ne_top r hx.symm
    have t2 : h₂ x ≠ ⊤ := by
      intro ht; rw [ht, EReal.add_top_of_ne_bot (hb₁ x)] at hx; exact EReal.coe_ne_top r hx.symm
    refine ⟨(h₁ x).toReal, (h₂ x).toReal, (EReal.coe_toReal t1 (hb₁ x)).symm,
      (EReal.coe_toReal t2 (hb₂ x)).symm, ?_⟩
    rw [← EReal.coe_toReal t1 (hb₁ x), ← EReal.coe_toReal t2 (hb₂ x), ← EReal.coe_add] at hx
    exact (EReal.coe_injective hx).symm
  intro x y r s hx hy a b ha hb hab
  obtain ⟨r₁, r₂, hx₁, hx₂, rfl⟩ := split x r hx
  obtain ⟨s₁, s₂, hy₁, hy₂, rfl⟩ := split y s hy
  have e1 := c₁ x y r₁ s₁ hx₁ hy₁ a b ha hb hab
  have e2 := c₂ x y r₂ s₂ hx₂ hy₂ a b ha hb hab
  refine (add_le_add e1 e2).trans (le_of_eq ?_)
  rw [← EReal.coe_add]
  congr 1
  ring

lemma ne_bot_sum {ι : Type*} (s : Finset ι) (g : ι → E → EReal) (hb : ∀ j x, g j x ≠ ⊥) (x : E) :
    ∑ j ∈ s, g j x ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    exact EReal.add_ne_bot_iff.2 ⟨hb j x, ih⟩

/-- Finite sums (domain form). -/
lemma curvIneq_sum {ι : Type*} (s : Finset ι) (g : ι → E → EReal) (σ : ι → ℝ)
    (hb : ∀ j x, g j x ≠ ⊥) (hc : ∀ j ∈ s, CurvIneq (g j) (σ j)) :
    CurvIneq (fun x => ∑ j ∈ s, g j x) (∑ j ∈ s, σ j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x y r s' hx hy a b ha hb' hab
    simp only [Finset.sum_empty] at hx hy ⊢
    have hr : r = 0 := by exact_mod_cast hx.symm
    have hs : s' = 0 := by exact_mod_cast hy.symm
    subst hr hs
    simp
  | insert j s hj ih =>
    have := curvIneq_add (hb j) (ne_bot_sum s g hb) (hc j (Finset.mem_insert_self j s))
      (ih fun k hk => hc k (Finset.mem_insert_of_mem hk))
    simpa only [Finset.sum_insert hj] using this

/-- sup{σ ∈ ℝ : σ ≤ m} = m in [−∞, +∞]. -/
lemma sSup_coe_le (m : EReal) : sSup {s : EReal | ∃ σ : ℝ, s = σ ∧ (σ : EReal) ≤ m} = m := by
  apply le_antisymm
  · exact sSup_le fun _ ⟨σ, hs, h⟩ => hs ▸ h
  · refine le_of_forall_lt_imp_le_of_dense fun c hc => ?_
    obtain ⟨y, hcy, hym⟩ := EReal.exists_between_coe_real hc
    exact hcy.le.trans (le_sSup ⟨y, rfl, hym.le⟩)

/-- If C(h, σ) holds for some σ > c, then C(h, c) holds. -/
lemma curvIneq_of_lt_sigmaMod {h : E → EReal} (hb : ∀ x, h x ≠ ⊥) {c : ℝ}
    (hc : (c : EReal) < sigmaMod h) : CurvIneq h c := by
  obtain ⟨_, ⟨σ, rfl, hσ⟩, hlt⟩ := lt_sSup_iff.1 hc
  exact curvIneq_anti ((curvClaim_iff_curvIneq hb σ).1 hσ) (EReal.coe_lt_coe_iff.1 hlt).le

/-- **prop:spec-moduli (c), first clause, for any h never −∞.** If σ(h) ∈ ℝ then C(h, σ(h)). -/
theorem curvClaim_sigmaMod {h : E → EReal} (hb : ∀ x, h x ≠ ⊥) {μ : ℝ} (hμ : sigmaMod h = μ) :
    CurvClaim h μ := by
  rw [curvClaim_iff_curvIneq hb]
  intro x y r s hx hy a b ha hb' hab
  have hall : ∀ σ : ℝ, σ < μ → h (a • x + b • y) ≤
      ((a * r + b * s - σ / 2 * (a * b * ‖x - y‖ ^ 2) : ℝ) : EReal) := fun σ hσ =>
    curvIneq_of_lt_sigmaMod hb (by rw [hμ]; exact_mod_cast hσ) x y r s hx hy a b ha hb' hab
  obtain ⟨t, ht⟩ := exists_coe_of_le (hb _) (hall (μ - 1) (by linarith))
  rw [ht, EReal.coe_le_coe_iff]
  set K := a * b * ‖x - y‖ ^ 2
  have hK : 0 ≤ K := by positivity
  have hall' : ∀ σ : ℝ, σ < μ → t ≤ a * r + b * s - σ / 2 * K := fun σ hσ => by
    have := hall σ hσ; rw [ht, EReal.coe_le_coe_iff] at this; exact this
  by_contra hcon
  push Not at hcon
  rcases hK.lt_or_eq with hKp | hK0
  · set σ := (μ + 2 * (a * r + b * s - t) / K) / 2
    have hμ' : 2 * (a * r + b * s - t) / K < μ := by
      rw [div_lt_iff₀ hKp]; nlinarith
    have h1 := hall' σ (by simp only [σ]; linarith)
    have h2 : σ * K > 2 * (a * r + b * s - t) := by
      have : 2 * (a * r + b * s - t) / K < σ := by simp only [σ]; linarith
      rwa [div_lt_iff₀ hKp] at this
    nlinarith
  · have := hall' (μ - 1) (by linarith)
    rw [← hK0] at this hcon
    linarith

/-- rem:sigma-infinite: for h never −∞, σ(h) = +∞ iff dom h has at most one point. -/
theorem sigmaMod_eq_top_iff {h : E → EReal} (hb : ∀ x, h x ≠ ⊥) :
    sigmaMod h = ⊤ ↔ (dom h).Subsingleton := by
  constructor
  · intro htop x hx y hy
    by_contra hxy
    obtain ⟨r, hr⟩ : ∃ r : ℝ, h x = r := ⟨(h x).toReal, (EReal.coe_toReal hx (hb x)).symm⟩
    obtain ⟨s, hs⟩ : ∃ s : ℝ, h y = s := ⟨(h y).toReal, (EReal.coe_toReal hy (hb y)).symm⟩
    have hall : ∀ σ : ℝ, h ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) ≤
        (((1 / 2) * r + (1 / 2) * s - σ / 2 * ((1 / 2) * (1 / 2) * ‖x - y‖ ^ 2) : ℝ) : EReal) :=
      fun σ => curvIneq_of_lt_sigmaMod hb (by rw [htop]; exact EReal.coe_lt_top σ) x y r s hr hs
        _ _ (by norm_num) (by norm_num) (by norm_num)
    obtain ⟨t, ht⟩ := exists_coe_of_le (hb _) (hall 0)
    have hK : 0 < ‖x - y‖ ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hxy
      positivity
    have := hall (8 * ((r + s) / 2 - t + 1) / ‖x - y‖ ^ 2)
    rw [ht, EReal.coe_le_coe_iff] at this
    have e : 8 * ((r + s) / 2 - t + 1) / ‖x - y‖ ^ 2 / 2 * (1 / 2 * (1 / 2) * ‖x - y‖ ^ 2)
        = (r + s) / 2 - t + 1 := by
      have hn : ‖x - y‖ ≠ 0 := norm_ne_zero_iff.2 (sub_ne_zero.2 hxy)
      field_simp; ring
    rw [e] at this
    linarith
  · intro hsub
    apply le_antisymm le_top
    have hall : ∀ σ : ℝ, CurvClaim h σ := by
      intro σ
      rw [curvClaim_iff_curvIneq hb]
      intro x y r s hx hy a b ha hb' hab
      have hxd : x ∈ dom h := by simp [dom, hx]
      have hyd : y ∈ dom h := by simp [dom, hy]
      have hxy := hsub hxd hyd
      subst hxy
      rw [← add_smul, hab, one_smul, hx]
      rw [hx] at hy
      have hrs : r = s := by exact_mod_cast hy
      subst hrs
      simp only [sub_self, norm_zero]
      have e : a * r + b * r - σ / 2 * (a * b * 0 ^ 2) = r := by
        have : b = 1 - a := by linarith
        subst this; ring
      rw [e]
    have : sSup {s : EReal | ∃ σ : ℝ, s = σ ∧ (σ : EReal) ≤ ⊤} = ⊤ := sSup_coe_le ⊤
    rw [← this]
    exact sSup_le_sSup fun s ⟨σ, hs, _⟩ => ⟨σ, hs, hall σ⟩

/-- Strong convexity of a proper lsc function on a proper space gives exactly one minimiser
(B&C Cor. 11.17; proved here from lsc on compact balls). -/
theorem exists_argmin_eq_singleton [ProperSpace E] {h : E → EReal} (hb : ∀ x, h x ≠ ⊥)
    (hlsc : LowerSemicontinuous h) (hne : (dom h).Nonempty) {σ : ℝ} (hσ : 0 < σ)
    (hc : CurvClaim h σ) : ∃ x₀, argmin h = {x₀} := by
  have hci := (curvClaim_iff_curvIneq hb σ).1 hc
  obtain ⟨x0, hx0⟩ := hne
  obtain ⟨c, hcx⟩ : ∃ c : ℝ, h x0 = c := ⟨(h x0).toReal, (EReal.coe_toReal hx0 (hb x0)).symm⟩
  -- a lower bound on the unit ball
  obtain ⟨p1, hp1, hmin1⟩ := (hlsc.lowerSemicontinuousOn (Metric.closedBall x0 1)).exists_isMinOn
    ⟨x0, Metric.mem_closedBall_self zero_le_one⟩ (isCompact_closedBall x0 1)
  rw [isMinOn_iff] at hmin1
  obtain ⟨m, hm⟩ := exists_coe_of_le (hb p1)
    ((hmin1 x0 (Metric.mem_closedBall_self zero_le_one)).trans_eq hcx)
  have hmc : m ≤ c := by
    have := hmin1 x0 (Metric.mem_closedBall_self zero_le_one)
    rwa [hm, hcx, EReal.coe_le_coe_iff] at this
  set R : ℝ := 2 + 2 * (c - m) / σ with hR
  have hR2 : 2 ≤ R := by
    have : 0 ≤ 2 * (c - m) / σ := div_nonneg (by linarith) hσ.le
    linarith
  -- growth outside the ball of radius R
  have grow : ∀ z, R < ‖z - x0‖ → h x0 < h z := by
    intro z hz
    by_cases htop : h z = ⊤
    · rw [htop, hcx]; exact EReal.coe_lt_top c
    obtain ⟨t, ht⟩ : ∃ t : ℝ, h z = t := ⟨(h z).toReal, (EReal.coe_toReal htop (hb z)).symm⟩
    set ρ := ‖z - x0‖
    have hρ : 0 < ρ := by linarith
    set b := ρ⁻¹
    set a := 1 - b
    have hbρ : b * ρ = 1 := inv_mul_cancel₀ hρ.ne'
    have hb0 : 0 ≤ b := inv_nonneg.2 hρ.le
    have hb1 : b ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
    have hq : a • x0 + b • z ∈ Metric.closedBall x0 1 := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      have : a • x0 + b • z - x0 = b • (z - x0) := by simp only [a]; module
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb0, hbρ]
    have h1 := hci x0 z c t hcx ht a b (by simp only [a]; linarith) hb0 (by simp only [a]; ring)
    have h2 := hmin1 _ hq
    rw [hm] at h2
    have h3 := EReal.coe_le_coe_iff.1 (h2.trans h1)
    rw [norm_sub_rev x0 z] at h3
    have key : ρ * (a * c + b * t - σ / 2 * (a * b * ρ ^ 2))
        = ρ * c - c + t - σ / 2 * (ρ - 1) * ρ := by
      simp only [a, b]
      field_simp
    have h4 : ρ * m ≤ ρ * c - c + t - σ / 2 * (ρ - 1) * ρ := by
      rw [← key]; exact mul_le_mul_of_nonneg_left h3 hρ.le
    have h5 : σ / 2 * (ρ - 1) ≥ σ / 2 + (c - m) := by
      have e : σ / 2 * (2 * (c - m) / σ) = c - m := by field_simp
      nlinarith
    rw [hcx, ht, EReal.coe_lt_coe_iff]
    nlinarith
  -- the minimiser on the ball of radius R is global
  obtain ⟨p, hp, hminR⟩ := (hlsc.lowerSemicontinuousOn (Metric.closedBall x0 R)).exists_isMinOn
    ⟨x0, Metric.mem_closedBall_self (by linarith)⟩ (isCompact_closedBall x0 R)
  rw [isMinOn_iff] at hminR
  have hpmin : p ∈ argmin h := by
    intro y
    by_cases hy : ‖y - x0‖ ≤ R
    · exact hminR y (by rw [Metric.mem_closedBall, dist_eq_norm]; exact hy)
    · exact (hminR x0 (Metric.mem_closedBall_self (by linarith))).trans
        (grow y (lt_of_not_ge hy)).le
  refine ⟨p, Set.eq_singleton_iff_unique_mem.2 ⟨hpmin, fun x hx => ?_⟩⟩
  by_contra hxp
  have e1 := hx p
  have e2 := hpmin x
  obtain ⟨v, hv⟩ := exists_coe_of_le (hb p) ((hpmin x0).trans_eq hcx)
  have hxv : h x = v := le_antisymm (e1.trans_eq hv) (hv ▸ e2)
  have := hci x p v v hxv hv (1 / 2) (1 / 2) (by norm_num) (by norm_num) (by norm_num)
  have h6 := (hpmin _).trans this
  rw [hv, EReal.coe_le_coe_iff] at h6
  have : 0 < ‖x - p‖ ^ 2 := by
    have : x - p ≠ 0 := sub_ne_zero.2 hxp
    positivity
  nlinarith

/-- def:moduli: β(f) is attained when finite. -/
theorem betaMod_attained {f : E → ℝ} (hfin : betaMod f ≠ ⊤) : LipGrad f (betaMod f).toReal := by
  intro u v
  by_contra hcon
  push Not at hcon
  have hpos : 0 < ‖u - v‖ := by
    rcases (norm_nonneg (u - v)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hcon
      have : u = v := sub_eq_zero.1 (norm_eq_zero.1 h.symm)
      subst this; simp at hcon
  set c := ‖gradient f u - gradient f v‖ / ‖u - v‖
  have hc : (betaMod f).toReal < c := by rw [lt_div_iff₀ hpos]; exact hcon
  have hlt : betaMod f < ENNReal.ofReal c := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt ENNReal.toReal_nonneg hc)).2 hc
  obtain ⟨β, hβ⟩ := iInf_lt_iff.1 hlt
  obtain ⟨hL, hβc⟩ := iInf_lt_iff.1 hβ
  have hβc' : (β : ℝ) < c := by
    rw [← ENNReal.ofReal_coe_nnreal] at hβc
    exact (ENNReal.ofReal_lt_ofReal_iff_of_nonneg β.2).1 hβc
  have := hL u v
  have : (β : ℝ) * ‖u - v‖ < c * ‖u - v‖ := mul_lt_mul_of_pos_right hβc' hpos
  have hcc : c * ‖u - v‖ = ‖gradient f u - gradient f v‖ := div_mul_cancel₀ _ hpos.ne'
  linarith

end Moduli

/-! ## §2. Energy specifications (def:energy-spec) and prop:spec-moduli (a), (c) -/

section Spec

variable {d : ℕ} {Prog : Type*}

open OCF.G12 (SDecl KComp ProxAttr ProgSem NModC sumF betaHatX sigmaHatX rule_sum_a
  differentiable_of_C1 contDiff_sumF extSum_of_fin)

/-- On ℝᵈ the curvature claim is G12's `NModC`, verbatim. -/
theorem curvClaim_iff_nmodC (g : Vec d → EReal) (σ : ℝ) : CurvClaim g σ ↔ NModC g σ := Iff.rfl

/-- Γ₀(ℝᵈ) (B&C Def. 9.12): proper (never −∞, somewhere finite), lower semicontinuous,
convex (convex epigraph = C(g, 0)). -/
structure Gamma0 (g : Vec d → EReal) : Prop where
  ne_bot : ∀ x, g x ≠ ⊥
  dom_nonempty : (dom g).Nonempty
  lsc : LowerSemicontinuous g
  convex : CurvClaim g 0

/-- A frame slot: void (`none`) or a matrix W ∈ ℝ^{n×d} (`some ⟨n, W⟩`, any n ∈ ℕ). -/
def FrameSlot (d : ℕ) := Option (Σ n : ℕ, Matrix (Fin n) (Fin d) ℝ)

/-- Validity of a frame slot: void, or WᵀW = cI_d with c > 0. -/
def FrameSlot.Valid : FrameSlot d → Prop
  | none => True
  | some ⟨_, W⟩ => ∃ c : ℝ, 0 < c ∧ W.transpose * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)

/-- A smooth term (f_i, w_i, β_i, σ_i, A_i): the attributes (β_i, σ_i, A_i) ∈ [0, ∞] ×
[−∞, ∞) × (void ∪ kernel attributes) are G12's `SDecl`. -/
structure SmoothTerm (d : ℕ) where
  f : Vec d → ℝ
  w : ℝ
  decl : SDecl d

/-- A non-smooth term (g_j, σ_j, π_j, W_j), σ_j ∈ [0, ∞). -/
structure NonsmoothTerm (d : ℕ) (Prog : Type*) where
  g : Vec d → EReal
  σ : ℝ≥0
  π : ProxAttr Prog
  W : FrameSlot d

/-- An energy specification on ℝᵈ (def:energy-spec), with S = Fin nS, N = Fin nN (finite,
disjoint as the two summands of S ⊕ N, possibly empty). -/
structure Spec (d : ℕ) (Prog : Type*) where
  nS : ℕ
  nN : ℕ
  S : Fin nS → SmoothTerm d
  N : Fin nN → NonsmoothTerm d Prog

namespace Spec

variable (𝔈 : Spec d Prog)

/-- The smooth part F = Σᵢ wᵢfᵢ. -/
noncomputable def F : Vec d → ℝ := sumF (fun i => (𝔈.S i).w) (fun i => (𝔈.S i).f)

/-- The energy E = Σᵢ wᵢfᵢ + Σⱼ gⱼ : ℝᵈ → (−∞, +∞]. -/
noncomputable def E : Vec d → EReal := fun x => ((𝔈.F x : ℝ) : EReal) + ∑ j, (𝔈.N j).g x

/-- σ̂ = Σᵢ wᵢσᵢ + Σⱼ σⱼ ∈ [−∞, ∞) (−∞ if some σᵢ = −∞). -/
noncomputable def sigmaHat : EReal := by
  classical
  exact if ∀ i, (𝔈.S i).decl.σ ≠ ⊥ then
    ((∑ i, (𝔈.S i).w * ((𝔈.S i).decl.σ).unbotD 0 + ∑ j, ((𝔈.N j).σ : ℝ) : ℝ) : EReal) else ⊥

/-- Σᵢ wᵢβᵢ ∈ [0, ∞] (∞ if some βᵢ = ∞); G12's `betaHatX`. -/
noncomputable def betaSum : ℝ≥0∞ := ∑ i, ENNReal.ofReal (𝔈.S i).w * (𝔈.S i).decl.β

/-- (O1): dom E ≠ ∅. -/
def O1 : Prop := (dom 𝔈.E).Nonempty

/-- Validity (def:energy-spec): every term is of its type and every attribute is true. -/
structure Valid (sem : ProgSem d Prog) : Prop where
  C1 : ∀ i, ContDiff ℝ 1 (𝔈.S i).f
  w_pos : ∀ i, 0 < (𝔈.S i).w
  smooth : ∀ i, (𝔈.S i).decl.Valid (𝔈.S i).f
  gamma0 : ∀ j, Gamma0 (𝔈.N j).g
  curv : ∀ j, CurvClaim (𝔈.N j).g (𝔈.N j).σ
  prox : ∀ j, (𝔈.N j).π.Valid sem (𝔈.N j).g
  frame : ∀ j, (𝔈.N j).W.Valid

variable {𝔈} {sem : ProgSem d Prog}

lemma E_ne_bot (hv : 𝔈.Valid sem) (x : Vec d) : 𝔈.E x ≠ ⊥ :=
  EReal.add_ne_bot_iff.2 ⟨EReal.coe_ne_bot _,
    ne_bot_sum _ (fun j => (𝔈.N j).g) (fun j => (hv.gamma0 j).ne_bot) x⟩

lemma sum_ne_top_iff {ι : Type*} (s : Finset ι) (g : ι → Vec d → EReal) (hb : ∀ j x, g j x ≠ ⊥)
    (x : Vec d) : ∑ j ∈ s, g j x ≠ ⊤ ↔ ∀ j ∈ s, g j x ≠ ⊤ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, EReal.add_ne_top_iff_ne_top₂ (hb j x) (ne_bot_sum s g hb x), ih,
      Finset.forall_mem_insert]

/-- dom E = ⋂ⱼ dom gⱼ (= ℝᵈ if N = ∅). -/
theorem dom_E (hv : 𝔈.Valid sem) : dom 𝔈.E = ⋂ j, dom (𝔈.N j).g := by
  ext x
  simp only [dom, mem_setOf_eq, mem_iInter, Spec.E]
  rw [EReal.add_ne_top_iff_ne_top₂ (EReal.coe_ne_bot _)
    (ne_bot_sum _ (fun j => (𝔈.N j).g) (fun j => (hv.gamma0 j).ne_bot) x),
    sum_ne_top_iff _ _ (fun j => (hv.gamma0 j).ne_bot)]
  simp

lemma lsc_sum {ι : Type*} (s : Finset ι) (g : ι → Vec d → EReal) (hb : ∀ j x, g j x ≠ ⊥)
    (hl : ∀ j, LowerSemicontinuous (g j)) : LowerSemicontinuous fun x => ∑ j ∈ s, g j x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using lowerSemicontinuous_const
  | insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (hl j).add' ih fun x => EReal.continuousAt_add (Or.inr (ne_bot_sum s g hb x))
      (Or.inl (hb j x))

/-- E is lower semicontinuous (fᵢ continuous, gⱼ lsc). -/
theorem E_lsc (hv : 𝔈.Valid sem) : LowerSemicontinuous 𝔈.E := by
  have hF : Continuous 𝔈.F := (contDiff_sumF _ hv.C1).continuous
  have h1 : LowerSemicontinuous fun x => ((𝔈.F x : ℝ) : EReal) :=
    (continuous_coe_real_ereal.comp hF).lowerSemicontinuous
  exact h1.add' (lsc_sum _ _ (fun j => (hv.gamma0 j).ne_bot) fun j => (hv.gamma0 j).lsc)
    fun x => EReal.continuousAt_add (Or.inl (EReal.coe_ne_top _)) (Or.inl (EReal.coe_ne_bot _))

/-- **prop:spec-moduli (a).** σ(E) ≥ σ̂ and β(F) ≤ Σᵢ wᵢβᵢ. -/
theorem spec_moduli_a (hv : 𝔈.Valid sem) :
    𝔈.sigmaHat ≤ sigmaMod 𝔈.E ∧ betaMod 𝔈.F ≤ 𝔈.betaSum := by
  have hR := rule_sum_a (fun i => (𝔈.S i).f) hv.C1 (fun i => (𝔈.S i).w) hv.w_pos
    (fun i => (𝔈.S i).decl) hv.smooth
  constructor
  · unfold sigmaHat
    split_ifs with hall
    · set sS := ∑ i, (𝔈.S i).w * ((𝔈.S i).decl.σ).unbotD 0
      have hF : ModC 𝔈.F sS := by
        apply hR.2.2.1 sS
        change sigmaHatX _ _ = _
        rw [sigmaHatX, extSum_of_fin (fun i _ => hall i)]
      have c1 : CurvIneq (toE 𝔈.F) sS :=
        (curvClaim_iff_curvIneq (fun x => EReal.coe_ne_bot _) sS).1
          ((curvClaim_toE_iff _ _).2 hF)
      have c2 := curvIneq_sum Finset.univ (fun j => (𝔈.N j).g) (fun j => ((𝔈.N j).σ : ℝ))
        (fun j => (hv.gamma0 j).ne_bot)
        (fun j _ => (curvClaim_iff_curvIneq (hv.gamma0 j).ne_bot _).1 (hv.curv j))
      have c3 := curvIneq_add (fun x => EReal.coe_ne_bot _)
        (ne_bot_sum _ (fun j => (𝔈.N j).g) (fun j => (hv.gamma0 j).ne_bot)) c1 c2
      have hE : CurvClaim 𝔈.E (sS + ∑ j, ((𝔈.N j).σ : ℝ)) :=
        (curvClaim_iff_curvIneq (E_ne_bot hv) _).2 c3
      exact le_sSup ⟨_, rfl, hE⟩
    · exact bot_le
  · by_cases htop : 𝔈.betaSum = ⊤
    · rw [htop]; exact le_top
    · have hL : LipGrad 𝔈.F (𝔈.betaSum).toReal := hR.2.1 htop
      have : LipGrad 𝔈.F ((𝔈.betaSum).toNNReal : ℝ) := by
        rwa [ENNReal.coe_toNNReal_eq_toReal]
      calc betaMod 𝔈.F ≤ ((𝔈.betaSum).toNNReal : ℝ≥0∞) :=
            iInf₂_le (f := fun (β : ℝ≥0) (_ : LipGrad 𝔈.F β) => (β : ℝ≥0∞)) _ this
        _ = 𝔈.betaSum := ENNReal.coe_toNNReal htop

/-- **prop:spec-moduli (c).** (i) If σ(E) ∈ ℝ then C(E, σ(E)). (ii) If moreover σ(E) > 0 and
(O1) holds, μ := σ(E) is the largest strong-convexity constant of E, μ ≥ σ̂, and argmin E is
one point. (iii) If (O1) holds and σ(E) = +∞, then dom E = argmin E = {x₀} for some x₀. -/
theorem spec_moduli_c (hv : 𝔈.Valid sem) :
    (∀ μ : ℝ, sigmaMod 𝔈.E = μ → CurvClaim 𝔈.E μ) ∧
    (∀ μ : ℝ, sigmaMod 𝔈.E = μ → 0 < μ → 𝔈.O1 →
      IsGreatest {σ : ℝ | 0 < σ ∧ CurvClaim 𝔈.E σ} μ ∧ 𝔈.sigmaHat ≤ μ ∧
      ∃ x₀, argmin 𝔈.E = {x₀}) ∧
    (𝔈.O1 → sigmaMod 𝔈.E = ⊤ → ∃ x₀, dom 𝔈.E = {x₀} ∧ argmin 𝔈.E = {x₀}) := by
  have hb := E_ne_bot hv
  refine ⟨fun μ hμ => curvClaim_sigmaMod hb hμ, fun μ hμ hpos hO1 => ⟨⟨⟨hpos,
    curvClaim_sigmaMod hb hμ⟩, fun σ ⟨_, hσ⟩ => ?_⟩, ?_, ?_⟩, fun hO1 htop => ?_⟩
  · have : (σ : EReal) ≤ sigmaMod 𝔈.E := le_sSup ⟨σ, rfl, hσ⟩
    rw [hμ] at this
    exact_mod_cast this
  · rw [← hμ]; exact (spec_moduli_a hv).1
  · exact exists_argmin_eq_singleton hb (E_lsc hv) hO1 hpos (curvClaim_sigmaMod hb hμ)
  · obtain ⟨x₀, hx₀⟩ := hO1
    have hsub := (sigmaMod_eq_top_iff hb).1 htop
    have hdom : dom 𝔈.E = {x₀} := Set.eq_singleton_iff_unique_mem.2
      ⟨hx₀, fun y hy => hsub hy hx₀⟩
    refine ⟨x₀, hdom, Set.eq_singleton_iff_unique_mem.2 ⟨fun y => ?_, fun y hy => ?_⟩⟩
    · by_cases hy : y ∈ dom 𝔈.E
      · rw [hsub hy hx₀]
      · have : 𝔈.E y = ⊤ := by simpa [dom] using hy
        rw [this]; exact le_top
    · have : 𝔈.E y ≠ ⊤ := ne_top_of_le_ne_top hx₀ (hy x₀)
      exact hsub this hx₀

end Spec

end Spec

/-! ## §3. prop:spec-moduli (b): the C² characterisations -/

section Hessian

variable {d : ℕ}

open OCF.G12 (opEv opLamMin eb ev_eq_inner inner_self_expand norm_sq_expand)

/-- The Hessian ∇²f(x), as the operator D(∇f)(x) on ℝᵈ. -/
noncomputable def hess (f : Vec d → ℝ) (x : Vec d) : Vec d →L[ℝ] Vec d :=
  fderiv ℝ (gradient f) x

/-- λ_min of a symmetric operator in [−∞, +∞]: the infimum of its eigenvalues (= +∞ for d = 0,
the empty spectrum; = G12's `opLamMin` for d ≥ 1, `lamMinE_eq_opLamMin`). -/
noncomputable def lamMinE (M : Vec d →L[ℝ] Vec d) : EReal := ⨅ j, ((opEv M j : ℝ) : EReal)

lemma lamMinE_eq_opLamMin (hd : 0 < d) (M : Vec d →L[ℝ] Vec d) :
    lamMinE M = (opLamMin M : EReal) := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_min (opEv M)
  have h1 : lamMinE M = (opEv M j0 : EReal) :=
    le_antisymm (iInf_le _ j0) (le_iInf fun j => EReal.coe_le_coe_iff.2 (hj0 j))
  have h2 : opLamMin M = opEv M j0 :=
    le_antisymm (ciInf_le (Set.finite_range _).bddBelow j0) (le_ciInf hj0)
  rw [h1, h2]

lemma gradient_eq_comp (f : Vec d → ℝ) :
    gradient f = (InnerProductSpace.toDual ℝ (Vec d)).symm ∘ fderiv ℝ f := rfl

lemma contDiff_gradient {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (gradient f) := by
  rw [gradient_eq_comp]
  exact (InnerProductSpace.toDual ℝ (Vec d)).symm.contDiff.comp (hf.fderiv_right (by norm_num))

lemma hasFDerivAt_gradient {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec d) :
    HasFDerivAt (gradient f) (hess f x) x :=
  (((contDiff_gradient hf).differentiable one_ne_zero) x).hasFDerivAt

lemma hess_inner {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x v w : Vec d) :
    inner ℝ (hess f x v) w = fderiv ℝ (fderiv ℝ f) x v w := by
  have hD : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero x).hasFDerivAt
  have hG := ((InnerProductSpace.toDual ℝ (Vec d)).symm.toContinuousLinearEquiv.hasFDerivAt
    (x := fderiv ℝ f x)).comp x hD
  rw [hess, gradient_eq_comp]
  erw [hG.fderiv]
  simp only [ContinuousLinearMap.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

/-- The Hessian of a C² function is symmetric (Schwarz). -/
lemma hess_symm {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x : Vec d) :
    (hess f x : Vec d →ₗ[ℝ] Vec d).IsSymmetric := by
  intro v w
  simp only [ContinuousLinearMap.coe_coe]
  rw [hess_inner hf, real_inner_comm, hess_inner hf]
  exact hf.contDiffAt.isSymmSndFDerivAt (by simp) v w

lemma hasDerivAt_inner_grad {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (x v w : Vec d) (t : ℝ) :
    HasDerivAt (fun t : ℝ => inner ℝ (gradient f (x + t • v)) w)
      (inner ℝ (hess f (x + t • v) v) w) t := by
  have hp : HasDerivAt (fun t : ℝ => x + t • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have hg := (hasFDerivAt_gradient hf (x + t • v)).comp_hasDerivAt t hp
  have := hg.inner ℝ (hasDerivAt_const t w)
  simpa using this

/-- C(f, σ) ⇔ ∇²f(x) ⪰ σI for all x (B&C Prop. 17.7 applied to f − (σ/2)‖·‖²). -/
theorem modC_iff_hess {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) (σ : ℝ) :
    ModC f σ ↔ ∀ x v, σ * ‖v‖ ^ 2 ≤ inner ℝ (hess f x v) v := by
  have hd : Differentiable ℝ f := hf.differentiable (by norm_num)
  rw [modC_iff_strongMono hd]
  constructor
  · intro hm x v
    set φ : ℝ → ℝ := fun t => inner ℝ (gradient f (x + t • v)) v - σ * ‖v‖ ^ 2 * t with hφ
    have mono : Monotone φ := by
      intro s t hst
      rcases hst.lt_or_eq with hlt | heq
      · have h1 := hm (x + t • v) (x + s • v)
        rw [show x + t • v - (x + s • v) = (t - s) • v by module, norm_smul,
          real_inner_smul_right, mul_pow, Real.norm_eq_abs, sq_abs, inner_sub_left] at h1
        have hts : 0 < t - s := sub_pos.2 hlt
        have h2 : (t - s) * (σ * (t - s) * ‖v‖ ^ 2) ≤ (t - s) *
            (inner ℝ (gradient f (x + t • v)) v - inner ℝ (gradient f (x + s • v)) v) := by
          calc (t - s) * (σ * (t - s) * ‖v‖ ^ 2) = σ * ((t - s) ^ 2 * ‖v‖ ^ 2) := by ring
            _ ≤ _ := h1
        have h3 := le_of_mul_le_mul_left h2 hts
        simp only [hφ]
        nlinarith
      · rw [heq]
    have hd0 : HasDerivAt φ (inner ℝ (hess f x v) v - σ * ‖v‖ ^ 2) 0 := by
      have := (hasDerivAt_inner_grad hf x v v 0).sub ((hasDerivAt_id (0 : ℝ)).const_mul (σ * ‖v‖ ^ 2))
      rw [mul_one, zero_smul, add_zero] at this
      exact this
    have := mono.deriv_nonneg (x := 0)
    rw [hd0.deriv] at this
    linarith
  · intro hH x y
    set u := x - y
    set ψ : ℝ → ℝ := fun t => inner ℝ (gradient f (y + t • u)) u - σ * ‖u‖ ^ 2 * t with hψ
    have hψd : ∀ t, HasDerivAt ψ (inner ℝ (hess f (y + t • u) u) u - σ * ‖u‖ ^ 2) t := fun t => by
      have := (hasDerivAt_inner_grad hf y u u t).sub ((hasDerivAt_id t).const_mul (σ * ‖u‖ ^ 2))
      rw [mul_one] at this
      exact this
    have mono := monotone_of_deriv_nonneg (fun t => (hψd t).differentiableAt)
      (fun t => by rw [(hψd t).deriv]; linarith [hH (y + t • u) u])
    have := mono (zero_le_one' ℝ)
    simp only [hψ, zero_smul, add_zero, one_smul, mul_zero, sub_zero, mul_one] at this
    have hx : y + u = x := by simp [u]
    rw [hx] at this
    rw [inner_sub_left]
    linarith

/-- For symmetric M: M ⪰ σI ⇔ σ ≤ λ_min(M) (Rayleigh, Boyd–Vandenberghe §A.5.2). -/
lemma psd_iff_le_lamMinE {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (σ : ℝ) : (∀ v, σ * ‖v‖ ^ 2 ≤ inner ℝ (M v) v) ↔ (σ : EReal) ≤ lamMinE M := by
  rw [lamMinE, le_iInf_iff]
  simp only [EReal.coe_le_coe_iff]
  constructor
  · intro hv j
    have := hv (eb h j)
    rw [← ev_eq_inner h j, (eb h).orthonormal.1 j] at this
    simpa using this
  · intro hj v
    rw [inner_self_expand h, norm_sq_expand h, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hj j) (sq_nonneg _)

/-- σ(f) = inf_x λ_min(∇²f(x)) for f ∈ C². -/
theorem sigmaMod_eq_iInf_lamMin {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    sigmaMod (toE f) = ⨅ x, lamMinE (hess f x) := by
  have : {s : EReal | ∃ σ : ℝ, s = σ ∧ CurvClaim (toE f) σ}
      = {s : EReal | ∃ σ : ℝ, s = σ ∧ (σ : EReal) ≤ ⨅ x, lamMinE (hess f x)} := by
    ext s
    simp only [mem_setOf_eq, curvClaim_toE_iff, modC_iff_hess hf, le_iInf_iff,
      ← psd_iff_le_lamMinE (hess_symm hf _)]
  rw [sigmaMod, this, sSup_coe_le]

/-- f is β-smooth ⇔ ‖∇²f(x)‖₂ ≤ β for all x (β ≥ 0, f ∈ C²). -/
theorem lipGrad_iff_hess {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) {β : ℝ} (hβ : 0 ≤ β) :
    LipGrad f β ↔ ∀ x, ‖hess f x‖ ≤ β := by
  constructor
  · intro hL x
    have hlip : LipschitzWith ⟨β, hβ⟩ (gradient f) :=
      LipschitzWith.of_dist_le_mul fun u v => by
        rw [dist_eq_norm, dist_eq_norm]; exact hL u v
    exact norm_fderiv_le_of_lipschitz ℝ hlip
  · intro hH u v
    have hdiff := (contDiff_gradient hf).differentiable one_ne_zero
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (f := gradient f) (s := univ)
      (fun x _ => hdiff x) (fun x _ => hH x) convex_univ (mem_univ v) (mem_univ u)

/-- β(f) = sup_x ‖∇²f(x)‖₂ for f ∈ C². -/
theorem betaMod_eq_iSup {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    betaMod f = ⨆ x, (‖hess f x‖₊ : ℝ≥0∞) := by
  apply le_antisymm
  · by_cases htop : (⨆ x, (‖hess f x‖₊ : ℝ≥0∞)) = ⊤
    · rw [htop]; exact le_top
    · set S := ⨆ x, (‖hess f x‖₊ : ℝ≥0∞)
      have hL : LipGrad f (S.toNNReal : ℝ) := by
        refine (lipGrad_iff_hess hf S.toNNReal.2).2 fun x => ?_
        have : (‖hess f x‖₊ : ℝ≥0∞) ≤ S.toNNReal := by
          rw [ENNReal.coe_toNNReal htop]; exact le_iSup (fun x => (‖hess f x‖₊ : ℝ≥0∞)) x
        exact_mod_cast ENNReal.coe_le_coe.1 this
      calc betaMod f ≤ (S.toNNReal : ℝ≥0∞) :=
            iInf₂_le (f := fun (β : ℝ≥0) (_ : LipGrad f β) => (β : ℝ≥0∞)) _ hL
        _ = S := ENNReal.coe_toNNReal htop
  · refine le_iInf₂ fun β hβ => iSup_le fun x => ?_
    have := (lipGrad_iff_hess hf β.2).1 hβ x
    exact ENNReal.coe_le_coe.2 (by exact_mod_cast this)

/-- **prop:spec-moduli (b).** For f ∈ C²(ℝᵈ): C(f, σ) ⇔ ∇²f(x) ⪰ σI for all x; hence
σ(f) = inf_x λ_min(∇²f(x)) and β(f) = sup_x ‖∇²f(x)‖₂. (∇²f(x) is symmetric: `hess_symm`.) -/
theorem spec_moduli_b {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    (∀ σ : ℝ, CurvClaim (toE f) σ ↔ ∀ x v, σ * ‖v‖ ^ 2 ≤ inner ℝ (hess f x v) v) ∧
    sigmaMod (toE f) = ⨅ x, lamMinE (hess f x) ∧
    betaMod f = ⨆ x, (‖hess f x‖₊ : ℝ≥0∞) :=
  ⟨fun σ => (curvClaim_toE_iff f σ).trans (modC_iff_hess hf σ), sigmaMod_eq_iInf_lamMin hf,
    betaMod_eq_iSup hf⟩

/-- prop:spec-moduli (b), d ≥ 1, with G12's real λ_min: σ(f) = inf_x λ_min(∇²f(x)). -/
theorem spec_moduli_b_opLamMin (hd : 0 < d) {f : Vec d → ℝ} (hf : ContDiff ℝ 2 f) :
    sigmaMod (toE f) = ⨅ x, ((opLamMin (hess f x) : ℝ) : EReal) := by
  rw [sigmaMod_eq_iInf_lamMin hf]
  simp only [lamMinE_eq_opLamMin hd]

/-- The sentence after prop:spec-moduli: if N = ∅ and F ∈ C², then E = F and
σ(E) = inf_x γ(x), γ(x) = λ_min(∇²E(x)) (so μ = inf_x γ(x) when 0 < σ(E) < ∞). -/
theorem sigmaMod_E_of_N_empty {Prog : Type*} (𝔈 : Spec d Prog) (hN : 𝔈.nN = 0)
    (hF : ContDiff ℝ 2 𝔈.F) : 𝔈.E = toE 𝔈.F ∧ sigmaMod 𝔈.E = ⨅ x, lamMinE (hess 𝔈.F x) := by
  have hE : 𝔈.E = toE 𝔈.F := by
    funext x
    obtain ⟨nS, nN, S, N⟩ := 𝔈
    simp only at hN
    subst hN
    simp [Spec.E, toE]
  exact ⟨hE, by rw [hE]; exact sigmaMod_eq_iInf_lamMin hF⟩

end Hessian

/-! ## §4. rem:sigma-infinite consequences and rem:spec-sharpness -/

section Sharpness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- σ(h) = s as soon as C(h, s) holds and every valid σ is ≤ s. -/
lemma sigmaMod_eq_of {h : E → EReal} {s : ℝ} (hs : CurvClaim h s)
    (hmax : ∀ σ, CurvClaim h σ → σ ≤ s) : sigmaMod h = s :=
  le_antisymm (sSup_le fun _ ⟨σ, hσ, hc⟩ => hσ ▸ EReal.coe_le_coe_iff.2 (hmax σ hc))
    (le_sSup ⟨s, rfl, hs⟩)

/-- rem:sigma-infinite: σ(f) < ∞ for real-valued f on a space with two points (d ≥ 1). -/
theorem sigmaMod_toE_lt_top (f : E → ℝ) (hE : ∃ u : E, u ≠ 0) : sigmaMod (toE f) < ⊤ := by
  obtain ⟨u, hu⟩ := hE
  rw [lt_top_iff_ne_top, Ne, sigmaMod_eq_top_iff (h := toE f) (fun x => EReal.coe_ne_bot _)]
  intro hsub
  exact hu (hsub (show u ∈ dom (toE f) from EReal.coe_ne_top _)
    (show (0 : E) ∈ dom (toE f) from EReal.coe_ne_top _))

open Classical in
/-- rem:sigma-infinite: σ(ι_{0}) = +∞. -/
theorem sigmaMod_indicator_zero :
    sigmaMod (fun x : E => if x = 0 then (0 : EReal) else ⊤) = ⊤ := by
  rw [sigmaMod_eq_top_iff (fun x => by split_ifs <;> simp)]
  intro x hx y hy
  simp only [dom, mem_setOf_eq] at hx hy
  split_ifs at hx hy with h1 h2 <;> simp_all

/-- β(c/2‖·‖²) = c for c ≥ 0 (d ≥ 1). -/
theorem betaMod_half_sq (hE : ∃ u : E, u ≠ 0) {c : ℝ} (hc : 0 ≤ c) :
    betaMod (fun x : E => c / 2 * ‖x‖ ^ 2) = ENNReal.ofReal c := by
  have hfun : (fun x : E => c / 2 * ‖x‖ ^ 2) = fun x => (fun _ : E => (0 : ℝ)) x - (-c) / 2 * ‖x‖ ^ 2 := by
    funext x; ring
  have hgrad : ∀ x, gradient (fun x : E => c / 2 * ‖x‖ ^ 2) x = c • x := by
    intro x
    rw [hfun, OCF.G3.gradient_sub_sq (differentiable_const _) (-c) x]
    have : gradient (fun _ : E => (0 : ℝ)) x = 0 := gradient_const x 0
    rw [this, zero_sub, neg_smul, neg_neg]
  have hiff : ∀ β : ℝ, LipGrad (fun x : E => c / 2 * ‖x‖ ^ 2) β ↔ c ≤ β := by
    intro β
    constructor
    · intro hL
      obtain ⟨u, hu⟩ := hE
      have := hL u 0
      rw [hgrad, hgrad, smul_zero, sub_zero, sub_zero, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg hc] at this
      exact le_of_mul_le_mul_right this (norm_pos_iff.2 hu)
    · intro hle u v
      rw [hgrad, hgrad, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      exact mul_le_mul_of_nonneg_right hle (norm_nonneg _)
  apply le_antisymm
  · have : LipGrad (fun x : E => c / 2 * ‖x‖ ^ 2) ((Real.toNNReal c : ℝ≥0) : ℝ) := by
      rw [Real.coe_toNNReal _ hc]; exact (hiff c).2 le_rfl
    exact iInf₂_le (f := fun (β : ℝ≥0) (_ : LipGrad (fun x : E => c / 2 * ‖x‖ ^ 2) β) =>
      (β : ℝ≥0∞)) _ this
  · refine le_iInf₂ fun β hβ => ?_
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_le_ofReal ((hiff β).1 hβ)

end Sharpness

section SharpnessExamples

open OCF.G12 (sumF)

/-- rem:spec-sharpness, last sentence: for fᵢ = (βᵢ/2)‖·‖² on ℝᵈ (d ≥ 1), β(fᵢ) = βᵢ and
β(Σ wᵢfᵢ) = Σ wᵢβ(fᵢ): the bound β(F) ≤ Σ wᵢβᵢ of (a) is attained. -/
theorem sharp_beta {d n : ℕ} (hd : 0 < d) (w β : Fin n → ℝ) (hw : ∀ i, 0 < w i)
    (hβ : ∀ i, 0 ≤ β i) :
    (∀ i, betaMod (fun x : Vec d => β i / 2 * ‖x‖ ^ 2) = ENNReal.ofReal (β i)) ∧
    betaMod (sumF w fun i (x : Vec d) => β i / 2 * ‖x‖ ^ 2)
      = ∑ i, ENNReal.ofReal (w i) * betaMod (fun x : Vec d => β i / 2 * ‖x‖ ^ 2) := by
  have hE : ∃ u : Vec d, u ≠ 0 := ⟨EuclideanSpace.single ⟨0, hd⟩ 1, by
    intro h
    have := congrArg (fun v : Vec d => v ⟨0, hd⟩) h
    simp at this⟩
  refine ⟨fun i => betaMod_half_sq hE (hβ i), ?_⟩
  have hsum : (sumF w fun i (x : Vec d) => β i / 2 * ‖x‖ ^ 2)
      = fun x : Vec d => (∑ i, w i * β i) / 2 * ‖x‖ ^ 2 := by
    funext x
    simp only [sumF, Finset.sum_div, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hnn : 0 ≤ ∑ i, w i * β i := Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (hβ i)
  rw [hsum, betaMod_half_sq hE hnn, ENNReal.ofReal_sum_of_nonneg
    (fun i _ => mul_nonneg (hw i).le (hβ i))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [betaMod_half_sq hE (hβ i), ENNReal.ofReal_mul (hw i).le]

/-- The midpoint form of C(φ, σ) for φ : ℝ → ℝ. -/
lemma modC_mid {φ : ℝ → ℝ} {σ : ℝ} (h : ModC φ σ) (x y : ℝ) :
    φ ((x + y) / 2) - σ / 2 * ((x + y) / 2) ^ 2
      ≤ (φ x - σ / 2 * x ^ 2) / 2 + (φ y - σ / 2 * y ^ 2) / 2 := by
  have := h.2 (mem_univ x) (mem_univ y) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at this
  have e : 1 / 2 * x + 1 / 2 * y = (x + y) / 2 := by ring
  rw [e] at this
  linarith

/-- rem:spec-sharpness, first example: on ℝ², σ(½x₁²) = σ(½x₂²) = 0 and σ(½x₁² + ½x₂²) = 1. -/
theorem sharp_sigma_quadratics :
    sigmaMod (toE fun x : Vec 2 => 1 / 2 * x 0 ^ 2) = 0 ∧
    sigmaMod (toE fun x : Vec 2 => 1 / 2 * x 1 ^ 2) = 0 ∧
    sigmaMod (toE fun x : Vec 2 => 1 / 2 * x 0 ^ 2 + 1 / 2 * x 1 ^ 2) = 1 := by
  have hn : ∀ x : Vec 2, ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := fun x => by
    rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  -- convexity of ½ x_k²
  have hconv : ∀ k : Fin 2, ModC (fun x : Vec 2 => 1 / 2 * x k ^ 2) 0 := by
    intro k
    refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    simp only [smul_eq_mul, PiLp.add_apply, PiLp.smul_apply, zero_div, zero_mul, sub_zero]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [sq_nonneg (x k - y k), mul_nonneg ha hb]
  -- failure for σ > 0 along the other axis
  have hfail : ∀ k l : Fin 2, k ≠ l → ∀ σ : ℝ, ModC (fun x : Vec 2 => 1 / 2 * x k ^ 2) σ →
      σ ≤ 0 := by
    intro k l hkl σ hσ
    by_contra hpos
    push Not at hpos
    set e : Vec 2 := EuclideanSpace.single l 1
    have := hσ.2 (mem_univ e) (mem_univ (-e)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    have hek : e k = 0 := by simp [e, hkl]
    have hne : ‖e‖ = 1 := by simp [e]
    simp only [smul_eq_mul, smul_neg, ← sub_eq_add_neg, sub_self, PiLp.neg_apply, hek,
      norm_neg, hne, norm_zero] at this
    norm_num at this
    linarith
  refine ⟨?_, ?_, ?_⟩
  · refine sigmaMod_eq_of ((curvClaim_toE_iff _ _).2 (hconv 0)) fun σ hσ => ?_
    exact hfail 0 1 (by decide) σ ((curvClaim_toE_iff _ _).1 hσ)
  · refine sigmaMod_eq_of ((curvClaim_toE_iff _ _).2 (hconv 1)) fun σ hσ => ?_
    exact hfail 1 0 (by decide) σ ((curvClaim_toE_iff _ _).1 hσ)
  · have hfun : ∀ σ : ℝ, (fun x : Vec 2 => 1 / 2 * x 0 ^ 2 + 1 / 2 * x 1 ^ 2 - σ / 2 * ‖x‖ ^ 2)
        = fun x => (1 - σ) / 2 * ‖x‖ ^ 2 := fun σ => by
      funext x; rw [hn]; ring
    refine sigmaMod_eq_of ((curvClaim_toE_iff _ _).2 ?_) fun σ hσ => ?_
    · show ConvexOn ℝ univ _
      rw [hfun]; simpa using convexOn_const (0 : ℝ) convex_univ
    · rw [curvClaim_toE_iff] at hσ
      have hσ' : ConvexOn ℝ univ (fun x : Vec 2 => (1 - σ) / 2 * ‖x‖ ^ 2) := by
        have : ConvexOn ℝ univ _ := hσ; rwa [hfun] at this
      by_contra hgt
      push Not at hgt
      set e : Vec 2 := EuclideanSpace.single 0 1
      have := hσ'.2 (mem_univ e) (mem_univ (-e)) (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
      have hne : ‖e‖ = 1 := by simp [e]
      simp only [smul_eq_mul, smul_neg, ← sub_eq_add_neg, sub_self, norm_neg, hne,
        norm_zero] at this
      norm_num at this
      linarith

/-- rem:spec-sharpness, second example (no kernel): on ℝ, σ(x⁴) = σ((x − 1)⁴) = 0 and
σ(x⁴ + (x − 1)⁴) = 6. -/
theorem sharp_sigma_quartics :
    sigmaMod (toE fun x : ℝ => x ^ 4) = 0 ∧
    sigmaMod (toE fun x : ℝ => (x - 1) ^ 4) = 0 ∧
    sigmaMod (toE fun x : ℝ => x ^ 4 + (x - 1) ^ 4) = ((6 : ℝ) : EReal) := by
  have hpow : ConvexOn ℝ univ fun x : ℝ => x ^ 4 := Even.convexOn_pow ⟨2, rfl⟩
  -- the small parameter t = min 1 (c/8) for c > 0
  have small : ∀ c : ℝ, 0 < c → ∃ t : ℝ, 0 < t ∧ t ≤ 1 ∧ t ≤ c / 8 :=
    fun c hc => ⟨min 1 (c / 8), lt_min one_pos (by linarith), min_le_left _ _, min_le_right _ _⟩
  refine ⟨?_, ?_, ?_⟩
  · refine sigmaMod_eq_of ((curvClaim_toE_iff _ _).2 ?_) fun σ hσ => ?_
    · show ConvexOn ℝ univ _
      simpa using hpow
    · rw [curvClaim_toE_iff] at hσ
      by_contra hpos; push Not at hpos
      obtain ⟨t, ht0, ht1, htc⟩ := small σ hpos
      have := modC_mid hσ t (-t)
      norm_num at this
      nlinarith [mul_pos ht0 ht0, mul_le_mul_of_nonneg_left ht1 ht0.le]
  · refine sigmaMod_eq_of ((curvClaim_toE_iff _ _).2 ?_) fun σ hσ => ?_
    · show ConvexOn ℝ univ _
      refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      have hp := hpow.2 (mem_univ (x - 1)) (mem_univ (y - 1)) ha hb hab
      simp only [smul_eq_mul, zero_div, zero_mul, sub_zero] at hp ⊢
      have e : a * x + b * y - 1 = a * (x - 1) + b * (y - 1) := by
        have hb' : b = 1 - a := by linarith
        subst hb'; ring
      rw [e]; exact hp
    · rw [curvClaim_toE_iff] at hσ
      by_contra hpos; push Not at hpos
      obtain ⟨t, ht0, ht1, htc⟩ := small σ hpos
      have := modC_mid hσ (1 + t) (1 - t)
      have e : (1 + t + (1 - t)) / 2 = 1 := by ring
      rw [e] at this
      nlinarith [mul_pos ht0 ht0, mul_le_mul_of_nonneg_left ht1 ht0.le]
  · refine sigmaMod_eq_of ((curvClaim_toE_iff _ _).2 ?_) fun σ hσ => ?_
    · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
      have hp := hpow.2 (mem_univ (x - 1 / 2)) (mem_univ (y - 1 / 2)) ha hb hab
      simp only [smul_eq_mul, Real.norm_eq_abs, sq_abs] at hp ⊢
      have hb' : b = 1 - a := by linarith
      subst hb'
      have key : a * ((x ^ 4 + (x - 1) ^ 4) - 6 / 2 * x ^ 2)
          + (1 - a) * ((y ^ 4 + (y - 1) ^ 4) - 6 / 2 * y ^ 2)
          - (((a * x + (1 - a) * y) ^ 4 + (a * x + (1 - a) * y - 1) ^ 4)
            - 6 / 2 * (a * x + (1 - a) * y) ^ 2)
          = 2 * (a * (x - 1 / 2) ^ 4 + (1 - a) * (y - 1 / 2) ^ 4
            - (a * (x - 1 / 2) + (1 - a) * (y - 1 / 2)) ^ 4) := by ring
      nlinarith [key, hp]
    · rw [curvClaim_toE_iff] at hσ
      by_contra hgt; push Not at hgt
      obtain ⟨t, ht0, ht1, htc⟩ := small (σ - 6) (by linarith)
      have := modC_mid hσ (1 / 2 + t) (1 / 2 - t)
      have e : (1 / 2 + t + (1 / 2 - t)) / 2 = 1 / 2 := by ring
      rw [e] at this
      have key : ((1 / 2 + t) ^ 4 + (1 / 2 + t - 1) ^ 4 - σ / 2 * (1 / 2 + t) ^ 2) / 2
          + ((1 / 2 - t) ^ 4 + (1 / 2 - t - 1) ^ 4 - σ / 2 * (1 / 2 - t) ^ 2) / 2
          - ((1 / 2) ^ 4 + (1 / 2 - 1) ^ 4 - σ / 2 * (1 / 2) ^ 2)
          = t ^ 2 * (3 - σ / 2 + 2 * t ^ 2) := by ring
      have hneg : 3 - σ / 2 + 2 * t ^ 2 < 0 := by nlinarith
      nlinarith [mul_pos ht0 ht0]

end SharpnessExamples

end OCF.DEF1

#print axioms OCF.DEF1.Spec.spec_moduli_a
#print axioms OCF.DEF1.spec_moduli_b
#print axioms OCF.DEF1.spec_moduli_b_opLamMin
#print axioms OCF.DEF1.Spec.spec_moduli_c
#print axioms OCF.DEF1.sigmaMod_E_of_N_empty
#print axioms OCF.DEF1.betaMod_attained
#print axioms OCF.DEF1.sigmaMod_eq_top_iff
#print axioms OCF.DEF1.sigmaMod_toE_lt_top
#print axioms OCF.DEF1.sigmaMod_indicator_zero
#print axioms OCF.DEF1.Spec.dom_E
#print axioms OCF.DEF1.sharp_sigma_quadratics
#print axioms OCF.DEF1.sharp_sigma_quartics
#print axioms OCF.DEF1.sharp_beta

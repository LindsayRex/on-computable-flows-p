/-
R0 (limits of stacking certificates) — the Lean targets assigned at the stage 3.5 gate of the adjudicated
dossier: Proposition r0-transfer-instance (exact rational counterexample for the Euclidean position-block
lift of the heavy-ball word), the algebra of Proposition r0-order (exact floors of the two Langevin letter
orders on the 1-D quadratic), and the d = 1 case of Proposition r0-lyap-typing (E ∈ C³ with a globally
Lipschitz gradient of Λ_W forces E‴ = 0, hence a quadratic).

Source of truth: project_plan/doing/proof_audits/R0_stacking/01_derivation.md (adjudicated stage 3,
2026-10-29), section 3 (r0-lyap-typing, r0-transfer-instance), section 4 (r0-order), section 6 (Lean tiers);
rulings in 03_adjudication.md. Dossier sha16 (first 16 hex of sha256sum of 01_derivation.md) when
formalised: c3ba699c9e9e404c (re-checked 2026-10-29 after the adjudicator's second pass; the previous
sha16 was 77475a5b80ea9c67; the three statements below were re-read against the edited text and match).

DEFINITIONAL MAP (dossier symbol — Lean name):
* The heavy-ball word W_hb = Φ^SV_1 ∘ D^{1−β,M'}_Kin of thm:conservative-word / prop:hb-word — C1's
  `OCF.C1.hbWord E α β GK` (NOT restated; `GK` is the phase-space gradient of Kin, hypothesis `hGK : IsGradPS …`,
  the definition of GK, as in C1/E0). Tuning β, s, q, c_β — C1's `hbBeta`, `hbS`, `hbQ`, `cBeta`.
  Λ_W(x, v) = E(x) − E* + c_β‖v + ½∇E(x)‖² — C1's `LamW` (instance: `LamI`, `E* = E(0)`).
* ℝ² (d = 2) — `V2 := EuclideanSpace ℝ (Fin 2)`; the point (a, b) — `pt a b`.
* The instance E(x) = (x₁² + 4x₂²)/2, pair (m, L) = (1, 4) — `EInst`, `grad_EInst` (∇E = (x₁, 4x₂)),
  `EInst_dal1a` (Dalalyan (1a) with m = 1), `EInst_lip` (4-Lipschitz gradient), `EInst_min` (x* = 0).
  α = 7/32 — `aI`; β = hbBeta 1 4 α = 5/16 — `bI`, `bI_val`; s = 1/3 — `sI_val`; q = 25/32 — `qI_val`;
  c_β = 2/63 — `cI_val`.
* g = indicator of C = span{(1,1)} — E0's convention for an indicator: the pair (S, g) = (C, 0), `Cline`
  (= `Submodule.span ℝ {pt 1 1}`), `mem_Cline`. The projective letter prox_{ā g} is any map `P` with
  `∀ x, IsProx (‖·‖²) ā Cline 0 x (P x)` (E0's `IsProx`, Q w = ‖w‖² the identity metric); it is
  unique (`prox_eq_projC`) and exists (`projC_isProx`, `projC x = ((x₁+x₂)/2)(1,1)`), so the hypothesis
  is neither vacuous nor weaker than "the projection". The lifted letter Pb(x, v) = (P x, v) — `Pb`.
* z_b = (x, v) = ((−1/2, 0), (−3/4, −1)) — `zb`.
* r0-order: T, μ, h, η = hμ, F(x) = μx²/2 — `T μ h : ℝ`, `h * μ`; the variance maps of N_h ∘ D_h and
  D_h ∘ N_h — `varND`, `varDN` (x ↦ (1−η)x + √(2Th) ξ  has variance map v ↦ (1−η)²v + 2Th, and
  x ↦ (1−η)(x + √(2Th) ξ) has v ↦ (1−η)²(v + 2Th)); the stationary variances
  (T/μ)/(1−η/2) and (T/μ)(1−η)²/(1−η/2) of [LANDED: ex:ou-words] — `statND`, `statDN`;
  u = (1 − η/2)^(−1/2) — `uF`; the Gibbs law has variance T/μ. Laws are ABSTRACT: a type `Law`, a map
  `gauss : ℝ → Law` (centred Gaussian of standard deviation σ ≥ 0) and `W2 : Law → Law → ℝ`; the
  stationary laws are taken to be `gauss (√statND)` and `gauss (√statDN)`, the target `gauss (√(T/μ))`.
  Floors f₁ = W2(π_ND, π_T), f₂ = W2(π_DN, π_T) — the `W2 (gauss …) (gauss …)` terms of `r0_order`.
* r0-lyap-typing, d = 1: ∇E = E' (`deriv E`), E ∈ C³ — `ContDiff ℝ 3 E`; Λ_W — `Lam1 E Es c` with
  c = c_β (generalised to any c > 0, see below); the gradient of Λ_W on ℝ² — `gradLam1` (the pair of
  partial derivatives); "gradient Lipschitz on ℝ × ℝ" — `LipEuclid` (∃ K ≥ 0 with
  ‖G z − G z'‖² ≤ K²‖z − z'‖², Euclidean norm of ℝ², written with squares); "Hessian of E is constant,
  E a quadratic polynomial" — `∀ x, deriv (deriv (deriv E)) x = 0`, resp. `∃ a b k, ∀ x, E x = a + b x + k x²`.

NAMED HYPOTHESES (classical inputs, stated as the source states them; never global axioms):
* `hW2 : W2Gaussian gauss W2` — [CLASSICAL] Bullo, Contraction Theory for Dynamical Systems v1.3,
  Ex. 6.11(iii),(iv), p. 229 (VERIFIED 2026-10-29, WANTED.md R0 record): W2(N(0,σ₁²), N(0,σ₂²)) = |σ₁ − σ₂|
  for σ₁, σ₂ ≥ 0 (σ = 0 is the Dirac case, via the quantile form (6.42)).
* `hGK : IsGradPS (½ s ‖v‖²) GK` — the definition of GK (not classical), as in C1/E0.
* Nothing else: the landed theorem's hypotheses at the instance are PROVED (`EInst_dal1a`, `EInst_lip`,
  `EInst_min`), and the landed conclusion at the instance is re-derived by C1's `lamW_decay`
  (`instance_landed_decay`).

COVERAGE (dossier item — Lean name):
* r0-transfer-instance — `r0_transfer_instance`: Λ_W(z_b) = 95/504, Λ_W(W z_b) = 75979/516096 ≤ q Λ_W(z_b),
  Λ_W(Pb W z_b) = 13781/57344, ratio 124029/97280, q Λ_W(z_b) < Λ_W(Pb W z_b), and the negation of the
  all-states inequality ∀ z, Λ_W(Pb(W z)) ≤ q Λ_W(z); for EVERY prox map P of the indicator of C (every
  weight ā > 0). Parameters and the starting point as in the dossier. NOT claimed (as in the dossier):
  that z_b is a landed start, anything about runs, metric lifts (SN-1, SN-2).
* r0-order — `r0_order` (+ `floors_key`, `varND_fixed`, `varDN_fixed`, `statDN` relation): (i) the stationary
  variances are the unique fixed points of the variance maps; (ii) Var π_DN = (1−η)² Var π_ND and the two
  differ for every η ∈ (0, 2); (iii) f₁ = √(T/μ)(u − 1), f₂ = √(T/μ)|1 − |1−η|u|; (iv) f₁ < f₂ for
  η < √5 − 1, f₁ = f₂ at η = √5 − 1 with the variances still different, f₁ > f₂ for η > √5 − 1 (hence f₁ = f₂
  iff η = √5 − 1); (v) at η = 3/2 the floor f₂ = 0. The cross-over η = √5 − 1 lies in (1, 3/2).
  NOT formalised (prose/classical): that the stationary law of the Gaussian AR(1) maps is the Gaussian with the
  fixed-point variance (the laws `π_ND`, `π_DN` are DEFINED here by their variances); part (i) of the dossier's
  proposition (equal letters, equal product bound |1−η|); the scope notes SN-3, SN-4 (numbers of the repository);
  the rewritten Consequence paragraph's positive counterpart (floor ≤ δ(π_T)/(1 − λ), the F-4 triangle-inequality
  bound and its tightness ratios, witness J6), which is a cited-trivial bound, not an equality of the proposition.
* r0-lyap-typing, d = 1 — `r0_lyap_typing_d1`: for E ∈ C³(ℝ) and c > 0 the gradient of Λ_W is Lipschitz iff
  E‴ ≡ 0 iff E is a quadratic polynomial (`lip_imp_third_zero`, `third_zero_imp_quad`, `quad_imp_lip`);
  `r0_lyap_typing_d1_cbeta` states it at c = c_β of a tuning with the computed pair (m, L) of the dossier.
  GENERALISATION (flagged, not a weakening): the proof does not use the pair (m, L) or the value of c beyond
  c > 0, so the main theorem is stated for every c > 0 and every E*; the wrapper takes the dossier's
  hypotheses (Dal1a, LipGrad, 0 < α, αL < 1) as unused hypotheses. Part (a) is d = 1 only; the dossier's
  general-d statement is NOT formalised. NOT formalised: part (b) (Hessian blocks and eigenvalue bounds
  σ~, β~) and consequences (i) to (iii).
* NOT formalised: r0-fixed-point (no Lean target), r0-jsr, r0-pairnorm, SN-1, SN-2 (executable witnesses),
  F-1 to F-4 (classical), the interface specification (requirements).

Status tier: FORMALISED (statement + proof, no sorry) for r0-transfer-instance, for the algebra of r0-order
relative to the named Gaussian W2 hypothesis, and for the d = 1 case of r0-lyap-typing (a). STATUS: COMPLETE.
-/
import Mathlib
import OcfVerification.C1ConservativeWord

open OCF.C1 OCF.E0

namespace OCF.R0

/-! ## Part A: Proposition r0-transfer-instance -/

abbrev V2 := EuclideanSpace ℝ (Fin 2)

noncomputable def EInst (x : V2) : ℝ := (x 0 ^ 2 + 4 * x 1 ^ 2) / 2

noncomputable def pt (a b : ℝ) : V2 := !₂[a, b]
@[simp] lemma pt_zero (a b : ℝ) : (pt a b) 0 = a := rfl
@[simp] lemma pt_one (a b : ℝ) : (pt a b) 1 = b := rfl

lemma grad_EInst (x : V2) : gradient EInst x = pt (x 0) (4 * x 1) := by
  have h0 : HasFDerivAt (fun x : V2 => x 0) (EuclideanSpace.proj (0 : Fin 2) : V2 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (0 : Fin 2) : V2 →L[ℝ] ℝ).hasFDerivAt
  have h1 : HasFDerivAt (fun x : V2 => x 1) (EuclideanSpace.proj (1 : Fin 2) : V2 →L[ℝ] ℝ) x :=
    (EuclideanSpace.proj (1 : Fin 2) : V2 →L[ℝ] ℝ).hasFDerivAt
  have h := (((h0.pow 2).add ((h1.pow 2).const_mul 4))).const_mul (1/2 : ℝ)
  have : HasGradientAt EInst (pt (x 0) (4 * x 1)) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have e : EInst = fun x : V2 => (1/2 : ℝ) * (x 0 ^ 2 + 4 * x 1 ^ 2) := by
      funext y; simp [EInst]; ring
    rw [e]
    refine h.congr_fderiv ?_
    ext w
    simp [EuclideanSpace.inner_eq_star_dotProduct, pt, Matrix.vecHead, Matrix.vecTail]
    ring
  exact this.gradient

lemma normsq2 (x : V2) : ‖x‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]; simp [Fin.sum_univ_two]

/-- instance parameters -/
noncomputable def aI : ℝ := 7 / 32
noncomputable def bI : ℝ := hbBeta 1 4 aI

lemma bI_val : bI = 5 / 16 := by
  unfold bI hbBeta aI
  rw [show (1 - (7:ℝ) / 32 * 1) * (1 - 7 / 32 * 4) = (5 / 16) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

lemma sI_val : hbS aI bI = 1 / 3 := by
  rw [hbS, bI_val, aI]; norm_num

lemma sI_val' : hbS aI (5 / 16) = 1 / 3 := by
  rw [hbS, aI]; norm_num

lemma cI_val : cBeta 4 aI bI = 2 / 63 := by
  rw [cBeta, bI_val, aI]; norm_num

lemma qI_val : hbQ 1 aI = 25 / 32 := by
  rw [hbQ, aI]; norm_num

noncomputable def zb : V2 × V2 := (pt (-1/2) 0, pt (-3/4) (-1))

lemma word_zb {GK : V2 × V2 → V2 × V2}
    (hGK : IsGradPS (fun z : V2 × V2 => (1 / 2 : ℝ) * hbS aI bI * ‖z.2‖ ^ 2) GK) :
    hbWord EInst aI bI GK zb = (pt (-95/192) (-5/48), pt (101/384) (-5/48)) := by
  have eGK : GK = fun z => (0, hbS aI bI • z.2) := hGK.unique (isGradPS_kinS _)
  subst eGK
  rw [hbWord]
  unfold sv dstep zb
  simp only [MprInv, MpHBinv, bI_val, sI_val', bdiag]
  ext i <;> fin_cases i <;> simp [grad_EInst] <;> norm_num

lemma lamW_pt (c a b u w : ℝ) :
    LamW EInst (EInst 0) c (pt a b, pt u w) = (a ^ 2 + 4 * b ^ 2) / 2 + c * ((u + a / 2) ^ 2 + (w + 2 * b) ^ 2) := by
  unfold LamW
  simp only [grad_EInst]
  have h0 : EInst 0 = 0 := by simp [EInst]
  rw [h0, normsq2]
  simp only [PiLp.add_apply, PiLp.smul_apply, pt_zero, pt_one, smul_eq_mul, EInst]
  ring

/-- the line `C = span{(1,1)}` -/
noncomputable def Cline : Set V2 := (Submodule.span ℝ {pt 1 1} : Submodule ℝ V2)

lemma mem_Cline {y : V2} : y ∈ Cline ↔ y 0 = y 1 := by
  unfold Cline
  rw [SetLike.mem_coe, Submodule.mem_span_singleton]
  constructor
  · rintro ⟨t, rfl⟩; simp [pt]
  · intro h
    refine ⟨y 0, ?_⟩
    ext i; fin_cases i <;> simp [pt, h]

/-- the Euclidean projection onto `C`, explicitly -/
noncomputable def projC (x : V2) : V2 := pt ((x 0 + x 1) / 2) ((x 0 + x 1) / 2)

lemma projC_mem (x : V2) : projC x ∈ Cline := mem_Cline.2 (by simp [projC])

/-- any prox of the indicator of `C` (Euclidean metric, any weight) is the explicit projection -/
lemma prox_eq_projC {abar : ℝ} {x p : V2}
    (hp : IsProx (fun w : V2 => ‖w‖ ^ 2) abar Cline (fun _ => (0 : ℝ)) x p) : p = projC x := by
  obtain ⟨hpC, hmin⟩ := hp
  have h := hmin (projC x) (projC_mem x)
  have hp01 := mem_Cline.1 hpC
  simp only [mul_zero, zero_add, normsq2] at h
  simp only [projC, pt_zero, pt_one, PiLp.sub_apply] at h
  rw [← hp01] at h
  have h2 : (p 0 - (x 0 + x 1) / 2) ^ 2 ≤ 0 := by nlinarith
  have h3 : p 0 - (x 0 + x 1) / 2 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm h2 (sq_nonneg _))
  have : p 0 = (x 0 + x 1) / 2 := by linarith
  ext i; fin_cases i
  · simpa [projC] using this
  · simp [projC]; rw [← hp01]; exact this

lemma projC_isProx (abar : ℝ) (x : V2) :
    IsProx (fun w : V2 => ‖w‖ ^ 2) abar Cline (fun _ => (0 : ℝ)) x (projC x) := by
  refine ⟨projC_mem x, fun y hy => ?_⟩
  have hy01 := mem_Cline.1 hy
  simp only [mul_zero, zero_add, normsq2]
  simp only [projC, pt_zero, pt_one, PiLp.sub_apply]
  rw [← hy01]
  nlinarith [sq_nonneg (y 0 - (x 0 + x 1) / 2)]

/-- the position-block lift `Pb(x, v) = (P x, v)` -/
def Pb (P : V2 → V2) (z : V2 × V2) : V2 × V2 := (P z.1, z.2)


/-- The instance `E` has the computed pair `(m, L) = (1, 4)` in the sense of the landed hypotheses
(`Dal1a` = Dalalyan (1a), `LipGrad` = (1b)) and the unique minimiser `x* = 0`, `0 ∈ C`. -/
lemma EInst_dal1a : OCF.S1.Dal1a EInst 1 := by
  intro θ θ'
  rw [grad_EInst, normsq2]
  simp only [EInst, PiLp.sub_apply, PiLp.inner_apply, Fin.sum_univ_two, pt_zero, pt_one,
    RCLike.inner_apply, conj_trivial]
  nlinarith [sq_nonneg (θ 0 - θ' 0), sq_nonneg (θ 1 - θ' 1)]

lemma EInst_lip : OCF.G3.LipGrad EInst 4 := by
  intro u v
  have h : ‖gradient EInst u - gradient EInst v‖ ^ 2 ≤ (4 * ‖u - v‖) ^ 2 := by
    rw [grad_EInst, grad_EInst, normsq2, mul_pow, normsq2]
    simp only [PiLp.sub_apply, pt_zero, pt_one]
    nlinarith [sq_nonneg (u 0 - v 0), sq_nonneg (u 1 - v 1)]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma EInst_diff : Differentiable ℝ EInst := by
  unfold EInst; fun_prop

lemma EInst_min (y : V2) : EInst 0 ≤ EInst y := by
  simp only [EInst]; simp; positivity


/-- The Lyapunov function of the instance, `Λ_W(x, v) = E(x) − E* + c_β ‖v + ½∇E(x)‖²`, `E* = E(0)`. -/
noncomputable def LamI : V2 × V2 → ℝ := LamW EInst (EInst 0) (cBeta 4 aI bI)

lemma LamI_pt (a b u w : ℝ) :
    LamI (pt a b, pt u w) = (a ^ 2 + 4 * b ^ 2) / 2 + 2 / 63 * ((u + a / 2) ^ 2 + (w + 2 * b) ^ 2) := by
  unfold LamI; rw [lamW_pt, cI_val]

/-- **The landed theorem holds at the instance** (sanity: the all-states inequality for `W_hb`). -/
theorem instance_landed_decay {GK : V2 × V2 → V2 × V2}
    (hGK : IsGradPS (fun z : V2 × V2 => (1 / 2 : ℝ) * hbS aI bI * ‖z.2‖ ^ 2) GK) (z : V2 × V2) :
    LamI (hbWord EInst aI bI GK z) ≤ (25 / 32) * LamI z := by
  have hβsq : bI ^ 2 = (1 - aI * 1) * (1 - aI * 4) := by rw [bI_val, aI]; norm_num
  have := lamW_decay (E := EInst) (Es := EInst 0) (m := 1) (L := 4) (α := aI) (β := bI) (GK := GK)
    one_pos (by rw [aI]; norm_num) (by rw [bI_val]; norm_num) (by rw [bI_val]; norm_num) hGK hβsq
    (beck57_holds EInst 4 EInst_diff EInst_lip) (bubeck69_holds EInst 1 0 one_pos
      ((strongConv313_iff).2 EInst_dal1a) EInst_min) z
  have hq : (1 - aI * 1) = 25 / 32 := by rw [aI]; norm_num
  rw [hq] at this
  exact this

/-- **Proposition r0-transfer-instance.** -/
theorem r0_transfer_instance {GK : V2 × V2 → V2 × V2}
    (hGK : IsGradPS (fun z : V2 × V2 => (1 / 2 : ℝ) * hbS aI bI * ‖z.2‖ ^ 2) GK)
    {abar : ℝ} (_habar : 0 < abar) (P : V2 → V2)
    (hP : ∀ x, IsProx (fun w : V2 => ‖w‖ ^ 2) abar Cline (fun _ => (0 : ℝ)) x (P x)) :
    LamI zb = 95 / 504 ∧
    LamI (hbWord EInst aI bI GK zb) = 75979 / 516096 ∧
    LamI (hbWord EInst aI bI GK zb) ≤ hbQ 1 aI * LamI zb ∧
    LamI (Pb P (hbWord EInst aI bI GK zb)) = 13781 / 57344 ∧
    LamI (Pb P (hbWord EInst aI bI GK zb)) / LamI zb = 124029 / 97280 ∧
    hbQ 1 aI * LamI zb < LamI (Pb P (hbWord EInst aI bI GK zb)) ∧
    ¬ (∀ z : V2 × V2, LamI (Pb P (hbWord EInst aI bI GK z)) ≤ hbQ 1 aI * LamI z) := by
  have e1 : LamI zb = 95 / 504 := by
    unfold zb; rw [LamI_pt]; norm_num
  have e2 : LamI (hbWord EInst aI bI GK zb) = 75979 / 516096 := by
    rw [word_zb hGK, LamI_pt]; norm_num
  have e3 : LamI (Pb P (hbWord EInst aI bI GK zb)) = 13781 / 57344 := by
    rw [word_zb hGK]
    have : P (pt (-95/192) (-5/48)) = pt (-115/384) (-115/384) := by
      rw [prox_eq_projC (hP _)]; unfold projC; simp only [pt_zero, pt_one]
      congr 1 <;> norm_num
    simp only [Pb]; rw [this, LamI_pt]; norm_num
  rw [qI_val]
  refine ⟨e1, e2, by rw [e1, e2]; norm_num, e3, by rw [e1, e3]; norm_num,
    by rw [e1, e3]; norm_num, fun h => ?_⟩
  have := h zb
  rw [e1, e3] at this
  norm_num at this

/-- The instance data in one place: the pair `(1, 4)` of the landed hypotheses, `x* = 0 ∈ C`,
`α = 7/32 < 1/L`, `β = 5/16`, `s = 1/3`, `q = 25/32`, `c_β = 2/63`. -/
theorem instance_params :
    OCF.S1.Dal1a EInst 1 ∧ OCF.G3.LipGrad EInst 4 ∧ (∀ y, EInst 0 ≤ EInst y) ∧ (0 : V2) ∈ Cline ∧
    0 < aI ∧ aI < 1 / 4 ∧ bI = 5 / 16 ∧ hbS aI bI = 1 / 3 ∧ hbQ 1 aI = 25 / 32 ∧
    cBeta 4 aI bI = 2 / 63 := by
  refine ⟨EInst_dal1a, EInst_lip, EInst_min, ?_, by rw [aI]; norm_num, by rw [aI]; norm_num,
    bI_val, sI_val, qI_val, cI_val⟩
  rw [mem_Cline]; simp

/-! ## Part B: Proposition r0-order (algebra) -/

lemma caseC_ge {η u : ℝ} (hη2 : η < 2) (hu : 0 < u) (hu2 : u ^ 2 * (2 - η) = 2) (hB : 3 / 2 ≤ η) :
    1 ≤ (η - 1) * u := by
  by_contra hcon
  push Not at hcon
  have h2η : 0 < 2 - η := by linarith
  have e : (2 - η) * ((η - 1) * u) ^ 2 = 2 * (η - 1) ^ 2 := by linear_combination (η - 1) ^ 2 * hu2
  have hnn : 0 ≤ (η - 1) * u := mul_nonneg (by linarith) hu.le
  have hx2 : ((η - 1) * u) ^ 2 < 1 := by nlinarith
  have := mul_lt_mul_of_pos_left hx2 h2η
  nlinarith

/-- key algebra of r0-order (iii): `u > 0`, `u² (2 − η) = 2` (i.e. `u = (1 − η/2)^(−1/2)`), `0 < η < 2`. -/
lemma floors_key {η u : ℝ} (hη0 : 0 < η) (hη2 : η < 2) (hu : 0 < u) (hu2 : u ^ 2 * (2 - η) = 2) :
    (η < Real.sqrt 5 - 1 → u - 1 < |(|1 - η|) * u - 1|) ∧
    (η = Real.sqrt 5 - 1 → u - 1 = |(|1 - η|) * u - 1|) ∧
    (Real.sqrt 5 - 1 < η → |(|1 - η|) * u - 1| < u - 1) := by
  have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hs5 : 0 < Real.sqrt 5 := Real.sqrt_pos.2 (by norm_num)
  have h52 : 2 < Real.sqrt 5 := by nlinarith
  have h53 : Real.sqrt 5 < 5 / 2 := by nlinarith
  have hfac : η ^ 2 + 2 * η - 4 = (η - (Real.sqrt 5 - 1)) * (η + 1 + Real.sqrt 5) := by
    nlinarith
  have hpos : 0 < η + 1 + Real.sqrt 5 := by linarith
  -- sign of η u − 2 equals sign of η² + 2η − 4
  have hsq : (2 - η) * (η * u) ^ 2 = 2 * η ^ 2 := by linear_combination η ^ 2 * hu2
  have hdiff : (2 - η) * ((η * u) ^ 2 - 4) = 2 * (η ^ 2 + 2 * η - 4) := by
    linear_combination hsq
  have h2η : 0 < 2 - η := by linarith
  -- three ranges
  by_cases hA : η ≤ 1
  · -- f2 = 1 - (1-η) u, f1 < f2
    have ht : |1 - η| = 1 - η := abs_of_nonneg (by linarith)
    have hlt : (1 - η) * u < 1 := by
      by_contra hcon
      push Not at hcon
      have e : (2 - η) * ((1 - η) * u) ^ 2 = 2 * (1 - η) ^ 2 := by linear_combination (1 - η) ^ 2 * hu2
      nlinarith [mul_nonneg h2η.le (sub_nonneg.2 hcon), mul_nonneg (mul_nonneg h2η.le (sub_nonneg.2 hcon)) (sub_nonneg.2 hcon)]
    have hab : |(1 - η) * u - 1| = 1 - (1 - η) * u := by
      rw [abs_of_neg (by linarith)]; ring
    rw [ht, hab]
    have hlt2 : u * (2 - η) < 2 := by
      by_contra hcon
      push Not at hcon
      have e : (u * (2 - η)) ^ 2 = 2 * (2 - η) := by linear_combination (2 - η) * hu2
      nlinarith
    have hlt_s : η < Real.sqrt 5 - 1 := by linarith
    refine ⟨fun _ => by nlinarith, fun h => absurd h (by linarith), fun h => absurd h (by linarith)⟩
  · push Not at hA
    by_cases hB : η < 3 / 2
    · have ht : |1 - η| = η - 1 := by rw [abs_of_neg (by linarith)]; ring
      -- (η-1) u < 1
      have hlt : (η - 1) * u < 1 := by
        by_contra hcon
        push Not at hcon
        have e : (2 - η) * ((η - 1) * u) ^ 2 = 2 * (η - 1) ^ 2 := by linear_combination (η - 1) ^ 2 * hu2
        nlinarith [mul_nonneg h2η.le (sub_nonneg.2 hcon), mul_nonneg (mul_nonneg h2η.le (sub_nonneg.2 hcon)) (sub_nonneg.2 hcon)]
      have hab : |(η - 1) * u - 1| = 1 - (η - 1) * u := by
        rw [abs_of_neg (by linarith)]; ring
      rw [ht, hab]
      -- u - 1 < 1 - (η-1) u  <=>  η u < 2
      refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
      · have hneg : η ^ 2 + 2 * η - 4 < 0 := by
          rw [hfac]; exact mul_neg_of_neg_of_pos (by linarith) hpos
        have : (η * u) ^ 2 - 4 < 0 := by
          by_contra hcon; push Not at hcon; nlinarith
        nlinarith [mul_pos hη0 hu]
      · have h0 : η ^ 2 + 2 * η - 4 = 0 := by rw [hfac, h]; ring
        have : (η * u) ^ 2 - 4 = 0 := by
          have : (2 - η) * ((η * u) ^ 2 - 4) = 0 := by rw [hdiff, h0]; ring
          rcases mul_eq_zero.1 this with h' | h'
          · linarith
          · exact h'
        have h3 : η * u = 2 := by nlinarith [mul_pos hη0 hu]
        nlinarith
      · have hpos' : 0 < η ^ 2 + 2 * η - 4 := by
          rw [hfac]; exact mul_pos (by linarith) hpos
        have : 0 < (η * u) ^ 2 - 4 := by
          by_contra hcon; push Not at hcon; nlinarith
        nlinarith [mul_pos hη0 hu]
    · push Not at hB
      have ht : |1 - η| = η - 1 := by rw [abs_of_neg (by linarith)]; ring
      have hge : 1 ≤ (η - 1) * u := caseC_ge hη2 hu hu2 hB
      have hab : |(η - 1) * u - 1| = (η - 1) * u - 1 := abs_of_nonneg (by linarith)
      rw [ht, hab]
      have hlt_s : Real.sqrt 5 - 1 < η := by linarith
      refine ⟨fun h => absurd h (by linarith), fun h => absurd h (by linarith), fun _ => ?_⟩
      have := mul_pos h2η hu
      nlinarith

/-! ### The two Langevin letter orders on the 1-D quadratic -/

section Order

/-- Variance of `N_h ∘ D_h` (noise after the gradient step), `F(x) = μ x²/2`, temperature `T`:
`x ↦ (1 − hμ) x + √(2Th) ξ`, so `v ↦ (1 − hμ)² v + 2Th`. -/
def varND (T μ h v : ℝ) : ℝ := (1 - h * μ) ^ 2 * v + 2 * T * h

/-- Variance of `D_h ∘ N_h` (noise before the gradient step): `x ↦ (1 − hμ)(x + √(2Th) ξ)`. -/
def varDN (T μ h v : ℝ) : ℝ := (1 - h * μ) ^ 2 * (v + 2 * T * h)

/-- The stationary variances of [LANDED: ex:ou-words]: `(T/μ)/(1 − η/2)` and
`(T/μ)(1 − η)²/(1 − η/2)`, `η = hμ`. -/
noncomputable def statND (T μ h : ℝ) : ℝ := (T / μ) / (1 - h * μ / 2)
noncomputable def statDN (T μ h : ℝ) : ℝ := (T / μ) * (1 - h * μ) ^ 2 / (1 - h * μ / 2)

/-- `u = (1 − η/2)^(−1/2)`. -/
noncomputable def uF (η : ℝ) : ℝ := 1 / Real.sqrt (1 - η / 2)

/-- The Gaussian `W2` formula for centred Gaussians in one dimension, the HYPOTHESIS of r0-order:
[CLASSICAL] Bullo, Contraction Theory for Dynamical Systems v1.3, Ex. 6.11(iii),(iv), p. 229
(VERIFIED 2026-10-29): `W2(N(0, σ₁²), N(0, σ₂²)) = |σ₁ − σ₂|`, including `σ = 0` (Dirac).
`gauss σ` is the centred Gaussian law with standard deviation `σ ≥ 0`; `Law` and `W2` are abstract. -/
def W2Gaussian {Law : Type*} (gauss : ℝ → Law) (W2 : Law → Law → ℝ) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → W2 (gauss a) (gauss b) = |a - b|

/-- Non-vacuity of the named hypothesis: the model `Law = ℝ` (a law is its standard deviation),
`gauss = id`, `W2 a b = |a − b|` satisfies `W2Gaussian`. -/
theorem w2Gaussian_model : W2Gaussian (Law := ℝ) id (fun a b => |a - b|) := fun _ _ _ _ => rfl

lemma uF_sq {η : ℝ} (hη2 : η < 2) : uF η ^ 2 * (2 - η) = 2 := by
  unfold uF
  have h : 0 < 1 - η / 2 := by linarith
  have h2 : (2 : ℝ) - η ≠ 0 := (by linarith : 0 < 2 - η).ne'
  have h3 : (1 : ℝ) - η / 2 ≠ 0 := h.ne'
  rw [div_pow, Real.sq_sqrt h.le]
  field_simp

lemma uF_pos {η : ℝ} (hη2 : η < 2) : 0 < uF η := by
  unfold uF
  have h : 0 < 1 - η / 2 := by linarith
  positivity


lemma sqrt_statND {T μ h : ℝ} (hT : 0 < T) (hμ : 0 < μ) :
    Real.sqrt (statND T μ h) = Real.sqrt (T / μ) * uF (h * μ) := by
  rw [statND, Real.sqrt_div (by positivity)]
  unfold uF; ring

lemma sqrt_statDN {T μ h : ℝ} (hT : 0 < T) (hμ : 0 < μ) :
    Real.sqrt (statDN T μ h) = Real.sqrt (T / μ) * (|1 - h * μ| * uF (h * μ)) := by
  rw [statDN, Real.sqrt_div (by positivity), Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]
  unfold uF; ring

lemma varND_fixed {T μ h : ℝ} (hμ : 0 < μ) (hh : 0 < h) (hη : h * μ < 2) (v : ℝ) :
    varND T μ h v = v ↔ v = statND T μ h := by
  have hb : (1 - h * μ / 2) ≠ 0 := by have : 0 < 1 - h * μ / 2 := by linarith
                                      exact this.ne'
  have hη0 : 0 < h * μ := mul_pos hh hμ
  have hμ' : μ ≠ 0 := hμ.ne'
  have h4 : T / μ * (h * μ) = T * h := by field_simp
  unfold varND statND
  rw [eq_div_iff hb]
  constructor
  · intro e
    have e2 : v * (h * μ * (2 - h * μ)) = 2 * T * h := by linear_combination -e
    have e3 : (v * (1 - h * μ / 2) - T / μ) * (h * μ * 2) = 0 := by
      linear_combination e2 - 2 * h4
    rcases mul_eq_zero.1 e3 with h1 | h1
    · linarith
    · nlinarith
  · intro e
    linear_combination (-2 * (h * μ)) * e - 2 * h4

lemma varDN_fixed {T μ h : ℝ} (hμ : 0 < μ) (hh : 0 < h) (hη : h * μ < 2) (v : ℝ) :
    varDN T μ h v = v ↔ v = statDN T μ h := by
  have hb : (1 - h * μ / 2) ≠ 0 := by have : 0 < 1 - h * μ / 2 := by linarith
                                      exact this.ne'
  have hη0 : 0 < h * μ := mul_pos hh hμ
  have hμ' : μ ≠ 0 := hμ.ne'
  have h4 : T / μ * (h * μ) = T * h := by field_simp
  unfold varDN statDN
  rw [eq_div_iff hb]
  constructor
  · intro e
    have e2 : v * (h * μ * (2 - h * μ)) = 2 * T * h * (1 - h * μ) ^ 2 := by linear_combination -e
    have e3 : (v * (1 - h * μ / 2) - T / μ * (1 - h * μ) ^ 2) * (h * μ * 2) = 0 := by
      linear_combination e2 - 2 * (1 - h * μ) ^ 2 * h4
    rcases mul_eq_zero.1 e3 with h1 | h1
    · linarith
    · nlinarith
  · intro e
    linear_combination (-2 * (h * μ)) * e - 2 * (1 - h * μ) ^ 2 * h4


/-- **Proposition r0-order** (algebra; the Gaussian `W2` formula is the hypothesis `hW2`).
`d = 1`, `F(x) = μ x²/2`, `T, μ, h > 0`, `η := hμ ∈ (0, 2)`; the floors are
`f₁ = W2(π_ND, π_T)` and `f₂ = W2(π_DN, π_T)` for the centred Gaussians with the stationary
variances and the Gibbs variance `T/μ`.
(i) the stationary variances are the unique fixed points of the variance maps;
(ii) `Var π_DN = (1 − η)² Var π_ND` and they differ for every `η ∈ (0, 2)`;
(iii) `f₁ = √(T/μ) (u − 1)`, `f₂ = √(T/μ) |1 − |1 − η| u|`, `u = (1 − η/2)^(−1/2)`;
(iv) `f₁ < f₂` on `η < √5 − 1`, `f₁ = f₂` at `η = √5 − 1` (variances still differ), `f₁ > f₂` above;
(v) `η = 3/2 → f₂ = 0`. -/
theorem r0_order {Law : Type*} {gauss : ℝ → Law} {W2 : Law → Law → ℝ} (hW2 : W2Gaussian gauss W2)
    {T μ h : ℝ} (hT : 0 < T) (hμ : 0 < μ) (hh : 0 < h) (hη : h * μ < 2) :
    (∀ v, varND T μ h v = v ↔ v = statND T μ h) ∧
    (∀ v, varDN T μ h v = v ↔ v = statDN T μ h) ∧
    (statDN T μ h = (1 - h * μ) ^ 2 * statND T μ h ∧ statND T μ h ≠ statDN T μ h) ∧
    (W2 (gauss (Real.sqrt (statND T μ h))) (gauss (Real.sqrt (T / μ)))
        = Real.sqrt (T / μ) * (uF (h * μ) - 1) ∧
      W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ)))
        = Real.sqrt (T / μ) * abs (1 - abs (1 - h * μ) * uF (h * μ))) ∧
    (h * μ < Real.sqrt 5 - 1 →
      W2 (gauss (Real.sqrt (statND T μ h))) (gauss (Real.sqrt (T / μ)))
        < W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ)))) ∧
    (h * μ = Real.sqrt 5 - 1 →
      W2 (gauss (Real.sqrt (statND T μ h))) (gauss (Real.sqrt (T / μ)))
        = W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ))) ∧
      statND T μ h ≠ statDN T μ h) ∧
    (Real.sqrt 5 - 1 < h * μ →
      W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ)))
        < W2 (gauss (Real.sqrt (statND T μ h))) (gauss (Real.sqrt (T / μ)))) ∧
    (h * μ = 3 / 2 →
      W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ))) = 0) := by
  have hη0 : 0 < h * μ := mul_pos hh hμ
  have hs : 0 < Real.sqrt (T / μ) := Real.sqrt_pos.2 (by positivity)
  have hu := uF_pos hη
  have hu2 := uF_sq hη
  have hu1 : 1 < uF (h * μ) := by
    by_contra hcon
    push Not at hcon
    have h1 : uF (h * μ) ^ 2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right h1 (by linarith : (0:ℝ) ≤ 2 - h * μ)]
  have hb : 0 < 1 - h * μ / 2 := by linarith
  -- (ii)
  have hrel : statDN T μ h = (1 - h * μ) ^ 2 * statND T μ h := by unfold statDN statND; ring
  have hposND : 0 < statND T μ h := by unfold statND; positivity
  have hne : statND T μ h ≠ statDN T μ h := by
    intro e
    rw [hrel] at e
    have : statND T μ h * (h * μ * (2 - h * μ)) = 0 := by linear_combination e
    have h2 : 0 < h * μ * (2 - h * μ) := mul_pos hη0 (by linarith)
    have := mul_pos hposND h2
    linarith
  -- (iii)
  have hf1 : W2 (gauss (Real.sqrt (statND T μ h))) (gauss (Real.sqrt (T / μ)))
      = Real.sqrt (T / μ) * (uF (h * μ) - 1) := by
    rw [hW2 _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), sqrt_statND hT hμ,
      show Real.sqrt (T / μ) * uF (h * μ) - Real.sqrt (T / μ)
        = Real.sqrt (T / μ) * (uF (h * μ) - 1) by ring,
      abs_of_nonneg (mul_nonneg hs.le (by linarith))]
  have hf2 : W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ)))
      = Real.sqrt (T / μ) * abs (1 - abs (1 - h * μ) * uF (h * μ)) := by
    rw [hW2 _ _ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), sqrt_statDN hT hμ,
      show Real.sqrt (T / μ) * (|1 - h * μ| * uF (h * μ)) - Real.sqrt (T / μ)
        = Real.sqrt (T / μ) * (|1 - h * μ| * uF (h * μ) - 1) by ring,
      abs_mul, abs_of_pos hs, abs_sub_comm]
  have hkey := floors_key hη0 hη hu hu2
  have hf2' : W2 (gauss (Real.sqrt (statDN T μ h))) (gauss (Real.sqrt (T / μ)))
      = Real.sqrt (T / μ) * abs (abs (1 - h * μ) * uF (h * μ) - 1) := by
    rw [hf2, abs_sub_comm]
  refine ⟨fun v => varND_fixed hμ hh hη v, fun v => varDN_fixed hμ hh hη v, ⟨hrel, hne⟩,
    ⟨hf1, hf2⟩, fun hlt => ?_, fun heq => ⟨?_, hne⟩, fun hgt => ?_, fun h32 => ?_⟩
  · rw [hf1, hf2']; exact mul_lt_mul_of_pos_left (hkey.1 hlt) hs
  · rw [hf1, hf2', hkey.2.1 heq]
  · rw [hf1, hf2']; exact mul_lt_mul_of_pos_left (hkey.2.2 hgt) hs
  · rw [hf2']
    have hsq : uF (h * μ) ^ 2 = 4 := by
      linear_combination 2 * hu2 + 2 * uF (h * μ) ^ 2 * h32
    have hu4 : uF (h * μ) = 2 := by nlinarith
    rw [hu4, h32]
    norm_num

end Order

/-! ## Part C: Proposition r0-lyap-typing, d = 1 -/

/-- `d = 1`: `Λ_W(x, v) = E(x) − E* + c ‖v + ½∇E(x)‖²`, `∇E = E'`. -/
noncomputable def Lam1 (E : ℝ → ℝ) (Es c : ℝ) (z : ℝ × ℝ) : ℝ :=
  E z.1 - Es + c * (z.2 + deriv E z.1 / 2) ^ 2

/-- The gradient field of `Λ_W` on `ℝ × ℝ`: the pair of partial derivatives. -/
noncomputable def gradLam1 (E : ℝ → ℝ) (Es c : ℝ) (z : ℝ × ℝ) : ℝ × ℝ :=
  (deriv (fun x => Lam1 E Es c (x, z.2)) z.1, deriv (fun v => Lam1 E Es c (z.1, v)) z.2)

/-- `G` is Lipschitz for the Euclidean norm of `ℝ²` (stated with squares, no square roots). -/
def LipEuclid (G : ℝ × ℝ → ℝ × ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ z z' : ℝ × ℝ,
    ((G z).1 - (G z').1) ^ 2 + ((G z).2 - (G z').2) ^ 2 ≤ K ^ 2 * ((z.1 - z'.1) ^ 2 + (z.2 - z'.2) ^ 2)

section
variable {E : ℝ → ℝ} {Es c : ℝ}

lemma hasDerivAt_x (hE : Differentiable ℝ E) (hE1 : Differentiable ℝ (deriv E)) (x v : ℝ) :
    HasDerivAt (fun x => Lam1 E Es c (x, v))
      (deriv E x + c * ((v + deriv E x / 2) * deriv (deriv E) x)) x := by
  have h1 : HasDerivAt E (deriv E x) x := (hE x).hasDerivAt
  have h2 : HasDerivAt (deriv E) (deriv (deriv E) x) x := (hE1 x).hasDerivAt
  have h3 := ((h2.div_const 2).const_add v)
  have h5 := (h1.sub_const Es).add ((h3.pow 2).const_mul c)
  exact h5.congr_deriv (by simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one]; ring)

lemma hasDerivAt_v (x v : ℝ) :
    HasDerivAt (fun v => Lam1 E Es c (x, v)) (2 * c * (v + deriv E x / 2)) v := by
  have h := (((hasDerivAt_id v).add_const (deriv E x / 2)).pow 2).const_mul c
  have h' := h.const_add (E x - Es)
  exact h'.congr_deriv (by simp only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, id_eq]; ring)

lemma gradLam1_eq (hE : Differentiable ℝ E) (hE1 : Differentiable ℝ (deriv E)) (z : ℝ × ℝ) :
    gradLam1 E Es c z = (deriv E z.1 + c * ((z.2 + deriv E z.1 / 2) * deriv (deriv E) z.1),
      2 * c * (z.2 + deriv E z.1 / 2)) := by
  unfold gradLam1
  rw [(hasDerivAt_x hE hE1 z.1 z.2).deriv, (hasDerivAt_v z.1 z.2).deriv]


lemma smooth3 (hE3 : ContDiff ℝ 3 E) :
    Differentiable ℝ E ∧ Differentiable ℝ (deriv E) ∧ Differentiable ℝ (deriv (deriv E)) := by
  have e3 : ((2 : WithTop ℕ∞) + 1) = 3 := by norm_num
  have h3 : ContDiff ℝ ((2 : WithTop ℕ∞) + 1) E := by rw [e3]; exact hE3
  obtain ⟨h0, -, h1⟩ := contDiff_succ_iff_deriv.1 h3
  have e2 : ((1 : WithTop ℕ∞) + 1) = 2 := by norm_num
  have h1' : ContDiff ℝ ((1 : WithTop ℕ∞) + 1) (deriv E) := by rw [e2]; exact h1
  obtain ⟨h1d, -, h2⟩ := contDiff_succ_iff_deriv.1 h1'
  have h2' : ContDiff ℝ ((0 : WithTop ℕ∞) + 1) (deriv (deriv E)) := by
    simpa using h2
  obtain ⟨h2d, -, -⟩ := contDiff_succ_iff_deriv.1 h2'
  exact ⟨h0, h1d, h2d⟩


/-- Lipschitz gradient of `Λ_W` forces `E''' = 0` (`c > 0`, `E ∈ C³`). -/
theorem lip_imp_third_zero (hE3 : ContDiff ℝ 3 E) (hc : 0 < c) (hlip : LipEuclid (gradLam1 E Es c)) :
    ∀ x, deriv (deriv (deriv E)) x = 0 := by
  obtain ⟨hE, hE1, hE2⟩ := smooth3 hE3
  obtain ⟨K, hK0, hK⟩ := hlip
  intro x0
  -- for fixed v, `x ↦ ∂ₓΛ(x, v)` is K-Lipschitz
  have hlipv : ∀ v : ℝ, LipschitzWith K.toNNReal
      (fun x => deriv E x + c * ((v + deriv E x / 2) * deriv (deriv E) x)) := by
    intro v
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hK (x, v) (y, v)
    rw [gradLam1_eq hE hE1, gradLam1_eq hE hE1] at h
    simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero] at h
    have h1 : (deriv E x + c * ((v + deriv E x / 2) * deriv (deriv E) x) -
        (deriv E y + c * ((v + deriv E y / 2) * deriv (deriv E) y))) ^ 2 ≤ (K * |x - y|) ^ 2 := by
      rw [mul_pow, sq_abs]; nlinarith [sq_nonneg (2 * c * (v + deriv E x / 2) - 2 * c * (v + deriv E y / 2))]
    rw [Real.coe_toNNReal K hK0, Real.dist_eq, Real.dist_eq]
    exact abs_le_of_sq_le_sq h1 (by positivity)
  -- its derivative at `x0` is `a + b v` with `b = c E'''(x0)`
  set a := deriv (deriv E) x0 + c * ((deriv (deriv E) x0 / 2) * deriv (deriv E) x0
      + (deriv E x0 / 2) * deriv (deriv (deriv E)) x0) with ha
  set b := c * deriv (deriv (deriv E)) x0 with hb
  have hbd : ∀ v : ℝ, |a + b * v| ≤ K := by
    intro v
    have h1 : HasDerivAt (deriv E) (deriv (deriv E) x0) x0 := (hE1 x0).hasDerivAt
    have h2 : HasDerivAt (deriv (deriv E)) (deriv (deriv (deriv E)) x0) x0 := (hE2 x0).hasDerivAt
    have hd := h1.add ((((h1.div_const 2).const_add v).mul h2).const_mul c)
    have hder : deriv (fun x => deriv E x + c * ((v + deriv E x / 2) * deriv (deriv E) x)) x0
        = a + b * v := by
      have hd' : HasDerivAt (fun x => deriv E x + c * ((v + deriv E x / 2) * deriv (deriv E) x))
          (deriv (deriv E) x0 +
            c * (deriv (deriv E) x0 / 2 * deriv (deriv E) x0
              + (v + deriv E x0 / 2) * deriv (deriv (deriv E)) x0)) x0 := hd
      rw [hd'.deriv, ha, hb]; ring
    have := norm_deriv_le_of_lipschitz (x₀ := x0) (hlipv v)
    rw [hder, Real.norm_eq_abs, Real.coe_toNNReal K hK0] at this
    exact this
  by_contra hne
  have hb0 : b ≠ 0 := mul_ne_zero hc.ne' hne
  have h := hbd ((K + 1 - a) / b)
  rw [show a + b * ((K + 1 - a) / b) = K + 1 by field_simp; ring] at h
  have := (le_abs_self (K + 1))
  linarith


/-- `E‴ ≡ 0` (so `E″` constant) gives a quadratic polynomial. -/
theorem third_zero_imp_quad (hE3 : ContDiff ℝ 3 E) (h : ∀ x, deriv (deriv (deriv E)) x = 0) :
    ∃ a b k : ℝ, ∀ x, E x = a + b * x + k * x ^ 2 := by
  obtain ⟨hE, hE1, hE2⟩ := smooth3 hE3
  have c2 : ∀ x, deriv (deriv E) x = deriv (deriv E) 0 := fun x => is_const_of_deriv_eq_zero hE2 h x 0
  have g1 : Differentiable ℝ (fun x => deriv E x - deriv (deriv E) 0 * x) := by fun_prop
  have d1 : ∀ x, deriv (fun x => deriv E x - deriv (deriv E) 0 * x) x = 0 := by
    intro x
    have := ((hE1 x).hasDerivAt.sub ((hasDerivAt_id x).const_mul (deriv (deriv E) 0)))
    have hh : HasDerivAt (fun x => deriv E x - deriv (deriv E) 0 * x) 0 x :=
      this.congr_deriv (by rw [c2 x]; simp)
    exact hh.deriv
  have c1 : ∀ x, deriv E x = deriv E 0 + deriv (deriv E) 0 * x := by
    intro x
    have := is_const_of_deriv_eq_zero g1 d1 x 0
    simp at this; linarith
  have g0 : Differentiable ℝ (fun x => E x - (deriv E 0 * x + deriv (deriv E) 0 / 2 * x ^ 2)) := by fun_prop
  have d0 : ∀ x, deriv (fun x => E x - (deriv E 0 * x + deriv (deriv E) 0 / 2 * x ^ 2)) x = 0 := by
    intro x
    have h1 := (hE x).hasDerivAt
    have h2 := (((hasDerivAt_id x).const_mul (deriv E 0)).add (((hasDerivAt_id x).pow 2).const_mul (deriv (deriv E) 0 / 2)))
    have := h1.sub h2
    have hh : HasDerivAt (fun x => E x - (deriv E 0 * x + deriv (deriv E) 0 / 2 * x ^ 2)) 0 x :=
      this.congr_deriv (by rw [c1 x]; simp; ring)
    exact hh.deriv
  refine ⟨E 0, deriv E 0, deriv (deriv E) 0 / 2, fun x => ?_⟩
  have := is_const_of_deriv_eq_zero g0 d0 x 0
  simp at this; linarith

/-- A quadratic polynomial has `E‴ ≡ 0` and a Lipschitz `∇Λ_W` (any `c`, any `E*`). -/
theorem quad_imp_lip (a b k : ℝ) (hE : E = fun x => a + b * x + k * x ^ 2) :
    (∀ x, deriv (deriv (deriv E)) x = 0) ∧ LipEuclid (gradLam1 E Es c) := by
  have d1 : deriv E = fun x => b + 2 * k * x := by
    funext x
    subst hE
    have : HasDerivAt (fun x => a + b * x + k * x ^ 2) (b + 2 * k * x) x := by
      have := (((hasDerivAt_id x).const_mul b).const_add a).add (((hasDerivAt_id x).pow 2).const_mul k)
      exact this.congr_deriv (by simp; ring)
    exact this.deriv
  have d2 : deriv (deriv E) = fun _ => 2 * k := by
    funext x
    rw [d1]
    have : HasDerivAt (fun x => b + 2 * k * x) (2 * k) x := by
      have := ((hasDerivAt_id x).const_mul (2 * k)).const_add b
      simpa using this
    exact this.deriv
  have d3 : deriv (deriv (deriv E)) = fun _ => 0 := by
    funext x; rw [d2]; simp
  have hdiff : Differentiable ℝ E := by subst hE; fun_prop
  have hdiff1 : Differentiable ℝ (deriv E) := by rw [d1]; fun_prop
  refine ⟨fun x => by rw [d3], ?_⟩
  refine ⟨Real.sqrt ((2 * k + 2 * c * k ^ 2) ^ 2 + (2 * c * k) ^ 2 + (2 * c * k) ^ 2 + (2 * c) ^ 2),
    Real.sqrt_nonneg _, fun z z' => ?_⟩
  rw [gradLam1_eq hdiff hdiff1, gradLam1_eq hdiff hdiff1, Real.sq_sqrt (by positivity)]
  have e1 : ∀ x, deriv E x = b + 2 * k * x := fun x => by rw [d1]
  have e2 : ∀ x, deriv (deriv E) x = 2 * k := fun x => by rw [d2]
  simp only [e1, e2]
  nlinarith [sq_nonneg ((2 * k + 2 * c * k ^ 2) * (z.2 - z'.2) - (2 * c * k) * (z.1 - z'.1)),
    sq_nonneg ((2 * c * k) * (z.2 - z'.2) - (2 * c) * (z.1 - z'.1))]

end

/-- **Proposition r0-lyap-typing, d = 1.** For `E ∈ C³(ℝ)` and any `c > 0`, `E*`: the gradient of
`Λ_W(x, v) = E(x) − E* + c (v + E'(x)/2)²` is Lipschitz on `ℝ × ℝ` iff `E‴ ≡ 0` (the Hessian `E″` of `E`
is constant), iff `E` is a quadratic polynomial. -/
theorem r0_lyap_typing_d1 {E : ℝ → ℝ} {Es c : ℝ} (hE3 : ContDiff ℝ 3 E) (hc : 0 < c) :
    (LipEuclid (gradLam1 E Es c) ↔ ∀ x, deriv (deriv (deriv E)) x = 0) ∧
    ((∀ x, deriv (deriv (deriv E)) x = 0) ↔ ∃ a b k : ℝ, ∀ x, E x = a + b * x + k * x ^ 2) := by
  have hq : (∀ x, deriv (deriv (deriv E)) x = 0) ↔ ∃ a b k : ℝ, ∀ x, E x = a + b * x + k * x ^ 2 := by
    constructor
    · exact third_zero_imp_quad hE3
    · rintro ⟨a, b, k, hk⟩
      exact (quad_imp_lip (Es := Es) (c := c) a b k (funext hk)).1
  refine ⟨⟨lip_imp_third_zero hE3 hc, fun h => ?_⟩, hq⟩
  obtain ⟨a, b, k, hk⟩ := hq.1 h
  exact (quad_imp_lip (Es := Es) (c := c) a b k (funext hk)).2

/-- The same at `c = c_β` of the heavy-ball tuning with a computed pair `(m, L)` (`0 < m ≤ L`,
`0 < α`, `αL < 1`; the pair hypotheses on `E` of the dossier are carried but not needed). -/
theorem r0_lyap_typing_d1_cbeta {E : ℝ → ℝ} {m L α Es : ℝ} (hE3 : ContDiff ℝ 3 E)
    (_hm : 0 < m) (_hmL : m ≤ L) (hα : 0 < α) (hαL : α * L < 1)
    (_h1a : OCF.S1.Dal1a E m) (_h1b : OCF.G3.LipGrad E L) :
    0 < cBeta L α (hbBeta m L α) ∧
    ((LipEuclid (gradLam1 E Es (cBeta L α (hbBeta m L α))) ↔ ∀ x, deriv (deriv (deriv E)) x = 0) ∧
    ((∀ x, deriv (deriv (deriv E)) x = 0) ↔ ∃ a b k : ℝ, ∀ x, E x = a + b * x + k * x ^ 2)) := by
  have hc : 0 < cBeta L α (hbBeta m L α) := by
    unfold cBeta
    have hb := beta_nonneg m L α
    exact div_pos (mul_pos (mul_pos two_pos hα) (by linarith)) (pow_pos (by linarith) 2)
  exact ⟨hc, r0_lyap_typing_d1 hE3 hc⟩

#print axioms OCF.R0.r0_transfer_instance
#print axioms OCF.R0.instance_landed_decay
#print axioms OCF.R0.instance_params
#print axioms OCF.R0.r0_order
#print axioms OCF.R0.r0_lyap_typing_d1
#print axioms OCF.R0.r0_lyap_typing_d1_cbeta

end OCF.R0

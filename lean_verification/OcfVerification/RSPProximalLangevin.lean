/-
R-SP (the proximal Langevin word: contraction factor, targets, floors) — the exact-arithmetic Lean
candidates of the adjudicated dossier (section 5 and 03_adjudication.md section 3). Novel parts only; every
law-level statement (W2 contraction, own-law certificate, Moreau-Yosida instance, conditional certificate,
refusal, colour remark) is PROSE-ONLY in the dossier and is NOT formalised here.

Source of truth: project_plan/doing/proof_audits/R_SP_proximal_langevin/01_derivation.md (adjudicated stage 3,
2026-10-29, repaired after the B4 mini-audit, 03_adjudication.md section 6), sections 2 (r-sp-factor, r-sp-step),
3.1 (r-sp-own (c)), 3.2 (r-sp-my, r-sp-zero, r-sp-lamh), 3.3 (r-sp-cond (c), (d)), 4 (r-sp-order, r-sp-frame),
5 (Lean tiers); rulings in 03_adjudication.md.
Dossier sha16 (first 16 hex of sha256sum of 01_derivation.md) when last checked: e612caec7929b3ce
(formalised first against 9657e419a7c0f97a; the drift check of 2026-10-29 against the B4-repaired text found
every formalised statement unchanged; only renames, the candidate list and the NDP/NPD wording moved).

DEFINITIONAL MAP (dossier symbol — Lean name):
* rho = (1 − m h)/(1 + h sg) — `rho m h sg`; max(|1 − h m|, |1 − h L|) — `lipD m L h`.
* Letters, by ORDER OF APPLICATION (first letter first), on a real normed space `X` (R^d):
  D = x − h ∇F(x) — `dS h G` (G stands for ∇F; E0's `dstep h id G`); N = x + z (realised noise z) — `nS z`;
  P = prox_{h g} — a map `P` with `∀ x, IsProx (‖·‖²) h univ g x (P x)` (E0's `IsProx`, the defining
  minimisation; never assumed to be a formula). The six words — `wDNP wDPN wNDP wNPD wPDN wPND`
  ((x, z) ↦ ω(x; z); e.g. `wDNP x z = P (N_z (D x))`, the dossier's P ∘ N ∘ D).
* Moreau–Yosida step x − h ∇F(x) − (h/λ)(x − prox_{λg}(x)) — `myStep h lam G P` (P the prox letter of λ g).
  bias(h) = 1.82 ((L + ell)/m) sqrt(T h d) — `biasMY ell L m T h d`; r_0^λ — `r0MY lam m T d gF u`
  (gF = ∇F(x_0), u = x_0 − prox_{λ g}(x_0)); the landed constants `OCF.S1.bias`, `OCF.S1.r0`.
* d = 1 instance of r-sp-lamh: F = x²/2 (∇F = `deriv (fun x => x^2/2)`, `deriv_half_sq`), g = |·|, prox of
  (1/2)|·| any map with `IsProx … (1/2) … (fun y => |y|)`; soft threshold — `softThr` (proved to be the prox
  letter: `isProx_softThr`, and the only one: `prox_abs_eq`). Bias coefficient (L + 1/h)/m · sqrt(T h d) —
  `biasCoeff m L T h d`; (1 + L h)/sqrt h — `psi L h`.
* r-sp-order (d = 1, F = (κ/2) x², g = (sg/2) x², m = L = κ): orders — `Ord6`; a_D = 1 − h κ, u = 1/(1 + h sg),
  ρ = a_D u (the dossier's B4 renames of dl and p; `lP sg h x = u x`); `∇F x = κ x` (`deriv_quad`), P = `lP sg h` (x ↦ x/(1 + h sg), proved a prox letter: `isProx_lP`);
  the six words — `word κ sg h ω`; c_ω — `cOf` (c = 1 for DPN, PDN; u for DNP; a_D for PND; ρ for NDP, NPD), and
  `word_lin`: ω(x; z) = ρ x + c_ω z (proved from the letters, so the six mean maps coincide);
  stationary variance v_ω = c_ω² 2 T h/(1 − ρ²) — `statVar T h κ sg ω` (the unique fixed point of the
  variance map, `statVar_fixed`); Gibbs variance T/(κ + sg) — `gibbsVar T κ sg`; the class (κ > 0, 0 < h,
  h κ ≤ 1 = 2/(m + L), sg ≥ 0, T > 0) — `InClass κ sg h T`.
* r-sp-cond (c), (d): the squared inequality a² ≤ r^k b² + c with r = 1 − h m — `sqrt_conversion`
  (r^{k/2} = (√r)^k), `sqrt_conversion_rpow` (r^{(k:ℝ)/2}), `r_sp_cond_count`.
* r-sp-frame: E^[c](x) = c⁻¹ E(c x) — `scaleE c E x`; prox attribute c⁻¹ P_g(c α, c x) — `frame_prox_iff`.

NAMED HYPOTHESES: none. The classical cores the dossier cites (K1/K2 Lipschitz constants of the letters,
K13 equal-covariance Gaussian W2, K17 AR(1) stationary variance) enter only as the dossier's own tags: K17 is
replaced here by the DEFINITION of v_ω as the fixed point of the variance map (`statVar_fixed`); K13 is not used
(the supremum of the mean-map ratio is computed, `quad_family_sup`; "W2 = mean difference" is cited prose).

COVERAGE (dossier item — Lean name), all FORMALISED (statement + proof, no sorry):
* (a) r-sp-factor arithmetic — `r_sp_factor_arith`: for 0 < m ≤ L, 0 < h ≤ 2/(m+L), sg ≥ 0: ρ ∈ [0, 1),
  1 − ρ = h (m + sg)/(1 + h sg) and ρ = max(|1 − h m|, |1 − h L|)/(1 + h sg) (`lipD_eq`).
* (b) r-sp-step — `step_formula_fails` (every h > 2/(m+L): the true constant is (h L − 1)/(1 + h sg) and ρ is
  strictly below it), `hL_gt_iff` (h L − 1 > 1 − m h iff h > 2/(m+L)), `step_formula_boundary` (equality at
  h = 2/(m+L)), `quad_family_sup` (the supremum of |A e|/|e| for A = diag(1 − h m, 1 − h L)/(1 + h sg) is
  max(…)/(1 + h sg), attained: `IsGreatest`), `step_counterexample` (m = 1, L = 3, sg = 1/2, h = 3/4: lipD = 5/4,
  ρ = 2/11, sup ratio 10/11, and 2/(m+L) = 1/2 < 3/4), `step_formula_negative_mL` (m = L: ρ < 0 once h > 1/m).
* (c) r-sp-zero (a), (b), (c) arithmetic — `isProx_zero_iff` (prox of the zero function is the identity),
  `r_sp_zero_kernel` (the identity, myStep = D for every λ, and the six words are N∘D (DNP, DPN, PDN) and
  D∘N (NDP, NPD, PND), as maps), `r_sp_zero_constants` and `r_sp_zero_r0` (the change of constants ell = 0:
  range 2/(m+L), bias and start bound are the landed S1 constants `OCF.S1.bias`, `OCF.S1.r0`),
  `floor_bias_ratio` (floor_*/bias² = 2m/(3.3124 L) ≤ 0.604 at g = 0, M_g = 0).
* (d) r-sp-lamh — `myStep_lamh` (λ = h: x ↦ P x − h ∇F x), `lamh_admissible` (h ≤ 2/(m + L + 1/h) iff
  h (m+L) + 1 ≤ 2), `r_sp_lamh_example` (d = 1, h = 1/2, x = 4/5: the three maps give −1/10, 0, 3/20, for
  every prox letter of (1/2)|·|), `r_sp_lamh_bias` (the bias coefficient is decreasing in h on (0, 1/(m+L)] and
  at least (m + 2L) sqrt(T d)/(m sqrt(m + L)), attained at the right end), `r_sp_lamh_witness` (m = 1, L = 3,
  T = d = 1: 7/2 at h = 1/4 and 403/20 at h = 1/400). The factor 1.82 multiplies both sides.
* (e) r-sp-order — `word_lin`, `statVar_fixed`, `exact_iff` (v_ω = T/(κ+sg) iff 2 (c_ω (1 + h sg))² = 2 + h (sg − κ)),
  `exact_DNP` (iff κ = sg, every admissible h), `exact_DPN_never`, `exact_PDN_never`, `exact_NDP_iff`,
  `exact_NPD_iff` (only at h = (3κ + sg)/(2κ²)), `exact_NDP_outside`, `exact_NPD_outside` (that step is outside
  the class), `ndp_locus_ge`, `exact_PND_iff` (the PND curve 2((1 − hκ)(1 + h sg))² = 2 + h (sg − κ)),
  `exact_PND_instance` (κ = 1, h = 1/4, T = 1, sg = (4 √70 − 20)/9 ≠ κ, in the class: stationary variance =
  T/(κ + sg)), `order_witness` (κ = 1, sg = 1/2, T = 1, h = 1/4: Gibbs 2/3; variances 32/45, 9/10, 2/5, 2/5, 9/10,
  81/160). Scope as in the dossier: d = 1 quadratics only.
* (f) r-sp-cond (c) — `sqrt_conversion`, `sqrt_conversion_rpow` (a, b, c, r ≥ 0: a² ≤ r^k b² + c ⟹
  a ≤ r^{k/2} b + √c); (d) — `r_sp_cond_count` (every K ≥ ⌈log(r_0²/(ε² − floor))/(h m)⌉₊ gives a ≤ ε when
  a² ≤ (1 − h m)^K r_0² + floor, for ε > 0 with floor < ε²); r-sp-own (c) — `log_inv_ge` (log(1/ρ) ≥ 1 − ρ),
  `pow_mul_le_of_log`, `r_sp_own_count` (k ≥ ⌈((1 + h sg)/(h (m + sg))) log(D̄/((1 − ρ) ε))⌉₊ ⟹
  ρ^k D̄/(1 − ρ) ≤ ε, hence K_ε ≤ max{0, ⌈…⌉}).
* (g) r-sp-frame, the pure-algebra part — `frame_energy` (c E^[c](x) = E(c x)), `frame_gibbs`
  (E^[c]/(T/c) = E(c x)/T, so the Gibbs exponents agree), `frame_prox_iff` (p = prox_{α g^[c]}(x) iff
  c p = prox_{c α g}(c x), i.e. the carried attribute c⁻¹ P_g(c α, c x)), `frame_factor` (the factor at the
  converted pair (c m, c L), curvature c sg, step range 2/(c (m + L)): ρ^[c] = (1 − c m h)/(1 + c h sg) ∈ [0, 1)).
* NOT formalised (prose or landed): the law-level statements listed above; that the lifted conjugation
  W⁺ ∘ (·) ∘ W with W^T W = c I yields the word of (F^[c], g^[c]) (lem:conj-lifted, landed; needs the matrix
  W), gradient of F^[c], curvature/convexity of g^[c], the dossier's "mutations", the Gaussian W2 and
  AR(1) classical inputs (K13, K17), m = L from r-sp-pair(b), the witnesses' non-exact (floating point) outputs.
* DOSSIER NOTE (agreement after the B4 repair): the dossier now reads the NDP/NPD step
  h = (3κ + sg)/(2κ²) as "≥ 3/(2κ) (equality at sg = 0), and 3/(2κ) > 1/κ, so outside the class", exactly the
  formalised `ndp_locus_ge` (`≥ 3/(2κ)`, equality iff sg = 0, `> 1/κ` always).
* DOSSIER NOTE (candidate list): the repaired section 5 no longer lists sqrt(a + b) ≤ sqrt a + sqrt b nor the
  squared-to-W2 conversion (r-sp-cond (c)) as Lean candidates (both are ELEMENTARY there). `sqrt_conversion`,
  `sqrt_conversion_rpow` (statement unchanged: a² ≤ r^k b² + c ⟹ a ≤ r^{k/2} b + √c) and the helper
  `sqrt_add_le_add_sqrt'` are retained as extras, proved and sorry-free; `r_sp_cond_count` (d) was never on
  the candidate list either. Neither affects any other item.
* DOSSIER NOTE (refusal clause): its new exemption (E2) for g declared zero rests on the kernel identity and
  the three/three split of the orders, which are `r_sp_zero_kernel`; the clause itself is prose-only.

Status tier: FORMALISED (statement + proof, no sorry) for items (a) to (g) as listed. STATUS: COMPLETE.
-/
import Mathlib
import OcfVerification.E0MethodWords
import OcfVerification.S1StochasticWord

open OCF.E0

namespace OCF.RSP

/-! ## Part A: the contraction-factor arithmetic (r-sp-factor, the arithmetic of rho) -/

/-- The factor `ρ = (1 − m h)/(1 + h sg)`. -/
noncomputable def rho (m h sg : ℝ) : ℝ := (1 - m * h) / (1 + h * sg)

/-- The Lipschitz factor of the gradient step on a quadratic with eigenvalues in `[m, L]`:
`max (|1 − h m|, |1 − h L|)`. -/
noncomputable def lipD (m L h : ℝ) : ℝ := max |1 - h * m| |1 - h * L|

lemma step_mul_le {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hhL : h ≤ 2 / (m + L)) :
    h * (m + L) ≤ 2 := by
  have : 0 < m + L := by linarith
  rwa [le_div_iff₀ this] at hhL

lemma lipD_eq {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) (hhL : h ≤ 2 / (m + L)) :
    lipD m L h = 1 - h * m := by
  have h2 := step_mul_le hm hmL hhL
  have hm1 : h * m ≤ 1 := by nlinarith
  unfold lipD
  rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - h * m)]
  apply max_eq_left
  rw [abs_le]
  constructor <;> nlinarith

theorem r_sp_factor_arith {m L h sg : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h)
    (hhL : h ≤ 2 / (m + L)) (hsg : 0 ≤ sg) :
    0 ≤ rho m h sg ∧ rho m h sg < 1 ∧ 1 - rho m h sg = h * (m + sg) / (1 + h * sg) ∧
      rho m h sg = lipD m L h / (1 + h * sg) := by
  have h2 := step_mul_le hm hmL hhL
  have hm1 : h * m ≤ 1 := by nlinarith
  have hpos : 0 < 1 + h * sg := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold rho; apply div_nonneg <;> linarith
  · unfold rho; rw [div_lt_one hpos]; nlinarith
  · unfold rho; field_simp; ring
  · rw [lipD_eq hm hmL hh hhL]; unfold rho; rw [mul_comm m h]

/-! ## Part B: the step formula (r-sp-step) -/

lemma lipD_eq_of_gt {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h)
    (hgt : 2 / (m + L) < h) : lipD m L h = h * L - 1 := by
  have hs : 0 < m + L := by linarith
  have h2 : 2 < h * (m + L) := by rwa [div_lt_iff₀ hs] at hgt
  unfold lipD
  have hL : 1 ≤ h * L := by nlinarith
  rw [abs_of_nonpos (by linarith : 1 - h * L ≤ 0), show -(1 - h * L) = h * L - 1 by ring]
  apply max_eq_right
  rw [abs_le]
  constructor <;> nlinarith

/-- `h L − 1 > 1 − m h` iff `h > 2/(m+L)`. -/
theorem hL_gt_iff {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L) :
    1 - m * h < h * L - 1 ↔ 2 / (m + L) < h := by
  have hs : 0 < m + L := by linarith
  rw [div_lt_iff₀ hs]; constructor <;> intro H <;> nlinarith

/-- Past `2/(m+L)` the formula `ρ` is strictly below the true Lipschitz constant of the
quadratic family `(h L − 1)/(1 + h sg)`. -/
theorem step_formula_fails {m L h sg : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h)
    (hsg : 0 ≤ sg) (hgt : 2 / (m + L) < h) :
    lipD m L h = h * L - 1 ∧ rho m h sg < lipD m L h / (1 + h * sg) := by
  have hpos : 0 < 1 + h * sg := by positivity
  refine ⟨lipD_eq_of_gt hm hmL hh hgt, ?_⟩
  rw [lipD_eq_of_gt hm hmL hh hgt]
  unfold rho
  exact div_lt_div_of_pos_right ((hL_gt_iff hm hmL).2 hgt) hpos

/-- At `h = 2/(m+L)` the formula is attained. -/
theorem step_formula_boundary {m L sg : ℝ} (hm : 0 < m) (hmL : m ≤ L) (_hsg : 0 ≤ sg) :
    rho m (2 / (m + L)) sg = lipD m L (2 / (m + L)) / (1 + 2 / (m + L) * sg) := by
  have hs : 0 < m + L := by linarith
  rw [lipD_eq hm hmL (by positivity) le_rfl]; unfold rho; rw [mul_comm m]

/-- The sup ratio over the quadratic family (mean map `diag(a, b)`). -/
def ratioSet (a b : ℝ) : Set ℝ :=
  {r | ∃ e1 e2 : ℝ, (e1 ≠ 0 ∨ e2 ≠ 0) ∧
    r = Real.sqrt (a ^ 2 * e1 ^ 2 + b ^ 2 * e2 ^ 2) / Real.sqrt (e1 ^ 2 + e2 ^ 2)}

theorem ratioSet_greatest (a b : ℝ) : IsGreatest (ratioSet a b) (max |a| |b|) := by
  constructor
  · rcases le_total |b| |a| with h | h
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      rw [max_eq_left h]; simp [Real.sqrt_sq_eq_abs]
    · refine ⟨0, 1, Or.inr one_ne_zero, ?_⟩
      rw [max_eq_right h]; simp [Real.sqrt_sq_eq_abs]
  · rintro r ⟨e1, e2, hne, rfl⟩
    have hs : 0 < e1 ^ 2 + e2 ^ 2 := by
      rcases hne with h | h
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg e2]
      · have := sq_pos_of_ne_zero h; nlinarith [sq_nonneg e1]
    have hsq : 0 < Real.sqrt (e1 ^ 2 + e2 ^ 2) := Real.sqrt_pos.2 hs
    rw [div_le_iff₀ hsq]
    set M := max |a| |b| with hM
    have ha : a ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs a]; exact pow_le_pow_left₀ (abs_nonneg a) (le_max_left _ _) 2
    have hb : b ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs b]; exact pow_le_pow_left₀ (abs_nonneg b) (le_max_right _ _) 2
    have hM0 : 0 ≤ M := le_trans (abs_nonneg a) (le_max_left _ _)
    calc Real.sqrt (a ^ 2 * e1 ^ 2 + b ^ 2 * e2 ^ 2)
        ≤ Real.sqrt (M ^ 2 * (e1 ^ 2 + e2 ^ 2)) := by
          apply Real.sqrt_le_sqrt
          nlinarith [sq_nonneg e1, sq_nonneg e2, mul_le_mul_of_nonneg_right ha (sq_nonneg e1),
            mul_le_mul_of_nonneg_right hb (sq_nonneg e2)]
      _ = M * Real.sqrt (e1 ^ 2 + e2 ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0]

/-- r-sp-step: on the quadratic family `F = (m x₁² + L x₂²)/2`, `g = (sg/2)|x|²`, the mean map of
every order is `diag(1 − h m, 1 − h L)/(1 + h sg)` and the supremum of the ratio is
`max(|1 − h m|, |1 − h L|)/(1 + h sg)`. -/
theorem quad_family_sup {m L h sg : ℝ} (hsg : 0 ≤ sg) (hh : 0 < h) :
    IsGreatest (ratioSet ((1 - h * m) / (1 + h * sg)) ((1 - h * L) / (1 + h * sg)))
      (lipD m L h / (1 + h * sg)) := by
  have hpos : 0 < 1 + h * sg := by positivity
  have := ratioSet_greatest ((1 - h * m) / (1 + h * sg)) ((1 - h * L) / (1 + h * sg))
  rwa [abs_div, abs_div, abs_of_pos hpos, max_div_div_right hpos.le] at this

/-- The dossier's numerical instance `m = 1, L = 3, sg = 1/2, h = 3/4`. -/
theorem step_counterexample :
    lipD 1 3 (3/4) = 5/4 ∧ rho 1 (3/4) (1/2) = 2/11 ∧ lipD 1 3 (3/4) / (1 + 3/4 * (1/2)) = 10/11 ∧
    rho 1 (3/4) (1/2) < lipD 1 3 (3/4) / (1 + 3/4 * (1/2)) ∧ (2:ℝ) / (1 + 3) < 3/4 := by
  have e1 : lipD 1 3 (3/4) = 5/4 := by
    unfold lipD; rw [max_eq_right] <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  refine ⟨e1, ?_, ?_, ?_, by norm_num⟩
  · unfold rho; norm_num
  · rw [e1]; norm_num
  · rw [e1]; unfold rho; norm_num

/-- For `m = L` the formula is negative once `h > 1/m` (`h > 2/(m+L)`). -/
theorem step_formula_negative_mL {m h sg : ℝ} (hm : 0 < m) (hsg : 0 ≤ sg) (hh : 1 / m < h) :
    rho m h sg < 0 := by
  unfold rho
  have : 1 < m * h := by rwa [div_lt_iff₀ hm, mul_comm] at hh
  have h0 : 0 < h := lt_trans (by positivity) hh
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)


/-! ## Part C: the g = 0 kernel identity (r-sp-zero) -/

noncomputable section zero
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Letter `D`: `x − h ∇F(x)` (E0's `dstep h id G`). -/
def dS (h : ℝ) (G : X → X) (x : X) : X := x - h • G x

/-- Letter `N` with the realised noise `z`: `x + z`. -/
def nS (z x : X) : X := x + z

/-- Moreau–Yosida step `x − h ∇F(x) − (h/λ)(x − prox_{λ g}(x))`; `P` is the prox letter of `λ g`. -/
def myStep (h lam : ℝ) (G : X → X) (P : X → X) (x : X) : X :=
  x - h • G x - (h / lam) • (x - P x)

/-- The six words, by ORDER OF APPLICATION (first letter first), as maps `(x, z) ↦ ω(x; z)`. -/
def wDNP (h : ℝ) (G P : X → X) (x z : X) : X := P (nS z (dS h G x))
def wDPN (h : ℝ) (G P : X → X) (x z : X) : X := nS z (P (dS h G x))
def wNDP (h : ℝ) (G P : X → X) (x z : X) : X := P (dS h G (nS z x))
def wNPD (h : ℝ) (G P : X → X) (x z : X) : X := dS h G (P (nS z x))
def wPDN (h : ℝ) (G P : X → X) (x z : X) : X := nS z (dS h G (P x))
def wPND (h : ℝ) (G P : X → X) (x z : X) : X := dS h G (nS z (P x))

omit [NormedSpace ℝ X] in
/-- The prox of the zero function is the identity (defining minimisation, E0's `IsProx`). -/
theorem isProx_zero_iff (α : ℝ) (x p : X) :
    IsProx (fun w => ‖w‖ ^ 2) α Set.univ (fun _ => (0:ℝ)) x p ↔ p = x := by
  constructor
  · rintro ⟨-, h⟩
    have := h x (Set.mem_univ _)
    simp only [sub_self, norm_zero] at this
    have h0 : ‖p - x‖ ^ 2 ≤ 0 := by nlinarith
    have : ‖p - x‖ = 0 := by nlinarith [norm_nonneg (p - x)]
    exact sub_eq_zero.1 (norm_eq_zero.1 this)
  · rintro rfl
    refine ⟨Set.mem_univ _, fun y _ => ?_⟩
    simp only [sub_self, norm_zero]
    nlinarith [sq_nonneg ‖y - p‖]

/-- r-sp-zero (a), kernel: at `g = 0` the prox letter is the identity, the Moreau–Yosida step is
`x − h ∇F(x)` for every `λ`, and the six words are `N ∘ D` (orders DNP, DPN, PDN) and `D ∘ N`
(orders NDP, NPD, PND), as maps. -/
theorem r_sp_zero_kernel (h : ℝ) (G P : X → X)
    (hP : ∀ x, IsProx (fun w => ‖w‖ ^ 2) h Set.univ (fun _ => (0:ℝ)) x (P x)) :
    (∀ x, P x = x) ∧
    (∀ lam, myStep h lam G P = dS h G) ∧
    (wDNP h G P = fun x z => nS z (dS h G x)) ∧
    (wDPN h G P = fun x z => nS z (dS h G x)) ∧
    (wPDN h G P = fun x z => nS z (dS h G x)) ∧
    (wNDP h G P = fun x z => dS h G (nS z x)) ∧
    (wNPD h G P = fun x z => dS h G (nS z x)) ∧
    (wPND h G P = fun x z => dS h G (nS z x)) := by
  have hid : ∀ x, P x = x := fun x => (isProx_zero_iff h x (P x)).1 (hP x)
  refine ⟨hid, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lam; funext x; simp [myStep, dS, hid]
  all_goals (funext x z; simp [wDNP, wDPN, wNDP, wNPD, wPDN, wPND, hid])

/-- Change of constants at `ell = 0` (r-sp-zero (a)): the Moreau–Yosida range, factor, bias and start
bound are the constants of the landed `S1StochasticWord` (`OCF.S1.bias`, `OCF.S1.r0`). -/
def biasMY (ell L m T h : ℝ) (d : ℕ) : ℝ := 1.82 * ((L + ell) / m) * Real.sqrt (T * h * d)

/-- `r_0^λ`, with `u` standing for `x₀ − prox_{λ g}(x₀)` and `gF = ∇F(x₀)`. -/
def r0MY (lam m T : ℝ) (d : ℕ) (gF u : X) : ℝ :=
  ‖gF + (1 / lam) • u‖ / m + Real.sqrt (T * d / m)

theorem r_sp_zero_constants (L m T h : ℝ) (d : ℕ) :
    2 / (m + (L + 0)) = 2 / (m + L) ∧ biasMY 0 L m T h d = OCF.S1.bias T d m L h := by
  refine ⟨by simp, ?_⟩
  simp [biasMY, OCF.S1.bias]

theorem r_sp_zero_r0 (lam m T : ℝ) (d : ℕ) (gF x0 : X) (P : X → X)
    (hP : IsProx (fun w => ‖w‖ ^ 2) lam Set.univ (fun _ => (0:ℝ)) x0 (P x0)) :
    r0MY lam m T d gF (x0 - P x0) = OCF.S1.r0 ‖gF‖ T d m := by
  have := (isProx_zero_iff lam x0 (P x0)).1 hP
  simp [r0MY, OCF.S1.r0, this]

end zero

/-- The ratio of the conditional squared floor to the squared bias at `g = 0`:
`floor_* / bias² = 2m/(3.3124 L) ≤ 0.604`. -/
theorem floor_bias_ratio {m L h T : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h)
    (hT : 0 < T) (hd : 0 < d) :
    (h / m) * (0 ^ 2 + 2 * L * d * T) / (OCF.S1.bias T d m L h) ^ 2 = 2 * m / (3.3124 * L) ∧
      2 * m / (3.3124 * L) ≤ 0.604 := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  have hs : 0 ≤ T * h * d := by positivity
  constructor
  · unfold OCF.S1.bias
    rw [mul_pow, mul_pow, Real.sq_sqrt hs]
    field_simp
    norm_num
  · rw [div_le_iff₀ (by positivity)]
    nlinarith

/-! ## Part D: the lambda = h Moreau–Yosida step (r-sp-lamh) -/

/-- Soft threshold: the prox of `h|·|` on `ℝ`. -/
noncomputable def softThr (h x : ℝ) : ℝ := if h < x then x - h else if x < -h then x + h else 0

/-- Quadratic growth of the prox objective at the soft threshold. -/
lemma softThr_growth {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    h * |softThr h x| + (softThr h x - x) ^ 2 / 2 + (y - softThr h x) ^ 2 / 2 ≤
      h * |y| + (y - x) ^ 2 / 2 := by
  unfold softThr
  split_ifs with h1 h2
  · rw [abs_of_pos (by linarith : 0 < x - h)]
    rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rw [hy] <;> nlinarith [sq_nonneg (y - x + h)]
  · rw [abs_of_neg (by linarith : x + h < 0)]
    rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rw [hy] <;> nlinarith [sq_nonneg (y - x - h)]
  · have hx : |x| ≤ h := abs_le.2 ⟨by linarith, by linarith⟩
    simp only [abs_zero, mul_zero, zero_add]
    rcases abs_cases y with ⟨hy, _⟩ | ⟨hy, _⟩ <;> rw [hy]
    all_goals nlinarith [abs_le.1 hx]

theorem isProx_softThr {h : ℝ} (hh : 0 < h) (x : ℝ) :
    IsProx (fun w => ‖w‖ ^ 2) h Set.univ (fun y => |y|) x (softThr h x) := by
  refine ⟨Set.mem_univ _, fun y _ => ?_⟩
  have := softThr_growth hh x y
  simp only [Real.norm_eq_abs, sq_abs]
  nlinarith [sq_nonneg (y - softThr h x)]

theorem prox_abs_eq {h : ℝ} (hh : 0 < h) (P : ℝ → ℝ)
    (hP : ∀ x, IsProx (fun w => ‖w‖ ^ 2) h Set.univ (fun y => |y|) x (P x)) (x : ℝ) :
    P x = softThr h x := by
  have h1 := (hP x).2 (softThr h x) (Set.mem_univ _)
  have h2 := softThr_growth hh x (P x)
  simp only [Real.norm_eq_abs, sq_abs] at h1
  have : (P x - softThr h x) ^ 2 ≤ 0 := by nlinarith
  have := pow_eq_zero_iff (two_ne_zero) |>.1 (le_antisymm this (sq_nonneg _))
  linarith

lemma deriv_half_sq (x : ℝ) : deriv (fun x : ℝ => x ^ 2 / 2) x = x := by
  rw [((hasDerivAt_pow 2 x).div_const 2).deriv]; push_cast; ring

/-- r-sp-lamh (a): for `lam = h` the Moreau–Yosida step is `x ↦ prox_{hg}(x) − h ∇F(x)`. -/
theorem myStep_lamh {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {h : ℝ} (hh : h ≠ 0)
    (G P : X → X) (x : X) : myStep h h G P x = P x - h • G x := by
  unfold myStep
  rw [div_self hh, one_smul]; abel

/-- r-sp-lamh (a), admissibility: `h ≤ 2/(m + L + 1/h)` iff `h (m+L) + 1 ≤ 2`. -/
theorem lamh_admissible {m L h : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h) :
    h ≤ 2 / (m + (L + 1 / h)) ↔ h * (m + L) + 1 ≤ 2 := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hpos : 0 < m + (L + 1 / h) := by positivity
  rw [le_div_iff₀ hpos]
  have : h * (m + (L + 1 / h)) = h * (m + L) + 1 := by field_simp; ring
  rw [this]

/-- r-sp-lamh (b): `d = 1`, `F = x²/2` (`∇F = deriv`), `g = |·|`, `h = λ = 1/2`, `x = 4/5`.
The Moreau–Yosida step, `P ∘ D` and `D ∘ P` give `−1/10`, `0` and `3/20`; any prox letter `P` of
`(1/2)|·|` is allowed (it is unique, `prox_abs_eq`). -/
theorem r_sp_lamh_example (P : ℝ → ℝ)
    (hP : ∀ x, IsProx (fun w => ‖w‖ ^ 2) (1/2) Set.univ (fun y => |y|) x (P x)) :
    myStep (1/2) (1/2) (deriv (fun x : ℝ => x ^ 2 / 2)) P (4/5) = -1/10 ∧
    P (dS (1/2) (deriv (fun x : ℝ => x ^ 2 / 2)) (4/5)) = 0 ∧
    dS (1/2) (deriv (fun x : ℝ => x ^ 2 / 2)) (P (4/5)) = 3/20 := by
  have hh : (0:ℝ) < 1/2 := by norm_num
  have hs := prox_abs_eq hh P hP
  have hd : ∀ x, dS (1/2) (deriv (fun x : ℝ => x ^ 2 / 2)) x = x / 2 := by
    intro x; simp only [dS, deriv_half_sq, smul_eq_mul]; ring
  refine ⟨?_, ?_, ?_⟩
  · rw [myStep_lamh (by norm_num), hs]; simp only [smul_eq_mul, deriv_half_sq, softThr]; norm_num
  · rw [hd, hs]; simp only [softThr]; norm_num
  · rw [hs, hd]; simp only [softThr]; norm_num

/-- The bias coefficient of the `λ = h` instance, `(L + 1/h)/m · √(T h d)`. -/
noncomputable def biasCoeff (m L T h : ℝ) (d : ℕ) : ℝ := (L + 1 / h) / m * Real.sqrt (T * h * d)

/-- `ψ h = (1 + L h)/√h`, so that `biasCoeff = (√(T d)/m) ψ h`. -/
noncomputable def psi (L h : ℝ) : ℝ := (1 + L * h) / Real.sqrt h

lemma biasCoeff_eq {m L T h : ℝ} {d : ℕ} (hh : 0 < h) (hT : 0 ≤ T) :
    biasCoeff m L T h d = Real.sqrt (T * d) / m * psi L h := by
  have hd : (0:ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨s, hs, rfl⟩ : ∃ s : ℝ, 0 < s ∧ h = s ^ 2 := ⟨Real.sqrt h, Real.sqrt_pos.2 hh,
    (Real.sq_sqrt hh.le).symm⟩
  unfold biasCoeff psi
  have e : Real.sqrt (T * s ^ 2 * d) = Real.sqrt (T * d) * s := by
    rw [show T * s ^ 2 * d = (T * d) * s ^ 2 by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hs.le]
  rw [e, Real.sqrt_sq hs.le]
  field_simp
  ring

lemma psi_antitone {m L h1 h2 : ℝ} (hm : 0 < m) (hmL : m ≤ L) (h1p : 0 < h1) (h12 : h1 ≤ h2)
    (h2le : h2 ≤ 1 / (m + L)) : psi L h2 ≤ psi L h1 := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have h2p : 0 < h2 := lt_of_lt_of_le h1p h12
  set a := Real.sqrt h1 with ha
  set b := Real.sqrt h2 with hb
  have hap : 0 < a := Real.sqrt_pos.2 h1p
  have hbp : 0 < b := Real.sqrt_pos.2 h2p
  have hab : a ≤ b := Real.sqrt_le_sqrt h12
  have e1 : h1 = a ^ 2 := (Real.sq_sqrt h1p.le).symm
  have e2 : h2 = b ^ 2 := (Real.sq_sqrt h2p.le).symm
  have hLb : L * b ^ 2 < 1 := by
    rw [← e2]
    have : h2 * (m + L) ≤ 1 := by rwa [le_div_iff₀ (by linarith)] at h2le
    nlinarith
  unfold psi
  rw [← ha, ← hb, e1, e2, div_le_div_iff₀ hbp hap]
  have : a * b * L ≤ L * b ^ 2 := by
    nlinarith [mul_nonneg (mul_nonneg hL.le hbp.le) (sub_nonneg.2 hab)]
  nlinarith [mul_pos hap hbp, mul_nonneg (sub_nonneg.2 hab) (sub_nonneg.2 (le_of_lt (lt_of_le_of_lt this hLb)))]

/-- r-sp-lamh (c): on `(0, 1/(m+L)]` the bias coefficient is decreasing in `h`, and at least its
value at the right end, `(m+2L)√(T d)/(m √(m+L))`; the end value is attained. -/
theorem r_sp_lamh_bias {m L T : ℝ} {d : ℕ} (hm : 0 < m) (hmL : m ≤ L) (hT : 0 < T) :
    (∀ h1 h2, 0 < h1 → h1 ≤ h2 → h2 ≤ 1 / (m + L) →
      biasCoeff m L T h2 d ≤ biasCoeff m L T h1 d) ∧
    (∀ h, 0 < h → h ≤ 1 / (m + L) →
      (m + 2 * L) * Real.sqrt (T * d) / (m * Real.sqrt (m + L)) ≤ biasCoeff m L T h d) ∧
    biasCoeff m L T (1 / (m + L)) d = (m + 2 * L) * Real.sqrt (T * d) / (m * Real.sqrt (m + L)) := by
  have hL : 0 < L := lt_of_lt_of_le hm hmL
  have hs : 0 < m + L := by linarith
  have hc : 0 ≤ Real.sqrt (T * d) / m := by positivity
  have hend : biasCoeff m L T (1 / (m + L)) d =
      (m + 2 * L) * Real.sqrt (T * d) / (m * Real.sqrt (m + L)) := by
    rw [biasCoeff_eq (by positivity) hT.le]
    unfold psi
    have hsq : Real.sqrt (1 / (m + L)) = 1 / Real.sqrt (m + L) := by
      rw [Real.sqrt_div' _ hs.le]; simp
    have hsp : 0 < Real.sqrt (m + L) := Real.sqrt_pos.2 hs
    have hsq2 : Real.sqrt (m + L) * Real.sqrt (m + L) = m + L := Real.mul_self_sqrt hs.le
    rw [hsq]
    field_simp
    simp only [Real.sq_sqrt hs.le]
    ring
  refine ⟨?_, ?_, hend⟩
  · intro h1 h2 h1p h12 h2le
    have h2p : 0 < h2 := lt_of_lt_of_le h1p h12
    rw [biasCoeff_eq h1p hT.le, biasCoeff_eq h2p hT.le]
    exact mul_le_mul_of_nonneg_left (psi_antitone hm hmL h1p h12 h2le) hc
  · intro h hp hle
    rw [← hend, biasCoeff_eq hp hT.le, biasCoeff_eq (by positivity) hT.le]
    exact mul_le_mul_of_nonneg_left (psi_antitone hm hmL hp hle le_rfl) hc

/-- r-sp-lamh (c), the dossier witness `m = 1, L = 3, T = d = 1`: minimum `7/2`, and `403/20` at
`h = 1/(100 (m+L)) = 1/400`. -/
theorem r_sp_lamh_witness :
    biasCoeff 1 3 1 (1 / (1 + 3)) 1 = 7 / 2 ∧ biasCoeff 1 3 1 (1 / 400) 1 = 403 / 20 := by
  have h1 : Real.sqrt (1 * (1 / (1 + 3)) * ((1:ℕ):ℝ)) = 1 / 2 := by
    rw [show (1:ℝ) * (1 / (1 + 3)) * ((1:ℕ):ℝ) = (1/2)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h2 : Real.sqrt (1 * (1 / 400) * ((1:ℕ):ℝ)) = 1 / 20 := by
    rw [show (1:ℝ) * (1 / 400) * ((1:ℕ):ℝ) = (1/20)^2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  constructor
  · unfold biasCoeff; rw [h1]; norm_num
  · unfold biasCoeff; rw [h2]; norm_num

/-! ## Part E: the six orders on the 1-D quadratic (r-sp-order) -/

noncomputable section orders

/-- The six orders. -/
inductive Ord6 | DNP | DPN | NDP | NPD | PDN | PND

/-- `P`: the prox letter of `h g`, `g = (sg/2) x²`, on `ℝ`: `x ↦ x/(1 + h sg)`. -/
def lP (sg h x : ℝ) : ℝ := x / (1 + h * sg)

/-- The six words on `F = (κ/2) x²`, `g = (sg/2) x²` (so `∇F x = κ x`), `(x, z) ↦ ω(x; z)`. -/
def word (κ sg h : ℝ) : Ord6 → ℝ → ℝ → ℝ
  | .DNP => wDNP h (fun x => κ * x) (lP sg h)
  | .DPN => wDPN h (fun x => κ * x) (lP sg h)
  | .NDP => wNDP h (fun x => κ * x) (lP sg h)
  | .NPD => wNPD h (fun x => κ * x) (lP sg h)
  | .PDN => wPDN h (fun x => κ * x) (lP sg h)
  | .PND => wPND h (fun x => κ * x) (lP sg h)

/-- `c_ω`: the product of the letter factors applied after `N`
(`u = 1/(1 + h sg)`, `a_D = 1 − h κ`, `ρ = a_D u`; the dossier's names after the B4 renames). -/
def cOf (κ sg h : ℝ) : Ord6 → ℝ
  | .DNP => 1 / (1 + h * sg)
  | .DPN => 1
  | .PDN => 1
  | .PND => 1 - h * κ
  | .NDP => rho κ h sg
  | .NPD => rho κ h sg

lemma deriv_quad (κ x : ℝ) : deriv (fun x : ℝ => κ / 2 * x ^ 2) x = κ * x := by
  rw [((hasDerivAt_pow 2 x).const_mul (κ / 2)).deriv]; push_cast; ring

/-- `lP` is the prox letter of `h g`, `g = (sg/2) x²`. -/
theorem isProx_lP {sg h : ℝ} (hh : 0 ≤ h) (hsg : 0 ≤ sg) (x : ℝ) :
    IsProx (fun w => ‖w‖ ^ 2) h Set.univ (fun y => sg / 2 * y ^ 2) x (lP sg h x) := by
  refine ⟨Set.mem_univ _, fun y _ => ?_⟩
  have hA : 0 < 1 + h * sg := by positivity
  simp only [Real.norm_eq_abs, sq_abs, lP]
  have : h * (sg / 2 * y ^ 2) + (y - x) ^ 2 / 2 - (h * (sg / 2 * (x / (1 + h * sg)) ^ 2) +
      (x / (1 + h * sg) - x) ^ 2 / 2) = (1 + h * sg) / 2 * (y - x / (1 + h * sg)) ^ 2 := by
    field_simp; ring
  nlinarith [sq_nonneg (y - x / (1 + h * sg))]

/-- Every order is affine in `(x, z)` with the SAME `x`-coefficient `ρ` (so the six mean maps
coincide) and `z`-coefficient `c_ω`. -/
theorem word_lin (κ sg h : ℝ) (hA : 1 + h * sg ≠ 0) (ω : Ord6) (x z : ℝ) :
    word κ sg h ω x z = rho κ h sg * x + cOf κ sg h ω * z := by
  cases ω <;> simp [word, cOf, rho, wDNP, wDPN, wNDP, wNPD, wPDN, wPND, dS, nS, lP] <;>
    field_simp

/-- Stationary variance of the Gaussian chain `x ↦ ρ x + c_ω z`, `z ~ N(0, 2 T h)`
([CLASSICAL K17], Meyn–Tweedie sec. 10.5.4): `v_ω = c_ω² 2 T h/(1 − ρ²)`; it is the unique fixed point
of the variance map `v ↦ ρ² v + c_ω² (2 T h)` when `ρ² < 1`. -/
def statVar (T h κ sg : ℝ) (ω : Ord6) : ℝ :=
  (cOf κ sg h ω) ^ 2 * (2 * T * h) / (1 - rho κ h sg ^ 2)

theorem statVar_fixed {T h κ sg : ℝ} (hρ : rho κ h sg ^ 2 < 1) (ω : Ord6) (v : ℝ) :
    v = rho κ h sg ^ 2 * v + (cOf κ sg h ω) ^ 2 * (2 * T * h) ↔ v = statVar T h κ sg ω := by
  have h1 : 1 - rho κ h sg ^ 2 ≠ 0 := by linarith
  unfold statVar
  rw [eq_div_iff h1]
  constructor <;> intro H <;> linarith

lemma one_sub_rho_sq {κ sg h : ℝ} (hA : 1 + h * sg ≠ 0) :
    1 - rho κ h sg ^ 2 = h * (κ + sg) * (2 + h * (sg - κ)) / (1 + h * sg) ^ 2 := by
  unfold rho; field_simp; ring

/-- The class for the order remark: `m = L = κ`, so `0 < h ≤ 1/κ`. -/
structure InClass (κ sg h T : ℝ) : Prop where
  hκ : 0 < κ
  hh : 0 < h
  hhκ : h * κ ≤ 1
  hsg : 0 ≤ sg
  hT : 0 < T

theorem InClass.rho_sq_lt {κ sg h T : ℝ} (H : InClass κ sg h T) : rho κ h sg ^ 2 < 1 := by
  have hk := H.hhκ
  have h1 := r_sp_factor_arith (m := κ) (L := κ) H.hκ le_rfl H.hh (by
    rw [le_div_iff₀ (by linarith [H.hκ])]; nlinarith [H.hκ, H.hh]) H.hsg
  nlinarith [h1.1, h1.2.1]

/-- Gibbs variance `T/(κ + sg)` (the Gibbs law of `(F + g)/T` is `N(0, T/(κ + sg))`). -/
def gibbsVar (T κ sg : ℝ) : ℝ := T / (κ + sg)

/-- Common exactness criterion: `v_ω = T/(κ+sg)` iff `2 (c_ω (1 + h sg))² = 2 + h (sg − κ)`. -/
theorem exact_iff {κ sg h T : ℝ} (H : InClass κ sg h T) (ω : Ord6) :
    statVar T h κ sg ω = gibbsVar T κ sg ↔
      2 * (cOf κ sg h ω * (1 + h * sg)) ^ 2 = 2 + h * (sg - κ) := by
  have hA : 0 < 1 + h * sg := by have := H.hh; have := H.hsg; positivity
  have hks : 0 < κ + sg := by have := H.hκ; have := H.hsg; linarith
  have hW : 0 < 2 + h * (sg - κ) := by nlinarith [H.hhκ, H.hh, H.hsg]
  have hhk : 0 < h * (κ + sg) := mul_pos H.hh hks
  have hh0 : h ≠ 0 := H.hh.ne'
  have key : statVar T h κ sg ω = T / (κ + sg) * (2 * (cOf κ sg h ω * (1 + h * sg)) ^ 2 /
      (2 + h * (sg - κ))) := by
    unfold statVar
    rw [one_sub_rho_sq hA.ne']
    field_simp
  rw [key]
  unfold gibbsVar
  have hg : T / (κ + sg) ≠ 0 := (div_pos H.hT hks).ne'
  constructor
  · intro E
    have E1 := mul_left_cancel₀ hg (E.trans (mul_one _).symm)
    rw [div_eq_one_iff_eq hW.ne'] at E1
    exact E1
  · intro E
    rw [E, div_self hW.ne', mul_one]

end orders

noncomputable section orders2

/-- DNP is Gibbs-exact exactly when `κ = sg`, for every admissible `h`. -/
theorem exact_DNP {κ sg h T : ℝ} (H : InClass κ sg h T) :
    statVar T h κ sg .DNP = gibbsVar T κ sg ↔ κ = sg := by
  have hA : 0 < 1 + h * sg := by have := H.hh; have := H.hsg; positivity
  rw [exact_iff H]
  have : cOf κ sg h .DNP * (1 + h * sg) = 1 := by simp [cOf]; field_simp
  rw [this]
  constructor
  · intro E
    have : h * (sg - κ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 H.hh.ne'
    · linarith
  · intro E; rw [← E]; ring

/-- DPN and PDN are never Gibbs-exact. -/
theorem exact_DPN_never {κ sg h T : ℝ} (H : InClass κ sg h T) :
    ¬ statVar T h κ sg .DPN = gibbsVar T κ sg := by
  rw [exact_iff H]
  have := H.hh; have := H.hκ; have := H.hsg
  simp only [cOf, one_mul]
  intro E
  have : h * (κ + 3 * sg + 2 * h * sg ^ 2) = 0 := by nlinarith
  have hpos : 0 < h * (κ + 3 * sg + 2 * h * sg ^ 2) := by positivity
  linarith

theorem exact_PDN_never {κ sg h T : ℝ} (H : InClass κ sg h T) :
    ¬ statVar T h κ sg .PDN = gibbsVar T κ sg := by
  have := exact_DPN_never H
  unfold statVar gibbsVar at *
  simpa [cOf] using this

/-- NDP and NPD are Gibbs-exact only at `h = (3κ + sg)/(2κ²)`, and that step is outside the class
(`h κ ≥ 3/2 > 1`). -/
theorem exact_NDP_iff {κ sg h T : ℝ} (H : InClass κ sg h T) :
    statVar T h κ sg .NDP = gibbsVar T κ sg ↔ h = (3 * κ + sg) / (2 * κ ^ 2) := by
  have hA : 0 < 1 + h * sg := by have := H.hh; have := H.hsg; positivity
  have hk := H.hκ
  rw [exact_iff H]
  have : cOf κ sg h .NDP * (1 + h * sg) = 1 - h * κ := by
    simp [cOf, rho]; field_simp
  rw [this, eq_div_iff (by positivity)]
  constructor
  · intro E
    have : h * (h * (2 * κ ^ 2) - (3 * κ + sg)) = 0 := by nlinarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 H.hh.ne'
    · linarith
  · intro E; nlinarith

theorem exact_NDP_outside {κ sg h T : ℝ} (H : InClass κ sg h T) :
    ¬ statVar T h κ sg .NDP = gibbsVar T κ sg := by
  rw [exact_NDP_iff H]
  intro E
  have hk := H.hκ; have hs := H.hsg; have hhk := H.hhκ
  have : h * (2 * κ ^ 2) = 3 * κ + sg := by rw [E]; field_simp
  nlinarith

theorem exact_NPD_iff {κ sg h T : ℝ} (H : InClass κ sg h T) :
    statVar T h κ sg .NPD = gibbsVar T κ sg ↔ h = (3 * κ + sg) / (2 * κ ^ 2) := by
  have := exact_NDP_iff H
  unfold statVar gibbsVar at *
  simpa [cOf] using this

theorem exact_NPD_outside {κ sg h T : ℝ} (H : InClass κ sg h T) :
    ¬ statVar T h κ sg .NPD = gibbsVar T κ sg := by
  have := exact_NDP_outside H
  unfold statVar gibbsVar at *
  simpa [cOf] using this

/-- The NDP/NPD locus lies at `h κ = (3κ + sg)/(2κ) ≥ 3/2 > 1` (equality `3/(2κ)` exactly at `sg = 0`;
strict `>` for `sg > 0`). -/
theorem ndp_locus_ge {κ sg : ℝ} (hκ : 0 < κ) (hsg : 0 ≤ sg) :
    3 / (2 * κ) ≤ (3 * κ + sg) / (2 * κ ^ 2) ∧ 1 / κ < (3 * κ + sg) / (2 * κ ^ 2) ∧
      ((3 * κ + sg) / (2 * κ ^ 2) = 3 / (2 * κ) ↔ sg = 0) := by
  have h2 : 0 < 2 * κ ^ 2 := by positivity
  have h3 : 0 < 2 * κ := by positivity
  have e : 3 / (2 * κ) = 3 * κ / (2 * κ ^ 2) := by field_simp
  have e1 : 1 / κ = 2 * κ / (2 * κ ^ 2) := by field_simp
  rw [e, e1, div_le_div_iff_of_pos_right h2, div_lt_div_iff_of_pos_right h2,
    div_left_inj' h2.ne']
  refine ⟨by linarith, by linarith, ⟨fun H => by linarith, fun H => by rw [H]; ring⟩⟩

/-- PND is Gibbs-exact exactly on the curve `2 ((1 − h κ)(1 + h sg))² = 2 + h (sg − κ)`. -/
theorem exact_PND_iff {κ sg h T : ℝ} (H : InClass κ sg h T) :
    statVar T h κ sg .PND = gibbsVar T κ sg ↔
      2 * ((1 - h * κ) * (1 + h * sg)) ^ 2 = 2 + h * (sg - κ) := by
  rw [exact_iff H]; rfl

/-- SECOND EXACT INSTANCE: `κ = 1, h = 1/4, T = 1, sg = (4√70 − 20)/9` (`≠ κ`, in the class): the word
P, N, D has stationary variance `T/(κ + sg)`. -/
theorem exact_PND_instance :
    InClass 1 ((4 * Real.sqrt 70 - 20) / 9) (1/4) 1 ∧ (4 * Real.sqrt 70 - 20) / 9 ≠ 1 ∧
    statVar 1 (1/4) 1 ((4 * Real.sqrt 70 - 20) / 9) .PND = gibbsVar 1 1 ((4 * Real.sqrt 70 - 20) / 9) := by
  have hs : Real.sqrt 70 ^ 2 = 70 := Real.sq_sqrt (by norm_num)
  have h8 : 8 < Real.sqrt 70 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have hI : InClass 1 ((4 * Real.sqrt 70 - 20) / 9) (1/4) 1 :=
    ⟨by norm_num, by norm_num, by norm_num, by linarith, by norm_num⟩
  refine ⟨hI, ?_, (exact_PND_iff hI).2 ?_⟩
  · intro E; linarith
  · linear_combination (1/72 : ℝ) * hs

/-- Witness values `κ = 1, sg = 1/2, T = 1, h = 1/4`: Gibbs variance `2/3`, and the six stationary
variances `32/45, 9/10, 2/5, 2/5, 9/10, 81/160` (`0.7111, 0.9, 0.4, 0.4, 0.9, 0.50625`). -/
theorem order_witness :
    gibbsVar 1 1 (1/2) = 2/3 ∧
    statVar 1 (1/4) 1 (1/2) .DNP = 32/45 ∧ statVar 1 (1/4) 1 (1/2) .DPN = 9/10 ∧
    statVar 1 (1/4) 1 (1/2) .NDP = 2/5 ∧ statVar 1 (1/4) 1 (1/2) .NPD = 2/5 ∧
    statVar 1 (1/4) 1 (1/2) .PDN = 9/10 ∧ statVar 1 (1/4) 1 (1/2) .PND = 81/160 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [statVar, gibbsVar, cOf, rho]

end orders2

/-! ## Part F: square-root conversion and the count inequalities (r-sp-cond (c), (d); r-sp-own (c)) -/

lemma sqrt_add_le_add_sqrt' {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- r-sp-cond (c): `a² ≤ r^k b² + c` implies `a ≤ r^{k/2} b + √c` (nonnegative reals), with
`r^{k/2} = (√r)^k`. -/
theorem sqrt_conversion {a b c r : ℝ} (k : ℕ) (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hr : 0 ≤ r)
    (H : a ^ 2 ≤ r ^ k * b ^ 2 + c) : a ≤ Real.sqrt r ^ k * b + Real.sqrt c := by
  have h1 : a ≤ Real.sqrt (r ^ k * b ^ 2 + c) := Real.le_sqrt_of_sq_le H
  have h2 := sqrt_add_le_add_sqrt' (x := r ^ k * b ^ 2) (y := c) (by positivity) hc
  have h3 : Real.sqrt (r ^ k * b ^ 2) = Real.sqrt r ^ k * b := by
    have : r ^ k * b ^ 2 = (Real.sqrt r ^ k * b) ^ 2 := by
      rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt hr]
    rw [this, Real.sqrt_sq (by positivity)]
  linarith

/-- The same with the real power `r^{k/2}`. -/
theorem sqrt_conversion_rpow {a b c r : ℝ} (k : ℕ) (_ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hr : 0 ≤ r) (H : a ^ 2 ≤ r ^ k * b ^ 2 + c) : a ≤ r ^ ((k : ℝ) / 2) * b + Real.sqrt c := by
  have e : Real.sqrt r ^ k = r ^ ((k : ℝ) / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hr]; congr 1; ring
  have := sqrt_conversion k _ha hb hc hr H
  rwa [e] at this

/-- `q^k A ≤ B` once `k (1 − q) ≥ log (A/B)` (`0 ≤ q`, `A ≥ 0`, `B > 0`); uses `q ≤ exp(q − 1)`. -/
theorem pow_mul_le_of_log {q A B : ℝ} (k : ℕ) (hq : 0 ≤ q) (hA : 0 ≤ A) (hB : 0 < B)
    (hk : Real.log (A / B) ≤ k * (1 - q)) : q ^ k * A ≤ B := by
  rcases hA.eq_or_lt with rfl | hA
  · simp [hB.le]
  have h1 : q ≤ Real.exp (q - 1) := by linarith [Real.add_one_le_exp (q - 1)]
  have h2 : q ^ k ≤ Real.exp (-(k * (1 - q))) := by
    calc q ^ k ≤ Real.exp (q - 1) ^ k := pow_le_pow_left₀ hq h1 k
      _ = Real.exp (-(k * (1 - q))) := by rw [← Real.exp_nat_mul]; congr 1; ring
  have h3 : Real.exp (-(k * (1 - q))) ≤ B / A := by
    calc Real.exp (-(k * (1 - q))) ≤ Real.exp (-Real.log (A / B)) := Real.exp_le_exp.2 (by linarith)
      _ = B / A := by rw [Real.exp_neg, Real.exp_log (by positivity)]; field_simp
  calc q ^ k * A ≤ B / A * A := mul_le_mul_of_nonneg_right (h2.trans h3) hA.le
    _ = B := by field_simp

/-- `log(1/ρ) ≥ 1 − ρ` for `ρ > 0`. -/
theorem log_inv_ge {ρ : ℝ} (hρ : 0 < ρ) : 1 - ρ ≤ Real.log (1 / ρ) := by
  have := Real.one_sub_inv_le_log_of_pos (x := 1 / ρ) (by positivity)
  simpa using this

/-- r-sp-own (c): in the class (`0 < m ≤ L`, `0 < h ≤ 2/(m+L)`, `sg ≥ 0`), if
`k ≥ ⌈((1 + h sg)/(h (m + sg))) log (D̄/((1 − ρ) ε))⌉₊` then `ρ^k D̄/(1 − ρ) ≤ ε`
(`D̄ ≥ 0`, `ε > 0`; this bounds `K_ε ≤ max{0, ⌈…⌉}`). -/
theorem r_sp_own_count {m L h sg D ε : ℝ} (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h)
    (hhL : h ≤ 2 / (m + L)) (hsg : 0 ≤ sg) (hD : 0 ≤ D) (hε : 0 < ε) (k : ℕ)
    (hk : ⌈(1 + h * sg) / (h * (m + sg)) * Real.log (D / ((1 - rho m h sg) * ε))⌉₊ ≤ k) :
    rho m h sg ^ k * (D / (1 - rho m h sg)) ≤ ε := by
  obtain ⟨h0, h1, h2, -⟩ := r_sp_factor_arith hm hmL hh hhL hsg
  have hpos : 0 < 1 - rho m h sg := by linarith
  have hA : 0 < 1 + h * sg := by positivity
  have hms : 0 < h * (m + sg) := by positivity
  apply pow_mul_le_of_log k h0 (by positivity) hε
  have hk' := (Nat.ceil_le.1 hk)
  have e : 1 / (1 - rho m h sg) = (1 + h * sg) / (h * (m + sg)) := by
    rw [h2]; field_simp
  have hk2 : Real.log (D / ((1 - rho m h sg) * ε)) ≤ k * (1 - rho m h sg) := by
    rw [← e, one_div, ← div_eq_inv_mul, div_le_iff₀ hpos] at hk'
    exact hk'
  rwa [div_div]

/-- r-sp-cond (d): `q = 1 − h m ∈ [0, 1)`, `ε² > floor`: every `K ≥ ⌈log(r₀²/(ε² − floor))/(h m)⌉₊`
turns `a² ≤ q^K r₀² + floor` into `a ≤ ε`. -/
theorem r_sp_cond_count {a r0 flr ε h m : ℝ} (hhm : 0 < h * m) (hq : 0 ≤ 1 - h * m) (ha : 0 ≤ a)
    (hε : 0 < ε) (hf : flr < ε ^ 2) (K : ℕ)
    (hK : ⌈Real.log (r0 ^ 2 / (ε ^ 2 - flr)) / (h * m)⌉₊ ≤ K)
    (H : a ^ 2 ≤ (1 - h * m) ^ K * r0 ^ 2 + flr) : a ≤ ε := by
  have hk := Nat.ceil_le.1 hK
  have hk2 : Real.log (r0 ^ 2 / (ε ^ 2 - flr)) ≤ K * (1 - (1 - h * m)) := by
    rw [div_le_iff₀ hhm] at hk; linarith
  have := pow_mul_le_of_log K hq (sq_nonneg r0) (by linarith : 0 < ε ^ 2 - flr) hk2
  nlinarith

/-! ## Part G: the frame identity (r-sp-frame), the pure-algebra part -/

noncomputable section frame
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- `E^{[c]}(x) = c⁻¹ E(c x)`. -/
def scaleE (c : ℝ) (E : X → ℝ) (x : X) : ℝ := c⁻¹ * E (c • x)

/-- `c E^{[c]}(x) = E(c x)`. -/
theorem frame_energy {c : ℝ} (hc : c ≠ 0) (E : X → ℝ) (x : X) : c * scaleE c E x = E (c • x) := by
  unfold scaleE; field_simp

/-- The Gibbs exponent: `E^{[c]}(x)/(T/c) = E(c x)/T`, so `exp(−E^{[c]}/(T/c)) = exp(−E(c x)/T)`. -/
theorem frame_gibbs {c T : ℝ} (hc : c ≠ 0) (hT : T ≠ 0) (E : X → ℝ) (x : X) :
    scaleE c E x / (T / c) = E (c • x) / T := by
  unfold scaleE; field_simp

/-- The carried prox attribute: `p = P_g(c α, c x)` gives `p/c = prox_{α g^{[c]}}(x)`. -/
theorem frame_prox_iff {c : ℝ} (hc : 0 < c) (α : ℝ) (g : X → ℝ) (x p : X) :
    IsProx (fun w => ‖w‖ ^ 2) α Set.univ (scaleE c g) x p ↔
      IsProx (fun w => ‖w‖ ^ 2) (c * α) Set.univ g (c • x) (c • p) := by
  have hc0 : c ≠ 0 := hc.ne'
  have nrm : ∀ u v : X, ‖c • u - c • v‖ ^ 2 = c ^ 2 * ‖u - v‖ ^ 2 := by
    intro u v
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have hc2 : 0 < c ^ 2 := by positivity
  constructor
  · rintro ⟨-, H⟩
    refine ⟨Set.mem_univ _, fun y' _ => ?_⟩
    have H1 := H (c⁻¹ • y') (Set.mem_univ _)
    have e : c • c⁻¹ • y' = y' := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
    have n1 := nrm p x
    have n2 := nrm (c⁻¹ • y') x
    rw [e] at n2
    unfold scaleE at H1
    simp only [e] at H1
    simp only [] at H1 ⊢
    rw [n1, n2]
    have key : ∀ (G1 G2 a1 a2 : ℝ), α * (c⁻¹ * G1) + a1 / 2 ≤ α * (c⁻¹ * G2) + a2 / 2 →
        c * α * G1 + c ^ 2 * a1 / 2 ≤ c * α * G2 + c ^ 2 * a2 / 2 := by
      intro G1 G2 a1 a2 H
      have := mul_le_mul_of_nonneg_left H hc2.le
      have e1 : c ^ 2 * (α * (c⁻¹ * G1) + a1 / 2) = c * α * G1 + c ^ 2 * a1 / 2 := by
        field_simp
      have e2 : c ^ 2 * (α * (c⁻¹ * G2) + a2 / 2) = c * α * G2 + c ^ 2 * a2 / 2 := by
        field_simp
      linarith
    exact key _ _ _ _ H1
  · rintro ⟨-, H⟩
    refine ⟨Set.mem_univ _, fun y _ => ?_⟩
    have H1 := H (c • y) (Set.mem_univ _)
    have n1 := nrm p x
    have n2 := nrm y x
    unfold scaleE
    simp only [] at H1 ⊢
    rw [n1, n2] at H1
    have e1 : c ^ 2 * (α * (c⁻¹ * g (c • p)) + ‖p - x‖ ^ 2 / 2) =
        c * α * g (c • p) + c ^ 2 * ‖p - x‖ ^ 2 / 2 := by field_simp
    have e2 : c ^ 2 * (α * (c⁻¹ * g (c • y)) + ‖y - x‖ ^ 2 / 2) =
        c * α * g (c • y) + c ^ 2 * ‖y - x‖ ^ 2 / 2 := by field_simp
    have : c ^ 2 * (α * (c⁻¹ * g (c • p)) + ‖p - x‖ ^ 2 / 2) ≤
        c ^ 2 * (α * (c⁻¹ * g (c • y)) + ‖y - x‖ ^ 2 / 2) := by
      rw [e1, e2]; linarith
    exact le_of_mul_le_mul_left this hc2

/-- Conjugated pair, curvature and factor: `(c m, c L)`, `c sg`; the step range is that of the converted
pair, and `ρ^{[c]} = (1 − c m h)/(1 + c h sg)` is in `[0,1)` there. -/
theorem frame_factor {c m L h sg : ℝ} (hc : 0 < c) (hm : 0 < m) (hmL : m ≤ L) (hh : 0 < h)
    (hhL : h ≤ 2 / (c * (m + L))) (hsg : 0 ≤ sg) :
    rho (c * m) h (c * sg) = (1 - c * m * h) / (1 + c * h * sg) ∧
    0 ≤ rho (c * m) h (c * sg) ∧ rho (c * m) h (c * sg) < 1 ∧
    rho (c * m) h (c * sg) = lipD (c * m) (c * L) h / (1 + h * (c * sg)) := by
  have hr : h ≤ 2 / (c * m + c * L) := by rwa [← mul_add]
  obtain ⟨h0, h1, -, h3⟩ := r_sp_factor_arith (mul_pos hc hm) (by nlinarith) hh hr
    (mul_nonneg hc.le hsg)
  refine ⟨?_, h0, h1, h3⟩
  unfold rho; ring

end frame

#print axioms OCF.RSP.r_sp_factor_arith
#print axioms OCF.RSP.lipD_eq
#print axioms OCF.RSP.step_formula_fails
#print axioms OCF.RSP.hL_gt_iff
#print axioms OCF.RSP.step_formula_boundary
#print axioms OCF.RSP.quad_family_sup
#print axioms OCF.RSP.ratioSet_greatest
#print axioms OCF.RSP.step_counterexample
#print axioms OCF.RSP.step_formula_negative_mL
#print axioms OCF.RSP.isProx_zero_iff
#print axioms OCF.RSP.r_sp_zero_kernel
#print axioms OCF.RSP.r_sp_zero_constants
#print axioms OCF.RSP.r_sp_zero_r0
#print axioms OCF.RSP.floor_bias_ratio
#print axioms OCF.RSP.myStep_lamh
#print axioms OCF.RSP.lamh_admissible
#print axioms OCF.RSP.r_sp_lamh_example
#print axioms OCF.RSP.r_sp_lamh_bias
#print axioms OCF.RSP.r_sp_lamh_witness
#print axioms OCF.RSP.isProx_softThr
#print axioms OCF.RSP.prox_abs_eq
#print axioms OCF.RSP.isProx_lP
#print axioms OCF.RSP.word_lin
#print axioms OCF.RSP.statVar_fixed
#print axioms OCF.RSP.exact_iff
#print axioms OCF.RSP.exact_DNP
#print axioms OCF.RSP.exact_DPN_never
#print axioms OCF.RSP.exact_PDN_never
#print axioms OCF.RSP.exact_NDP_iff
#print axioms OCF.RSP.exact_NPD_iff
#print axioms OCF.RSP.exact_NDP_outside
#print axioms OCF.RSP.exact_NPD_outside
#print axioms OCF.RSP.ndp_locus_ge
#print axioms OCF.RSP.exact_PND_iff
#print axioms OCF.RSP.exact_PND_instance
#print axioms OCF.RSP.order_witness
#print axioms OCF.RSP.sqrt_conversion
#print axioms OCF.RSP.sqrt_conversion_rpow
#print axioms OCF.RSP.pow_mul_le_of_log
#print axioms OCF.RSP.log_inv_ge
#print axioms OCF.RSP.r_sp_own_count
#print axioms OCF.RSP.r_sp_cond_count
#print axioms OCF.RSP.frame_energy
#print axioms OCF.RSP.frame_gibbs
#print axioms OCF.RSP.frame_prox_iff
#print axioms OCF.RSP.frame_factor

end OCF.RSP

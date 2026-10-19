/-
R110 pipeline: one step of the Rule 110 automaton as three certified stages (clamp
products), the exact minimiser table of the single summed energy, what that minimiser
reads out to, the certified threshold-1/4 read-out, and the arithmetic of the declared
curvature pair.

Source of truth: project_plan/doing/proof_audits/R110_pipeline/01_derivation.md
(items R1, R4 to R12; section 10 "Lean targets"), adjudication 03_adjudication.md and
re-audit 02b_reaudit_R110.md. sha16 (sha256, first 16 hex) of 01_derivation.md when
formalised: e64d550fa222c0b1.

DEFINITIONAL MAP (dossier symbol, Lean name):
* ring of n cells, indices mod n (including n = 1, 2) : `Fin n` with `[NeZero n]`,
  `i - 1`, `i + 1` cyclic; binary row : `IsBin x` (every x i is 0 or 1).
* clamp (prox of the box [0,1]) : `clamp`; Cook polynomial c + r - c r - l c r :
  `poly110`; the next row t(x) : `rule110 x`; Cook's table : `cookF`.
* l_i = x_{i-1}, s_i = x_i + x_{i+1} : `lVec x`, `sVec x`.
* read-out rd_tau (ties up: u_i >= tau gives 1) : `rdT tau`; rd_tau = C6 `rd` after the
  shift u - tau : `rdT_eq_C6`; margin min_i |y_i - tau| : `marg tau y`.
* stage energy E_{a,C}, update U(v) = P_C(gamma v + alpha a), gamma = 1 - alpha,
  residual R_alpha = (v - U v)/alpha : `stageEnergy`, `stageU`, `stageR`;
  iterates `stageIter`, fixed point `stageStar`; C = [0,1]^n or R^n by `Bool` (`projC`).
* pipeline data a^P, a^Q, a^Y and stage minimisers : `aP`, `aQ`, `aY`, `phat`, `qhat`,
  `yhat`; acceptance at rho_k < 1/2 : `Accepted`.
* closed-form counts : `stopCount`, `Kbound`; indicator and counting helpers `ind1`,
  `cnt1`, `mY`, `mP`, `mQ`.
* summed energy E_x^w, weights w = (w1, w2, w3) all positive : `Ejoint w1 w2 w3 x p q y`;
  theta = w1/(w1+w2) : `theta`; per-cell energy : `cellE`; cell minimisers :
  `pTab`, `qTab`, `yTab`; the minimiser z° = (p°, q°, y°) : `pMin`, `qMin`, `yMin`.
* bad cell (l = 0 and s = 1) : `Bad x i`; unit-weight cell values : `phi`.
* declaration gradients, forward-backward residual R_alpha(z) on R^{3n} :
  `gradP`, `gradQ`, `gradY`, `resP`, `resQ`, `resY`, `resNorm`; product norm `eN3`.
* Hessian H_w = M^T diag(w) M : `Hw`, `Mmat`; unit weights `Hunit`; characteristic cubic
  pi(lambda) = lambda^3 - 6 lambda^2 + 9 lambda - 1 : `cubic`; declared pair
  (beta, sigma) = (18/5, 3/25) valid for A : `ValidPair A beta sigma`.

COVERAGE (target, Lean name):
1. R1 clamp gadget: `clamp_and`, `clamp_and'`, `clamp_and_fails` (the non-binary
   counterexample), `rule110_poly_table`, `rule110_bin`.
2. R4 certified read-out at any threshold, any l_p : `readout_threshold`,
   `readout_threshold_eN`, `rdT_eq_of_abs_lt` (derived from C6 `rd_stable_lp`).
3. R3, elementary coordinatewise parts only (the cited theorem itself is classical and is
   NOT formalised): `stageU_lip`, `stageU_star`, `stage_distance`, `resid_contr`,
   `resid_norm_iter_le`, `stage_exists_accepted`, `stage_unique_min`, `stage_report`.
4. R5 pipeline exactness: `pipeline_minimisers`, `pipeline_step_exact`,
   `pipeline_exists_accepted`.
5. R6 exact closed forms of iterates and residuals and the stopping counts:
   `boxStage_iter_closed`, `boxStage_resid_closed`, `yStage_iter_closed`,
   `yStage_resid_closed`, `count_isLeast`, `boxStage_stop`, `yStage_stop`,
   `pipeline_exact_counts`, `stopCount_le_Kbound`, `stage_count_bound`.
6. R7 k-step composition (N steps, each exactly the rule): `pipeline_N_steps`.
7. R9 exact minimiser table of the summed energy for all positive weights:
   `Ejoint_eq_sum_cell`, `cell_min`, `joint_cell_table` (the cell table),
   `R9_i` to `R9_v` (theta-dependent table with max 0 (1 - 2 theta), uniqueness, bad
   cells, unit-weight values and cell energies).
8. R10 the three exact-arithmetic witnesses (n = 5 minimiser with sup-distance 1/2 to the
   next row; n = 3 cascade point not block-stationary; n = 1 with min E = 1 > 0):
   `R10_i`, `R10_ii`, `R10_iii`.
9. R11 what the minimiser reads out to, one clause per theorem (wording of the second pass):
   (a) `R11_a`; (b) `R11_b`;
   (c) separated cases: `w1 > w2` `R11_c_gt`; `w1 = w2` `R11_c_eq` (margin 0) with
   `R11_c_eq_readout` (ties-up read-out still equals t(x)); `w1 < w2` `R11_c_lt` (every bad
   cell misread); the "iff w1 > w2" quantifier `R11_c_iff` (uses `bad_row_exists`, n >= 2);
   (d) `R11_d`, with the corrected equality statement (margin exactly 1/4 at every w1 >= w2 on
   rows with a cell of type (1,0),(1,2),(0,0)) `R11_d_margin_eq` (cells `ZeroCell`);
   (e) `R11_e`; (f) `R11_f` (threshold theta/2 for every positive weighting, margin >= theta/2,
   every l_p ball and the Euclidean ball) and `R11_f_thresholds` (admissible thresholds on
   every row of every length are exactly (0, theta]).
10. R12 (ii) certified threshold-1/4 read-out given the distance bound `JointSound`:
   `joint_readout_quarter`, `joint_readout_quarter_sq`, `joint_readout_quarter_unit`;
   (iv) N-step composition : `joint_N_steps`.
11. R8 arithmetic: (a), (b) `Mmat`, `det_Mmat`, `Hw_explicit`, `Hw_unit`, `qf_Hw`,
   `Hw_posdef`, `grad_inner_eq`; (c) `charpoly_Hunit`, `Hunit_invariants`, `cubic_values`,
   `cubic_roots` (three real roots with 3/25 < r1 < 121/1000 and r3 < 18/5, by the
   intermediate value theorem), `cubic_root_cases` (completeness by Vieta),
   `eigenvector_of_root`, `rayleigh_of_root`, `lambda_brackets` (the Rayleigh infimum and
   supremum of H lie in the same brackets as the smallest and largest root);
   (e) `Hunit_lower` (241/2000), `Hunit_upper` (71/20), `declared_pair_valid`
   ((18/5, 3/25) valid), `Hw_upper` (upper half for all positive w), `unit_grad_strong_mono`
   (the curvature inequality for the concrete declaration gradient at unit weights).

HYPOTHESES (named, not proved here):
* `JointSound` : the distance bound of thm:soundness(c) for the declaration D_x^w,
  ‖z - z°‖ <= ‖R_alpha(z)‖/sigma, with z° the R9 minimiser. Used by `joint_readout_quarter`,
  `joint_readout_quarter_sq`, `joint_N_steps` (the last for every binary row). The theorem
  it comes from is `G3SoundnessProx.regimeAP_of` in an abstract space; it was not
  instantiated on R^{3n}. Its premise (a valid pair) is proved only at unit weights
  (`declared_pair_valid`, `unit_grad_strong_mono`).
* Exact real arithmetic (Lean's real numbers), step alpha in (0,1], binary rows.
* Acceptance: stage residual below 1/2 (pipeline) or ‖R‖ < sigma/4 (single energy), with
  alpha = 1/beta, beta, sigma > 0; w1 >= w2 > 0, w3 > 0 where R12 and R9(i) say so.
* Start point p0 = q0 = 0, y0 = x in R6 (the dossier's H-START).

NOT FORMALISED (and why):
* R2 typing and the scope prose, R12(i) typing, Remark R12.3 and R13: prose-only by instruction
  (R12.3 follows from `R11_f` by the proof of `joint_readout_quarter`; not stated here).
* R3 as a cited theorem: classical (forward-backward on a strongly convex smooth sum).
* R8(d) strong convexity and Gamma_0 membership of the stage and summed energies.
* R8(e), lower curvature half for general w (sigma-hat = 4 w1 w2 w3/(tr)^2): only the
  upper half (`Hw_upper`) and the unit-weight pair are proved.
* Identification of lambda_min(H) and lambda_max(H) with the individual roots r1, r3:
  proved only that the Rayleigh infimum and supremum lie in the same brackets as r1, r3
  (`lambda_brackets`), which is what the declared pair needs.
* R12(iii) (contraction, count, start bound 21): prose; the count facts used are R6.
* R7(ii),(iii) summed counts: immediate from R6, not stated separately.

Status tier: FORMALISED (statement + proof, no sorry) for R1, R4, R5, R6, R7(i), R8(a)(b)(c)
and the unit-weight part of (e), R9, R10, R11(a)-(f), R12(ii),(iv); R12(ii),(iv) are conditional on
the named hypothesis `JointSound`. Items listed under NOT FORMALISED are not in this file.
-/
import Mathlib
import OcfVerification.C6Rounding

namespace OCF.R110

open Finset

set_option linter.unusedSectionVars false

/-! ## Basic objects -/

/-- Euclidean norm of a vector of `Fin n → ℝ` (bridge lemma `eN_eq_norm`). -/
noncomputable def eN {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

lemma eN_eq_norm {n : ℕ} (v : Fin n → ℝ) :
    eN v = ‖(WithLp.toLp 2 v : EuclideanSpace ℝ (Fin n))‖ := by
  rw [EuclideanSpace.norm_eq]; simp [eN]

lemma eN_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ eN v := Real.sqrt_nonneg _

lemma abs_le_eN {n : ℕ} (v : Fin n → ℝ) (i : Fin n) : |v i| ≤ eN v := by
  unfold eN
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun j => v j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

lemma eN_le_mul {n : ℕ} {u v : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ i, |u i| ≤ c * |v i|) : eN u ≤ c * eN v := by
  unfold eN
  have h1 : ∑ i, u i ^ 2 ≤ c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    have := h i
    have h2 : |u i| ^ 2 ≤ (c * |v i|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
    rw [sq_abs] at h2
    calc u i ^ 2 ≤ (c * |v i|) ^ 2 := h2
      _ = c ^ 2 * v i ^ 2 := by rw [mul_pow, sq_abs]
  calc Real.sqrt (∑ i, u i ^ 2) ≤ Real.sqrt (c ^ 2 * ∑ i, v i ^ 2) := Real.sqrt_le_sqrt h1
    _ = c * Real.sqrt (∑ i, v i ^ 2) := by
      rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

lemma eN_mono {n : ℕ} {u v : Fin n → ℝ} (h : ∀ i, |u i| ≤ |v i|) : eN u ≤ eN v := by
  have := eN_le_mul (u := u) (v := v) (c := 1) zero_le_one (by simpa using h)
  simpa using this

/-- Clamp onto `[0,1]`: `clamp s = min 1 (max 0 s)` (SD2). -/
noncomputable def clamp (s : ℝ) : ℝ := min 1 (max 0 s)

lemma clamp_eq_max_min (s : ℝ) : clamp s = max 0 (min 1 s) := by
  unfold clamp
  rcases le_total s 0 with h | h
  · simp [h]
  · rcases le_total s 1 with h' | h'
    · simp [h, h']
    · simp [h, h']

lemma clamp_mem (s : ℝ) : 0 ≤ clamp s ∧ clamp s ≤ 1 := by
  unfold clamp
  exact ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

lemma clamp_of_mem {s : ℝ} (h0 : 0 ≤ s) (h1 : s ≤ 1) : clamp s = s := by
  unfold clamp; rw [max_eq_right h0, min_eq_right h1]

lemma clamp_of_nonpos {s : ℝ} (h : s ≤ 0) : clamp s = 0 := by
  unfold clamp; rw [max_eq_left h]; simp

lemma clamp_of_ge_one {s : ℝ} (h : 1 ≤ s) : clamp s = 1 := by
  unfold clamp; rw [max_eq_right (by linarith)]; exact min_eq_left h

lemma clamp_lip (s s' : ℝ) : |clamp s - clamp s'| ≤ |s - s'| := by
  unfold clamp
  have h1 := abs_max_sub_max_le_max 0 s 0 s'
  have h2 := abs_min_sub_min_le_max 1 (max 0 s) 1 (max 0 s')
  have h3 : |max 0 s - max 0 s'| ≤ |s - s'| := by
    simpa using h1
  have h4 : |min 1 (max 0 s) - min 1 (max 0 s')| ≤ |max 0 s - max 0 s'| := by
    simpa using h2
  exact h4.trans h3

/-! ## R1 (binary identities) -/

/-- R1(a): on `{0,1}`, `clamp(a + b - 1) = a b` (the clamp performs the AND). -/
theorem clamp_and {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    clamp (a + b - 1) = a * b := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [clamp]

/-- The same identity in the form quoted in the dossier's section 10. -/
theorem clamp_and' {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) :
    max 0 (min 1 (a + b - 1)) = a * b := by
  rw [← clamp_eq_max_min]; exact clamp_and ha hb

/-- R1(c): the identity is false off `{0,1}`: `clamp (1/2 + 1/2 - 1) = 0 ≠ 1/4`. -/
theorem clamp_and_fails : clamp ((1 / 2 : ℝ) + 1 / 2 - 1) = 0 ∧ (0 : ℝ) ≠ 1 / 4 * 1 ∧
    (1 / 2 : ℝ) * (1 / 2) = 1 / 4 := by
  refine ⟨?_, by norm_num, by norm_num⟩
  norm_num [clamp]

/-- Cook's table `F(l,c,r)` of Rule 110 (cook2004, Sec. 1, p. 1), as a function on `ℝ`-valued
binary inputs: `F(0,0,0)=0, F(0,0,1)=1, F(0,1,0)=1, F(0,1,1)=1, F(1,0,0)=0, F(1,0,1)=1,
F(1,1,0)=1, F(1,1,1)=0`. -/
noncomputable def cookF (l c r : ℝ) : ℝ :=
  if l = 0 then (if c = 0 then (if r = 0 then 0 else 1) else 1)
  else (if c = 0 then (if r = 0 then 0 else 1) else (if r = 0 then 1 else 0))

/-- The Rule 110 polynomial `c + r - c r - l c r` (SD1). -/
def poly110 (l c r : ℝ) : ℝ := c + r - c * r - l * c * r

/-- R1(b): on `{0,1}³` the polynomial equals Cook's table value and is `0` or `1`. -/
theorem rule110_poly_table {l c r : ℝ} (hl : l = 0 ∨ l = 1) (hc : c = 0 ∨ c = 1)
    (hr : r = 0 ∨ r = 1) :
    poly110 l c r = cookF l c r ∧ (poly110 l c r = 0 ∨ poly110 l c r = 1) := by
  rcases hl with rfl | rfl <;> rcases hc with rfl | rfl <;> rcases hr with rfl | rfl <;>
    simp [poly110, cookF]

/-! ## Ring rows, Rule 110 -/

section Ring

variable {n : ℕ} [NeZero n]

/-- `x ∈ {0,1}ⁿ`. -/
def IsBin (x : Fin n → ℝ) : Prop := ∀ i, x i = 0 ∨ x i = 1

/-- The Rule 110 update on the ring `Z/nZ` (`Fin n` with cyclic `±1`; for `n = 1, 2` the
neighbours coincide and the formula is read literally as an index formula, SD1):
`t_i(x) = c + r - c r - l c r` at `(l,c,r) = (x_{i-1}, x_i, x_{i+1})`. -/
def rule110 (x : Fin n → ℝ) : Fin n → ℝ := fun i => poly110 (x (i - 1)) (x i) (x (i + 1))

/-- Neighbourhood sum `s_i = c_i + r_i`. -/
def sVec (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i + x (i + 1)

/-- Left neighbour vector `l_i = x_{i-1}`. -/
def lVec (x : Fin n → ℝ) : Fin n → ℝ := fun i => x (i - 1)

lemma rule110_bin {x : Fin n → ℝ} (hx : IsBin x) : IsBin (rule110 x) :=
  fun i => (rule110_poly_table (hx (i - 1)) (hx i) (hx (i + 1))).2

/-! ## R4 (read-out at a threshold) -/

/-- SD5: `rd_τ(u)_i = 1` if `u_i ≥ τ`, else `0` (ties up). -/
noncomputable def rdT (τ : ℝ) (u : Fin n → ℝ) : Fin n → ℝ := fun i => if τ ≤ u i then 1 else 0

/-- `rd01 = rd_{1/2}`. -/
noncomputable def rd01 (u : Fin n → ℝ) : Fin n → ℝ := rdT (1 / 2) u

/-- Read-out margin `min_i |y_i - τ|` (the `δ` of def:rounding at `y - τ𝟙`). -/
noncomputable def marg (τ : ℝ) (y : Fin n → ℝ) : ℝ := ⨅ i, |y i - τ|

lemma marg_le (τ : ℝ) (y : Fin n → ℝ) (i : Fin n) : marg τ y ≤ |y i - τ| :=
  ciInf_le (Set.finite_range _).bddBelow i

lemma le_marg {τ : ℝ} {y : Fin n → ℝ} {m : ℝ} (h : ∀ i, m ≤ |y i - τ|) : m ≤ marg τ y :=
  le_ciInf h

lemma exists_marg_eq (τ : ℝ) (y : Fin n → ℝ) : ∃ i, |y i - τ| = marg τ y :=
  exists_eq_ciInf_of_finite

/-- Link to the `rd` of `C6Rounding.lean` (def:rounding), via `u ↦ u - τ𝟙`:
`rd_τ(u) = (rd(u - τ𝟙) + 1)/2`. -/
lemma rdT_eq_C6 (τ : ℝ) (u : Fin n → ℝ) (i : Fin n) :
    rdT τ u i = (((OCF.C6.rd (fun j => u j - τ) i : ℤ) : ℝ) + 1) / 2 := by
  unfold rdT OCF.C6.rd
  by_cases h : τ ≤ u i
  · rw [if_pos h, if_pos (by linarith)]; norm_num
  · rw [if_neg h, if_neg (by linarith)]; norm_num

/-- R4: shifted-threshold read-out, a one-line reduction of prop:readout(a)
(`C6Rounding.rd_stable_lp`) along `u ↦ u - τ𝟙`: if `‖u - y‖_p < min_i |y_i - τ|`
then `rd_τ(u) = rd_τ(y)`, for every norm `ℓ_p`, `p ∈ [1,∞]` (hence for `ℓ₂`). -/
theorem readout_threshold (p : ENNReal) [Fact (1 ≤ p)] (τ : ℝ) (y u : Fin n → ℝ)
    (h : ‖WithLp.toLp p (u - y)‖ < marg τ y) : rdT τ u = rdT τ y := by
  have h' : ‖WithLp.toLp p ((fun j => u j - τ) - (fun j => y j - τ))‖ <
      OCF.C6.delta (fun j => y j - τ) := by
    have : ((fun j => u j - τ) - (fun j => y j - τ)) = u - y := by
      funext j; simp
    rw [this]; exact h
  have := OCF.C6.rd_stable_lp p _ _ h'
  funext i
  rw [rdT_eq_C6, rdT_eq_C6, this]

/-- R4 in the Euclidean norm of the file (`eN`). -/
theorem readout_threshold_eN (τ : ℝ) (y u : Fin n → ℝ) {m : ℝ}
    (hm : ∀ i, m ≤ |y i - τ|) (h : eN (u - y) < m) : rdT τ u = rdT τ y := by
  have h1 : ‖WithLp.toLp 2 (u - y)‖ < marg τ y := by
    rw [← eN_eq_norm]; exact lt_of_lt_of_le h (le_marg hm)
  exact readout_threshold 2 τ y u h1

/-- Coordinatewise form of R4 (used inside the proofs): if every coordinate error is below
the coordinate's distance to `τ`, the read-outs agree. -/
lemma rdT_eq_of_abs_lt {τ : ℝ} {y u : Fin n → ℝ} (h : ∀ i, |u i - y i| < |y i - τ|) :
    rdT τ u = rdT τ y := by
  funext i
  have h1 := h i
  rw [abs_sub_lt_iff] at h1
  unfold rdT
  rcases le_or_gt τ (y i) with hy | hy
  · rw [abs_of_nonneg (by linarith)] at h1
    rw [if_pos hy, if_pos (by linarith)]
  · rw [abs_of_neg (by linarith)] at h1
    rw [if_neg (by linarith), if_neg (by linarith)]


/-! ## Stage runs (SD3, SD4) and the elementary parts of R3 -/

/-- `P_C` coordinatewise: `C = B` (`b = true`, the clamp) or `C = ℝⁿ` (`b = false`, identity). -/
noncomputable def projC (b : Bool) (s : ℝ) : ℝ := if b then clamp s else s

lemma projC_lip (b : Bool) (s s' : ℝ) : |projC b s - projC b s'| ≤ |s - s'| := by
  cases b
  · simp [projC]
  · simpa [projC] using clamp_lip s s'

/-- The stage update `U(v) = P_C(γ v + α a)`, `γ = 1 - α` (SD4). -/
noncomputable def stageU (α : ℝ) (b : Bool) (a v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => projC b ((1 - α) * v i + α * a i)

/-- The residual `R_α(v) = (v - U(v))/α` (SD4). -/
noncomputable def stageR (α : ℝ) (b : Bool) (a v : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (v i - stageU α b a v i) / α

/-- The stage run `v_k = U^k(v_0)`. -/
noncomputable def stageIter (α : ℝ) (b : Bool) (a v0 : Fin n → ℝ) (k : ℕ) : Fin n → ℝ :=
  (stageU α b a)^[k] v0

/-- The candidate stage minimiser `P_C(a)`. -/
noncomputable def stageStar (b : Bool) (a : Fin n → ℝ) : Fin n → ℝ := fun i => projC b (a i)

/-- The stage energy `E_{a,C}(v) = ½‖v - a‖²` (the indicator `ι_C` is the side condition
`InC`). -/
noncomputable def stageEnergy (a v : Fin n → ℝ) : ℝ := 1 / 2 * ∑ i, (v i - a i) ^ 2

/-- `v ∈ C`. -/
def InC (b : Bool) (v : Fin n → ℝ) : Prop := b = true → ∀ i, 0 ≤ v i ∧ v i ≤ 1

lemma stageIter_zero (α : ℝ) (b : Bool) (a v0 : Fin n → ℝ) : stageIter α b a v0 0 = v0 := rfl

lemma stageIter_succ (α : ℝ) (b : Bool) (a v0 : Fin n → ℝ) (k : ℕ) :
    stageIter α b a v0 (k + 1) = stageU α b a (stageIter α b a v0 k) := by
  unfold stageIter; rw [Function.iterate_succ_apply']

/-- R3(a), coordinatewise: `U` is `γ`-Lipschitz. -/
lemma stageU_lip {α : ℝ} (hα1 : α ≤ 1) (b : Bool) (a v v' : Fin n → ℝ) (i : Fin n) :
    |stageU α b a v i - stageU α b a v' i| ≤ (1 - α) * |v i - v' i| := by
  unfold stageU
  refine (projC_lip _ _ _).trans ?_
  have : (1 - α) * v i + α * a i - ((1 - α) * v' i + α * a i) = (1 - α) * (v i - v' i) := by ring
  rw [this, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - α)]

/-- R3(b): `P_C(a)` is a fixed point of `U` (`α ∈ (0,1]`). -/
lemma stageU_star {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a : Fin n → ℝ) :
    stageU α b a (stageStar b a) = stageStar b a := by
  funext i
  unfold stageU stageStar
  cases b
  · simp [projC]; ring
  · simp only [projC, if_true]
    rcases le_total (a i) 0 with h | h
    · rw [clamp_of_nonpos h, mul_zero, zero_add, clamp_of_nonpos (by nlinarith)]
    · rcases le_total (a i) 1 with h' | h'
      · rw [clamp_of_mem h h']
        have : (1 - α) * a i + α * a i = a i := by ring
        rw [this, clamp_of_mem h h']
      · rw [clamp_of_ge_one h', mul_one, clamp_of_ge_one (by nlinarith)]

/-- R3(c), coordinatewise: `|v_i - v*_i| ≤ |R_α(v)_i|`. -/
lemma dist_star_le_resid {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a v : Fin n → ℝ)
    (i : Fin n) : |v i - stageStar b a i| ≤ |stageR α b a v i| := by
  have h1 := stageU_lip hα1 b a v (stageStar b a) i
  rw [stageU_star hα0 hα1] at h1
  have h2 : |v i - stageU α b a v i| = α * |stageR α b a v i| := by
    unfold stageR
    rw [abs_div, abs_of_pos hα0]; field_simp
  have h3 : |v i - stageStar b a i| ≤ |v i - stageU α b a v i| + |stageU α b a v i - stageStar b a i| := by
    have := abs_add_le (v i - stageU α b a v i) (stageU α b a v i - stageStar b a i)
    simpa using this
  rw [h2] at h3
  have h4 : α * |v i - stageStar b a i| ≤ α * |stageR α b a v i| := by nlinarith [abs_nonneg (v i - stageStar b a i)]
  exact le_of_mul_le_mul_left h4 hα0

/-- R3(c): certified distance in the Euclidean norm, `‖v - v*‖ ≤ ‖R_α(v)‖`. -/
theorem stage_distance {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a v : Fin n → ℝ) :
    eN (v - stageStar b a) ≤ eN (stageR α b a v) :=
  eN_mono fun i => by simpa using dist_star_le_resid hα0 hα1 b a v i

/-- R3(d), coordinatewise: `|R_α(U v)_i| ≤ γ |R_α(v)_i|`. -/
lemma resid_contr {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a v : Fin n → ℝ) (i : Fin n) :
    |stageR α b a (stageU α b a v) i| ≤ (1 - α) * |stageR α b a v i| := by
  have h1 := stageU_lip hα1 b a v (stageU α b a v) i
  have h2 : |v i - stageU α b a v i| = α * |stageR α b a v i| := by
    unfold stageR
    rw [abs_div, abs_of_pos hα0]; field_simp
  have h3 : |stageU α b a v i - stageU α b a (stageU α b a v) i| =
      α * |stageR α b a (stageU α b a v) i| := by
    unfold stageR
    rw [abs_div, abs_of_pos hα0]; field_simp
  rw [h3] at h1
  rw [h2] at h1
  have h4 : α * |stageR α b a (stageU α b a v) i| ≤ α * ((1 - α) * |stageR α b a v i|) := by
    calc _ ≤ _ := h1
      _ = _ := by ring
  exact le_of_mul_le_mul_left h4 hα0

lemma resid_iter_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a v0 : Fin n → ℝ) (k : ℕ)
    (i : Fin n) : |stageR α b a (stageIter α b a v0 k) i| ≤ (1 - α) ^ k * |stageR α b a v0 i| := by
  induction k with
  | zero => simp [stageIter_zero]
  | succ k ih =>
    rw [stageIter_succ]
    calc _ ≤ (1 - α) * |stageR α b a (stageIter α b a v0 k) i| := resid_contr hα0 hα1 b a _ i
      _ ≤ (1 - α) * ((1 - α) ^ k * |stageR α b a v0 i|) :=
        mul_le_mul_of_nonneg_left ih (by linarith)
      _ = _ := by ring

/-- R3(d): `ρ_k ≤ γ^k ρ_0`. -/
theorem resid_norm_iter_le {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a v0 : Fin n → ℝ)
    (k : ℕ) : eN (stageR α b a (stageIter α b a v0 k)) ≤ (1 - α) ^ k * eN (stageR α b a v0) :=
  eN_le_mul (pow_nonneg (by linarith) k) (resid_iter_le hα0 hα1 b a v0 k)

/-- R3(d) and R5(iii): along every stage run some index has `ρ_k < ε`, for every `ε > 0`
(in particular acceptance at `ρ_k < 1/2` occurs). -/
theorem stage_exists_accepted {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool)
    (a v0 : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k, eN (stageR α b a (stageIter α b a v0 k)) < ε := by
  set c := eN (stageR α b a v0) + 1 with hc
  have hc0 : 0 < c := by have := eN_nonneg (stageR α b a v0); linarith
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hε hc0) (by linarith : 1 - α < 1)
  refine ⟨k, ?_⟩
  calc _ ≤ (1 - α) ^ k * eN (stageR α b a v0) := resid_norm_iter_le hα0 hα1 b a v0 k
    _ ≤ (1 - α) ^ k * c := mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg (by linarith) k)
    _ < ε / c * c := mul_lt_mul_of_pos_right hk hc0
    _ = ε := by field_simp

/-- R3(b): `P_C(a)` is the unique minimiser of `E_{a,C}` on `C`. -/
theorem stage_unique_min (b : Bool) (a v : Fin n → ℝ) (hv : InC b v) :
    stageEnergy a (stageStar b a) ≤ stageEnergy a v ∧
      (stageEnergy a v ≤ stageEnergy a (stageStar b a) → v = stageStar b a) := by
  have key : ∀ i, (stageStar b a i - a i) ^ 2 ≤ (v i - a i) ^ 2 ∧
      ((v i - a i) ^ 2 ≤ (stageStar b a i - a i) ^ 2 → v i = stageStar b a i) := by
    intro i
    cases b
    · simp [stageStar, projC]
      exact ⟨sq_nonneg _, fun h => by linarith⟩
    · have hvi := hv rfl i
      simp only [stageStar, projC, if_true]
      rcases le_total (a i) 0 with h | h
      · rw [clamp_of_nonpos h]
        refine ⟨by nlinarith [hvi.1], fun h2 => ?_⟩
        nlinarith [hvi.1]
      · rcases le_total (a i) 1 with h' | h'
        · rw [clamp_of_mem h h']
          refine ⟨by simp; positivity, fun h2 => ?_⟩
          have : (v i - a i) ^ 2 ≤ 0 := by simpa using h2
          nlinarith [sq_nonneg (v i - a i)]
        · rw [clamp_of_ge_one h']
          refine ⟨by nlinarith [hvi.2], fun h2 => ?_⟩
          nlinarith [hvi.2]
  constructor
  · unfold stageEnergy
    have := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (key i).1)
    linarith
  · intro h
    unfold stageEnergy at h
    have hle : ∑ i, (v i - a i) ^ 2 ≤ ∑ i, (stageStar b a i - a i) ^ 2 := by linarith
    have hge := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (key i).1)
    have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (key i).1)).mp (le_antisymm hge hle)
    funext i
    exact (key i).2 (heq i (Finset.mem_univ i)).symm.le

/-- A report: if `P_C(a)` is binary and the iterate has residual `< 1/2`, then
`rd01(v_k) = P_C(a)`. (R4 at `τ = 1/2`, `μ = 1/2`, with R3(c).) -/
theorem stage_report {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (b : Bool) (a v : Fin n → ℝ)
    (hbin : IsBin (stageStar b a)) (hacc : eN (stageR α b a v) < 1 / 2) :
    rd01 v = stageStar b a := by
  have h1 : rdT (1 / 2) v = rdT (1 / 2) (stageStar b a) := by
    apply rdT_eq_of_abs_lt
    intro i
    have h2 := dist_star_le_resid hα0 hα1 b a v i
    have h3 := abs_le_eN (stageR α b a v) i
    have h4 : |stageStar b a i - 1 / 2| = 1 / 2 := by
      rcases hbin i with h | h <;> rw [h] <;> norm_num
    rw [h4]
    have : |v i - stageStar b a i| < 1 / 2 := by linarith
    exact this
  rw [rd01, h1]
  funext i
  unfold rdT
  rcases hbin i with h | h <;> rw [h] <;> norm_num


/-! ## The pipeline (SD3, SD6), R5 -/

/-- Stage P data `a^P = s - 1`. -/
def aP (x : Fin n → ℝ) : Fin n → ℝ := fun i => x i + x (i + 1) - 1

/-- Stage Q data `a^Q = l + p̂ - 1`. -/
def aQ (x ph : Fin n → ℝ) : Fin n → ℝ := fun i => x (i - 1) + ph i - 1

/-- Stage Y data `a^Y = s - p̂ - q̂`. -/
def aY (x ph qh : Fin n → ℝ) : Fin n → ℝ := fun i => (x i + x (i + 1)) - ph i - qh i

/-- `p̂ = rd01` of the stage-P iterate (arbitrary start `p0`, index `kP`). -/
noncomputable def phat (α : ℝ) (x p0 : Fin n → ℝ) (kP : ℕ) : Fin n → ℝ :=
  rd01 (stageIter α true (aP x) p0 kP)

/-- `q̂ = rd01` of the stage-Q iterate, stage Q's data built from the ACTUAL report `p̂`. -/
noncomputable def qhat (α : ℝ) (x p0 q0 : Fin n → ℝ) (kP kQ : ℕ) : Fin n → ℝ :=
  rd01 (stageIter α true (aQ x (phat α x p0 kP)) q0 kQ)

/-- `ŷ = rd01` of the stage-Y iterate, data built from the actual reports `p̂, q̂`. -/
noncomputable def yhat (α : ℝ) (x p0 q0 y0 : Fin n → ℝ) (kP kQ kY : ℕ) : Fin n → ℝ :=
  rd01 (stageIter α false (aY x (phat α x p0 kP) (qhat α x p0 q0 kP kQ)) y0 kY)

/-- Acceptance of the three chosen indices: `ρ_k < 1/2` at each stage (the only property
of the stopping rule used, H-ACCEPT). -/
def Accepted (α : ℝ) (x p0 q0 y0 : Fin n → ℝ) (kP kQ kY : ℕ) : Prop :=
  eN (stageR α true (aP x) (stageIter α true (aP x) p0 kP)) < 1 / 2 ∧
  eN (stageR α true (aQ x (phat α x p0 kP))
      (stageIter α true (aQ x (phat α x p0 kP)) q0 kQ)) < 1 / 2 ∧
  eN (stageR α false (aY x (phat α x p0 kP) (qhat α x p0 q0 kP kQ))
      (stageIter α false (aY x (phat α x p0 kP) (qhat α x p0 q0 kP kQ)) y0 kY)) < 1 / 2

lemma stageStar_aP {x : Fin n → ℝ} (hx : IsBin x) :
    stageStar true (aP x) = fun i => x i * x (i + 1) := by
  funext i
  simp only [stageStar, projC, if_true, aP]
  have := clamp_and (hx i) (hx (i + 1))
  exact this

lemma stageStar_aQ {x ph : Fin n → ℝ} (hx : IsBin x) (hp : IsBin ph) :
    stageStar true (aQ x ph) = fun i => x (i - 1) * ph i := by
  funext i
  simp only [stageStar, projC, if_true, aQ]
  exact clamp_and (hx (i - 1)) (hp i)

lemma stageStar_aY (x ph qh : Fin n → ℝ) :
    stageStar false (aY x ph qh) = aY x ph qh := by
  funext i; simp [stageStar, projC]

lemma aY_eq_rule110 {x : Fin n → ℝ} (hp : ph = fun i => x i * x (i + 1))
    (hq : qh = fun i => x (i - 1) * x i * x (i + 1)) : aY x ph qh = rule110 x := by
  funext i
  subst hp hq
  simp only [aY, rule110, poly110]

lemma isBin_mul {a b : ℝ} (ha : a = 0 ∨ a = 1) (hb : b = 0 ∨ b = 1) : a * b = 0 ∨ a * b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp

/-- R5(i): the stage minimisers are `p* = (x_i x_{i+1})`, `q* = (x_{i-1} x_i x_{i+1})`
(for `p̂ = p*`), `y* = t(x)`, all binary (stage Y: `C = ℝⁿ`, `y* = a^Y`). -/
theorem pipeline_minimisers {x : Fin n → ℝ} (hx : IsBin x) :
    stageStar true (aP x) = (fun i => x i * x (i + 1)) ∧
    stageStar true (aQ x (fun i => x i * x (i + 1))) = (fun i => x (i - 1) * x i * x (i + 1)) ∧
    stageStar false (aY x (fun i => x i * x (i + 1)) (fun i => x (i - 1) * x i * x (i + 1)))
      = rule110 x ∧
    IsBin (fun i => x i * x (i + 1)) ∧ IsBin (fun i => x (i - 1) * x i * x (i + 1)) ∧
    IsBin (rule110 x) := by
  have hp : IsBin (fun i => x i * x (i + 1)) := fun i => isBin_mul (hx i) (hx (i + 1))
  have hq : IsBin (fun i => x (i - 1) * x i * x (i + 1)) :=
    fun i => isBin_mul (isBin_mul (hx (i - 1)) (hx i)) (hx (i + 1))
  refine ⟨stageStar_aP hx, ?_, ?_, hp, hq, rule110_bin hx⟩
  · rw [stageStar_aQ hx hp]; funext i; simp [mul_assoc]
  · rw [stageStar_aY, aY_eq_rule110 rfl rfl]

/-- R5 (ii)–(iii): exactness of one pipeline step. For `n ≥ 1`, `x ∈ {0,1}ⁿ`,
`α ∈ (0,1]`, arbitrary starts and any accepted indices (`ρ_k < 1/2` at each stage, stage Q's
data built from the actual report `p̂`, stage Y's from the actual `p̂, q̂`), the reports are
`p̂ = (x_i x_{i+1})`, `q̂ = (x_{i-1} x_i x_{i+1})`, `ŷ = t(x)`. -/
theorem pipeline_step_exact {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x : Fin n → ℝ}
    (hx : IsBin x) (p0 q0 y0 : Fin n → ℝ) (kP kQ kY : ℕ)
    (hacc : Accepted α x p0 q0 y0 kP kQ kY) :
    phat α x p0 kP = (fun i => x i * x (i + 1)) ∧
    qhat α x p0 q0 kP kQ = (fun i => x (i - 1) * x i * x (i + 1)) ∧
    yhat α x p0 q0 y0 kP kQ kY = rule110 x := by
  obtain ⟨hP, hQ, hY⟩ := hacc
  obtain ⟨-, -, -, hpb, hqb, htb⟩ := pipeline_minimisers hx
  have e1 : phat α x p0 kP = (fun i => x i * x (i + 1)) := by
    unfold phat
    rw [stage_report hα0 hα1 true _ _ (by rw [stageStar_aP hx]; exact hpb) hP, stageStar_aP hx]
  refine ⟨e1, ?_, ?_⟩
  · have hpb' : IsBin (phat α x p0 kP) := by rw [e1]; exact hpb
    unfold qhat
    rw [stage_report hα0 hα1 true _ _ (by rw [stageStar_aQ hx hpb']; exact fun i => isBin_mul (hx (i-1)) (hpb' i)) hQ,
      stageStar_aQ hx hpb', e1]
    funext i; simp [mul_assoc]
  · have e2 : qhat α x p0 q0 kP kQ = (fun i => x (i - 1) * x i * x (i + 1)) := by
      have hpb' : IsBin (phat α x p0 kP) := by rw [e1]; exact hpb
      unfold qhat
      rw [stage_report hα0 hα1 true _ _ (by rw [stageStar_aQ hx hpb']; exact fun i => isBin_mul (hx (i-1)) (hpb' i)) hQ,
        stageStar_aQ hx hpb', e1]
      funext i; simp [mul_assoc]
    have hdat : aY x (phat α x p0 kP) (qhat α x p0 q0 kP kQ) = rule110 x := aY_eq_rule110 e1 e2
    unfold yhat
    rw [stage_report hα0 hα1 false _ _ (by rw [stageStar_aY, hdat]; exact htb) hY,
      stageStar_aY, hdat]

/-- R5(iii), existence: for any starts, acceptance occurs at every stage, in order. -/
theorem pipeline_exists_accepted {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (x p0 q0 y0 : Fin n → ℝ) :
    ∃ kP kQ kY, Accepted α x p0 q0 y0 kP kQ kY := by
  obtain ⟨kP, hP⟩ := stage_exists_accepted hα0 hα1 true (aP x) p0 (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨kQ, hQ⟩ := stage_exists_accepted hα0 hα1 true (aQ x (phat α x p0 kP)) q0
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨kY, hY⟩ := stage_exists_accepted hα0 hα1 false
    (aY x (phat α x p0 kP) (qhat α x p0 q0 kP kQ)) y0 (by norm_num : (0 : ℝ) < 1 / 2)
  exact ⟨kP, kQ, kY, hP, hQ, hY⟩

/-! ### R7: composition over rows -/

/-- R7(i): an `N`-step run (`3N` stage runs, each with any start and any indices accepted at
`ρ < 1/2`) reproduces `t^h(x⁽⁰⁾)` at every `h ≤ N`, for every `n ≥ 1` and `N`; every row
handed on is binary. -/
theorem pipeline_N_steps {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {x0 : Fin n → ℝ} (hx0 : IsBin x0)
    (N : ℕ) (rows P0 Q0 Y0 : ℕ → Fin n → ℝ) (kP kQ kY : ℕ → ℕ)
    (h0 : rows 0 = x0)
    (hstep : ∀ h < N, Accepted α (rows h) (P0 h) (Q0 h) (Y0 h) (kP h) (kQ h) (kY h) ∧
      rows (h + 1) = yhat α (rows h) (P0 h) (Q0 h) (Y0 h) (kP h) (kQ h) (kY h)) :
    ∀ h ≤ N, rows h = rule110^[h] x0 ∧ IsBin (rows h) := by
  intro h
  induction h with
  | zero => intro _; simp [h0, hx0]
  | succ h ih =>
    intro hh
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hacc, hnext⟩ := hstep h (by omega)
    have := (pipeline_step_exact hα0 hα1 ih2 _ _ _ _ _ _ hacc).2.2
    rw [hnext, this, ih1, Function.iterate_succ_apply']
    exact ⟨rfl, by rw [← ih1]; exact rule110_bin ih2⟩


/-! ## R6: closed forms, exact stopping counts -/

/-- Indicator `1[a_i = 1]`. -/
noncomputable def ind1 (a : Fin n → ℝ) (i : Fin n) : ℝ := if a i = 1 then 1 else 0

/-- Number of coordinates with data `+1`. -/
noncomputable def cnt1 (a : Fin n → ℝ) : ℕ := (Finset.univ.filter fun i => a i = 1).card

/-- R6(ii), stages P and Q (`C = B`, data `a ∈ {-1,0,1}ⁿ`, start `0`):
`v_k = (1 - γ^k) 1[a = 1]` coordinatewise (`0^0 = 1`, so `α = 1` is included). -/
theorem boxStage_iter_closed {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {a : Fin n → ℝ}
    (ha : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1) (k : ℕ) (i : Fin n) :
    stageIter α true a 0 k i = (1 - (1 - α) ^ k) * ind1 a i := by
  induction k with
  | zero => simp [stageIter_zero]
  | succ k ih =>
    rw [stageIter_succ]
    unfold stageU
    simp only [projC, if_true]
    rw [ih]
    have hg0 : 0 ≤ 1 - α := by linarith
    have hg1 : (1 - α) ^ (k + 1) ≤ 1 := pow_le_one₀ hg0 (by linarith)
    have hg2 : 0 ≤ (1 - α) ^ (k + 1) := pow_nonneg hg0 _
    rcases ha i with h | h | h
    · have : ind1 a i = 0 := by simp only [ind1, h]; norm_num
      rw [this, h]
      simp only [mul_zero, zero_add, mul_neg, mul_one]
      rw [clamp_of_nonpos (by linarith)]
    · have : ind1 a i = 0 := by simp [ind1, h]
      rw [this, h]; simp [clamp]
    · have : ind1 a i = 1 := by simp [ind1, h]
      rw [this, h]
      have e : (1 - α) * ((1 - (1 - α) ^ k) * 1) + α * 1 = 1 - (1 - α) ^ (k + 1) := by ring
      rw [e, clamp_of_mem (by linarith) (by linarith)]
      ring

/-- R6(ii), stages P and Q: the residual is `-γ^k 1[a = 1]`, and `ρ_k = γ^k √m`,
`m = #{i : a_i = 1}`. -/
theorem boxStage_resid_closed {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {a : Fin n → ℝ}
    (ha : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1) (k : ℕ) :
    (∀ i, stageR α true a (stageIter α true a 0 k) i = -(1 - α) ^ k * ind1 a i) ∧
    eN (stageR α true a (stageIter α true a 0 k)) = (1 - α) ^ k * Real.sqrt (cnt1 a) := by
  have hres : ∀ i, stageR α true a (stageIter α true a 0 k) i = -(1 - α) ^ k * ind1 a i := by
    intro i
    unfold stageR
    have h1 := boxStage_iter_closed hα0 hα1 ha k i
    have h2 := boxStage_iter_closed hα0 hα1 ha (k + 1) i
    rw [stageIter_succ] at h2
    rw [h2, h1]
    field_simp
    ring
  refine ⟨hres, ?_⟩
  unfold eN
  have hsum : ∑ i, (stageR α true a (stageIter α true a 0 k) i) ^ 2 =
      ((1 - α) ^ k) ^ 2 * (cnt1 a : ℝ) := by
    have : ∀ i, (stageR α true a (stageIter α true a 0 k) i) ^ 2 =
        ((1 - α) ^ k) ^ 2 * ind1 a i := by
      intro i
      rw [hres i]
      have : ind1 a i ^ 2 = ind1 a i := by unfold ind1; split_ifs <;> simp
      calc (-(1 - α) ^ k * ind1 a i) ^ 2 = ((1 - α) ^ k) ^ 2 * ind1 a i ^ 2 := by ring
        _ = _ := by rw [this]
    simp_rw [this]
    rw [← Finset.mul_sum]
    congr 1
    unfold ind1 cnt1
    rw [Finset.sum_boole]
  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg (by linarith) _)]

/-- R6(ii), stage Y (`C = ℝⁿ`, data `t = t(x)`, start `x`): `y_k = t + γ^k (x - t)`. -/
theorem yStage_iter_closed {α : ℝ} {x : Fin n → ℝ} (k : ℕ) (i : Fin n) :
    stageIter α false (rule110 x) x k i = rule110 x i + (1 - α) ^ k * (x i - rule110 x i) := by
  induction k with
  | zero => simp [stageIter_zero]
  | succ k ih =>
    rw [stageIter_succ]
    unfold stageU
    simp only [projC, Bool.false_eq_true, if_false]
    rw [ih]; ring

/-- Number of cells where `x_i ≠ t_i(x)`: `m_Y`. -/
noncomputable def mY (x : Fin n → ℝ) : ℕ := (Finset.univ.filter fun i => x i ≠ rule110 x i).card

/-- R6(ii), stage Y: residual `γ^k (x - t)` and `ρ_k = γ^k √m_Y`. -/
theorem yStage_resid_closed {α : ℝ} (hα0 : 0 < α) {x : Fin n → ℝ} (hx : IsBin x) (k : ℕ) :
    (∀ i, stageR α false (rule110 x) (stageIter α false (rule110 x) x k) i =
      (1 - α) ^ k * (x i - rule110 x i)) ∧
    eN (stageR α false (rule110 x) (stageIter α false (rule110 x) x k)) =
      |(1 - α) ^ k| * Real.sqrt (mY x) := by
  have hres : ∀ i, stageR α false (rule110 x) (stageIter α false (rule110 x) x k) i =
      (1 - α) ^ k * (x i - rule110 x i) := by
    intro i
    unfold stageR
    have h1 := yStage_iter_closed (α := α) (x := x) k i
    have h2 := yStage_iter_closed (α := α) (x := x) (k + 1) i
    rw [stageIter_succ] at h2
    rw [h2, h1]
    field_simp
    ring
  refine ⟨hres, ?_⟩
  unfold eN
  have hsum : ∑ i, (stageR α false (rule110 x) (stageIter α false (rule110 x) x k) i) ^ 2 =
      ((1 - α) ^ k) ^ 2 * (mY x : ℝ) := by
    have : ∀ i, (stageR α false (rule110 x) (stageIter α false (rule110 x) x k) i) ^ 2 =
        ((1 - α) ^ k) ^ 2 * (if x i ≠ rule110 x i then 1 else 0) := by
      intro i
      rw [hres i, mul_pow]
      congr 1
      have hb := rule110_bin hx i
      rcases hx i with h | h <;> rcases hb with h' | h' <;> simp [h, h']
    simp_rw [this]
    rw [← Finset.mul_sum]
    congr 1
    unfold mY
    rw [Finset.sum_boole]
  rw [hsum, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The stopping index of R6: the first `k` with `γ^k √m ≤ ε`:
`0` if `m = 0`; `1` if `α = 1`; `⌈log(√m/ε)/log(1/γ)⌉` otherwise. -/
noncomputable def stopCount (α ε : ℝ) (m : ℕ) : ℕ :=
  if m = 0 then 0 else if α = 1 then 1 else ⌈Real.log (Real.sqrt m / ε) / Real.log (1 / (1 - α))⌉₊

/-- R6(ii), the count equation: the stopping index is exactly `stopCount`, with equality. -/
theorem count_isLeast {α ε : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (m : ℕ) : IsLeast {k : ℕ | (1 - α) ^ k * Real.sqrt m ≤ ε} (stopCount α ε m) := by
  unfold stopCount
  by_cases hm : m = 0
  · simp only [hm, if_true, Nat.cast_zero, Real.sqrt_zero, mul_zero]
    exact ⟨hε.le, fun k _ => Nat.zero_le k⟩
  · rw [if_neg hm]
    have hm1 : (1 : ℝ) ≤ Real.sqrt m := by
      rw [Real.one_le_sqrt]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hm
    by_cases hα : α = 1
    · rw [if_pos hα]
      subst hα
      refine ⟨by simp; linarith, ?_⟩
      intro k hk
      by_contra hk0
      have : k = 0 := by omega
      subst this
      simp at hk; linarith
    · rw [if_neg hα]
      have hg0 : 0 < 1 - α := by
        have : α < 1 := lt_of_le_of_ne hα1 hα
        linarith
      have hg1 : 1 - α < 1 := by linarith
      have hL : 0 < Real.log (1 / (1 - α)) := by
        apply Real.log_pos
        rw [lt_div_iff₀ hg0]; linarith
      have key : ∀ k : ℕ, (1 - α) ^ k * Real.sqrt m ≤ ε ↔
          Real.log (Real.sqrt m / ε) / Real.log (1 / (1 - α)) ≤ k := by
        intro k
        have hsq : 0 < Real.sqrt m := by linarith
        rw [div_le_iff₀ hL]
        have e1 : (1 - α) ^ k * Real.sqrt m ≤ ε ↔
            Real.log ((1 - α) ^ k * Real.sqrt m) ≤ Real.log ε :=
          (Real.log_le_log_iff (by positivity) hε).symm
        rw [e1, Real.log_mul (by positivity) hsq.ne', Real.log_pow, Real.log_div hsq.ne' hε.ne',
          one_div, Real.log_inv]
        constructor <;> intro h <;> nlinarith
      refine ⟨(key _).mpr (Nat.le_ceil _), ?_⟩
      intro k hk
      exact Nat.ceil_le.mpr ((key k).mp hk)

/-- R6(ii) for stages P and Q: the stopping index of the run `v_0 = 0` is `stopCount α ε m`,
`m = #{a_i = 1}`: `{k : ρ_k ≤ ε}` has least element `stopCount α ε m`. -/
theorem boxStage_stop {α ε : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {a : Fin n → ℝ} (ha : ∀ i, a i = -1 ∨ a i = 0 ∨ a i = 1) :
    IsLeast {k : ℕ | eN (stageR α true a (stageIter α true a 0 k)) ≤ ε}
      (stopCount α ε (cnt1 a)) := by
  have := count_isLeast hα0 hα1 hε hε2 (cnt1 a)
  simpa only [(boxStage_resid_closed hα0 hα1 ha _).2] using this

/-- R6(ii) for stage Y: the stopping index of the run `y_0 = x` is `stopCount α ε m_Y`. -/
theorem yStage_stop {α ε : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (hε2 : ε < 1 / 2)
    {x : Fin n → ℝ} (hx : IsBin x) :
    IsLeast {k : ℕ | eN (stageR α false (rule110 x) (stageIter α false (rule110 x) x k)) ≤ ε}
      (stopCount α ε (mY x)) := by
  have := count_isLeast hα0 hα1 hε hε2 (mY x)
  simpa only [(yStage_resid_closed hα0 hx _).2,
    abs_of_nonneg (pow_nonneg (by linarith : 0 ≤ 1 - α) _)] using this

/-- The data of stage P is in `{-1,0,1}` for binary `x`, and `a^P_i = 1` iff
`x_i = x_{i+1} = 1`. -/
lemma aP_range {x : Fin n → ℝ} (hx : IsBin x) (i : Fin n) :
    aP x i = -1 ∨ aP x i = 0 ∨ aP x i = 1 := by
  unfold aP
  rcases hx i with h | h <;> rcases hx (i + 1) with h' | h' <;> simp [h, h']

lemma aP_eq_one_iff {x : Fin n → ℝ} (hx : IsBin x) (i : Fin n) :
    aP x i = 1 ↔ x i = 1 ∧ x (i + 1) = 1 := by
  unfold aP
  rcases hx i with h | h <;> rcases hx (i + 1) with h' | h' <;> simp [h, h'] <;> norm_num

lemma aQ_range {x ph : Fin n → ℝ} (hx : IsBin x) (hp : IsBin ph) (i : Fin n) :
    aQ x ph i = -1 ∨ aQ x ph i = 0 ∨ aQ x ph i = 1 := by
  unfold aQ
  rcases hx (i - 1) with h | h <;> rcases hp i with h' | h' <;> simp [h, h']

lemma aQ_eq_one_iff {x ph : Fin n → ℝ} (hx : IsBin x) (hp : IsBin ph) (i : Fin n) :
    aQ x ph i = 1 ↔ x (i - 1) = 1 ∧ ph i = 1 := by
  unfold aQ
  rcases hx (i - 1) with h | h <;> rcases hp i with h' | h' <;> simp [h, h'] <;> norm_num

/-- `m_P = #{i : x_i = x_{i+1} = 1}`. -/
noncomputable def mP (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i => x i = 1 ∧ x (i + 1) = 1).card

/-- `m_Q = #{i : x_{i-1} = 1 ∧ p̂_i = 1}`. -/
noncomputable def mQ (x ph : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i => x (i - 1) = 1 ∧ ph i = 1).card

lemma cnt1_aP {x : Fin n → ℝ} (hx : IsBin x) : cnt1 (aP x) = mP x := by
  unfold cnt1 mP; congr 1; ext i; simp [aP_eq_one_iff hx]

lemma cnt1_aQ {x ph : Fin n → ℝ} (hx : IsBin x) (hp : IsBin ph) : cnt1 (aQ x ph) = mQ x ph := by
  unfold cnt1 mQ; congr 1; ext i; simp [aQ_eq_one_iff hx hp]

/-- With `p̂` as in R5, `m_Q = #{i : x_{i-1} x_i x_{i+1} = 1}`. -/
lemma mQ_pstar {x : Fin n → ℝ} (hx : IsBin x) :
    mQ x (fun i => x i * x (i + 1)) =
      (Finset.univ.filter fun i => x (i - 1) * x i * x (i + 1) = 1).card := by
  unfold mQ; congr 1; ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hx (i - 1) with h | h <;> rcases hx i with h' | h' <;> rcases hx (i + 1) with h'' | h'' <;>
    simp [h, h', h'']

/-- R6(ii) packaged for the pipeline (stage P from `0`, stage Q from `0` with the report
`p̂ = (x_i x_{i+1})`, stage Y from `x` with the reports of R5): exact residuals and counts
`m_P, m_Q, m_Y`. -/
theorem pipeline_exact_counts {α ε : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε)
    (hε2 : ε < 1 / 2) {x : Fin n → ℝ} (hx : IsBin x) :
    (∀ k, eN (stageR α true (aP x) (stageIter α true (aP x) 0 k)) =
        (1 - α) ^ k * Real.sqrt (mP x)) ∧
    IsLeast {k : ℕ | eN (stageR α true (aP x) (stageIter α true (aP x) 0 k)) ≤ ε}
      (stopCount α ε (mP x)) ∧
    (∀ k, eN (stageR α true (aQ x (fun i => x i * x (i + 1)))
        (stageIter α true (aQ x (fun i => x i * x (i + 1))) 0 k)) =
        (1 - α) ^ k * Real.sqrt (mQ x (fun i => x i * x (i + 1)))) ∧
    IsLeast {k : ℕ | eN (stageR α true (aQ x (fun i => x i * x (i + 1)))
        (stageIter α true (aQ x (fun i => x i * x (i + 1))) 0 k)) ≤ ε}
      (stopCount α ε (mQ x (fun i => x i * x (i + 1)))) ∧
    (∀ k, eN (stageR α false (rule110 x) (stageIter α false (rule110 x) x k)) =
        (1 - α) ^ k * Real.sqrt (mY x)) ∧
    IsLeast {k : ℕ | eN (stageR α false (rule110 x) (stageIter α false (rule110 x) x k)) ≤ ε}
      (stopCount α ε (mY x)) := by
  have hp : IsBin (fun i => x i * x (i + 1)) := fun i => isBin_mul (hx i) (hx (i + 1))
  have haP := aP_range hx
  have haQ := aQ_range hx hp
  refine ⟨fun k => ?_, ?_, fun k => ?_, ?_, fun k => ?_, yStage_stop hα0 hα1 hε hε2 hx⟩
  · rw [(boxStage_resid_closed hα0 hα1 haP k).2, cnt1_aP hx]
  · have := boxStage_stop hα0 hα1 hε hε2 haP
    rwa [cnt1_aP hx] at this
  · rw [(boxStage_resid_closed hα0 hα1 haQ k).2, cnt1_aQ hx hp]
  · have := boxStage_stop hα0 hα1 hε hε2 haQ
    rwa [cnt1_aQ hx hp] at this
  · rw [(yStage_resid_closed hα0 hx k).2, abs_of_nonneg (pow_nonneg (by linarith) _)]

/-- R6(iii): the per-stage bound `K(n, ε, α)`: `⌈log(√n/ε)/log(1/γ)⌉` if `α < 1`, `1` if
`α = 1`. -/
noncomputable def Kbound (α ε : ℝ) (n : ℕ) : ℕ :=
  if α = 1 then 1 else ⌈Real.log (Real.sqrt n / ε) / Real.log (1 / (1 - α))⌉₊

/-- R6(iii): every stage count `m ≤ n` is at most `K(n, ε, α)`. -/
theorem stopCount_le_Kbound {α ε : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) {m : ℕ}
    (hm : m ≤ n) : stopCount α ε m ≤ Kbound α ε n := by
  unfold stopCount Kbound
  by_cases hm0 : m = 0
  · simp [hm0]
  by_cases hα : α = 1
  · simp [hm0, hα]
  · simp only [hm0, hα, if_false]
    have hg0 : 0 < 1 - α := by
      have : α < 1 := lt_of_le_of_ne hα1 hα
      linarith
    have hL : 0 < Real.log (1 / (1 - α)) := by
      apply Real.log_pos
      rw [lt_div_iff₀ hg0]; linarith
    apply Nat.ceil_mono
    apply div_le_div_of_nonneg_right _ hL.le
    have hm1 : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
    apply Real.log_le_log (by positivity)
    apply div_le_div_of_nonneg_right _ hε.le
    exact Real.sqrt_le_sqrt (by exact_mod_cast hm)

/-- R6(i) (any start): for `α < 1`, `ρ_0 > ε`, every `k ≥ ⌈log(ρ_0/ε)/log(1/γ)⌉` has
`ρ_k ≤ ε`; for `α = 1`, every `k ≥ 1`. In particular the stopping index is at most this. -/
theorem stage_count_bound {α ε : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) (hε : 0 < ε) (b : Bool)
    (a v0 : Fin n → ℝ) (k : ℕ)
    (hk : (α = 1 ∧ 1 ≤ k) ∨ (α < 1 ∧ Real.log (eN (stageR α b a v0) / ε) /
      Real.log (1 / (1 - α)) ≤ k)) (hρ : ε < eN (stageR α b a v0)) :
    eN (stageR α b a (stageIter α b a v0 k)) ≤ ε := by
  have h1 := resid_norm_iter_le hα0 hα1 b a v0 k
  rcases hk with ⟨rfl, hk1⟩ | ⟨hα, hk2⟩
  · have : (1 - 1 : ℝ) ^ k = 0 := by simp; omega
    rw [this] at h1; simp at h1
    linarith [eN_nonneg (stageR 1 b a (stageIter 1 b a v0 k))]
  · have hg0 : 0 < 1 - α := by linarith
    have hL : 0 < Real.log (1 / (1 - α)) := by
      apply Real.log_pos
      rw [lt_div_iff₀ hg0]; linarith
    have hρ0 : 0 < eN (stageR α b a v0) := by linarith
    rw [div_le_iff₀ hL] at hk2
    have : (1 - α) ^ k * eN (stageR α b a v0) ≤ ε := by
      rw [← Real.log_le_log_iff (by positivity) hε, Real.log_mul (by positivity) hρ0.ne',
        Real.log_pow, Real.log_div hρ0.ne' hε.ne', one_div, Real.log_inv] at *
      nlinarith
    linarith


end Ring

/-! ## The summed energy (section 9): cell energy, table, R9 (cell level) -/

/-- `θ = w_1/(w_1 + w_2)`. -/
noncomputable def theta (w1 w2 : ℝ) : ℝ := w1 / (w1 + w2)

/-- R8(a): the cell energy
`e^w_{l,s}(p,q,y) = (w_1/2)(p - s + 1)² + (w_2/2)(q - l - p + 1)² + (w_3/2)(y - s + p + q)²`. -/
noncomputable def cellE (w1 w2 w3 l s p q y : ℝ) : ℝ :=
  w1 / 2 * (p - s + 1) ^ 2 + w2 / 2 * (q - l - p + 1) ^ 2 + w3 / 2 * (y - s + p + q) ^ 2

/-- Table (R9): `p°` as a function of `(l, s)`. -/
noncomputable def pTab (θ l s : ℝ) : ℝ :=
  if l = 1 then (if s = 2 then 1 else 0)
  else if s = 0 then max 0 (1 - 2 * θ) else if s = 1 then 1 - θ else 1

/-- Table (R9): `q°` as a function of `(l, s)`. -/
noncomputable def qTab (l s : ℝ) : ℝ := if l = 1 ∧ s = 2 then 1 else 0

/-- Table (R9): `y°` as a function of `(l, s)`. -/
noncomputable def yTab (θ l s : ℝ) : ℝ :=
  if l = 1 then (if s = 1 then 1 else 0)
  else if s = 0 then -max 0 (1 - 2 * θ) else if s = 1 then θ else 1

/-- The cell minimum values at unit weights, `φ(l,s)`. -/
noncomputable def phi (l s : ℝ) : ℝ :=
  if l = 1 then (if s = 0 then 1 / 2 else 0) else (if s = 0 then 1 else if s = 1 then 1 / 4 else 0)

lemma theta_pos {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) : 0 < theta w1 w2 := by
  unfold theta; positivity

lemma theta_lt_one {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) : theta w1 w2 < 1 := by
  unfold theta; rw [div_lt_one (by positivity)]; linarith

lemma pTab_mem {w1 w2 l s : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hl : l = 0 ∨ l = 1)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) : 0 ≤ pTab (theta w1 w2) l s ∧ pTab (theta w1 w2) l s ≤ 1 := by
  have ht0 := theta_pos h1 h2
  have ht1 := theta_lt_one h1 h2
  rcases hl with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> norm_num [pTab]
  all_goals first
    | exact ht0.le
    | exact ht1.le
    | exact ⟨ht1.le, ht0.le⟩

lemma yTab_eq {w1 w2 l s : ℝ} (hl : l = 0 ∨ l = 1)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    yTab (theta w1 w2) l s = s - pTab (theta w1 w2) l s - qTab l s := by
  rcases hl with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp [yTab, pTab, qTab] <;>
    norm_num

lemma qTab_eq {w1 w2 l s : ℝ} (hl : l = 0 ∨ l = 1) (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    qTab l s = (if l = 1 then pTab (theta w1 w2) l s else 0) := by
  rcases hl with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp [qTab, pTab]

/-- `ψ(p)`, the one-variable problem left after eliminating `y` and `q`. -/
noncomputable def psi (w1 w2 l s p : ℝ) : ℝ := w1 / 2 * (p - s + 1) ^ 2 + (if l = 1 then 0 else w2 / 2 * (1 - p) ^ 2)

lemma psi_ge {w1 w2 l s p : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hl : l = 0 ∨ l = 1)
    (hs : s = 0 ∨ s = 1 ∨ s = 2) (hp0 : 0 ≤ p) :
    psi w1 w2 l s (pTab (theta w1 w2) l s) +
      (if l = 1 then w1 / 2 else (w1 + w2) / 2) * (p - pTab (theta w1 w2) l s) ^ 2
      ≤ psi w1 w2 l s p := by
  have hW : 0 < w1 + w2 := by linarith
  rcases hl with rfl | rfl <;> rcases hs with rfl | rfl | rfl
  · -- l = 0, s = 0
    have hv : 1 - 2 * theta w1 w2 = (w2 - w1) / (w1 + w2) := by
      unfold theta; field_simp; ring
    rcases le_total 0 (1 - 2 * theta w1 w2) with h | h
    · have hp : pTab (theta w1 w2) 0 0 = 1 - 2 * theta w1 w2 := by
        simp [pTab, max_eq_right h]
      rw [hp]; simp only [psi]; rw [hv]; simp
      field_simp; ring_nf; rfl
    · have hp : pTab (theta w1 w2) 0 0 = 0 := by simp [pTab, max_eq_left h]
      rw [hp]; simp only [psi]
      rw [hv] at h
      have h' : w2 - w1 ≤ 0 := by
        by_contra hc; rw [not_le] at hc
        have := div_pos hc hW; linarith
      simp
      nlinarith [mul_nonneg hp0 (sub_nonneg.mpr h'), mul_nonneg hp0 hp0]
  · -- l = 0, s = 1
    have hp : pTab (theta w1 w2) 0 1 = w2 / (w1 + w2) := by
      simp [pTab, theta]; field_simp; ring
    rw [hp]; simp only [psi]; simp
    field_simp; ring_nf; rfl
  · -- l = 0, s = 2
    simp [pTab, psi]; nlinarith [sq_nonneg (p - 1)]
  · simp [pTab, psi]; nlinarith [mul_nonneg h1.le hp0, mul_nonneg h1.le (mul_nonneg hp0 hp0)]
  · simp [pTab, psi]
  · simp [pTab, psi]; nlinarith [mul_nonneg h1.le (sq_nonneg (p - 1))]

/-- Step 2 of the elimination: for `p ∈ [0,1]` the `q`-term on `q ∈ [0,1]` is minimised only at
`q = clamp(l + p - 1)`, which is `p` if `l = 1` and `0` if `l = 0`. -/
lemma q_step {l p q : ℝ} (hl : l = 0 ∨ l = 1) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) :
    (if l = 1 then p else 0) |> fun qo =>
      (qo - l - p + 1) ^ 2 ≤ (q - l - p + 1) ^ 2 ∧
      ((q - l - p + 1) ^ 2 ≤ (qo - l - p + 1) ^ 2 → q = qo) := by
  rcases hl with rfl | rfl
  · simp only [zero_ne_one, if_false]
    constructor
    · nlinarith [mul_nonneg hq0 hq0, mul_nonneg hq0 (sub_nonneg.mpr hp1)]
    · intro h
      by_contra hne
      have hq : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hne)
      nlinarith [mul_pos hq hq, mul_nonneg hq.le (sub_nonneg.mpr hp1)]
  · simp only [if_true]
    constructor
    · nlinarith [sq_nonneg (q - p)]
    · intro h
      nlinarith [sq_nonneg (q - p)]

/-- R9, cell level: the table point is the unique minimiser of `e^w_{l,s}` on
`[0,1] × [0,1] × ℝ`, for all positive weights. -/
theorem cell_min {w1 w2 w3 l s p q y : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (hl : l = 0 ∨ l = 1) (hs : s = 0 ∨ s = 1 ∨ s = 2)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    cellE w1 w2 w3 l s (pTab (theta w1 w2) l s) (qTab l s) (yTab (theta w1 w2) l s) ≤
        cellE w1 w2 w3 l s p q y ∧
      (cellE w1 w2 w3 l s p q y ≤
          cellE w1 w2 w3 l s (pTab (theta w1 w2) l s) (qTab l s) (yTab (theta w1 w2) l s) →
        p = pTab (theta w1 w2) l s ∧ q = qTab l s ∧ y = yTab (theta w1 w2) l s) := by
  set po := pTab (theta w1 w2) l s with hpo
  set qo := (if l = 1 then p else 0) with hqo
  have hq := q_step hl hp1 hq0
  have hqoT : qTab l s = (if l = 1 then po else 0) := qTab_eq hl hs
  have hyT : yTab (theta w1 w2) l s = s - po - qTab l s := yTab_eq hl hs
  have hps := psi_ge h1 h2 hl hs hp0
  -- value of the table point
  have hval : cellE w1 w2 w3 l s po (qTab l s) (yTab (theta w1 w2) l s) = psi w1 w2 l s po := by
    unfold cellE psi
    rw [hyT, hqoT]
    rcases hl with rfl | rfl <;>
      simp only [zero_ne_one, ite_false, ite_true] <;> ring
  -- lower bound for an arbitrary feasible point
  have hge : psi w1 w2 l s p + w2 / 2 * ((q - l - p + 1) ^ 2 - (qo - l - p + 1) ^ 2) +
      w3 / 2 * (y - s + p + q) ^ 2 = cellE w1 w2 w3 l s p q y := by
    unfold cellE psi
    rw [hqo]
    rcases hl with rfl | rfl <;>
      simp only [zero_ne_one, ite_false, ite_true] <;> ring
  have hD2 : 0 ≤ w2 / 2 * ((q - l - p + 1) ^ 2 - (qo - l - p + 1) ^ 2) :=
    mul_nonneg (by positivity) (by linarith [hq.1])
  have hD1 : 0 ≤ w3 / 2 * (y - s + p + q) ^ 2 := by positivity
  have hc : 0 < (if l = 1 then w1 / 2 else (w1 + w2) / 2) := by
    split_ifs <;> linarith
  have hD3 : 0 ≤ (if l = 1 then w1 / 2 else (w1 + w2) / 2) * (p - po) ^ 2 := by positivity
  constructor
  · rw [hval, ← hge]; linarith
  · intro hle
    rw [hval, ← hge] at hle
    have e1 : w3 / 2 * (y - s + p + q) ^ 2 = 0 := by linarith
    have e2 : w2 / 2 * ((q - l - p + 1) ^ 2 - (qo - l - p + 1) ^ 2) = 0 := by linarith
    have e3 : (if l = 1 then w1 / 2 else (w1 + w2) / 2) * (p - po) ^ 2 = 0 := by linarith
    have hpp : p = po := by
      have := (mul_eq_zero.mp e3).resolve_left hc.ne'
      exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp this)
    have hqq : q = qo := by
      refine hq.2 ?_
      have := (mul_eq_zero.mp e2).resolve_left (by positivity)
      linarith
    have hqq' : q = qTab l s := by
      rw [hqq, hqo, hqoT, hpp]
    have hyy : y = yTab (theta w1 w2) l s := by
      have := (mul_eq_zero.mp e1).resolve_left (by positivity)
      have h0 : y - s + p + q = 0 := pow_eq_zero_iff (two_ne_zero) |>.mp this
      rw [hyT, ← hqq', ← hpp]; linarith
    exact ⟨hpp, hqq', hyy⟩

section Joint

variable {n : ℕ} [NeZero n]

/-- The summed energy `E_x^w` on `B × B × ℝⁿ` (the box indicators are the side condition
`FeasPQ`): `(w_1/2)‖ω₁‖² + (w_2/2)‖ω₂‖² + (w_3/2)‖ω₃‖²`,
`ω₁ = p - (s-1)`, `ω₂ = q - (l+p-1)`, `ω₃ = y - (s-p-q)`. -/
noncomputable def Ejoint (w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) : ℝ :=
  w1 / 2 * ∑ i, (p i - (sVec x i - 1)) ^ 2 +
  w2 / 2 * ∑ i, (q i - (lVec x i + p i - 1)) ^ 2 +
  w3 / 2 * ∑ i, (y i - (sVec x i - p i - q i)) ^ 2

/-- Feasibility of `(p, q)`: `p, q ∈ B = [0,1]ⁿ` (`y` is free). -/
def FeasPQ (p q : Fin n → ℝ) : Prop := ∀ i, 0 ≤ p i ∧ p i ≤ 1 ∧ 0 ≤ q i ∧ q i ≤ 1

/-- R8(a): cell separation. -/
theorem Ejoint_eq_sum_cell (w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) :
    Ejoint w1 w2 w3 x p q y = ∑ i, cellE w1 w2 w3 (lVec x i) (sVec x i) (p i) (q i) (y i) := by
  unfold Ejoint cellE
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The minimiser's blocks, cell by cell, from the table (R9). -/
noncomputable def pMin (w1 w2 : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => pTab (theta w1 w2) (lVec x i) (sVec x i)
noncomputable def qMin (x : Fin n → ℝ) : Fin n → ℝ := fun i => qTab (lVec x i) (sVec x i)
noncomputable def yMin (w1 w2 : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => yTab (theta w1 w2) (lVec x i) (sVec x i)

lemma lVec_range {x : Fin n → ℝ} (hx : IsBin x) (i : Fin n) : lVec x i = 0 ∨ lVec x i = 1 :=
  hx (i - 1)

lemma sVec_range {x : Fin n → ℝ} (hx : IsBin x) (i : Fin n) :
    sVec x i = 0 ∨ sVec x i = 1 ∨ sVec x i = 2 := by
  unfold sVec
  rcases hx i with h | h <;> rcases hx (i + 1) with h' | h' <;> simp [h, h'] <;> norm_num

/-- R9 (`joint_cell_table`): for every `n ≥ 1`, binary `x`, and positive weights, the table
point is feasible and is the unique minimiser of `E_x^w` on `B × B × ℝⁿ`. -/
theorem joint_cell_table {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    {x : Fin n → ℝ} (hx : IsBin x) :
    FeasPQ (pMin w1 w2 x) (qMin x) ∧
    ∀ p q y : Fin n → ℝ, FeasPQ p q →
      Ejoint w1 w2 w3 x (pMin w1 w2 x) (qMin x) (yMin w1 w2 x) ≤ Ejoint w1 w2 w3 x p q y ∧
      (Ejoint w1 w2 w3 x p q y ≤ Ejoint w1 w2 w3 x (pMin w1 w2 x) (qMin x) (yMin w1 w2 x) →
        p = pMin w1 w2 x ∧ q = qMin x ∧ y = yMin w1 w2 x) := by
  refine ⟨fun i => ?_, fun p q y hf => ?_⟩
  · have hpm := pTab_mem h1 h2 (lVec_range hx i) (sVec_range hx i)
    have hqm : 0 ≤ qTab (lVec x i) (sVec x i) ∧ qTab (lVec x i) (sVec x i) ≤ 1 := by
      unfold qTab; split_ifs <;> norm_num
    exact ⟨hpm.1, hpm.2, hqm.1, hqm.2⟩
  · have hcell := fun i => cell_min h1 h2 h3 (lVec_range hx i) (sVec_range hx i)
      (hf i).1 (hf i).2.1 (hf i).2.2.1 (hf i).2.2.2 (y := y i)
    rw [Ejoint_eq_sum_cell, Ejoint_eq_sum_cell]
    constructor
    · exact Finset.sum_le_sum fun i _ => (hcell i).1
    · intro hle
      have hge := Finset.sum_le_sum (s := Finset.univ) fun i _ => (hcell i).1
      have heq := (Finset.sum_eq_sum_iff_of_le (fun i _ => (hcell i).1)).mp (le_antisymm hge hle)
      refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
      · exact ((hcell i).2 (heq i (Finset.mem_univ i)).symm.le).1
      · exact ((hcell i).2 (heq i (Finset.mem_univ i)).symm.le).2.1
      · exact ((hcell i).2 (heq i (Finset.mem_univ i)).symm.le).2.2

/-- A bad cell: `l = 0` and `s = 1`, i.e. `(l,c,r) ∈ {(0,0,1), (0,1,0)}`. -/
def Bad (x : Fin n → ℝ) (i : Fin n) : Prop := x (i - 1) = 0 ∧ x i + x (i + 1) = 1

lemma bad_iff {x : Fin n → ℝ} (hx : IsBin x) (i : Fin n) :
    Bad x i ↔ (x (i - 1) = 0 ∧ x i = 0 ∧ x (i + 1) = 1) ∨ (x (i - 1) = 0 ∧ x i = 1 ∧ x (i + 1) = 0) := by
  unfold Bad
  rcases hx i with h | h <;> rcases hx (i + 1) with h' | h' <;> rcases hx (i - 1) with h'' | h'' <;>
    simp [h, h', h'']

/-- The y-block of the minimiser, cell by cell (R9 consequences). The hypothesis pattern used
throughout: `l = x_{i-1}`, `c = x_i`, `r = x_{i+1}`. -/
lemma max_one_sub_two_theta {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hw : w2 ≤ w1) :
    max 0 (1 - 2 * theta w1 w2) = 0 := by
  apply max_eq_left
  unfold theta
  have : 2 * (w1 / (w1 + w2)) = 2 * w1 / (w1 + w2) := by ring
  rw [this, sub_nonpos, le_div_iff₀ (by positivity)]
  linarith

/-- R9(i): for `w_1 ≥ w_2`, `y°_i = t_i(x)` unless cell `i` is bad; at a bad cell
`y°_i = θ ∈ [1/2, 1)` and `|y°_i - t_i| = w_2/(w_1+w_2) ≤ 1/2`, with equality iff `w_1 = w_2`. -/
theorem R9_i {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hw : w2 ≤ w1) {x : Fin n → ℝ}
    (hx : IsBin x) (i : Fin n) :
    (¬ Bad x i → yMin w1 w2 x i = rule110 x i) ∧
    (Bad x i → yMin w1 w2 x i = theta w1 w2 ∧ 1 / 2 ≤ theta w1 w2 ∧ theta w1 w2 < 1 ∧
      |yMin w1 w2 x i - rule110 x i| = w2 / (w1 + w2) ∧ w2 / (w1 + w2) ≤ 1 / 2 ∧
      (w2 / (w1 + w2) = 1 / 2 ↔ w1 = w2)) := by
  have hm := max_one_sub_two_theta h1 h2 hw
  have hth : theta w1 w2 + w2 / (w1 + w2) = 1 := by unfold theta; field_simp
  have hth2 : 1 / 2 ≤ theta w1 w2 := by
    unfold theta; rw [le_div_iff₀ (by positivity)]; linarith
  have hlt := theta_lt_one h1 h2
  have hiff : w2 / (w1 + w2) = 1 / 2 ↔ w1 = w2 := by
    rw [div_eq_div_iff (by positivity) (by norm_num)]; constructor <;> intro h <;> linarith
  have hle : w2 / (w1 + w2) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have habs : |theta w1 w2 - 1| = w2 / (w1 + w2) := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
  have hth2' : (2 : ℝ)⁻¹ ≤ theta w1 w2 := by simpa using hth2
  have hiff' : w2 / (w1 + w2) = (2 : ℝ)⁻¹ ↔ w1 = w2 := by simpa using hiff
  have hle' : w2 / (w1 + w2) ≤ (2 : ℝ)⁻¹ := by simpa using hle
  unfold Bad
  rcases hx (i - 1) with hl | hl <;> rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
    simp [yMin, yTab, lVec, sVec, rule110, poly110, hl, hc, hr, hm] <;>
    first
      | exact ⟨hth2', hlt, habs, hle', hiff'⟩
      | exact ⟨hth2, hlt, habs, hle, hiff⟩
      | skip

lemma theta_one : theta 1 1 = 1 / 2 := by norm_num [theta]

/-- R9(ii): for every positive weighting and every row with a bad cell, `y° ≠ t(x)`;
for `w_1 < w_2` also every cell `(0,0,0)` is inexact: `y°_i = 2θ - 1 < 0 = t_i`. -/
theorem R9_ii {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) {x : Fin n → ℝ} (hx : IsBin x) :
    ((∃ i, Bad x i) → yMin w1 w2 x ≠ rule110 x) ∧
    (w1 < w2 → ∀ i, x (i - 1) = 0 → x i = 0 → x (i + 1) = 0 →
      yMin w1 w2 x i = 2 * theta w1 w2 - 1 ∧ yMin w1 w2 x i < 0 ∧ rule110 x i = 0) := by
  have hlt := theta_lt_one h1 h2
  constructor
  · rintro ⟨i, hi⟩ heq
    have h := congrFun heq i
    obtain ⟨hl, hs⟩ := hi
    rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
      simp [yMin, lVec, sVec, rule110, poly110, yTab, hl, hc, hr] at h hs <;> linarith
  · intro hw i hl hc hr
    have hhalf : theta w1 w2 < 1 / 2 := by
      unfold theta; rw [div_lt_iff₀ (by positivity)]; linarith
    have hpos : 0 < 1 - 2 * theta w1 w2 := by linarith
    have hm : max 0 (1 - 2 * theta w1 w2) = 1 - 2 * theta w1 w2 := max_eq_right hpos.le
    simp [yMin, lVec, sVec, rule110, poly110, yTab, hl, hc, hr, hm]
    linarith

/-- R9(iii): at unit weights `y° ∈ {0, 1/2, 1}ⁿ`, and `y°_i = 1/2` exactly at the bad cells. -/
theorem R9_iii {x : Fin n → ℝ} (hx : IsBin x) (i : Fin n) :
    (yMin 1 1 x i = 0 ∨ yMin 1 1 x i = 1 / 2 ∨ yMin 1 1 x i = 1) ∧
    (yMin 1 1 x i = 1 / 2 ↔ Bad x i) := by
  have hm : max 0 (1 - 2 * theta 1 1) = 0 := by rw [theta_one]; norm_num
  unfold Bad
  rcases hx (i - 1) with hl | hl <;> rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
    simp [yMin, lVec, sVec, yTab, hl, hc, hr, hm, theta_one] <;> norm_num

/-- R9(iv): for `w_1 ≥ w_2` the cascade point `(p*, q*, t(x))` of R5 equals the minimiser iff
`x` has no bad cell. -/
theorem R9_iv {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hw : w2 ≤ w1) {x : Fin n → ℝ}
    (hx : IsBin x) :
    (pMin w1 w2 x = (fun i => x i * x (i + 1)) ∧
      qMin x = (fun i => x (i - 1) * x i * x (i + 1)) ∧
      yMin w1 w2 x = rule110 x) ↔ ∀ i, ¬ Bad x i := by
  have hm := max_one_sub_two_theta h1 h2 hw
  have hlt := theta_lt_one h1 h2
  constructor
  · rintro ⟨-, -, hy⟩ i hi
    exact (R9_ii h1 h2 hx).1 ⟨i, hi⟩ hy
  · intro hb
    refine ⟨funext fun i => ?_, funext fun i => ?_, funext fun i => ?_⟩
    · have := hb i
      unfold Bad at this
      rcases hx (i - 1) with hl | hl <;> rcases hx i with hc | hc <;>
        rcases hx (i + 1) with hr | hr <;>
        simp [pMin, lVec, sVec, pTab, hl, hc, hr, hm] at this ⊢ <;> norm_num
    · rcases hx (i - 1) with hl | hl <;> rcases hx i with hc | hc <;>
        rcases hx (i + 1) with hr | hr <;>
        simp [qMin, lVec, sVec, qTab, hl, hc, hr] <;> norm_num
    · exact (R9_i h1 h2 hw hx i).1 (hb i)

/-- The four zero-cost neighbourhoods `(1,0,1), (1,1,0), (0,1,1), (1,1,1)`. -/
def GoodNb (l c r : ℝ) : Prop :=
  (l = 1 ∧ c = 0 ∧ r = 1) ∨ (l = 1 ∧ c = 1 ∧ r = 0) ∨ (l = 0 ∧ c = 1 ∧ r = 1) ∨
    (l = 1 ∧ c = 1 ∧ r = 1)

lemma cellE_unit_tab {l s : ℝ} (hl : l = 0 ∨ l = 1) (hs : s = 0 ∨ s = 1 ∨ s = 2) :
    cellE 1 1 1 l s (pTab (theta 1 1) l s) (qTab l s) (yTab (theta 1 1) l s) = phi l s := by
  have hm : max 0 (1 - 2 * theta 1 1) = 0 := by rw [theta_one]; norm_num
  rcases hl with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;>
    simp [cellE, phi, pTab, qTab, yTab, hm, theta_one] <;> norm_num

lemma phi_nonneg {l s : ℝ} (hl : l = 0 ∨ l = 1) (hs : s = 0 ∨ s = 1 ∨ s = 2) : 0 ≤ phi l s := by
  rcases hl with rfl | rfl <;> rcases hs with rfl | rfl | rfl <;> simp [phi] <;> norm_num

/-- R9(v): at unit weights `min E_x = ∑_i φ(l_i, s_i)`, which is `0` iff every cell has
`(l,c,r) ∈ {(1,0,1), (1,1,0), (0,1,1), (1,1,1)}`. -/
theorem R9_v {x : Fin n → ℝ} (hx : IsBin x) :
    Ejoint 1 1 1 x (pMin 1 1 x) (qMin x) (yMin 1 1 x) = ∑ i, phi (lVec x i) (sVec x i) ∧
    ((∑ i, phi (lVec x i) (sVec x i) = 0) ↔ ∀ i, GoodNb (x (i - 1)) (x i) (x (i + 1))) := by
  constructor
  · rw [Ejoint_eq_sum_cell]
    exact Finset.sum_congr rfl fun i _ => cellE_unit_tab (lVec_range hx i) (sVec_range hx i)
  · rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => phi_nonneg (lVec_range hx i) (sVec_range hx i))]
    constructor
    · intro h i
      have := h i (Finset.mem_univ i)
      unfold GoodNb
      rcases hx (i - 1) with hl | hl <;> rcases hx i with hc | hc <;>
        rcases hx (i + 1) with hr | hr <;>
        simp [phi, lVec, sVec, hl, hc, hr] at this ⊢ <;> norm_num at this ⊢
    · intro h i _
      have := h i
      unfold GoodNb at this
      rcases this with ⟨hl, hc, hr⟩ | ⟨hl, hc, hr⟩ | ⟨hl, hc, hr⟩ | ⟨hl, hc, hr⟩ <;>
        simp [phi, lVec, sVec, hl, hc, hr] <;> norm_num

/-! ### R11: what the minimiser reads out to -/

lemma rdT_bin {τ b : ℝ} (hb : b = 0 ∨ b = 1) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    (if τ ≤ b then (1 : ℝ) else 0) = b := by
  rcases hb with rfl | rfl
  · simp [not_le.mpr hτ0]
  · simp [hτ1]

lemma rule110_bad {x : Fin n → ℝ} (hx : IsBin x) {i : Fin n} (hi : Bad x i) : rule110 x i = 1 := by
  obtain ⟨hl, hs⟩ := hi
  rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
    simp [rule110, poly110, hl, hc, hr] <;> simp [hc, hr] at hs

/-- R11(a): for every positive weighting and every row with a bad cell, the minimiser's
y-block is not the next row. -/
theorem R11_a {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) {x : Fin n → ℝ} (hx : IsBin x)
    (hbad : ∃ i, Bad x i) : yMin w1 w2 x ≠ rule110 x :=
  (R9_ii h1 h2 hx).1 hbad

/-- R11(b): at unit weights, a bad cell `i` has `y°_i = 1/2`, read-out margin `0`, and for
every `ρ > 0` and every `ℓ_p` norm (`p ∈ [1,∞]`) the ball of radius `ρ` about `y°` contains
points `u⁺, u⁻` with `u⁺_i > 1/2 > u⁻_i` (so `rd01(u⁺)_i = 1`, `rd01(u⁻)_i = 0`, for the
ties-up convention and for the strict one alike). -/
theorem R11_b {x : Fin n → ℝ} (hx : IsBin x) {i : Fin n} (hi : Bad x i) :
    yMin 1 1 x i = 1 / 2 ∧ marg (1 / 2) (yMin 1 1 x) = 0 ∧
    ∀ (p : ENNReal) [Fact (1 ≤ p)] (ρ : ℝ), 0 < ρ →
      ∃ up um : Fin n → ℝ,
        ‖WithLp.toLp p (up - yMin 1 1 x)‖ < ρ ∧ ‖WithLp.toLp p (um - yMin 1 1 x)‖ < ρ ∧
        1 / 2 < up i ∧ um i < 1 / 2 ∧ rdT (1 / 2) up i = 1 ∧ rdT (1 / 2) um i = 0 := by
  have hy : yMin 1 1 x i = 1 / 2 := ((R9_iii hx i).2).mpr hi
  refine ⟨hy, ?_, ?_⟩
  · apply le_antisymm
    · have := marg_le (1 / 2) (yMin 1 1 x) i
      rw [hy, sub_self, abs_zero] at this
      exact this
    · exact le_marg fun j => abs_nonneg _
  · intro p _ ρ hρ
    refine ⟨yMin 1 1 x + Pi.single i (ρ / 2), yMin 1 1 x + Pi.single i (-(ρ / 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [add_sub_cancel_left, OCF.C6.norm_single_lp, abs_of_pos (by linarith)]; linarith
    · rw [add_sub_cancel_left, OCF.C6.norm_single_lp, abs_neg, abs_of_pos (by linarith)]; linarith
    · simp [hy]; linarith
    · simp [hy]; linarith
    · simp [rdT, hy]; linarith
    · simp [rdT, hy]; linarith

/-- R11(c), `w_1 > w_2`: `rd_{1/2}(y°) = t(x)`, with margin `μ_w = (w_1 - w_2)/(2(w_1+w_2))`
at the bad cells (and `1/2` elsewhere). -/
theorem R11_c_gt {w1 w2 : ℝ} (h2 : 0 < w2) (hw : w2 < w1) {x : Fin n → ℝ} (hx : IsBin x) :
    rdT (1 / 2) (yMin w1 w2 x) = rule110 x ∧
    (∀ i, (w1 - w2) / (2 * (w1 + w2)) ≤ |yMin w1 w2 x i - 1 / 2|) ∧
    (∀ i, Bad x i → |yMin w1 w2 x i - 1 / 2| = (w1 - w2) / (2 * (w1 + w2))) ∧
    (∀ i, ¬ Bad x i → |yMin w1 w2 x i - 1 / 2| = 1 / 2) := by
  have h1 : 0 < w1 := by linarith
  have hμ : theta w1 w2 - 1 / 2 = (w1 - w2) / (2 * (w1 + w2)) := by
    unfold theta; field_simp; ring
  have hμpos : 0 < (w1 - w2) / (2 * (w1 + w2)) := by apply div_pos <;> linarith
  have hμle : (w1 - w2) / (2 * (w1 + w2)) ≤ 1 / 2 := by
    rw [← hμ]; linarith [theta_lt_one h1 h2]
  have hbadabs : ∀ i, Bad x i → |yMin w1 w2 x i - 1 / 2| = (w1 - w2) / (2 * (w1 + w2)) := by
    intro i hi
    have := (R9_i h1 h2 hw.le hx i).2 hi
    rw [this.1, abs_of_nonneg (by linarith [this.2.1]), hμ]
  have hnb : ∀ i, ¬ Bad x i → |yMin w1 w2 x i - 1 / 2| = 1 / 2 := by
    intro i hi
    rw [(R9_i h1 h2 hw.le hx i).1 hi]
    rcases rule110_bin hx i with h | h <;> rw [h] <;> norm_num
  refine ⟨funext fun i => ?_, fun i => ?_, hbadabs, hnb⟩
  · by_cases hi : Bad x i
    · have := (R9_i h1 h2 hw.le hx i).2 hi
      simp only [rdT, this.1]
      rw [if_pos this.2.1, rule110_bad hx hi]
    · simp only [rdT, (R9_i h1 h2 hw.le hx i).1 hi]
      exact rdT_bin (rule110_bin hx i) (by norm_num) (by norm_num)
  · by_cases hi : Bad x i
    · rw [hbadabs i hi]
    · rw [hnb i hi]; exact hμle

/-- R11(c), `w_1 = w_2`: the read-out margin at a bad cell is `0`. -/
theorem R11_c_eq {w : ℝ} (hw : 0 < w) {x : Fin n → ℝ} (hx : IsBin x) {i : Fin n}
    (hi : Bad x i) : |yMin w w x i - 1 / 2| = 0 ∧ marg (1 / 2) (yMin w w x) = 0 := by
  have h := (R9_i hw hw le_rfl hx i).2 hi
  have hth : theta w w = 1 / 2 := by
    unfold theta; rw [div_eq_div_iff (by positivity) (by norm_num)]; ring
  have h0 : |yMin w w x i - 1 / 2| = 0 := by rw [h.1, hth]; norm_num
  refine ⟨h0, le_antisymm ?_ (le_marg fun j => abs_nonneg _)⟩
  have := marg_le (1 / 2) (yMin w w x) i
  rwa [h0] at this

/-- R11(c), `w_1 = w_2`: the ties-up threshold-`1/2` read-out of the minimiser still equals
`t(x)` on every row (the margin is `0` at a bad cell by `R11_c_eq`, so no certified distance bound
determines it). -/
theorem R11_c_eq_readout {w : ℝ} (hw : 0 < w) {x : Fin n → ℝ} (hx : IsBin x) :
    rdT (1 / 2) (yMin w w x) = rule110 x := by
  funext i
  by_cases hi : Bad x i
  · have := (R9_i hw hw le_rfl hx i).2 hi
    simp only [rdT, this.1]
    rw [if_pos this.2.1, rule110_bad hx hi]
  · simp only [rdT, (R9_i hw hw le_rfl hx i).1 hi]
    exact rdT_bin (rule110_bin hx i) (by norm_num) (by norm_num)

/-- R11(c), `w_1 < w_2`: at every bad cell `rd_{1/2}(y°)_i = 0 ≠ 1 = t_i`. -/
theorem R11_c_lt {w1 w2 : ℝ} (h1 : 0 < w1) (hw : w1 < w2) {x : Fin n → ℝ} (hx : IsBin x)
    {i : Fin n} (hi : Bad x i) : rdT (1 / 2) (yMin w1 w2 x) i = 0 ∧ rule110 x i = 1 := by
  have h2 : 0 < w2 := by linarith
  refine ⟨?_, rule110_bad hx hi⟩
  have hy : yMin w1 w2 x i = theta w1 w2 := by
    obtain ⟨hl, hs⟩ := hi
    rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
      simp [yMin, lVec, sVec, yTab, hl, hc, hr] <;> simp [hc, hr] at hs
  have hhalf : theta w1 w2 < 1 / 2 := by
    unfold theta; rw [div_lt_iff₀ (by positivity)]; linarith
  simp only [rdT, hy]
  rw [if_neg (by linarith)]

/-- A row with a bad cell exists for every `n ≥ 2`: `x = e_0`, whose cell `0` is `(0,1,0)`. -/
theorem bad_row_exists (hn : 2 ≤ n) : ∃ x : Fin n → ℝ, IsBin x ∧ ∃ i, Bad x i := by
  have h1 : (1 : Fin n) ≠ 0 := by
    intro h
    have := Fin.one_eq_zero_iff.mp h
    omega
  have h2 : (0 : Fin n) - 1 ≠ 0 := by
    intro h
    exact h1 (by simpa using h)
  refine ⟨Pi.single 0 1, fun i => ?_, 0, ?_⟩
  · by_cases hi : i = 0
    · subst hi; right; simp
    · left; simp [hi]
  · unfold Bad
    simp [Pi.single_apply, h1, h2]

/-- R11(c) quantifier: the threshold-`1/2` read-out of the minimiser with a strict margin is
available on every row of every length iff `w_1 > w_2`. -/
theorem R11_c_iff {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) :
    (∀ (m : ℕ) [NeZero m] (x : Fin m → ℝ), IsBin x →
      rdT (1 / 2) (yMin w1 w2 x) = rule110 x ∧ 0 < marg (1 / 2) (yMin w1 w2 x)) ↔ w2 < w1 := by
  constructor
  · intro H
    by_contra hnot
    have hle : w1 ≤ w2 := not_lt.mp hnot
    haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
    obtain ⟨x, hx, i, hi⟩ := bad_row_exists (n := 2) le_rfl
    obtain ⟨hr, hm⟩ := H 2 x hx
    rcases lt_or_eq_of_le hle with hlt | heq
    · have := R11_c_lt h1 hlt hx hi
      have h3 := congrFun hr i
      rw [this.1, this.2] at h3
      norm_num at h3
    · subst heq
      have := (R11_c_eq h1 hx hi).2
      linarith
  · intro hw m _ x hx
    obtain ⟨hr, hm1, hm2, hm3⟩ := R11_c_gt h2 hw hx
    refine ⟨hr, ?_⟩
    have hμ : 0 < (w1 - w2) / (2 * (w1 + w2)) := by apply div_pos <;> linarith
    exact lt_of_lt_of_le hμ (le_marg hm1)

/-- R11(d): for `w_1 ≥ w_2`, `rd_{1/4}(y°) = t(x)` with `min_i |y°_i - 1/4| ≥ 1/4`; at unit
weights the margin is exactly `1/4` on every row with a bad cell (the equality at every
`w_1 ≥ w_2` on rows with a cell of type (1,0), (1,2), (0,0) is `R11_d_margin_eq`). Consequently
`rd_{1/4}(u) = t(x)` whenever `‖u - y°‖_p < 1/4` (every `ℓ_p`, `p ∈ [1,∞]`), in particular
for the Euclidean norm. -/
theorem R11_d {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hw : w2 ≤ w1) {x : Fin n → ℝ}
    (hx : IsBin x) :
    rdT (1 / 4) (yMin w1 w2 x) = rule110 x ∧
    (∀ i, 1 / 4 ≤ |yMin w1 w2 x i - 1 / 4|) ∧
    (w1 = w2 → ∀ i, Bad x i → |yMin w1 w2 x i - 1 / 4| = 1 / 4) ∧
    (w1 = w2 → (∃ i, Bad x i) → marg (1 / 4) (yMin w1 w2 x) = 1 / 4) ∧
    (∀ (p : ENNReal) [Fact (1 ≤ p)] (u : Fin n → ℝ),
      ‖WithLp.toLp p (u - yMin w1 w2 x)‖ < 1 / 4 → rdT (1 / 4) u = rule110 x) ∧
    (∀ u : Fin n → ℝ, eN (u - yMin w1 w2 x) < 1 / 4 → rdT (1 / 4) u = rule110 x) := by
  have hbadv : ∀ i, Bad x i → yMin w1 w2 x i = theta w1 w2 ∧ 1 / 2 ≤ theta w1 w2 :=
    fun i hi => by have := (R9_i h1 h2 hw hx i).2 hi; exact ⟨this.1, this.2.1⟩
  have hnb : ∀ i, ¬ Bad x i → yMin w1 w2 x i = rule110 x i := fun i hi => (R9_i h1 h2 hw hx i).1 hi
  have hrd : rdT (1 / 4) (yMin w1 w2 x) = rule110 x := by
    funext i
    by_cases hi : Bad x i
    · obtain ⟨e1, e2⟩ := hbadv i hi
      simp only [rdT, e1]
      rw [if_pos (by linarith), rule110_bad hx hi]
    · simp only [rdT, hnb i hi]
      exact rdT_bin (rule110_bin hx i) (by norm_num) (by norm_num)
  have hge : ∀ i, 1 / 4 ≤ |yMin w1 w2 x i - 1 / 4| := by
    intro i
    by_cases hi : Bad x i
    · obtain ⟨e1, e2⟩ := hbadv i hi
      rw [e1, abs_of_nonneg (by linarith)]; linarith
    · rw [hnb i hi]
      rcases rule110_bin hx i with h | h <;> rw [h] <;> norm_num
  have hmarg : 1 / 4 ≤ marg (1 / 4) (yMin w1 w2 x) := le_marg hge
  have hth : w1 = w2 → theta w1 w2 = 1 / 2 := by
    intro h; subst h; unfold theta
    rw [div_eq_div_iff (by positivity) (by norm_num)]; ring
  refine ⟨hrd, hge, ?_, ?_, ?_, ?_⟩
  · intro h i hi
    obtain ⟨e1, e2⟩ := hbadv i hi
    rw [e1, hth h]; norm_num
  · intro h ⟨i, hi⟩
    refine le_antisymm ?_ hmarg
    have := marg_le (1 / 4) (yMin w1 w2 x) i
    obtain ⟨e1, e2⟩ := hbadv i hi
    rw [e1, hth h] at this
    norm_num at this
    exact this
  · intro p _ u hu
    rw [readout_threshold p (1 / 4) (yMin w1 w2 x) u (lt_of_lt_of_le hu hmarg), hrd]
  · intro u hu
    rw [readout_threshold_eN (1 / 4) (yMin w1 w2 x) u (m := 1 / 4) hge hu, hrd]

/-- Cell types `(l,s) = (1,0), (1,2), (0,0)` of the dossier (R11(d)): the cells at which
`y°_i = 0` for every `w_1 ≥ w_2`. -/
def ZeroCell (x : Fin n → ℝ) (i : Fin n) : Prop :=
  (x (i - 1) = 1 ∧ x i + x (i + 1) = 0) ∨ (x (i - 1) = 1 ∧ x i + x (i + 1) = 2) ∨
    (x (i - 1) = 0 ∧ x i + x (i + 1) = 0)

/-- R11(d), `y°_i = 0` at the cells of `ZeroCell`, for every `w_1 ≥ w_2`. -/
lemma yMin_zeroCell {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hw : w2 ≤ w1)
    {x : Fin n → ℝ} {i : Fin n} (hz : ZeroCell x i) : yMin w1 w2 x i = 0 := by
  have hm := max_one_sub_two_theta h1 h2 hw
  rcases hz with ⟨hl, hs⟩ | ⟨hl, hs⟩ | ⟨hl, hs⟩ <;>
    simp [yMin, yTab, lVec, sVec, hl, hs, hm]

/-- R11(d), equality statement (corrected wording): at EVERY weighting with `w_1 ≥ w_2`, the
threshold-`1/4` margin is exactly `1/4` at each cell of type `(1,0)`, `(1,2)`, `(0,0)`, hence on
every row containing such a cell. (At unit weights the bad cells give the same value; that is the
`w1 = w2` conjuncts of `R11_d`.) -/
theorem R11_d_margin_eq {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (hw : w2 ≤ w1)
    {x : Fin n → ℝ} (hx : IsBin x) :
    (∀ i, ZeroCell x i → |yMin w1 w2 x i - 1 / 4| = 1 / 4) ∧
    ((∃ i, ZeroCell x i) → marg (1 / 4) (yMin w1 w2 x) = 1 / 4) := by
  have hz : ∀ i, ZeroCell x i → |yMin w1 w2 x i - 1 / 4| = 1 / 4 := by
    intro i hi
    rw [yMin_zeroCell h1 h2 hw hi]; norm_num
  refine ⟨hz, fun ⟨i, hi⟩ => le_antisymm ?_ (le_marg (R11_d h1 h2 hw hx).2.1)⟩
  have := marg_le (1 / 4) (yMin w1 w2 x) i
  rwa [hz i hi] at this

/-- At a bad cell, `y°_i = θ` for every positive weighting. -/
lemma yMin_bad {w1 w2 : ℝ} {x : Fin n → ℝ} (hx : IsBin x) {i : Fin n} (hi : Bad x i) :
    yMin w1 w2 x i = theta w1 w2 := by
  obtain ⟨hl, hs⟩ := hi
  rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
    simp [yMin, lVec, sVec, yTab, hl, hc, hr] <;> simp [hc, hr] at hs

/-- Per-cell bounds for every positive weighting (R9 table): cells with `t_i = 0` have
`y°_i ≤ 0`; cells with `t_i = 1` have `y°_i ≥ θ`. -/
lemma yMin_cell_bounds {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) {x : Fin n → ℝ} (hx : IsBin x)
    (i : Fin n) :
    (rule110 x i = 0 → yMin w1 w2 x i ≤ 0) ∧ (rule110 x i = 1 → theta w1 w2 ≤ yMin w1 w2 x i) := by
  have hlt := theta_lt_one h1 h2
  have hpos := theta_pos h1 h2
  have hmx : 0 ≤ max 0 (1 - 2 * theta w1 w2) := le_max_left _ _
  rcases hx (i - 1) with hl | hl <;> rcases hx i with hc | hc <;> rcases hx (i + 1) with hr | hr <;>
    simp [yMin, lVec, sVec, rule110, poly110, yTab, hl, hc, hr] <;> first | linarith | skip

/-- R11(f): for EVERY positive weighting `w` and every row, the threshold-`θ/2` read-out of the
minimiser's y-block is `t(x)` with margin `≥ θ/2`, `θ = w_1/(w_1+w_2)`; consequently
`rd_{θ/2}(u) = t(x)` whenever `‖u - y°‖_p < θ/2` (every `ℓ_p`, and the Euclidean norm). -/
theorem R11_f {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) {x : Fin n → ℝ} (hx : IsBin x) :
    rdT (theta w1 w2 / 2) (yMin w1 w2 x) = rule110 x ∧
    (∀ i, theta w1 w2 / 2 ≤ |yMin w1 w2 x i - theta w1 w2 / 2|) ∧
    theta w1 w2 / 2 ≤ marg (theta w1 w2 / 2) (yMin w1 w2 x) ∧
    (∀ (p : ENNReal) [Fact (1 ≤ p)] (u : Fin n → ℝ),
      ‖WithLp.toLp p (u - yMin w1 w2 x)‖ < theta w1 w2 / 2 →
        rdT (theta w1 w2 / 2) u = rule110 x) ∧
    (∀ u : Fin n → ℝ, eN (u - yMin w1 w2 x) < theta w1 w2 / 2 →
        rdT (theta w1 w2 / 2) u = rule110 x) := by
  have hpos := theta_pos h1 h2
  have hlt := theta_lt_one h1 h2
  have hrd : rdT (theta w1 w2 / 2) (yMin w1 w2 x) = rule110 x := by
    funext i
    obtain ⟨hb0, hb1⟩ := yMin_cell_bounds h1 h2 hx i
    rcases rule110_bin hx i with h | h
    · have := hb0 h
      simp only [rdT, h]; rw [if_neg (by linarith)]
    · have := hb1 h
      simp only [rdT, h]; rw [if_pos (by linarith)]
  have hge : ∀ i, theta w1 w2 / 2 ≤ |yMin w1 w2 x i - theta w1 w2 / 2| := by
    intro i
    obtain ⟨hb0, hb1⟩ := yMin_cell_bounds h1 h2 hx i
    rcases rule110_bin hx i with h | h
    · have := hb0 h
      rw [abs_of_nonpos (by linarith)]; linarith
    · have := hb1 h
      rw [abs_of_nonneg (by linarith)]; linarith
  have hmarg := le_marg hge
  refine ⟨hrd, hge, hmarg, ?_, ?_⟩
  · intro p _ u hu
    rw [readout_threshold p _ (yMin w1 w2 x) u (lt_of_lt_of_le hu hmarg), hrd]
  · intro u hu
    rw [readout_threshold_eN _ (yMin w1 w2 x) u (m := theta w1 w2 / 2) hge hu, hrd]

/-- R11(f), admissible thresholds: `rd_τ(y°) = t(x)` on every row of every length iff
`0 < τ ≤ θ` (ties up at `τ = θ`). -/
theorem R11_f_thresholds {w1 w2 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (τ : ℝ) :
    (∀ (m : ℕ) [NeZero m] (x : Fin m → ℝ), IsBin x → rdT τ (yMin w1 w2 x) = rule110 x) ↔
      (0 < τ ∧ τ ≤ theta w1 w2) := by
  have hpos := theta_pos h1 h2
  constructor
  · intro H
    constructor
    · by_contra hτ
      have hτ' : τ ≤ 0 := not_lt.mp hτ
      -- the row (1) on a ring of one cell: cell type (1,2), y° = 0, t = 0
      haveI : NeZero (1 : ℕ) := ⟨by norm_num⟩
      have hx : IsBin (fun _ : Fin 1 => (1 : ℝ)) := fun _ => Or.inr rfl
      have h := congrFun (H 1 (fun _ => 1) hx) 0
      have hy : yMin w1 w2 (fun _ : Fin 1 => (1 : ℝ)) 0 = 0 := by
        simp [yMin, yTab, lVec, sVec]
      have ht : rule110 (fun _ : Fin 1 => (1 : ℝ)) 0 = 0 := by
        simp [rule110, poly110]
      simp only [rdT, hy, ht] at h
      rw [if_pos hτ'] at h
      norm_num at h
    · by_contra hτ
      have hτ' : theta w1 w2 < τ := not_le.mp hτ
      haveI : NeZero (2 : ℕ) := ⟨by norm_num⟩
      obtain ⟨x, hx, i, hi⟩ := bad_row_exists (n := 2) le_rfl
      have h := congrFun (H 2 x hx) i
      simp only [rdT, yMin_bad hx hi, rule110_bad hx hi] at h
      rw [if_neg (not_le.mpr hτ')] at h
      norm_num at h
  · rintro ⟨hτ0, hτ1⟩ m _ x hx
    funext i
    obtain ⟨hb0, hb1⟩ := yMin_cell_bounds h1 h2 hx i
    rcases rule110_bin hx i with h | h
    · have := hb0 h
      simp only [rdT, h]; rw [if_neg (by linarith)]
    · have := hb1 h
      simp only [rdT, h]; rw [if_pos (by linarith)]

/-! ### R10 (witnesses) and R11(e) (sharpness) -/

/-- The row `x = (0,0,1,1,1)` on the ring of 5 cells (R10(i)). -/
def x5 : Fin 5 → ℝ := ![0, 0, 1, 1, 1]

lemma x5_bin : IsBin x5 := by
  intro i; fin_cases i <;> simp [x5]

lemma pMin_x5 : pMin 1 1 x5 = ![0, 1 / 2, 1, 1, 0] := by
  funext i
  fin_cases i <;> simp [pMin, pTab, lVec, sVec, x5, theta_one] <;> norm_num

lemma qMin_x5 : qMin x5 = ![0, 0, 0, 1, 0] := by
  funext i
  fin_cases i <;> simp [qMin, qTab, lVec, sVec, x5] <;> norm_num

lemma yMin_x5 : yMin 1 1 x5 = ![0, 1 / 2, 1, 0, 1] := by
  funext i
  fin_cases i <;> simp [yMin, yTab, lVec, sVec, x5, theta_one] <;> norm_num

lemma rule110_x5 : rule110 x5 = ![0, 1, 1, 0, 1] := by
  funext i
  fin_cases i <;> simp [rule110, poly110, x5] <;> norm_num

lemma bad_x5 (i : Fin 5) : Bad x5 i ↔ i = 1 := by
  fin_cases i <;> simp [Bad, x5] <;> norm_num

lemma marg_eq_of {τ m : ℝ} {y : Fin n → ℝ} (h1 : ∀ i, m ≤ |y i - τ|) (h2 : ∃ i, |y i - τ| = m) :
    marg τ y = m := by
  obtain ⟨i, hi⟩ := h2
  exact le_antisymm ((marg_le τ y i).trans hi.le) (le_marg h1)

/-- R10(i): `n = 5`, `x = (0,0,1,1,1)`, unit weights. The unique minimiser is
`p° = (0,1/2,1,1,0)`, `q° = (0,0,0,1,0)`, `y° = (0,1/2,1,0,1)`, `min E_x = 3/4`; the only bad
cell is cell `1` (0-indexed; "cell 2" of the dossier); `‖y° - t(x)‖_∞ = 1/2`, attained at that
cell only; the threshold-`1/2` margin is `0` and the threshold-`1/4` margin is `1/4`. -/
theorem R10_i :
    (∀ p q y : Fin 5 → ℝ, FeasPQ p q →
      3 / 4 ≤ Ejoint 1 1 1 x5 p q y ∧
      (Ejoint 1 1 1 x5 p q y ≤ 3 / 4 →
        p = ![0, 1 / 2, 1, 1, 0] ∧ q = ![0, 0, 0, 1, 0] ∧ y = ![0, 1 / 2, 1, 0, 1])) ∧
    FeasPQ (![0, 1 / 2, 1, 1, 0] : Fin 5 → ℝ) ![0, 0, 0, 1, 0] ∧
    rule110 x5 = ![0, 1, 1, 0, 1] ∧
    (∀ i, Bad x5 i ↔ i = 1) ∧
    (∀ i, |yMin 1 1 x5 i - rule110 x5 i| ≤ 1 / 2) ∧ |yMin 1 1 x5 1 - rule110 x5 1| = 1 / 2 ∧
    (∀ i, i ≠ 1 → yMin 1 1 x5 i = rule110 x5 i) ∧
    marg (1 / 2) (yMin 1 1 x5) = 0 ∧ marg (1 / 4) (yMin 1 1 x5) = 1 / 4 := by
  have hE : Ejoint 1 1 1 x5 (pMin 1 1 x5) (qMin x5) (yMin 1 1 x5) = 3 / 4 := by
    rw [Ejoint_eq_sum_cell]
    simp only [Fin.sum_univ_five, pMin_x5, qMin_x5, yMin_x5]
    simp [cellE, lVec, sVec, x5]
    norm_num
  obtain ⟨hf, hmin⟩ := joint_cell_table (w1 := 1) (w2 := 1) (w3 := 1) one_pos one_pos one_pos x5_bin
  refine ⟨fun p q y hpq => ?_, ?_, rule110_x5, bad_x5, ?_, ?_, ?_, ?_, ?_⟩
  · have := hmin p q y hpq
    rw [hE, pMin_x5, qMin_x5, yMin_x5] at this
    exact this
  · rw [← pMin_x5, ← qMin_x5]; exact hf
  · intro i; rw [yMin_x5, rule110_x5]; fin_cases i <;> simp <;> norm_num
  · rw [yMin_x5, rule110_x5]; simp; norm_num
  · intro i hi; rw [yMin_x5, rule110_x5]; fin_cases i <;> simp at hi ⊢
  · exact marg_eq_of (fun i => by rw [yMin_x5]; fin_cases i <;> simp <;> norm_num)
      ⟨1, by rw [yMin_x5]; simp⟩
  · exact marg_eq_of (fun i => by rw [yMin_x5]; fin_cases i <;> simp <;> norm_num)
      ⟨0, by rw [yMin_x5]; simp⟩

/-- R11(e): on the row of R10(i) the thresholds `τ` with `rd_τ(y°) = t(x)` are exactly
`τ ∈ (0, 1/2]`; the read-out margin there is `min(τ, 1/2 - τ)`, so its largest value is
`1/4`, attained only at `τ = 1/4`. -/
theorem R11_e :
    (∀ τ : ℝ, rdT τ (yMin 1 1 x5) = rule110 x5 ↔ 0 < τ ∧ τ ≤ 1 / 2) ∧
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → marg τ (yMin 1 1 x5) = min τ (1 / 2 - τ)) ∧
    (∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → marg τ (yMin 1 1 x5) ≤ 1 / 4 ∧
      (marg τ (yMin 1 1 x5) = 1 / 4 → τ = 1 / 4)) ∧
    marg (1 / 4) (yMin 1 1 x5) = 1 / 4 := by
  have hmarg : ∀ τ : ℝ, 0 < τ → τ ≤ 1 / 2 → marg τ (yMin 1 1 x5) = min τ (1 / 2 - τ) := by
    intro τ h0 h1
    have e0 : |(0 : ℝ) - τ| = τ := by rw [zero_sub, abs_neg, abs_of_pos h0]
    have e1 : |(1 : ℝ) / 2 - τ| = 1 / 2 - τ := abs_of_nonneg (by linarith)
    have e2 : |(1 : ℝ) - τ| = 1 - τ := abs_of_nonneg (by linarith)
    rw [yMin_x5]
    apply marg_eq_of
    · intro i
      have m1 : min τ (1 / 2 - τ) ≤ τ := min_le_left _ _
      have m2 : min τ (1 / 2 - τ) ≤ 1 / 2 - τ := min_le_right _ _
      fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val, Fin.isValue] <;>
        first | (rw [e0]; exact m1) | (rw [e1]; exact m2) | (rw [e2]; linarith)
    · rcases min_choice τ (1 / 2 - τ) with h | h
      · exact ⟨0, by show |(0 : ℝ) - τ| = _; rw [e0, h]⟩
      · exact ⟨1, by show |(1 : ℝ) / 2 - τ| = _; rw [e1, h]⟩
  refine ⟨?_, hmarg, ?_, ?_⟩
  · intro τ
    constructor
    · intro h
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      rw [yMin_x5, rule110_x5] at h0 h1
      simp [rdT] at h0 h1
      exact ⟨h0, by rw [one_div]; exact h1⟩
    · rintro ⟨h0, h1⟩
      rw [yMin_x5, rule110_x5]
      funext i
      fin_cases i <;> simp [rdT] <;> first | linarith | skip
  · intro τ h0 h1
    rw [hmarg τ h0 h1]
    refine ⟨?_, fun h => ?_⟩
    · rcases le_total τ (1 / 2 - τ) with h' | h'
      · rw [min_eq_left h']; linarith
      · rw [min_eq_right h']; linarith
    · rcases le_total τ (1 / 2 - τ) with h' | h'
      · rw [min_eq_left h'] at h; exact h
      · rw [min_eq_right h'] at h; linarith
  · rw [hmarg (1 / 4) (by norm_num) (by norm_num)]; norm_num

/-- The single-cell row `x = (0)` (`n = 1`, `(l,c,r) = (0,0,0)`). -/
def x1 : Fin 1 → ℝ := fun _ => 0

/-- R10(iii): `n = 1`, `x = (0)`, unit weights: the unique minimiser is `(0,0,0)`, which is
the cascade point `(p*, q*, t(x))`, and `min E_x = 1 > 0`. -/
theorem R10_iii :
    IsBin x1 ∧
    (∀ p q y : Fin 1 → ℝ, FeasPQ p q →
      1 ≤ Ejoint 1 1 1 x1 p q y ∧
      (Ejoint 1 1 1 x1 p q y ≤ 1 → p = 0 ∧ q = 0 ∧ y = 0)) ∧
    ((fun i => x1 i * x1 (i + 1)) = 0 ∧ (fun i => x1 (i - 1) * x1 i * x1 (i + 1)) = 0 ∧
      rule110 x1 = 0) := by
  have hb : IsBin x1 := fun i => Or.inl rfl
  have hE : Ejoint 1 1 1 x1 (pMin 1 1 x1) (qMin x1) (yMin 1 1 x1) = 1 := by
    rw [Ejoint_eq_sum_cell]
    simp [Fin.sum_univ_one, cellE, pMin, qMin, yMin, pTab, qTab, yTab, lVec, sVec, x1, theta_one]
    norm_num
  obtain ⟨hf, hmin⟩ := joint_cell_table (w1 := 1) (w2 := 1) (w3 := 1) one_pos one_pos one_pos hb
  have hp : pMin 1 1 x1 = 0 := by funext i; simp [pMin, pTab, lVec, sVec, x1, theta_one]
  have hq : qMin x1 = 0 := by funext i; simp [qMin, qTab, lVec, sVec, x1]
  have hy : yMin 1 1 x1 = 0 := by funext i; simp [yMin, yTab, lVec, sVec, x1, theta_one]
  refine ⟨hb, fun p q y hpq => ?_, ?_, ?_, ?_⟩
  · have := hmin p q y hpq
    rw [hE, hp, hq, hy] at this
    exact this
  · funext i; simp [x1]
  · funext i; simp [x1]
  · funext i; simp [rule110, poly110, x1]

/-- The row `x = (0,1,0)` on the ring of 3 cells (R10(ii)). -/
def x3 : Fin 3 → ℝ := ![0, 1, 0]

/-- R10(ii): `n = 3`, `x = (0,1,0)`, unit weights. The cascade point
`(p*, q*, y*) = ((0,0,0), (0,0,0), (1,1,0))` is not stationary for the exact `p`-block re-solve of
`E_x` with `(q, y)` held: over `p ∈ B` the energy `p ↦ E_x(p, q*, y*)` has the unique
minimiser `p = (1/3, 1/3, 0) ≠ (0,0,0)`. -/
theorem R10_ii :
    IsBin x3 ∧ (fun i => x3 i * x3 (i + 1)) = ![0, 0, 0] ∧
    (fun i => x3 (i - 1) * x3 i * x3 (i + 1)) = ![0, 0, 0] ∧ rule110 x3 = ![1, 1, 0] ∧
    (∀ p : Fin 3 → ℝ, FeasPQ p (![0, 0, 0] : Fin 3 → ℝ) →
      Ejoint 1 1 1 x3 ![1 / 3, 1 / 3, 0] ![0, 0, 0] ![1, 1, 0] ≤
        Ejoint 1 1 1 x3 p ![0, 0, 0] ![1, 1, 0] ∧
      (Ejoint 1 1 1 x3 p ![0, 0, 0] ![1, 1, 0] ≤
          Ejoint 1 1 1 x3 ![1 / 3, 1 / 3, 0] ![0, 0, 0] ![1, 1, 0] → p = ![1 / 3, 1 / 3, 0])) ∧
    (![1 / 3, 1 / 3, 0] : Fin 3 → ℝ) ≠ ![0, 0, 0] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i; fin_cases i <;> simp [x3]
  · funext i; fin_cases i <;> simp [x3]
  · funext i; fin_cases i <;> simp [x3]
  · funext i; fin_cases i <;> simp [rule110, poly110, x3] <;> norm_num
  · intro p hp
    have h0 := hp 0
    have h1 := hp 1
    have h2 := hp 2
    simp only [Ejoint_eq_sum_cell, Fin.sum_univ_three, cellE, lVec, sVec]
    simp [x3]
    obtain ⟨ha0, ha1, -, -⟩ := h0
    obtain ⟨hb0, hb1, -, -⟩ := h1
    obtain ⟨hc0, hc1, -, -⟩ := h2
    constructor
    · nlinarith [sq_nonneg (p 0 - 1 / 3), sq_nonneg (p 1 - 1 / 3), sq_nonneg (p 2)]
    · intro hle
      have hA : (p 0 - 1 / 3) ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (p 0 - 1 / 3), sq_nonneg (p 1 - 1 / 3), sq_nonneg (p 2)]
      have hB : (p 1 - 1 / 3) ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (p 0 - 1 / 3), sq_nonneg (p 1 - 1 / 3), sq_nonneg (p 2)]
      have hC : p 2 ^ 2 ≤ 0 := by
        nlinarith [sq_nonneg (p 0 - 1 / 3), sq_nonneg (p 1 - 1 / 3), sq_nonneg (p 2)]
      have e0 : p 0 = 1 / 3 := by nlinarith [sq_nonneg (p 0 - 1 / 3)]
      have e1 : p 1 = 1 / 3 := by nlinarith [sq_nonneg (p 1 - 1 / 3)]
      have e2 : p 2 = 0 := by nlinarith [sq_nonneg (p 2)]
      funext i
      fin_cases i <;> simp [e0, e1, e2]
  · intro h
    have := congrFun h 0
    simp at this

/-! ### R12: the single summed energy as a construction (certified read-out at 1/4) -/

/-- Euclidean norm on `ℝ^{3n}` of a point `(u, v, w)` given by its three blocks. -/
noncomputable def eN3 (u v w : Fin n → ℝ) : ℝ :=
  Real.sqrt (∑ i, u i ^ 2 + ∑ i, v i ^ 2 + ∑ i, w i ^ 2)

lemma eN_le_eN3_right (u v w : Fin n → ℝ) : eN w ≤ eN3 u v w := by
  unfold eN eN3
  apply Real.sqrt_le_sqrt
  have h1 : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have h2 : 0 ≤ ∑ i, v i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  linarith

lemma eN3_lt_iff (u v w : Fin n → ℝ) {c : ℝ} (hc : 0 < c) :
    eN3 u v w < c ↔ ∑ i, u i ^ 2 + ∑ i, v i ^ 2 + ∑ i, w i ^ 2 < c ^ 2 := by
  unfold eN3
  have h0 : 0 ≤ ∑ i, u i ^ 2 + ∑ i, v i ^ 2 + ∑ i, w i ^ 2 := by
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (u i))
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (v i))
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg (w i))
    linarith
  exact Real.sqrt_lt' hc

/-- Residual vector `ω₁ = p - (s - 1)`, `ω₂ = q - (l + p - 1)`, `ω₃ = y - (s - p - q)` (9.0). -/
def om1 (x p : Fin n → ℝ) : Fin n → ℝ := fun i => p i - (sVec x i - 1)
def om2 (x p q : Fin n → ℝ) : Fin n → ℝ := fun i => q i - (lVec x i + p i - 1)
def om3 (x p q y : Fin n → ℝ) : Fin n → ℝ := fun i => y i - (sVec x i - p i - q i)

/-- Gradient of the smooth part `f_w` at `z = (p,q,y)`: `∇f_w = Σ_j w_j ω_j b_j` with
`b₁ = (1,0,0)`, `b₂ = (-1,1,0)`, `b₃ = (1,1,1)`. -/
def gradP (w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w1 * om1 x p i - w2 * om2 x p q i + w3 * om3 x p q y i
def gradQ (w2 w3 : ℝ) (x p q y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => w2 * om2 x p q i + w3 * om3 x p q y i
def gradY (w3 : ℝ) (x p q y : Fin n → ℝ) : Fin n → ℝ := fun i => w3 * om3 x p q y i

/-- The forward–backward residual `R_α(z) = (z - prox_{αg}(z - α∇f_w(z)))/α` of the single
declaration `D_x^w`, block by block; `prox_{αg}` is the clamp on `p, q` and the identity on `y`
(the projection onto `B × B × ℝⁿ`). -/
noncomputable def resP (α w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (p i - clamp (p i - α * gradP w1 w2 w3 x p q y i)) / α
noncomputable def resQ (α w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (q i - clamp (q i - α * gradQ w2 w3 x p q y i)) / α
noncomputable def resY (α w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (y i - (y i - α * gradY w3 x p q y i)) / α

/-- `‖R_α(z)‖`. -/
noncomputable def resNorm (α w1 w2 w3 : ℝ) (x p q y : Fin n → ℝ) : ℝ :=
  eN3 (resP α w1 w2 w3 x p q y) (resQ α w1 w2 w3 x p q y) (resY α w1 w2 w3 x p q y)

/-- The soundness distance bound for the declaration `D_x^w` at step `α` with declared
curvature `σ`: `‖z - z°‖ ≤ ‖R_α(z)‖/σ` for every `z`, with `z° = (pMin, qMin, yMin)` the unique
minimiser of `E_x^w` (R9). HYPOTHESIS of R12(ii), (iv): it is the conclusion of thm:soundness(c)
(`G3SoundnessProx.regimeAP_of`) applied to a valid declaration, and is not proved here. -/
def JointSound (α w1 w2 w3 σ : ℝ) (x : Fin n → ℝ) : Prop :=
  ∀ p q y : Fin n → ℝ,
    eN3 (p - pMin w1 w2 x) (q - qMin x) (y - yMin w1 w2 x) ≤ resNorm α w1 w2 w3 x p q y / σ

/-- R12(ii): certified read-out. For `w_1 ≥ w_2 > 0`, `w_3 > 0`, `α = 1/β̂`, `σ̂ > 0`, and the
soundness distance bound (hypothesis `hSound`), every `z = (p,q,y)` with
`‖R_α(z)‖ < σ̂/4` has `rd_{1/4}(y) = t(x)`; `z` may be produced by any method. -/
theorem joint_readout_quarter {w1 w2 w3 β σ : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (hw : w2 ≤ w1) (hβ : 0 < β) (hσ : 0 < σ) {x : Fin n → ℝ} (hx : IsBin x)
    (hSound : JointSound (1 / β) w1 w2 w3 σ x) (p q y : Fin n → ℝ)
    (hres : resNorm (1 / β) w1 w2 w3 x p q y < σ / 4) : rdT (1 / 4) y = rule110 x := by
  have hd : eN (y - yMin w1 w2 x) < 1 / 4 := by
    calc eN (y - yMin w1 w2 x) ≤ eN3 (p - pMin w1 w2 x) (q - qMin x) (y - yMin w1 w2 x) :=
          eN_le_eN3_right _ _ _
      _ ≤ resNorm (1 / β) w1 w2 w3 x p q y / σ := hSound p q y
      _ < 1 / 4 := by
        rw [div_lt_iff₀ hσ]; linarith
  exact (R11_d h1 h2 hw hx).2.2.2.2.2 _ hd

/-- R12(ii) in the form tested by the harness (no square root): `‖R_α(z)‖² < (σ̂/4)²`. -/
theorem joint_readout_quarter_sq {w1 w2 w3 β σ : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (hw : w2 ≤ w1) (hβ : 0 < β) (hσ : 0 < σ) {x : Fin n → ℝ} (hx : IsBin x)
    (hSound : JointSound (1 / β) w1 w2 w3 σ x) (p q y : Fin n → ℝ)
    (hres : ∑ i, resP (1 / β) w1 w2 w3 x p q y i ^ 2 + ∑ i, resQ (1 / β) w1 w2 w3 x p q y i ^ 2 +
      ∑ i, resY (1 / β) w1 w2 w3 x p q y i ^ 2 < (σ / 4) ^ 2) : rdT (1 / 4) y = rule110 x :=
  joint_readout_quarter h1 h2 h3 hw hβ hσ hx hSound p q y
    ((eN3_lt_iff _ _ _ (by positivity)).mpr hres)

/-- R12(iv): `N` automaton steps by the single summed energy. At each step any `z` with
`‖R_α(z)‖ < σ̂/4` for the declaration `D^w_{x⁽ʰ⁾}` is accepted and the next row is
`rd_{1/4}` of its y-block; then `x⁽ʰ⁾ = t^h(x⁽⁰⁾)` for all `h ≤ N`, every `n`, `N`. The soundness
hypothesis is required for every binary row (the same declared pair serves every step). -/
theorem joint_N_steps {w1 w2 w3 β σ : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3)
    (hw : w2 ≤ w1) (hβ : 0 < β) (hσ : 0 < σ)
    (hSound : ∀ x : Fin n → ℝ, IsBin x → JointSound (1 / β) w1 w2 w3 σ x)
    {x0 : Fin n → ℝ} (hx0 : IsBin x0) (N : ℕ) (rows P Q Y : ℕ → Fin n → ℝ)
    (h0 : rows 0 = x0)
    (hstep : ∀ h < N, resNorm (1 / β) w1 w2 w3 (rows h) (P h) (Q h) (Y h) < σ / 4 ∧
      rows (h + 1) = rdT (1 / 4) (Y h)) :
    ∀ h ≤ N, rows h = rule110^[h] x0 ∧ IsBin (rows h) := by
  intro h
  induction h with
  | zero => intro _; simp [h0, hx0]
  | succ h ih =>
    intro hh
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    obtain ⟨hres, hnext⟩ := hstep h (by omega)
    have := joint_readout_quarter h1 h2 h3 hw hβ hσ ih2 (hSound _ ih2) _ _ _ hres
    rw [hnext, this, ih1, Function.iterate_succ_apply']
    exact ⟨rfl, by rw [← ih1]; exact rule110_bin ih2⟩

/-- R12(ii) at the headline instance: unit weights, declared pair `(β̂, σ̂) = (18/5, 3/25)`,
step `α = 5/18` (`declared_pair_valid` below establishes the validity of this pair). -/
theorem joint_readout_quarter_unit {n : ℕ} [NeZero n] {x : Fin n → ℝ} (hx : IsBin x)
    (hSound : JointSound (1 / (18 / 5)) 1 1 1 (3 / 25) x) (p q y : Fin n → ℝ)
    (hres : resNorm (1 / (18 / 5)) 1 1 1 x p q y < (3 / 25) / 4) : rdT (1 / 4) y = rule110 x :=
  joint_readout_quarter one_pos one_pos one_pos le_rfl (by norm_num) (by norm_num) hx hSound p q y hres

end Joint

/-! ## R8: Hessian, the cubic, brackets, validity of the declared pair -/

section R8

open Matrix

/-- `M` with rows `b₁ = (1,0,0)`, `b₂ = (-1,1,0)`, `b₃ = (1,1,1)` (coordinates `(p,q,y)`). -/
def Mmat : Matrix (Fin 3) (Fin 3) ℝ := !![1, 0, 0; -1, 1, 0; 1, 1, 1]

/-- `H_w = Mᵀ diag(w) M = Σ_j w_j b_j b_jᵀ`. -/
def Hw (w1 w2 w3 : ℝ) : Matrix (Fin 3) (Fin 3) ℝ := Mmatᵀ * Matrix.diagonal ![w1, w2, w3] * Mmat

/-- The unit-weight Hessian `H = [[3,0,1],[0,2,1],[1,1,1]]`. -/
def Hunit : Matrix (Fin 3) (Fin 3) ℝ := !![3, 0, 1; 0, 2, 1; 1, 1, 1]

/-- The quadratic form `vᵀ A v` and the squared norm. -/
def qf (A : Matrix (Fin 3) (Fin 3) ℝ) (v : Fin 3 → ℝ) : ℝ := v ⬝ᵥ (A *ᵥ v)

/-- R8(b): `det M = 1`. -/
theorem det_Mmat : Mmat.det = 1 := by
  simp [Mmat, Matrix.det_fin_three]

/-- R8(b): `H_w` explicitly, and the unit-weight case. -/
theorem Hw_explicit (w1 w2 w3 : ℝ) :
    Hw w1 w2 w3 = !![w1 + w2 + w3, -w2 + w3, w3; -w2 + w3, w2 + w3, w3; w3, w3, w3] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Hw, Mmat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.diagonal_apply]

theorem Hw_unit : Hw 1 1 1 = Hunit := by
  rw [Hw_explicit]; ext i j; fin_cases i <;> fin_cases j <;> simp [Hunit] <;> norm_num

/-- R8(b): `vᵀ H_w v = Σ_j w_j (b_j · v)²`. -/
theorem qf_Hw (w1 w2 w3 : ℝ) (v : Fin 3 → ℝ) :
    qf (Hw w1 w2 w3) v =
      w1 * (v 0) ^ 2 + w2 * (v 1 - v 0) ^ 2 + w3 * (v 0 + v 1 + v 2) ^ 2 := by
  rw [Hw_explicit]
  simp [qf, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- R8(c): `H_w` is positive definite for `w > 0`. -/
theorem Hw_posdef {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3) (v : Fin 3 → ℝ)
    (hv : v ≠ 0) : 0 < qf (Hw w1 w2 w3) v := by
  rw [qf_Hw]
  by_contra hle
  rw [not_lt] at hle
  have a0 : 0 ≤ w1 * (v 0) ^ 2 := by positivity
  have a1 : 0 ≤ w2 * (v 1 - v 0) ^ 2 := by positivity
  have a2 : 0 ≤ w3 * (v 0 + v 1 + v 2) ^ 2 := by positivity
  have e0 : w1 * (v 0) ^ 2 = 0 := by linarith
  have e1 : w2 * (v 1 - v 0) ^ 2 = 0 := by linarith
  have e2 : w3 * (v 0 + v 1 + v 2) ^ 2 = 0 := by linarith
  have f0 : v 0 = 0 := by
    have := (mul_eq_zero.mp e0).resolve_left h1.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have f1 : v 1 - v 0 = 0 := by
    have := (mul_eq_zero.mp e1).resolve_left h2.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  have f2 : v 0 + v 1 + v 2 = 0 := by
    have := (mul_eq_zero.mp e2).resolve_left h3.ne'
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  apply hv
  funext i
  fin_cases i <;> simp <;> linarith

/-- R8(b), link to the energy: the inner product of a gradient difference of `f_w` with the
displacement is `Σ_i (Δ_i)ᵀ H_w Δ_i`, so `H_w` is the (constant) Hessian of the cell-grouped
quadratic `f_w`. -/
theorem grad_inner_eq {n : ℕ} [NeZero n] (w1 w2 w3 : ℝ) (x p q y p' q' y' : Fin n → ℝ) :
    ∑ i, ((gradP w1 w2 w3 x p q y i - gradP w1 w2 w3 x p' q' y' i) * (p i - p' i) +
      (gradQ w2 w3 x p q y i - gradQ w2 w3 x p' q' y' i) * (q i - q' i) +
      (gradY w3 x p q y i - gradY w3 x p' q' y' i) * (y i - y' i)) =
    ∑ i, qf (Hw w1 w2 w3) ![p i - p' i, q i - q' i, y i - y' i] := by
  apply Finset.sum_congr rfl
  intro i _
  rw [qf_Hw]
  simp [gradP, gradQ, gradY, om1, om2, om3]
  ring

/-- R8(c): the characteristic polynomial of the unit-weight Hessian,
`det(λI - H) = λ³ - 6λ² + 9λ - 1 =: π(λ)`. -/
def cubic (t : ℝ) : ℝ := t ^ 3 - 6 * t ^ 2 + 9 * t - 1

theorem charpoly_Hunit (t : ℝ) : (t • (1 : Matrix (Fin 3) (Fin 3) ℝ) - Hunit).det = cubic t := by
  simp [Hunit, cubic, Matrix.det_fin_three]
  ring

/-- R8(c): trace `6`, sum of the principal `2×2` minors `9`, determinant `1`. -/
theorem Hunit_invariants :
    Hunit.trace = 6 ∧
    (Hunit 0 0 * Hunit 1 1 - Hunit 0 1 * Hunit 1 0) + (Hunit 0 0 * Hunit 2 2 - Hunit 0 2 * Hunit 2 0) +
      (Hunit 1 1 * Hunit 2 2 - Hunit 1 2 * Hunit 2 1) = 9 ∧ Hunit.det = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Hunit, Matrix.trace, Matrix.det_fin_three, Fin.sum_univ_three] <;>
    norm_num

/-- R8(c): the evaluations used for the brackets. -/
theorem cubic_values :
    cubic 0 = -1 ∧ cubic (3 / 25) = -73 / 15625 ∧ cubic (121 / 1000) = 2925561 / 1000000000 ∧
    cubic 1 = 3 ∧ cubic 2 = 1 ∧ cubic 3 = -1 ∧ cubic (7 / 2) = -1 / 8 ∧ cubic (18 / 5) = 37 / 125 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [cubic]

lemma cubic_continuous : Continuous cubic := by
  unfold cubic; fun_prop

/-- Root existence in an interval where the sign changes (intermediate value theorem). -/
lemma cubic_root_of_sign_pos_neg {a b : ℝ} (hab : a < b) (ha : 0 < cubic a) (hb : cubic b < 0) :
    ∃ r ∈ Set.Ioo a b, cubic r = 0 := by
  have := intermediate_value_Ioo' hab.le cubic_continuous.continuousOn
  obtain ⟨r, hr, h⟩ := this (show (0 : ℝ) ∈ Set.Ioo (cubic b) (cubic a) from ⟨hb, ha⟩)
  exact ⟨r, hr, h⟩

lemma cubic_root_of_sign_neg_pos {a b : ℝ} (hab : a < b) (ha : cubic a < 0) (hb : 0 < cubic b) :
    ∃ r ∈ Set.Ioo a b, cubic r = 0 := by
  have := intermediate_value_Ioo hab.le cubic_continuous.continuousOn
  obtain ⟨r, hr, h⟩ := this (show (0 : ℝ) ∈ Set.Ioo (cubic a) (cubic b) from ⟨ha, hb⟩)
  exact ⟨r, hr, h⟩

/-- The difference quotient of the cubic. -/
lemma cubic_sub (r r' : ℝ) :
    cubic r - cubic r' = (r - r') * (r ^ 2 + r * r' + r' ^ 2 - 6 * (r + r') + 9) := by
  unfold cubic; ring

/-- R8(c): at most one root below `1`. -/
lemma cubic_root_unique_lt_one {r r' : ℝ} (hr : r < 1) (hr' : r' < 1) (h : cubic r = 0)
    (h' : cubic r' = 0) : r = r' := by
  have := cubic_sub r r'
  rw [h, h'] at this
  have hF : 0 < r ^ 2 + r * r' + r' ^ 2 - 6 * (r + r') + 9 := by
    nlinarith [mul_pos (sub_pos.mpr hr) (sub_pos.mpr hr'), sq_nonneg (r - r'),
      sub_pos.mpr hr, sub_pos.mpr hr']
  have h0 : (r - r') * (r ^ 2 + r * r' + r' ^ 2 - 6 * (r + r') + 9) = 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hF.ne')

/-- R8(c): at most one root above `3`. -/
lemma cubic_root_unique_gt_three {r r' : ℝ} (hr : 3 < r) (hr' : 3 < r') (h : cubic r = 0)
    (h' : cubic r' = 0) : r = r' := by
  have := cubic_sub r r'
  rw [h, h'] at this
  have hF : 0 < r ^ 2 + r * r' + r' ^ 2 - 6 * (r + r') + 9 := by
    nlinarith [mul_pos (sub_pos.mpr hr) (sub_pos.mpr hr'), sq_nonneg (r - r'),
      sub_pos.mpr hr, sub_pos.mpr hr']
  have h0 : (r - r') * (r ^ 2 + r * r' + r' ^ 2 - 6 * (r + r') + 9) = 0 := by linarith
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right hF.ne')

/-- R8(c): the three roots of `π`: the unique root below `1` lies in `(3/25, 121/1000)`; there is
a root in `(2,3)`; the unique root above `3` lies in `(7/2, 18/5)`; and these are all the real
roots (`π(λ) = (λ - r₁)(λ - r₂)(λ - r₃)`). -/
theorem cubic_roots :
    ∃ r₁ r₂ r₃ : ℝ, r₁ ∈ Set.Ioo (3 / 25 : ℝ) (121 / 1000) ∧ r₂ ∈ Set.Ioo (2 : ℝ) 3 ∧
      r₃ ∈ Set.Ioo (7 / 2 : ℝ) (18 / 5) ∧
      (∀ t, cubic t = (t - r₁) * (t - r₂) * (t - r₃)) ∧
      (∀ r, r < 1 → cubic r = 0 → r = r₁) ∧ (∀ r, 3 < r → cubic r = 0 → r = r₃) := by
  obtain ⟨v0, v1, v2, v3, v4, v5, v6, v7⟩ := cubic_values
  obtain ⟨r₁, hr₁, e₁⟩ := cubic_root_of_sign_neg_pos (a := 3 / 25) (b := 121 / 1000)
    (by norm_num) (by rw [v1]; norm_num) (by rw [v2]; norm_num)
  obtain ⟨r₂, hr₂, e₂⟩ := cubic_root_of_sign_pos_neg (a := 2) (b := 3) (by norm_num)
    (by rw [v4]; norm_num) (by rw [v5]; norm_num)
  obtain ⟨r₃, hr₃, e₃⟩ := cubic_root_of_sign_neg_pos (a := 7 / 2) (b := 18 / 5)
    (by norm_num) (by rw [v6]; norm_num) (by rw [v7]; norm_num)
  have hr₁' := hr₁
  have hr₂' := hr₂
  have hr₃' := hr₃
  obtain ⟨a1, b1⟩ := hr₁
  obtain ⟨a2, b2⟩ := hr₂
  obtain ⟨a3, b3⟩ := hr₃
  refine ⟨r₁, r₂, r₃, hr₁', hr₂', hr₃', ?_, ?_, ?_⟩
  · -- Vieta: three distinct roots of a monic cubic
    intro t
    have d12 : r₁ - r₂ ≠ 0 := by intro h; linarith
    have d13 : r₁ - r₃ ≠ 0 := by intro h; linarith
    have d23 : r₂ - r₃ ≠ 0 := by intro h; linarith
    set A := r₁ + r₂ + r₃ - 6 with hA
    set B := 9 - (r₁ * r₂ + r₁ * r₃ + r₂ * r₃) with hB
    set C := r₁ * r₂ * r₃ - 1 with hC
    have dq : ∀ t, cubic t - (t - r₁) * (t - r₂) * (t - r₃) = A * t ^ 2 + B * t + C := by
      intro t; simp only [cubic, hA, hB, hC]; ring
    have k1 : A * r₁ ^ 2 + B * r₁ + C = 0 := by rw [← dq, e₁]; ring
    have k2 : A * r₂ ^ 2 + B * r₂ + C = 0 := by rw [← dq, e₂]; ring
    have k3 : A * r₃ ^ 2 + B * r₃ + C = 0 := by rw [← dq, e₃]; ring
    have l12 : A * (r₁ + r₂) + B = 0 := by
      have : (r₁ - r₂) * (A * (r₁ + r₂) + B) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left d12
    have l13 : A * (r₁ + r₃) + B = 0 := by
      have : (r₁ - r₃) * (A * (r₁ + r₃) + B) = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left d13
    have hA0 : A = 0 := by
      have : (r₂ - r₃) * A = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left d23
    have hB0 : B = 0 := by rw [hA0] at l12; linarith
    have hC0 : C = 0 := by rw [hA0, hB0] at k1; linarith
    have := dq t
    rw [hA0, hB0, hC0] at this
    linarith
  · intro r hr hr0
    exact cubic_root_unique_lt_one hr (by linarith) hr0 e₁
  · intro r hr hr0
    exact cubic_root_unique_gt_three hr (by linarith) hr0 e₃

/-- Every real root of `π` is one of the three. -/
theorem cubic_root_cases {r₁ r₂ r₃ : ℝ} (h : ∀ t, cubic t = (t - r₁) * (t - r₂) * (t - r₃))
    {r : ℝ} (hr : cubic r = 0) : r = r₁ ∨ r = r₂ ∨ r = r₃ := by
  rw [h] at hr
  rcases mul_eq_zero.mp hr with h12 | h3
  · rcases mul_eq_zero.mp h12 with h1 | h2
    · left; linarith
    · right; left; linarith
  · right; right; linarith

/-- `vᵀ H v` for the unit-weight Hessian, as a polynomial. -/
theorem qf_Hunit (v : Fin 3 → ℝ) :
    qf Hunit v = 3 * v 0 ^ 2 + 2 * v 1 ^ 2 + v 2 ^ 2 + 2 * v 0 * v 2 + 2 * v 1 * v 2 := by
  simp [qf, Hunit, dotProduct, Matrix.mulVec, Fin.sum_univ_three]
  ring

/-- `‖v‖²`. -/
def nsq (v : Fin 3 → ℝ) : ℝ := v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2

/-- A pair `(β̂, σ̂)` is a valid declared smoothness/curvature for the Hessian `A`
(R8(e): `σ̂ ∈ (0, λ_min(A)]`, `β̂ ≥ λ_max(A)`, in Rayleigh form): `σ̂‖v‖² ≤ vᵀAv ≤ β̂‖v‖²`. -/
def ValidPair (A : Matrix (Fin 3) (Fin 3) ℝ) (β σ : ℝ) : Prop :=
  0 < σ ∧ (∀ v, σ * nsq v ≤ qf A v) ∧ (∀ v, qf A v ≤ β * nsq v)

/-- A lower Rayleigh bound with a margin above `3/25`: `(241/2000)‖v‖² ≤ vᵀHv`. -/
theorem Hunit_lower (v : Fin 3 → ℝ) : 241 / 2000 * nsq v ≤ qf Hunit v := by
  rw [qf_Hunit]; unfold nsq
  nlinarith [sq_nonneg (v 0 + 2000 / 5759 * v 2), sq_nonneg (v 1 + 2000 / 3759 * v 2),
    sq_nonneg (v 2)]

/-- An upper Rayleigh bound with a margin below `18/5`: `vᵀHv ≤ (71/20)‖v‖²`. -/
theorem Hunit_upper (v : Fin 3 → ℝ) : qf Hunit v ≤ 71 / 20 * nsq v := by
  rw [qf_Hunit]; unfold nsq
  nlinarith [sq_nonneg (v 0 - 20 / 11 * v 2), sq_nonneg (v 1 - 20 / 31 * v 2), sq_nonneg (v 2)]

/-- R8(e): the declared pair `(β̂, σ̂) = (18/5, 3/25)` is valid at unit weights. -/
theorem declared_pair_valid : ValidPair Hunit (18 / 5) (3 / 25) := by
  refine ⟨by norm_num, fun v => ?_, fun v => ?_⟩
  · have h := Hunit_lower v
    have : 0 ≤ nsq v := by unfold nsq; positivity
    nlinarith
  · have h := Hunit_upper v
    have : 0 ≤ nsq v := by unfold nsq; positivity
    nlinarith

/-- A root of `π` is an eigenvalue of `H`: `H v = r v` for some `v ≠ 0`. -/
theorem eigenvector_of_root {r : ℝ} (hr : cubic r = 0) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ Hunit *ᵥ v = r • v := by
  have hdet : (r • (1 : Matrix (Fin 3) (Fin 3) ℝ) - Hunit).det = 0 := by
    rw [charpoly_Hunit]; exact hr
  obtain ⟨v, hv, hmul⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hmul
  exact hmul.symm

/-- The Rayleigh quotient of a root's eigenvector is the root. -/
theorem rayleigh_of_root {r : ℝ} (hr : cubic r = 0) :
    ∃ v : Fin 3 → ℝ, v ≠ 0 ∧ qf Hunit v = r * nsq v ∧ 0 < nsq v := by
  obtain ⟨v, hv, hev⟩ := eigenvector_of_root hr
  refine ⟨v, hv, ?_, ?_⟩
  · have : qf Hunit v = r * (v ⬝ᵥ v) := by
      unfold qf; rw [hev]; simp [dotProduct_smul]
    have hn : v ⬝ᵥ v = nsq v := by simp [nsq, dotProduct, Fin.sum_univ_three, sq]
    rw [this, hn]
  · by_contra hle
    rw [not_lt] at hle
    apply hv
    unfold nsq at hle
    have h0 : v 0 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h1 : v 1 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h2 : v 2 = 0 := by nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    funext i; fin_cases i <;> simp [h0, h1, h2]

/-- The set of Rayleigh quotients of `H`. -/
def rayleighSet (A : Matrix (Fin 3) (Fin 3) ℝ) : Set ℝ :=
  {ρ | ∃ v : Fin 3 → ℝ, 0 < nsq v ∧ ρ = qf A v / nsq v}

/-- R8(c): `σ_J = λ_min(H)` (the infimum of the Rayleigh quotients, Boyd–Vandenberghe
App. A.5.2) lies in `(3/25, 121/1000)`, `λ_max(H)` (the supremum) lies in `(7/2, 18/5)`; both
infimum and supremum exist. -/
theorem lambda_brackets :
    (∃ g, IsGLB (rayleighSet Hunit) g) ∧ (∃ g, IsLUB (rayleighSet Hunit) g) ∧
    (∀ g, IsGLB (rayleighSet Hunit) g → 3 / 25 < g ∧ g < 121 / 1000) ∧
    (∀ g, IsLUB (rayleighSet Hunit) g → 7 / 2 < g ∧ g < 18 / 5) := by
  obtain ⟨r₁, r₂, r₃, h1, h2, h3, hfac, hu1, hu3⟩ := cubic_roots
  have hne : (rayleighSet Hunit).Nonempty := by
    refine ⟨qf Hunit ![1, 0, 0] / nsq ![1, 0, 0], ![1, 0, 0], ?_, rfl⟩
    simp [nsq]
  have hlb : ∀ ρ ∈ rayleighSet Hunit, 241 / 2000 ≤ ρ := by
    rintro ρ ⟨v, hv, rfl⟩
    rw [le_div_iff₀ hv]; exact Hunit_lower v
  have hub : ∀ ρ ∈ rayleighSet Hunit, ρ ≤ 71 / 20 := by
    rintro ρ ⟨v, hv, rfl⟩
    rw [div_le_iff₀ hv]; exact Hunit_upper v
  have hr1 : r₁ ∈ rayleighSet Hunit := by
    have hroot : cubic r₁ = 0 := by rw [hfac]; ring
    obtain ⟨v, -, hq, hpos⟩ := rayleigh_of_root hroot
    exact ⟨v, hpos, by rw [hq]; field_simp⟩
  have hr3 : r₃ ∈ rayleighSet Hunit := by
    have hroot : cubic r₃ = 0 := by rw [hfac]; ring
    obtain ⟨v, -, hq, hpos⟩ := rayleigh_of_root hroot
    exact ⟨v, hpos, by rw [hq]; field_simp⟩
  refine ⟨⟨_, Real.isGLB_sInf hne ⟨241 / 2000, hlb⟩⟩, ⟨_, Real.isLUB_sSup hne ⟨71 / 20, hub⟩⟩,
    ?_, ?_⟩
  · intro g hg
    have h1' : g ≤ r₁ := hg.1 hr1
    have h2' : 241 / 2000 ≤ g := hg.2 hlb
    obtain ⟨a1, b1⟩ := h1
    constructor <;> linarith
  · intro g hg
    have h1' : r₃ ≤ g := hg.1 hr3
    have h2' : g ≤ 71 / 20 := hg.2 hub
    obtain ⟨a3, b3⟩ := h3
    constructor <;> linarith

/-- R8(e), general weights, smoothness half: `vᵀ H_w v ≤ (w₁ + 2w₂ + 3w₃) ‖v‖²`, the sum-rule
value `β̂ = Σ_j w_j ‖b_j‖²` (each `(b_j · v)² ≤ ‖b_j‖² ‖v‖²`). -/
theorem Hw_upper {w1 w2 w3 : ℝ} (h1 : 0 < w1) (h2 : 0 < w2) (h3 : 0 < w3) (v : Fin 3 → ℝ) :
    qf (Hw w1 w2 w3) v ≤ (w1 + 2 * w2 + 3 * w3) * nsq v := by
  rw [qf_Hw]; unfold nsq
  have a : (v 0) ^ 2 ≤ v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by nlinarith [sq_nonneg (v 1), sq_nonneg (v 2)]
  have b : (v 1 - v 0) ^ 2 ≤ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
    nlinarith [sq_nonneg (v 1 + v 0), sq_nonneg (v 2)]
  have c : (v 0 + v 1 + v 2) ^ 2 ≤ 3 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
    nlinarith [sq_nonneg (v 0 - v 1), sq_nonneg (v 0 - v 2), sq_nonneg (v 1 - v 2)]
  nlinarith [mul_le_mul_of_nonneg_left a h1.le, mul_le_mul_of_nonneg_left b h2.le,
    mul_le_mul_of_nonneg_left c h3.le]

/-- R8(e), unit weights, curvature half on the concrete gradient: the declared `σ̂ = 3/25` is a
strong-monotonicity constant of the gradient of `f_w` on `ℝ^{3n}` (cell-grouped Hessian
`H ⊗ I`): `⟨∇f(z) - ∇f(z'), z - z'⟩ ≥ (3/25) ‖z - z'‖²`. -/
theorem unit_grad_strong_mono {n : ℕ} [NeZero n] (x p q y p' q' y' : Fin n → ℝ) :
    3 / 25 * ∑ i, ((p i - p' i) ^ 2 + (q i - q' i) ^ 2 + (y i - y' i) ^ 2) ≤
      ∑ i, ((gradP 1 1 1 x p q y i - gradP 1 1 1 x p' q' y' i) * (p i - p' i) +
        (gradQ 1 1 x p q y i - gradQ 1 1 x p' q' y' i) * (q i - q' i) +
        (gradY 1 x p q y i - gradY 1 x p' q' y' i) * (y i - y' i)) := by
  rw [grad_inner_eq, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have := (declared_pair_valid.2.1 ![p i - p' i, q i - q' i, y i - y' i])
  rw [Hw_unit]
  simpa [nsq] using this

end R8

#print axioms OCF.R110.clamp_and
#print axioms OCF.R110.rule110_poly_table
#print axioms OCF.R110.readout_threshold
#print axioms OCF.R110.stage_unique_min
#print axioms OCF.R110.pipeline_minimisers
#print axioms OCF.R110.pipeline_step_exact
#print axioms OCF.R110.pipeline_exists_accepted
#print axioms OCF.R110.pipeline_N_steps
#print axioms OCF.R110.pipeline_exact_counts
#print axioms OCF.R110.stopCount_le_Kbound
#print axioms OCF.R110.stage_count_bound
#print axioms OCF.R110.joint_cell_table
#print axioms OCF.R110.R9_i
#print axioms OCF.R110.R9_ii
#print axioms OCF.R110.R9_iii
#print axioms OCF.R110.R9_iv
#print axioms OCF.R110.R9_v
#print axioms OCF.R110.R10_i
#print axioms OCF.R110.R10_ii
#print axioms OCF.R110.R10_iii
#print axioms OCF.R110.R11_b
#print axioms OCF.R110.R11_c_gt
#print axioms OCF.R110.R11_c_iff
#print axioms OCF.R110.R11_d
#print axioms OCF.R110.R11_c_eq_readout
#print axioms OCF.R110.R11_d_margin_eq
#print axioms OCF.R110.R11_f
#print axioms OCF.R110.R11_f_thresholds
#print axioms OCF.R110.R11_e
#print axioms OCF.R110.joint_readout_quarter
#print axioms OCF.R110.joint_readout_quarter_sq
#print axioms OCF.R110.joint_N_steps
#print axioms OCF.R110.Ejoint_eq_sum_cell
#print axioms OCF.R110.grad_inner_eq
#print axioms OCF.R110.Hw_posdef
#print axioms OCF.R110.cubic_roots
#print axioms OCF.R110.lambda_brackets
#print axioms OCF.R110.declared_pair_valid
#print axioms OCF.R110.Hw_upper
#print axioms OCF.R110.unit_grad_strong_mono
#print axioms OCF.R110.joint_readout_quarter_unit

end OCF.R110

/-
C6 (with C1 and C5) — the rounding certificate: the gadget value lemma of
Proposition C5.1, the read-out statements of Proposition C5.2, the margin
chain and the family E_n of Proposition C5.3, Example C5.4 and the
flip-difference formula of Remark C5.5.

Source of truth: project_plan/done/proof_audits/C6_certificate_scope/01_derivation.md
(Def. C5.0 = S2.1; Prop. C5.1 = S2.4–S2.6; Prop. C5.2 = S2.9–S2.10;
Prop. C5.3 = S2.12–S2.13; Ex. C5.4 = S2.14; flip formula in S2.15),
adjudication 03_adjudication.md (section 4 "Formalisation tier" and the
section 7 addendum; gadget penalty M = 2(‖a‖₁² + 1) per ADJ-F1).
Landing draft: 04_landing_draft_a.tex (def:rounding, prop:sep-hard,
prop:readout, prop:margins, ex:two-spins, rem:rounding-cost).
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised:
ae11fea21a1f9a02.

DEFINITIONAL MAP (dossier symbol — Lean name):
* 𝒴 = {−1,1}ⁿ — `Y n`, a `Finset (Fin n → ℤ)` (`mem_Y`: every coordinate
  is 1 or −1). A discrete energy E : 𝒴 → ℝ is a function
  `(Fin n → ℤ) → α` into a linearly ordered additive group α (ℝ in the
  dossier; ℤ is used for the integral examples); only its values on `Y n`
  enter any statement.
* y^{(i)} — `flip y i`; d_H — Mathlib's `hammingDist`.
* m_r(y*) = min{E(y) − E(y*) : 1 ≤ d_H(y,y*) ≤ r} — `margin E ys r`, a
  `Finset.min` in `WithTop α` (⊤ only for an empty feasible set, which
  never occurs for 1 ≤ r, n ≥ 1). m₁ = min_i Δ_i — `flipMargin E ys`
  (`margin_one_eq_flipMargin` proves m₁ is also m_r at r = 1, S2.10).
  m_glob = min_{y ≠ y*} E(y) − E(y*) — `mglob E ys` (`margin_n_eq_mglob`
  proves m_n = m_glob).
* rd — `rd u` (rd(u)ᵢ = 1 if uᵢ ≥ 0, else −1); δ(u) = minᵢ|uᵢ| — `delta u`
  (`⨅ i, |u i|`, a minimum since Fin n is finite; n ≥ 1 where attainment
  is needed); Z — `Z n`. The ℓ_p norm, p ∈ [1,∞], is the `PiLp p` norm of
  `WithLp.toLp p (·)` (p = ∞ is the sup norm).
* Quadratic energy yᵀQy + cᵀy + e₀ — `quadEnergy Q c e0` (Q, c, e₀ over any
  commutative ring R; the SEP format is R = ℤ).
* Stones/partition instance a ∈ ℤⁿ — `a : Fin n → ℤ`; solvable —
  `Solvable a` (∃ x ∈ {±1}ⁿ, Σ aᵢxᵢ = 0). A = Σᵢaᵢ — `gA a` (= ‖a‖₁ for
  a > 0); M = 2(A² + 1) — `gM a`. A state (x, z) ∈ {±1}^{n+1} is
  y : Fin (n+1) → ℤ with xᵢ = y (castSucc i), z = y (last n).
  E_a — `gadgetE a`; y* = (𝟏, −1) — `ystar`; SEP data — `gadgetQ a`,
  `gadgetc a`, `gadgete0 a`.
* E_n — `En n` (Σ_{i<j} written Σᵢ Σⱼ [i < j]); 𝟏 — `ones`.

COVERAGE (target → Lean name):
1. C5.1 gadget value lemma (S2.4–S2.6), stated for EVERY a ∈ ℤⁿ (the
   dossier's a ∈ ℤ_{>0}ⁿ is a special case; positivity is used only for
   m₁ ≥ 2):
   E(y*) = 2 — `gadget_E_ystar`;
   every state y ≠ y* has E(y) ≥ E(y*) + 2 or E(y) = E(y*) − 2 —
   `gadget_dichotomy`; the second case holds exactly at z = +1, aᵀx = 0 —
   `gadget_low_iff_state`; it occurs iff the instance is solvable —
   `gadget_low_iff_solvable`;
   m_glob ∈ {−2} ∪ [2, ∞), = −2 iff solvable — `gadget_mglob`;
   m₁ = 4A² − 2 — `gadget_flipMargin`, `gadget_margin_one`; m₁ ≥ 2 for
   a > 0, n ≥ 1 — `gadget_m1_ge_two`; neighbour energies (S2.6) —
   `gadget_E_flip_last`, `gadget_E_flip_castSucc`;
   SEP format: Q symmetric, zero diagonal, integral (ℤ entries), and
   E_a = yᵀQy + cᵀy + e₀ on 𝒴 — `gadget_format`.
2. C5.2 (i): δ > 0 ⇒ u ∉ Z — `delta_pos_not_mem_Z`; rd = sign —
   `rd_eq_sign`; stability on every open ℓ_p ball of radius δ —
   `rd_stable_lp`; δ = dist_p(u, Z) (lower bound + attained) —
   `delta_le_dist_Z`, `exists_Z_dist_eq_delta`; sharpness — `rd_sharp`.
   C5.2 (ii) — `strict_one_opt`; S2.10 — `margin_one_eq_flipMargin`,
   `hammingDist_eq_one_iff`.
3. C5.3 (a) — `margin_antitone`, `margin_n_eq_mglob`, `margin_chain`,
   necessity `margin_pos_of_mglob_pos`; (b) —
   `En_eq` (E_n = k(2n − 1 − 2k)), `En_margins`.
   Ex. C5.4 — `two_spins`.
4. Flip-difference formula (S2.15) — `quad_flip_diff`.
PROSE-ONLY (by instruction): the bit-model complexity statements
C5.1(1)–(4) (P = NP, approximation, coNP membership).

Status tier: FORMALISED (statement + proof, no sorry) for items 1–4.
-/
import Mathlib

namespace OCF.C6

open Finset Matrix

/-! ## Definition C5.0 -/

/-- 𝒴 = {−1, 1}ⁿ. -/
def Y (n : ℕ) : Finset (Fin n → ℤ) := Fintype.piFinset fun _ => ({1, -1} : Finset ℤ)

lemma mem_Y {n : ℕ} {y : Fin n → ℤ} : y ∈ Y n ↔ ∀ i, y i = 1 ∨ y i = -1 := by
  simp [Y, Fintype.mem_piFinset]

/-- `flip y i` is y with coordinate i negated. -/
def flip {n : ℕ} (y : Fin n → ℤ) (i : Fin n) : Fin n → ℤ := Function.update y i (-(y i))

section Margins

variable {α : Type*} [AddCommGroup α] [LinearOrder α] {n : ℕ}

/-- The neighbourhood margin m_r(y*). -/
def margin (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) (r : ℕ) : WithTop α :=
  (((Y n).filter fun y => 1 ≤ hammingDist y ys ∧ hammingDist y ys ≤ r).image
    fun y => E y - E ys).min

/-- The flip margin m₁ = minᵢ Δᵢ(y*). -/
def flipMargin (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) : WithTop α :=
  ((univ : Finset (Fin n)).image fun i => E (flip ys i) - E ys).min

/-- The global separation margin m_glob(y*) = min_{y ≠ y*} E(y) − E(y*). -/
def mglob (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) : WithTop α :=
  (((Y n).filter fun y => y ≠ ys).image fun y => E y - E ys).min

lemma spin_ne_neg {x : ℤ} (h : x = 1 ∨ x = -1) : x ≠ -x := by omega

lemma flip_mem_Y {ys : Fin n → ℤ} (h : ys ∈ Y n) (i : Fin n) : flip ys i ∈ Y n := by
  rw [mem_Y] at *
  intro j
  by_cases hj : j = i
  · subst hj; simp [flip]; rcases h j with h | h <;> simp [h]
  · simp [flip, Function.update_of_ne hj, h j]

lemma hammingDist_flip {ys : Fin n → ℤ} (h : ys ∈ Y n) (i : Fin n) :
    hammingDist (flip ys i) ys = 1 := by
  rw [mem_Y] at h
  unfold hammingDist
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  by_cases hj : j = i
  · subst hj
    have := spin_ne_neg (h j)
    simp [flip]
    omega
  · simp [flip, hj]

/-- S2.10: the points at Hamming distance 1 from a spin vector are exactly its flips. -/
lemma hammingDist_eq_one_iff {ys y : Fin n → ℤ} (hys : ys ∈ Y n) (hy : y ∈ Y n) :
    hammingDist y ys = 1 ↔ ∃ i, y = flip ys i := by
  constructor
  · intro hd
    unfold hammingDist at hd
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hd
    refine ⟨i, funext fun j => ?_⟩
    have hj := congrArg (j ∈ ·) hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      eq_iff_iff] at hj
    rw [mem_Y] at hys hy
    by_cases hji : j = i
    · subst hji
      have hne : y j ≠ ys j := hj.mpr rfl
      simp [flip]
      rcases hys j with h1 | h1 <;> rcases hy j with h2 | h2 <;> simp_all
    · have : y j = ys j := by
        by_contra hc; exact hji (hj.mp hc)
      simp [flip, Function.update_of_ne hji, this]
  · rintro ⟨i, rfl⟩
    exact hammingDist_flip hys i

/-- S2.10: m₁ is the neighbourhood margin at radius 1. -/
theorem margin_one_eq_flipMargin (E : (Fin n → ℤ) → α) {ys : Fin n → ℤ} (hys : ys ∈ Y n) :
    margin E ys 1 = flipMargin E ys := by
  unfold margin flipMargin
  congr 1
  have hset : ((Y n).filter fun y => 1 ≤ hammingDist y ys ∧ hammingDist y ys ≤ 1) =
      (univ : Finset (Fin n)).image (flip ys) := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hy, h1, h2⟩
      obtain ⟨i, rfl⟩ := (hammingDist_eq_one_iff hys hy).mp (by omega)
      exact ⟨i, rfl⟩
    · rintro ⟨i, rfl⟩
      refine ⟨flip_mem_Y hys i, ?_⟩
      rw [hammingDist_flip hys i]; omega
  rw [hset, Finset.image_image]
  rfl

/-- C5.3(a), monotonicity: m_{r'} ≤ m_r for r ≤ r'. -/
theorem margin_antitone (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) {r r' : ℕ} (h : r ≤ r') :
    margin E ys r' ≤ margin E ys r := by
  unfold margin
  apply Finset.min_mono
  apply Finset.image_subset_image
  intro y
  simp only [Finset.mem_filter]
  rintro ⟨hy, h1, h2⟩
  exact ⟨hy, h1, h2.trans h⟩

/-- C5.3(a), end of the chain: m_n = m_glob. -/
theorem margin_n_eq_mglob (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) :
    margin E ys n = mglob E ys := by
  unfold margin mglob
  congr 2
  ext y
  simp only [Finset.mem_filter]
  have hle : hammingDist y ys ≤ n := by
    simpa using (hammingDist_le_card_fintype (x := y) (y := ys))
  constructor
  · rintro ⟨hy, h1, _⟩
    exact ⟨hy, hammingDist_pos.mp (by omega)⟩
  · rintro ⟨hy, hne⟩
    exact ⟨hy, hammingDist_pos.mpr hne, hle⟩

/-- C5.3(a), the full chain m₁ ≥ m₂ ≥ ⋯ ≥ m_n = m_glob, packaged. -/
theorem margin_chain (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) :
    (∀ r r', r ≤ r' → margin E ys r' ≤ margin E ys r) ∧ margin E ys n = mglob E ys :=
  ⟨fun _ _ h => margin_antitone E ys h, margin_n_eq_mglob E ys⟩

/-- C5.3(a), consequence: m_glob > 0 forces m_r > 0 for every r ≤ n (necessity; the
family E_n of `En_margins` shows it is never sufficient for r < n). -/
theorem margin_pos_of_mglob_pos (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ)
    (h : 0 < mglob E ys) {r : ℕ} (hr : r ≤ n) : 0 < margin E ys r := by
  rw [← margin_n_eq_mglob] at h
  exact lt_of_lt_of_le h (margin_antitone E ys hr)

/-- C5.2(ii): if m₁ = m > 0 then E(y) ≥ E(y*) + m > E(y*) at every y with d_H(y, y*) = 1. -/
theorem strict_one_opt [IsOrderedAddMonoid α] (E : (Fin n → ℤ) → α) (ys : Fin n → ℤ) (m : α)
    (hm : margin E ys 1 = m) (hpos : 0 < m) :
    ∀ y ∈ Y n, hammingDist y ys = 1 → E ys + m ≤ E y ∧ E ys < E y := by
  intro y hy hd
  have hmem : E y - E ys ∈ (((Y n).filter fun y => 1 ≤ hammingDist y ys ∧
      hammingDist y ys ≤ 1).image fun y => E y - E ys) :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hy, by omega, by omega⟩)
  have hle := Finset.min_le hmem
  unfold margin at hm
  rw [hm, WithTop.coe_le_coe] at hle
  constructor
  · rw [le_sub_iff_add_le'] at hle; exact hle
  · have := lt_of_lt_of_le hpos hle
    exact sub_pos.mp this

end Margins

/-! ## Proposition C5.2 (i): the read-out -/

section Readout

variable {n : ℕ}

/-- The rounding map, sign with the tie convention sign 0 := +1. -/
noncomputable def rd (u : Fin n → ℝ) : Fin n → ℤ := fun i => if 0 ≤ u i then 1 else -1

/-- The geometric read-out margin δ(u) = minᵢ |uᵢ|. -/
noncomputable def delta (u : Fin n → ℝ) : ℝ := ⨅ i, |u i|

/-- Z = {v : vᵢ = 0 for some i}. -/
def Z (n : ℕ) : Set (Fin n → ℝ) := {v | ∃ i, v i = 0}

lemma delta_le (u : Fin n → ℝ) (i : Fin n) : delta u ≤ |u i| :=
  ciInf_le (Set.finite_range _).bddBelow i

/-- C5.2(i): δ(u) > 0 implies u ∉ Z. -/
theorem delta_pos_not_mem_Z (u : Fin n → ℝ) (h : 0 < delta u) : u ∉ Z n := by
  rintro ⟨i, hi⟩
  have := delta_le u i
  rw [hi, abs_zero] at this
  linarith

/-- C5.2(i): if δ(u) > 0, rd(u) is sign(u) (the tie convention is not used). -/
theorem rd_eq_sign (u : Fin n → ℝ) (h : 0 < delta u) (i : Fin n) :
    ((rd u i : ℤ) : ℝ) = Real.sign (u i) := by
  have hi := delta_le u i
  rcases lt_trichotomy (u i) 0 with hlt | heq | hgt
  · simp [rd, not_le.mpr hlt, Real.sign_of_neg hlt]
  · rw [heq, abs_zero] at hi; linarith
  · simp [rd, hgt.le, Real.sign_of_pos hgt]

/-- C5.2(i): rd is constant on the open ℓ_p ball of radius δ(u), every p ∈ [1, ∞]. -/
theorem rd_stable_lp (p : ENNReal) [Fact (1 ≤ p)] (u u' : Fin n → ℝ)
    (h : ‖WithLp.toLp p (u' - u)‖ < delta u) : rd u' = rd u := by
  funext i
  have h1 : ‖(WithLp.toLp p (u' - u)) i‖ ≤ ‖WithLp.toLp p (u' - u)‖ :=
    PiLp.norm_apply_le _ i
  rw [PiLp.toLp_apply, Pi.sub_apply, Real.norm_eq_abs] at h1
  have h2 := delta_le u i
  have h3 : |u' i - u i| < |u i| := by linarith
  rw [abs_sub_lt_iff] at h3
  unfold rd
  rcases le_or_gt 0 (u i) with hu | hu
  · rw [abs_of_nonneg hu] at h3
    rw [if_pos hu, if_pos (by linarith)]
  · rw [abs_of_neg hu] at h3
    rw [if_neg (by linarith), if_neg (by linarith)]

/-- C5.2(i), distance: every point of Z is at ℓ_p distance ≥ δ(u) from u. -/
theorem delta_le_dist_Z (p : ENNReal) [Fact (1 ≤ p)] (u v : Fin n → ℝ) (hv : v ∈ Z n) :
    delta u ≤ ‖WithLp.toLp p (u - v)‖ := by
  obtain ⟨i, hi⟩ := hv
  have h1 : ‖(WithLp.toLp p (u - v)) i‖ ≤ ‖WithLp.toLp p (u - v)‖ :=
    PiLp.norm_apply_le _ i
  rw [PiLp.toLp_apply, Pi.sub_apply, hi, sub_zero, Real.norm_eq_abs] at h1
  exact (delta_le u i).trans h1

lemma exists_delta_eq [NeZero n] (u : Fin n → ℝ) : ∃ i, |u i| = delta u :=
  exists_eq_ciInf_of_finite

lemma norm_single_lp (p : ENNReal) [Fact (1 ≤ p)] (i : Fin n) (b : ℝ) :
    ‖WithLp.toLp p (Pi.single i b : Fin n → ℝ)‖ = |b| := by
  have := PiLp.norm_single p (fun _ : Fin n => ℝ) i b
  rw [PiLp.single, Real.norm_eq_abs] at this
  exact this

/-- C5.2(i), distance attained: δ(u) = dist_p(u, Z) (n ≥ 1). -/
theorem exists_Z_dist_eq_delta (p : ENNReal) [Fact (1 ≤ p)] [NeZero n] (u : Fin n → ℝ) :
    ∃ v ∈ Z n, ‖WithLp.toLp p (u - v)‖ = delta u := by
  obtain ⟨i, hi⟩ := exists_delta_eq u
  refine ⟨u - Pi.single i (u i), ⟨i, by simp⟩, ?_⟩
  rw [sub_sub_cancel, norm_single_lp, hi]

/-- C5.2(i), sharpness: every ℓ_p ball about u of radius ρ > δ(u) contains u' with
rd(u') ≠ rd(u) (n ≥ 1). -/
theorem rd_sharp (p : ENNReal) [Fact (1 ≤ p)] [NeZero n] (u : Fin n → ℝ) (ρ : ℝ)
    (hρ : delta u < ρ) : ∃ u', ‖WithLp.toLp p (u' - u)‖ < ρ ∧ rd u' ≠ rd u := by
  obtain ⟨i, hi⟩ := exists_delta_eq u
  rcases le_or_gt 0 (u i) with hu | hu
  · refine ⟨u + Pi.single i (-(u i + ρ) / 2), ?_, ?_⟩
    · rw [abs_of_nonneg hu] at hi
      rw [add_sub_cancel_left, norm_single_lp, abs_of_nonpos (by linarith)]
      linarith
    · intro h
      have := congrFun h i
      rw [abs_of_nonneg hu] at hi
      simp only [rd, Pi.add_apply, Pi.single_eq_same, if_pos hu] at this
      rw [if_neg (by linarith)] at this
      omega
  · refine ⟨u + Pi.single i (-(u i)), ?_, ?_⟩
    · rw [add_sub_cancel_left, norm_single_lp, abs_neg, hi]; exact hρ
    · intro h
      have := congrFun h i
      simp only [rd, Pi.add_apply, Pi.single_eq_same, add_neg_cancel, le_refl, if_true,
        if_neg (not_le.mpr hu)] at this
      omega

end Readout

/-! ## Quadratic energies and the flip-difference formula (Remark C5.5, S2.15) -/

section Quadratic

variable {n : ℕ} {R : Type*} [CommRing R]

/-- E(y) = yᵀQy + cᵀy + e₀ evaluated at an integer vector y. -/
def quadEnergy (Q : Matrix (Fin n) (Fin n) R) (c : Fin n → R) (e0 : R) (y : Fin n → ℤ) : R :=
  (fun p => (y p : R)) ⬝ᵥ (Q *ᵥ fun p => (y p : R)) + c ⬝ᵥ (fun p => (y p : R)) + e0

/-- Flip-difference formula: for Q symmetric with zero diagonal,
Δᵢ = E(y^{(i)}) − E(y) = −2 yᵢ (2 (Qy)ᵢ + cᵢ). (Holds for every integer y.) -/
theorem quad_flip_diff (Q : Matrix (Fin n) (Fin n) R) (hQ : Q.IsSymm) (hd : ∀ i, Q i i = 0)
    (c : Fin n → R) (e0 : R) (y : Fin n → ℤ) (i : Fin n) :
    quadEnergy Q c e0 (flip y i) - quadEnergy Q c e0 y =
      -2 * (y i : R) * (2 * (Q *ᵥ fun p => (y p : R)) i + c i) := by
  set v : Fin n → R := fun p => (y p : R) with hv
  have hflip : (fun p => ((flip y i p : ℤ) : R)) = v + Pi.single i (-2 * v i) := by
    funext p
    by_cases hp : p = i
    · subst hp; simp [flip, hv]; ring
    · simp [flip, hv, hp]
  have hsym : v ⬝ᵥ (Q *ᵥ Pi.single i (-2 * v i)) = (-2 * v i) * (Q *ᵥ v) i := by
    rw [dotProduct_mulVec, dotProduct_single]
    have : v ᵥ* Q = Q *ᵥ v := by
      conv_lhs => rw [← hQ.eq]
      rw [vecMul_transpose]
    rw [this, mul_comm]
  unfold quadEnergy
  rw [hflip, ← hv]
  simp only [mulVec_add, dotProduct_add, add_dotProduct, single_dotProduct, dotProduct_single, hsym]
  have h0 : (Q *ᵥ Pi.single i (-2 * v i)) i = 0 := by
    simp [mulVec_single, hd i]
  rw [h0]
  simp only [hv]
  ring

end Quadratic

/-! ## Proposition C5.1: the gadget value lemma (S2.4–S2.6) -/

section Gadget

variable {n : ℕ} (a : Fin n → ℤ)

/-- A = Σᵢ aᵢ (= ‖a‖₁ for a > 0). -/
def gA : ℤ := ∑ i, a i

/-- The even penalty M = 2(A² + 1). -/
def gM : ℤ := 2 * (gA a ^ 2 + 1)

/-- E_a(x, z) = 4 s(x)² + (1 − z)(1 − 2A² + M Σᵢ(1 − xᵢ)), xᵢ = y(castSucc i), z = y(last). -/
def gadgetE (y : Fin (n + 1) → ℤ) : ℤ :=
  4 * (∑ i : Fin n, a i * y i.castSucc) ^ 2 +
    (1 - y (Fin.last n)) * (1 - 2 * gA a ^ 2 + gM a * ∑ i : Fin n, (1 - y i.castSucc))

/-- y* = (𝟏, −1). -/
def ystar : Fin (n + 1) → ℤ := Fin.lastCases (motive := fun _ => ℤ) (-1) (fun _ => 1)

/-- The stones (partition) instance a is solvable. -/
def Solvable : Prop := ∃ x ∈ Y n, ∑ i, a i * x i = 0

/-- SEP coupling matrix: Q_{xᵢxⱼ} = 4aᵢaⱼ (i ≠ j), Q_{xᵢz} = Q_{zxᵢ} = A² + 1, diag 0. -/
def gadgetQ : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ :=
  Matrix.of fun p q =>
    Fin.lastCases (motive := fun _ => ℤ)
      (Fin.lastCases (motive := fun _ => ℤ) 0 (fun _ => gA a ^ 2 + 1) q)
      (fun i => Fin.lastCases (motive := fun _ => ℤ) (gA a ^ 2 + 1)
        (fun j => if i = j then 0 else 4 * a i * a j) q) p

/-- SEP field: c_{xᵢ} = −M, c_z = −(1 − 2A² + nM). -/
def gadgetc : Fin (n + 1) → ℤ :=
  Fin.lastCases (motive := fun _ => ℤ) (-(1 - 2 * gA a ^ 2 + n * gM a)) (fun _ => -gM a)

/-- SEP constant: e₀ = 4Σaᵢ² + 1 − 2A² + nM. -/
def gadgete0 : ℤ := 4 * ∑ i, a i ^ 2 + 1 - 2 * gA a ^ 2 + n * gM a

@[simp] lemma ystar_castSucc (i : Fin n) : (ystar : Fin (n + 1) → ℤ) i.castSucc = 1 := by
  simp [ystar]

@[simp] lemma ystar_last : (ystar : Fin (n + 1) → ℤ) (Fin.last n) = -1 := by
  simp [ystar]

lemma ystar_mem : (ystar : Fin (n + 1) → ℤ) ∈ Y (n + 1) := by
  rw [mem_Y]
  intro p
  refine Fin.lastCases ?_ (fun i => ?_) p <;> simp

/-- S2.5: E_a(y*) = 2. -/
theorem gadget_E_ystar : gadgetE a ystar = 2 := by
  simp [gadgetE, gA]
  ring

lemma gadgetE_z_pos (y : Fin (n + 1) → ℤ) (hz : y (Fin.last n) = 1) :
    gadgetE a y = 4 * (∑ i : Fin n, a i * y i.castSucc) ^ 2 := by
  simp [gadgetE, hz]

lemma gadgetE_z_neg (y : Fin (n + 1) → ℤ) (hz : y (Fin.last n) = -1) :
    gadgetE a y = 4 * (∑ i : Fin n, a i * y i.castSucc) ^ 2 +
      2 * (1 - 2 * gA a ^ 2 + gM a * ∑ i : Fin n, (1 - y i.castSucc)) := by
  simp [gadgetE, hz]

lemma eq_ystar_of {y : Fin (n + 1) → ℤ} (hz : y (Fin.last n) = -1)
    (hx : ∀ i : Fin n, y i.castSucc = 1) : y = ystar := by
  funext p
  refine Fin.lastCases ?_ (fun i => ?_) p
  · simp [hz]
  · simp [hx i]

/-- At z = −1 and x ≠ 𝟏 the energy is at least 4A² + 10 (S2.5). -/
lemma gadgetE_ge_of_ne {y : Fin (n + 1) → ℤ} (hy : y ∈ Y (n + 1)) (hz : y (Fin.last n) = -1)
    (hne : y ≠ ystar) : 4 * gA a ^ 2 + 10 ≤ gadgetE a y := by
  rw [mem_Y] at hy
  have hx : ∃ i : Fin n, y i.castSucc = -1 := by
    by_contra hc
    push Not at hc
    exact hne (eq_ystar_of hz fun i => (hy i.castSucc).resolve_right (hc i))
  obtain ⟨i, hi⟩ := hx
  have hsum : 2 ≤ ∑ j : Fin n, (1 - y j.castSucc) := by
    have h0 : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ 1 - y j.castSucc := by
      intro j _; rcases hy j.castSucc with h | h <;> omega
    have := Finset.single_le_sum h0 (Finset.mem_univ i)
    simp only [hi] at this
    omega
  rw [gadgetE_z_neg a y hz]
  have hM : gM a = 2 * (gA a ^ 2 + 1) := rfl
  nlinarith [sq_nonneg (∑ i : Fin n, a i * y i.castSucc), sq_nonneg (gA a)]

/-- The energy is non-negative on 𝒴. -/
lemma gadgetE_nonneg {y : Fin (n + 1) → ℤ} (hy : y ∈ Y (n + 1)) : 0 ≤ gadgetE a y := by
  rcases (mem_Y.mp hy) (Fin.last n) with hz | hz
  · rw [gadgetE_z_pos a y hz]; positivity
  · by_cases hne : y = ystar
    · subst hne; rw [gadget_E_ystar]; norm_num
    · have := gadgetE_ge_of_ne a hy hz hne; nlinarith [sq_nonneg (gA a)]

/-- S2.5, per state: for y ∈ 𝒴 with y ≠ y*, E(y) = E(y*) − 2 iff z = +1 and aᵀx = 0. -/
theorem gadget_low_iff_state {y : Fin (n + 1) → ℤ} (hy : y ∈ Y (n + 1)) (hne : y ≠ ystar) :
    gadgetE a y = gadgetE a ystar - 2 ↔
      (y (Fin.last n) = 1 ∧ ∑ i : Fin n, a i * y i.castSucc = 0) := by
  rw [gadget_E_ystar]
  rcases (mem_Y.mp hy) (Fin.last n) with hz | hz
  · rw [gadgetE_z_pos a y hz]
    constructor
    · intro h; exact ⟨hz, by nlinarith [sq_nonneg (∑ i : Fin n, a i * y i.castSucc)]⟩
    · rintro ⟨_, h⟩; rw [h]; norm_num
  · have := gadgetE_ge_of_ne a hy hz hne
    constructor
    · intro h; nlinarith [sq_nonneg (gA a)]
    · rintro ⟨h, _⟩; omega

/-- S2.5: every state y ≠ y* has E(y) ≥ E(y*) + 2 or E(y) = E(y*) − 2. -/
theorem gadget_dichotomy {y : Fin (n + 1) → ℤ} (hy : y ∈ Y (n + 1)) (hne : y ≠ ystar) :
    gadgetE a ystar + 2 ≤ gadgetE a y ∨ gadgetE a y = gadgetE a ystar - 2 := by
  rw [gadget_E_ystar]
  rcases (mem_Y.mp hy) (Fin.last n) with hz | hz
  · rw [gadgetE_z_pos a y hz]
    by_cases hs : ∑ i : Fin n, a i * y i.castSucc = 0
    · right; rw [hs]; norm_num
    · left
      have : 0 < (∑ i : Fin n, a i * y i.castSucc) ^ 2 := by positivity
      omega
  · left
    have := gadgetE_ge_of_ne a hy hz hne
    nlinarith [sq_nonneg (gA a)]

/-- The state (x, +1) for x ∈ {±1}ⁿ. -/
def liftPos (x : Fin n → ℤ) : Fin (n + 1) → ℤ := Fin.lastCases (motive := fun _ => ℤ) 1 x

lemma liftPos_mem {x : Fin n → ℤ} (hx : x ∈ Y n) : liftPos x ∈ Y (n + 1) := by
  rw [mem_Y] at *
  intro p
  refine Fin.lastCases ?_ (fun i => ?_) p <;> simp [liftPos, hx]

lemma liftPos_ne (x : Fin n → ℤ) : liftPos x ≠ ystar := by
  intro h
  have := congrFun h (Fin.last n)
  simp [liftPos] at this

/-- S2.5: a state with E(y) = E(y*) − 2 exists iff the stones instance is solvable. -/
theorem gadget_low_iff_solvable :
    (∃ y ∈ Y (n + 1), y ≠ ystar ∧ gadgetE a y = gadgetE a ystar - 2) ↔ Solvable a := by
  constructor
  · rintro ⟨y, hy, hne, h⟩
    obtain ⟨_, hs⟩ := (gadget_low_iff_state a hy hne).mp h
    refine ⟨fun i => y i.castSucc, ?_, hs⟩
    rw [mem_Y] at *
    exact fun i => hy i.castSucc
  · rintro ⟨x, hx, hs⟩
    refine ⟨liftPos x, liftPos_mem hx, liftPos_ne x, ?_⟩
    rw [gadget_low_iff_state a (liftPos_mem hx) (liftPos_ne x)]
    simp [liftPos, hs]

/-- S2.5: m_glob(y*) = −2 if solvable, and m_glob(y*) = m ≥ 2 (finite) otherwise;
so m_glob ∈ {−2} ∪ [2, ∞), and m_glob = −2 exactly when the instance is solvable. -/
theorem gadget_mglob :
    (Solvable a → mglob (gadgetE a) ystar = ((-2 : ℤ) : WithTop ℤ)) ∧
    (¬ Solvable a → ∃ m : ℤ, 2 ≤ m ∧ mglob (gadgetE a) ystar = m) ∧
    (mglob (gadgetE a) ystar = ((-2 : ℤ) : WithTop ℤ) ↔ Solvable a) := by
  have lower : ∀ v ∈ (((Y (n + 1)).filter fun y => y ≠ ystar).image
      fun y => gadgetE a y - gadgetE a ystar), -2 ≤ v := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
    have := gadgetE_nonneg a (Finset.mem_filter.mp hy).1
    rw [gadget_E_ystar]; omega
  have hsol : Solvable a → mglob (gadgetE a) ystar = ((-2 : ℤ) : WithTop ℤ) := by
    intro h
    obtain ⟨y, hy, hne, hE⟩ := (gadget_low_iff_solvable a).mpr h
    apply le_antisymm
    · have hmem : gadgetE a y - gadgetE a ystar ∈ (((Y (n + 1)).filter fun y => y ≠ ystar).image
          fun y => gadgetE a y - gadgetE a ystar) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hy, hne⟩)
      have := Finset.min_le hmem
      unfold mglob
      rw [hE, sub_sub_cancel_left] at this
      exact this
    · unfold mglob
      exact Finset.le_min fun v hv => WithTop.coe_le_coe.mpr (lower v hv)
  have hunsol : ¬ Solvable a → ∃ m : ℤ, 2 ≤ m ∧ mglob (gadgetE a) ystar = m := by
    intro h
    have hne : (((Y (n + 1)).filter fun y => y ≠ ystar).image
        fun y => gadgetE a y - gadgetE a ystar).Nonempty := by
      refine ⟨_, Finset.mem_image_of_mem _ (Finset.mem_filter.mpr
        ⟨flip_mem_Y ystar_mem (Fin.last n), ?_⟩)⟩
      intro hc
      have := congrFun hc (Fin.last n)
      simp [flip] at this
    obtain ⟨m, hm⟩ := Finset.min_of_nonempty hne
    refine ⟨m, ?_, hm⟩
    obtain ⟨y, hy, hym⟩ := Finset.mem_image.mp (Finset.mem_of_min hm)
    obtain ⟨hyY, hyne⟩ := Finset.mem_filter.mp hy
    rcases gadget_dichotomy a hyY hyne with h1 | h1
    · omega
    · exact absurd ((gadget_low_iff_solvable a).mp ⟨y, hyY, hyne, h1⟩) h
  refine ⟨hsol, hunsol, ⟨fun h => ?_, hsol⟩⟩
  by_contra hc
  obtain ⟨m, hm, hm'⟩ := hunsol hc
  rw [h] at hm'
  have := WithTop.coe_injective hm'
  omega

/-- S2.6: the neighbour (𝟏, +1) has energy 4A². -/
theorem gadget_E_flip_last : gadgetE a (flip ystar (Fin.last n)) = 4 * gA a ^ 2 := by
  rw [gadgetE_z_pos]
  · congr 2
    unfold gA
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [flip]
  · simp [flip]

/-- S2.6: the neighbour (𝟏^{(i)}, −1) has energy 4(A − 2aᵢ)² + 4A² + 10. -/
theorem gadget_E_flip_castSucc (i : Fin n) :
    gadgetE a (flip ystar i.castSucc) = 4 * (gA a - 2 * a i) ^ 2 + 4 * gA a ^ 2 + 10 := by
  have hval : ∀ j : Fin n, (flip ystar i.castSucc) j.castSucc = if j = i then -1 else 1 := by
    intro j
    by_cases hj : j = i
    · subst hj; simp [flip]
    · simp [flip, hj]
  have hz : (flip ystar i.castSucc) (Fin.last n) = -1 := by
    simp [flip, Function.update_of_ne (Fin.castSucc_ne_last i).symm]
  rw [gadgetE_z_neg a _ hz]
  simp only [hval]
  have h1 : ∑ j, a j * (if j = i then (-1 : ℤ) else 1) = gA a - 2 * a i := by
    have : ∀ j, a j * (if j = i then (-1 : ℤ) else 1) = a j - 2 * (if j = i then a j else 0) := by
      intro j; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      Finset.mem_univ, if_true, gA]
  have h2 : ∑ j : Fin n, (1 - (if j = i then (-1 : ℤ) else 1)) = 2 := by
    have : ∀ j : Fin n, (1 - (if j = i then (-1 : ℤ) else 1)) = if j = i then 2 else 0 := by
      intro j; split_ifs <;> ring
    simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [h1, h2]
  simp only [gM]
  ring

/-- S2.6: m₁(y*) = 4A² − 2 (the flip margin). -/
theorem gadget_flipMargin :
    flipMargin (gadgetE a) ystar = ((4 * gA a ^ 2 - 2 : ℤ) : WithTop ℤ) := by
  unfold flipMargin
  apply le_antisymm
  · have hmem : gadgetE a (flip ystar (Fin.last n)) - gadgetE a ystar ∈
        ((univ : Finset (Fin (n + 1))).image fun i => gadgetE a (flip ystar i) - gadgetE a ystar) :=
      Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hv : gadgetE a (flip ystar (Fin.last n)) - gadgetE a ystar = 4 * gA a ^ 2 - 2 := by
      rw [gadget_E_flip_last, gadget_E_ystar]
    have := Finset.min_le hmem
    rw [hv] at this
    exact this
  · apply Finset.le_min
    intro v hv
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hv
    rw [WithTop.coe_le_coe]
    refine Fin.lastCases ?_ (fun i => ?_) p
    · simp only [gadget_E_flip_last, gadget_E_ystar]; exact le_rfl
    · simp only [gadget_E_flip_castSucc, gadget_E_ystar]
      nlinarith [sq_nonneg (gA a - 2 * a i)]

/-- S2.6: m₁(y*) = 4A² − 2 as the neighbourhood margin at radius 1. -/
theorem gadget_margin_one :
    margin (gadgetE a) ystar 1 = ((4 * gA a ^ 2 - 2 : ℤ) : WithTop ℤ) := by
  rw [margin_one_eq_flipMargin _ ystar_mem, gadget_flipMargin]

/-- C5.1(2): for a ∈ ℤ_{>0}ⁿ, n ≥ 1, the instance is strictly 1-optimal with m₁ ≥ 2. -/
theorem gadget_m1_ge_two (hn : 1 ≤ n) (ha : ∀ i, 0 < a i) : 2 ≤ 4 * gA a ^ 2 - 2 := by
  have : 1 ≤ gA a := by
    have h0 : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ a j := fun j _ => (ha j).le
    have := Finset.single_le_sum h0 (Finset.mem_univ ⟨0, hn⟩)
    have := ha ⟨0, hn⟩
    unfold gA; omega
  nlinarith

/-- Off-diagonal quadratic form: Σᵢ xᵢ Σⱼ [i ≠ j] 4aᵢaⱼ xⱼ = 4(aᵀx)² − 4Σᵢ aᵢ² xᵢ². -/
lemma offdiag_form (x : Fin n → ℤ) :
    ∑ i, x i * ∑ j, (if i = j then 0 else 4 * a i * a j) * x j =
      4 * (∑ i, a i * x i) ^ 2 - 4 * ∑ i, a i ^ 2 * x i ^ 2 := by
  have h : ∀ i, x i * ∑ j, (if i = j then 0 else 4 * a i * a j) * x j =
      ∑ j, 4 * (a i * x i) * (a j * x j) - 4 * (a i ^ 2 * x i ^ 2) := by
    intro i
    have : ∀ j, (if i = j then 0 else 4 * a i * a j) * x j =
        4 * a i * a j * x j - (if i = j then 4 * a i * a j * x j else 0) := by
      intro j; split_ifs <;> ring
    simp only [this, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
      Finset.mul_sum, mul_sub]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_; ring
    · ring
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_sub_distrib, ← Finset.mul_sum]
  congr 1
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/-- SEP format (S2.4): Q symmetric, zero diagonal, integral (entries in ℤ), and
E_a(y) = yᵀQy + cᵀy + e₀ for every y ∈ {±1}^{n+1}. -/
theorem gadget_format :
    (gadgetQ a).IsSymm ∧ (∀ p, gadgetQ a p p = 0) ∧
    ∀ y ∈ Y (n + 1), gadgetE a y = quadEnergy (gadgetQ a) (gadgetc a) (gadgete0 a) y := by
  refine ⟨?_, ?_, ?_⟩
  · refine Matrix.IsSymm.ext fun p q => ?_
    refine Fin.lastCases ?_ (fun i => ?_) p <;> refine Fin.lastCases ?_ (fun j => ?_) q <;>
      simp [gadgetQ]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · ring
  · intro p
    refine Fin.lastCases ?_ (fun i => ?_) p <;> simp [gadgetQ]
  · intro y hy
    rw [mem_Y] at hy
    have hsq : ∀ i : Fin n, y i.castSucc ^ 2 = 1 := by
      intro i; rcases hy i.castSucc with h | h <;> simp [h]
    unfold quadEnergy
    simp only [Int.cast_id]
    have hQ : y ⬝ᵥ (gadgetQ a *ᵥ y) =
        ∑ i : Fin n, y i.castSucc * ∑ j : Fin n, (if i = j then 0 else 4 * a i * a j) * y j.castSucc +
          2 * (gA a ^ 2 + 1) * y (Fin.last n) * ∑ i : Fin n, y i.castSucc := by
      simp only [dotProduct, mulVec, Fin.sum_univ_castSucc, gadgetQ, Matrix.of_apply,
        Fin.lastCases_castSucc, Fin.lastCases_last]
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
      ring
    have hc : gadgetc a ⬝ᵥ y = -gM a * ∑ i : Fin n, y i.castSucc -
        (1 - 2 * gA a ^ 2 + n * gM a) * y (Fin.last n) := by
      simp only [dotProduct, Fin.sum_univ_castSucc, gadgetc, Fin.lastCases_castSucc,
        Fin.lastCases_last, ← Finset.mul_sum]
      ring
    have hy' : (fun p => y p) = y := rfl
    rw [hy', hQ, hc, offdiag_form]
    simp only [hsq, mul_one]
    unfold gadgetE gadgete0 gM
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
    ring

end Gadget

/-! ## Proposition C5.3(b): the family E_n -/

section Family

/-- 𝟏. -/
def ones (n : ℕ) : Fin n → ℤ := fun _ => 1

/-- E_n(x) = ½(n(n − 2) + Σᵢxᵢ) − Σ_{i<j} xᵢxⱼ. -/
noncomputable def En (n : ℕ) (x : Fin n → ℤ) : ℝ :=
  ((n : ℝ) * (n - 2) + ∑ i, (x i : ℝ)) / 2 - ∑ i, ∑ j, if i < j then (x i : ℝ) * x j else 0

lemma sum_spin_eq {n : ℕ} {x : Fin n → ℤ} (hx : x ∈ Y n) :
    ∑ i, (x i : ℝ) = n - 2 * (hammingDist x (ones n) : ℝ) := by
  rw [mem_Y] at hx
  have h : ∀ i, (x i : ℝ) = 1 - 2 * (if x i ≠ ones n i then (1 : ℝ) else 0) := by
    intro i; rcases hx i with h | h <;> simp [h, ones]; norm_num
  simp only [h, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  unfold hammingDist
  rw [Finset.natCast_card_filter]

lemma pair_sum_eq {n : ℕ} {x : Fin n → ℤ} (hx : x ∈ Y n) :
    2 * ∑ i, ∑ j, (if i < j then (x i : ℝ) * x j else 0) = (∑ i, (x i : ℝ)) ^ 2 - n := by
  rw [mem_Y] at hx
  have hsq : ∀ i, (x i : ℝ) * x i = 1 := by
    intro i; rcases hx i with h | h <;> simp [h]
  have split : ∀ i j, (x i : ℝ) * x j = (if i < j then (x i : ℝ) * x j else 0) +
      (if i = j then (x i : ℝ) * x j else 0) + (if j < i then (x i : ℝ) * x j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le]
  have hswap : ∑ i, ∑ j, (if j < i then (x i : ℝ) * x j else 0) =
      ∑ i, ∑ j, (if i < j then (x i : ℝ) * x j else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> ring
  have : (∑ i, (x i : ℝ)) ^ 2 = ∑ i, ∑ j, (x i : ℝ) * x j := by
    rw [sq, Finset.sum_mul_sum]
  rw [this, Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => split i j]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ,
    if_true, hsq, hswap, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

/-- S2.13: on 𝒴, E_n(x) = k(2n − 1 − 2k) with k = d_H(x, 𝟏). -/
theorem En_eq {n : ℕ} {x : Fin n → ℤ} (hx : x ∈ Y n) :
    En n x = (hammingDist x (ones n) : ℝ) * (2 * n - 1 - 2 * (hammingDist x (ones n) : ℝ)) := by
  have h1 := sum_spin_eq hx
  have h2 := pair_sum_eq hx
  unfold En
  have : ∑ i, ∑ j, (if i < j then (x i : ℝ) * x j else 0) =
      ((∑ i, (x i : ℝ)) ^ 2 - n) / 2 := by linarith
  rw [this, h1]
  ring

lemma ones_mem (n : ℕ) : ones n ∈ Y n := by rw [mem_Y]; intro i; simp [ones]

/-- C5.3(b): for n ≥ 2, m_{n−1}(𝟏) = n − 1 and m_glob(𝟏) = −n for E_n. -/
theorem En_margins (n : ℕ) (hn : 2 ≤ n) :
    margin (En n) (ones n) (n - 1) = (((n : ℝ) - 1 : ℝ) : WithTop ℝ) ∧
    mglob (En n) (ones n) = ((-(n : ℝ) : ℝ) : WithTop ℝ) := by
  have h0 : En n (ones n) = 0 := by
    rw [En_eq (ones_mem n), hammingDist_self]; simp
  have hk : ∀ y : Fin n → ℤ, hammingDist y (ones n) ≤ n := fun y => by
    simpa using (hammingDist_le_card_fintype (x := y) (y := ones n))
  constructor
  · unfold margin
    apply le_antisymm
    · -- witness: one +1 coordinate, the rest −1 (k = n − 1)
      set w : Fin n → ℤ := fun i => if i.val = 0 then 1 else -1 with hw
      have wY : w ∈ Y n := by
        rw [mem_Y]; intro i; by_cases h : i.val = 0 <;> simp [hw, h]
      have hd : hammingDist w (ones n) = n - 1 := by
        unfold hammingDist
        have : (univ.filter fun i => w i ≠ ones n i) = univ.erase ⟨0, by omega⟩ := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq,
            and_true, hw, ones, Fin.ext_iff]
          by_cases h : i.val = 0 <;> simp [h]
        rw [this, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
          Fintype.card_fin]
      have hmem : En n w - En n (ones n) ∈ (((Y n).filter fun y => 1 ≤ hammingDist y (ones n) ∧
          hammingDist y (ones n) ≤ n - 1).image fun y => En n y - En n (ones n)) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨wY, by omega, by omega⟩)
      have hv : En n w - En n (ones n) = (n : ℝ) - 1 := by
        rw [h0, sub_zero, En_eq wY, hd, Nat.cast_sub (by omega)]; push_cast; ring
      have := Finset.min_le hmem
      rw [hv] at this
      exact this
    · apply Finset.le_min
      intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hyY, h1, h2⟩ := Finset.mem_filter.mp hy
      rw [WithTop.coe_le_coe, h0, sub_zero, En_eq hyY]
      have hk1 : (1 : ℝ) ≤ hammingDist y (ones n) := by exact_mod_cast h1
      have hk2 : (hammingDist y (ones n) : ℝ) + 1 ≤ n := by
        have : hammingDist y (ones n) + 1 ≤ n := by omega
        exact_mod_cast this
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n - 1 - hammingDist y (ones n))
        (by linarith : (0 : ℝ) ≤ 2 * hammingDist y (ones n) - 1)]
  · unfold mglob
    apply le_antisymm
    · -- witness: −𝟏 (k = n)
      have wY : (fun _ : Fin n => (-1 : ℤ)) ∈ Y n := by rw [mem_Y]; intro i; simp
      have hd : hammingDist (fun _ : Fin n => (-1 : ℤ)) (ones n) = n := by
        unfold hammingDist
        have : (univ.filter fun i : Fin n => (-1 : ℤ) ≠ ones n i) = univ := by
          ext i; simp [ones]
        rw [this, Finset.card_univ, Fintype.card_fin]
      have hne : (fun _ : Fin n => (-1 : ℤ)) ≠ ones n := by
        intro h; have := congrFun h ⟨0, by omega⟩; simp [ones] at this
      have hmem : En n (fun _ => -1) - En n (ones n) ∈ (((Y n).filter fun y => y ≠ ones n).image
          fun y => En n y - En n (ones n)) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨wY, hne⟩)
      have hv : (En n fun _ => -1) - En n (ones n) = -(n : ℝ) := by
        rw [h0, sub_zero, En_eq wY, hd]; ring
      have := Finset.min_le hmem
      rw [hv] at this
      exact this
    · apply Finset.le_min
      intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hyY, hne⟩ := Finset.mem_filter.mp hy
      rw [WithTop.coe_le_coe, h0, sub_zero, En_eq hyY]
      have h1 : 1 ≤ hammingDist y (ones n) := hammingDist_pos.mpr hne
      have hk1 : (1 : ℝ) ≤ hammingDist y (ones n) := by exact_mod_cast h1
      have hk2 : (hammingDist y (ones n) : ℝ) ≤ n := by exact_mod_cast hk y
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ n - hammingDist y (ones n))
        (by linarith : (0 : ℝ) ≤ 2 * hammingDist y (ones n) + 1)]

end Family

/-! ## Example C5.4 (two spins) -/

section TwoSpins

/-- E(x) = x₁ + x₂ − 3x₁x₂. -/
def E2 (x : Fin 2 → ℤ) : ℤ := x 0 + x 1 - 3 * x 0 * x 1

lemma Y2_cases {x : Fin 2 → ℤ} (hx : x ∈ Y 2) :
    (x 0 = 1 ∨ x 0 = -1) ∧ (x 1 = 1 ∨ x 1 = -1) := ⟨(mem_Y.mp hx) 0, (mem_Y.mp hx) 1⟩

/-- Ex. C5.4: u = (1, 1) has δ(u) = 1 and rd(u) = 𝟏; m₁(𝟏) = 4 and m_glob(𝟏) = −4. -/
theorem two_spins :
    delta (fun _ : Fin 2 => (1 : ℝ)) = 1 ∧ rd (fun _ : Fin 2 => (1 : ℝ)) = ones 2 ∧
    margin E2 (ones 2) 1 = ((4 : ℤ) : WithTop ℤ) ∧ mglob E2 (ones 2) = ((-4 : ℤ) : WithTop ℤ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [delta]
  · funext i; simp [rd, ones]
  · rw [margin_one_eq_flipMargin _ (ones_mem 2)]
    unfold flipMargin
    have : ((univ : Finset (Fin 2)).image fun i => E2 (flip (ones 2) i) - E2 (ones 2)) = {4} := by
      ext v
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp [E2, flip, ones]
      · rintro rfl; exact ⟨0, by simp [E2, flip, ones]⟩
    rw [this, Finset.min_singleton]
  · unfold mglob
    apply le_antisymm
    · have wY : (fun _ : Fin 2 => (-1 : ℤ)) ∈ Y 2 := by rw [mem_Y]; intro i; simp
      have hne : (fun _ : Fin 2 => (-1 : ℤ)) ≠ ones 2 := by
        intro h; have := congrFun h 0; simp [ones] at this
      have hmem : E2 (fun _ => -1) - E2 (ones 2) ∈ (((Y 2).filter fun y => y ≠ ones 2).image
          fun y => E2 y - E2 (ones 2)) :=
        Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨wY, hne⟩)
      have := Finset.min_le hmem
      simpa [E2, ones] using this
    · apply Finset.le_min
      intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      rw [WithTop.coe_le_coe]
      obtain ⟨h0, h1⟩ := Y2_cases (Finset.mem_filter.mp hy).1
      simp only [E2, ones]
      rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] <;> norm_num

end TwoSpins

end OCF.C6

/-
A3 (Störmer–Verlet: the scope of the conservative primitive) — the cheap Lean targets named in
the stage-3 adjudication (§4 "Formalisation tier", DECISION D9, and the §8 addendum): Proposition
B in d = 1 (invariance, det S = 1, the sandwich for all n ∈ ℤ, the constant γ, the edge hω = 2),
Proposition B / Corollary B′ in general d with general mass, the algebra of C.3 (product, trace,
determinant, eigen-direction, sign pattern, the period-3 orbit), Example C′ (C.7, both exact
instances), and the countability (continuant) lemma of C.8 Step 2 (LR III Lemma 4.1, as used).
Also, cheaply on the way: Proposition A(ii)–(iii) (every step, every force, general d and mass),
C.1 (scaling), C.2 (Φ₁ ∘ K_{1/2} = K_{1/2} ∘ G), C.2′ (G_k C_LR = C_LR T_{2−k}), one attained
instance of B(iv), and Proposition C(b) for the C¹ piecewise-linear potential.

Source of truth: project_plan/done/proof_audits/A3_stormer_verlet/01_derivation.md (adjudicated and
re-audited 2026-10-10; sha16 d79b41bdeabc105a at the start and at the end of formalisation; file
not edited), 03_adjudication.md (§4, §8 addendum, D9). PROSE-ONLY by ruling and not attempted:
the C⁴ smoothing (C.4–C.5), the exact-flow claim C(c), Corollary C.8 (rests on cited LR III
Thms 2.1, 2.4 and LR I Thm 2.4), Proposition A(i) (symplecticity), B(iv) density, B(v) for hω > 2,
item (d).

DEFINITIONAL MAP:
* Φ_h (d = 1, unit mass, force f = V′, every real h) — `sv f h`; general d with force F = ∇V and
  N = M_p⁻¹ — `svD F N h` on `(Fin d → ℝ) × (Fin d → ℝ)`. The formula is the dossier's 0.1:
  p½ = p − (h/2)F(q), q' = q + hN p½, p' = p½ − (h/2)F(q').
* ρ — `flip`, `flipD`. The ℤ-orbit y_n = Φ_hⁿ(y₀), n ∈ ℤ — `orbit`, `orbitD` (via `zIter`, with
  negative n through Φ_{−h}; `orbit_succ`/`orbitD_succ`: y_{n+1} = Φ_h(y_n) for all n ∈ ℤ).
* d = 1, V = ½kq² (k = ω²): force `lin k`; H — `Hk k`; E_h = ½p² + ½k(1 − h²k/4)q² — `Eh h k`
  (at k = ω² this is ½p² + ½(ω² − h²ω⁴/4)q², restated literally in `Eh_sv_omega`); S — `S h k`.
  r = (hω)²/4, γ = (hω)²/(4 − (hω)²) are written out. Hypothesis hω < 2 (with h > 0, ω ≥ 0) is
  stated as (hω)² < 4, which contains it.
* general d: H = ½pᵀNp + ½qᵀAq — `HD A N`; E_h = ½pᵀNp + ½qᵀ(A − (h²/4)ANA)q — `EhD h A N`
  (B.9's form with N = M_p⁻¹; `EhD_one_eq`: at N = I it is ½|p|² + ½qᵀA(I − (h²/4)A)q).
  A symmetric: `Aᵀ = A`; A ⪰ 0: `∀ x, 0 ≤ xᵀAx`; M_p ≻ 0: `M.PosDef`. The constant ω_max:
  for M_p = I, "every eigenvalue of A lies in [0, ω²]" (`propB_iii_eig`, ω ≥ ω_max, equality
  allowed); for general M_p, "A ⪯ ω²M_p" (`∀ x, xᵀAx ≤ ω² xᵀM_p x`), the generalised Rayleigh
  form of ω² ≥ λ_max(M_p⁻¹A) (that equivalence itself is not formalised for M_p ≠ I).
  "A² ⪯ ω²A" / "AM_p⁻¹A ⪯ ω²A" is PROVED (`ANA_le`), not assumed.
* C.1–C.3: kick K_s — `kick`; G = D₁ ∘ K₁ — `Gmap`; two-slope force (a on q ≥ 0, b on q < 0) —
  `pw a b`, its C¹ potential — `Vpw a b` (`hasDerivAt_Vpw`: Vpw' = pw everywhere); G_k — `Gk k`;
  P = G_aG_bG_a — `Pmat δ`; τ = δ²(1 − δ) — `tau`; λ₊ = 1 + τ/2 + √(τ + τ²/4) — `lamP`;
  P₁₁ — `P11`; v = (δ², P₁₁ − λ₊) — `vP`; the map with slopes (3 − δ, 3 + δ) — `Gpw δ`.
  C.2′: T_f — `Tlr f`, C_LR — `CLR`.
* C.7: P along the word (first letter rightmost) — `ex1P`, `ex2P`; λ₊ = (T + √(T² − 4))/2 —
  `ex1Lam`, `ex2Lam`; v = ±(P₁₂, λ₊ − P₁₁), sign chosen so q₀ has the first letter's sign (as
  in a3_witness.py) — `ex1V`, `ex2V`. Bounds on λ₊ are rational (`*_lam_bounds`).
* C.8 Step 2: polynomials in E = E_LR over ℝ (`ℝ[X]`); f₊ = 2 − E + μ, f₋ = 2 − E − μ —
  `fpoly μ s` (s = true for +); T_f — `Tpoly`; T_w := T_{f_ℓ} ⋯ T_{f_1} — `Tw μ w`; u_w — `uw μ w`.
  Bad(μ) — the set {E | ∃ w ≠ [], u_w(E) = 0} (the empty word is excluded: T_∅ = I has u = 0;
  every ray word has ℓ ≥ 1).

THEOREMS:
* Prop. A(ii), (iii): `sv_neg_sv`, `sv_sv_neg`, `flip_sv_flip` (d = 1); `svD_neg_svD`,
  `svD_svD_neg`, `flipD_svD_flipD` (general d, any N, any force, every h).
* Prop. B, d = 1: B.1 `sv_lin_eq_S`; `det_S`; B(i) `Eh_sv`, `Eh_sv_omega`, `Eh_orbit`;
  B(ii) `sandwich_pointwise`; γ `gamma_eq`; B(iii) `propB_iii` (every n ∈ ℤ); B(iv) one attained
  instance `sharp_instance`; B(v) edge: `S_pow_edge` (Sⁿ = (−1)ⁿ[[1, −nh], [0, 1]]),
  `iterate_edge`, `H_edge` (H_n = ½p₀² + ½ω²(q₀ − nhp₀)²), `edge_unbounded` (p₀ ≠ 0),
  `edge_p_zero`.
* Prop. B / Cor. B′, general d: B(i) `EhD_svD`, `EhD_orbitD` (A, N symmetric; every h);
  `ANA_le`; B(ii) `sandwichD`; B(iii) `propBprime_iii` (general mass), `propB_iii_eig`
  (M_p = I, eigenvalue hypotheses).
* Prop. C (piecewise-linear part): C.1 `sv_scale`, `sv_scale_iterate`; C.2 `sv_kick`,
  `sv_iterate_kick`; C.2′ `conj_LR`; C.3 `GbGa`, `Pmat_eq`, `trace_Pmat`, `det_Pmat`,
  `trace_Pmat_gt_two`, `lamP_charpoly`, `lamP_gt_one`, `Pmat_mulVec_v`, `P11_bounds`,
  `C3_signs` ((+, −, +) and G³v = λ₊v), `C3_orbit` (G^{3m+j}(tv) = tλ₊^m G^j v);
  `propC_b_pl` (Prop. C(b) for the C¹ two-slope potential at every h > 0, with H → ∞).
* C.7: `ex1_trace_gt_two`, `ex1_orbit` ((1/4, 13/20), period 10, +++----+++);
  `ex2_trace_gt_two`, `ex2_orbit` ((7/40, 5/16), period 13, ---+++++++---).
* C.8 Step 2: `uw_degree` (exact degree ℓ − 1, leading coefficient (−1)^ℓ, every μ),
  `uw_ne_zero`, `bad_countable`, `uw_eval_zero_of_ray`, `Tpoly_eval`.

NOT COVERED: Prop. A(i); B(iv) beyond one instance; B(v) for hω > 2; C.4–C.5, C(a) (C⁴), C(c);
C.6, C.8 (beyond Step 2), C.9–C.11; block E illustrations; (d).

Status tier: FORMALISED (statement + proof, no sorry) for every theorem listed above.
-/
import Mathlib

open Matrix Filter Topology

noncomputable section

namespace OCF.A3

/-! ## Part A (d = 1 and general d): the Störmer–Verlet map -/

/-- One Störmer–Verlet step in d = 1, unit mass, force `f = V′`, step `h ∈ ℝ`:
p½ = p − (h/2) f(q), q' = q + h p½, p' = p½ − (h/2) f(q'). -/
def sv (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) : ℝ × ℝ :=
  (y.1 + h * (y.2 - h / 2 * f y.1),
   (y.2 - h / 2 * f y.1) - h / 2 * f (y.1 + h * (y.2 - h / 2 * f y.1)))

/-- Proposition A(ii), d = 1, every force and every step: Φ_{−h} ∘ Φ_h = id. -/
theorem sv_neg_sv (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) : sv f (-h) (sv f h y) = y := by
  obtain ⟨q, p⟩ := y
  simp only [sv, Prod.mk.injEq]
  constructor
  · ring_nf
  · ring_nf

/-- Proposition A(ii), d = 1: Φ_h ∘ Φ_{−h} = id. -/
theorem sv_sv_neg (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) : sv f h (sv f (-h) y) = y := by
  simpa using sv_neg_sv f (-h) y

/-- Momentum flip ρ(q, p) = (q, −p). -/
def flip (y : ℝ × ℝ) : ℝ × ℝ := (y.1, -y.2)

/-- Proposition A(iii), d = 1, every force and every step: ρ ∘ Φ_h ∘ ρ = Φ_{−h} = Φ_h⁻¹. -/
theorem flip_sv_flip (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) : flip (sv f h (flip y)) = sv f (-h) y := by
  obtain ⟨q, p⟩ := y
  simp only [flip, sv, Prod.mk.injEq]
  constructor
  · ring_nf
  · ring_nf

/-- ℤ-iteration of a map `g` with inverse `g'`: n ≥ 0 ↦ gⁿ(y), n < 0 ↦ g'^{−n}(y). -/
def zIter {α : Type*} (g g' : α → α) (y : α) (n : ℤ) : α :=
  if 0 ≤ n then g^[n.toNat] y else g'^[(-n).toNat] y

theorem zIter_zero {α : Type*} (g g' : α → α) (y : α) : zIter g g' y 0 = y := by
  simp [zIter]

/-- If g ∘ g' = id, `zIter` is the ℤ-orbit: y_{n+1} = g(y_n) for every n ∈ ℤ. -/
theorem zIter_succ {α : Type*} {g g' : α → α} (hg : ∀ x, g (g' x) = x) (y : α) (n : ℤ) :
    zIter g g' y (n + 1) = g (zIter g g' y n) := by
  rcases le_or_gt 0 n with hn | hn
  · have h1 : (n + 1).toNat = n.toNat + 1 := by omega
    simp only [zIter, if_pos hn, if_pos (by omega : (0:ℤ) ≤ n + 1), h1,
      Function.iterate_succ_apply']
  · rcases (show n = -1 ∨ n < -1 by omega) with rfl | hn'
    · simp [zIter, hg]
    · have h1 : (-n).toNat = (-(n + 1)).toNat + 1 := by omega
      simp only [zIter, if_neg (by omega : ¬ (0:ℤ) ≤ n + 1), if_neg (by omega : ¬ (0:ℤ) ≤ n), h1,
        Function.iterate_succ_apply', hg]

/-- A quantity invariant under g and g' is constant along the ℤ-orbit. -/
theorem zIter_invariant {α : Type*} {g g' : α → α} (E : α → ℝ) (hE : ∀ x, E (g x) = E x)
    (hE' : ∀ x, E (g' x) = E x) (y : α) (n : ℤ) : E (zIter g g' y n) = E y := by
  have hit : ∀ (k : α → α), (∀ z, E (k z) = E z) → ∀ m : ℕ, E (k^[m] y) = E y := by
    intro k hk m
    induction m with
    | zero => rfl
    | succ m ih => rw [Function.iterate_succ_apply', hk, ih]
  unfold zIter
  split_ifs
  · exact hit _ hE _
  · exact hit _ hE' _

/-- The ℤ-indexed Störmer–Verlet orbit y_n = Φ_hⁿ(y₀) (negative n via Φ_h⁻¹ = Φ_{−h}). -/
def orbit (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) (n : ℤ) : ℝ × ℝ := zIter (sv f h) (sv f (-h)) y n

theorem orbit_zero (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) : orbit f h y 0 = y := zIter_zero _ _ _

/-- `orbit` is the ℤ-orbit: y_{n+1} = Φ_h(y_n) for every n ∈ ℤ. -/
theorem orbit_succ (f : ℝ → ℝ) (h : ℝ) (y : ℝ × ℝ) (n : ℤ) :
    orbit f h y (n + 1) = sv f h (orbit f h y n) := zIter_succ (sv_sv_neg f h) y n

/-! ## Proposition B, d = 1: V = ½ k q² (k = ω² for Proposition B) -/

/-- The linear force of V = ½ k q². -/
def lin (k : ℝ) : ℝ → ℝ := fun q => k * q

/-- True energy H(q, p) = ½p² + ½kq². -/
def Hk (k : ℝ) (y : ℝ × ℝ) : ℝ := y.2 ^ 2 / 2 + k * y.1 ^ 2 / 2

/-- Modified (shadow) energy E_h(q, p) = ½p² + ½k(1 − h²k/4)q². With k = ω² this is
½p² + ½(ω² − h²ω⁴/4)q². -/
def Eh (h k : ℝ) (y : ℝ × ℝ) : ℝ := y.2 ^ 2 / 2 + k * (1 - h ^ 2 * k / 4) * y.1 ^ 2 / 2

/-- B.1: the step matrix S in (q, p) coordinates. -/
def S (h k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 - h ^ 2 * k / 2, h; -h * k * (1 - h ^ 2 * k / 4), 1 - h ^ 2 * k / 2]

/-- B.1: Φ_h for V = ½kq² acts by S. -/
theorem sv_lin_eq_S (h k : ℝ) (y : ℝ × ℝ) :
    sv (lin k) h y = ((S h k *ᵥ ![y.1, y.2]) 0, (S h k *ᵥ ![y.1, y.2]) 1) := by
  obtain ⟨q, p⟩ := y
  simp only [sv, lin, S, Prod.mk.injEq]
  simp [mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> ring

/-- det S = 1 (every h, k). -/
theorem det_S (h k : ℝ) : (S h k).det = 1 := by
  rw [S, det_fin_two_of]; ring

/-- Proposition B(i), d = 1: E_h ∘ Φ_h = E_h, for every real k (only symmetry of A is
used, as the dossier notes for the R-M4 use with k = m < 0) and every real h. -/
theorem Eh_sv (h k : ℝ) (y : ℝ × ℝ) : Eh h k (sv (lin k) h y) = Eh h k y := by
  obtain ⟨q, p⟩ := y
  simp only [Eh, sv, lin]
  ring

/-- Proposition B(i) in the dossier's ω-form: with V = ½ω²q²,
E_h = ½p² + ½(ω² − h²ω⁴/4)q² is invariant. -/
theorem Eh_sv_omega (h ω q p : ℝ) :
    let y' := sv (fun x => ω ^ 2 * x) h (q, p)
    y'.2 ^ 2 / 2 + (ω ^ 2 - h ^ 2 * ω ^ 4 / 4) * y'.1 ^ 2 / 2
      = p ^ 2 / 2 + (ω ^ 2 - h ^ 2 * ω ^ 4 / 4) * q ^ 2 / 2 := by
  simp only [sv]
  ring

/-- E_h is conserved along the whole ℤ-orbit. -/
theorem Eh_orbit (h k : ℝ) (y : ℝ × ℝ) (n : ℤ) : Eh h k (orbit (lin k) h y n) = Eh h k y := by
  refine zIter_invariant (Eh h k) (Eh_sv h k) (fun z => ?_) y n
  have := Eh_sv (-h) k z
  simpa [Eh] using this

/-- Proposition B(ii), d = 1: (1 − r)H ≤ E_h ≤ H with r = h²k/4, for k ≥ 0. -/
theorem sandwich_pointwise {h k : ℝ} (hk : 0 ≤ k) (y : ℝ × ℝ) :
    (1 - h ^ 2 * k / 4) * Hk k y ≤ Eh h k y ∧ Eh h k y ≤ Hk k y := by
  obtain ⟨q, p⟩ := y
  simp only [Eh, Hk]
  constructor
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) hk) (sq_nonneg p)]
  · nlinarith [mul_nonneg (mul_nonneg (sq_nonneg h) (mul_nonneg hk hk)) (sq_nonneg q)]

/-- The constant: with r = (hω)²/4, γ := r/(1 − r) = (hω)²/(4 − (hω)²). -/
theorem gamma_eq {h ω : ℝ} (hr : (h * ω) ^ 2 < 4) :
    ((h * ω) ^ 2 / 4) / (1 - (h * ω) ^ 2 / 4) = (h * ω) ^ 2 / (4 - (h * ω) ^ 2) := by
  have : (4 : ℝ) - (h * ω) ^ 2 ≠ 0 := by linarith
  field_simp

/-- **Proposition B(iii), d = 1.** V = ½ω²q², (hω)² < 4 (i.e. |hω| < 2), r = (hω)²/4:
for every y₀ and every n ∈ ℤ, (1 − r)H₀ ≤ H_n ≤ H₀/(1 − r); hence
H_n − H₀ ≤ γH₀ and H₀ − H_n ≤ rH₀ ≤ γH₀ with γ = (hω)²/(4 − (hω)²). -/
theorem propB_iii {h ω : ℝ} (hr : (h * ω) ^ 2 < 4) (y : ℝ × ℝ) (n : ℤ) :
    let r := (h * ω) ^ 2 / 4
    let γ := (h * ω) ^ 2 / (4 - (h * ω) ^ 2)
    let Hn := Hk (ω ^ 2) (orbit (lin (ω ^ 2)) h y n)
    (1 - r) * Hk (ω ^ 2) y ≤ Hn ∧ Hn ≤ Hk (ω ^ 2) y / (1 - r) ∧
    Hn - Hk (ω ^ 2) y ≤ γ * Hk (ω ^ 2) y ∧ Hk (ω ^ 2) y - Hn ≤ r * Hk (ω ^ 2) y ∧
    r * Hk (ω ^ 2) y ≤ γ * Hk (ω ^ 2) y := by
  intro r γ Hn
  have hk : (0 : ℝ) ≤ ω ^ 2 := sq_nonneg ω
  have hrk : h ^ 2 * ω ^ 2 / 4 = r := by simp only [r]; ring
  have hr1 : 0 < 1 - r := by simp only [r]; linarith
  have hr0 : 0 ≤ r := by simp only [r]; positivity
  have h0 := sandwich_pointwise (h := h) hk y
  have hn := sandwich_pointwise (h := h) hk (orbit (lin (ω ^ 2)) h y n)
  rw [hrk] at h0 hn
  have hE := Eh_orbit h (ω ^ 2) y n
  have H0nn : 0 ≤ Hk (ω ^ 2) y := by
    simp only [Hk]; positivity
  have hγ : γ = r / (1 - r) := by simp only [γ, r]; rw [gamma_eq hr]
  have lo : (1 - r) * Hk (ω ^ 2) y ≤ Hn := by
    simp only [Hn]; linarith [h0.1, hn.2]
  have up : Hn ≤ Hk (ω ^ 2) y / (1 - r) := by
    rw [le_div_iff₀ hr1]
    simp only [Hn]; nlinarith [h0.2, hn.1]
  refine ⟨lo, up, ?_, ?_, ?_⟩
  · have : Hk (ω ^ 2) y / (1 - r) = Hk (ω ^ 2) y + γ * Hk (ω ^ 2) y := by
      rw [hγ]; field_simp; ring
    linarith
  · linarith
  · rw [hγ]
    have h1 : r ≤ r / (1 - r) := by rw [le_div_iff₀ hr1]; nlinarith
    exact mul_le_mul_of_nonneg_right h1 H0nn

/-- B(iv), one attained instance (θ = π/2, m = 1, (hω)² = 2, r = 1/2): from (0, p₀) one step
gives H₁ = H₀/(1 − r) = 2H₀, and from (q₀, 0) one step gives H₁ = (1 − r)H₀ = H₀/2. -/
theorem sharp_instance {h ω : ℝ} (hk : (h * ω) ^ 2 = 2) (q p : ℝ) :
    Hk (ω ^ 2) (sv (lin (ω ^ 2)) h (0, p)) = Hk (ω ^ 2) (0, p) / (1 - (h * ω) ^ 2 / 4) ∧
    Hk (ω ^ 2) (sv (lin (ω ^ 2)) h (q, 0)) = (1 - (h * ω) ^ 2 / 4) * Hk (ω ^ 2) (q, 0) := by
  simp only [Hk, sv, lin]
  rw [hk]
  have hk' : h ^ 2 * ω ^ 2 = 2 := by rw [← hk]; ring
  constructor
  · linear_combination (p ^ 2 * (h ^ 2 * ω ^ 2 + 2) / 8) * hk'
  · linear_combination (ω ^ 2 * q ^ 2 * ((h ^ 2 * ω ^ 2) ^ 2 / 32 - h ^ 2 * ω ^ 2 / 16 - 1 / 8)) * hk'

/-! ### The edge hω = 2: quadratic growth -/

/-- B.7: at h²k = 4, S = [[−1, h], [0, −1]] and Sⁿ = (−1)ⁿ[[1, −nh], [0, 1]]. -/
theorem S_pow_edge {h k : ℝ} (hk : h ^ 2 * k = 4) (n : ℕ) :
    S h k ^ n = (-1 : ℝ) ^ n • !![1, -(n : ℝ) * h; 0, 1] := by
  have hS : S h k = !![-1, h; 0, -1] := by
    rw [S]
    have e1 : 1 - h ^ 2 * k / 2 = -1 := by linarith
    have e2 : -h * k * (1 - h ^ 2 * k / 4) = 0 := by rw [hk]; ring
    rw [e1, e2]
  induction n with
  | zero => simp [Matrix.one_fin_two]
  | succ n ih =>
    rw [pow_succ, ih, hS]
    ext i j
    fin_cases i <;> fin_cases j <;>
      (simp [Matrix.mul_apply, Fin.sum_univ_two, pow_succ]; try ring)

/-- B.7: the iterates at h²k = 4: q_n = (−1)ⁿ(q₀ − nhp₀), p_n = (−1)ⁿp₀. -/
theorem iterate_edge {h k : ℝ} (hk : h ^ 2 * k = 4) (q p : ℝ) (n : ℕ) :
    (sv (lin k) h)^[n] (q, p) = ((-1) ^ n * (q - n * h * p), (-1) ^ n * p) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [sv, lin, Prod.mk.injEq]
    push_cast
    constructor
    · linear_combination (-(-(1:ℝ)) ^ n * (q - n * h * p) / 2) * hk
    · linear_combination (-(-(1:ℝ)) ^ n * (p - h * k * (q - n * h * p) / 2) / 2) * hk

/-- B.7: at (hω)² = 4, H_n = ½p₀² + ½ω²(q₀ − nhp₀)². -/
theorem H_edge {h ω : ℝ} (hk : h ^ 2 * ω ^ 2 = 4) (q p : ℝ) (n : ℕ) :
    Hk (ω ^ 2) ((sv (lin (ω ^ 2)) h)^[n] (q, p)) = p ^ 2 / 2 + ω ^ 2 * (q - n * h * p) ^ 2 / 2 := by
  rw [iterate_edge hk]
  simp only [Hk]
  have : ((-1 : ℝ) ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  linear_combination (p ^ 2 / 2 + ω ^ 2 * (q - n * h * p) ^ 2 / 2) * this

/-- **Proposition B(v), edge case, d = 1.** At (hω)² = 4 the energy grows (quadratically,
by `H_edge`) without bound for every initial point with p₀ ≠ 0. -/
theorem edge_unbounded {h ω : ℝ} (hk : h ^ 2 * ω ^ 2 = 4) (q p : ℝ) (hp : p ≠ 0) :
    Tendsto (fun n : ℕ => Hk (ω ^ 2) ((sv (lin (ω ^ 2)) h)^[n] (q, p))) atTop atTop := by
  have hh : h ≠ 0 := by rintro rfl; norm_num at hk
  have hω : 0 < ω ^ 2 := by
    rcases (sq_nonneg ω).lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at hk; norm_num at hk
  set c := h * p with hc
  have hc0 : 0 < c ^ 2 := by positivity
  have lin_t : Tendsto (fun n : ℕ => ω ^ 2 * c ^ 2 / 4 * (n : ℝ) + (-(ω ^ 2 * q ^ 2 / 2)))
      atTop atTop :=
    tendsto_atTop_add_const_right _ _
      (Tendsto.const_mul_atTop (by positivity) tendsto_natCast_atTop_atTop)
  refine tendsto_atTop_mono (fun n => ?_) lin_t
  rw [H_edge hk]
  have hn : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · simp [h0]
    · have : (1 : ℝ) ≤ n := by exact_mod_cast h0
      nlinarith
  have key : c ^ 2 * (n : ℝ) ^ 2 / 2 - q ^ 2 ≤ (q - n * h * p) ^ 2 := by
    have : (q - n * h * p) = q - n * c := by rw [hc]; ring
    rw [this]; nlinarith [sq_nonneg ((n : ℝ) * c - 2 * q)]
  nlinarith [mul_le_mul_of_nonneg_left key hω.le, mul_le_mul_of_nonneg_left hn
    (by positivity : (0 : ℝ) ≤ ω ^ 2 * c ^ 2 / 4), sq_nonneg p]

/-- B.7: at (hω)² = 4 with p₀ = 0 the orbit has period 2 and H is constant. -/
theorem edge_p_zero {h ω : ℝ} (hk : h ^ 2 * ω ^ 2 = 4) (q : ℝ) (n : ℕ) :
    Hk (ω ^ 2) ((sv (lin (ω ^ 2)) h)^[n] (q, 0)) = Hk (ω ^ 2) (q, 0) := by
  rw [H_edge hk]; simp [Hk]

/-! ## Proposition A (general d) and Proposition B / Corollary B′ (general d, general mass) -/

section GeneralD

variable {d : ℕ}

local notation "Vec" => (Fin d → ℝ)

/-- Störmer–Verlet step in ℝᵈ with force F = ∇V and inverse mass N = M_p⁻¹:
p½ = p − (h/2)F(q), q' = q + hN p½, p' = p½ − (h/2)F(q'). -/
def svD (F : Vec → Vec) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) (y : Vec × Vec) : Vec × Vec :=
  (y.1 + h • (N *ᵥ (y.2 - (h / 2) • F y.1)),
   (y.2 - (h / 2) • F y.1) - (h / 2) • F (y.1 + h • (N *ᵥ (y.2 - (h / 2) • F y.1))))

/-- **Proposition A(ii), general d**, every force F, every N, every step h: Φ_{−h} ∘ Φ_h = id. -/
theorem svD_neg_svD (F : Vec → Vec) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) (y : Vec × Vec) :
    svD F N (-h) (svD F N h y) = y := by
  obtain ⟨q, p⟩ := y
  set u := p - (h / 2) • F q with hu
  set q' := q + h • (N *ᵥ u) with hq'
  have hu' : (u - (h / 2) • F q') - (-h / 2) • F q' = u := by
    rw [neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]
  have hq'' : q' + (-h) • (N *ᵥ u) = q := by
    rw [hq', neg_smul, add_neg_cancel_right]
  simp only [svD, ← hu, ← hq', hu', hq'']
  ext1
  · rfl
  · simp only [hu, neg_div, neg_smul, sub_neg_eq_add, sub_add_cancel]

theorem svD_svD_neg (F : Vec → Vec) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) (y : Vec × Vec) :
    svD F N h (svD F N (-h) y) = y := by
  simpa using svD_neg_svD F N (-h) y

/-- Momentum flip in ℝᵈ. -/
def flipD (y : Vec × Vec) : Vec × Vec := (y.1, -y.2)

/-- **Proposition A(iii), general d**, every force, every N, every step: ρ Φ_h ρ = Φ_{−h}. -/
theorem flipD_svD_flipD (F : Vec → Vec) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) (y : Vec × Vec) :
    flipD (svD F N h (flipD y)) = svD F N (-h) y := by
  obtain ⟨q, p⟩ := y
  have e : -p - (h / 2) • F q = -(p - (-h / 2) • F q) := by module
  have hx : q + h • (N *ᵥ (-p - (h / 2) • F q)) = q + (-h) • (N *ᵥ (p - (-h / 2) • F q)) := by
    rw [e, mulVec_neg, smul_neg, neg_smul]
  simp only [flipD, svD, hx, Prod.mk.injEq, true_and]
  module

/-- The ℤ-orbit in ℝᵈ. -/
def orbitD (F : Vec → Vec) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) (y : Vec × Vec) (n : ℤ) :
    Vec × Vec := zIter (svD F N h) (svD F N (-h)) y n

theorem orbitD_succ (F : Vec → Vec) (N : Matrix (Fin d) (Fin d) ℝ) (h : ℝ) (y : Vec × Vec)
    (n : ℤ) : orbitD F N h y (n + 1) = svD F N h (orbitD F N h y n) :=
  zIter_succ (svD_svD_neg F N h) y n

/-- True energy H = ½pᵀNp + ½qᵀAq (N = M_p⁻¹). -/
def HD (A N : Matrix (Fin d) (Fin d) ℝ) (y : Vec × Vec) : ℝ :=
  y.2 ⬝ᵥ (N *ᵥ y.2) / 2 + y.1 ⬝ᵥ (A *ᵥ y.1) / 2

/-- Modified energy E_h = ½pᵀNp + ½qᵀ(A − (h²/4)ANA)q (B.9 with N = M_p⁻¹; for N = I this
is ½|p|² + ½qᵀA(I − (h²/4)A)q). -/
def EhD (h : ℝ) (A N : Matrix (Fin d) (Fin d) ℝ) (y : Vec × Vec) : ℝ :=
  y.2 ⬝ᵥ (N *ᵥ y.2) / 2 + y.1 ⬝ᵥ ((A - (h ^ 2 / 4) • (A * N * A)) *ᵥ y.1) / 2

theorem dot_mulVec_symm {S : Matrix (Fin d) (Fin d) ℝ} (hS : Sᵀ = S) (x y : Vec) :
    x ⬝ᵥ (S *ᵥ y) = (S *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec]
  conv_lhs => rw [← hS, vecMul_transpose]

/-- E_h in the half-step variable: E_h(x, u + cAx) = ½uᵀNu + c(Ax)ᵀNu + ½xᵀAx when c² = h²/4. -/
theorem EhD_shift {A N : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (hN : Nᵀ = N)
    {h c : ℝ} (hc : c ^ 2 = h ^ 2 / 4) (x u : Vec) :
    EhD h A N (x, u + c • (A *ᵥ x)) =
      u ⬝ᵥ (N *ᵥ u) / 2 + c * ((A *ᵥ x) ⬝ᵥ (N *ᵥ u)) + x ⬝ᵥ (A *ᵥ x) / 2 := by
  simp only [EhD, sub_mulVec, smul_mulVec, ← mulVec_mulVec, mulVec_add, mulVec_smul,
    dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, dotProduct_sub,
    smul_eq_mul]
  have s1 : u ⬝ᵥ (N *ᵥ (A *ᵥ x)) = (A *ᵥ x) ⬝ᵥ (N *ᵥ u) := by
    rw [dot_mulVec_symm hN, dotProduct_comm]
  have s2 : x ⬝ᵥ (A *ᵥ (N *ᵥ (A *ᵥ x))) = (A *ᵥ x) ⬝ᵥ (N *ᵥ (A *ᵥ x)) := by
    rw [dot_mulVec_symm hA]
  rw [s1, s2]
  linear_combination ((1 : ℝ) / 2) * ((A *ᵥ x) ⬝ᵥ (N *ᵥ (A *ᵥ x))) * hc

/-- **Proposition B(i) / Corollary B′, general d, general mass.** For symmetric A and
symmetric N (in particular N = M_p⁻¹ with M_p ≻ 0), every real h:
E_h ∘ Φ_h = E_h, with Φ_h the Störmer–Verlet map for V = ½qᵀAq. -/
theorem EhD_svD {A N : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (hN : Nᵀ = N) (h : ℝ)
    (y : Vec × Vec) : EhD h A N (svD (fun x => A *ᵥ x) N h y) = EhD h A N y := by
  obtain ⟨q, p⟩ := y
  set u := p - (h / 2) • (A *ᵥ q) with hu
  set q' := q + h • (N *ᵥ u) with hq'
  have hc1 : (h / 2) ^ 2 = h ^ 2 / 4 := by ring
  have hc2 : (-(h / 2)) ^ 2 = h ^ 2 / 4 := by ring
  have e1 : (q, p) = (q, u + (h / 2) • (A *ᵥ q)) := by rw [hu, sub_add_cancel]
  have e2 : svD (fun x => A *ᵥ x) N h (q, p) = (q', u + (-(h / 2)) • (A *ᵥ q')) := by
    simp only [svD, ← hu, ← hq', neg_smul, ← sub_eq_add_neg]
  rw [e2, EhD_shift hA hN hc2, e1, EhD_shift hA hN hc1]
  simp only [hq', mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, dotProduct_add,
    dotProduct_smul, smul_eq_mul]
  have s1 : q ⬝ᵥ (A *ᵥ (N *ᵥ u)) = (A *ᵥ q) ⬝ᵥ (N *ᵥ u) := dot_mulVec_symm hA _ _
  have s2 : (N *ᵥ u) ⬝ᵥ (A *ᵥ q) = (A *ᵥ q) ⬝ᵥ (N *ᵥ u) := dotProduct_comm _ _
  have s3 : (A *ᵥ (N *ᵥ u)) ⬝ᵥ (N *ᵥ u) = (N *ᵥ u) ⬝ᵥ (A *ᵥ (N *ᵥ u)) := dotProduct_comm _ _
  rw [s1, s2, s3]
  ring

/-- E_h is conserved along the ℤ-orbit (general d, general mass). -/
theorem EhD_orbitD {A N : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (hN : Nᵀ = N) (h : ℝ)
    (y : Vec × Vec) (n : ℤ) :
    EhD h A N (orbitD (fun x => A *ᵥ x) N h y n) = EhD h A N y := by
  refine zIter_invariant (EhD h A N) (EhD_svD hA hN h) (fun z => ?_) y n
  have := EhD_svD hA hN (-h) z
  simpa [EhD] using this

/-- Cauchy–Schwarz for a positive semidefinite symmetric form. -/
theorem cs_psd {A : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (hA0 : ∀ x : Vec, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (x y : Vec) : (x ⬝ᵥ (A *ᵥ y)) ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (y ⬝ᵥ (A *ᵥ y)) := by
  have hq : ∀ t : ℝ, 0 ≤ (y ⬝ᵥ (A *ᵥ y)) * (t * t) + (2 * (x ⬝ᵥ (A *ᵥ y))) * t +
      x ⬝ᵥ (A *ᵥ x) := by
    intro t
    have := hA0 (x + t • y)
    have s : y ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ y) := by
      rw [dot_mulVec_symm hA, dotProduct_comm]
    simp only [mulVec_add, mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
      smul_dotProduct, smul_eq_mul, s] at this
    linarith
  have := discrim_le_zero hq
  unfold discrim at this
  nlinarith

/-- The general-mass bridge: A ⪰ 0 and A ⪯ ω²M_p (i.e. ω² ≥ λ_max(M_p⁻¹A), the generalised
Rayleigh quotient bound) imply AM_p⁻¹A ⪯ ω²A. -/
theorem ANA_le {A M : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A) (hA0 : ∀ x : Vec, 0 ≤ x ⬝ᵥ (A *ᵥ x))
    (hM : M.PosDef) {ω : ℝ} (hω : ∀ x : Vec, x ⬝ᵥ (A *ᵥ x) ≤ ω ^ 2 * (x ⬝ᵥ (M *ᵥ x))) (x : Vec) :
    (A *ᵥ x) ⬝ᵥ (M⁻¹ *ᵥ (A *ᵥ x)) ≤ ω ^ 2 * (x ⬝ᵥ (A *ᵥ x)) := by
  have hMs : Mᵀ = M := by
    have := hM.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hdet : IsUnit M.det := (isUnit_iff_isUnit_det M).mp hM.isUnit
  set y := M⁻¹ *ᵥ (A *ᵥ x) with hy
  have hMy : M *ᵥ y = A *ᵥ x := by rw [hy, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec]
  set s := (A *ᵥ x) ⬝ᵥ y with hs
  have s_eq1 : s = x ⬝ᵥ (A *ᵥ y) := by rw [hs, dot_mulVec_symm hA]
  have s_eq2 : s = y ⬝ᵥ (M *ᵥ y) := by rw [hs, ← hMy, dotProduct_comm]
  have s_nn : 0 ≤ s := by
    rw [s_eq2]; simpa [star_trivial] using hM.posSemidef.dotProduct_mulVec_nonneg y
  have hcs := cs_psd hA hA0 x y
  rw [← s_eq1] at hcs
  have hyy : y ⬝ᵥ (A *ᵥ y) ≤ ω ^ 2 * s := by rw [s_eq2]; exact hω y
  have hxx := hA0 x
  rcases s_nn.lt_or_eq with hpos | hzero
  · have : s ^ 2 ≤ (x ⬝ᵥ (A *ᵥ x)) * (ω ^ 2 * s) :=
      hcs.trans (mul_le_mul_of_nonneg_left hyy hxx)
    nlinarith
  · rw [← hzero]; positivity

/-- **Proposition B(ii), general d, general mass:** (1 − r)H ≤ E_h ≤ H, r = (hω)²/4. -/
theorem sandwichD {A M : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A)
    (hA0 : ∀ x : Vec, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (hM : M.PosDef) {ω : ℝ}
    (hω : ∀ x : Vec, x ⬝ᵥ (A *ᵥ x) ≤ ω ^ 2 * (x ⬝ᵥ (M *ᵥ x))) (h : ℝ) (y : Vec × Vec) :
    (1 - (h * ω) ^ 2 / 4) * HD A M⁻¹ y ≤ EhD h A M⁻¹ y ∧ EhD h A M⁻¹ y ≤ HD A M⁻¹ y := by
  obtain ⟨q, p⟩ := y
  have hb := ANA_le hA hA0 hM hω q
  have hN := hM.inv
  have hp : 0 ≤ p ⬝ᵥ (M⁻¹ *ᵥ p) := by
    simpa [star_trivial] using hN.posSemidef.dotProduct_mulVec_nonneg p
  have hAq : 0 ≤ (A *ᵥ q) ⬝ᵥ (M⁻¹ *ᵥ (A *ᵥ q)) := by
    simpa [star_trivial] using hN.posSemidef.dotProduct_mulVec_nonneg (A *ᵥ q)
  have e : q ⬝ᵥ ((A - (h ^ 2 / 4) • (A * M⁻¹ * A)) *ᵥ q) =
      q ⬝ᵥ (A *ᵥ q) - h ^ 2 / 4 * ((A *ᵥ q) ⬝ᵥ (M⁻¹ *ᵥ (A *ᵥ q))) := by
    rw [sub_mulVec, smul_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_sub,
      dotProduct_smul, dot_mulVec_symm hA q (M⁻¹ *ᵥ (A *ᵥ q)), smul_eq_mul]
  simp only [EhD, HD, e]
  have hq0 := hA0 q
  constructor
  · nlinarith [mul_nonneg (sq_nonneg h) hp, mul_le_mul_of_nonneg_left hb (sq_nonneg h)]
  · nlinarith [mul_nonneg (sq_nonneg h) hAq]

/-- **Proposition B(iii) / Corollary B′, general d, general mass.** V = ½qᵀAq with A
symmetric, A ⪰ 0; M_p ≻ 0; ω with A ⪯ ω²M_p (equivalently ω² ≥ λ_max(M_p⁻¹A)); (hω)² < 4.
For every y₀ and n ∈ ℤ, with H = ½pᵀM_p⁻¹p + ½qᵀAq, r = (hω)²/4, γ = (hω)²/(4 − (hω)²):
(1 − r)H₀ ≤ H_n ≤ H₀/(1 − r), H_n − H₀ ≤ γH₀, H₀ − H_n ≤ rH₀ ≤ γH₀. -/
theorem propBprime_iii {A M : Matrix (Fin d) (Fin d) ℝ} (hA : Aᵀ = A)
    (hA0 : ∀ x : Vec, 0 ≤ x ⬝ᵥ (A *ᵥ x)) (hM : M.PosDef) {h ω : ℝ}
    (hω : ∀ x : Vec, x ⬝ᵥ (A *ᵥ x) ≤ ω ^ 2 * (x ⬝ᵥ (M *ᵥ x))) (hr : (h * ω) ^ 2 < 4)
    (y : Vec × Vec) (n : ℤ) :
    let r := (h * ω) ^ 2 / 4
    let γ := (h * ω) ^ 2 / (4 - (h * ω) ^ 2)
    let H0 := HD A M⁻¹ y
    let Hn := HD A M⁻¹ (orbitD (fun x => A *ᵥ x) M⁻¹ h y n)
    (1 - r) * H0 ≤ Hn ∧ Hn ≤ H0 / (1 - r) ∧ Hn - H0 ≤ γ * H0 ∧ H0 - Hn ≤ r * H0 ∧
    r * H0 ≤ γ * H0 := by
  intro r γ H0 Hn
  have hNs : (M⁻¹)ᵀ = M⁻¹ := by
    have := hM.inv.isHermitian.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hr1 : 0 < 1 - r := by simp only [r]; linarith
  have hr0 : 0 ≤ r := by simp only [r]; positivity
  have h0 := sandwichD hA hA0 hM hω h y
  have hn := sandwichD hA hA0 hM hω h (orbitD (fun x => A *ᵥ x) M⁻¹ h y n)
  have hr' : (h * ω) ^ 2 / 4 = r := rfl
  rw [hr'] at h0 hn
  have hE := EhD_orbitD hA hNs h y n
  have H0nn : 0 ≤ H0 := by
    simp only [H0, HD]
    have := hA0 y.1
    have := hM.inv.posSemidef.dotProduct_mulVec_nonneg y.2
    simp only [star_trivial] at this
    positivity
  have hγ : γ = r / (1 - r) := by simp only [γ, r]; rw [gamma_eq hr]
  have lo : (1 - r) * H0 ≤ Hn := by
    simp only [Hn, H0]; linarith [h0.1, hn.2]
  have up : Hn ≤ H0 / (1 - r) := by
    rw [le_div_iff₀ hr1]
    simp only [Hn, H0]; nlinarith [h0.2, hn.1]
  refine ⟨lo, up, ?_, ?_, ?_⟩
  · have : H0 / (1 - r) = H0 + γ * H0 := by
      rw [hγ]; field_simp; ring
    linarith
  · linarith
  · rw [hγ]
    have h1 : r ≤ r / (1 - r) := by rw [le_div_iff₀ hr1]; nlinarith
    exact mul_le_mul_of_nonneg_right h1 H0nn

/-- Spectral reading for M_p = I: x ⬝ Ax = Σⱼ λⱼ (bⱼ ⬝ x)² and x ⬝ x = Σⱼ (bⱼ ⬝ x)². -/
theorem quad_eig {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) (x : Vec) :
    x ⬝ᵥ (A *ᵥ x) = ∑ j, hA.eigenvalues j * ((hA.eigenvectorBasis j).ofLp ⬝ᵥ x) ^ 2 ∧
    x ⬝ᵥ x = ∑ j, ((hA.eigenvectorBasis j).ofLp ⬝ᵥ x) ^ 2 := by
  set b := hA.eigenvectorBasis
  have hsym : Aᵀ = A := by
    have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have inner_toLp : ∀ u v : Vec,
      inner ℝ (WithLp.toLp 2 u : EuclideanSpace ℝ (Fin d)) (WithLp.toLp 2 v) = u ⬝ᵥ v := by
    intro u v
    rw [EuclideanSpace.inner_eq_star_dotProduct, star_trivial, dotProduct_comm]
  have hc : ∀ j, (b j).ofLp ⬝ᵥ (A *ᵥ x) = hA.eigenvalues j * ((b j).ofLp ⬝ᵥ x) := by
    intro j
    rw [dot_mulVec_symm hsym, hA.mulVec_eigenvectorBasis, smul_dotProduct, smul_eq_mul]
  constructor
  · have hp := b.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 (A *ᵥ x))
    rw [inner_toLp] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (b j) = (b j).ofLp ⬝ᵥ x := by
      rw [real_inner_comm, ← inner_toLp]
    have e2 : inner ℝ (b j) (WithLp.toLp 2 (A *ᵥ x) : EuclideanSpace ℝ (Fin d)) =
        (b j).ofLp ⬝ᵥ (A *ᵥ x) := by rw [← inner_toLp]
    rw [e1, e2, hc]; ring
  · have hp := b.sum_inner_mul_inner (WithLp.toLp 2 x) (WithLp.toLp 2 x)
    rw [inner_toLp] at hp
    rw [← hp]
    refine Finset.sum_congr rfl fun j _ => ?_
    have e1 : inner ℝ (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) (b j) = (b j).ofLp ⬝ᵥ x := by
      rw [real_inner_comm, ← inner_toLp]
    have e2 : inner ℝ (b j) (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin d)) = (b j).ofLp ⬝ᵥ x := by
      rw [← inner_toLp]
    rw [e1, e2]; ring

/-- **Proposition B(iii), general d, M_p = I, in the dossier's hypotheses:** A symmetric with
every eigenvalue in [0, ω²] (A ⪰ 0 and ω ≥ ω_max := λ_max(A)^{1/2}), (hω)² < 4. With
E_h = ½|p|² + ½qᵀA(I − (h²/4)A)q conserved (`EhD_orbitD`), and H = ½|p|² + ½qᵀAq:
the sandwich and the error bounds hold for every n ∈ ℤ. -/
theorem propB_iii_eig {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.IsHermitian) {h ω : ℝ}
    (heig : ∀ j, 0 ≤ hA.eigenvalues j ∧ hA.eigenvalues j ≤ ω ^ 2) (hr : (h * ω) ^ 2 < 4)
    (y : Vec × Vec) (n : ℤ) :
    let r := (h * ω) ^ 2 / 4
    let γ := (h * ω) ^ 2 / (4 - (h * ω) ^ 2)
    let H0 := HD A 1 y
    let Hn := HD A 1 (orbitD (fun x => A *ᵥ x) 1 h y n)
    (1 - r) * H0 ≤ Hn ∧ Hn ≤ H0 / (1 - r) ∧ Hn - H0 ≤ γ * H0 ∧ H0 - Hn ≤ r * H0 ∧
    r * H0 ≤ γ * H0 := by
  have hsym : Aᵀ = A := by
    have := hA.eq; rwa [conjTranspose_eq_transpose_of_trivial] at this
  have hA0 : ∀ x : Vec, 0 ≤ x ⬝ᵥ (A *ᵥ x) := by
    intro x; rw [(quad_eig hA x).1]
    exact Finset.sum_nonneg fun j _ => mul_nonneg (heig j).1 (sq_nonneg _)
  have hω : ∀ x : Vec, x ⬝ᵥ (A *ᵥ x) ≤ ω ^ 2 * (x ⬝ᵥ ((1 : Matrix (Fin d) (Fin d) ℝ) *ᵥ x)) := by
    intro x
    rw [one_mulVec, (quad_eig hA x).1, (quad_eig hA x).2, Finset.mul_sum]
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (heig j).2 (sq_nonneg _)
  have := propBprime_iii hsym hA0 Matrix.PosDef.one hω hr y n
  simpa only [inv_one] using this

/-- B(i) for M_p = I in the dossier's form E_h = ½|p|² + ½qᵀA(I − (h²/4)A)q. -/
theorem EhD_one_eq (h : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (y : Vec × Vec) :
    EhD h A 1 y = y.2 ⬝ᵥ y.2 / 2 + y.1 ⬝ᵥ ((A * (1 - (h ^ 2 / 4) • A)) *ᵥ y.1) / 2 := by
  simp only [EhD, one_mulVec, mul_one, Matrix.mul_sub, Matrix.mul_smul]

end GeneralD

/-! ## Proposition C: the piecewise-linear model (C.1, C.2, C.3) -/

/-- The kick K_s(q, p) = (q, p − s f(q)). -/
def kick (f : ℝ → ℝ) (s : ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (y.1, y.2 - s * f y.1)

/-- C.2: the kick-then-drift map G = D₁ ∘ K₁, G(q, p) = (q + p − f(q), p − f(q)). -/
def Gmap (f : ℝ → ℝ) (y : ℝ × ℝ) : ℝ × ℝ := (y.1 + y.2 - f y.1, y.2 - f y.1)

/-- C.2: Φ₁ ∘ K_{1/2} = K_{1/2} ∘ G, for every force. -/
theorem sv_kick (f : ℝ → ℝ) (z : ℝ × ℝ) : sv f 1 (kick f (1 / 2) z) = kick f (1 / 2) (Gmap f z) := by
  obtain ⟨q, p⟩ := z
  simp only [sv, kick, Gmap, Prod.mk.injEq]
  constructor
  · ring
  · ring_nf

/-- C.2: Φ₁ⁿ ∘ K_{1/2} = K_{1/2} ∘ Gⁿ; in particular the q-coordinates agree. -/
theorem sv_iterate_kick (f : ℝ → ℝ) (z : ℝ × ℝ) (n : ℕ) :
    (sv f 1)^[n] (kick f (1 / 2) z) = kick f (1 / 2) ((Gmap f)^[n] z) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, sv_kick, Function.iterate_succ_apply']

/-- C.1: scaling to h = 1. With V = W/h² (force f/h²) and p̃ = hp, one step for (V, h) is one
step for (W, 1). -/
theorem sv_scale (f : ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (q p : ℝ) :
    sv (fun x => f x / h ^ 2) h (q, p) = ((sv f 1 (q, h * p)).1, (sv f 1 (q, h * p)).2 / h) := by
  simp only [sv, Prod.mk.injEq]
  constructor <;> field_simp

theorem sv_scale_iterate (f : ℝ → ℝ) {h : ℝ} (hh : h ≠ 0) (q p : ℝ) (n : ℕ) :
    (sv (fun x => f x / h ^ 2) h)^[n] (q, p) =
      (((sv f 1)^[n] (q, h * p)).1, ((sv f 1)^[n] (q, h * p)).2 / h) := by
  induction n with
  | zero => simp [hh]
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, sv_scale f hh, Function.iterate_succ_apply']
    congr 3 <;> field_simp

/-- The two-slope force F(q) = aq (q ≥ 0), bq (q < 0); the derivative of the C¹ potential
½aq² (q ≥ 0), ½bq² (q < 0). -/
def pw (a b : ℝ) (q : ℝ) : ℝ := if 0 ≤ q then a * q else b * q

/-- C.3: G_k = [[1 − k, 1], [−k, 1]]. -/
def Gk (k : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![1 - k, 1; -k, 1]

theorem Gmap_lin (k : ℝ) (y : ℝ × ℝ) :
    Gmap (lin k) y = ((Gk k *ᵥ ![y.1, y.2]) 0, (Gk k *ᵥ ![y.1, y.2]) 1) := by
  simp [Gmap, lin, Gk, mulVec, dotProduct, Fin.sum_univ_two]
  constructor <;> ring

theorem det_Gk (k : ℝ) : (Gk k).det = 1 := by rw [Gk, det_fin_two_of]; ring

/-- C.2′: LR's linear branch T_f = [[f, −1], [1, 0]] and C_LR = [[1, 0], [1, −1]]. -/
def Tlr (f : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := !![f, -1; 1, 0]

def CLR : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 1, -1]

/-- C.2′ (observation): G_k C_LR = C_LR T_{2−k}, identically in k; det C_LR = −1. -/
theorem conj_LR (k : ℝ) : Gk k * CLR = CLR * Tlr (2 - k) ∧ CLR.det = -1 := by
  constructor
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Gk, CLR, Tlr, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  · simp [CLR, det_fin_two_of]

/-- C.3: G_b G_a. -/
theorem GbGa (δ : ℝ) :
    Gk (3 + δ) * Gk (3 - δ) = !![1 + δ - δ ^ 2, -1 - δ; 3 - δ ^ 2, -2 - δ] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gk, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

/-- C.3: P = G_a G_b G_a, a = 3 − δ, b = 3 + δ. -/
def Pmat (δ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ := Gk (3 - δ) * Gk (3 + δ) * Gk (3 - δ)

theorem Pmat_eq (δ : ℝ) :
    Pmat δ = !![1 - δ + 2 * δ ^ 2 - δ ^ 3, -δ ^ 2;
                -2 * δ + 3 * δ ^ 2 - δ ^ 3, 1 + δ - δ ^ 2] := by
  rw [Pmat, mul_assoc, GbGa]
  ext i j; fin_cases i <;> fin_cases j <;> simp [Gk, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem trace_Pmat (δ : ℝ) : (Pmat δ).trace = 2 + δ ^ 2 * (1 - δ) := by
  rw [Pmat_eq, trace_fin_two_of]; ring

theorem det_Pmat (δ : ℝ) : (Pmat δ).det = 1 := by
  rw [Pmat, det_mul, det_mul, det_Gk, det_Gk]; norm_num

theorem trace_Pmat_gt_two {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 2 < (Pmat δ).trace := by
  rw [trace_Pmat]; have : 0 < δ ^ 2 * (1 - δ) := by positivity
  linarith

/-- τ = δ²(1 − δ). -/
def tau (δ : ℝ) : ℝ := δ ^ 2 * (1 - δ)

/-- λ₊ = 1 + τ/2 + √(τ + τ²/4). -/
def lamP (δ : ℝ) : ℝ := 1 + tau δ / 2 + Real.sqrt (tau δ + tau δ ^ 2 / 4)

theorem tau_pos {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 0 < tau δ := by
  unfold tau; have : 0 < 1 - δ := by linarith
  positivity

/-- λ₊ is a root of the characteristic polynomial λ² − (tr P)λ + det P of P. -/
theorem lamP_charpoly {δ : ℝ} (h1 : δ ≤ 1) :
    lamP δ ^ 2 - (2 + tau δ) * lamP δ + 1 = 0 := by
  have h1' : 0 ≤ 1 - δ := by linarith
  have ht : 0 ≤ tau δ := by unfold tau; positivity
  have hs := Real.sq_sqrt (show 0 ≤ tau δ + tau δ ^ 2 / 4 by positivity)
  unfold lamP
  linear_combination hs

theorem lamP_gt_one {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 1 < lamP δ := by
  unfold lamP
  have := tau_pos h0 h1
  have := Real.sqrt_nonneg (tau δ + tau δ ^ 2 / 4)
  linarith

/-- P₁₁ = 1 − δ + 2δ² − δ³. -/
def P11 (δ : ℝ) : ℝ := 1 - δ + 2 * δ ^ 2 - δ ^ 3

/-- The eigen-direction v = (δ², P₁₁ − λ₊). -/
def vP (δ : ℝ) : ℝ × ℝ := (δ ^ 2, P11 δ - lamP δ)

/-- C.3: v is a λ₊-eigenvector of P. -/
theorem Pmat_mulVec_v {δ : ℝ} (h1 : δ ≤ 1) :
    Pmat δ *ᵥ ![(vP δ).1, (vP δ).2] = lamP δ • ![(vP δ).1, (vP δ).2] := by
  have hc := lamP_charpoly h1
  rw [Pmat_eq]
  ext i; fin_cases i
  · simp [vP, P11, mulVec, dotProduct, Fin.sum_univ_two]; ring
  · simp [vP, P11, mulVec, dotProduct, Fin.sum_univ_two]
    unfold tau at hc
    linear_combination hc

theorem P11_bounds {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) : 0 < P11 δ ∧ P11 δ < 1 := by
  have e : P11 δ = 1 - δ * (1 - δ) ^ 2 := by unfold P11; ring
  have h1' : 0 < 1 - δ := by linarith
  have hp : 0 < δ * (1 - δ) ^ 2 := by positivity
  have hq : δ * (1 - δ) ^ 2 < 1 := by
    have : (1 - δ) ^ 2 < 1 := by nlinarith
    nlinarith
  constructor <;> linarith

/-- The two-slope map for C.3's slopes. -/
def Gpw (δ : ℝ) : ℝ × ℝ → ℝ × ℝ := Gmap (pw (3 - δ) (3 + δ))

/-- G is positively homogeneous. -/
theorem Gmap_pw_smul (a b : ℝ) {t : ℝ} (ht : 0 < t) (z : ℝ × ℝ) :
    Gmap (pw a b) (t • z) = t • Gmap (pw a b) z := by
  obtain ⟨q, p⟩ := z
  have hq : (0 ≤ t * q) ↔ (0 ≤ q) := by
    constructor
    · intro h; by_contra hc; push Not at hc; nlinarith
    · intro h; positivity
  simp only [Gmap, pw, Prod.smul_mk, smul_eq_mul, hq]
  split_ifs <;> simp only [Prod.mk.injEq] <;> constructor <;> ring

/-- **C.3, sign pattern (+, −, +)** for δ ∈ (0, 1): q₀ = δ² > 0, q₁ < 0, q₂ > 0, and
G³v = λ₊v. -/
theorem C3_signs {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) :
    0 < (vP δ).1 ∧ (Gpw δ (vP δ)).1 < 0 ∧ 0 < (Gpw δ (Gpw δ (vP δ))).1 ∧
    Gpw δ (Gpw δ (Gpw δ (vP δ))) = lamP δ • vP δ := by
  have hl := lamP_gt_one h0 h1
  have hP := P11_bounds h0 h1
  have hc := lamP_charpoly h1.le
  unfold tau at hc
  have q0 : 0 < (vP δ).1 := by simp [vP]; positivity
  have e1 : Gpw δ (vP δ) = (δ ^ 2 + (P11 δ - lamP δ) - (3 - δ) * δ ^ 2,
      (P11 δ - lamP δ) - (3 - δ) * δ ^ 2) := by
    simp [Gpw, Gmap, vP, pw, sq_nonneg]
  have q1 : (Gpw δ (vP δ)).1 < 0 := by
    rw [e1]; dsimp only; nlinarith
  set z1 := Gpw δ (vP δ) with hz1
  have e2 : Gpw δ z1 = (z1.1 + z1.2 - (3 + δ) * z1.1, z1.2 - (3 + δ) * z1.1) := by
    simp [Gpw, Gmap, pw, not_le.mpr q1]
  have q2 : 0 < (Gpw δ z1).1 := by
    rw [e2, e1]; dsimp only
    have : 0 < 1 + δ - δ ^ 2 := by nlinarith
    nlinarith
  refine ⟨q0, q1, q2, ?_⟩
  set z2 := Gpw δ z1 with hz2
  have e3 : Gpw δ z2 = (z2.1 + z2.2 - (3 - δ) * z2.1, z2.2 - (3 - δ) * z2.1) := by
    simp [Gpw, Gmap, pw, q2.le]
  rw [e3, e2, e1]
  simp only [vP, P11, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
  constructor
  · ring
  · linear_combination hc

/-- **C.3, the orbit.** For t > 0, Gpw^{3m+j}(tv) = (tλ₊^m)·Gpw^j(v), so the branch word
a, b, a repeats forever and the q-coordinates satisfy q_{3m+j} = λ₊^m q_j. -/
theorem C3_orbit {δ : ℝ} (h0 : 0 < δ) (h1 : δ < 1) {t : ℝ} (ht : 0 < t) (m j : ℕ) :
    (Gpw δ)^[3 * m + j] (t • vP δ) = (t * lamP δ ^ m) • (Gpw δ)^[j] (vP δ) := by
  have hl := lamP_gt_one h0 h1
  have hom : ∀ (s : ℝ), 0 < s → ∀ (n : ℕ) (z : ℝ × ℝ),
      (Gpw δ)^[n] (s • z) = s • (Gpw δ)^[n] z := by
    intro s hs n
    induction n with
    | zero => intro z; rfl
    | succ n ih =>
      intro z
      rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
      exact Gmap_pw_smul _ _ hs _
  have h3 : (Gpw δ)^[3] (vP δ) = lamP δ • vP δ := (C3_signs h0 h1).2.2.2
  have h3m : ∀ m : ℕ, (Gpw δ)^[3 * m] (vP δ) = lamP δ ^ m • vP δ := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.mul_succ, Function.iterate_add_apply, h3, hom _ (by linarith), ih, smul_smul,
        pow_succ, mul_comm]
  rw [Nat.add_comm, Function.iterate_add_apply, hom t ht, h3m, smul_smul,
    hom _ (by positivity)]

/-- The C¹ two-slope potential ½aq² (q ≥ 0), ½bq² (q < 0). -/
def Vpw (a b : ℝ) (q : ℝ) : ℝ := if 0 ≤ q then a * q ^ 2 / 2 else b * q ^ 2 / 2

/-- `pw a b` is the derivative of `Vpw a b` everywhere (including q = 0). -/
theorem hasDerivAt_Vpw (a b q : ℝ) : HasDerivAt (Vpw a b) (pw a b q) q := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · have hd : HasDerivAt (fun x : ℝ => b * x ^ 2 / 2) (b * q) q := by
      have := ((hasDerivAt_pow 2 q).const_mul b).div_const 2
      exact this.congr_deriv (by norm_num; ring)
    have hpw : pw a b q = b * q := by simp [pw, not_le.mpr hq]
    rw [hpw]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hq] with x hx
    simp [Vpw, not_le.mpr (show x < 0 from hx)]
  · rw [hasDerivAt_iff_isLittleO]
    have hb : (fun x : ℝ => Vpw a b x - Vpw a b 0 - (x - 0) • pw a b 0) =O[𝓝 0]
        (fun x : ℝ => x ^ 2) := by
      refine Asymptotics.IsBigO.of_bound (|a| / 2 + |b| / 2) (Eventually.of_forall fun x => ?_)
      simp only [Vpw, pw, le_refl, if_true, mul_zero, sub_zero, smul_eq_mul, Real.norm_eq_abs,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
      have hx2 : |x ^ 2| = x ^ 2 := abs_of_nonneg (sq_nonneg x)
      split_ifs
      · rw [abs_div, abs_mul, hx2, abs_two]
        nlinarith [abs_nonneg b, sq_nonneg x]
      · rw [abs_div, abs_mul, hx2, abs_two]
        nlinarith [abs_nonneg a, sq_nonneg x]
    simpa using hb.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num : 1 < 2))
  · have hd : HasDerivAt (fun x : ℝ => a * x ^ 2 / 2) (a * q) q := by
      have := ((hasDerivAt_pow 2 q).const_mul a).div_const 2
      exact this.congr_deriv (by norm_num; ring)
    have hpw : pw a b q = a * q := by simp [pw, hq.le]
    rw [hpw]
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hq] with x hx
    simp [Vpw, (show 0 < x from hx).le]

/-- **Proposition C(b) for the piecewise-linear model** (C.1 + C.2 + C.3), every h > 0,
δ ∈ (0, 1), t > 0. Potential V = Vpw(3 − δ, 3 + δ)/h² (curvature (3 ∓ δ)/h²), force
F/h² with F = pw(3 − δ, 3 + δ), initial point y₀ := (z.1, z.2/h) with z := K_{1/2}(t v)
(in the h = 1 scaled variables). Then for all m, j: q_{3m+j} = λ₊^m q_j, the signs of
q₀, q₁, q₂ are (+, −, +), and H(y_{3m}) = ½p² + V(q) → ∞. (The C⁴ smoothing C.4–C.5
and the exact-flow claim (c) are not formalised.) -/
theorem propC_b_pl {h δ t : ℝ} (hh : 0 < h) (h0 : 0 < δ) (h1 : δ < 1) (ht : 0 < t) :
    let F := pw (3 - δ) (3 + δ)
    let z := kick F (1 / 2) (t • vP δ)
    let y : ℕ → ℝ × ℝ := fun n => (sv (fun x => F x / h ^ 2) h)^[n] (z.1, z.2 / h)
    (∀ m j : ℕ, (y (3 * m + j)).1 = lamP δ ^ m * (y j).1) ∧
    0 < (y 0).1 ∧ (y 1).1 < 0 ∧ 0 < (y 2).1 ∧
    Tendsto (fun m : ℕ => (y (3 * m)).2 ^ 2 / 2 + Vpw (3 - δ) (3 + δ) (y (3 * m)).1 / h ^ 2)
      atTop atTop := by
  intro F z y
  have hh0 : h ≠ 0 := hh.ne'
  have hy : ∀ n, (y n).1 = ((Gpw δ)^[n] (t • vP δ)).1 := by
    intro n
    simp only [y]
    rw [sv_scale_iterate _ hh0]
    have : h * (z.2 / h) = z.2 := by field_simp
    rw [this]
    have hz : (z.1, z.2) = z := rfl
    rw [hz, sv_iterate_kick]
    rfl
  have hq : ∀ m j : ℕ, (y (3 * m + j)).1 = t * lamP δ ^ m * ((Gpw δ)^[j] (vP δ)).1 := by
    intro m j
    rw [hy, C3_orbit h0 h1 ht]; rfl
  obtain ⟨s0, s1, s2, -⟩ := C3_signs h0 h1
  have hq0 : ∀ m : ℕ, (y (3 * m)).1 = t * lamP δ ^ m * δ ^ 2 := by
    intro m; simpa [vP] using hq m 0
  refine ⟨fun m j => ?_, ?_, ?_, ?_, ?_⟩
  · rw [hq, show j = 3 * 0 + j by ring, hq 0 j]; ring_nf
  · simpa using (show 0 < (y (3 * 0 + 0)).1 by rw [hq]; simp; positivity)
  · have := hq 0 1; simp only [mul_zero, zero_add, pow_zero, mul_one] at this
    rw [this]; exact mul_neg_of_pos_of_neg ht s1
  · have := hq 0 2; simp only [mul_zero, zero_add, pow_zero, mul_one] at this
    rw [this]; exact mul_pos ht s2
  · have hl := lamP_gt_one h0 h1
    have hpow : Tendsto (fun m : ℕ => (lamP δ ^ 2) ^ m) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by nlinarith)
    have hc : 0 < (3 - δ) * (t * δ ^ 2) ^ 2 / 2 / h ^ 2 := by
      have : 0 < 3 - δ := by linarith
      positivity
    refine tendsto_atTop_mono (fun m => ?_) (hpow.const_mul_atTop hc)
    rw [hq0 m]
    have hpos : 0 ≤ t * lamP δ ^ m * δ ^ 2 := by
      have := (lt_trans zero_lt_one hl).le
      positivity
    simp only [Vpw, hpos, if_true]
    have e : (3 - δ) * (t * δ ^ 2) ^ 2 / 2 / h ^ 2 * (lamP δ ^ 2) ^ m =
        (3 - δ) * (t * lamP δ ^ m * δ ^ 2) ^ 2 / 2 / h ^ 2 := by
      rw [← pow_mul, mul_comm 2 m, pow_mul]; ring
    rw [e]
    nlinarith [sq_nonneg (y (3 * m)).2]

/-! ## C.7 (Example C′): two exact instances at smaller hω_max -/

theorem Gmap_pw_of_nonneg (a b : ℝ) {z : ℝ × ℝ} (hz : 0 ≤ z.1) :
    Gmap (pw a b) z = (z.1 + z.2 - a * z.1, z.2 - a * z.1) := by
  simp [Gmap, pw, hz]

theorem Gmap_pw_of_neg (a b : ℝ) {z : ℝ × ℝ} (hz : z.1 < 0) :
    Gmap (pw a b) z = (z.1 + z.2 - b * z.1, z.2 - b * z.1) := by
  simp [Gmap, pw, not_le.mpr hz]

/-- C.7 example (1/4, 13/20): P = product of G_k along the sign word +++----+++ (first letter rightmost). -/
def ex1P : Matrix (Fin 2) (Fin 2) ℝ := Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4)
theorem ex1P_eq : ex1P = !![((656538133:ℝ)/655360000), ((61100727:ℝ)/163840000); ((1715529:ℝ)/655360000), ((163705651:ℝ)/163840000)] := by
  have h0 : Gk ((1:ℝ)/4) = !![((3:ℝ)/4), (1:ℝ); ((-1:ℝ)/4), (1:ℝ)] := by simp only [Gk]; norm_num
  have h1 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) = !![((5:ℝ)/16), ((7:ℝ)/4); ((-7:ℝ)/16), ((3:ℝ)/4)] := by
    rw [h0]; simp only [Matrix.mul_fin_two]; norm_num
  have h2 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) = !![((-13:ℝ)/64), ((33:ℝ)/16); ((-33:ℝ)/64), ((5:ℝ)/16)] := by
    rw [h1]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h3 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) = !![((-1807:ℝ)/1280), ((119:ℝ)/64); ((-491:ℝ)/1280), ((-13:ℝ)/64)] := by
    rw [h2]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h4 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) = !![((-43589:ℝ)/25600), ((573:ℝ)/1280); ((-57:ℝ)/25600), ((-751:ℝ)/1280)] := by
    rw [h3]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h5 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) = !![((-454103:ℝ)/512000), ((-32129:ℝ)/25600); ((194861:ℝ)/512000), ((-15077:ℝ)/25600)] := by
    rw [h4]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h6 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) = !![((5174819:ℝ)/10240000), ((-1096683:ℝ)/512000); ((5284047:ℝ)/10240000), ((-106679:ℝ)/512000)] := by
    rw [h5]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h7 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((1:ℝ)/4) = !![((37458117:ℝ)/40960000), ((-16758841:ℝ)/10240000); ((17985721:ℝ)/40960000), ((3150467:ℝ)/10240000)] := by
    rw [h6]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h8 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) = !![((35881943:ℝ)/32768000), ((-29577247:ℝ)/40960000); ((8271059:ℝ)/32768000), ((30587589:ℝ)/40960000)] := by
    rw [h7]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h9 : Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((13:ℝ)/20) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) * Gk ((1:ℝ)/4) = !![((656538133:ℝ)/655360000), ((61100727:ℝ)/163840000); ((1715529:ℝ)/655360000), ((163705651:ℝ)/163840000)] := by
    rw [h8]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  exact h9
theorem ex1_trace_gt_two : 2 < ex1P.trace := by
  rw [ex1P_eq, trace_fin_two_of]; norm_num
/-- C.7 example (1/4, 13/20): λ₊ = (T + √(T² − 4))/2 with T = tr P = 1311360737/655360000. -/
def ex1Lam : ℝ := (((1311360737:ℝ)/655360000) + Real.sqrt (((1311360737:ℝ)/655360000) ^ 2 - 4)) / 2
theorem ex1_trace : ex1P.trace = ((1311360737:ℝ)/655360000) := by
  rw [ex1P_eq, trace_fin_two_of]; norm_num
theorem ex1_lam_quad : ex1Lam ^ 2 - ((1311360737:ℝ)/655360000) * ex1Lam + 1 = 0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ ((1311360737:ℝ)/655360000) ^ 2 - 4 by norm_num)
  unfold ex1Lam
  linear_combination hs / 4
theorem ex1_lam_bounds : ((3462014265721551381594134516123002292051454883:ℝ)/3355443200000000000000000000000000000000000000) < ex1Lam ∧ ex1Lam < ((886275652024717153688098436127488586765172450049:ℝ)/858993459200000000000000000000000000000000000000) := by
  have h1 : ((104930779001551381594134516123002292051454883:ℝ)/1677721600000000000000000000000000000000000000) < Real.sqrt (((1311360737:ℝ)/655360000) ^ 2 - 4) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt (((1311360737:ℝ)/655360000) ^ 2 - 4) < ((26862279424397153688098436127488586765172450049:ℝ)/429496729600000000000000000000000000000000000000) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold ex1Lam
  constructor <;> linarith
/-- The eigen-direction ±(P₁₂, λ₊ − P₁₁) (sign chosen so that q₀ has the first letter's sign). -/
def ex1V : ℝ × ℝ := ((((61100727:ℝ)/163840000) + (0:ℝ) * ex1Lam), (((-656538133:ℝ)/655360000) + (1:ℝ) * ex1Lam))
/-- **Example C′ (1/4, 13/20)**, exact: trace > 2, strict signs +++----+++ along the orbit of
the eigen-direction, and G^10 v = λ₊ v. -/
theorem ex1_orbit :
    0 < ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[0] ex1V).1 ∧
    0 < ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[1] ex1V).1 ∧
    0 < ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[2] ex1V).1 ∧
    ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[3] ex1V).1 < 0 ∧
    ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[4] ex1V).1 < 0 ∧
    ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[5] ex1V).1 < 0 ∧
    ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[6] ex1V).1 < 0 ∧
    0 < ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[7] ex1V).1 ∧
    0 < ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[8] ex1V).1 ∧
    0 < ((Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[9] ex1V).1 ∧
    (Gmap (pw ((1:ℝ)/4) ((13:ℝ)/20)))^[10] ex1V = ex1Lam • ex1V := by
  obtain ⟨lo, hi⟩ := ex1_lam_bounds
  have hq := ex1_lam_quad
  set F := pw ((1:ℝ)/4) ((13:ℝ)/20) with hF
  have z0 : (Gmap F)^[0] ex1V = ((((61100727:ℝ)/163840000) + (0:ℝ) * ex1Lam), (((-656538133:ℝ)/655360000) + (1:ℝ) * ex1Lam)) := by
    simp only [Function.iterate_zero, id, ex1V]
  have z1 : (Gmap F)^[1] ex1V = ((((-29577247:ℝ)/40960000) + (1:ℝ) * ex1Lam), (((-35881943:ℝ)/32768000) + (1:ℝ) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z0]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z2 : (Gmap F)^[2] ex1V = ((((-16758841:ℝ)/10240000) + ((7:ℝ)/4) * ex1Lam), (((-37458117:ℝ)/40960000) + ((3:ℝ)/4) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z1]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z3 : (Gmap F)^[3] ex1V = ((((-1096683:ℝ)/512000) + ((33:ℝ)/16) * ex1Lam), (((-5174819:ℝ)/10240000) + ((5:ℝ)/16) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z2]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z4 : (Gmap F)^[4] ex1V = ((((-32129:ℝ)/25600) + ((331:ℝ)/320) * ex1Lam), (((454103:ℝ)/512000) + ((-329:ℝ)/320) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z3]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z5 : (Gmap F)^[5] ex1V = ((((573:ℝ)/1280) + ((-4263:ℝ)/6400) * ex1Lam), (((43589:ℝ)/25600) + ((-10883:ℝ)/6400) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z4]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z6 : (Gmap F)^[6] ex1V = ((((119:ℝ)/64) + ((-247501:ℝ)/128000) * ex1Lam), (((1807:ℝ)/1280) + ((-162241:ℝ)/128000) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z5]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z7 : (Gmap F)^[7] ex1V = ((((33:ℝ)/16) + ((-4977327:ℝ)/2560000) * ex1Lam), (((13:ℝ)/64) + ((-27307:ℝ)/2560000) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z6]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z8 : (Gmap F)^[8] ex1V = ((((7:ℝ)/4) + ((-15041209:ℝ)/10240000) * ex1Lam), (((-5:ℝ)/16) + ((4868099:ℝ)/10240000) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z7]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z9 : (Gmap F)^[9] ex1V = (((1:ℝ) + ((-25651231:ℝ)/40960000) * ex1Lam), (((-3:ℝ)/4) + ((6902721:ℝ)/8192000) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z8]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z10 : (Gmap F)^[10] ex1V = (((0:ℝ) + ((61100727:ℝ)/163840000) * ex1Lam), ((-1:ℝ) + ((163705651:ℝ)/163840000) * ex1Lam)) := by
    rw [Function.iterate_succ_apply', z9]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  exact ⟨by rw [z0]; dsimp only; linarith,
    by rw [z1]; dsimp only; linarith,
    by rw [z2]; dsimp only; linarith,
    by rw [z3]; dsimp only; linarith,
    by rw [z4]; dsimp only; linarith,
    by rw [z5]; dsimp only; linarith,
    by rw [z6]; dsimp only; linarith,
    by rw [z7]; dsimp only; linarith,
    by rw [z8]; dsimp only; linarith,
    by rw [z9]; dsimp only; linarith,
    by
      rw [z10]; simp only [ex1V, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      exact ⟨by linear_combination (0:ℝ) * hq, by linear_combination (-1:ℝ) * hq⟩⟩

/-- C.7 example (7/40, 5/16): P = product of G_k along the sign word ---+++++++--- (first letter rightmost). -/
def ex2P : Matrix (Fin 2) (Fin 2) ℝ := Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16)
theorem ex2P_eq : ex2P = !![((2750855446004118673:ℝ)/2748779069440000000), ((34478728745995859:ℝ)/171798691840000000); ((3457762297149537:ℝ)/2748779069440000000), ((171712355231685571:ℝ)/171798691840000000)] := by
  have h0 : Gk ((5:ℝ)/16) = !![((11:ℝ)/16), (1:ℝ); ((-5:ℝ)/16), (1:ℝ)] := by simp only [Gk]; norm_num
  have h1 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) = !![((41:ℝ)/256), ((27:ℝ)/16); ((-135:ℝ)/256), ((11:ℝ)/16)] := by
    rw [h0]; simp only [Matrix.mul_fin_two]; norm_num
  have h2 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) = !![((-1709:ℝ)/4096), ((473:ℝ)/256); ((-2365:ℝ)/4096), ((41:ℝ)/256)] := by
    rw [h1]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h3 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) = !![((-109373:ℝ)/163840), ((5859:ℝ)/4096); ((-82637:ℝ)/163840), ((-1709:ℝ)/4096)] := by
    rw [h2]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h4 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) = !![((-5249829:ℝ)/6553600), ((124987:ℝ)/163840); ((-2248501:ℝ)/6553600), ((-150997:ℝ)/163840)] := by
    rw [h3]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h5 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) = !![((-208240717:ℝ)/262144000), ((-250349:ℝ)/6553600); ((-31921373:ℝ)/262144000), ((-8288381:ℝ)/6553600)] := by
    rw [h4]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h6 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) = !![((-6801845941:ℝ)/10485760000), ((-218254677:ℝ)/262144000); ((1267341371:ℝ)/10485760000), ((-363456613:ℝ)/262144000)] := by
    rw [h5]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h7 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) = !![((-163349606493:ℝ)/419430400000), ((-15532033021:ℝ)/10485760000); ((143590116883:ℝ)/419430400000), ((-13270923149:ℝ)/10485760000)] := by
    rw [h6]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h8 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) = !![((-1041567768389:ℝ)/16777216000000), ((-784630927333:ℝ)/419430400000); ((8454332338859:ℝ)/16777216000000), ((-387246809077:ℝ)/419430400000)] := by
    rw [h7]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h9 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) = !![((185324923296403:ℝ)/671088640000000), ((-32426804861709:ℝ)/16777216000000); ((387422073723907:ℝ)/671088640000000), ((-7035540024221:ℝ)/16777216000000)] := by
    rw [h8]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h10 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((5:ℝ)/16) = !![((8523935128602233:ℝ)/10737418240000000), ((-1111747271171957:ℝ)/671088640000000); ((5668750815807177:ℝ)/10737418240000000), ((106000472755067:ℝ)/671088640000000)] := by
    rw [h9]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h11 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) = !![((182703068108381123:ℝ)/171798691840000000), ((-9264021210149079:ℝ)/10737418240000000); ((53876221153473587:ℝ)/171798691840000000), ((7364758379888249:ℝ)/10737418240000000)] := by
    rw [h10]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  have h12 : Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((7:ℝ)/40) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) * Gk ((5:ℝ)/16) = !![((2750855446004118673:ℝ)/2748779069440000000), ((34478728745995859:ℝ)/171798691840000000); ((3457762297149537:ℝ)/2748779069440000000), ((171712355231685571:ℝ)/171798691840000000)] := by
    rw [h11]; simp only [Gk, Matrix.mul_fin_two]; norm_num
  exact h12
theorem ex2_trace_gt_two : 2 < ex2P.trace := by
  rw [ex2P_eq, trace_fin_two_of]; norm_num
/-- C.7 example (7/40, 5/16): λ₊ = (T + √(T² − 4))/2 with T = tr P = 5498253129711087809/2748779069440000000. -/
def ex2Lam : ℝ := (((5498253129711087809:ℝ)/2748779069440000000) + Real.sqrt (((5498253129711087809:ℝ)/2748779069440000000) ^ 2 - 4)) / 2
theorem ex2_trace : ex2P.trace = ((5498253129711087809:ℝ)/2748779069440000000) := by
  rw [ex2P_eq, trace_fin_two_of]; norm_num
theorem ex2_lam_quad : ex2Lam ^ 2 - ((5498253129711087809:ℝ)/2748779069440000000) * ex2Lam + 1 = 0 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ ((5498253129711087809:ℝ)/2748779069440000000) ^ 2 - 4 by norm_num)
  unfold ex2Lam
  linear_combination hs / 4
theorem ex2_lam_bounds : ((3070755433627160919020056949077431512865707798458105292978546807479:ℝ)/3022314549036572936765440000000000000000000000000000000000000000000) < ex2Lam ∧ ex2Lam < ((3838444292033951148775071186346789391082134748072631616223183509349:ℝ)/3777893186295716170956800000000000000000000000000000000000000000000) := by
  have h1 : ((48058809340598606285427257685431512865707798458105292978546807479:ℝ)/1511157274518286468382720000000000000000000000000000000000000000000) < Real.sqrt (((5498253129711087809:ℝ)/2748779069440000000) ^ 2 - 4) := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h2 : Real.sqrt (((5498253129711087809:ℝ)/2748779069440000000) ^ 2 - 4) < ((60073511675748257856784072106789391082134748072631616223183509349:ℝ)/1888946593147858085478400000000000000000000000000000000000000000000) := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold ex2Lam
  constructor <;> linarith
/-- The eigen-direction ±(P₁₂, λ₊ − P₁₁) (sign chosen so that q₀ has the first letter's sign). -/
def ex2V : ℝ × ℝ := ((((-34478728745995859:ℝ)/171798691840000000) + (0:ℝ) * ex2Lam), (((2750855446004118673:ℝ)/2748779069440000000) + (-1:ℝ) * ex2Lam))
/-- **Example C′ (7/40, 5/16)**, exact: trace > 2, strict signs ---+++++++--- along the orbit of
the eigen-direction, and G^13 v = λ₊ v. -/
theorem ex2_orbit :
    ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[0] ex2V).1 < 0 ∧
    ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[1] ex2V).1 < 0 ∧
    ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[2] ex2V).1 < 0 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[3] ex2V).1 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[4] ex2V).1 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[5] ex2V).1 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[6] ex2V).1 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[7] ex2V).1 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[8] ex2V).1 ∧
    0 < ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[9] ex2V).1 ∧
    ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[10] ex2V).1 < 0 ∧
    ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[11] ex2V).1 < 0 ∧
    ((Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[12] ex2V).1 < 0 ∧
    (Gmap (pw ((7:ℝ)/40) ((5:ℝ)/16)))^[13] ex2V = ex2Lam • ex2V := by
  obtain ⟨lo, hi⟩ := ex2_lam_bounds
  have hq := ex2_lam_quad
  set F := pw ((7:ℝ)/40) ((5:ℝ)/16) with hF
  have z0 : (Gmap F)^[0] ex2V = ((((-34478728745995859:ℝ)/171798691840000000) + (0:ℝ) * ex2Lam), (((2750855446004118673:ℝ)/2748779069440000000) + (-1:ℝ) * ex2Lam)) := by
    simp only [Function.iterate_zero, id, ex2V]
  have z1 : (Gmap F)^[1] ex2V = ((((9264021210149079:ℝ)/10737418240000000) + (-1:ℝ) * ex2Lam), (((182703068108381123:ℝ)/171798691840000000) + (-1:ℝ) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z0]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z2 : (Gmap F)^[2] ex2V = ((((1111747271171957:ℝ)/671088640000000) + ((-27:ℝ)/16) * ex2Lam), (((8523935128602233:ℝ)/10737418240000000) + ((-11:ℝ)/16) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z1]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z3 : (Gmap F)^[3] ex2V = ((((32426804861709:ℝ)/16777216000000) + ((-473:ℝ)/256) * ex2Lam), (((185324923296403:ℝ)/671088640000000) + ((-41:ℝ)/256) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z2]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z4 : (Gmap F)^[4] ex2V = ((((784630927333:ℝ)/419430400000) + ((-17249:ℝ)/10240) * ex2Lam), (((-1041567768389:ℝ)/16777216000000) + ((1671:ℝ)/10240) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z3]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z5 : (Gmap F)^[5] ex2V = ((((15532033021:ℝ)/10485760000) + ((-502377:ℝ)/409600) * ex2Lam), (((-163349606493:ℝ)/419430400000) + ((187583:ℝ)/409600) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z4]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z6 : (Gmap F)^[6] ex2V = ((((218254677:ℝ)/262144000) + ((-9075121:ℝ)/16384000) * ex2Lam), (((-6801845941:ℝ)/10485760000) + ((11019959:ℝ)/16384000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z5]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z7 : (Gmap F)^[7] ex2V = ((((250349:ℝ)/6553600) + ((141319367:ℝ)/655360000) * ex2Lam), (((-208240717:ℝ)/262144000) + ((504324207:ℝ)/655360000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z6]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z8 : (Gmap F)^[8] ex2V = ((((-124987:ℝ)/163840) + ((24836507391:ℝ)/26214400000) * ex2Lam), (((-5249829:ℝ)/6553600) + ((19183732711:ℝ)/26214400000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z7]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z9 : (Gmap F)^[9] ex2V = ((((-5859:ℝ)/4096) + ((1586954052343:ℝ)/1048576000000) * ex2Lam), (((-109373:ℝ)/163840) + ((593493756703:ℝ)/1048576000000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z8]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z10 : (Gmap F)^[10] ex2V = ((((-473:ℝ)/256) + ((76109233995439:ℝ)/41943040000000) * ex2Lam), (((-1709:ℝ)/4096) + ((12631071901719:ℝ)/41943040000000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z9]
    rw [Gmap_pw_of_nonneg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z11 : (Gmap F)^[11] ex2V = ((((-27:ℝ)/16) + ((1039298724377333:ℝ)/671088640000000) * ex2Lam), (((41:ℝ)/256) + ((-178449019549691:ℝ)/671088640000000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z10]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z12 : (Gmap F)^[12] ex2V = (((-1:ℝ) + ((8577101655355607:ℝ)/10737418240000000) * ex2Lam), (((11:ℝ)/16) + ((-8051677934681721:ℝ)/10737418240000000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z11]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  have z13 : (Gmap F)^[13] ex2V = (((0:ℝ) + ((-34478728745995859:ℝ)/171798691840000000) * ex2Lam), ((1:ℝ) + ((-171712355231685571:ℝ)/171798691840000000) * ex2Lam)) := by
    rw [Function.iterate_succ_apply', z12]
    rw [Gmap_pw_of_neg _ _ (by dsimp only; linarith)]
    simp only [Prod.mk.injEq]; constructor <;> ring
  exact ⟨by rw [z0]; dsimp only; linarith,
    by rw [z1]; dsimp only; linarith,
    by rw [z2]; dsimp only; linarith,
    by rw [z3]; dsimp only; linarith,
    by rw [z4]; dsimp only; linarith,
    by rw [z5]; dsimp only; linarith,
    by rw [z6]; dsimp only; linarith,
    by rw [z7]; dsimp only; linarith,
    by rw [z8]; dsimp only; linarith,
    by rw [z9]; dsimp only; linarith,
    by rw [z10]; dsimp only; linarith,
    by rw [z11]; dsimp only; linarith,
    by rw [z12]; dsimp only; linarith,
    by
      rw [z13]; simp only [ex2V, Prod.smul_mk, smul_eq_mul, Prod.mk.injEq]
      exact ⟨by linear_combination (0:ℝ) * hq, by linear_combination (1:ℝ) * hq⟩⟩


/-! ## C.8 Step 2: the continuant (countability) lemma (LR III Lemma 4.1, as used) -/

section Continuant

open Polynomial

/-- The LR slope of a letter as a polynomial in E = E_LR: f₊ = 2 − E + μ, f₋ = 2 − E − μ. -/
def fpoly (μ : ℝ) (s : Bool) : ℝ[X] := C (2 + if s then μ else -μ) - X

/-- LR's linear branch T_f = [[f, −1], [1, 0]] over ℝ[E]. -/
def Tpoly (μ : ℝ) (s : Bool) : Matrix (Fin 2) (Fin 2) ℝ[X] := !![fpoly μ s, -1; 1, 0]

/-- Left-to-right product T_{s₁} ⋯ T_{s_ℓ}. -/
def wprod (μ : ℝ) : List Bool → Matrix (Fin 2) (Fin 2) ℝ[X]
  | [] => 1
  | s :: w => Tpoly μ s * wprod μ w

/-- The dossier's word product T_w := T_{f_ℓ} ⋯ T_{f_1} for w = (s₁, …, s_ℓ). -/
def Tw (μ : ℝ) (w : List Bool) : Matrix (Fin 2) (Fin 2) ℝ[X] := wprod μ w.reverse

/-- u_w(E): the (1, 2) entry of T_w. -/
def uw (μ : ℝ) (w : List Bool) : ℝ[X] := Tw μ w 0 1

theorem fpoly_eval (μ E : ℝ) (s : Bool) :
    (fpoly μ s).eval E = 2 - E + if s then μ else -μ := by
  simp [fpoly]; ring

theorem degree_fpoly (μ : ℝ) (s : Bool) : (fpoly μ s).degree = 1 := by
  have : fpoly μ s = -(X - C (2 + if s then μ else -μ)) := by simp [fpoly]
  rw [this, degree_neg, degree_X_sub_C]

theorem leadingCoeff_fpoly (μ : ℝ) (s : Bool) : (fpoly μ s).leadingCoeff = -1 := by
  have : fpoly μ s = -(X - C (2 + if s then μ else -μ)) := by simp [fpoly]
  rw [this, leadingCoeff_neg, leadingCoeff_X_sub_C]

/-- Induction on words for the left-to-right product: for a word of length ℓ + 1, the (1, 2)
entry has degree ℓ and leading coefficient (−1)^{ℓ+1}, and the (2, 2) entry has degree < ℓ. -/
theorem wprod_deg (μ : ℝ) : ∀ (w : List Bool), w ≠ [] →
    (wprod μ w 0 1).degree = ((w.length - 1 : ℕ) : WithBot ℕ) ∧
    (wprod μ w 0 1).leadingCoeff = (-1) ^ w.length ∧
    (wprod μ w 1 1).degree < ((w.length - 1 : ℕ) : WithBot ℕ)
  | [], h => absurd rfl h
  | [s], _ => by
    simp [wprod, Tpoly]
  | s :: t :: w, _ => by
    obtain ⟨h1, h2, h3⟩ := wprod_deg μ (t :: w) (List.cons_ne_nil _ _)
    set N := wprod μ (t :: w) with hN
    have eW : wprod μ (s :: t :: w) = Tpoly μ s * N := rfl
    have e01 : wprod μ (s :: t :: w) 0 1 = fpoly μ s * N 0 1 - N 1 1 := by
      rw [eW]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two]; ring
    have e11 : wprod μ (s :: t :: w) 1 1 = N 0 1 := by
      rw [eW]; simp [Tpoly, Matrix.mul_apply, Fin.sum_univ_two]
    simp only [List.length_cons, Nat.add_sub_cancel] at h1 h2 h3 ⊢
    have hdm : (fpoly μ s * N 0 1).degree = ((w.length + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_mul, degree_fpoly, h1]
      norm_cast; ring
    have hlt : (N 1 1).degree < (fpoly μ s * N 0 1).degree := by
      rw [hdm]; refine lt_trans h3 ?_
      exact_mod_cast Nat.lt_succ_self _
    refine ⟨?_, ?_, ?_⟩
    · rw [e01, degree_sub_eq_left_of_degree_lt hlt, hdm]
    · rw [e01, leadingCoeff_sub_of_degree_lt hlt, leadingCoeff_mul, leadingCoeff_fpoly, h2]
      ring
    · rw [e11, h1]; exact_mod_cast Nat.lt_succ_self _

/-- **The continuant lemma (C.8 Step 2; LR III Lemma 4.1).** For every μ and every nonempty
word w of length ℓ, u_w(E) is a polynomial in E of exact degree ℓ − 1 with leading
coefficient (−1)^ℓ. -/
theorem uw_degree (μ : ℝ) {w : List Bool} (hw : w ≠ []) :
    (uw μ w).degree = ((w.length - 1 : ℕ) : WithBot ℕ) ∧
    (uw μ w).leadingCoeff = (-1) ^ w.length := by
  have hr : w.reverse ≠ [] := by simpa using hw
  obtain ⟨h1, h2, -⟩ := wprod_deg μ w.reverse hr
  simp only [List.length_reverse] at h1 h2
  exact ⟨h1, h2⟩

theorem uw_ne_zero (μ : ℝ) {w : List Bool} (hw : w ≠ []) : uw μ w ≠ 0 := by
  intro h
  have := (uw_degree μ hw).2
  rw [h, leadingCoeff_zero] at this
  have h1 : ((-1 : ℝ) ^ w.length) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact h1 this.symm

/-- Bad(μ) := {E : u_w(E) = 0 for some nonempty word w} is countable. -/
theorem bad_countable (μ : ℝ) :
    {E : ℝ | ∃ w : List Bool, w ≠ [] ∧ (uw μ w).eval E = 0}.Countable := by
  have : {E : ℝ | ∃ w : List Bool, w ≠ [] ∧ (uw μ w).eval E = 0} =
      ⋃ w : {w : List Bool // w ≠ []}, {E | IsRoot (uw μ w.1) E} := by
    ext E; simp [IsRoot]
  rw [this]
  exact Set.countable_iUnion fun w => (finite_setOf_isRoot (uw_ne_zero μ w.2)).countable

/-- A periodic ray through a point (0, y) forces u_w(E) = 0: if T_w(E)(0, 1)ᵀ = λ(0, 1)ᵀ
then u_w(E) = 0. -/
theorem uw_eval_zero_of_ray (μ E lam : ℝ) (w : List Bool)
    (h : ((Tw μ w).map (eval E)) *ᵥ ![0, 1] = lam • ![0, 1]) : (uw μ w).eval E = 0 := by
  have := congrFun h 0
  simpa [mulVec, dotProduct, Fin.sum_univ_two, uw] using this

/-- The evaluated branch is LR's T_f with f = 2 − E ± μ. -/
theorem Tpoly_eval (μ E : ℝ) (s : Bool) :
    (Tpoly μ s).map (eval E) = !![2 - E + (if s then μ else -μ), -1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Tpoly, fpoly_eval]

end Continuant

end OCF.A3

end

#print axioms OCF.A3.sv_neg_sv
#print axioms OCF.A3.sv_sv_neg
#print axioms OCF.A3.flip_sv_flip
#print axioms OCF.A3.svD_neg_svD
#print axioms OCF.A3.svD_svD_neg
#print axioms OCF.A3.flipD_svD_flipD
#print axioms OCF.A3.orbit_succ
#print axioms OCF.A3.orbitD_succ
#print axioms OCF.A3.sv_lin_eq_S
#print axioms OCF.A3.det_S
#print axioms OCF.A3.Eh_sv
#print axioms OCF.A3.Eh_sv_omega
#print axioms OCF.A3.Eh_orbit
#print axioms OCF.A3.sandwich_pointwise
#print axioms OCF.A3.gamma_eq
#print axioms OCF.A3.propB_iii
#print axioms OCF.A3.sharp_instance
#print axioms OCF.A3.S_pow_edge
#print axioms OCF.A3.iterate_edge
#print axioms OCF.A3.H_edge
#print axioms OCF.A3.edge_unbounded
#print axioms OCF.A3.edge_p_zero
#print axioms OCF.A3.EhD_svD
#print axioms OCF.A3.EhD_orbitD
#print axioms OCF.A3.EhD_one_eq
#print axioms OCF.A3.ANA_le
#print axioms OCF.A3.sandwichD
#print axioms OCF.A3.propBprime_iii
#print axioms OCF.A3.propB_iii_eig
#print axioms OCF.A3.sv_scale
#print axioms OCF.A3.sv_scale_iterate
#print axioms OCF.A3.sv_kick
#print axioms OCF.A3.sv_iterate_kick
#print axioms OCF.A3.conj_LR
#print axioms OCF.A3.GbGa
#print axioms OCF.A3.Pmat_eq
#print axioms OCF.A3.trace_Pmat
#print axioms OCF.A3.det_Pmat
#print axioms OCF.A3.trace_Pmat_gt_two
#print axioms OCF.A3.lamP_charpoly
#print axioms OCF.A3.lamP_gt_one
#print axioms OCF.A3.Pmat_mulVec_v
#print axioms OCF.A3.P11_bounds
#print axioms OCF.A3.C3_signs
#print axioms OCF.A3.C3_orbit
#print axioms OCF.A3.hasDerivAt_Vpw
#print axioms OCF.A3.propC_b_pl
#print axioms OCF.A3.ex1P_eq
#print axioms OCF.A3.ex1_trace_gt_two
#print axioms OCF.A3.ex1_orbit
#print axioms OCF.A3.ex2P_eq
#print axioms OCF.A3.ex2_trace_gt_two
#print axioms OCF.A3.ex2_orbit
#print axioms OCF.A3.uw_degree
#print axioms OCF.A3.uw_ne_zero
#print axioms OCF.A3.bad_countable
#print axioms OCF.A3.uw_eval_zero_of_ray
#print axioms OCF.A3.Tpoly_eval

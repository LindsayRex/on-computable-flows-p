/-
G12 (atom types and typing rules) — the declaration order (spine G1) and the typing rules
R-sum and R-affine for smooth atoms (spine G2), plus the "not a lattice" witness.
Companion of `G12DominanceLemma.lean` (S2.8), which it imports and reuses (`extSum`).

Source of truth: project_plan/done/proof_audits/G12_typing_calculus/01_derivation.md (sha256 prefix
04bc98fa19e21ad2, unchanged by this pass): Definitions G1.1, G1.2, Lemma G1.3, Remark G1.4(b),(c)
(S1.7, S1.8), Lemma G2.1(a)–(e), Lemma G2.3(a) with Remark G2.4 (S3.6); the landing draft
04_landing_draft_a.tex (def:declarations, lem:decl-order, the diag(1,4) paragraph,
lem:rule-sum(a)–(c), lem:rule-affine(a)); rulings in 03_adjudication.md (tier call:
STATEMENT-FORMALISED recommended for G1.3 and G2.1; erratum: d ≥ 1 for S2.8 only).

DEFINITIONAL MAP:
* ℝᵈ — G3's `Vec d = EuclideanSpace ℝ (Fin d)`. β-smooth, C(f, σ), kernel attribute validity —
  G3's `LipGrad`, `ModC`, `KernelValid` (verbatim landed def:moduli, def:kernel-attribute).
* 𝒦 = {void} ∪ {(K, ν) : K a subspace, ν > 0} — `KComp` (`void`, `pair K ν hν`), with the order
  of Definition G1.2 (`KComp.pair_le_pair`: K ⊇ K′ ∧ ν ≤ ν′; void least).
* 𝒟_S = [0, ∞] × [−∞, ∞) × 𝒦 — `SDecl` with β : ℝ≥0∞, σ : WithBot ℝ (the dominance file's
  convention), A : KComp. Validity — `SDecl.Valid` = `SmoothOK` (β = ∞ no claim) ∧ `CurvOK`
  (σ = −∞ no claim) ∧ `KComp.Valid`. f ∈ C¹ is `ContDiff ℝ 1 f`, a hypothesis of every rule and
  a conclusion for F and f∘ℓ.
* 𝒟_N = [0, ∞) × Π × 𝒲 — `NDecl` with σ : ℝ≥0, Π — `ProxAttr Prog` (oracle | explicit 𝒫 κ,
  κ ∈ ℕ), 𝒲 — `FrameAttr` (void | an (n+1) × d matrix). Programs are abstract: `ProgSem`
  gives "𝒫 is oracle-free, well defined on (0, ∞) × ℝᵈ and returns prox_{αg}" (`computes`) and the
  operation count; every result holds for every semantics. C(g, σ) for g : ℝᵈ → [−∞, +∞] —
  `NModC` (epigraph of g − (σ/2)‖·‖² convex, B&C Def. 8.1). g ∈ Γ₀ is not used.
* product order — the `LE`/`PartialOrder` instances of `SDecl`, `NDecl` (componentwise);
  different sorts — `AnyDecl = SDecl ⊕ NDecl` with Mathlib's sum order.
* finite index set S — `Fin n`; F = Σ wᵢfᵢ — `sumF`; β̂ — `betaHatX` (in [0, ∞]); σ̂_S —
  `sigmaHatX` (= `extSum`, −∞ absorbs); S_K — `SKX`; Δ_w(T) — `deltaWX` (T1SharpBound's `deltaW`
  of (Kᵢ, wᵢνᵢ)_{i∈T}, T enumerated by G3's `tIdx`, Kᵢ by Mathlib's `stdOrthonormalBasis`; it
  is choice-independent by `deltaW_isGreatest`); b(T) — `bX`; σ_𝔈^T — `sigmaTX`; σ_𝔈 of
  rem:fb-spec — `sigmaEX`; Q = Σ wᵢνᵢP_{Kᵢ⊥} — `Qsum`.
* λ_min, λ_max, λ⁺ of a symmetric operator — `opLamMin`, `opLamMax`, `opLamPlus` (min, max,
  smallest nonzero of Mathlib's `LinearMap.IsSymmetric.eigenvalues`).
* L ∈ ℝ^{p×d} — a linear map `L : Vec d →L[ℝ] Vec p` (the standard identification; Lᵀ is the
  adjoint), ℓ(x) = Lx + b; LᵀL — `gramL L`; N_L = LᵀP_{K⊥}L — `NL L K`; L⁻¹(K) —
  `K.comap L`; β^ℓ, σ^ℓ, A^ℓ — `betaAff`, `sigmaAff`, `affKC`.

STATEMENTS FORMALISED (statement + proof):
* Lemma G1.3(a): `decl_order_partial` (both sorts: reflexive, transitive, antisymmetric, equal
  to the componentwise order; sorts incomparable); instances `KComp`, `ProxAttr`, `FrameAttr`,
  `SDecl`, `NDecl` : PartialOrder.
* Lemma G1.3(b): `SDecl.valid_of_le`, `NDecl.valid_of_le` (components: `lipGrad_mono`,
  `modC_anti`, `kernelValid_anti`, `nmodC_anti`, `ProxAttr.valid_of_le`, `FrameAttr.valid_of_le`).
* Lemma G1.3(c)(i)–(iii): `sat_i`, `sat_ii`, `sat_iii`.
* Remark G1.4(b) (S1.7), Π has no joins: `ProxAttr.no_upper_bound`.
* Remark G1.4(c) (S1.8), "not a lattice" witness H = diag(1, 4): `not_lattice_witness`
  (kernel component: ({0}, 1), (span e₁, 4) valid and maximal, LUB ({0}, 4), invalid) and
  `not_lattice_witness_decl` (the same for full declarations (4, 1, ·)).
* R-sum, draft lem:rule-sum (a)–(c) = G2.1(a)–(e): `rule_sum_a` ((β̂, σ̂_S, void) valid, F ∈ C¹;
  the β̂ clause through G3's `Decl.betaHat_valid`), `rule_sum_b` (C(F, b(T)) for every T ⊆ S_K,
  (β̂, σ_𝔈^T, void) valid; extended values, any d), `rule_sum_b_compare` (σ_𝔈^{S_K} ≥ σ_𝔈,
  equality if S_K = S), `rule_sum_b_G3` (G3's `Decl.sigmaT_valid`, cited: finite βᵢ, real σᵢ),
  `rule_sum_c` and `rule_sum_c_decl` (the kernel attribute (⋂Kᵢ, ν), ν ∈ (0, λ⁺(Q)]; (ℝᵈ, ν) if
  Q = 0).
* R-affine, draft lem:rule-affine(a) = G2.3(a), for C¹ atoms: `rule_affine` (packaged),
  `rule_affine_beta` (β(f∘ℓ) ≤ λ_max(LᵀL)β), `opLamMax_gramL` (λ_max(LᵀL) = ‖L‖²),
  `rule_affine_sigma` (signed rule), `rule_affine_kernel` (preimage pair), `rule_affine_invariance`;
  sharpness (S3.6, "each output is attained"): `rule_affine_sharp_beta`,
  `rule_affine_sharp_sigma` (d ≥ 1), `rule_affine_sharp_kernel`.
* Supporting: Rayleigh bounds `opLamMin_mul_le`, `le_opLamMax_mul`, `opLamPlus_mul_le`,
  `opLamPlus_pos`; `ker_Qsum_le`, `ker_NL_le`, `le_ker_NL`; `gradient_comp_aff`.

NOT COVERED (remain PROSE-ONLY): every prox clause — lem:rule-sum(d) (G2.1(f), non-smooth
scaling), lem:rule-affine(b) (G2.3(b)), lem:rule-frame (G2.5), the oracle repair and
rem:nonlift-oracle, R-split (Definition G2.6, Lemma G2.7); Remark G1.4(a) (S1.6, order versus
implication); Definition G2.9 and Lemma G2.10 (obligations); Remarks G2.2(i),(iii), G2.4 S3.7–S3.9,
G2.8, G2.11, G2.12; the numerical checks. Mathlib has no proximity operator.

Status tier: FORMALISED (statement + proof, no sorry) for Lemma G1.3(a)–(c), Remark G1.4(b),(c),
Lemma G2.1(a)–(e) (draft lem:rule-sum(a)–(c)) and Lemma G2.3(a) with its sharpness (draft
lem:rule-affine(a)), for C¹ atoms.
-/
import Mathlib
import OcfVerification.G3SoundnessQuadratic
import OcfVerification.G12DominanceLemma

open scoped ENNReal NNReal
open Set

namespace OCF.G12

open OCF.G3 (Vec LipGrad ModC StrongMono KernelValid modC_iff_strongMono)

/-! ## §1. Declarations, their order, validity (Definitions G1.1, G1.2; Lemma G1.3) -/

section Declarations

variable {d : ℕ}

/-- The kernel component 𝒦 := {void} ∪ {(K, ν) : K ⊆ ℝᵈ a subspace, ν > 0}. -/
inductive KComp (d : ℕ) where
  | void : KComp d
  | pair (K : Submodule ℝ (Vec d)) (ν : ℝ) (hν : 0 < ν) : KComp d

namespace KComp

/-- The order on 𝒦 (Definition G1.2): void ⪯ everything; (K, ν) ⪯ (K', ν') iff K ⊇ K' and
ν ≤ ν'. -/
def le : KComp d → KComp d → Prop
  | void, _ => True
  | pair _ _ _, void => False
  | pair K ν _, pair K' ν' _ => K' ≤ K ∧ ν ≤ ν'

instance : LE (KComp d) := ⟨KComp.le⟩

@[simp] lemma void_le (A : KComp d) : (void : KComp d) ≤ A := trivial
@[simp] lemma not_pair_le_void {K : Submodule ℝ (Vec d)} {ν : ℝ} {hν : 0 < ν} :
    ¬ (pair K ν hν ≤ void) := fun h => h
@[simp] lemma pair_le_pair {K K' : Submodule ℝ (Vec d)} {ν ν' : ℝ} {hν : 0 < ν} {hν' : 0 < ν'} :
    pair K ν hν ≤ pair K' ν' hν' ↔ K' ≤ K ∧ ν ≤ ν' := Iff.rfl

instance : PartialOrder (KComp d) where
  le := KComp.le
  le_refl A := by
    cases A with
    | void => trivial
    | pair K ν hν => exact ⟨le_rfl, le_rfl⟩
  le_trans A B C hAB hBC := by
    cases A with
    | void => trivial
    | pair K ν hν =>
      cases B with
      | void => exact absurd hAB not_pair_le_void
      | pair K' ν' hν' =>
        cases C with
        | void => exact absurd hBC not_pair_le_void
        | pair K'' ν'' hν'' =>
          exact ⟨hBC.1.trans hAB.1, hAB.2.trans hBC.2⟩
  le_antisymm A B hAB hBA := by
    cases A with
    | void => cases B with
      | void => rfl
      | pair K ν hν => exact absurd hBA not_pair_le_void
    | pair K ν hν =>
      cases B with
      | void => exact absurd hAB not_pair_le_void
      | pair K' ν' hν' =>
        obtain ⟨h1, h2⟩ := hAB
        obtain ⟨h3, h4⟩ := hBA
        have hK : K = K' := le_antisymm h3 h1
        have hn : ν = ν' := le_antisymm h2 h4
        subst hK hn
        rfl

/-- Validity of the kernel component for f (Definition G1.1): void, or (K, ν) valid in the
sense of the landed def:kernel-attribute (G3's `KernelValid`, verbatim). -/
def Valid : KComp d → (Vec d → ℝ) → Prop
  | void, _ => True
  | pair K ν _, f => KernelValid f K ν

end KComp

/-- Validity of a curvature component σ ∈ [−∞, ∞) (`WithBot ℝ`): σ = −∞ makes no claim,
a real σ claims C(f, σ). -/
def CurvOK {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (σ : WithBot ℝ) : Prop :=
  ∀ s : ℝ, σ = (s : WithBot ℝ) → ModC f s

/-- Validity of a smoothness component β ∈ [0, ∞] (`ℝ≥0∞`): β = ∞ makes no claim, a finite β
claims that f is β-smooth. -/
def SmoothOK {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (β : ℝ≥0∞) : Prop :=
  β ≠ ⊤ → LipGrad f β.toReal

/-- A smooth declaration (β, σ, A) ∈ 𝒟_S = [0, ∞] × [−∞, ∞) × 𝒦 (Definition G1.1). -/
structure SDecl (d : ℕ) where
  β : ℝ≥0∞
  σ : WithBot ℝ
  A : KComp d

namespace SDecl

/-- Validity of a smooth declaration for f (Definition G1.1; f ∈ C¹ is the standing
assumption on the term, carried as a hypothesis where used). -/
def Valid (δ : SDecl d) (f : Vec d → ℝ) : Prop :=
  SmoothOK f δ.β ∧ CurvOK f δ.σ ∧ δ.A.Valid f

/-- The order on 𝒟_S: the product of β ≥ β' (reverse order on [0, ∞]), σ ≤ σ', and the order
of 𝒦 (Definition G1.2). -/
instance : LE (SDecl d) := ⟨fun δ δ' => δ'.β ≤ δ.β ∧ δ.σ ≤ δ'.σ ∧ δ.A ≤ δ'.A⟩

lemma le_def {δ δ' : SDecl d} : δ ≤ δ' ↔ δ'.β ≤ δ.β ∧ δ.σ ≤ δ'.σ ∧ δ.A ≤ δ'.A := Iff.rfl

/-- **Lemma G1.3(a), smooth sort.** The product order on 𝒟_S is a partial order. -/
instance : PartialOrder (SDecl d) where
  le_refl δ := ⟨le_rfl, le_rfl, le_rfl⟩
  le_trans a b c h1 h2 := ⟨h2.1.trans h1.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
  le_antisymm a b h1 h2 := by
    obtain ⟨β, σ, A⟩ := a
    obtain ⟨β', σ', A'⟩ := b
    have e1 : β = β' := le_antisymm h2.1 h1.1
    have e2 : σ = σ' := le_antisymm h1.2.1 h2.2.1
    have e3 : A = A' := le_antisymm h1.2.2 h2.2.2
    subst e1 e2 e3
    rfl

end SDecl

/-! ### Non-smooth declarations -/

/-- The prox component Π := {oracle} ∪ {explicit(𝒫, κ)}, κ ∈ ℕ (landed def:prox-attribute);
programs range over an arbitrary type `Prog` (the real-RAM programs). -/
inductive ProxAttr (Prog : Type*) where
  | oracle : ProxAttr Prog
  | explicit (P : Prog) (κ : ℕ) : ProxAttr Prog

namespace ProxAttr

variable {Prog : Type*}

/-- oracle ⪯ everything; explicit(𝒫, κ) ⪯ explicit(𝒫', κ') iff 𝒫 = 𝒫' and κ ≥ κ'. -/
def le : ProxAttr Prog → ProxAttr Prog → Prop
  | oracle, _ => True
  | explicit _ _, oracle => False
  | explicit P κ, explicit P' κ' => P = P' ∧ κ' ≤ κ

instance : LE (ProxAttr Prog) := ⟨ProxAttr.le⟩

@[simp] lemma oracle_le (π : ProxAttr Prog) : (oracle : ProxAttr Prog) ≤ π := trivial
@[simp] lemma not_explicit_le_oracle {P : Prog} {κ : ℕ} : ¬ (explicit P κ ≤ oracle) :=
  fun h => h
@[simp] lemma explicit_le_explicit {P P' : Prog} {κ κ' : ℕ} :
    explicit P κ ≤ explicit P' κ' ↔ P = P' ∧ κ' ≤ κ := Iff.rfl

instance : PartialOrder (ProxAttr Prog) where
  le := ProxAttr.le
  le_refl π := by
    cases π with
    | oracle => trivial
    | explicit P κ => exact ⟨rfl, le_rfl⟩
  le_trans a b c h1 h2 := by
    cases a with
    | oracle => trivial
    | explicit P κ =>
      cases b with
      | oracle => exact absurd h1 not_explicit_le_oracle
      | explicit P' κ' =>
        cases c with
        | oracle => exact absurd h2 not_explicit_le_oracle
        | explicit P'' κ'' => exact ⟨h1.1.trans h2.1, h2.2.trans h1.2⟩
  le_antisymm a b h1 h2 := by
    cases a with
    | oracle => cases b with
      | oracle => rfl
      | explicit P κ => exact absurd h2 not_explicit_le_oracle
    | explicit P κ =>
      cases b with
      | oracle => exact absurd h1 not_explicit_le_oracle
      | explicit P' κ' =>
        obtain ⟨rfl, h⟩ := h1
        obtain ⟨-, h'⟩ := h2
        rw [le_antisymm h' h]

/-- **Remark G1.4(b) (S1.7).** Two explicit attributes with different programs have no
common upper bound in Π; so Π (hence 𝒟_N) is not a lattice. -/
theorem no_upper_bound {P P' : Prog} (hP : P ≠ P') (κ κ' : ℕ) :
    ¬ ∃ π : ProxAttr Prog, explicit P κ ≤ π ∧ explicit P' κ' ≤ π := by
  rintro ⟨π, h1, h2⟩
  cases π with
  | oracle => exact not_explicit_le_oracle h1
  | explicit Q μ => exact hP (h1.1.trans h2.1.symm)

end ProxAttr

/-- The semantics of real-RAM programs, abstracted: `computes P g` reads "𝒫, without oracle
calls, is well defined on every (α, x) ∈ (0, ∞) × ℝᵈ and returns prox_{αg}(x)", and
`opCount P α x` is the number of instructions 𝒫 executes on (α, x). Every theorem below
holds for every such semantics. -/
structure ProgSem (d : ℕ) (Prog : Type*) where
  computes : Prog → (Vec d → EReal) → Prop
  opCount : Prog → ℝ → Vec d → ℕ

namespace ProxAttr

variable {Prog : Type*}

/-- Validity of a prox attribute (landed def:prox-attribute): oracle asserts nothing;
explicit(𝒫, κ) asserts that 𝒫 computes the prox and executes at most κ instructions. -/
def Valid (sem : ProgSem d Prog) : ProxAttr Prog → (Vec d → EReal) → Prop
  | oracle, _ => True
  | explicit P κ, g => sem.computes P g ∧ ∀ α > 0, ∀ x, sem.opCount P α x ≤ κ

end ProxAttr

/-- The frame component 𝒲 := {void} ∪ ⋃_{n ≥ 1} ℝ^{n×d} (a matrix with n + 1 ≥ 1 rows). -/
inductive FrameAttr (d : ℕ) where
  | void : FrameAttr d
  | mat (n : ℕ) (W : Matrix (Fin (n + 1)) (Fin d) ℝ) : FrameAttr d

namespace FrameAttr

/-- void ⪯ everything; W ⪯ W' iff W = W'. -/
def le : FrameAttr d → FrameAttr d → Prop
  | void, _ => True
  | mat _ _, void => False
  | W@(mat _ _), W'@(mat _ _) => W = W'

instance : LE (FrameAttr d) := ⟨FrameAttr.le⟩

@[simp] lemma void_le (W : FrameAttr d) : (void : FrameAttr d) ≤ W := trivial
@[simp] lemma not_mat_le_void {n : ℕ} {W : Matrix (Fin (n + 1)) (Fin d) ℝ} :
    ¬ (mat n W ≤ void) := fun h => h
@[simp] lemma mat_le_mat {n n' : ℕ} {W : Matrix (Fin (n + 1)) (Fin d) ℝ}
    {W' : Matrix (Fin (n' + 1)) (Fin d) ℝ} : mat n W ≤ mat n' W' ↔ mat n W = mat n' W' :=
  Iff.rfl

instance : PartialOrder (FrameAttr d) where
  le := FrameAttr.le
  le_refl W := by
    cases W with
    | void => trivial
    | mat n W => exact (rfl : mat n W = mat n W)
  le_trans a b c h1 h2 := by
    cases a with
    | void => trivial
    | mat n W =>
      cases b with
      | void => exact absurd h1 not_mat_le_void
      | mat n' W' =>
        cases c with
        | void => exact absurd h2 not_mat_le_void
        | mat n'' W'' => exact (mat_le_mat.1 h1).trans (mat_le_mat.1 h2)
  le_antisymm a b h1 h2 := by
    cases a with
    | void => cases b with
      | void => rfl
      | mat n W => exact absurd h2 not_mat_le_void
    | mat n W =>
      cases b with
      | void => exact absurd h1 not_mat_le_void
      | mat n' W' => exact mat_le_mat.1 h1

/-- Validity of the frame component: void, or WᵀW = cI_d for some c > 0. -/
def Valid : FrameAttr d → Prop
  | void => True
  | mat _ W => ∃ c : ℝ, 0 < c ∧ W.transpose * W = c • (1 : Matrix (Fin d) (Fin d) ℝ)

end FrameAttr

/-- The curvature claim C(g, σ) for an extended-valued g : ℝᵈ → [−∞, +∞]: g − (σ/2)‖·‖² is
convex, i.e. its epigraph {(x, t) : g(x) − (σ/2)‖x‖² ≤ t} is convex (B&C Def. 8.1). -/
def NModC (g : Vec d → EReal) (σ : ℝ) : Prop :=
  Convex ℝ {p : Vec d × ℝ | g p.1 ≤ ((p.2 + σ / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)}

/-- A non-smooth declaration (σ, π, W) ∈ 𝒟_N = [0, ∞) × Π × 𝒲 (Definition G1.1). -/
structure NDecl (d : ℕ) (Prog : Type*) where
  σ : ℝ≥0
  π : ProxAttr Prog
  W : FrameAttr d

namespace NDecl

variable {Prog : Type*}

/-- Validity of a non-smooth declaration for g (Definition G1.1; g ∈ Γ₀ is the standing
assumption on the term and is not used). -/
def Valid (sem : ProgSem d Prog) (δ : NDecl d Prog) (g : Vec d → EReal) : Prop :=
  NModC g δ.σ ∧ δ.π.Valid sem g ∧ δ.W.Valid

instance : LE (NDecl d Prog) := ⟨fun δ δ' => δ.σ ≤ δ'.σ ∧ δ.π ≤ δ'.π ∧ δ.W ≤ δ'.W⟩

lemma le_def {δ δ' : NDecl d Prog} : δ ≤ δ' ↔ δ.σ ≤ δ'.σ ∧ δ.π ≤ δ'.π ∧ δ.W ≤ δ'.W := Iff.rfl

/-- **Lemma G1.3(a), non-smooth sort.** The product order on 𝒟_N is a partial order. -/
instance : PartialOrder (NDecl d Prog) where
  le_refl δ := ⟨le_rfl, le_rfl, le_rfl⟩
  le_trans a b c h1 h2 := ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
  le_antisymm a b h1 h2 := by
    obtain ⟨σ, π, W⟩ := a
    obtain ⟨σ', π', W'⟩ := b
    have e1 : σ = σ' := le_antisymm h1.1 h2.1
    have e2 : π = π' := le_antisymm h1.2.1 h2.2.1
    have e3 : W = W' := le_antisymm h1.2.2 h2.2.2
    subst e1 e2 e3
    rfl

end NDecl

/-- Declarations of either sort; Mathlib's order on a sum type (declarations of different
sorts are incomparable). -/
abbrev AnyDecl (d : ℕ) (Prog : Type*) := SDecl d ⊕ NDecl d Prog

/-- **Lemma G1.3(a), both sorts.** On each sort ⪯ is reflexive, transitive and antisymmetric,
and it is the product of the component orders of Definition G1.2; declarations of different
sorts are incomparable. -/
theorem decl_order_partial (Prog : Type*) :
    ((∀ δ : SDecl d, δ ≤ δ) ∧ (∀ a b c : SDecl d, a ≤ b → b ≤ c → a ≤ c) ∧
      (∀ a b : SDecl d, a ≤ b → b ≤ a → a = b) ∧
      (∀ a b : SDecl d, a ≤ b ↔ b.β ≤ a.β ∧ a.σ ≤ b.σ ∧ a.A ≤ b.A)) ∧
    ((∀ δ : NDecl d Prog, δ ≤ δ) ∧ (∀ a b c : NDecl d Prog, a ≤ b → b ≤ c → a ≤ c) ∧
      (∀ a b : NDecl d Prog, a ≤ b → b ≤ a → a = b) ∧
      (∀ a b : NDecl d Prog, a ≤ b ↔ a.σ ≤ b.σ ∧ a.π ≤ b.π ∧ a.W ≤ b.W)) ∧
    (∀ (δ : SDecl d) (η : NDecl d Prog),
      ¬ ((Sum.inl δ : AnyDecl d Prog) ≤ Sum.inr η) ∧ ¬ ((Sum.inr η : AnyDecl d Prog) ≤ Sum.inl δ)) :=
  ⟨⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, fun _ _ => Iff.rfl⟩,
   ⟨le_refl, fun _ _ _ => le_trans, fun _ _ => le_antisymm, fun _ _ => Iff.rfl⟩,
   fun _ _ => ⟨Sum.not_inl_le_inr, Sum.not_inr_le_inl⟩⟩

end Declarations

/-! ### Lemma G1.3(b): validity is downward closed -/

section DownwardClosure

variable {d : ℕ}

lemma lipGrad_mono {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {β β' : ℝ} (h : LipGrad f β) (hle : β ≤ β') : LipGrad f β' :=
  fun u v => (h u v).trans (mul_le_mul_of_nonneg_right hle (norm_nonneg _))

lemma convexOn_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] :
    ConvexOn ℝ univ (fun x : E => ‖x‖ ^ 2) := by
  have h : ConvexOn ℝ univ ((fun x : E => ‖x‖) ^ 2) :=
    ConvexOn.pow convexOn_univ_norm (fun x _ => norm_nonneg x) 2
  exact h

/-- C(f, σ') and σ ≤ σ' give C(f, σ) (no differentiability needed). -/
lemma modC_anti {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    {f : E → ℝ} {σ σ' : ℝ} (h : ModC f σ') (hle : σ ≤ σ') : ModC f σ := by
  have hq : ConvexOn ℝ univ (fun x : E => (σ' - σ) / 2 * ‖x‖ ^ 2) := by
    have := (convexOn_norm_sq (E := E)).smul (c := (σ' - σ) / 2) (by linarith)
    simpa only [smul_eq_mul] using this
  have := h.add hq
  have e : (fun x => f x - σ / 2 * ‖x‖ ^ 2)
      = ((fun x => f x - σ' / 2 * ‖x‖ ^ 2) + fun x => (σ' - σ) / 2 * ‖x‖ ^ 2) := by
    funext x; simp only [Pi.add_apply]; ring
  unfold ModC
  rw [e]; exact this

lemma norm_perp_anti {K K' : Submodule ℝ (Vec d)} (h : K' ≤ K) (v : Vec d) :
    ‖Kᗮ.starProjection v‖ ≤ ‖K'ᗮ.starProjection v‖ := by
  have hle : Kᗮ ≤ K'ᗮ := Submodule.orthogonal_le h
  have e : Kᗮ.starProjection (K'ᗮ.starProjection v) = Kᗮ.starProjection v := by
    have := Submodule.starProjection_comp_starProjection_of_le hle
    exact congrArg (fun T : Vec d →L[ℝ] Vec d => T v) this
  rw [← e]
  exact Submodule.norm_starProjection_apply_le _ _

lemma kernelValid_anti {f : Vec d → ℝ} {K K' : Submodule ℝ (Vec d)} {ν ν' : ℝ}
    (h : KernelValid f K' ν') (hK : K' ≤ K) (hν0 : 0 ≤ ν) (hν : ν ≤ ν') :
    KernelValid f K ν := by
  intro x y
  have h1 := norm_perp_anti hK (x - y)
  have h2 : ‖Kᗮ.starProjection (x - y)‖ ^ 2 ≤ ‖K'ᗮ.starProjection (x - y)‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  calc ν * ‖Kᗮ.starProjection (x - y)‖ ^ 2 ≤ ν' * ‖K'ᗮ.starProjection (x - y)‖ ^ 2 :=
        mul_le_mul hν h2 (sq_nonneg _) (hν0.trans hν)
    _ ≤ _ := h x y

lemma KComp.valid_of_le {f : Vec d → ℝ} {A A' : KComp d} (h : A ≤ A') (hv : A'.Valid f) :
    A.Valid f := by
  cases A with
  | void => trivial
  | pair K ν hν =>
    cases A' with
    | void => exact absurd h KComp.not_pair_le_void
    | pair K' ν' hν' => exact kernelValid_anti hv h.1 hν.le h.2

/-- **Lemma G1.3(b), smooth sort.** If δ' is valid for f and δ ⪯ δ', then δ is valid for f. -/
theorem SDecl.valid_of_le {f : Vec d → ℝ} {δ δ' : SDecl d} (h : δ ≤ δ') (hv : δ'.Valid f) :
    δ.Valid f := by
  obtain ⟨hβ, hσ, hA⟩ := hv
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨fun hne => ?_, fun s hs => ?_, KComp.valid_of_le h3 hA⟩
  · have hne' : δ'.β ≠ ⊤ := ne_top_of_le_ne_top hne h1
    exact lipGrad_mono (hβ hne') ((ENNReal.toReal_le_toReal hne' hne).2 h1)
  · rw [hs] at h2
    obtain ⟨s', hs', hss'⟩ := WithBot.coe_le_iff.1 h2
    exact modC_anti (hσ s' hs') hss'

/-- C(g, σ') and σ ≤ σ' give C(g, σ) for extended-valued g (epigraph form). -/
lemma nmodC_anti {g : Vec d → EReal} {σ σ' : ℝ} (h : NModC g σ') (hle : σ ≤ σ') :
    NModC g σ := by
  intro p hp q hq a b ha hb hab
  have hp' : ((p.1, p.2 + (σ - σ') / 2 * ‖p.1‖ ^ 2) : Vec d × ℝ) ∈
      {p : Vec d × ℝ | g p.1 ≤ ((p.2 + σ' / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)} := by
    have e : p.2 + (σ - σ') / 2 * ‖p.1‖ ^ 2 + σ' / 2 * ‖p.1‖ ^ 2 = p.2 + σ / 2 * ‖p.1‖ ^ 2 := by
      ring
    simp only [mem_setOf_eq] at hp ⊢
    rw [e]; exact hp
  have hq' : ((q.1, q.2 + (σ - σ') / 2 * ‖q.1‖ ^ 2) : Vec d × ℝ) ∈
      {p : Vec d × ℝ | g p.1 ≤ ((p.2 + σ' / 2 * ‖p.1‖ ^ 2 : ℝ) : EReal)} := by
    have e : q.2 + (σ - σ') / 2 * ‖q.1‖ ^ 2 + σ' / 2 * ‖q.1‖ ^ 2 = q.2 + σ / 2 * ‖q.1‖ ^ 2 := by
      ring
    simp only [mem_setOf_eq] at hq ⊢
    rw [e]; exact hq
  have hc := h hp' hq' ha hb hab
  simp only [mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul] at hc ⊢
  refine hc.trans (EReal.coe_le_coe_iff.2 ?_)
  have key : ‖a • p.1 + b • q.1‖ ^ 2 ≤ a * ‖p.1‖ ^ 2 + b * ‖q.1‖ ^ 2 := by
    have := convexOn_norm_sq.2 (mem_univ p.1) (mem_univ q.1) ha hb hab
    simpa [smul_eq_mul] using this
  have := mul_le_mul_of_nonneg_left key (sub_nonneg.2 hle)
  nlinarith

lemma ProxAttr.valid_of_le {Prog : Type*} {sem : ProgSem d Prog} {g : Vec d → EReal}
    {π π' : ProxAttr Prog} (h : π ≤ π') (hv : π'.Valid sem g) : π.Valid sem g := by
  cases π with
  | oracle => trivial
  | explicit P κ =>
    cases π' with
    | oracle => exact absurd h ProxAttr.not_explicit_le_oracle
    | explicit P' κ' =>
      obtain ⟨rfl, hκ⟩ := h
      exact ⟨hv.1, fun α hα x => (hv.2 α hα x).trans hκ⟩

lemma FrameAttr.valid_of_le {W W' : FrameAttr d} (h : W ≤ W') (hv : W'.Valid) : W.Valid := by
  cases W with
  | void => trivial
  | mat n M =>
    cases W' with
    | void => exact absurd h FrameAttr.not_mat_le_void
    | mat n' M' =>
      have e := FrameAttr.mat_le_mat.1 h
      rw [e]; exact hv

/-- **Lemma G1.3(b), non-smooth sort.** If δ' is valid for g and δ ⪯ δ', then δ is valid for
g (for every program semantics). -/
theorem NDecl.valid_of_le {Prog : Type*} {sem : ProgSem d Prog} {g : Vec d → EReal}
    {δ δ' : NDecl d Prog} (h : δ ≤ δ') (hv : δ'.Valid sem g) : δ.Valid sem g :=
  ⟨nmodC_anti hv.1 (by exact_mod_cast h.1), ProxAttr.valid_of_le h.2.1 hv.2.1,
    FrameAttr.valid_of_le h.2.2 hv.2.2⟩

end DownwardClosure

/-! ### Lemma G1.3(c): saturation -/

section Saturation

variable {d : ℕ}

lemma starProjection_orth_bot (v : Vec d) : (⊥ : Submodule ℝ (Vec d))ᗮ.starProjection v = v := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_bot]
  simp

lemma starProjection_orth_top (v : Vec d) : (⊤ : Submodule ℝ (Vec d))ᗮ.starProjection v = 0 := by
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_top]
  simp

/-- **Lemma G1.3(c)(i).** A valid kernel attribute gives C(f, 0). -/
theorem sat_i {f : Vec d → ℝ} (hf : Differentiable ℝ f) {K : Submodule ℝ (Vec d)} {ν : ℝ}
    (hν : 0 < ν) (h : KernelValid f K ν) : ModC f 0 := by
  rw [modC_iff_strongMono hf]
  intro x y
  have := h x y
  have : 0 ≤ ν * ‖Kᗮ.starProjection (x - y)‖ ^ 2 := by positivity
  simp only [zero_mul]
  linarith

/-- **Lemma G1.3(c)(ii).** C(f, σ) with σ ≥ 0 makes (ℝᵈ, ν) valid for every ν > 0. -/
theorem sat_ii {f : Vec d → ℝ} (hf : Differentiable ℝ f) {σ : ℝ} (hσ : 0 ≤ σ)
    (h : ModC f σ) (ν : ℝ) : KernelValid f ⊤ ν := by
  rw [modC_iff_strongMono hf] at h
  intro x y
  rw [starProjection_orth_top, norm_zero]
  have := h x y
  have : 0 ≤ σ * ‖x - y‖ ^ 2 := by positivity
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  linarith

/-- **Lemma G1.3(c)(iii).** For σ > 0, C(f, σ) holds iff ({0}, σ) is valid. -/
theorem sat_iii {f : Vec d → ℝ} (hf : Differentiable ℝ f) (σ : ℝ) :
    ModC f σ ↔ KernelValid f ⊥ σ := by
  rw [modC_iff_strongMono hf]
  unfold StrongMono KernelValid
  simp only [starProjection_orth_bot]

end Saturation

/-! ## §2. Spectral toolkit: λ_min, λ_max, λ⁺ of a symmetric operator on ℝᵈ -/

section Spectral

variable {d : ℕ}

/-- The eigenvalues (with multiplicity, Mathlib's ordering) of a symmetric operator on ℝᵈ;
0 by convention for a non-symmetric operator (never used). -/
noncomputable def opEv (M : Vec d →L[ℝ] Vec d) : Fin d → ℝ := by
  classical
  exact if h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric then h.eigenvalues finrank_euclideanSpace_fin
    else 0

/-- λ_min(M): the smallest eigenvalue. -/
noncomputable def opLamMin (M : Vec d →L[ℝ] Vec d) : ℝ := ⨅ j, opEv M j

/-- λ_max(M): the largest eigenvalue. -/
noncomputable def opLamMax (M : Vec d →L[ℝ] Vec d) : ℝ := ⨆ j, opEv M j

/-- λ⁺(M): the smallest nonzero eigenvalue (dossier §0, for a nonzero PSD M). -/
noncomputable def opLamPlus (M : Vec d →L[ℝ] Vec d) : ℝ :=
  sInf {μ : ℝ | ∃ j, opEv M j = μ ∧ μ ≠ 0}

/-- The eigenvector basis of a symmetric operator. -/
noncomputable abbrev eb {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric) :
    OrthonormalBasis (Fin d) ℝ (Vec d) :=
  h.eigenvectorBasis finrank_euclideanSpace_fin

lemma opEv_eq {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric) :
    opEv M = h.eigenvalues finrank_euclideanSpace_fin := by
  simp only [opEv, dif_pos h]

lemma apply_eb {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric) (j : Fin d) :
    M (eb h j) = opEv M j • eb h j := by
  have := h.apply_eigenvectorBasis finrank_euclideanSpace_fin j
  rw [opEv_eq h]
  simpa only [ContinuousLinearMap.coe_coe, RCLike.ofReal_real_eq_id, id] using this

lemma inner_apply_eb {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (x : Vec d) (j : Fin d) :
    inner ℝ (M x) (eb h j) = opEv M j * inner ℝ (eb h j) x := by
  have hs := h x (eb h j)
  simp only [ContinuousLinearMap.coe_coe] at hs
  rw [hs, apply_eb h, real_inner_smul_right, real_inner_comm]

/-- Spectral expansion: ⟨Mx, x⟩ = Σⱼ λⱼ⟨eⱼ, x⟩². -/
lemma inner_self_expand {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (x : Vec d) : inner ℝ (M x) x = ∑ j, opEv M j * inner ℝ (eb h j) x ^ 2 := by
  rw [← (eb h).sum_inner_mul_inner (M x) x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_apply_eb h]; ring

/-- Parseval: ‖x‖² = Σⱼ⟨eⱼ, x⟩². -/
lemma norm_sq_expand {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (x : Vec d) : ‖x‖ ^ 2 = ∑ j, inner ℝ (eb h j) x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← (eb h).sum_inner_mul_inner x x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm x]; ring

lemma opLamMin_le_ev (M : Vec d →L[ℝ] Vec d) (j : Fin d) : opLamMin M ≤ opEv M j :=
  ciInf_le (Set.finite_range _).bddBelow j

lemma ev_le_opLamMax (M : Vec d →L[ℝ] Vec d) (j : Fin d) : opEv M j ≤ opLamMax M :=
  le_ciSup (Set.finite_range _).bddAbove j

/-- Rayleigh: λ_min(M)‖x‖² ≤ ⟨Mx, x⟩ (Boyd–Vandenberghe §A.5.2). -/
theorem opLamMin_mul_le {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (x : Vec d) : opLamMin M * ‖x‖ ^ 2 ≤ inner ℝ (M x) x := by
  rw [inner_self_expand h, norm_sq_expand h, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (opLamMin_le_ev M j) (sq_nonneg _)

/-- Rayleigh: ⟨Mx, x⟩ ≤ λ_max(M)‖x‖². -/
theorem le_opLamMax_mul {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (x : Vec d) : inner ℝ (M x) x ≤ opLamMax M * ‖x‖ ^ 2 := by
  rw [inner_self_expand h, norm_sq_expand h, Finset.mul_sum]
  exact Finset.sum_le_sum fun j _ =>
    mul_le_mul_of_nonneg_right (ev_le_opLamMax M j) (sq_nonneg _)

lemma ev_eq_inner {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (j : Fin d) : opEv M j = inner ℝ (M (eb h j)) (eb h j) := by
  rw [apply_eb h, real_inner_smul_left, real_inner_self_eq_norm_sq,
    (eb h).orthonormal.1 j]
  ring

lemma ev_nonneg {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hpsd : ∀ x, 0 ≤ inner ℝ (M x) x) (j : Fin d) : 0 ≤ opEv M j := by
  rw [ev_eq_inner h]; exact hpsd _

lemma opLamPlus_nonneg {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hpsd : ∀ x, 0 ≤ inner ℝ (M x) x) : 0 ≤ opLamPlus M :=
  Real.sInf_nonneg (by rintro μ ⟨j, rfl, -⟩; exact ev_nonneg h hpsd j)

lemma opLamPlus_le_ev (M : Vec d →L[ℝ] Vec d) {j : Fin d} (hj : opEv M j ≠ 0) :
    opLamPlus M ≤ opEv M j := by
  apply csInf_le
  · exact ((Set.finite_range (opEv M)).subset
      (by rintro μ ⟨i, rfl, -⟩; exact ⟨i, rfl⟩)).bddBelow
  · exact ⟨j, rfl, hj⟩

/-- **Rayleigh bound for λ⁺** (landed rem:kernel-attribute(iii) for ½xᵀMx; Boyd–Vandenberghe
§A.5.2): for symmetric PSD M, ⟨Mx, x⟩ ≥ λ⁺(M)‖P_{(ker M)⊥}x‖². -/
theorem opLamPlus_mul_le {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hpsd : ∀ x, 0 ≤ inner ℝ (M x) x) (x : Vec d) :
    opLamPlus M * ‖(LinearMap.ker (M : Vec d →ₗ[ℝ] Vec d))ᗮ.starProjection x‖ ^ 2
      ≤ inner ℝ (M x) x := by
  classical
  set e := eb h with he
  set K := LinearMap.ker (M : Vec d →ₗ[ℝ] Vec d) with hK
  set c : Fin d → ℝ := fun j => inner ℝ (e j) x with hc
  set g : Fin d → ℝ := fun j => if opEv M j = 0 then 0 else c j with hg
  set y : Vec d := ∑ j, (if opEv M j = 0 then c j else 0) • e j with hy
  have hyK : y ∈ K := by
    rw [hK, LinearMap.mem_ker, hy, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [map_smul, ContinuousLinearMap.coe_coe, he, apply_eb h]
    by_cases hj : opEv M j = 0
    · rw [hj, zero_smul, smul_zero]
    · rw [if_neg hj, zero_smul]
  have hxy : x - y = ∑ j, g j • e j := by
    conv_lhs => rw [← e.sum_repr' x]
    rw [hy, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul]
    congr 1
    by_cases hj : opEv M j = 0 <;> simp [hg, hc, hj]
  have hcoef : ∀ k, inner ℝ (e k) (x - y) = g k := by
    intro k
    rw [hxy]
    exact e.orthonormal.inner_right_fintype g k
  have hnorm : ‖x - y‖ ^ 2 = ∑ j, g j ^ 2 := by
    rw [norm_sq_expand h (x - y)]
    exact Finset.sum_congr rfl fun j _ => by rw [← he, hcoef j]
  have hP : ‖Kᗮ.starProjection x‖ ≤ ‖x - y‖ := by
    rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_minimal]
    exact ciInf_le ⟨0, by rintro _ ⟨z, rfl⟩; exact norm_nonneg _⟩ (⟨y, hyK⟩ : K)
  have hl0 := opLamPlus_nonneg h hpsd
  calc opLamPlus M * ‖Kᗮ.starProjection x‖ ^ 2 ≤ opLamPlus M * ‖x - y‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hP 2) hl0
    _ = ∑ j, opLamPlus M * g j ^ 2 := by rw [hnorm, Finset.mul_sum]
    _ ≤ ∑ j, opEv M j * c j ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hj : opEv M j = 0
        · simp [hg, hj]
        · simp only [hg, if_neg hj]
          exact mul_le_mul_of_nonneg_right (opLamPlus_le_ev M hj) (sq_nonneg _)
    _ = inner ℝ (M x) x := (inner_self_expand h x).symm

/-- For a nonzero symmetric PSD M, λ⁺(M) > 0. -/
theorem opLamPlus_pos {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hpsd : ∀ x, 0 ≤ inner ℝ (M x) x) (hM : M ≠ 0) : 0 < opLamPlus M := by
  have hex : ∃ j, opEv M j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hM
    ext1 x
    rw [← (eb h).sum_repr' x, map_sum]
    simp only [map_smul, apply_eb h, hall, zero_smul, smul_zero, Finset.sum_const_zero,
      zero_apply]
  obtain ⟨j, hj⟩ := hex
  have hne : {μ : ℝ | ∃ j, opEv M j = μ ∧ μ ≠ 0}.Nonempty := ⟨_, j, rfl, hj⟩
  have hfin : {μ : ℝ | ∃ j, opEv M j = μ ∧ μ ≠ 0}.Finite :=
    (Set.finite_range (opEv M)).subset (by rintro μ ⟨i, rfl, -⟩; exact ⟨i, rfl⟩)
  obtain ⟨k, hk, hk0⟩ := hne.csInf_mem hfin
  have e : opLamPlus M = opEv M k := hk.symm
  have hk0' : opEv M k ≠ 0 := by rw [← e]; exact hk0
  rw [e]
  exact lt_of_le_of_ne (ev_nonneg h hpsd k) (Ne.symm hk0')

end Spectral

/-! ## §3. R-sum (Lemma G2.1; draft lem:rule-sum (a)–(c)) -/

section RuleSum

variable {d n : ℕ}

/-- F = Σᵢ wᵢfᵢ (pointwise; definitionally G3's `Decl.energy`). -/
noncomputable def sumF (w : Fin n → ℝ) (f : Fin n → Vec d → ℝ) : Vec d → ℝ :=
  fun x => ∑ i, w i * f i x

/-- β̂ = Σᵢ wᵢβᵢ in [0, ∞] (∞ if some βᵢ = ∞, as wᵢ > 0). -/
noncomputable def betaHatX (w : Fin n → ℝ) (δ : Fin n → SDecl d) : ℝ≥0∞ :=
  ∑ i, ENNReal.ofReal (w i) * (δ i).β

/-- σ̂_S = Σᵢ wᵢσᵢ in [−∞, ∞) (−∞ if some σᵢ = −∞): the dominance file's `extSum`. -/
noncomputable def sigmaHatX (w : Fin n → ℝ) (δ : Fin n → SDecl d) : WithBot ℝ :=
  extSum Finset.univ w (fun i => (δ i).σ)

lemma differentiable_of_C1 {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} (hf : ContDiff ℝ 1 f) :
    Differentiable ℝ f :=
  hf.differentiable one_ne_zero

lemma contDiff_sumF (w : Fin n → ℝ) {f : Fin n → Vec d → ℝ} (hf : ∀ i, ContDiff ℝ 1 (f i)) :
    ContDiff ℝ 1 (sumF w f) := by
  unfold sumF
  exact ContDiff.sum fun i _ => contDiff_const.mul (hf i)

lemma inner_gradient_sumF (w : Fin n → ℝ) {f : Fin n → Vec d → ℝ}
    (hf : ∀ i, Differentiable ℝ (f i)) (x y : Vec d) :
    inner ℝ (gradient (sumF w f) x - gradient (sumF w f) y) (x - y)
      = ∑ i, w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y) := by
  unfold sumF
  rw [OCF.gradient_weighted_sum f w hf x, OCF.gradient_weighted_sum f w hf y,
    Finset.sum_apply, Finset.sum_apply, ← Finset.sum_sub_distrib, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply]
  rw [← smul_sub, real_inner_smul_left]

lemma strongMono_of_dim_zero (hd : d = 0) (f : Vec d → ℝ) (σ : ℝ) : StrongMono f σ := by
  subst hd
  intro x y
  have : x - y = 0 := Subsingleton.elim _ _
  simp [this]

/-- The aux G3 declaration used to cite `OCF.G3.Decl.betaHat_valid`: weights w, the finite
βᵢ, σᵢ := −βᵢ (valid by `modC_neg_of_lipGrad`), no kernel attributes. -/
noncomputable def auxDecl (w : Fin n → ℝ) (β : Fin n → ℝ) : G3.Decl d n where
  w := w
  β := β
  σ := fun i => -β i
  SK := ∅
  K := fun _ => ⊥
  ν := fun _ => 1
  kdim := fun _ => 0
  basis := fun _ => Fin.elim0

/-- **R-sum (a)** (draft lem:rule-sum(a), G2.1(a)): F ∈ C¹ and (β̂, σ̂_S, void) is valid for
F = Σ wᵢfᵢ. The β̂ part is G3's `Decl.betaHat_valid`. -/
theorem rule_sum_a (f : Fin n → Vec d → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (δ : Fin n → SDecl d) (hv : ∀ i, (δ i).Valid (f i)) :
    ContDiff ℝ 1 (sumF w f) ∧
      (⟨betaHatX w δ, sigmaHatX w δ, KComp.void⟩ : SDecl d).Valid (sumF w f) := by
  have hdiff : ∀ i, Differentiable ℝ (f i) := fun i => differentiable_of_C1 (hf i)
  refine ⟨contDiff_sumF w hf, ?_, ?_, trivial⟩
  · -- β̂
    intro hne
    have hfin : ∀ i, (δ i).β ≠ ⊤ := by
      intro i hi
      apply hne
      rw [betaHatX, ENNReal.sum_eq_top]
      exact ⟨i, Finset.mem_univ _, ENNReal.mul_eq_top.2
        (Or.inl ⟨by simpa using hw i, hi⟩)⟩
    set D : G3.Decl d n := auxDecl w (fun i => (δ i).β.toReal)
    have hD : D.Valid f :=
      { w_pos := hw
        β_nonneg := fun i => ENNReal.toReal_nonneg
        diff := hdiff
        smooth := fun i => (hv i).1 (hfin i)
        curv := fun i => G3.modC_neg_of_lipGrad (hdiff i) ((hv i).1 (hfin i))
        ν_pos := by simp [D, auxDecl]
        basis_orth := by simp [D, auxDecl]
        basis_span := by simp [D, auxDecl]
        kernel := by simp [D, auxDecl] }
    have hL := D.betaHat_valid hD
    have he : (betaHatX w δ).toReal = D.betaHat := by
      rw [betaHatX, ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (hfin i))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hw i).le]
      rfl
    rw [he]
    exact hL
  · -- σ̂_S
    intro s hs
    change sigmaHatX w δ = ↑s at hs
    have hne : sigmaHatX w δ ≠ ⊥ := by rw [hs]; exact WithBot.coe_ne_bot
    have hall := extSum_fin_of_ne_bot hne
    rw [sigmaHatX, extSum_of_fin hall] at hs
    have hs' : s = ∑ i, w i * ((δ i).σ).unbotD 0 := (WithBot.coe_injective hs).symm
    rw [modC_iff_strongMono (differentiable_of_C1 (contDiff_sumF w hf))]
    intro x y
    rw [inner_gradient_sumF w hdiff, hs', Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    obtain ⟨t, ht⟩ := WithBot.ne_bot_iff_exists.1 (hall i (Finset.mem_univ _))
    have hmc := (hv i).2.1 t ht.symm
    rw [modC_iff_strongMono (hdiff i)] at hmc
    rw [← ht, WithBot.unbotD_coe, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hmc x y) (hw i).le

/-! ### Δ_w(T), b(T), σ_𝔈^T for declarations with subspace kernel components -/

/-- The subspace of a kernel component (ℝᵈ for void; only read on S_K). -/
def KComp.sub : KComp d → Submodule ℝ (Vec d)
  | .void => ⊤
  | .pair K _ _ => K

/-- The gap of a kernel component (0 for void; only read on S_K). -/
def KComp.nu : KComp d → ℝ
  | .void => 0
  | .pair _ ν _ => ν

lemma KComp.valid_pair {f : Vec d → ℝ} {A : KComp d} (hA : A ≠ .void) (hv : A.Valid f) :
    0 < A.nu ∧ KernelValid f A.sub A.nu := by
  cases A with
  | void => exact absurd rfl hA
  | pair K ν hν => exact ⟨hν, hv⟩

/-- An orthonormal basis of a subspace, as vectors of ℝᵈ (Mathlib's `stdOrthonormalBasis`). -/
noncomputable def kb (K : Submodule ℝ (Vec d)) : Fin (Module.finrank ℝ K) → Vec d :=
  fun p => ((stdOrthonormalBasis ℝ K) p : Vec d)

lemma kb_orth (K : Submodule ℝ (Vec d)) : Orthonormal ℝ (kb K) :=
  (stdOrthonormalBasis ℝ K).orthonormal.comp_linearIsometry K.subtypeₗᵢ

lemma kb_span (K : Submodule ℝ (Vec d)) : Submodule.span ℝ (Set.range (kb K)) = K := by
  have e : Set.range (kb K) = K.subtype '' Set.range (stdOrthonormalBasis ℝ K) := by
    rw [← Set.range_comp]; rfl
  have hs : Submodule.span ℝ (Set.range (stdOrthonormalBasis ℝ K)) = ⊤ := by
    simpa using (stdOrthonormalBasis ℝ K).toBasis.span_eq
  rw [e, Submodule.span_image K.subtype, hs, Submodule.map_subtype_top]

/-- S_K: the indices whose declaration carries a kernel attribute. -/
noncomputable def SKX (δ : Fin n → SDecl d) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun i => (δ i).A ≠ KComp.void

lemma mem_SKX {δ : Fin n → SDecl d} {i : Fin n} : i ∈ SKX δ ↔ (δ i).A ≠ KComp.void := by
  classical
  unfold SKX
  simp

/-- Δ_w(T): the transversality defect of the Kernel Gram certificate of (Kᵢ, wᵢνᵢ)_{i∈T}
(T1SharpBound's `deltaW`, T enumerated by G3's `tIdx`, Kᵢ by an orthonormal basis; it does
not depend on either choice, `deltaW_isGreatest`). Δ_w(∅) = 0 (`G3.deltaW_card_zero`). -/
noncomputable def deltaWX (w : Fin n → ℝ) (δ : Fin n → SDecl d) (T : Finset (Fin n)) : ℝ :=
  OCF.deltaW (k := fun j => Module.finrank ℝ ((δ (G3.Decl.tIdx T j)).A.sub))
    (fun j p => (kb ((δ (G3.Decl.tIdx T j)).A.sub) p).ofLp)
    (fun j => w (G3.Decl.tIdx T j) * (δ (G3.Decl.tIdx T j)).A.nu)

/-- b(T) = Δ_w(T) + Σ_{i∉T} wᵢσᵢ in [−∞, ∞). -/
noncomputable def bX (w : Fin n → ℝ) (δ : Fin n → SDecl d) (T : Finset (Fin n)) : WithBot ℝ :=
  ((deltaWX w δ T : ℝ) : WithBot ℝ) + extSum Tᶜ w (fun i => (δ i).σ)

/-- σ_𝔈^T = max{σ̂_S, b(T)}. -/
noncomputable def sigmaTX (w : Fin n → ℝ) (δ : Fin n → SDecl d) (T : Finset (Fin n)) :
    WithBot ℝ :=
  max (sigmaHatX w δ) (bX w δ T)

/-- σ_𝔈 of the landed rem:fb-spec: max{σ̂_S, Δ_w} if S_K = S, σ̂_S otherwise. -/
noncomputable def sigmaEX (w : Fin n → ℝ) (δ : Fin n → SDecl d) : WithBot ℝ := by
  classical
  exact if SKX δ = Finset.univ then max (sigmaHatX w δ) ((deltaWX w δ Finset.univ : ℝ) : WithBot ℝ)
    else sigmaHatX w δ

/-- The T-part: Δ_w(T)‖x − y‖² ≤ Σ_{i∈T} wᵢ⟨∇fᵢx − ∇fᵢy, x − y⟩ (B1p Theorem (a) on T;
G3's `strongMono_T` with subspace kernel components). -/
lemma strongMono_T_X (hd : 0 < d) {f : Fin n → Vec d → ℝ}
    {w : Fin n → ℝ} (hw : ∀ i, 0 < w i) {δ : Fin n → SDecl d} (hv : ∀ i, (δ i).Valid (f i))
    {T : Finset (Fin n)} (hT : T ⊆ SKX δ) (x y : Vec d) :
    deltaWX w δ T * ‖x - y‖ ^ 2
      ≤ ∑ i ∈ T, w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y) := by
  have hpair : ∀ j, 0 < (δ (G3.Decl.tIdx T j)).A.nu ∧
      KernelValid (f (G3.Decl.tIdx T j)) (δ (G3.Decl.tIdx T j)).A.sub
        (δ (G3.Decl.tIdx T j)).A.nu := fun j =>
    KComp.valid_pair (mem_SKX.1 (hT (G3.tIdx_mem T j))) (hv _).2.2
  rcases Nat.eq_zero_or_pos T.card with h0 | hpos
  · rw [deltaWX, G3.deltaW_card_zero h0, zero_mul, Finset.card_eq_zero.1 h0, Finset.sum_empty]
  · have hm := OCF.uniform_composite_gap_of_restricted_monotone hpos hd
      (fun j => gradient (f (G3.Decl.tIdx T j))) (fun j => w (G3.Decl.tIdx T j))
      (fun j => hw _) (fun j => (δ (G3.Decl.tIdx T j)).A.sub)
      (fun j => (δ (G3.Decl.tIdx T j)).A.nu) (fun j => (hpair j).1)
      (fun j x y => (hpair j).2 x y)
      (k := fun j => Module.finrank ℝ ((δ (G3.Decl.tIdx T j)).A.sub))
      (fun j => kb ((δ (G3.Decl.tIdx T j)).A.sub))
      (fun j => kb_orth _) (fun j => kb_span _) x y
    have hexp : inner ℝ ((∑ j, w (G3.Decl.tIdx T j) • (fun j => gradient (f (G3.Decl.tIdx T j))) j) x
        - (∑ j, w (G3.Decl.tIdx T j) • (fun j => gradient (f (G3.Decl.tIdx T j))) j) y) (x - y)
        = ∑ j : Fin T.card, w (G3.Decl.tIdx T j)
            * inner ℝ (gradient (f (G3.Decl.tIdx T j)) x
              - gradient (f (G3.Decl.tIdx T j)) y) (x - y) := by
      simp only [Finset.sum_apply, Pi.smul_apply, ← Finset.sum_sub_distrib, ← smul_sub,
        sum_inner, real_inner_smul_left]
    rw [hexp, G3.sum_tIdx T
      (fun i => w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y))] at hm
    exact hm

/-- **R-sum (b), subset bound** (draft lem:rule-sum(b), G2.1(d)): C(F, b(T)) holds for every
T ⊆ S_K, and (β̂, σ_𝔈^T, void) is valid for F. No dimension hypothesis (d = 0 is trivial). -/
theorem rule_sum_b (f : Fin n → Vec d → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (δ : Fin n → SDecl d) (hv : ∀ i, (δ i).Valid (f i))
    {T : Finset (Fin n)} (hT : T ⊆ SKX δ) :
    CurvOK (sumF w f) (bX w δ T) ∧
      (⟨betaHatX w δ, sigmaTX w δ T, KComp.void⟩ : SDecl d).Valid (sumF w f) := by
  have hdiff : ∀ i, Differentiable ℝ (f i) := fun i => differentiable_of_C1 (hf i)
  have hF := differentiable_of_C1 (contDiff_sumF w hf)
  have ha := rule_sum_a f hf w hw δ hv
  have hb : CurvOK (sumF w f) (bX w δ T) := by
    intro s hs
    by_cases hbot : extSum Tᶜ w (fun i => (δ i).σ) = ⊥
    · rw [bX, hbot, WithBot.add_bot] at hs
      exact absurd hs.symm WithBot.coe_ne_bot
    have hall := extSum_fin_of_ne_bot hbot
    rw [bX, extSum_of_fin hall] at hs
    have hs' : s = deltaWX w δ T + ∑ i ∈ Tᶜ, w i * ((δ i).σ).unbotD 0 := by
      have := hs.symm
      rw [← WithBot.coe_add] at this
      exact WithBot.coe_injective this
    rw [modC_iff_strongMono hF]
    intro x y
    rcases Nat.eq_zero_or_pos d with hd0 | hd
    · exact strongMono_of_dim_zero hd0 _ _ x y
    rw [inner_gradient_sumF w hdiff, ← Finset.sum_add_sum_compl T, hs', add_mul,
      Finset.sum_mul]
    have h1 := strongMono_T_X hd hw hv hT x y
    have h2 : ∑ i ∈ Tᶜ, w i * ((δ i).σ).unbotD 0 * ‖x - y‖ ^ 2
        ≤ ∑ i ∈ Tᶜ, w i * inner ℝ (gradient (f i) x - gradient (f i) y) (x - y) := by
      refine Finset.sum_le_sum fun i hi => ?_
      obtain ⟨t, ht⟩ := WithBot.ne_bot_iff_exists.1 (hall i hi)
      have hmc := (hv i).2.1 t ht.symm
      rw [modC_iff_strongMono (hdiff i)] at hmc
      rw [← ht, WithBot.unbotD_coe, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hmc x y) (hw i).le
    linarith
  refine ⟨hb, ha.2.1, ?_, trivial⟩
  intro s hs
  rcases max_choice (sigmaHatX w δ) (bX w δ T) with h | h
  · rw [sigmaTX, h] at hs; exact ha.2.2.1 s hs
  · rw [sigmaTX, h] at hs; exact hb s hs

/-- **R-sum (b), comparison** (draft lem:rule-sum(b), last clause): σ_𝔈^{S_K} ≥ σ_𝔈, with
equality if S_K = S. -/
theorem rule_sum_b_compare (w : Fin n → ℝ) (δ : Fin n → SDecl d) :
    sigmaEX w δ ≤ sigmaTX w δ (SKX δ) ∧
      (SKX δ = Finset.univ → sigmaEX w δ = sigmaTX w δ (SKX δ)) := by
  classical
  have heq : SKX δ = Finset.univ → sigmaEX w δ = sigmaTX w δ (SKX δ) := by
    intro h
    have e0 : extSum (Finset.univᶜ : Finset (Fin n)) w (fun i => (δ i).σ) = ((0 : ℝ) : WithBot ℝ) := by
      rw [Finset.compl_univ, extSum_of_fin (by simp)]
      simp
    simp only [sigmaEX, sigmaTX, bX, h, if_true, e0, ← WithBot.coe_add, add_zero]
  refine ⟨?_, heq⟩
  by_cases h : SKX δ = Finset.univ
  · exact (heq h).le
  · simp only [sigmaEX, if_neg h, sigmaTX]
    exact le_max_left _ _

/-- G3's form of R-sum (b) (cited, finite βᵢ and real σᵢ): `OCF.G3.Decl.sigmaT_valid`. -/
theorem rule_sum_b_G3 (hd : 0 < d) (D : G3.Decl d n) {f : Fin n → Vec d → ℝ}
    (hv : D.Valid f) {T : Finset (Fin n)} (hT : T ⊆ D.SK) :
    ModC (D.energy f) (D.sigmaT T) :=
  D.sigmaT_valid hd hv hT

/-! ### R-sum (c): the kernel attribute of the sum -/

lemma inner_starProj_self (K : Submodule ℝ (Vec d)) (v : Vec d) :
    inner ℝ (K.starProjection v) v = ‖K.starProjection v‖ ^ 2 := by
  have hidem : K.starProjection (K.starProjection v) = K.starProjection v :=
    Submodule.starProjection_eq_self_iff.2 (K.starProjection_apply_mem v)
  rw [← real_inner_self_eq_norm_sq]
  conv_rhs => rw [Submodule.inner_starProjection_left_eq_right, hidem]
  rw [real_inner_comm]

/-- Q := Σᵢ wᵢνᵢP_{Kᵢ⊥}. -/
noncomputable def Qsum (w ν : Fin n → ℝ) (K : Fin n → Submodule ℝ (Vec d)) :
    Vec d →L[ℝ] Vec d :=
  ∑ i, (w i * ν i) • (K i)ᗮ.starProjection

lemma Qsum_apply (w ν : Fin n → ℝ) (K : Fin n → Submodule ℝ (Vec d)) (v : Vec d) :
    Qsum w ν K v = ∑ i, (w i * ν i) • (K i)ᗮ.starProjection v := by
  simp [Qsum]

lemma Qsum_symm (w ν : Fin n → ℝ) (K : Fin n → Submodule ℝ (Vec d)) :
    ((Qsum w ν K : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, Qsum_apply, sum_inner, inner_sum,
    real_inner_smul_left, real_inner_smul_right, Submodule.inner_starProjection_left_eq_right]

lemma Qsum_quad (w ν : Fin n → ℝ) (K : Fin n → Submodule ℝ (Vec d)) (v : Vec d) :
    inner ℝ (Qsum w ν K v) v = ∑ i, w i * ν i * ‖(K i)ᗮ.starProjection v‖ ^ 2 := by
  rw [Qsum_apply, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [real_inner_smul_left, inner_starProj_self]

/-- ker Q ⊆ ⋂ᵢ Kᵢ (the inclusion that the rule consumes). -/
lemma ker_Qsum_le {w ν : Fin n → ℝ} (hw : ∀ i, 0 < w i) (hν : ∀ i, 0 < ν i)
    (K : Fin n → Submodule ℝ (Vec d)) :
    LinearMap.ker ((Qsum w ν K : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d) ≤ ⨅ i, K i := by
  intro v hv
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  have h0 : ∑ i, w i * ν i * ‖(K i)ᗮ.starProjection v‖ ^ 2 = 0 := by
    rw [← Qsum_quad, hv, inner_zero_left]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by
    have := mul_pos (hw i) (hν i); positivity)] at h0
  rw [Submodule.mem_iInf]
  intro i
  have hi := h0 i (Finset.mem_univ _)
  have hp : (K i)ᗮ.starProjection v = 0 := by
    have hwν : w i * ν i ≠ 0 := (mul_pos (hw i) (hν i)).ne'
    have : ‖(K i)ᗮ.starProjection v‖ ^ 2 = 0 := by
      rcases mul_eq_zero.1 hi with h | h
      · exact absurd h hwν
      · exact h
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at hp
  exact hp

/-- **R-sum (c)** (draft lem:rule-sum(c), G2.1(e)): let every term carry a valid kernel
attribute (Kᵢ, νᵢ) (S_K = S) and Q := Σ wᵢνᵢP_{Kᵢ⊥}. If Q ≠ 0, (⋂ᵢKᵢ, ν) is valid for F for
every ν ∈ (0, λ⁺(Q)]; if Q = 0, (ℝᵈ, ν) is valid for every ν > 0. -/
theorem rule_sum_c (f : Fin n → Vec d → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (K : Fin n → Submodule ℝ (Vec d)) (ν : Fin n → ℝ)
    (hν : ∀ i, 0 < ν i) (hK : ∀ i, KernelValid (f i) (K i) (ν i)) :
    (Qsum w ν K ≠ 0 → ∀ ν' : ℝ, 0 < ν' → ν' ≤ opLamPlus (Qsum w ν K) →
        KernelValid (sumF w f) (⨅ i, K i) ν') ∧
      (Qsum w ν K = 0 → ∀ ν' : ℝ, 0 < ν' → KernelValid (sumF w f) ⊤ ν') := by
  have hdiff : ∀ i, Differentiable ℝ (f i) := fun i => differentiable_of_C1 (hf i)
  set Q := Qsum w ν K with hQ
  have hpsd : ∀ v, 0 ≤ inner ℝ (Q v) v := by
    intro v; rw [hQ, Qsum_quad]
    exact Finset.sum_nonneg fun i _ => by have := mul_pos (hw i) (hν i); positivity
  have hmain : ∀ x y, inner ℝ (Q (x - y)) (x - y)
      ≤ inner ℝ (gradient (sumF w f) x - gradient (sumF w f) y) (x - y) := by
    intro x y
    rw [hQ, Qsum_quad, inner_gradient_sumF w hdiff]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hK i x y) (hw i).le
  refine ⟨fun hQ0 ν' hν' hle x y => ?_, fun hQ0 ν' _ x y => ?_⟩
  · have h1 := opLamPlus_mul_le (Qsum_symm w ν K) hpsd (x - y)
    have h2 := norm_perp_anti (ker_Qsum_le hw hν K) (x - y)
    have h3 : ‖(⨅ i, K i)ᗮ.starProjection (x - y)‖ ^ 2
        ≤ ‖(LinearMap.ker ((Q : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d))ᗮ.starProjection
            (x - y)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    calc ν' * ‖(⨅ i, K i)ᗮ.starProjection (x - y)‖ ^ 2
        ≤ opLamPlus Q * ‖(LinearMap.ker ((Q : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d))ᗮ.starProjection
            (x - y)‖ ^ 2 := mul_le_mul hle h3 (sq_nonneg _) (opLamPlus_nonneg (Qsum_symm w ν K) hpsd)
      _ ≤ inner ℝ (Q (x - y)) (x - y) := h1
      _ ≤ _ := hmain x y
  · rw [starProjection_orth_top, norm_zero]
    have := hmain x y
    rw [hQ0, zero_apply, inner_zero_left] at this
    simpa using this

/-- **R-sum (c), packaged:** with Q ≠ 0, F carries the full declaration
(β̂, σ_𝔈^T, (⋂ᵢKᵢ, λ⁺(Q))) for every T ⊆ S_K — "again a smooth atom". -/
theorem rule_sum_c_decl (f : Fin n → Vec d → ℝ) (hf : ∀ i, ContDiff ℝ 1 (f i)) (w : Fin n → ℝ)
    (hw : ∀ i, 0 < w i) (δ : Fin n → SDecl d) (hv : ∀ i, (δ i).Valid (f i))
    (K : Fin n → Submodule ℝ (Vec d)) (ν : Fin n → ℝ) (hν : ∀ i, 0 < ν i)
    (hA : ∀ i, (δ i).A = KComp.pair (K i) (ν i) (hν i)) {T : Finset (Fin n)}
    (hT : T ⊆ SKX δ) (hQ : Qsum w ν K ≠ 0) :
    (⟨betaHatX w δ, sigmaTX w δ T,
      KComp.pair (⨅ i, K i) (opLamPlus (Qsum w ν K))
        (opLamPlus_pos (Qsum_symm w ν K) (fun v => by
          rw [Qsum_quad]
          exact Finset.sum_nonneg fun i _ => by have := mul_pos (hw i) (hν i); positivity)
          hQ)⟩ : SDecl d).Valid (sumF w f) := by
  have hb := (rule_sum_b f hf w hw δ hv hT).2
  have hK : ∀ i, KernelValid (f i) (K i) (ν i) := by
    intro i; have := (hv i).2.2; rw [hA i] at this; exact this
  refine ⟨hb.1, hb.2.1, ?_⟩
  exact (rule_sum_c f hf w hw K ν hν hK).1 hQ _ (opLamPlus_pos (Qsum_symm w ν K) (fun v => by
          rw [Qsum_quad]
          exact Finset.sum_nonneg fun i _ => by have := mul_pos (hw i) (hν i); positivity) hQ)
    le_rfl

end RuleSum

/-! ## §4. R-affine (Lemma G2.3(a); draft lem:rule-affine(a)), C¹ atoms -/

section RuleAffine

variable {d p : ℕ}

/-- LᵀL (as the operator L* ∘ L on ℝᵈ). -/
noncomputable def gramL (L : Vec d →L[ℝ] Vec p) : Vec d →L[ℝ] Vec d :=
  (ContinuousLinearMap.adjoint L).comp L

lemma gramL_quad (L : Vec d →L[ℝ] Vec p) (v : Vec d) : inner ℝ (gramL L v) v = ‖L v‖ ^ 2 := by
  rw [gramL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    real_inner_self_eq_norm_sq]

lemma gramL_symm (L : Vec d →L[ℝ] Vec p) :
    ((gramL L : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, gramL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]

/-- N_L = LᵀP_{K⊥}L. -/
noncomputable def NL (L : Vec d →L[ℝ] Vec p) (K : Submodule ℝ (Vec p)) : Vec d →L[ℝ] Vec d :=
  (ContinuousLinearMap.adjoint L).comp (Kᗮ.starProjection.comp L)

lemma NL_quad (L : Vec d →L[ℝ] Vec p) (K : Submodule ℝ (Vec p)) (v : Vec d) :
    inner ℝ (NL L K v) v = ‖Kᗮ.starProjection (L v)‖ ^ 2 := by
  rw [NL, ContinuousLinearMap.comp_apply, ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.comp_apply, inner_starProj_self]

lemma NL_symm (L : Vec d →L[ℝ] Vec p) (K : Submodule ℝ (Vec p)) :
    ((NL L K : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d).IsSymmetric := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, NL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right,
    Submodule.inner_starProjection_left_eq_right]

lemma NL_psd (L : Vec d →L[ℝ] Vec p) (K : Submodule ℝ (Vec p)) (v : Vec d) :
    0 ≤ inner ℝ (NL L K v) v := by
  rw [NL_quad]; positivity

/-- ker N_L ⊆ L⁻¹(K). -/
lemma ker_NL_le (L : Vec d →L[ℝ] Vec p) (K : Submodule ℝ (Vec p)) :
    LinearMap.ker ((NL L K : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d)
      ≤ K.comap (L : Vec d →ₗ[ℝ] Vec p) := by
  intro v hv
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at hv
  have h0 : ‖Kᗮ.starProjection (L v)‖ ^ 2 = 0 := by rw [← NL_quad, hv, inner_zero_left]
  have hp : Kᗮ.starProjection (L v) = 0 := norm_eq_zero.1 ((pow_eq_zero_iff two_ne_zero).1 h0)
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal] at hp
  exact hp

/-- L⁻¹(K) ⊆ ker N_L (so ker N_L = L⁻¹(K)). -/
lemma le_ker_NL (L : Vec d →L[ℝ] Vec p) (K : Submodule ℝ (Vec p)) :
    K.comap (L : Vec d →ₗ[ℝ] Vec p)
      ≤ LinearMap.ker ((NL L K : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d) := by
  intro v hv
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hv
  rw [LinearMap.mem_ker, ContinuousLinearMap.coe_coe, NL, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, Submodule.starProjection_orthogonal_apply_eq_zero hv,
    map_zero]

/-- ∇(f∘ℓ)(x) = Lᵀ∇f(ℓx) (Boyd–Vandenberghe §A.4.2). -/
lemma hasGradientAt_comp_aff {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) (x : Vec d) :
    HasGradientAt (fun x => f (L x + b))
      (ContinuousLinearMap.adjoint L (gradient f (L x + b))) x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h1 : HasFDerivAt (fun x => L x + b) L x := L.hasFDerivAt.add_const b
  have h2 := (hf (L x + b)).hasFDerivAt.comp x h1
  refine h2.congr_fderiv ?_
  ext v
  simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply,
    ContinuousLinearMap.adjoint_inner_left]
  rw [gradient, InnerProductSpace.toDual_symm_apply]

lemma gradient_comp_aff {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) (x : Vec d) :
    gradient (fun x => f (L x + b)) x = ContinuousLinearMap.adjoint L (gradient f (L x + b)) :=
  (hasGradientAt_comp_aff hf L b x).gradient

lemma differentiable_comp_aff {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) : Differentiable ℝ (fun x => f (L x + b)) :=
  fun x => (hasGradientAt_comp_aff hf L b x).differentiableAt

lemma inner_gradient_comp_aff {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) (x y : Vec d) :
    inner ℝ (gradient (fun x => f (L x + b)) x - gradient (fun x => f (L x + b)) y) (x - y)
      = inner ℝ (gradient f (L x + b) - gradient f (L y + b)) ((L x + b) - (L y + b)) := by
  rw [gradient_comp_aff hf, gradient_comp_aff hf, ← map_sub,
    ContinuousLinearMap.adjoint_inner_left, map_sub]
  congr 1; abel

lemma opLamMax_nonneg_of_psd {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hpsd : ∀ x, 0 ≤ inner ℝ (M x) x) : 0 ≤ opLamMax M := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [opLamMax]
  · exact (ev_nonneg h hpsd ⟨0, hd⟩).trans (ev_le_opLamMax M ⟨0, hd⟩)

lemma gramL_psd (L : Vec d →L[ℝ] Vec p) (v : Vec d) : 0 ≤ inner ℝ (gramL L v) v := by
  rw [gramL_quad]; positivity

/-- λ_max(LᵀL) = ‖L‖² (B&C Fact 2.25(ii); Boyd–Vandenberghe §A.5.2). -/
theorem opLamMax_gramL (L : Vec d →L[ℝ] Vec p) : opLamMax (gramL L) = ‖L‖ ^ 2 := by
  have hl0 := opLamMax_nonneg_of_psd (gramL_symm L) (gramL_psd L)
  apply le_antisymm
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp [opLamMax]
    · haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
      obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := opEv (gramL L))
      rw [opLamMax, ← hj, ev_eq_inner (gramL_symm L), gramL_quad]
      have h1 := L.le_opNorm (eb (gramL_symm L) j)
      rw [(eb (gramL_symm L)).orthonormal.1 j, mul_one] at h1
      exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  · have h : ‖L‖ ≤ Real.sqrt (opLamMax (gramL L)) := by
      refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun v => ?_
      have h1 : ‖L v‖ ^ 2 ≤ (Real.sqrt (opLamMax (gramL L)) * ‖v‖) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hl0, ← gramL_quad]
        exact le_opLamMax_mul (gramL_symm L) v
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h1
    calc ‖L‖ ^ 2 ≤ Real.sqrt (opLamMax (gramL L)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = opLamMax (gramL L) := Real.sq_sqrt hl0

/-- β^ℓ := λ_max(LᵀL)·β, and ∞ if β = ∞. -/
noncomputable def betaAff (L : Vec d →L[ℝ] Vec p) (β : ℝ≥0∞) : ℝ≥0∞ :=
  if β = ⊤ then ⊤ else ENNReal.ofReal (opLamMax (gramL L) * β.toReal)

/-- σ^ℓ := σλ_min if σ ≥ 0, σλ_max if −∞ < σ < 0, −∞ if σ = −∞ (the signed rule). -/
noncomputable def sigmaAff (L : Vec d →L[ℝ] Vec p) (σ : WithBot ℝ) : WithBot ℝ :=
  σ.map fun s => if 0 ≤ s then s * opLamMin (gramL L) else s * opLamMax (gramL L)

/-- A^ℓ: void ↦ void; (K, ν) ↦ (L⁻¹(K), νλ⁺(N_L)) if N_L ≠ 0, (ℝᵈ, ν) if N_L = 0. -/
noncomputable def affKC (L : Vec d →L[ℝ] Vec p) : KComp p → KComp d
  | .void => .void
  | .pair K ν hν => by
    classical
    exact if h : NL L K ≠ 0 then
      .pair (K.comap (L : Vec d →ₗ[ℝ] Vec p)) (ν * opLamPlus (NL L K))
        (mul_pos hν (opLamPlus_pos (NL_symm L K) (NL_psd L K) h))
    else .pair ⊤ ν hν

/-- **R-affine, β** (G2.3(a), β^ℓ): β(f∘ℓ) ≤ λ_max(LᵀL)β = ‖L‖²β. -/
theorem rule_affine_beta {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) {β : ℝ} (hβ : 0 ≤ β) (hL : LipGrad f β) :
    LipGrad (fun x => f (L x + b)) (opLamMax (gramL L) * β) := by
  intro x y
  rw [gradient_comp_aff hf, gradient_comp_aff hf, ← map_sub, opLamMax_gramL]
  have h1 := (ContinuousLinearMap.adjoint L).le_opNorm (gradient f (L x + b) - gradient f (L y + b))
  rw [LinearIsometryEquiv.norm_map] at h1
  have h2 := hL (L x + b) (L y + b)
  have e : L x + b - (L y + b) = L (x - y) := by rw [map_sub]; abel
  rw [e] at h2
  have h3 := L.le_opNorm (x - y)
  calc _ ≤ ‖L‖ * ‖gradient f (L x + b) - gradient f (L y + b)‖ := h1
    _ ≤ ‖L‖ * (β * ‖L (x - y)‖) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ ‖L‖ * (β * (‖L‖ * ‖x - y‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hβ) (norm_nonneg _)
    _ = ‖L‖ ^ 2 * β * ‖x - y‖ := by ring

/-- **R-affine, σ (signed rule)** (G2.3(a), σ^ℓ): C(f, σ) gives C(f∘ℓ, σλ_min(LᵀL)) if
σ ≥ 0 and C(f∘ℓ, σλ_max(LᵀL)) if σ < 0. -/
theorem rule_affine_sigma {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) {σ : ℝ} (hσ : ModC f σ) :
    ModC (fun x => f (L x + b))
      (if 0 ≤ σ then σ * opLamMin (gramL L) else σ * opLamMax (gramL L)) := by
  rw [modC_iff_strongMono hf] at hσ
  rw [modC_iff_strongMono (differentiable_comp_aff hf L b)]
  intro x y
  rw [inner_gradient_comp_aff hf]
  have h1 := hσ (L x + b) (L y + b)
  have e : L x + b - (L y + b) = L (x - y) := by rw [map_sub]; abel
  rw [e] at h1 ⊢
  rw [← gramL_quad] at h1
  have hmin := opLamMin_mul_le (gramL_symm L) (x - y)
  have hmax := le_opLamMax_mul (gramL_symm L) (x - y)
  split_ifs with h0
  · have := mul_le_mul_of_nonneg_left hmin h0
    nlinarith
  · push Not at h0
    have := mul_le_mul_of_nonpos_left hmax h0.le
    nlinarith

/-- **R-affine, kernel preimage** (G2.3(a), A^ℓ): if (K, ν) is valid for f and
N_L = LᵀP_{K⊥}L ≠ 0, then (L⁻¹(K), νλ⁺(N_L)) is valid for f∘ℓ; if N_L = 0, (ℝᵈ, ν) is. -/
theorem rule_affine_kernel {f : Vec p → ℝ} (hf : Differentiable ℝ f) (L : Vec d →L[ℝ] Vec p)
    (b : Vec p) {K : Submodule ℝ (Vec p)} {ν : ℝ} (hν : 0 < ν) (hK : KernelValid f K ν) :
    (NL L K ≠ 0 → KernelValid (fun x => f (L x + b)) (K.comap (L : Vec d →ₗ[ℝ] Vec p))
        (ν * opLamPlus (NL L K))) ∧
      (NL L K = 0 → KernelValid (fun x => f (L x + b)) ⊤ ν) := by
  have hmain : ∀ x y, ν * inner ℝ (NL L K (x - y)) (x - y)
      ≤ inner ℝ (gradient (fun x => f (L x + b)) x - gradient (fun x => f (L x + b)) y)
          (x - y) := by
    intro x y
    rw [inner_gradient_comp_aff hf, NL_quad]
    have e : L x + b - (L y + b) = L (x - y) := by rw [map_sub]; abel
    have := hK (L x + b) (L y + b)
    rw [e] at this ⊢
    exact this
  refine ⟨fun hN x y => ?_, fun hN x y => ?_⟩
  · have h1 := opLamPlus_mul_le (NL_symm L K) (NL_psd L K) (x - y)
    have h2 := norm_perp_anti (ker_NL_le L K) (x - y)
    have h3 : ‖(K.comap (L : Vec d →ₗ[ℝ] Vec p))ᗮ.starProjection (x - y)‖ ^ 2
        ≤ ‖(LinearMap.ker ((NL L K : Vec d →L[ℝ] Vec d) : Vec d →ₗ[ℝ] Vec d))ᗮ.starProjection
            (x - y)‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    have hl0 := opLamPlus_nonneg (NL_symm L K) (NL_psd L K)
    calc ν * opLamPlus (NL L K) * ‖(K.comap (L : Vec d →ₗ[ℝ] Vec p))ᗮ.starProjection (x - y)‖ ^ 2
        ≤ ν * (opLamPlus (NL L K) * ‖(LinearMap.ker ((NL L K : Vec d →L[ℝ] Vec d) :
            Vec d →ₗ[ℝ] Vec d))ᗮ.starProjection (x - y)‖ ^ 2) := by
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h3 hl0) hν.le
      _ ≤ ν * inner ℝ (NL L K (x - y)) (x - y) := mul_le_mul_of_nonneg_left h1 hν.le
      _ ≤ _ := hmain x y
  · rw [starProjection_orth_top, norm_zero]
    have := hmain x y
    rw [hN, zero_apply, inner_zero_left, mul_zero] at this
    simpa using this

/-- **R-affine (a)** (draft lem:rule-affine(a), G2.3(a)), packaged: if (β, σ, A_f) is valid
for f ∈ C¹(ℝᵖ), then f∘ℓ ∈ C¹(ℝᵈ) and (β^ℓ, σ^ℓ, A^ℓ) is valid for f∘ℓ, ℓ(x) = Lx + b. -/
theorem rule_affine (L : Vec d →L[ℝ] Vec p) (b : Vec p) {f : Vec p → ℝ} (hf : ContDiff ℝ 1 f)
    (δ : SDecl p) (hv : δ.Valid f) :
    ContDiff ℝ 1 (fun x => f (L x + b)) ∧
      (⟨betaAff L δ.β, sigmaAff L δ.σ, affKC L δ.A⟩ : SDecl d).Valid (fun x => f (L x + b)) := by
  have hdf := differentiable_of_C1 hf
  refine ⟨hf.comp (L.contDiff.add contDiff_const), ?_, ?_, ?_⟩
  · intro hne
    have hβ : δ.β ≠ ⊤ := by
      intro h; apply hne; simp [betaAff, h]
    simp only [betaAff, if_neg hβ]
    rw [ENNReal.toReal_ofReal (mul_nonneg (opLamMax_nonneg_of_psd (gramL_symm L) (gramL_psd L))
      ENNReal.toReal_nonneg)]
    exact rule_affine_beta hdf L b ENNReal.toReal_nonneg (hv.1 hβ)
  · intro s hs
    change sigmaAff L δ.σ = ↑s at hs
    cases hσ : δ.σ with
    | bot => rw [hσ] at hs; simp [sigmaAff] at hs
    | coe t =>
      rw [hσ] at hs
      simp only [sigmaAff, WithBot.map_coe, WithBot.coe_inj] at hs
      rw [← hs]
      exact rule_affine_sigma hdf L b (hv.2.1 t hσ)
  · have hA := hv.2.2
    cases hAc : δ.A with
    | void => simp [affKC, KComp.Valid]
    | pair K ν hν =>
      rw [hAc] at hA
      have hk := rule_affine_kernel hdf L b hν hA
      by_cases hN : NL L K ≠ 0
      · simp only [affKC, dif_pos hN, KComp.Valid]
        exact hk.1 hN
      · simp only [affKC, dif_neg hN, KComp.Valid]
        exact hk.2 (not_not.1 hN)

/-- G2.3(a), "Moreover": if f is K-invariant then f∘ℓ is L⁻¹(K)-invariant. -/
theorem rule_affine_invariance (L : Vec d →L[ℝ] Vec p) (b : Vec p) {f : Vec p → ℝ}
    {K : Submodule ℝ (Vec p)} (hinv : ∀ y z, z ∈ K → f (y + z) = f y) :
    ∀ x z, z ∈ K.comap (L : Vec d →ₗ[ℝ] Vec p) → f (L (x + z) + b) = f (L x + b) := by
  intro x z hz
  rw [Submodule.mem_comap, ContinuousLinearMap.coe_coe] at hz
  rw [map_add, add_right_comm]
  exact hinv _ _ hz

end RuleAffine

/-! ## §5. Remark G1.4(c) (S1.8): joins of valid declarations need not be valid -/

section NotLattice

/-- e₁ (the dossier's first basis vector) and e₂ of ℝ². -/
noncomputable def E0 : Vec 2 := EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
noncomputable def E1 : Vec 2 := EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

/-- span e₁ (the dossier's `span e₁`), and span e₂. -/
noncomputable def U1 : Submodule ℝ (Vec 2) := ℝ ∙ E0
noncomputable def V2 : Submodule ℝ (Vec 2) := ℝ ∙ E1

/-- H = diag(1, 4) = I + 3P_{span e₂}. -/
noncomputable def Hdiag : Vec 2 →L[ℝ] Vec 2 :=
  ContinuousLinearMap.id ℝ (Vec 2) + (3 : ℝ) • V2.starProjection

/-- f(x) = ½xᵀ diag(1, 4) x (as G3's quadratic atom ½⟨Hx, x⟩ − ⟨0, x⟩). -/
noncomputable def fdiag : Vec 2 → ℝ :=
  G3.quadAtom (fun _ : Fin 1 => Hdiag) (fun _ => 0) 0

lemma E0_norm : ‖E0‖ = 1 := by simp [E0]
lemma E1_norm : ‖E1‖ = 1 := by simp [E1]
lemma inner_E1_E0 : inner ℝ E1 E0 = 0 := by simp [E0, E1, EuclideanSpace.inner_single_left]
lemma inner_E0_E1 : inner ℝ E0 E1 = 0 := by rw [real_inner_comm]; exact inner_E1_E0

lemma Hdiag_apply (v : Vec 2) : Hdiag v = v + (3 : ℝ) • V2.starProjection v := by
  simp [Hdiag]

lemma Hdiag_symm (x y : Vec 2) : inner ℝ (Hdiag x) y = inner ℝ x (Hdiag y) := by
  rw [Hdiag_apply, Hdiag_apply, inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, Submodule.inner_starProjection_left_eq_right]

lemma Hdiag_quad (v : Vec 2) : inner ℝ (Hdiag v) v = ‖v‖ ^ 2 + 3 * inner ℝ E1 v ^ 2 := by
  rw [Hdiag_apply, inner_add_left, real_inner_smul_left, inner_starProj_self,
    real_inner_self_eq_norm_sq, V2, Submodule.starProjection_unit_singleton ℝ E1_norm,
    norm_smul, E1_norm, mul_one, Real.norm_eq_abs, sq_abs]

/-- Parseval in ℝ²: ‖v‖² = ⟨e₁, v⟩² + ⟨e₂, v⟩². -/
lemma parseval2 (v : Vec 2) : ‖v‖ ^ 2 = inner ℝ E0 v ^ 2 + inner ℝ E1 v ^ 2 := by
  classical
  have h := (EuclideanSpace.basisFun (Fin 2) ℝ).sum_inner_mul_inner v v
  rw [Fin.sum_univ_two, EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_apply,
    real_inner_self_eq_norm_sq, real_inner_comm (EuclideanSpace.single 0 1) v,
    real_inner_comm (EuclideanSpace.single 1 1) v] at h
  rw [← h, E0, E1]
  ring

lemma perpU1_norm_sq (v : Vec 2) :
    ‖U1ᗮ.starProjection v‖ ^ 2 = ‖v‖ ^ 2 - inner ℝ E0 v ^ 2 := by
  rw [← inner_starProj_self, Submodule.starProjection_orthogonal_val, U1,
    Submodule.starProjection_unit_singleton ℝ E0_norm, inner_sub_left,
    real_inner_self_eq_norm_sq, real_inner_smul_left, real_inner_comm v E0]
  ring

lemma kernelValid_fdiag_iff (K : Submodule ℝ (Vec 2)) (ν : ℝ) :
    KernelValid fdiag K ν ↔ ∀ v, ν * ‖Kᗮ.starProjection v‖ ^ 2 ≤ ‖v‖ ^ 2 + 3 * inner ℝ E1 v ^ 2 := by
  unfold fdiag
  rw [G3.quad_kernel_iff (fun _ => Hdiag_symm) 0 K ν]
  simp only [Hdiag_quad]

lemma valid_bot_iff (ν : ℝ) : KernelValid fdiag ⊥ ν ↔ ν ≤ 1 := by
  rw [kernelValid_fdiag_iff]
  constructor
  · intro h
    have := h E0
    rw [starProjection_orth_bot, E0_norm, inner_E1_E0] at this
    linarith
  · intro h v
    rw [starProjection_orth_bot]
    have := mul_le_mul_of_nonneg_right h (sq_nonneg ‖v‖)
    nlinarith [sq_nonneg (inner ℝ E1 v)]

lemma valid_U1_iff (ν : ℝ) : KernelValid fdiag U1 ν ↔ ν ≤ 4 := by
  rw [kernelValid_fdiag_iff]
  constructor
  · intro h
    have := h E1
    rw [perpU1_norm_sq, E1_norm, inner_E0_E1, real_inner_self_eq_norm_sq, E1_norm] at this
    linarith
  · intro h v
    rw [perpU1_norm_sq, parseval2 v]
    have := mul_le_mul_of_nonneg_right h (sq_nonneg (inner ℝ E1 v))
    nlinarith [sq_nonneg (inner ℝ E0 v)]

/-- Submodules of span e₁ are {0} and span e₁. -/
lemma le_U1_cases {K : Submodule ℝ (Vec 2)} (hK : K ≤ U1) : K = ⊥ ∨ U1 ≤ K := by
  by_cases h : E0 ∈ K
  · exact Or.inr ((Submodule.span_singleton_le_iff_mem _ _).2 h)
  · left
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 (hK hz)
    by_cases hc : c = 0
    · simp [hc]
    · exact absurd (by simpa [smul_smul, inv_mul_cancel₀ hc] using K.smul_mem c⁻¹ hz) h

/-- The two maximal valid kernel attributes of f = ½xᵀdiag(1,4)x. -/
noncomputable def Abot1 : KComp 2 := .pair ⊥ 1 one_pos
noncomputable def AU4 : KComp 2 := .pair U1 4 (by norm_num)
/-- Their join ({0}, 4). -/
noncomputable def Abot4 : KComp 2 := .pair ⊥ 4 (by norm_num)

/-- **Remark G1.4(c) (S1.8), the "not a lattice" witness.** For f(x) = ½xᵀdiag(1, 4)x on ℝ²:
({0}, 1) and (span e₁, 4) are valid and maximal among valid kernel attributes, their least
upper bound in 𝒦 is ({0}, 4), and ({0}, 4) is not valid. -/
theorem not_lattice_witness :
    Maximal (fun A : KComp 2 => A.Valid fdiag) Abot1 ∧
    Maximal (fun A : KComp 2 => A.Valid fdiag) AU4 ∧
    IsLUB ({Abot1, AU4} : Set (KComp 2)) Abot4 ∧
    ¬ Abot4.Valid fdiag := by
  refine ⟨⟨(valid_bot_iff 1).2 le_rfl, ?_⟩, ⟨(valid_U1_iff 4).2 le_rfl, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro B hB hle
    cases B with
    | void => exact absurd hle KComp.not_pair_le_void
    | pair K ν hν =>
      have hK : K = ⊥ := le_bot_iff.1 hle.1
      subst hK
      exact ⟨le_rfl, (valid_bot_iff ν).1 hB⟩
  · intro B hB hle
    cases B with
    | void => exact absurd hle KComp.not_pair_le_void
    | pair K ν hν =>
      rcases le_U1_cases hle.1 with hK | hK
      · subst hK
        have h1 := (valid_bot_iff ν).1 hB
        have h2 : (4 : ℝ) ≤ ν := hle.2
        linarith
      · have hKe : K = U1 := le_antisymm hle.1 hK
        subst hKe
        exact ⟨le_rfl, (valid_U1_iff ν).1 hB⟩
  · rintro A (rfl | rfl)
    · exact ⟨le_rfl, by norm_num⟩
    · exact ⟨bot_le, le_rfl⟩
  · intro B hB
    have h1 : Abot1 ≤ B := hB (by simp)
    have h2 : AU4 ≤ B := hB (by simp)
    cases B with
    | void => exact absurd h1 KComp.not_pair_le_void
    | pair K ν hν => exact ⟨h1.1, h2.2⟩
  · intro h
    have := (valid_bot_iff 4).1 h
    norm_num at this

end NotLattice

/-! ### Remark G1.4(c) at the level of full declarations -/

section NotLatticeDecl

lemma Hdiag_psd (v : Vec 2) : 0 ≤ inner ℝ (Hdiag v) v := by
  rw [Hdiag_quad]; positivity

lemma fdiag_lipGrad_iff {β : ℝ} (hβ : 0 ≤ β) :
    LipGrad fdiag β ↔ ∀ v, ‖v‖ ^ 2 + 3 * inner ℝ E1 v ^ 2 ≤ β * ‖v‖ ^ 2 := by
  unfold fdiag
  rw [G3.quad_lipGrad_iff (fun _ => Hdiag_symm) (fun _ => Hdiag_psd) 0 hβ]
  simp only [Hdiag_quad]

lemma fdiag_modC_iff (σ : ℝ) :
    ModC fdiag σ ↔ ∀ v, σ * ‖v‖ ^ 2 ≤ ‖v‖ ^ 2 + 3 * inner ℝ E1 v ^ 2 := by
  unfold fdiag
  rw [G3.quad_modC_iff (fun _ => Hdiag_symm) 0 σ]
  simp only [Hdiag_quad]

/-- The two maximal valid declarations (4, 1, ({0}, 1)) and (4, 1, (span e₁, 4)) of
f = ½xᵀdiag(1,4)x, and their join (4, 1, ({0}, 4)). -/
noncomputable def D1 : SDecl 2 := ⟨4, ((1 : ℝ) : WithBot ℝ), Abot1⟩
noncomputable def D2 : SDecl 2 := ⟨4, ((1 : ℝ) : WithBot ℝ), AU4⟩
noncomputable def Djoin : SDecl 2 := ⟨4, ((1 : ℝ) : WithBot ℝ), Abot4⟩

lemma smooth4 : SmoothOK fdiag 4 := by
  intro _
  have h4 : (4 : ℝ≥0∞).toReal = 4 := by norm_num
  rw [h4, fdiag_lipGrad_iff (by norm_num)]
  intro v
  have := parseval2 v
  nlinarith [sq_nonneg (inner ℝ E0 v)]

lemma curv1 : CurvOK fdiag ((1 : ℝ) : WithBot ℝ) := by
  intro s hs
  rw [← WithBot.coe_injective hs, fdiag_modC_iff]
  intro v; nlinarith [sq_nonneg (inner ℝ E1 v)]

lemma valid_maximal_aux {B : SDecl 2} (hB : B.Valid fdiag) (hβ : B.β ≤ 4)
    (hσ : ((1 : ℝ) : WithBot ℝ) ≤ B.σ) : 4 ≤ B.β ∧ B.σ ≤ ((1 : ℝ) : WithBot ℝ) := by
  have hne : B.β ≠ ⊤ := ne_top_of_le_ne_top (by norm_num) hβ
  refine ⟨?_, ?_⟩
  · have hL := hB.1 hne
    rw [fdiag_lipGrad_iff ENNReal.toReal_nonneg] at hL
    have h := hL E1
    rw [E1_norm, real_inner_self_eq_norm_sq, E1_norm] at h
    have h4 : (4 : ℝ) ≤ B.β.toReal := by linarith
    have : ENNReal.ofReal 4 ≤ B.β := ENNReal.ofReal_le_of_le_toReal h4
    simpa using this
  · obtain ⟨s, hs, hs1⟩ := WithBot.coe_le_iff.1 hσ
    have hm := hB.2.1 s hs
    rw [fdiag_modC_iff] at hm
    have h := hm E0
    rw [E0_norm, inner_E1_E0] at h
    rw [hs]
    exact WithBot.coe_le_coe.2 (by linarith)

/-- **Remark G1.4(c) (S1.8) for full declarations:** (4, 1, ({0}, 1)) and
(4, 1, (span e₁, 4)) are valid for f = ½xᵀdiag(1, 4)x and maximal among its valid
declarations, their least upper bound in 𝒟_S is (4, 1, ({0}, 4)), and it is not valid. So the
valid declarations of a term form a down-set (`SDecl.valid_of_le`) with several maximal
elements, not closed under joins. -/
theorem not_lattice_witness_decl :
    Maximal (fun δ : SDecl 2 => δ.Valid fdiag) D1 ∧
    Maximal (fun δ : SDecl 2 => δ.Valid fdiag) D2 ∧
    IsLUB ({D1, D2} : Set (SDecl 2)) Djoin ∧
    ¬ Djoin.Valid fdiag := by
  obtain ⟨hm1, hm2, hlub, hinv⟩ := not_lattice_witness
  refine ⟨⟨⟨smooth4, curv1, hm1.1⟩, ?_⟩, ⟨⟨smooth4, curv1, hm2.1⟩, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro B hB hle
    obtain ⟨h1, h2⟩ := valid_maximal_aux hB hle.1 hle.2.1
    exact ⟨h1, h2, hm1.2 hB.2.2 hle.2.2⟩
  · intro B hB hle
    obtain ⟨h1, h2⟩ := valid_maximal_aux hB hle.1 hle.2.1
    exact ⟨h1, h2, hm2.2 hB.2.2 hle.2.2⟩
  · rintro A (rfl | rfl)
    · exact ⟨le_rfl, le_rfl, hlub.1 (by simp [D1])⟩
    · exact ⟨le_rfl, le_rfl, hlub.1 (by simp [D2])⟩
  · intro B hB
    have h1 : D1 ≤ B := hB (by simp)
    have h2 : D2 ≤ B := hB (by simp)
    refine ⟨h1.1, h1.2.1, hlub.2 ?_⟩
    rintro A (rfl | rfl)
    · exact h1.2.2
    · exact h2.2.2
  · intro h
    exact hinv h.2.2

end NotLatticeDecl

/-! ## §6. R-affine sharpness (draft lem:rule-affine(a), "each output is attained") -/

section AffineSharp

variable {d p : ℕ}

/-- The quadratic test term ½⟨My, y⟩ (G3's quadratic atom with c = 0). -/
noncomputable def qT (M : Vec p →L[ℝ] Vec p) : Vec p → ℝ :=
  G3.quadAtom (fun _ : Fin 1 => M) (fun _ => 0) 0

lemma qT_grad {M : Vec p →L[ℝ] Vec p} (hM : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (y : Vec p) : gradient (qT M) y = M y := by
  unfold qT
  rw [G3.gradient_quadAtom (fun _ => hM)]
  simp

lemma qT_diff {M : Vec p →L[ℝ] Vec p} (hM : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y)) :
    Differentiable ℝ (qT M) :=
  G3.differentiable_quadAtom (fun _ => hM) 0

lemma qT_comp_grad_diff {M : Vec p →L[ℝ] Vec p} (hM : ∀ x y, inner ℝ (M x) y = inner ℝ x (M y))
    (L : Vec d →L[ℝ] Vec p) (b : Vec p) (x y : Vec d) :
    gradient (fun x => qT M (L x + b)) x - gradient (fun x => qT M (L x + b)) y
      = ContinuousLinearMap.adjoint L (M (L (x - y))) := by
  rw [gradient_comp_aff (qT_diff hM), gradient_comp_aff (qT_diff hM), qT_grad hM, qT_grad hM,
    ← map_sub, ← map_sub]
  congr 2
  rw [map_sub]; abel

lemma smul_id_symm (c : ℝ) (x y : Vec p) :
    inner ℝ ((c • ContinuousLinearMap.id ℝ (Vec p)) x) y
      = inner ℝ x ((c • ContinuousLinearMap.id ℝ (Vec p)) y) := by
  simp [real_inner_smul_left, real_inner_smul_right]

lemma smul_proj_symm (ν : ℝ) (K : Submodule ℝ (Vec p)) (x y : Vec p) :
    inner ℝ ((ν • Kᗮ.starProjection) x) y = inner ℝ x ((ν • Kᗮ.starProjection) y) := by
  simp only [smul_apply, real_inner_smul_left, real_inner_smul_right,
    Submodule.inner_starProjection_left_eq_right]

lemma qT_smul_id (c : ℝ) (y : Vec p) :
    qT (c • ContinuousLinearMap.id ℝ (Vec p)) y = c / 2 * ‖y‖ ^ 2 := by
  simp [qT, G3.quadAtom, real_inner_smul_left]
  ring

lemma qT_smul_proj (ν : ℝ) (K : Submodule ℝ (Vec p)) (y : Vec p) :
    qT (ν • Kᗮ.starProjection) y = ν / 2 * ‖Kᗮ.starProjection y‖ ^ 2 := by
  simp only [qT, G3.quadAtom, smul_apply, real_inner_smul_left,
    inner_starProj_self, inner_zero_left, sub_zero]
  ring

lemma exists_ev_eq_lamPlus {M : Vec d →L[ℝ] Vec d} (h : (M : Vec d →ₗ[ℝ] Vec d).IsSymmetric)
    (hM : M ≠ 0) : ∃ k, opEv M k = opLamPlus M ∧ opEv M k ≠ 0 := by
  have hex : ∃ j, opEv M j ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hM
    ext1 x
    rw [← (eb h).sum_repr' x, map_sum]
    simp only [map_smul, apply_eb h, hall, zero_smul, smul_zero, Finset.sum_const_zero,
      zero_apply]
  obtain ⟨j, hj⟩ := hex
  have hne : {μ : ℝ | ∃ j, opEv M j = μ ∧ μ ≠ 0}.Nonempty := ⟨_, j, rfl, hj⟩
  have hfin : {μ : ℝ | ∃ j, opEv M j = μ ∧ μ ≠ 0}.Finite :=
    (Set.finite_range (opEv M)).subset (by rintro μ ⟨i, rfl, -⟩; exact ⟨i, rfl⟩)
  obtain ⟨k, hk, hk0⟩ := hne.csInf_mem hfin
  exact ⟨k, hk, by rw [hk]; exact hk0⟩

/-- **R-affine sharpness, β:** f = (β/2)‖·‖² is β-smooth, and every valid β' ≥ 0 for f∘ℓ is
at least β^ℓ = λ_max(LᵀL)β. -/
theorem rule_affine_sharp_beta (L : Vec d →L[ℝ] Vec p) (b : Vec p) {β : ℝ} (hβ : 0 ≤ β) :
    LipGrad (qT (β • ContinuousLinearMap.id ℝ (Vec p))) β ∧
    ∀ β' : ℝ, 0 ≤ β' → LipGrad (fun x => qT (β • ContinuousLinearMap.id ℝ (Vec p)) (L x + b)) β' →
      opLamMax (gramL L) * β ≤ β' := by
  have hM := smul_id_symm (p := p) β
  refine ⟨fun u v => ?_, fun β' hβ' hL => ?_⟩
  · rw [qT_grad hM, qT_grad hM, ← map_sub]
    simp [norm_smul, Real.norm_of_nonneg hβ]
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [opLamMax, Real.iSup_of_isEmpty, zero_mul]
      exact hβ'
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := opEv (gramL L))
    have h := hL (eb (gramL_symm L) j) 0
    rw [qT_comp_grad_diff hM] at h
    simp only [sub_zero, smul_apply, ContinuousLinearMap.id_apply, map_smul] at h
    rw [(eb (gramL_symm L)).orthonormal.1 j, mul_one] at h
    have e : ContinuousLinearMap.adjoint L (L (eb (gramL_symm L) j)) = gramL L (eb (gramL_symm L) j) :=
      rfl
    rw [e, apply_eb (gramL_symm L), norm_smul, norm_smul, (eb (gramL_symm L)).orthonormal.1 j,
      mul_one, Real.norm_of_nonneg hβ, Real.norm_of_nonneg (ev_nonneg (gramL_symm L)
        (gramL_psd L) j), hj] at h
    rw [opLamMax]
    linarith

/-- **R-affine sharpness, σ (signed):** f = (σ/2)‖·‖² satisfies C(f, σ), and on ℝᵈ, d ≥ 1,
every τ with C(f∘ℓ, τ) is at most σ^ℓ (σλ_min if σ ≥ 0, σλ_max if σ < 0). -/
theorem rule_affine_sharp_sigma (hd : 0 < d) (L : Vec d →L[ℝ] Vec p) (b : Vec p) (σ : ℝ) :
    ModC (qT (σ • ContinuousLinearMap.id ℝ (Vec p))) σ ∧
    ∀ τ : ℝ, ModC (fun x => qT (σ • ContinuousLinearMap.id ℝ (Vec p)) (L x + b)) τ →
      τ ≤ (if 0 ≤ σ then σ * opLamMin (gramL L) else σ * opLamMax (gramL L)) := by
  have hM := smul_id_symm (p := p) σ
  refine ⟨?_, fun τ hτ => ?_⟩
  · rw [modC_iff_strongMono (qT_diff hM)]
    intro x y
    rw [qT_grad hM, qT_grad hM, ← map_sub]
    simp [real_inner_smul_left]
  · rw [modC_iff_strongMono (differentiable_comp_aff (qT_diff hM) L b)] at hτ
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    have key : ∀ j, τ ≤ σ * opEv (gramL L) j := by
      intro j
      have h := hτ (eb (gramL_symm L) j) 0
      rw [qT_comp_grad_diff hM] at h
      simp only [sub_zero, smul_apply, ContinuousLinearMap.id_apply, map_smul,
        real_inner_smul_left] at h
      rw [(eb (gramL_symm L)).orthonormal.1 j] at h
      have e : ContinuousLinearMap.adjoint L (L (eb (gramL_symm L) j))
          = gramL L (eb (gramL_symm L) j) := rfl
      rw [e, ← ev_eq_inner (gramL_symm L)] at h
      nlinarith
    split_ifs with h0
    · obtain ⟨j, hj⟩ := exists_eq_ciInf_of_finite (f := opEv (gramL L))
      have := key j
      rw [hj] at this
      exact this
    · obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := opEv (gramL L))
      have := key j
      rw [hj] at this
      exact this

/-- **R-affine sharpness, kernel:** f = (ν/2)‖P_{K⊥}·‖² carries (K, ν), and when N_L ≠ 0
every valid gap ν' of f∘ℓ relative to L⁻¹(K) is at most νλ⁺(N_L). -/
theorem rule_affine_sharp_kernel (L : Vec d →L[ℝ] Vec p) (b : Vec p) (K : Submodule ℝ (Vec p))
    (ν : ℝ) (hN : NL L K ≠ 0) :
    KernelValid (qT (ν • Kᗮ.starProjection)) K ν ∧
    ∀ ν' : ℝ, KernelValid (fun x => qT (ν • Kᗮ.starProjection) (L x + b))
        (K.comap (L : Vec d →ₗ[ℝ] Vec p)) ν' → ν' ≤ ν * opLamPlus (NL L K) := by
  have hM := smul_proj_symm (p := p) ν K
  refine ⟨fun x y => ?_, fun ν' hν' => ?_⟩
  · rw [qT_grad hM, qT_grad hM, ← map_sub, smul_apply, real_inner_smul_left,
      inner_starProj_self]
  · obtain ⟨k, hk, hk0⟩ := exists_ev_eq_lamPlus (NL_symm L K) hN
    set e := eb (NL_symm L K) k with he
    have horth : e ∈ (K.comap (L : Vec d →ₗ[ℝ] Vec p))ᗮ := by
      rw [Submodule.mem_orthogonal]
      intro z hz
      have hNz : NL L K z = 0 := by
        have := le_ker_NL L K hz
        rwa [LinearMap.mem_ker, ContinuousLinearMap.coe_coe] at this
      have h1 : inner ℝ z (NL L K e) = 0 := by
        have := NL_symm L K z e
        simp only [ContinuousLinearMap.coe_coe] at this
        rw [← this, hNz, inner_zero_left]
      rw [he, apply_eb (NL_symm L K), real_inner_smul_right] at h1
      rcases mul_eq_zero.1 h1 with h | h
      · exact absurd h hk0
      · exact h
    have hP : (K.comap (L : Vec d →ₗ[ℝ] Vec p))ᗮ.starProjection e = e :=
      Submodule.starProjection_eq_self_iff.2 horth
    have h := hν' e 0
    rw [sub_zero, hP, he, (eb (NL_symm L K)).orthonormal.1 k, qT_comp_grad_diff hM, sub_zero,
      smul_apply, map_smul, real_inner_smul_left] at h
    have e2 : inner ℝ (ContinuousLinearMap.adjoint L (Kᗮ.starProjection (L (eb (NL_symm L K) k))))
        (eb (NL_symm L K) k) = opEv (NL L K) k := by
      rw [ev_eq_inner (NL_symm L K)]
      rfl
    rw [e2, hk] at h
    linarith

end AffineSharp

end OCF.G12

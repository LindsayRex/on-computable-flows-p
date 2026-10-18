/-
H5 (Soundness for pipelines of composed solvers; the a-posteriori principle) — the novel
results of the unit: Definition H5.1 and Lemma H5.2 (composite report and its certificate,
with the equality instances), Lemma H5.3 (every continuous rule emits composite reports),
Lemma H5.4 (interfaces: slice report = block report, report = bracket with thm:h1-pick,
prox-subproblem reports), Lemma H5.8 (liveness and counts), Theorem H5.9 (soundness for
pipelines, over an inductive type of pipeline terms; the leaf rule theorems enter as interface
hypotheses, the stitch rule's are H4's Lean theorems), Corollary H5.10 (counts compose), Theorem H5.11 (the a-posteriori principle,
parts (a)–(c) and the common bounds) and Proposition H5.12(a)–(c) (where the chain breaks).

Source of truth: project_plan/doing/proof_audits/H5_pipeline_soundness/01_derivation.md
(stage-1 dossier, 2026-10-10; §§2–10), landing draft 04_landing_draft.tex (h5-def:report,
h5-lem:cert, h5-lem:closure, h5-def:pipeline, h5-lem:live, h5-thm:soundness, h5-cor:counts,
h5-thm:aposteriori, h5-prop:breaks).
sha16 (sha256, first 16 hex) of 01_derivation.md when formalised: 7ea5d5e0c54791ab (unchanged
at the revision of 2026-10-10 that fixed the two defects of faithfulness run 6: the stitch
execution and the counts).

DEFINITIONAL MAP (dossier symbol → Lean):
* ℝ^d — an arbitrary complete real inner product space `X` (d ≥ 1 as `[Nontrivial X]` only
  where used); SC2 (no frame slot) — no frame data exists in the encoding.
* SC3 split target E = F + Σ_{j∈N} g_j — `SplitTarget F σF D g σ` (N a `Fintype`; g_j ∈ Γ₀ as
  the pair (D j, g j) of H2/H3: g_j on D j, +∞ off it; C(g_j, σ_j) — H3's `ExtModC`;
  C(F, σ_F) — G3's `ModC`; F ∈ C¹ — `Differentiable ℝ F`; ∇F — Mathlib `gradient`).
  dom E — H3's `domE D`; E — H3's `Eval F g`; μ_E — H3's `muHat σF σ`.
* Definition H5.1: report (x̂, u, (v_j, ε_j)) — `IsReport D g xh v ε` (v_j ∈ ∂_{ε_j} g_j(x̂) is
  H2's `EpsSubgrad`); u — `uR F v xh`; ε — `accR ε`; J_R — `exactSet ε`; μ_R — `muR`;
  s_R — `sR`; τ_R — `tauR`/`tauRep`; t̄ — `tbar`; G_R — `GR`/`GRep`; ℓ_R — `ellRep`;
  x* a minimiser — `IsMinD (domE D) (Eval F g) xs`.
* Lemma H5.3: R_α(x_k) — `α⁻¹ • (x_k − x_{k+1})` (H2's `rres`); the constructed iteration /
  inexact run — H2's `ProxEps`, `InexactRun`, G3's `step`; consensus data — H3's `HCert`,
  `ConsIter`, `ConsIter.Typed`; the block maps U_l^T, U_l — adjoint pairs `P l`, `U l`.
* Lemma H5.4: slice φ_{x,l}(y) = F(x + U_l(y − x_l)) — `fun y => F (x + U (y - P x))`;
  Φ_y — smooth part `sqf α⁻¹ (· − y)` plus g; brackets of a pick — `ExtBracket`; the hybrid
  problem — `HybMin` (extended-valued form of H1's pick); thm:h1-pick (a)–(e) — `pick_a`…
  `pick_e`, re-derived in the extended encoding from H1's scalar pruning lemmas.
* Definition H5.5–H5.7 and Theorem H5.9: targets — `Tgt` (a split target bundled with its
  space); reports — `Rep t` (`Rep.Valid`, `Rep.unorm` = ‖u‖, `Rep.acc` = ε, `Rep.Meets`,
  `Rep.Cert` = clause (A)); block target 𝔅 (BT) — `BlockTgt m` (H4's data: block spaces,
  F on `PiLp 2 Xb`, C(F, σ), σ > 0, slice moduli τ_l, cross constants L_{jl}, terms g_{l,i}
  with moduli σ_{l,i}); its declared part — `BlockDecl m` (`BlockTgt.decl`); H4's
  dom g_l, g_l, dom g, U_lᵀ — `BlockTgt.Dh`, `gh`, `dom`, `prj`; E_𝔅 as a split target
  (terms g_{l,i} ∘ U_lᵀ, modulus 0) — `BlockTgt.tgt`; the slice specification 𝔈_{x,l} —
  `BlockTgt.sliceT x l` (smooth part H4's `slice F x l`, σ_F := τ_l); pipeline terms —
  inductive `Node` (fb, inx, cons, stitch with the declared part of 𝔅, θ, the targets
  (η̄_{k,l}, ε̄_{k,l}) and m block pipelines; a block pipeline is ONE term used on every
  slice: UNI) plus a root pick over a finite nonempty `Z` (`soundness_pick`); leaf rule
  semantics — `Sem` = `LeafSem` (three times; `LeafSem.Ex` = executions, `LeafSem.out` = their
  report sequences); executions of a node and their reports — `Exec`, `out` (via `sem`); an
  execution of a stitch — `StitchEx` (sweep points x^{k,i} = `x k i`, 0-based blocks, so the
  dossier's x^{k,l−1} is `x k l`; the call of block l in sweep k is an execution `call k l`
  of the child on `sliceT (x k l) l`, stopped at `n k l`; its final report `fin k l`; the
  stitch report at x^{k+1} — `rep k`); the stitched run of h4-def:report — `StitchEx.toRun`,
  `StitchEx.IsRun` (H4's `Run`); typing, clauses, live condition, count, height —
  `Node.Typed`, `Node.Clauses` (`StitchEx.Clauses` at a stitch), `Node.Live`
  (`BlockTgt.StitchLive`), `Node.Count` (a function of the execution;
  `BlockTgt.stitchCount`), `Node.height`; stopping rules — `FirstMeet` (target) and
  `StopRule`/`Stops` (pick children).
* Lemma H5.8(d) at a stitch: Λ, ρ_θ — `BlockTgt.Λ`, `BlockTgt.ρθ` (H4's `Lam`, `rhoth`);
  E* — `BlockTgt.Estar` (= E(x*) for a minimiser, `Estar_eq`); a₀ — `StitchEx.a0`;
  B̄_k(θ) — `BlockTgt.Bbar` (H4's `Bfun` at the declared targets); A_k — `BlockTgt.Aseq`;
  Ū_k — `BlockTgt.Ubar`.
* Lemma H5.8(d), Corollary H5.10: Γ_k, ‖η_k‖, Q_k, B_k(θ) as functions of the reports — `GamF`,
  `etaN`, `QF`, `BF`; A_k — the explicit sum in `live_stitch`/`accum_le`; 𝖪_{k,l} — `Kkl`;
  the (S5A) count — `Kcount`.
* Proposition H5.12(a): {A, B} — `AB`; E_z — `Eab`; exact block steps — `xstepAB`, `zstepAB`;
  a sweep — `sweepAB`. (b): f — `f2`; the smooth part of Φ₂ — `q2`. (c): φ — `sqf τ` on ℝ.

MODELLING CHOICES (none weakens a dossier statement):
* Theorem H5.9 is stated over the inductive pipeline type (dossier §13 D6, the H1 pattern).
  The LEAF rules enter through interface hypotheses, the fields of `LeafSem`:
  Lemma H5.3(i)–(iii) (`report`), the landed theorem of the row (`sound`) and
  Lemma H5.8(a)–(c) (`livecount`, with a count that is a function of the execution, as the
  counts of Lemma H5.8 depend on the start of the call). Those lemmas are formalised concretely
  in this file (`closure_*`, `live_*`); the instantiation of `LeafSem` by them is not (see NOT
  FORMALISED). The STITCH rule has no interface: its semantics is concrete (`BlockTgt`,
  `StitchEx`), every execution is a stitched run of H4 (`StitchEx.toRun`), and its clauses are
  discharged from the H4 Lean theorems (`BlockTgt.h4Clauses`: `Run.H4_4_c`, `Run.H4_6`,
  `Run.H4_7_a`, `Run.H4_7_a_zero`, `Run.H4_7_b`, `Run.H4_7_c`, `Run.H4_7_c1`–`c3`,
  `Run.H4_7_d_declared`, `Run.H4_7_d_dist`), with Lemma H5.3(iv) (`closure_stitch`),
  Lemma H5.4(a) (`StitchEx.eta_eq`, via H4's `gradient_slice`) and Lemma H5.8(d)
  (`StitchEx.apriori`, `StitchEx.live_count`). Clause (A) and the pick clauses are NOT
  interfaces: they are `lemma_H5_2`, `report_bracket` and `pick_b`–`pick_d`.
* A stitch execution carries its sweep points, and the call of block l in sweep k runs on the
  slice at x^{k,l−1} (Lean `x k l`), the point built from x^k and the earlier outputs of the
  sweep (`StitchEx.call`, `StitchEx.step`). Each call of a child is an execution of the child
  term on that slice, from ANY start: the warm start y₀ = x^k_l is not imposed. This is a
  genuine over-approximation: every fact used about a call (the leaf fields, quantified over
  all executions, and H4's theorems, which admit any producer of block reports) holds for any
  start. The warm start matters only for the count of Corollary H5.10(b), where it enters
  `cor_b` as the hypotheses `hR`, `hgrow`, `hG`.
* A stitch node carries the declared part of its block target (`BlockDecl`: block spaces,
  σ, τ_l, L_{jl}, terms and their moduli); the block target of an execution is a `BlockTgt` B
  with t = B.tgt and that declared part (B is then fixed by t: t fixes F). Diagonal constants
  L_l are not part of `BlockTgt`: they enter only through the leaf typing on the slice
  (abstract) and Corollary H5.10(b) (`cor_b`).
* Declared accuracies of the a-priori quantities: ε̄'_{k,l} := ε̄_{k,l} for every child (for an
  fb child, whose reports are exact and whose live target is (η̄, 0), declare ε̄_{k,l} = 0,
  which gives the dossier's ε̄' = 0). θ > 0 is declared in the node; the count of
  Lemma H5.8(d) is taken with Ā₀ := a₀ of the execution, and the a-priori clauses hold for
  every Ā₀ ≥ a₀. The live condition of a stitch (`StitchLive`) asks, besides B̄_k(θ),
  Γ̄_k, ‖η̄_k‖ → 0 and η̄ > 0, that ε̄_k ≤ ε̄ eventually; both English cases (ε̄_k → 0 with
  ε̄ > 0, and ε̄_k = 0 for fb children) imply it. It also asks for a minimiser x* of E_𝔅
  (existence classical, B&C Cor. 11.17: a hypothesis, as elsewhere).
* Picks: nested picks are flattened (`minOver_sigma`) and a pick is not admissible below a
  stitch (Definition H5.5; Proposition H5.12(a)), so the grammar is `Node` plus a root pick.
* Existence of minimisers (B&C Cor. 11.17) enters as a hypothesis x* (`IsMinD`) wherever used;
  uniqueness, the growth inequality and convexity of E − (μ_E/2)‖·‖² are PROVED (`cert_b`,
  `extModC_Eval`). Lower semicontinuity is never used, so it is not assumed.

STRENGTHENINGS: Lemma H5.2(a) and (b) (growth) hold without μ_E > 0; Lemma H5.2(b)'s uniqueness
needs only a minimiser; Corollary H5.10(c) part 1 holds for q² ≥ ρ_θ; in Theorem H5.9 the calls
of a stitch may start anywhere (above), and the a-priori clauses hold for every Ā₀ ≥ a₀.

COVERAGE (dossier target → Lean name):
* Def. H5.1 — `IsReport`, `uR`, `accR`, `exactSet`, `muR`, `sR`; μ_R ≤ μ_E — `muR_le_muE`;
  μ_R = μ_E cases — `muR_eq_of_sigma`, `muR_eq_of_acc_zero`.
* Lemma H5.2: (a) `cert_a`; (b) `cert_b` (with `extModC_Eval`); (b)–(d) `lemma_H5_2`
  (scalar cores `scalar_c`, `scalar_d`, `scalar_d_eq`, `GRep_eq_case`); (e) `cert_e1`,
  `cert_e2`, `cert_e3`.
* Lemma H5.3: (i) `closure_fb` (N = {j}), `closure_fb_empty` (N = ∅), `closure_fb_run`;
  (ii) `closure_inx`; (iii) `closure_cons` (point form), `closure_cons_iter` (iteration form,
  with ‖r_k‖ ≤ e_k/(α√m') and ε_k ≤ 2‖L‖e_k); (iv) `closure_stitch` (with `epsSubgrad_comp`,
  `extModC_comp`).
* Lemma H5.4: (a) `slice_report_block` (with `hasGradientAt_sliceP`, `epsSubgrad_sum`),
  `slice_moduli_pos`; (b) `report_bracket`, `pick_a`, `pick_b`, `pick_c`, `pick_d`,
  `pick_d_bound`, `pick_e`, flattening `minOver_sigma`; (d) `prox_report_iff`,
  `prox_report_not_answer` (with `epsSubgrad_zero_fun`).
* Lemma H5.8: (a) `live_fb`; (b) `live_inx`, `ellRep_lower`; (c) `live_cons`, `cons_count`,
  `cons_ebar_min`; (d) `live_stitch` (with `accum_le`, `BF_mono`, `GamF_mono`, `etaN_mono`).
* Definitions H5.5–H5.7 — `Tgt`, `Rep`, `BlockDecl`, `BlockTgt` (`tgt`, `sliceT`, `sd`),
  `Node`, `LeafSem`, `Sem`, `StitchEx`, `sem`, `Exec`, `out`, `Node.Typed`, `Node.Clauses`,
  `Node.Live`, `Node.Count`, `Node.height`, `FirstMeet`, `StopRule`, `Stops`.
* Theorem H5.9: non-pick nodes (R), (A), (C), (L) — `Node.soundness` (conclusion
  `Node.Sound`; (A) from `Rep.cert_of_valid`); at a stitch: the induction over the position
  (k, l) — `Node.stitch_valid`, `StitchEx.mem_of_valid`; the execution is a stitched run —
  `StitchEx.toRun`, `StitchEx.isRun_toRun`; (R) — `StitchEx.rep_valid` (via `closure_stitch`);
  (C) — `StitchEx.clauses` (H4's theorem `BlockTgt.h4Clauses`; residuals and accuracies of the
  children `StitchEx.eta_eq`; ‖u‖ and ε of the stitch report `StitchEx.rep_unorm_acc`;
  a-priori clauses `StitchEx.apriori`, with the Minkowski step `BlockTgt.Dk_le`); (L) —
  `StitchEx.live_count` (with `Aseq_succ`, `Bbar_nonneg`, `Estar_eq`); every call of a stitch
  stops within the count of that call — `Node.calls_stop` (with `exists_firstMeet`); a pick —
  `soundness_pick`.
* Corollary H5.10: (a) `cor_a` (with `geom_conv_le`, `BF_scale`); (b) `cor_b`; (c)
  `cor_c_uniform`, `cor_c_total`, `cor_c_sweeps`; (d) `cor_d`.
* Theorem H5.11: the bounds — `aposteriori`; (a) `aposteriori_a`; (b) `aposteriori_b`;
  (c) `aposteriori_c`.
* Proposition H5.12: (a) `breaks_a`; (b) `breaks_b`; (c) `breaks_c`.

CLASSICAL INPUTS TAKEN AS HYPOTHESES (stated as the sources state them): existence of a
minimiser of a strongly convex Γ₀ function (B&C Cor. 11.17, p. 194) — an `IsMinD` hypothesis;
the exact prox inclusion (P) (B&C Prop. 16.44, p. 276) — `ProxEps … 0` hypotheses; the landed
row theorems (thm:soundness (S2)/(S5A), h2 (I2), thm:h3-soundness(c) rate, thm:fb-residual(b),
(Q), h4-thm:stitch (a)–(d), h4-lem:assembly(b)) — explicit hypotheses of `live_*`, `cor_*`
and the fields of `LeafSem`. In Theorem H5.9 the stitch rule's theorems (h4-thm:stitch (a)–(d),
h4-lem:assembly(b), the Minkowski step of its proof) are NOT hypotheses: they are the H4 Lean
theorems, imported from `OcfVerification.H4BlockStitching`; the three interface hypotheses of
`live_stitch` are discharged from them in `StitchEx.apriori`. (GI) (B&C Prop. 17.7), (SI) (Beck Thm 5.24), sums of convex
functions (B&C Prop. 8.17) and the chain rule are PROVED here or in G3/H1–H3.

NOT FORMALISED: (R)'s "computed by a program from the oracle calls" (computability is not
modelled); the instantiation of `LeafSem` by the concrete leaf iterations of G3/H2/H3 and their
row lemmas (so the leaf rows of the typing table are interfaces in Theorem H5.9; the stitch row
is formalised concretely); the warm start of a stitch call (calls may start anywhere, above);
the hypotheses of `cor_a`–`cor_d` are not derived from a stitch execution; Lemma H5.4(a) validity of the
slice specification (regime A, (O2), (O3): landed lem:fb-obligations) beyond μ_E ≥ τ_l > 0;
Lemma H5.4(c) (a meta-statement, landed); Remarks H5.2a–c (Remark H5.2c is a [CLASSICAL?]
derivation); Theorem H5.11(d), (e) as separate statements (they are `closure_stitch` +
`aposteriori` and `soundness_pick`/`pick_*` read together) and its "is a certificate"
sentence; Proposition H5.12(d), (e) (landed instances: h2-prop:needed(b),
prop:h3-necessity(ii)); Remarks H5.13–H5.15.

Status tier: FORMALISED (statement + proof, no sorry) for every Lean name listed under
COVERAGE; Theorem H5.9 with the leaf rules as interface hypotheses and the stitch rule
discharged from H4. Axioms: only propext, Classical.choice, Quot.sound (see #print axioms at the end).
-/
import Mathlib
import OcfVerification.A1DescentLemma
import OcfVerification.G3SoundnessQuadratic
import OcfVerification.H1DiscretePick
import OcfVerification.H2InexactOracles
import OcfVerification.H3MultiNonsmooth
import OcfVerification.H4BlockStitching

namespace OCF.H5

open Set Filter Topology Finset OCF.A1 OCF.G3 OCF.H1 OCF.H2 OCF.H3

set_option linter.unusedSectionVars false

/-! ## §2 The composite report (Definition H5.1) and its certificate (Lemma H5.2) -/

section Report

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {N : Type*} [Fintype N]

/-- SC3: the declarations of a split target E = F + Σ_{j∈N} g_j: F ∈ C¹ (differentiable
suffices) with C(F, σ_F), σ_F ∈ ℝ; each g_j extended-valued (`g j` on `D j`, +∞ off it)
with C(g_j, σ_j), σ_j ≥ 0. -/
structure SplitTarget (F : X → ℝ) (σF : ℝ) (D : N → Set X) (g : N → X → ℝ) (σ : N → ℝ) :
    Prop where
  diffF : Differentiable ℝ F
  curvF : ModC F σF
  curv : ∀ j, ExtModC (D j) (g j) (σ j)
  sigma_nonneg : ∀ j, 0 ≤ σ j

/-- **Definition H5.1.** `(x̂, u, (v_j, ε_j)_j)` is a composite report for E: ε_j ≥ 0 and
v_j ∈ ∂_{ε_j} g_j(x̂) (H2's `EpsSubgrad`; so x̂ ∈ dom E); u is `uR F v x̂` below. -/
def IsReport (D : N → Set X) (g : N → X → ℝ) (xh : X) (v : N → X) (ε : N → ℝ) : Prop :=
  ∀ j, 0 ≤ ε j ∧ EpsSubgrad (D j) (g j) (ε j) xh (v j)

/-- u = ∇F(x̂) + Σ_j v_j. -/
noncomputable def uR (F : X → ℝ) (v : N → X) (xh : X) : X := gradient F xh + ∑ j, v j

/-- The accuracy ε = Σ_j ε_j. -/
def accR (ε : N → ℝ) : ℝ := ∑ j, ε j

open Classical in
/-- The exact set J = {j : ε_j = 0}. -/
noncomputable def exactSet (ε : N → ℝ) : Finset N := univ.filter (fun j => ε j = 0)

/-- μ_R = σ_F + Σ_{j∈J} σ_j (μ_E is H3's `muHat σF σ` = σ_F + Σ_N σ_j). -/
noncomputable def muR (σF : ℝ) (σ : N → ℝ) (ε : N → ℝ) : ℝ := σF + ∑ j ∈ exactSet ε, σ j

/-- s = μ_E + μ_R. -/
noncomputable def sR (σF : ℝ) (σ : N → ℝ) (ε : N → ℝ) : ℝ := muHat σF σ + muR σF σ ε

/-- τ_R = (b + √(b² + 2sε))/s, with b = ‖u‖. -/
noncomputable def tauR (b ε s : ℝ) : ℝ := (b + √(b ^ 2 + 2 * s * ε)) / s

/-- t̄ = τ if μ_R ≤ 0, min{τ, b/μ_R} otherwise. -/
noncomputable def tbar (b τ μ : ℝ) : ℝ := if μ ≤ 0 then τ else min τ (b / μ)

/-- G_R = ε + b t̄ − (μ_R/2) t̄². -/
noncomputable def GR (b ε μ τ : ℝ) : ℝ := ε + b * tbar b τ μ - μ / 2 * tbar b τ μ ^ 2

/-- The report's three scalars and the certificate quantities, from the report data. -/
noncomputable def tauRep (F : X → ℝ) (σF : ℝ) (σ : N → ℝ) (xh : X) (v : N → X) (ε : N → ℝ) :
    ℝ := tauR ‖uR F v xh‖ (accR ε) (sR σF σ ε)

noncomputable def GRep (F : X → ℝ) (σF : ℝ) (σ : N → ℝ) (xh : X) (v : N → X) (ε : N → ℝ) :
    ℝ := GR ‖uR F v xh‖ (accR ε) (muR σF σ ε) (tauRep F σF σ xh v ε)

/-- ℓ_R = E(x̂) − G_R. -/
noncomputable def ellRep (F : X → ℝ) (σF : ℝ) (g : N → X → ℝ) (σ : N → ℝ) (xh : X) (v : N → X)
    (ε : N → ℝ) : ℝ := Eval F g xh - GRep F σF σ xh v ε

variable {F : X → ℝ} {σF : ℝ} {D : N → Set X} {g : N → X → ℝ} {σ : N → ℝ}

lemma accR_nonneg {xh : X} {v : N → X} {ε : N → ℝ} (h : IsReport D g xh v ε) :
    0 ≤ accR ε := Finset.sum_nonneg fun j _ => (h j).1

lemma IsReport.mem {xh : X} {v : N → X} {ε : N → ℝ} (h : IsReport D g xh v ε) :
    xh ∈ domE D := fun j => (h j).2.1

lemma sum_exact_eq (σ ε : N → ℝ) :
    ∑ j ∈ exactSet ε, σ j = ∑ j, if ε j = 0 then σ j else 0 := by
  classical
  unfold exactSet
  rw [Finset.sum_filter]

/-- μ_R ≤ μ_E (every σ_j ≥ 0). -/
lemma muR_le_muE (hσ : ∀ j, 0 ≤ σ j) (ε : N → ℝ) : muR σF σ ε ≤ muHat σF σ := by
  unfold muR muHat
  have := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ (exactSet ε))
    (fun j _ _ => hσ j)
  linarith

/-- μ_R = μ_E when σ_j = 0 for every j outside J. -/
lemma muR_eq_of_sigma (ε : N → ℝ) (h : ∀ j, ε j ≠ 0 → σ j = 0) :
    muR σF σ ε = muHat σF σ := by
  unfold muR muHat
  rw [sum_exact_eq]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · exact (h j hj).symm

/-- μ_R = μ_E when the report is exact (ε = 0). -/
lemma muR_eq_of_acc_zero {xh : X} {v : N → X} {ε : N → ℝ} (h : IsReport D g xh v ε)
    (h0 : accR ε = 0) : muR σF σ ε = muHat σF σ := by
  have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => (h j).1)).1 h0
  exact muR_eq_of_sigma ε fun j hj => absurd (hall j (mem_univ j)) hj

/-- The per-term inequality: exact terms carry their modulus, inexact ones their ε_j. -/
lemma report_term (hT : SplitTarget F σF D g σ) {xh : X} {v : N → X} {ε : N → ℝ}
    (h : IsReport D g xh v ε) (j : N) {y : X} (hy : y ∈ D j) :
    g j xh + inner ℝ (v j) (y - xh) + (if ε j = 0 then σ j else 0) / 2 * ‖y - xh‖ ^ 2 - ε j
      ≤ g j y := by
  obtain ⟨hε, hs⟩ := h j
  split_ifs with h0
  · have hsub : ExtSub (D j) (g j) 0 xh (v j) :=
      ⟨hs.1, fun w hw => by have := hs.2 w hw; rw [h0] at this; simpa using this⟩
    have := (extSub_strong (hT.curv j) hsub).2 y hy
    rw [h0]; linarith
  · have := hs.2 y hy
    simp only [zero_div, zero_mul, add_zero]
    exact this

/-- **Lemma H5.2(a).** x̂ ∈ dom E and, for every y ∈ dom E (off dom E, E(y) = +∞),
E(y) ≥ E(x̂) + ⟨u, y − x̂⟩ + (μ_R/2)‖y − x̂‖² − ε. -/
theorem cert_a (hT : SplitTarget F σF D g σ) {xh : X} {v : N → X} {ε : N → ℝ}
    (h : IsReport D g xh v ε) :
    xh ∈ domE D ∧ ∀ y ∈ domE D,
      Eval F g xh + inner ℝ (uR F v xh) (y - xh) + muR σF σ ε / 2 * ‖y - xh‖ ^ 2 - accR ε
        ≤ Eval F g y := by
  refine ⟨h.mem, fun y hy => ?_⟩
  have hF := OCF.H1.strongSubgrad_of_modC hT.diffF hT.curvF xh y
  have hsum : ∑ j, (g j xh + inner ℝ (v j) (y - xh)
      + (if ε j = 0 then σ j else 0) / 2 * ‖y - xh‖ ^ 2 - ε j) ≤ ∑ j, g j y :=
    Finset.sum_le_sum fun j _ => report_term hT h j (hy j)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← sum_inner, ← Finset.sum_mul, ← Finset.sum_div, ← sum_exact_eq] at hsum
  unfold Eval uR muR accR
  rw [inner_add_left]
  linarith

/-- E − (μ_E/2)‖·‖² is convex on dom E (B&C Prop. 8.17; proved). -/
lemma extModC_Eval (hT : SplitTarget F σF D g σ) :
    ExtModC (domE D) (Eval F g) (muHat σF σ) := by
  classical
  have hconv : Convex ℝ (domE D) := by
    have : domE D = ⋂ j, D j := by ext y; simp [domE]
    rw [this]; exact convex_iInter fun j => (hT.curv j).1
  have hsum : ∀ s : Finset N, ConvexOn ℝ (domE D)
      (fun y => ∑ j ∈ s, (g j y - σ j / 2 * ‖y‖ ^ 2)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using convexOn_const (0 : ℝ) hconv
    | insert a s ha ih =>
      have ha' : ConvexOn ℝ (domE D) (fun y => g a y - σ a / 2 * ‖y‖ ^ 2) :=
        (hT.curv a).subset (fun y hy => hy a) hconv
      refine (ha'.add ih).congr fun y _ => ?_
      rw [Pi.add_apply, Finset.sum_insert ha]
  have hF : ConvexOn ℝ (domE D) (fun y => F y - σF / 2 * ‖y‖ ^ 2) :=
    hT.curvF.subset (subset_univ _) hconv
  refine ((hF.add (hsum univ))).congr fun y _ => ?_
  rw [Pi.add_apply]
  simp only [Eval, muHat, Finset.sum_sub_distrib, ← Finset.sum_mul, ← Finset.sum_div]
  ring

/-- x* minimises E over dom E. -/
def IsMinD (S : Set X) (E : X → ℝ) (xs : X) : Prop := xs ∈ S ∧ ∀ y ∈ S, E xs ≤ E y

/-- **Lemma H5.2(b).** If μ_E > 0 and x* is a minimiser of E (existence: B&C Cor. 11.17,
classical, a hypothesis as in H3), then x* is the only minimiser and
(μ_E/2)‖y − x*‖² ≤ E(y) − E(x*) on dom E (in particular at y = x̂). -/
theorem cert_b (hT : SplitTarget F σF D g σ) {xs : X} (hxs : IsMinD (domE D) (Eval F g) xs) :
    (∀ y ∈ domE D, muHat σF σ / 2 * ‖y - xs‖ ^ 2 ≤ Eval F g y - Eval F g xs) ∧
    (0 < muHat σF σ → ∀ y, IsMinD (domE D) (Eval F g) y ↔ y = xs) := by
  have h0 : ExtSub (domE D) (Eval F g) 0 xs 0 :=
    ⟨hxs.1, fun y hy => by simpa using hxs.2 y hy⟩
  have hs := extSub_strong (extModC_Eval hT) h0
  have hgr : ∀ y ∈ domE D, muHat σF σ / 2 * ‖y - xs‖ ^ 2 ≤ Eval F g y - Eval F g xs := by
    intro y hy
    have := hs.2 y hy
    simp only [inner_zero_left, add_zero] at this
    linarith
  refine ⟨hgr, fun hμ y => ⟨fun hy => ?_, fun e => e ▸ hxs⟩⟩
  have h1 := hgr y hy.1
  have h2 := hy.2 xs hxs.1
  have : ‖y - xs‖ ^ 2 ≤ 0 := by nlinarith
  have : ‖y - xs‖ = 0 := by nlinarith [norm_nonneg (y - xs)]
  exact sub_eq_zero.1 (norm_eq_zero.1 this)

/-- τ_R written as H3's larger root `tauC` with μ = s/2. -/
lemma tauR_eq_tauC (b ε s : ℝ) (hs : 0 < s) : tauR b ε s = tauC b ε (s / 2) := by
  unfold tauR tauC
  congr 1
  · ring_nf
  · ring

/-- Scalar core of (c): s/2 t² ≤ bt + ε ⇒ t ≤ τ_R ≤ 2b/s + √(2ε/s). -/
lemma scalar_c {b ε s t : ℝ} (hs : 0 < s) (hb : 0 ≤ b) (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (h : s / 2 * t ^ 2 ≤ b * t + ε) : t ≤ tauR b ε s ∧ tauR b ε s ≤ 2 * b / s + √(2 * ε / s) := by
  rw [tauR_eq_tauC b ε s hs]
  obtain ⟨h1, h2⟩ := quad_root (by linarith : 0 < s / 2) hb hε ht h
  refine ⟨h1, h2.trans (le_of_eq ?_)⟩
  congr 1
  · field_simp
  · congr 1; field_simp

/-- Scalar core of (d): for t ∈ [0, τ], bt − (μ/2)t² ≤ b t̄ − (μ/2)t̄². -/
lemma scalar_d {b μ τ t : ℝ} (hb : 0 ≤ b) (ht : 0 ≤ t) (htτ : t ≤ τ) :
    b * t - μ / 2 * t ^ 2 ≤ b * tbar b τ μ - μ / 2 * tbar b τ μ ^ 2 := by
  unfold tbar
  split_ifs with hμ
  · nlinarith [mul_nonneg (sub_nonneg.2 htτ) (add_nonneg ht (ht.trans htτ))]
  · push Not at hμ
    rcases le_total τ (b / μ) with hc | hc
    · rw [min_eq_left hc]
      have hb' : μ * τ ≤ b := by rwa [le_div_iff₀ hμ, mul_comm] at hc
      nlinarith [mul_nonneg (sub_nonneg.2 htτ) (sub_nonneg.2 hb'), mul_nonneg (sub_nonneg.2 htτ) hμ.le]
    · rw [min_eq_right hc]
      have e : b * (b / μ) - μ / 2 * (b / μ) ^ 2 - (b * t - μ / 2 * t ^ 2)
          = μ / 2 * (t - b / μ) ^ 2 := by field_simp; ring
      nlinarith [sq_nonneg (t - b / μ), mul_nonneg hμ.le (sq_nonneg (t - b / μ))]

/-- The equality case of (d): μ_R = μ_E = μ > 0 (so s = 2μ) gives t̄ = b/μ and
G_R = ε + b²/(2μ). -/
lemma scalar_d_eq {b ε μ : ℝ} (hμ : 0 < μ) (hb : 0 ≤ b) (hε : 0 ≤ ε) :
    tbar b (tauR b ε (μ + μ)) μ = b / μ ∧
      GR b ε μ (tauR b ε (μ + μ)) = ε + b ^ 2 / (2 * μ) := by
  have hτ : b / μ ≤ tauR b ε (μ + μ) := by
    unfold tauR
    have hs : b ≤ √(b ^ 2 + 2 * (μ + μ) * ε) :=
      Real.le_sqrt_of_sq_le (by nlinarith)
    rw [div_le_div_iff₀ hμ (by linarith)]
    nlinarith
  have ht : tbar b (tauR b ε (μ + μ)) μ = b / μ := by
    unfold tbar
    rw [if_neg (not_le.2 hμ), min_eq_right hτ]
  refine ⟨ht, ?_⟩
  unfold GR
  rw [ht]
  field_simp
  ring

/-- The equality case of Lemma H5.2(d) at the report level. -/
lemma GRep_eq_case {xh : X} {v : N → X} {ε : N → ℝ} (h : IsReport D g xh v ε)
    (hμ : 0 < muHat σF σ) (hEq : muR σF σ ε = muHat σF σ) :
    tbar ‖uR F v xh‖ (tauRep F σF σ xh v ε) (muR σF σ ε) = ‖uR F v xh‖ / muHat σF σ ∧
      GRep F σF σ xh v ε = accR ε + ‖uR F v xh‖ ^ 2 / (2 * muHat σF σ) := by
  have hsE : sR σF σ ε = muHat σF σ + muHat σF σ := by unfold sR; rw [hEq]
  unfold GRep tauRep
  rw [hsE, hEq]
  exact scalar_d_eq hμ (norm_nonneg _) (accR_nonneg h)

/-- **Lemma H5.2(b)–(d).** Split target, composite report, μ_E > 0, s > 0, x* a minimiser
(existence classical, hypothesis). Then:
(b) x* is the unique minimiser and (μ_E/2)‖x̂ − x*‖² ≤ E(x̂) − E(x*);
(c) ‖x̂ − x*‖ ≤ τ_R ≤ 2‖u‖/s + √(2ε/s);
(d) E(x̂) − E(x*) ≤ G_R, so ℓ_R ≤ min E = E(x*) ≤ E(x̂); and if μ_R = μ_E then
t̄ = ‖u‖/μ_E and G_R = ε + ‖u‖²/(2μ_E). -/
theorem lemma_H5_2 (hT : SplitTarget F σF D g σ) {xh : X} {v : N → X} {ε : N → ℝ}
    (h : IsReport D g xh v ε) (hμ : 0 < muHat σF σ) (hs : 0 < sR σF σ ε) {xs : X}
    (hxs : IsMinD (domE D) (Eval F g) xs) :
    ((∀ y, IsMinD (domE D) (Eval F g) y ↔ y = xs) ∧
      muHat σF σ / 2 * ‖xh - xs‖ ^ 2 ≤ Eval F g xh - Eval F g xs) ∧
    (‖xh - xs‖ ≤ tauRep F σF σ xh v ε ∧
      tauRep F σF σ xh v ε ≤ 2 * ‖uR F v xh‖ / sR σF σ ε + √(2 * accR ε / sR σF σ ε)) ∧
    (Eval F g xh - Eval F g xs ≤ GRep F σF σ xh v ε ∧
      ellRep F σF g σ xh v ε ≤ Eval F g xs ∧ Eval F g xs ≤ Eval F g xh ∧
      (muR σF σ ε = muHat σF σ →
        tbar ‖uR F v xh‖ (tauRep F σF σ xh v ε) (muR σF σ ε) = ‖uR F v xh‖ / muHat σF σ ∧
        GRep F σF σ xh v ε = accR ε + ‖uR F v xh‖ ^ 2 / (2 * muHat σF σ))) := by
  obtain ⟨hx, hM⟩ := cert_a hT h
  obtain ⟨hgr, huniq⟩ := cert_b hT hxs
  have hε := accR_nonneg h
  set u := uR F v xh
  set t := ‖xh - xs‖
  set μE := muHat σF σ
  set μR := muR σF σ ε
  have hb := hgr xh hx
  -- (a) at x* and Cauchy–Schwarz
  have hMs := hM xs hxs.1
  have hcs : -(‖u‖ * t) ≤ inner ℝ u (xs - xh) := by
    have := neg_le_of_abs_le (abs_real_inner_le_norm u (xs - xh))
    rwa [norm_sub_rev] at this
  rw [norm_sub_rev xs xh] at hMs
  have hgap : Eval F g xh - Eval F g xs ≤ ‖u‖ * t - μR / 2 * t ^ 2 + accR ε := by linarith
  have hq : sR σF σ ε / 2 * t ^ 2 ≤ ‖u‖ * t + accR ε := by
    unfold sR; nlinarith
  obtain ⟨hc1, hc2⟩ := scalar_c hs (norm_nonneg u) hε (norm_nonneg _) hq
  have hd := scalar_d (μ := μR) (norm_nonneg u) (norm_nonneg (xh - xs)) hc1
  have hG : Eval F g xh - Eval F g xs ≤ GRep F σF σ xh v ε := by
    unfold GRep GR tauRep; linarith
  refine ⟨⟨huniq hμ, hb⟩, ⟨hc1, hc2⟩, hG, ?_, ?_, fun hEq => ?_⟩
  · unfold ellRep; linarith
  · have := hxs.2 xh hx; exact this
  · exact GRep_eq_case h hμ hEq

end Report

/-! ### Lemma H5.2(e): the equality instances (on ℝ, one term, N = `Unit`) -/

section Instances

lemma sqrt_div_self {s ε : ℝ} (hs : 0 < s) (hε : 0 ≤ ε) : √(2 * s * ε) / s = √(2 * ε / s) := by
  rw [div_eq_iff hs.ne', show 2 * s * ε = s ^ 2 * (2 * ε / s) by field_simp,
    Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs.le]
  ring

lemma exactSet_unit_empty {ε : ℝ} (hε : ε ≠ 0) : exactSet (fun _ : Unit => ε) = ∅ := by
  classical
  unfold exactSet
  rw [Finset.filter_eq_empty_iff]
  intro _ _; exact hε

lemma muR_unit_inexact {σF s ε : ℝ} (hε : ε ≠ 0) :
    muR σF (fun _ : Unit => s) (fun _ : Unit => ε) = σF := by
  unfold muR; rw [exactSet_unit_empty hε, Finset.sum_empty, add_zero]

lemma muHat_unit (σF s : ℝ) : muHat σF (fun _ : Unit => s) = σF + s := by
  simp [muHat]

lemma accR_unit (ε : ℝ) : accR (fun _ : Unit => ε) = ε := by simp [accR]

/-- **Lemma H5.2(e1)** (distance attained with μ_R < μ_E; the instance of
h2-prop:next-gradient): F = 0, g = (s/2)x² on ℝ (σ_g = s > 0), ε > 0, x̂ = √(2ε/s), v = 0.
The report is valid, J = ∅, μ_R = 0 < μ_E = s = s_R, u = 0, x* = 0 and
‖x̂ − x*‖ = τ_R. -/
theorem cert_e1 {s ε : ℝ} (hs : 0 < s) (hε : 0 < ε) :
    SplitTarget (fun _ : ℝ => (0 : ℝ)) 0 (fun _ : Unit => univ) (fun _ => sqf s) (fun _ => s) ∧
    IsReport (fun _ : Unit => (univ : Set ℝ)) (fun _ => sqf s) (√(2 * ε / s)) (fun _ => 0)
      (fun _ => ε) ∧
    muR 0 (fun _ : Unit => s) (fun _ => ε) = 0 ∧
    muR 0 (fun _ : Unit => s) (fun _ => ε) < muHat 0 (fun _ : Unit => s) ∧
    sR 0 (fun _ : Unit => s) (fun _ => ε) = s ∧
    uR (fun _ : ℝ => (0 : ℝ)) (fun _ : Unit => (0 : ℝ)) (√(2 * ε / s)) = 0 ∧
    IsMinD (domE (fun _ : Unit => (univ : Set ℝ))) (Eval (fun _ => 0) (fun (_ : Unit) => sqf s)) 0 ∧
    ‖√(2 * ε / s) - 0‖
      = tauRep (fun _ : ℝ => (0 : ℝ)) 0 (fun _ : Unit => s) (√(2 * ε / s)) (fun _ => 0)
          (fun _ => ε) := by
  have hmuR := muR_unit_inexact (σF := 0) (s := s) hε.ne'
  have hu : uR (fun _ : ℝ => (0 : ℝ)) (fun _ : Unit => (0 : ℝ)) (√(2 * ε / s)) = 0 := by
    simp [uR]
  have hsR : sR 0 (fun _ : Unit => s) (fun _ => ε) = s := by
    unfold sR; rw [hmuR, muHat_unit]; ring
  refine ⟨⟨differentiable_const 0, ?_, fun _ => modC_sqf s, fun _ => hs.le⟩, fun _ => ⟨hε.le,
    mem_univ _, fun w _ => ?_⟩, hmuR, ?_, hsR, hu, ⟨fun _ => mem_univ _, fun y _ => ?_⟩, ?_⟩
  · unfold ModC; simpa using convexOn_const (0 : ℝ) convex_univ
  · simp only [sqf, inner_zero_left, add_zero, Real.norm_eq_abs, sq_abs]
    rw [Real.sq_sqrt (by positivity)]
    have : s / 2 * (2 * ε / s) = ε := by field_simp
    rw [this, sub_self]; positivity
  · rw [hmuR, muHat_unit]; linarith
  · simp only [Eval, sqf, Finset.univ_unique, Finset.sum_singleton, Real.norm_eq_abs, sq_abs]
    simp; positivity
  · unfold tauRep; rw [hu, hsR, accR_unit, norm_zero, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    unfold tauR
    rw [show (0 : ℝ) ^ 2 + 2 * s * ε = 2 * s * ε by ring, zero_add, sqrt_div_self hs hε.le]

/-- **Lemma H5.2(e2)** (distance attained with μ_R = μ_E; the distance instance of
h4-prop:cert(a)): F = (σ/2)x², g = ι_{[0,∞)} (the pair ([0,∞), 0), σ_g = 0), ε > 0,
x̂ = √(ε/σ), v = −√(σε). The report is valid, u = 0, μ_R = μ_E = σ, s_R = 2σ, x* = 0 and
‖x̂ − x*‖ = τ_R. -/
theorem cert_e2 {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε) :
    SplitTarget (sqf σ) σ (fun _ : Unit => Ici (0 : ℝ)) (fun _ _ => 0) (fun _ => 0) ∧
    IsReport (fun _ : Unit => Ici (0 : ℝ)) (fun _ _ => 0) (√(ε / σ)) (fun _ => -√(σ * ε))
      (fun _ => ε) ∧
    uR (sqf σ) (fun _ : Unit => -√(σ * ε)) (√(ε / σ)) = 0 ∧
    muR σ (fun _ : Unit => (0 : ℝ)) (fun _ => ε) = muHat σ (fun _ : Unit => (0 : ℝ)) ∧
    muHat σ (fun _ : Unit => (0 : ℝ)) = σ ∧
    sR σ (fun _ : Unit => (0 : ℝ)) (fun _ => ε) = 2 * σ ∧
    IsMinD (domE (fun _ : Unit => Ici (0 : ℝ))) (Eval (sqf σ) (fun (_ : Unit) _ => 0)) 0 ∧
    ‖√(ε / σ) - 0‖
      = tauRep (sqf σ) σ (fun _ : Unit => (0 : ℝ)) (√(ε / σ)) (fun _ => -√(σ * ε))
          (fun _ => ε) := by
  have hmuR : muR σ (fun _ : Unit => (0 : ℝ)) (fun _ => ε) = muHat σ (fun _ : Unit => (0 : ℝ)) :=
    muR_eq_of_sigma _ fun _ _ => rfl
  have hmu : muHat σ (fun _ : Unit => (0 : ℝ)) = σ := by rw [muHat_unit]; ring
  have hsR : sR σ (fun _ : Unit => (0 : ℝ)) (fun _ => ε) = 2 * σ := by
    unfold sR; rw [hmuR, hmu]; ring
  have hprod : √(σ * ε) * √(ε / σ) = ε := by
    rw [← Real.sqrt_mul (by positivity), show σ * ε * (ε / σ) = ε ^ 2 by field_simp,
      Real.sqrt_sq hε.le]
  have hsx : σ * √(ε / σ) = √(σ * ε) := by
    rw [show σ * ε = σ ^ 2 * (ε / σ) by field_simp, Real.sqrt_mul (sq_nonneg σ),
      Real.sqrt_sq hσ.le]
  have hu : uR (sqf σ) (fun _ : Unit => -√(σ * ε)) (√(ε / σ)) = 0 := by
    unfold uR; rw [gradient_sqf]; simp only [smul_eq_mul, Finset.univ_unique,
      Finset.sum_singleton]; rw [hsx]; ring
  refine ⟨⟨differentiable_sqf σ, modC_sqf σ, fun _ => ?_, fun _ => le_rfl⟩,
    fun _ => ⟨hε.le, Real.sqrt_nonneg _, fun w hw => ?_⟩, hu, hmuR, hmu, hsR,
    ⟨fun _ => self_mem_Ici, fun y hy => ?_⟩, ?_⟩
  · unfold ExtModC; simpa using convexOn_const (0 : ℝ) (convex_Ici (0 : ℝ))
  · have hw' : (0 : ℝ) ≤ w := hw
    have hi : inner ℝ (-√(σ * ε)) (w - √(ε / σ)) = -√(σ * ε) * (w - √(ε / σ)) := by
      simp; ring
    rw [hi]
    nlinarith [Real.sqrt_nonneg (σ * ε), mul_nonneg (Real.sqrt_nonneg (σ * ε)) hw']
  · simp only [Eval, sqf, Finset.univ_unique, Finset.sum_singleton, Real.norm_eq_abs, sq_abs]
    simp; positivity
  · unfold tauRep; rw [hu, hsR, accR_unit, norm_zero, sub_zero, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    unfold tauR
    rw [show (0 : ℝ) ^ 2 + 2 * (2 * σ) * ε = 2 * (2 * σ) * ε by ring, zero_add,
      sqrt_div_self (by linarith) hε.le]
    congr 1; field_simp

/-- **Lemma H5.2(e3)** (value attained; the value instance of h4-prop:cert(a)):
F = (σ/2)x², g = (ε/t)|·| (σ_g = 0), t > 0, ε > 0, x̂ = t, v = 0. The report is valid,
u = σt, μ_R = μ_E = σ, x* = 0 and E(x̂) − min E = G_R = ε + σt²/2. -/
theorem cert_e3 {σ ε t : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (ht : 0 < t) :
    SplitTarget (sqf σ) σ (fun _ : Unit => univ) (fun _ y => ε / t * |y|) (fun _ => 0) ∧
    IsReport (fun _ : Unit => (univ : Set ℝ)) (fun _ y => ε / t * |y|) t (fun _ => 0)
      (fun _ => ε) ∧
    uR (sqf σ) (fun _ : Unit => (0 : ℝ)) t = σ * t ∧
    muR σ (fun _ : Unit => (0 : ℝ)) (fun _ => ε) = muHat σ (fun _ : Unit => (0 : ℝ)) ∧
    IsMinD (domE (fun _ : Unit => (univ : Set ℝ))) (Eval (sqf σ) (fun (_ : Unit) y => ε / t * |y|)) 0 ∧
    Eval (sqf σ) (fun (_ : Unit) y => ε / t * |y|) t - Eval (sqf σ) (fun (_ : Unit) y => ε / t * |y|) 0
      = GRep (sqf σ) σ (fun _ : Unit => (0 : ℝ)) t (fun _ => 0) (fun _ => ε) ∧
    GRep (sqf σ) σ (fun _ : Unit => (0 : ℝ)) t (fun _ => 0) (fun _ => ε) = ε + σ * t ^ 2 / 2 := by
  have hmuR : muR σ (fun _ : Unit => (0 : ℝ)) (fun _ => ε) = muHat σ (fun _ : Unit => (0 : ℝ)) :=
    muR_eq_of_sigma _ fun _ _ => rfl
  have hmu : muHat σ (fun _ : Unit => (0 : ℝ)) = σ := by rw [muHat_unit]; ring
  have hu : uR (sqf σ) (fun _ : Unit => (0 : ℝ)) t = σ * t := by
    unfold uR; rw [gradient_sqf]; simp
  have hrep : IsReport (fun _ : Unit => (univ : Set ℝ)) (fun _ y => ε / t * |y|) t (fun _ => 0)
      (fun _ => ε) := fun _ => ⟨hε.le, mem_univ _, fun w _ => by
        simp only [inner_zero_left, add_zero, abs_of_pos ht]
        rw [div_mul_cancel₀ ε ht.ne', sub_self]; positivity⟩
  have hG : GRep (sqf σ) σ (fun _ : Unit => (0 : ℝ)) t (fun _ => 0) (fun _ => ε)
      = ε + σ * t ^ 2 / 2 := by
    have := (GRep_eq_case (F := sqf σ) hrep (by rw [hmu]; exact hσ) hmuR).2
    rw [this, hu, hmu, accR_unit, Real.norm_eq_abs, sq_abs]
    field_simp
  refine ⟨⟨differentiable_sqf σ, modC_sqf σ, fun _ => ?_, fun _ => le_rfl⟩, hrep, hu, hmuR,
    ⟨fun _ => mem_univ _, fun y _ => ?_⟩, ?_, hG⟩
  · unfold ExtModC
    have hc : ConvexOn ℝ univ (fun y : ℝ => (ε / t) • ‖y‖) :=
      (convexOn_norm convex_univ).smul (by positivity)
    refine hc.congr fun y _ => ?_
    simp only [smul_eq_mul, Real.norm_eq_abs, zero_div, zero_mul, sub_zero]
  · simp only [Eval, sqf, Finset.univ_unique, Finset.sum_singleton, Real.norm_eq_abs, sq_abs]
    simp; positivity
  · rw [hG]
    simp only [Eval, sqf, Finset.univ_unique, Finset.sum_singleton, Real.norm_eq_abs, sq_abs,
      abs_of_pos ht]
    simp
    field_simp
    ring

end Instances

/-! ## §3 Report closure (Lemma H5.3 = landing h5-lem:closure(a)–(d)) -/

section Closure

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

lemma uR_unit (F : X → ℝ) (v : X) (xh : X) : uR F (fun _ : Unit => v) xh = gradient F xh + v := by
  simp [uR]

/-- **Lemma H5.3(i) (fb, N = {j}).** One step of the constructed iteration,
x_{k+1} = prox_{αg}(x_k − α∇F(x_k)) (the exact inclusion (P) as hypothesis): with
R := R_α(x_k) = (x_k − x_{k+1})/α, v_k := R − ∇F(x_k), the triple
(x_{k+1}, u_k, (v_k, 0)) is a composite report, u_k = R − ∇F(x_k) + ∇F(x_{k+1}), J = N, and
‖u_k‖ ≤ 2‖R‖ when ∇F is β-Lipschitz and α = 1/β. No convexity is used. -/
theorem closure_fb {F : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ} (hα : 0 < α)
    (hL : LipGrad F β) (hαβ : α * β = 1) {xk xk1 : X}
    (hP : ProxEps D g α 0 (step F α xk) xk1) :
    IsReport (fun _ : Unit => D) (fun _ => g) xk1
        (fun _ => α⁻¹ • (xk - xk1) - gradient F xk) (fun _ => 0) ∧
    uR F (fun _ : Unit => α⁻¹ • (xk - xk1) - gradient F xk) xk1
        = α⁻¹ • (xk - xk1) - gradient F xk + gradient F xk1 ∧
    ‖uR F (fun _ : Unit => α⁻¹ • (xk - xk1) - gradient F xk) xk1‖ ≤ 2 * ‖α⁻¹ • (xk - xk1)‖ ∧
    exactSet (fun _ : Unit => (0 : ℝ)) = Finset.univ := by
  have hu : uR F (fun _ : Unit => α⁻¹ • (xk - xk1) - gradient F xk) xk1
      = α⁻¹ • (xk - xk1) - gradient F xk + gradient F xk1 := by rw [uR_unit]; abel
  refine ⟨fun _ => ⟨le_rfl, ?_⟩, hu, ?_, ?_⟩
  · have h := hP
    unfold ProxEps at h
    rwa [prox_vec_eq F hα.ne'] at h
  · rw [hu]
    have := prox_u_norm hα hL xk xk1
    rwa [hαβ, show (1 : ℝ) + 1 = 2 by norm_num] at this
  · classical
    unfold exactSet; ext j; simp

/-- **Lemma H5.3(i) (fb, N = ∅).** x_{k+1} = x_k − α∇F(x_k): (x_{k+1}, ∇F(x_{k+1})) is a
composite report of E = F (no terms, v_k = 0 = R_α(x_k) − ∇F(x_k)) with
‖∇F(x_{k+1})‖ ≤ 2‖R_α(x_k)‖. -/
theorem closure_fb_empty {F : X → ℝ} {α β : ℝ} (hα : 0 < α) (hL : LipGrad F β)
    (hαβ : α * β = 1) (xk : X) :
    IsReport (fun j : Empty => j.elim) (fun j : Empty => j.elim) (step F α xk) (fun j => j.elim)
      (fun j => j.elim) ∧
    uR F (fun j : Empty => j.elim) (step F α xk) = gradient F (step F α xk) ∧
    α⁻¹ • (xk - step F α xk) - gradient F xk = 0 ∧
    ‖gradient F (step F α xk)‖ ≤ 2 * ‖α⁻¹ • (xk - step F α xk)‖ := by
  have hR : α⁻¹ • (xk - step F α xk) = gradient F xk := by
    simp only [step, sub_sub_cancel, smul_smul, inv_mul_cancel₀ hα.ne', one_smul]
  refine ⟨fun j => j.elim, by simp [uR], by rw [hR, sub_self], ?_⟩
  have := prox_u_norm hα hL xk (step F α xk)
  rw [hR, sub_self, zero_add, hαβ] at this
  rw [hR]; linarith

/-- **Lemma H5.3(i), run form.** Every output of the constructed iteration
x_{k+1} = P(x_k − α∇F(x_k)) (P the exact prox, (P) as hypothesis) carries the report. -/
theorem closure_fb_run {F : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ} (hα : 0 < α)
    (hL : LipGrad F β) (hαβ : α * β = 1) {P : X → X} (hP : ∀ y, ProxEps D g α 0 y (P y))
    {x : ℕ → X} (hx : ∀ k, x (k + 1) = P (step F α (x k))) (k : ℕ) :
    IsReport (fun _ : Unit => D) (fun _ => g) (x (k + 1))
        (fun _ => rres α x k - gradient F (x k)) (fun _ => 0) ∧
    ‖uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))‖ ≤ 2 * ‖rres α x k‖ := by
  have h := closure_fb hα hL hαβ (xk := x k) (xk1 := x (k + 1)) (by rw [hx k]; exact hP _)
  exact ⟨h.1, h.2.2.1⟩

/-- **Lemma H5.3(ii) (inx).** In an inexact run (answers meeting their reported accuracies),
for every k, (x_{k+1}, u_k, (v_k, ε_k)) with v_k = r_k − ∇F(x_k) is a composite report,
u_k = r_k + ∇F(x_{k+1}) − ∇F(x_k), ‖u_k‖ ≤ 2‖r_k‖, and J = N iff ε_k = 0. -/
theorem closure_inx {F : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ} (hα : 0 < α)
    (hL : LipGrad F β) (hαβ : α * β = 1) {x : ℕ → X} {ε : ℕ → ℝ}
    (hr : InexactRun F D g α x ε) (k : ℕ) :
    IsReport (fun _ : Unit => D) (fun _ => g) (x (k + 1))
        (fun _ => rres α x k - gradient F (x k)) (fun _ => ε k) ∧
    uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))
        = rres α x k + gradient F (x (k + 1)) - gradient F (x k) ∧
    ‖uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))‖ ≤ 2 * ‖rres α x k‖ ∧
    (exactSet (fun _ : Unit => ε k) = Finset.univ ↔ ε k = 0) := by
  obtain ⟨hsub, hnorm⟩ := E2d_u hL hα hαβ hr k
  have hu : uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))
      = rres α x k + gradient F (x (k + 1)) - gradient F (x k) := by rw [uR_unit]; abel
  refine ⟨fun _ => ⟨(hr k).1, ?_⟩, hu, by rw [hu]; exact hnorm, ?_⟩
  · convert hsub using 1; abel_nf
  · classical
    unfold exactSet
    constructor
    · intro h
      have : () ∈ univ.filter (fun _ : Unit => ε k = 0) := by rw [h]; exact mem_univ _
      exact (Finset.mem_filter.1 this).2
    · intro h; ext j; simp [h]

/-- **Lemma H5.3(iii) (cons), point form.** Under H3's (H-cert) at x (v_j ∈ ∂g_j(p_j);
terms with p_j ≠ x real-valued with a Lipschitz attribute L_j), the tuple
(x, r, (v_j, ε_j)) with ε_j := (‖v_j‖ + L_j)‖p_j − x‖ is a composite report of
E = F + Σ_j g_j: u = r (H3's `resid`), ε = H3's `epsC`, every j with p_j = x is exact
(J ∋ j₀), and μ_R = μ_E = μ̂ (σ_j = 0 for Lipschitz terms, H3's `lipAttr_sigma_eq_zero`). -/
theorem closure_cons [Nontrivial X] {N : Type*} [Fintype N] {F : X → ℝ} {σF : ℝ}
    {D : N → Set X} {g : N → X → ℝ} {σ L : N → ℝ} {x : X} {p v : N → X}
    (h : HCert F σF D g σ L x p v) :
    SplitTarget F σF D g σ ∧
    IsReport D g x v (fun j => (‖v j‖ + L j) * ‖p j - x‖) ∧
    uR F v x = OCF.H3.resid F v x ∧
    accR (fun j => (‖v j‖ + L j) * ‖p j - x‖) = epsC x p v L ∧
    (∀ j, p j = x → j ∈ exactSet (fun j => (‖v j‖ + L j) * ‖p j - x‖)) ∧
    muR σF σ (fun j => (‖v j‖ + L j) * ‖p j - x‖) = muHat σF σ := by
  classical
  have hx := (consensus_minorant h).1
  refine ⟨⟨h.diffF, h.curvF, h.curv, h.sigma_nonneg⟩, fun j => ⟨?_, hx j, fun y hy => ?_⟩,
    rfl, (epsC_eq_sum x p v L).symm, fun j hj => ?_, ?_⟩
  · show 0 ≤ (‖v j‖ + L j) * ‖p j - x‖
    by_cases hj : p j = x
    · rw [hj, sub_self, norm_zero, mul_zero]
    · have := (h.lip j hj).2.1; positivity
  · have := h.term j hy
    nlinarith [mul_nonneg (h.sigma_nonneg j) (sq_nonneg ‖y - x‖)]
  · unfold exactSet; simp [hj]
  · refine muR_eq_of_sigma _ fun j hj => ?_
    have hpj : p j ≠ x := fun e => hj (by rw [e, sub_self, norm_zero, mul_zero])
    obtain ⟨hD, hL⟩ := h.lip j hpj
    have hC : ModC (g j) (σ j) := by have := h.curv j; rwa [hD] at this
    exact lipAttr_sigma_eq_zero hL hC (h.sigma_nonneg j)

/-- **Lemma H5.3(iii) (cons), iteration form.** For consensus-typed data (H3's `Typed`),
at every state z the read-outs give a composite report at x_k for
E = F + g_{j₀} + Σ_{N'} g_j (indexed by `Option ι`, j₀ = `none`) with u = r_k,
ε = ε_k (H3's `epsIt`), j₀ exact, μ_R = μ_E = μ̂, ‖r_k‖ ≤ e_k/(α√m') and ε_k ≤ 2‖L‖e_k. -/
theorem closure_cons_iter [Nontrivial X] {ι : Type*} [Fintype ι] [Nonempty ι]
    {C : ConsIter X ι} {σF σ0 : ℝ} {D0 : Set X} {g0 : X → ℝ} {gj : ι → X → ℝ} {σj Lj : ι → ℝ}
    (h : C.Typed σF σ0 D0 g0 gj σj Lj) (hα : 0 < C.α) (z : ι → X) :
    let D : Option ι → Set X := fun o => o.elim D0 (fun _ => univ)
    let g : Option ι → X → ℝ := fun o => o.elim g0 gj
    let σ : Option ι → ℝ := fun o => o.elim σ0 σj
    let v : Option ι → X := fun o => o.elim (C.v0 z) (C.v z)
    let ε : Option ι → ℝ := fun o =>
      (‖v o‖ + o.elim 0 Lj) * ‖(o.elim (C.x z) (C.p z)) - C.x z‖
    SplitTarget C.F σF D g σ ∧ IsReport D g (C.x z) v ε ∧ uR C.F v (C.x z) = C.r z ∧
      accR ε = C.epsIt Lj z ∧ none ∈ exactSet ε ∧ muR σF σ ε = muHat σF σ ∧
      ‖C.r z‖ ≤ C.e z / (C.α * √(ConsIter.mP ι)) ∧ C.epsIt Lj z ≤ 2 * ConsIter.normL Lj * C.e z := by
  intro D g σ v ε
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := closure_cons (h.hcert z)
  refine ⟨h1, h2, ?_, ?_, h5 none rfl, h6, (ConsIter.readout_bounds hα z).2.2,
    ConsIter.epsIt_le h hα z⟩
  · rw [h3]; exact ConsIter.resid_opt z
  · rw [h4]; exact ConsIter.epsC_opt z

end Closure

/-! ### Lemma H5.3(iv) (stitch): block terms composed with the block maps -/

section Stitch

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {B : Type*} [Fintype B] {Y : B → Type*} [∀ l, NormedAddCommGroup (Y l)]
  [∀ l, InnerProductSpace ℝ (Y l)] [∀ l, CompleteSpace (Y l)]

/-- An ε-subgradient moves through a linear map with its adjoint:
v ∈ ∂_ε g(Px) ⇒ U v ∈ ∂_ε (g ∘ P)(x) when ⟨U y, w⟩ = ⟨y, P w⟩ (U = Pᵀ). -/
lemma epsSubgrad_comp {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [CompleteSpace Z] (P : X →L[ℝ] Z) (U : Z →L[ℝ] X)
    (hadj : ∀ y w, inner ℝ (U y) w = inner ℝ y (P w)) {D : Set Z} {g : Z → ℝ} {ε : ℝ} {x : X}
    {v : Z} (h : EpsSubgrad D g ε (P x) v) :
    EpsSubgrad (P ⁻¹' D) (fun y => g (P y)) ε x (U v) := by
  refine ⟨h.1, fun w hw => ?_⟩
  have := h.2 (P w) hw
  rw [hadj, map_sub]
  exact this

/-- The declared modulus 0 of g ∘ P is valid (lem:rule-affine(b)): convexity is preserved. -/
lemma extModC_comp {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    (P : X →L[ℝ] Z) {D : Set Z} {g : Z → ℝ} (h : ExtModC D g 0) :
    ExtModC (P ⁻¹' D) (fun y => g (P y)) 0 := by
  unfold ExtModC at *
  have h' : ConvexOn ℝ D g := h.congr fun y _ => by simp
  have := h'.comp_linearMap P.toLinearMap
  exact this.congr fun y _ => by simp

/-- **Lemma H5.3(iv) (stitch).** Block maps P_l = U_lᵀ : ℝ^d → ℝ^{d_l} and embeddings U_l
(adjoint pairs), block terms g_{l,i} (`gl l i` on `Dl l i`) with block reports split over
the terms, v_{l,i} ∈ ∂_{ε_{l,i}} g_{l,i}(z_l), at a point x' with P_l x' = z_l for every l
(block l is not moved after its turn). Regard E as the split target with smooth part F,
σ_F := σ and terms g_{l,i} ∘ P_l declared with modulus 0 (index set Σ_l N_l). Then
(x', u, (U_l v_{l,i}, ε_{l,i})) is a composite report with u = ∇F(x') + Σ_l U_l v_l
(v_l = Σ_i v_{l,i}; one gradient of F), ε = Σ_l Σ_i ε_{l,i} and μ_R = μ_E = σ. -/
theorem closure_stitch (P : ∀ l, X →L[ℝ] Y l) (U : ∀ l, Y l →L[ℝ] X)
    (hadj : ∀ l y w, inner ℝ (U l y) w = inner ℝ y (P l w))
    {I : B → Type*} [∀ l, Fintype (I l)] {Dl : ∀ l, I l → Set (Y l)} {gl : ∀ l, I l → Y l → ℝ}
    {F : X → ℝ} {σ : ℝ} (hF : Differentiable ℝ F) (hC : ModC F σ)
    (hg : ∀ l i, ExtModC (Dl l i) (gl l i) 0)
    {x' : X} {z : ∀ l, Y l} (hz : ∀ l, P l x' = z l) {v : ∀ l, I l → Y l} {ε : ∀ l, I l → ℝ}
    (hv : ∀ l i, 0 ≤ ε l i ∧ EpsSubgrad (Dl l i) (gl l i) (ε l i) (z l) (v l i)) :
    SplitTarget F σ (fun j : (Σ l, I l) => P j.1 ⁻¹' Dl j.1 j.2)
      (fun j y => gl j.1 j.2 (P j.1 y)) (fun _ => 0) ∧
    IsReport (fun j : (Σ l, I l) => P j.1 ⁻¹' Dl j.1 j.2) (fun j y => gl j.1 j.2 (P j.1 y)) x'
      (fun j => U j.1 (v j.1 j.2)) (fun j => ε j.1 j.2) ∧
    uR F (fun j : (Σ l, I l) => U j.1 (v j.1 j.2)) x' = gradient F x' + ∑ l, U l (∑ i, v l i) ∧
    accR (fun j : (Σ l, I l) => ε j.1 j.2) = ∑ l, ∑ i, ε l i ∧
    muR σ (fun _ : (Σ l, I l) => (0 : ℝ)) (fun j => ε j.1 j.2)
      = muHat σ (fun _ : (Σ l, I l) => (0 : ℝ)) ∧
    muHat σ (fun _ : (Σ l, I l) => (0 : ℝ)) = σ := by
  refine ⟨⟨hF, hC, fun j => extModC_comp (P j.1) (hg j.1 j.2), fun _ => le_rfl⟩,
    fun j => ⟨(hv j.1 j.2).1, epsSubgrad_comp (P j.1) (U j.1) (hadj j.1) ?_⟩, ?_, ?_,
    muR_eq_of_sigma _ fun _ _ => rfl, by simp [muHat]⟩
  · rw [hz]; exact (hv j.1 j.2).2
  · unfold uR; rw [Fintype.sum_sigma]; simp only [map_sum]
  · unfold accR; rw [Fintype.sum_sigma]

end Stitch

/-! ## §4 Interfaces (Lemma H5.4 = landing h5-lem:closure(e),(f) and the pick interface) -/

section Interfaces

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

/-- The chain rule for the slice φ_x(y) = F(x + U(y − Px)) (U = Pᵀ):
∇φ_x(y) = P ∇F(x + U(y − Px)) = ∇_l F at the block output. -/
lemma hasGradientAt_sliceP {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (P : X →L[ℝ] Y) (U : Y →L[ℝ] X)
    (hadj : ∀ y w, inner ℝ (U y) w = inner ℝ y (P w)) {F : X → ℝ} (hF : Differentiable ℝ F)
    (x : X) (y : Y) :
    HasGradientAt (fun y => F (x + U (y - P x))) (P (gradient F (x + U (y - P x)))) y := by
  have hA : HasFDerivAt (fun y : Y => x + U (y - P x)) U y := by
    have e : (fun y : Y => x + U (y - P x)) = fun y => x + (U y - U (P x)) := by
      funext y; simp [map_sub]
    rw [e]
    exact (U.hasFDerivAt.sub_const _).const_add x
  have hc := (hF (x + U (y - P x))).hasFDerivAt.comp y hA
  have hL : InnerProductSpace.toDual ℝ Y (P (gradient F (x + U (y - P x))))
      = (fderiv ℝ F (x + U (y - P x))).comp U := by
    ext k
    simp only [ContinuousLinearMap.comp_apply, InnerProductSpace.toDual_apply_apply]
    rw [real_inner_comm, ← hadj, real_inner_comm,
      ← InnerProductSpace.toDual_apply_apply (𝕜 := ℝ), gradient,
      LinearIsometryEquiv.apply_symm_apply]
  rw [hasGradientAt_iff_hasFDerivAt, hL]
  exact hc

/-- Summing ε_i-subgradients of the terms gives an (Σ ε_i)-subgradient of their sum. -/
lemma epsSubgrad_sum {I : Type*} [Fintype I] {Y : Type*} [NormedAddCommGroup Y]
    [InnerProductSpace ℝ Y] [CompleteSpace Y] {D : I → Set Y} {g : I → Y → ℝ} {z : Y}
    {v : I → Y} {ε : I → ℝ} (h : IsReport D g z v ε) :
    EpsSubgrad (domE D) (fun y => ∑ i, g i y) (accR ε) z (∑ i, v i) := by
  refine ⟨h.mem, fun w hw => ?_⟩
  have hs : ∑ i, (g i z + inner ℝ (v i) (w - z) - ε i) ≤ ∑ i, g i w :=
    Finset.sum_le_sum fun i _ => (h i).2.2 w (hw i)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← sum_inner] at hs
  unfold accR
  linarith

/-- **Lemma H5.4(a) (slice report = block report; landing h5-lem:closure(e)).** A composite
report (z, u, (v_i, ε_i)_i) of the slice target φ_x + Σ_i g_{l,i} (smooth part
φ_x(y) = F(x + U(y − Px))) gives the block report (z, Σ_i v_i, Σ_i ε_i) of h4-def:report:
Σ_i v_i ∈ ∂_{Σε_i} g_l(z), g_l = Σ_i g_{l,i}, and its residual
η = ‖∇_l F(x') + Σ_i v_i‖ (x' = x + U(z − Px) the block output, ∇_l F = P∇F) equals ‖u‖. -/
theorem slice_report_block {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] (P : X →L[ℝ] Y) (U : Y →L[ℝ] X)
    (hadj : ∀ y w, inner ℝ (U y) w = inner ℝ y (P w)) {F : X → ℝ} (hF : Differentiable ℝ F)
    (x : X) {I : Type*} [Fintype I] {D : I → Set Y} {g : I → Y → ℝ} {z : Y} {v : I → Y}
    {ε : I → ℝ} (h : IsReport D g z v ε) :
    EpsSubgrad (domE D) (fun y => ∑ i, g i y) (accR ε) z (∑ i, v i) ∧
    uR (fun y => F (x + U (y - P x))) v z = P (gradient F (x + U (z - P x))) + ∑ i, v i ∧
    ‖P (gradient F (x + U (z - P x))) + ∑ i, v i‖ = ‖uR (fun y => F (x + U (y - P x))) v z‖ := by
  have hu : uR (fun y => F (x + U (y - P x))) v z = P (gradient F (x + U (z - P x))) + ∑ i, v i := by
    unfold uR; rw [(hasGradientAt_sliceP P U hadj hF x z).gradient]
  exact ⟨epsSubgrad_sum h, hu, by rw [hu]⟩

/-- The slice is in regime A: with declared slice modulus τ > 0 and term moduli σ_i ≥ 0,
μ_E ≥ τ > 0 and s ≥ 2τ > 0, so Lemma H5.2 certifies every slice report. -/
lemma slice_moduli_pos {I : Type*} [Fintype I] {τ : ℝ} (hτ : 0 < τ) {σ : I → ℝ}
    (hσ : ∀ i, 0 ≤ σ i) (ε : I → ℝ) : τ ≤ muHat τ σ ∧ 0 < muHat τ σ ∧ 0 < sR τ σ ε := by
  have h1 : τ ≤ muHat τ σ := by
    have := Finset.sum_nonneg (s := Finset.univ) fun i _ => hσ i
    unfold muHat; linarith
  have h2 : τ ≤ muR τ σ ε := by
    have := Finset.sum_nonneg (s := exactSet ε) fun i _ => hσ i
    unfold muR; linarith
  exact ⟨h1, by linarith, by unfold sR; linarith⟩

/-- ∇(σ/2 ‖· − y‖²)(w) = σ(w − y). -/
lemma hasGradientAt_sqf_sub (σ : ℝ) (y w : X) :
    HasGradientAt (fun w => sqf σ (w - y)) (σ • (w - y)) w := by
  have h := (hasGradientAt_sqf σ (w - y))
  rw [hasGradientAt_iff_hasFDerivAt] at h ⊢
  have h2 := h.comp w ((hasFDerivAt_id w).sub_const y)
  have e : InnerProductSpace.toDual ℝ X (σ • (w - y))
      = (InnerProductSpace.toDual ℝ X (σ • (w - y))).comp (ContinuousLinearMap.id ℝ X) := by
    ext; simp
  rw [e]; exact h2

/-- **Lemma H5.4(d) (prox-subproblem reports; landing h5-lem:closure(f)).** For
Φ_y = g + ‖· − y‖²/(2α) regarded as a split target (smooth part
q_y = sqf α⁻¹ (· − y) = ‖· − y‖²/(2α), one term g), α > 0, ε ≥ 0:
(z, u, (v, ε)) is a composite report of Φ_y iff z ∈ prox^ε_{αg}(y + αu) and
v = (y + αu − z)/α. -/
theorem prox_report_iff {D : Set X} {g : X → ℝ} {α ε : ℝ} (hα : 0 < α) (hε : 0 ≤ ε)
    (y z u v : X) :
    (IsReport (fun _ : Unit => D) (fun _ => g) z (fun _ => v) (fun _ => ε) ∧
      uR (fun w => sqf α⁻¹ (w - y)) (fun _ : Unit => v) z = u) ↔
    (ProxEps D g α ε (y + α • u) z ∧ v = α⁻¹ • (y + α • u - z)) := by
  have hu : uR (fun w => sqf α⁻¹ (w - y)) (fun _ : Unit => v) z = α⁻¹ • (z - y) + v := by
    rw [uR_unit, (hasGradientAt_sqf_sub α⁻¹ y z).gradient]
  have hv : (α⁻¹ • (z - y) + v = u) ↔ v = α⁻¹ • (y + α • u - z) := by
    have e : α⁻¹ • (y + α • u - z) = u - α⁻¹ • (z - y) := by
      rw [show y + α • u - z = α • u - (z - y) by abel, smul_sub, smul_smul,
        inv_mul_cancel₀ hα.ne', one_smul]
    rw [e]
    constructor
    · intro h; rw [← h]; abel
    · intro h; rw [h]; abel
  rw [hu, hv]
  constructor
  · rintro ⟨hr, hv'⟩
    refine ⟨?_, hv'⟩
    unfold ProxEps; rw [← hv']; exact (hr ()).2
  · rintro ⟨hp, hv'⟩
    refine ⟨fun _ => ⟨hε, ?_⟩, hv'⟩
    rw [hv']; exact hp

/-- ∂_ε 0(z) = {0} (sentence before h2-lem:one-step). -/
lemma epsSubgrad_zero_fun {ε : ℝ} {z w : X} (h : EpsSubgrad univ (fun _ => (0 : ℝ)) ε z w) :
    w = 0 := by
  by_contra hw
  have hpos : 0 < ‖w‖ ^ 2 := by positivity
  have hε : 0 ≤ ε := by have := h.2 z (mem_univ _); simp at this; linarith
  have := h.2 (z + ((ε + 1) / ‖w‖ ^ 2) • w) (mem_univ _)
  rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq,
    div_mul_cancel₀ _ hpos.ne'] at this
  linarith

/-- **Lemma H5.4(d), last sentence.** For g = 0, a report of Φ_y with u ≠ 0 is not an
answer z ∈ prox^{ε'}_{α·0}(y) for any ε' ≥ 0 (such an answer forces z = y, while the report
has u = (z − y)/α). -/
theorem prox_report_not_answer {α ε : ℝ} (hα : 0 < α) {y z u v : X}
    (hr : IsReport (fun _ : Unit => (univ : Set X)) (fun _ _ => (0 : ℝ)) z (fun _ => v)
      (fun _ => ε))
    (hu : uR (fun w => sqf α⁻¹ (w - y)) (fun _ : Unit => v) z = u) (hu0 : u ≠ 0) (ε' : ℝ) :
    ¬ ProxEps univ (fun _ => (0 : ℝ)) α ε' y z := by
  intro hp
  have hv0 : v = 0 := epsSubgrad_zero_fun (hr ()).2
  have hz : α⁻¹ • (y - z) = 0 := epsSubgrad_zero_fun hp
  rw [uR_unit, (hasGradientAt_sqf_sub α⁻¹ y z).gradient, hv0, add_zero] at hu
  apply hu0
  rw [← hu, show z - y = -(y - z) by abel, smul_neg, hz, neg_zero]

end Interfaces

/-! ### Lemma H5.4(b): a report is a bracket, and thm:h1-pick holds with these brackets

H1's Lean formalisation of thm:h1-pick (`thm_H1_4_a`–`thm_H1_4_e`) takes real-valued blocks
E_z : X_z → ℝ. The targets here are extended-valued (`E z` on `D z`, +∞ off it), so the
pick conclusions are re-derived below in the extended encoding from H1's scalar pruning
lemmas (`pruning_optimal`, `pruning_unique`, `rival_ge`, `minOver_L_eq_of_margin`): exactly
the facts the proof of thm:h1-pick uses (uniqueness, L_z ≤ v(z) ≤ U_z, ‖x̂_z − x*_z‖ ≤ ρ_z). -/

section Pick

/-- The facts a pick uses from a choice: x̂ ∈ dom E, E has a minimiser x* on dom E, it is the
only one, L ≤ E(x*) and ‖x̂ − x*‖ ≤ ρ. (U = E(x̂).) -/
def ExtBracket {Y : Type*} [NormedAddCommGroup Y] (S : Set Y) (E : Y → ℝ) (xh : Y)
    (L ρ : ℝ) : Prop :=
  xh ∈ S ∧ ∃ xs, IsMinD S E xs ∧ (∀ y, IsMinD S E y ↔ y = xs) ∧ L ≤ E xs ∧ ‖xh - xs‖ ≤ ρ

/-- **Lemma H5.4(b), bracket part.** A composite report with μ_E > 0 and s > 0 gives the
bracket (L, U, ρ) = (ℓ_R, E(x̂), τ_R) (x* a minimiser; existence classical, hypothesis). -/
theorem report_bracket {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [CompleteSpace X] {N : Type*} [Fintype N] {F : X → ℝ} {σF : ℝ} {D : N → Set X}
    {g : N → X → ℝ} {σ : N → ℝ} (hT : SplitTarget F σF D g σ) {xh : X} {v : N → X}
    {ε : N → ℝ} (h : IsReport D g xh v ε) (hμ : 0 < muHat σF σ) (hs : 0 < sR σF σ ε)
    {xs : X} (hxs : IsMinD (domE D) (Eval F g) xs) :
    ExtBracket (domE D) (Eval F g) xh (ellRep F σF g σ xh v ε) (tauRep F σF σ xh v ε) := by
  obtain ⟨⟨hu, -⟩, ⟨hc, -⟩, ⟨-, hl, -, -⟩⟩ := lemma_H5_2 hT h hμ hs hxs
  exact ⟨h.mem, xs, hxs, hu, hl, hc⟩

variable {Z : Type*} [Fintype Z] [DecidableEq Z] {X : Z → Type*}
  [∀ z, NormedAddCommGroup (X z)]

/-- (z, x) minimises the extended hybrid energy E_hyb(z, x) = E_z(x) (+∞ off dom E_z). -/
def HybMin (D : ∀ z, Set (X z)) (E : ∀ z, X z → ℝ) (p : Σ z, X z) : Prop :=
  p.2 ∈ D p.1 ∧ ∀ q : Σ z, X z, q.2 ∈ D q.1 → E p.1 p.2 ≤ E q.1 q.2

variable (D : ∀ z, Set (X z)) (E : ∀ z, X z → ℝ) (xh : ∀ z, X z) (L ρ : Z → ℝ)
  (xs : ∀ z, X z)

lemma brackets_HB (hB : ∀ z, ExtBracket (D z) (E z) (xh z) (L z) (ρ z))
    (hxs : ∀ z, IsMinD (D z) (E z) (xs z)) :
    ∀ z, L z ≤ E z (xs z) ∧ E z (xs z) ≤ E z (xh z) := by
  intro z
  obtain ⟨hxh, y, -, hu, hL, -⟩ := hB z
  have : xs z = y := (hu (xs z)).1 (hxs z)
  exact ⟨this ▸ hL, (hxs z).2 _ hxh⟩

/-- **thm:h1-pick (a), extended.** Every choice has exactly one minimiser x*_z and
L_z ≤ v(z) ≤ U_z, v(z) := E_z(x*_z). -/
theorem pick_a (hB : ∀ z, ExtBracket (D z) (E z) (xh z) (L z) (ρ z)) (z : Z) :
    ∃ y, IsMinD (D z) (E z) y ∧ (∀ y', IsMinD (D z) (E z) y' ↔ y' = y) ∧
      L z ≤ E z y ∧ E z y ≤ E z (xh z) := by
  obtain ⟨hxh, y, hy, hu, hL, -⟩ := hB z
  exact ⟨y, hy, hu, hL, hy.2 _ hxh⟩

/-- **thm:h1-pick (b), extended (always issued).** v* := min_z v(z) is the infimum of the
hybrid problem, attained; E_hyb(ẑ, x̂_ẑ) − v* ≤ U_ẑ − min_z L_z and ‖x̂_ẑ − x*_ẑ‖ ≤ ρ_ẑ. -/
theorem pick_b [Nonempty Z] (hB : ∀ z, ExtBracket (D z) (E z) (xh z) (L z) (ρ z))
    (hxs : ∀ z, IsMinD (D z) (E z) (xs z)) (zh : Z) :
    (∀ q : Σ z, X z, q.2 ∈ D q.1 → minOver (fun z => E z (xs z)) ≤ E q.1 q.2) ∧
    (∃ z, HybMin D E ⟨z, xs z⟩ ∧ E z (xs z) = minOver (fun z => E z (xs z))) ∧
    E zh (xh zh) - minOver (fun z => E z (xs z)) ≤ E zh (xh zh) - minOver L ∧
    ‖xh zh - xs zh‖ ≤ ρ zh := by
  have HB := brackets_HB D E xh L ρ xs hB hxs
  have hlow : ∀ q : Σ z, X z, q.2 ∈ D q.1 → minOver (fun z => E z (xs z)) ≤ E q.1 q.2 :=
    fun q hq => (minOver_le _ q.1).trans ((hxs q.1).2 _ hq)
  refine ⟨hlow, ?_, ?_, ?_⟩
  · obtain ⟨z0, hz0⟩ := exists_minOver_eq (fun z => E z (xs z))
    exact ⟨z0, ⟨(hxs z0).1, fun q hq => hz0 ▸ hlow q hq⟩, hz0.symm⟩
  · have : minOver L ≤ minOver (fun z => E z (xs z)) :=
      le_minOver fun z => (minOver_le L z).trans (HB z).1
    linarith
  · obtain ⟨-, y, -, hu, -, hd⟩ := hB zh
    rwa [(hu (xs zh)).1 (hxs zh)]

/-- **thm:h1-pick (c), extended.** If |𝒵| = 1 or 𝔪 ≥ 0: ẑ is an optimal pick, (ẑ, x*_ẑ)
minimises the hybrid problem, and E_hyb(ẑ, x̂_ẑ) − v* ≤ U_ẑ − L_ẑ. -/
theorem pick_c [Nonempty Z] (hB : ∀ z, ExtBracket (D z) (E z) (xh z) (L z) (ρ z))
    (hxs : ∀ z, IsMinD (D z) (E z) (xs z)) (zh : Z)
    (hm : MarginNonneg L (fun z => E z (xh z)) zh) :
    E zh (xs zh) = minOver (fun z => E z (xs z)) ∧ HybMin D E ⟨zh, xs zh⟩ ∧
      E zh (xh zh) - minOver (fun z => E z (xs z)) ≤ E zh (xh zh) - L zh := by
  have HB := brackets_HB D E xh L ρ xs hB hxs
  have hopt : E zh (xs zh) = minOver (fun z => E z (xs z)) := by
    rcases hm with h1 | ⟨hZ, hm⟩
    · exact (minOver_eq_of_forall_le (f := fun z => E z (xs z))
        fun z => by rw [eq_of_card_one h1 z zh]).symm
    · exact pruning_optimal hZ HB hm
  refine ⟨hopt, ⟨(hxs zh).1, fun q hq => ?_⟩, ?_⟩
  · rw [hopt]; exact (minOver_le _ q.1).trans ((hxs q.1).2 _ hq)
  · rw [← hopt]; linarith [(HB zh).1]

/-- **thm:h1-pick (d), extended.** If |𝒵| = 1 or 𝔪 > 0: ẑ is the unique optimal pick
(v(z) > v* for z ≠ ẑ), the hybrid problem has exactly one minimiser (ẑ, x*_ẑ), and
‖x̂_ẑ − x*_ẑ‖ ≤ ρ_ẑ. -/
theorem pick_d [Nonempty Z] (hB : ∀ z, ExtBracket (D z) (E z) (xh z) (L z) (ρ z))
    (hxs : ∀ z, IsMinD (D z) (E z) (xs z)) (zh : Z)
    (hm : MarginPos L (fun z => E z (xh z)) zh) :
    E zh (xs zh) = minOver (fun z => E z (xs z)) ∧
    (∀ z, z ≠ zh → minOver (fun z => E z (xs z)) < E z (xs z)) ∧
    (∀ p : Σ z, X z, HybMin D E p ↔ p = ⟨zh, xs zh⟩) ∧ ‖xh zh - xs zh‖ ≤ ρ zh := by
  have HB := brackets_HB D E xh L ρ xs hB hxs
  have hc := pick_c D E xh L ρ xs hB hxs zh (by
    rcases hm with h1 | ⟨hZ, hm⟩
    · exact Or.inl h1
    · exact Or.inr ⟨hZ, hm.le⟩)
  have hstrict : ∀ z, z ≠ zh → minOver (fun z => E z (xs z)) < E z (xs z) := by
    intro z hz
    rcases hm with h1 | ⟨hZ, hm⟩
    · exact absurd (eq_of_card_one h1 z zh) hz
    · exact (pruning_unique hZ HB hm).2.1 z hz
  refine ⟨hc.1, hstrict, fun p => ⟨fun hp => ?_, fun e => e ▸ hc.2.1⟩,
    (pick_b D E xh L ρ xs hB hxs zh).2.2.2⟩
  obtain ⟨z, x⟩ := p
  obtain ⟨hxD, hle⟩ := hp
  have h1 : E z x ≤ E zh (xs zh) := hle ⟨zh, xs zh⟩ (hxs zh).1
  by_cases hz : z = zh
  · subst hz
    have hmin : IsMinD (D z) (E z) x := ⟨hxD, fun w hw => hle ⟨z, w⟩ hw⟩
    obtain ⟨-, y, -, hu, -, -⟩ := hB z
    have e1 := (hu x).1 hmin
    have e2 := (hu (xs z)).1 (hxs z)
    rw [e1, e2]
  · have := hstrict z hz
    have := (hxs z).2 x hxD
    linarith [hc.1]

/-- **thm:h1-pick (d), "moreover", extended.** E_hyb(z, x) ≥ v* + 𝔪 for every z ≠ ẑ and
x ∈ dom E_z (for every value of 𝔪). -/
theorem pick_d_bound [Nonempty Z] (hB : ∀ z, ExtBracket (D z) (E z) (xh z) (L z) (ρ z))
    (hxs : ∀ z, IsMinD (D z) (E z) (xs z)) (hZ : 1 < Fintype.card Z) (zh : Z) :
    ∀ z, z ≠ zh → ∀ x ∈ D z,
      minOver (fun z => E z (xs z)) + margin hZ L (fun z => E z (xh z)) zh ≤ E z x := by
  intro z hz x hx
  have HB := brackets_HB D E xh L ρ xs hB hxs
  have h1 := rival_ge hZ HB z hz
  have h2 := minOver_le (fun z => E z (xs z)) zh
  have h3 := (hxs z).2 x hx
  linarith

/-- Nested picks flatten (Lemma H5.4(b), last sentence): the hybrid value of a pick over picks,
min_a min_w f(a, w), is the value min over the disjoint union Σ_a W_a. -/
theorem minOver_sigma {A : Type*} [Fintype A] [Nonempty A] {W : A → Type*}
    [∀ a, Fintype (W a)] [∀ a, Nonempty (W a)] [Nonempty (Σ a, W a)] (f : (Σ a, W a) → ℝ) :
    minOver f = minOver (fun a => minOver (fun w => f ⟨a, w⟩)) := by
  classical
  apply le_antisymm
  · obtain ⟨a, ha⟩ := exists_minOver_eq (fun a => minOver (fun w => f ⟨a, w⟩))
    obtain ⟨w, hw⟩ := exists_minOver_eq (fun w => f ⟨a, w⟩)
    rw [ha, hw]; exact minOver_le f ⟨a, w⟩
  · exact le_minOver fun p => (minOver_le _ p.1).trans (minOver_le (fun w => f ⟨p.1, w⟩) p.2)

end Pick

/-- **thm:h1-pick (e) with reports.** 𝔪 = 0 does not give (d): two copies of E = ½x² on ℝ
(split targets with N = ∅, σ_F = 1), the exact reports at x̂ = 0 (u = 0, ε = 0) give the
brackets L = ℓ_R = 0 = U, ρ = τ_R = 0, the margin is 0, and both (0, 0) and (1, 0) minimise
the hybrid problem. -/
theorem pick_e :
    (∀ z : Fin 2, SplitTarget (sqf (X := ℝ) 1) 1 (fun j : Empty => j.elim) (fun j => j.elim)
      (fun j => j.elim)) ∧
    (∀ z : Fin 2, IsReport (fun j : Empty => (j.elim : Set ℝ)) (fun j => j.elim) (0 : ℝ)
      (fun j => j.elim) (fun j => j.elim)) ∧
    ellRep (sqf (X := ℝ) 1) 1 (fun j : Empty => j.elim) (fun j => j.elim) 0 (fun j => j.elim)
      (fun j => j.elim) = 0 ∧
    tauRep (sqf (X := ℝ) 1) 1 (fun j : Empty => j.elim) 0 (fun j => j.elim) (fun j => j.elim)
      = 0 ∧
    margin (by simp : 1 < Fintype.card (Fin 2)) (fun _ => 0) (fun _ => 0) 0 = 0 ∧
    HybMin (X := fun _ : Fin 2 => ℝ) (fun _ => univ) (fun _ => sqf 1) ⟨0, 0⟩ ∧
    HybMin (X := fun _ : Fin 2 => ℝ) (fun _ => univ) (fun _ => sqf 1) ⟨1, 0⟩ := by
  have hu : uR (sqf (X := ℝ) 1) (fun j : Empty => (j.elim : ℝ)) 0 = 0 := by
    simp [uR, gradient_sqf]
  have hacc : accR (fun j : Empty => (j.elim : ℝ)) = 0 := by simp [accR]
  have hmin : ∀ z : Fin 2, HybMin (X := fun _ : Fin 2 => ℝ) (fun _ => univ) (fun _ => sqf 1)
      ⟨z, 0⟩ := fun z => ⟨mem_univ _, fun q _ => by simp only [sqf]; simp; positivity⟩
  refine ⟨fun _ => ⟨differentiable_sqf 1, modC_sqf 1, fun j => j.elim, fun j => j.elim⟩,
    fun _ j => j.elim, ?_, ?_, ?_, hmin 0, hmin 1⟩
  · unfold ellRep GRep GR tbar tauRep tauR
    rw [hu, hacc]; simp [Eval, sqf]
  · unfold tauRep tauR; rw [hu, hacc]; simp
  · unfold margin rivalMin; simp

/-! ## §9 The a-posteriori principle (Theorem H5.11) -/

section Aposteriori

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {N : Type*} [Fintype N] {F : X → ℝ} {σF : ℝ} {D : N → Set X} {g : N → X → ℝ}
  {σ : N → ℝ}

/-- **Theorem H5.11, the bounds.** Any point x̂ (no hypothesis on its provenance), any point
p with a composite report (computed from oracle calls), μ_E > 0, s > 0, x* a minimiser
(existence classical): ‖x̂ − x*‖ ≤ ‖x̂ − p‖ + τ_R, ℓ_R ≤ min E ≤ E(p), and, if x̂ ∈ dom E,
E(x̂) − min E ≤ E(x̂) − ℓ_R; so (x̂, ℓ_R, ‖x̂ − p‖ + τ_R) is a bracket (Lemma H5.4(b)). -/
theorem aposteriori (hT : SplitTarget F σF D g σ) (xh : X) {p : X} {v : N → X}
    {ε : N → ℝ} (h : IsReport D g p v ε) (hμ : 0 < muHat σF σ) (hs : 0 < sR σF σ ε)
    {xs : X} (hxs : IsMinD (domE D) (Eval F g) xs) :
    ‖xh - xs‖ ≤ ‖xh - p‖ + tauRep F σF σ p v ε ∧
    ellRep F σF g σ p v ε ≤ Eval F g xs ∧ Eval F g xs ≤ Eval F g p ∧
    (xh ∈ domE D → Eval F g xh - Eval F g xs ≤ Eval F g xh - ellRep F σF g σ p v ε) ∧
    (xh ∈ domE D → ExtBracket (domE D) (Eval F g) xh (ellRep F σF g σ p v ε)
      (‖xh - p‖ + tauRep F σF σ p v ε)) := by
  obtain ⟨⟨hu, -⟩, ⟨hc, -⟩, ⟨-, hl, hp, -⟩⟩ := lemma_H5_2 hT h hμ hs hxs
  have hd : ‖xh - xs‖ ≤ ‖xh - p‖ + tauRep F σF σ p v ε := by
    have := norm_sub_le_norm_sub_add_norm_sub xh p xs
    linarith
  exact ⟨hd, hl, hp, fun _ => by linarith, fun hx => ⟨hx, xs, hxs, hu, hl, hd⟩⟩

/-- **Theorem H5.11(a)** (N = {j}, explicit prox; zero-trust producer): p := T_α x̂ (the exact
prox at x̂ − α∇F(x̂)), u := R_α(x̂) − ∇F(x̂) + ∇F(p), ε = 0, J = N, so s = 2μ_E;
‖x̂ − p‖ = α‖R_α(x̂)‖ and ‖u‖ ≤ (1 + αβ)‖R_α(x̂)‖; hence
‖x̂ − x*‖ ≤ (α + (1 + αβ)/μ_E)‖R_α(x̂)‖ (recovering thm:fb-residual(d) with μ = μ_E) and
the value bracket ℓ_R = E(p) − ‖u‖²/(2μ_E) ≤ min E ≤ E(p). -/
theorem aposteriori_a {D : Set X} {g : X → ℝ} {σg α β : ℝ} (hα : 0 < α) (hL : LipGrad F β)
    (hT : SplitTarget F σF (fun _ : Unit => D) (fun _ => g) (fun _ => σg))
    (hμ : 0 < σF + σg) (xh : X) {p : X} (hP : ProxEps D g α 0 (step F α xh) p) {xs : X}
    (hxs : IsMinD (domE (fun _ : Unit => D)) (Eval F (fun (_ : Unit) => g)) xs) :
    ‖xh - p‖ = α * ‖α⁻¹ • (xh - p)‖ ∧
    ‖uR F (fun _ : Unit => α⁻¹ • (xh - p) - gradient F xh) p‖ ≤ (1 + α * β) * ‖α⁻¹ • (xh - p)‖ ∧
    ‖xh - xs‖ ≤ (α + (1 + α * β) / (σF + σg)) * ‖α⁻¹ • (xh - p)‖ ∧
    ellRep F σF (fun _ : Unit => g) (fun _ => σg) p
        (fun _ => α⁻¹ • (xh - p) - gradient F xh) (fun _ => 0)
      = Eval F (fun _ : Unit => g) p
        - ‖uR F (fun _ : Unit => α⁻¹ • (xh - p) - gradient F xh) p‖ ^ 2 / (2 * (σF + σg)) ∧
    ellRep F σF (fun _ : Unit => g) (fun _ => σg) p
        (fun _ => α⁻¹ • (xh - p) - gradient F xh) (fun _ => 0) ≤ Eval F (fun _ : Unit => g) xs ∧
    Eval F (fun _ : Unit => g) xs ≤ Eval F (fun _ : Unit => g) p := by
  set R := α⁻¹ • (xh - p)
  set v : Unit → X := fun _ => R - gradient F xh
  have hrep : IsReport (fun _ : Unit => D) (fun _ => g) p v (fun _ => 0) := by
    intro _
    refine ⟨le_rfl, ?_⟩
    have h := hP
    unfold ProxEps at h
    rwa [prox_vec_eq F hα.ne'] at h
  have hmuE : muHat σF (fun _ : Unit => σg) = σF + σg := muHat_unit σF σg
  have hacc : accR (fun _ : Unit => (0 : ℝ)) = 0 := by simp [accR]
  have hmuR : muR σF (fun _ : Unit => σg) (fun _ => 0) = σF + σg := by
    rw [muR_eq_of_acc_zero hrep hacc, hmuE]
  have hs : 0 < sR σF (fun _ : Unit => σg) (fun _ => 0) := by
    unfold sR; rw [hmuE, hmuR]; linarith
  have hμ' : 0 < muHat σF (fun _ : Unit => σg) := by rw [hmuE]; exact hμ
  have hu : uR F v p = R - gradient F xh + gradient F p := by rw [uR_unit]; abel
  have hun : ‖uR F v p‖ ≤ (1 + α * β) * ‖R‖ := by rw [hu]; exact prox_u_norm hα hL xh p
  have hpx : ‖xh - p‖ = α * ‖R‖ := by
    simp only [R, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hα), ← mul_assoc,
      mul_inv_cancel₀ hα.ne', one_mul]
  obtain ⟨hd, hl, hp, -, -⟩ := aposteriori hT xh hrep hμ' hs hxs
  have htau : tauRep F σF (fun _ : Unit => σg) p v (fun _ => 0) = ‖uR F v p‖ / (σF + σg) := by
    unfold tauRep tauR sR
    rw [hacc, hmuE, hmuR, mul_zero, add_zero, Real.sqrt_sq (norm_nonneg _)]
    field_simp
  have hG := (GRep_eq_case (F := F) hrep hμ' (by rw [hmuR, hmuE])).2
  refine ⟨hpx, hun, ?_, ?_, hl, hp⟩
  · rw [htau] at hd
    have : ‖uR F v p‖ / (σF + σg) ≤ (1 + α * β) * ‖R‖ / (σF + σg) :=
      div_le_div_of_nonneg_right hun hμ.le
    calc ‖xh - xs‖ ≤ α * ‖R‖ + (1 + α * β) * ‖R‖ / (σF + σg) := by linarith
      _ = (α + (1 + α * β) / (σF + σg)) * ‖R‖ := by ring
  · unfold ellRep; rw [hG, hacc, hmuE, zero_add]

/-- **Theorem H5.11(b)** (N = {j}, inexact oracle): the oracle answers (α, x̂ − α∇F(x̂)) by
(z, ε') with z ∈ prox^{ε'}_{αg}(x̂ − α∇F(x̂)); p := z, u := (x̂ − z)/α − ∇F(x̂) + ∇F(z),
ε = ε', J = ∅ if ε' > 0 (μ_R = σ_F, s = 2σ_F + σ_g). The report is valid, so the bounds of
`aposteriori` hold at p. -/
theorem aposteriori_b {D : Set X} {g : X → ℝ} {σg α ε' : ℝ} (hα : 0 < α) (hε : 0 ≤ ε')
    (xh : X) {z : X} (hz : ProxEps D g α ε' (step F α xh) z) :
    IsReport (fun _ : Unit => D) (fun _ => g) z (fun _ => α⁻¹ • (xh - z) - gradient F xh)
      (fun _ => ε') ∧
    uR F (fun _ : Unit => α⁻¹ • (xh - z) - gradient F xh) z
      = α⁻¹ • (xh - z) - gradient F xh + gradient F z ∧
    (0 < ε' → muR σF (fun _ : Unit => σg) (fun _ => ε') = σF ∧
      sR σF (fun _ : Unit => σg) (fun _ => ε') = 2 * σF + σg) := by
  refine ⟨fun _ => ⟨hε, ?_⟩, by rw [uR_unit]; abel, fun hpos => ?_⟩
  · have h := hz; unfold ProxEps at h; rwa [prox_vec_eq F hα.ne'] at h
  · have h1 := muR_unit_inexact (σF := σF) (s := σg) hpos.ne'
    refine ⟨h1, ?_⟩
    unfold sR; rw [h1, muHat_unit]; ring

/-- **Theorem H5.11(c)** (|N| ≥ 2, explicit proxes, Lipschitz attributes off j₀): any
read-outs (p_j, v_j) with v_j ∈ ∂g_j(p_j), moved to x by their Lipschitz attributes, give a
composite report at x with μ_R = μ_E (Lemma H5.3(iii), point form); with μ_E > 0 the bounds of
`aposteriori` hold with s = 2μ_E. -/
theorem aposteriori_c [Nontrivial X] {L : N → ℝ} {x : X} {p v : N → X}
    (h : HCert F σF D g σ L x p v) (hμ : 0 < muHat σF σ) (xh : X) {xs : X}
    (hxs : IsMinD (domE D) (Eval F g) xs) :
    ‖xh - xs‖ ≤ ‖xh - x‖ + tauRep F σF σ x v (fun j => (‖v j‖ + L j) * ‖p j - x‖) ∧
    ellRep F σF g σ x v (fun j => (‖v j‖ + L j) * ‖p j - x‖) ≤ Eval F g xs ∧
    Eval F g xs ≤ Eval F g x := by
  obtain ⟨hT, hrep, -, -, -, hmuR⟩ := closure_cons h
  have hs : 0 < sR σF σ (fun j => (‖v j‖ + L j) * ‖p j - x‖) := by
    unfold sR; rw [hmuR]; linarith
  obtain ⟨h1, h2, h3, -, -⟩ := aposteriori hT xh hrep hμ hs hxs
  exact ⟨h1, h2, h3⟩

end Aposteriori

/-! ## §6 Liveness and counts (Lemma H5.8, arithmetic and assembly) -/

section Live

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]

lemma k0_eq_zero {D : Set X} {x : ℕ → X} (hx0 : x 0 ∈ D) : k0 D x = 0 := by
  unfold k0; simp [hx0]

lemma count_eq (β A η : ℝ) (hη : 0 < η) : 2 * β * A / (η / 2) ^ 2 = 8 * β * A / η ^ 2 := by
  field_simp; ring

/-- **Lemma H5.8(a) (fb).** For the constructed iteration from x₀ ∈ dom g (exact prox (P) as
hypothesis), under (O2) (E_low ≤ E on dom g): the stopping rule `‖u‖ ≤ η̄` fires no later
than the first k with ‖R_α(x_k)‖ ≤ η̄/2 (so in regime A no later than k_{η̄/2} of (S5A)), and
some output x_{k+1} with k ≤ ⌊8β̂(E(x₀) − E_low)/η̄²⌋ meets the target (η̄, 0) (via H2's
(I2) with all accuracies 0 = landed (S2)). -/
theorem live_fb {F : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ} (hF : Differentiable ℝ F)
    (hL : LipGrad F β) (hα : 0 < α) (hαβ : α * β = 1) {P : X → X}
    (hP : ∀ y, ProxEps D g α 0 y (P y)) {x : ℕ → X} (hx : ∀ k, x (k + 1) = P (step F α (x k)))
    (hx0 : x 0 ∈ D) {Elow : ℝ} (hlow : ∀ w ∈ D, Elow ≤ F w + g w) {η : ℝ} (hη : 0 < η) :
    (∀ k, ‖rres α x k‖ ≤ η / 2 →
      ‖uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))‖ ≤ η) ∧
    ∃ k, k ≤ ⌊8 * β * (F (x 0) + g (x 0) - Elow) / η ^ 2⌋₊ ∧
      ‖uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))‖ ≤ η := by
  have hr : InexactRun F D g α x (fun _ => 0) := fun k => ⟨le_rfl, by rw [hx k]; exact hP _⟩
  have hstop : ∀ k, ‖rres α x k‖ ≤ η / 2 →
      ‖uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))‖ ≤ η := fun k hk => by
    have := (closure_inx hα hL hαβ hr k).2.2.1; linarith
  refine ⟨hstop, ?_⟩
  obtain ⟨-, hex, hcount⟩ := E2b_limits hF hL hα hαβ hr hlow summable_zero
  have hk0 := k0_eq_zero (D := D) hx0
  rw [hk0] at hex hcount
  set S := {k | 0 ≤ k ∧ ‖rres α x k‖ ≤ η / 2}
  have hne : S.Nonempty := hex (η / 2) (by linarith)
  have hmem := Nat.sInf_mem hne
  have hc := hcount (η / 2) (by linarith) 0 (by simp)
  rw [zero_add, add_zero, count_eq β _ η hη] at hc
  exact ⟨sInf S, hc, hstop _ hmem.2⟩

/-- **Lemma H5.8(b) (inx).** An inexact run from x₀ ∈ dom g with answers meeting their
reported accuracies ε_k ≤ ε̄^O_k, the schedule nonincreasing with Σ_k ε̄^O_k ≤ S̄ < ∞, under
(O2) (any E_low ≤ inf E, e.g. ℓ_R of any report, `ellRep_lower`), and any index k̄ with
ε̄^O_{k̄} ≤ ε̄ (e.g. the least one): some output x_{k+1} with
k̄ ≤ k ≤ k̄ + ⌊8β̂(E(x_{k̄}) − E_low + S̄)/η̄²⌋ meets the target (η̄, ε̄). -/
theorem live_inx {F : X → ℝ} {D : Set X} {g : X → ℝ} {α β : ℝ} (hF : Differentiable ℝ F)
    (hL : LipGrad F β) (hα : 0 < α) (hαβ : α * β = 1) {x : ℕ → X} {ε : ℕ → ℝ}
    (hr : InexactRun F D g α x ε) (hx0 : x 0 ∈ D) {Elow : ℝ}
    (hlow : ∀ w ∈ D, Elow ≤ F w + g w) {εO : ℕ → ℝ} (hεO : ∀ k, ε k ≤ εO k)
    (hanti : Antitone εO) (hsum : Summable εO) {Sbar : ℝ} (hS : ∑' k, εO k ≤ Sbar)
    {εbar : ℝ} {kbar : ℕ} (hk : εO kbar ≤ εbar) {η : ℝ} (hη : 0 < η) :
    ∃ k, kbar ≤ k ∧ k ≤ kbar + ⌊8 * β * (F (x kbar) + g (x kbar) - Elow + Sbar) / η ^ 2⌋₊ ∧
      ‖uR F (fun _ : Unit => rres α x k - gradient F (x k)) (x (k + 1))‖ ≤ η ∧ ε k ≤ εbar := by
  set y : ℕ → X := fun j => x (j + kbar)
  set e' : ℕ → ℝ := fun j => ε (j + kbar)
  have hry : InexactRun F D g α y e' := by
    intro j
    have := hr (j + kbar)
    simp only [y, e']
    rwa [show j + 1 + kbar = j + kbar + 1 by omega]
  have hy0 : y 0 ∈ D := by
    simp only [y, zero_add]
    rcases kbar with _ | k
    · exact hx0
    · exact hr.mem k
  have hε : Summable ε := Summable.of_nonneg_of_le (fun k => (hr k).1) hεO hsum
  have he' : Summable e' := (summable_nat_add_iff kbar).2 hε
  have hshift : ∑' j, e' (j + k0 D y) ≤ Sbar := by
    rw [k0_eq_zero hy0]
    simp only [add_zero, e']
    have h1 := hε.sum_add_tsum_nat_add kbar
    have h2 : 0 ≤ ∑ i ∈ range kbar, ε i := Finset.sum_nonneg fun i _ => (hr i).1
    have h3 : ∑' k, ε k ≤ ∑' k, εO k := Summable.tsum_le_tsum hεO hε hsum
    linarith
  obtain ⟨-, hex, hcount⟩ := E2b_limits hF hL hα hαβ hry hlow he'
  rw [k0_eq_zero hy0] at hshift
  rw [k0_eq_zero hy0] at hex hcount
  set S := {j | 0 ≤ j ∧ ‖rres α y j‖ ≤ η / 2}
  have hne : S.Nonempty := hex (η / 2) (by linarith)
  have hmem := Nat.sInf_mem hne
  have hc := hcount (η / 2) (by linarith) Sbar hshift
  rw [zero_add, count_eq β _ η hη] at hc
  have hy00 : y 0 = x kbar := by simp [y]
  rw [hy00] at hc
  set j := sInf S
  have hrr : rres α y j = rres α x (j + kbar) := by
    simp only [rres, y]; rw [show j + 1 + kbar = j + kbar + 1 by omega]
  refine ⟨j + kbar, Nat.le_add_left _ _, by omega, ?_, ?_⟩
  · have := (closure_inx hα hL hαβ hr (j + kbar)).2.2.1
    have h2 := hmem.2
    rw [hrr] at h2
    linarith
  · exact (hεO _).trans ((hanti (Nat.le_add_left kbar j)).trans hk)

/-- ℓ_R of any report is a valid E_low (Lemma H5.8(b), via Lemma H5.2(d)). -/
theorem ellRep_lower {N : Type*} [Fintype N] {F : X → ℝ} {σF : ℝ} {D : N → Set X}
    {g : N → X → ℝ} {σ : N → ℝ} (hT : SplitTarget F σF D g σ) {xh : X} {v : N → X}
    {ε : N → ℝ} (h : IsReport D g xh v ε) (hμ : 0 < muHat σF σ) (hs : 0 < sR σF σ ε)
    {xs : X} (hxs : IsMinD (domE D) (Eval F g) xs) :
    ∀ w ∈ domE D, ellRep F σF g σ xh v ε ≤ Eval F g w := fun w hw =>
  ((lemma_H5_2 hT h hμ hs hxs).2.2.2.1).trans (hxs.2 w hw)

/-- The count arithmetic of Lemma H5.8(c): k := max{0, ⌈2D̄₀²/ē²⌉ − 1} has
√(2/(k+1)) D̄₀ ≤ ē. -/
lemma cons_count {D e : ℝ} (hD : 0 ≤ D) (he : 0 < e) :
    √(2 / ((⌈2 * D ^ 2 / e ^ 2⌉₊ - 1 : ℕ) + 1)) * D ≤ e := by
  set k : ℕ := ⌈2 * D ^ 2 / e ^ 2⌉₊ - 1
  have hk : 2 * D ^ 2 / e ^ 2 ≤ (k : ℝ) + 1 := by
    rcases Nat.eq_zero_or_pos ⌈2 * D ^ 2 / e ^ 2⌉₊ with h0 | hpos
    · have : 2 * D ^ 2 / e ^ 2 ≤ 0 := Nat.ceil_eq_zero.1 h0
      have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    · have h1 : (k : ℝ) + 1 = ⌈2 * D ^ 2 / e ^ 2⌉₊ := by
        simp only [k]; rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [h1]; exact Nat.le_ceil _
  have hk1 : (0 : ℝ) < k + 1 := by positivity
  have h2 : 2 / (k + 1) * D ^ 2 ≤ e ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hk
    rw [div_mul_eq_mul_div, div_le_iff₀ hk1]; linarith
  calc √(2 / ((k : ℝ) + 1)) * D = √(2 / (k + 1) * D ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq hD]
    _ ≤ √(e ^ 2) := Real.sqrt_le_sqrt h2
    _ = e := Real.sqrt_sq he.le

/-- **Lemma H5.8(c) (cons).** Consensus-typed data, step α > 0; the landed rate
e_k ≤ ē_k := √(2/(k+1)) D̄₀ (proof of thm:h3-soundness(c), an interface hypothesis here);
η̄ > 0 and any ē > 0 with ē ≤ α√m' η̄ and 2‖L‖ē ≤ ε̄ (e.g. ē = min{α√m'η̄, ε̄/(2‖L‖)},
`cons_ebar_min`). Then the output x_k with k = max{0, ⌈2D̄₀²/ē²⌉ − 1} meets the target:
‖r_k‖ ≤ η̄ and ε_k ≤ ε̄. -/
theorem live_cons [Nontrivial X] {ι : Type*} [Fintype ι] [Nonempty ι] {C : ConsIter X ι}
    {σF σ0 : ℝ} {D0 : Set X} {g0 : X → ℝ} {gj : ι → X → ℝ} {σj Lj : ι → ℝ}
    (h : C.Typed σF σ0 D0 g0 gj σj Lj) (hα : 0 < C.α) (z0 : ι → X) {Dbar : ℝ} (hD : 0 ≤ Dbar)
    (he : ∀ k : ℕ, C.e (C.iter z0 k) ≤ √(2 / (k + 1)) * Dbar) {η εbar ebar : ℝ}
    (heb : 0 < ebar) (h1 : ebar ≤ C.α * √(ConsIter.mP ι) * η)
    (h2 : 2 * ConsIter.normL Lj * ebar ≤ εbar) :
    ‖C.r (C.iter z0 (⌈2 * Dbar ^ 2 / ebar ^ 2⌉₊ - 1))‖ ≤ η ∧
      C.epsIt Lj (C.iter z0 (⌈2 * Dbar ^ 2 / ebar ^ 2⌉₊ - 1)) ≤ εbar := by
  set k := ⌈2 * Dbar ^ 2 / ebar ^ 2⌉₊ - 1
  have hek : C.e (C.iter z0 k) ≤ ebar := by
    have := he k
    have hc := cons_count hD heb
    linarith
  have hm : 0 < √(ConsIter.mP ι) := Real.sqrt_pos.2 ConsIter.mP_pos
  have hden : 0 < C.α * √(ConsIter.mP ι) := mul_pos hα hm
  constructor
  · have hr := (ConsIter.readout_bounds hα (C.iter z0 k)).2.2
    have : C.e (C.iter z0 k) / (C.α * √(ConsIter.mP ι)) ≤ η := by
      rw [div_le_iff₀ hden]; nlinarith
    linarith
  · have hε := ConsIter.epsIt_le h hα (C.iter z0 k)
    have hL : 0 ≤ ConsIter.normL Lj := Real.sqrt_nonneg _
    nlinarith

/-- ē := min{α√m'η̄, ε̄/(2‖L‖)} satisfies the two conditions of `live_cons` (‖L‖ > 0). -/
lemma cons_ebar_min {a nL η εbar : ℝ} (hnL : 0 < nL) :
    min (a * η) (εbar / (2 * nL)) ≤ a * η ∧ 2 * nL * min (a * η) (εbar / (2 * nL)) ≤ εbar := by
  refine ⟨min_le_left _ _, ?_⟩
  have := min_le_right (a * η) (εbar / (2 * nL))
  rw [le_div_iff₀ (by positivity)] at this
  linarith

/-! ### The stitch: declared-target quantities (H4's Γ_k, ‖η_k‖, Q_k, B_k(θ) as functions of
the reports' (η_l, ε_l)), accumulation, and Lemma H5.8(d) -/

variable {B : Type*} [Fintype B]

/-- Γ = Σ_l (η_l²/(2τ_l) + ε_l). -/
noncomputable def GamF (τ η ε : B → ℝ) : ℝ := ∑ l, (η l ^ 2 / (2 * τ l) + ε l)
/-- ‖η‖ = (Σ_l η_l²)^{1/2}. -/
noncomputable def etaN (η : B → ℝ) : ℝ := √(∑ l, η l ^ 2)
/-- Q = ‖η‖ + Λ√(2Γ). -/
noncomputable def QF (τ : B → ℝ) (Λ : ℝ) (η ε : B → ℝ) : ℝ := etaN η + Λ * √(2 * GamF τ η ε)
/-- B(θ) = c_θΓ + (1 + 1/θ)Q²/(2σ) + Σ_l ε_l. -/
noncomputable def BF (τ : B → ℝ) (Λ σ c θ : ℝ) (η ε : B → ℝ) : ℝ :=
  c * GamF τ η ε + (1 + 1 / θ) * QF τ Λ η ε ^ 2 / (2 * σ) + ∑ l, ε l

lemma GamF_mono {τ η η' ε ε' : B → ℝ} (hτ : ∀ l, 0 < τ l) (hη0 : ∀ l, 0 ≤ η l)
    (hη : ∀ l, η l ≤ η' l) (hε : ∀ l, ε l ≤ ε' l) : GamF τ η ε ≤ GamF τ η' ε' := by
  unfold GamF
  refine Finset.sum_le_sum fun l _ => ?_
  have := pow_le_pow_left₀ (hη0 l) (hη l) 2
  have := hτ l
  have : η l ^ 2 / (2 * τ l) ≤ η' l ^ 2 / (2 * τ l) := by gcongr
  linarith [hε l]

lemma GamF_nonneg {τ η ε : B → ℝ} (hτ : ∀ l, 0 < τ l) (hε : ∀ l, 0 ≤ ε l) :
    0 ≤ GamF τ η ε :=
  Finset.sum_nonneg fun l _ => by have := hτ l; have := hε l; positivity

lemma etaN_mono {η η' : B → ℝ} (hη0 : ∀ l, 0 ≤ η l) (hη : ∀ l, η l ≤ η' l) :
    etaN η ≤ etaN η' :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun l _ => pow_le_pow_left₀ (hη0 l) (hη l) 2)

/-- B(θ) is nondecreasing in every η_l and ε_l (the monotonicity clause of h4-thm:stitch(d),
proved here for the explicit formula). -/
lemma BF_mono {τ η η' ε ε' : B → ℝ} {Λ σ c θ : ℝ} (hτ : ∀ l, 0 < τ l) (hΛ : 0 ≤ Λ)
    (hσ : 0 < σ) (hc : 0 ≤ c) (hθ : 0 < θ) (hη0 : ∀ l, 0 ≤ η l) (hη : ∀ l, η l ≤ η' l)
    (hε0 : ∀ l, 0 ≤ ε l) (hε : ∀ l, ε l ≤ ε' l) :
    BF τ Λ σ c θ η ε ≤ BF τ Λ σ c θ η' ε' := by
  have hG := GamF_mono hτ hη0 hη hε
  have hG0 := GamF_nonneg (η := η) hτ hε0
  have hN := etaN_mono hη0 hη
  have hQ0 : 0 ≤ QF τ Λ η ε := by unfold QF etaN; positivity
  have hQ : QF τ Λ η ε ≤ QF τ Λ η' ε' := by
    unfold QF
    have := Real.sqrt_le_sqrt (by linarith : 2 * GamF τ η ε ≤ 2 * GamF τ η' ε')
    nlinarith
  have hQ2 := pow_le_pow_left₀ hQ0 hQ 2
  have hs : ∑ l, ε l ≤ ∑ l, ε' l := Finset.sum_le_sum fun l _ => hε l
  unfold BF
  have h1 : (1 + 1 / θ) * QF τ Λ η ε ^ 2 / (2 * σ) ≤ (1 + 1 / θ) * QF τ Λ η' ε' ^ 2 / (2 * σ) := by
    gcongr
  nlinarith

/-- Accumulation (the unrolled recursion of h4-thm:stitch(c)): a_{k+1} ≤ ρa_k + (1 − ρ)B_k,
B_k ≤ B̄_k, a₀ ≤ Ā₀, ρ ∈ [0, 1] ⇒ a_k ≤ A_k := ρ^k Ā₀ + (1 − ρ) Σ_{i<k} ρ^{k−1−i} B̄_i. -/
lemma accum_le {a Bk Bb : ℕ → ℝ} {ρ A0 : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (ha0 : a 0 ≤ A0)
    (hrec : ∀ k, a (k + 1) ≤ ρ * a k + (1 - ρ) * Bk k) (hB : ∀ k, Bk k ≤ Bb k) :
    ∀ k, a k ≤ ρ ^ k * A0 + (1 - ρ) * ∑ i ∈ range k, ρ ^ (k - 1 - i) * Bb i := by
  intro k
  induction k with
  | zero => simpa using ha0
  | succ k ih =>
    have h1 := hrec k
    have h2 : (1 - ρ) * Bk k ≤ (1 - ρ) * Bb k := mul_le_mul_of_nonneg_left (hB k) (by linarith)
    have h3 : ρ * a k ≤ ρ * (ρ ^ k * A0 + (1 - ρ) * ∑ i ∈ range k, ρ ^ (k - 1 - i) * Bb i) :=
      mul_le_mul_of_nonneg_left ih hρ0
    have hsum : ∑ i ∈ range (k + 1), ρ ^ (k + 1 - 1 - i) * Bb i
        = ρ * ∑ i ∈ range k, ρ ^ (k - 1 - i) * Bb i + Bb k := by
      rw [Finset.sum_range_succ, Finset.mul_sum, show k + 1 - 1 - k = 0 by omega, pow_zero,
        one_mul]
      congr 1
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' := Finset.mem_range.1 hi
      rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega, pow_succ]; ring
    rw [hsum, pow_succ]
    nlinarith

/-- **Lemma H5.8(d) (stitch), the a-priori report bound.** In a stitched run whose child calls
meet their declared targets (η_{k,l} ≤ η̄_{k,l}, ε_{k,l} ≤ ε̄'_{k,l}), with H4's run facts as
interface hypotheses — the recursion of h4-thm:stitch(c) (`hrec`), the assembly bound
‖u‖ ≤ ‖η_k‖ + ΛD_k of h4-lem:assembly(b) (`hu`) and the Minkowski step
D_k ≤ √(2(a_k − a_{k+1} + Γ_k)) + √(2Γ_k) of its proof (`hD`) — and Ā₀ ≥ a₀:
the stitch's report at x^{k+1} has
‖u‖ ≤ Ū_k := ‖η̄_k‖ + Λ(√(2(A_k + Γ̄_k)) + √(2Γ̄_k)) and ε ≤ ε̄_k := Σ_l ε̄'_{k,l}, with
A_k := ρ_θ^k Ā₀ + (1 − ρ_θ)Σ_{i<k} ρ_θ^{k−1−i} B̄_i(θ). -/
theorem live_stitch {τ : B → ℝ} {Λ σ c θ ρ A0 : ℝ} (hτ : ∀ l, 0 < τ l) (hΛ : 0 ≤ Λ)
    (hσ : 0 < σ) (hc : 0 ≤ c) (hθ : 0 < θ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    {a Dk unorm : ℕ → ℝ} {η ε ηb εb : ℕ → B → ℝ}
    (ha : ∀ k, 0 ≤ a k) (ha0 : a 0 ≤ A0)
    (hrec : ∀ k, a (k + 1) ≤ ρ * a k + (1 - ρ) * BF τ Λ σ c θ (η k) (ε k))
    (hu : ∀ k, unorm k ≤ etaN (η k) + Λ * Dk k)
    (hD : ∀ k, Dk k ≤ √(2 * (a k - a (k + 1) + GamF τ (η k) (ε k))) + √(2 * GamF τ (η k) (ε k)))
    (hη0 : ∀ k l, 0 ≤ η k l) (hηb : ∀ k l, η k l ≤ ηb k l)
    (hε0 : ∀ k l, 0 ≤ ε k l) (hεb : ∀ k l, ε k l ≤ εb k l) (k : ℕ) :
    a k ≤ ρ ^ k * A0 + (1 - ρ) * ∑ i ∈ range k, ρ ^ (k - 1 - i) * BF τ Λ σ c θ (ηb i) (εb i) ∧
    unorm k ≤ etaN (ηb k) + Λ * (√(2 * ((ρ ^ k * A0 + (1 - ρ) * ∑ i ∈ range k,
        ρ ^ (k - 1 - i) * BF τ Λ σ c θ (ηb i) (εb i)) + GamF τ (ηb k) (εb k)))
      + √(2 * GamF τ (ηb k) (εb k))) ∧
    ∑ l, ε k l ≤ ∑ l, εb k l := by
  have hA := accum_le hρ0 hρ1 ha0 hrec (fun i => BF_mono hτ hΛ hσ hc hθ (hη0 i) (hηb i)
    (hε0 i) (hεb i)) k
  refine ⟨hA, ?_, Finset.sum_le_sum fun l _ => hεb k l⟩
  have hG := GamF_mono hτ (hη0 k) (hηb k) (hεb k)
  have hN := etaN_mono (hη0 k) (hηb k)
  have hs1 : √(2 * (a k - a (k + 1) + GamF τ (η k) (ε k)))
      ≤ √(2 * ((ρ ^ k * A0 + (1 - ρ) * ∑ i ∈ range k,
        ρ ^ (k - 1 - i) * BF τ Λ σ c θ (ηb i) (εb i)) + GamF τ (ηb k) (εb k))) :=
    Real.sqrt_le_sqrt (by linarith [ha (k + 1)])
  have hs2 : √(2 * GamF τ (η k) (ε k)) ≤ √(2 * GamF τ (ηb k) (εb k)) :=
    Real.sqrt_le_sqrt (by linarith)
  have := hu k
  have := hD k
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hs1 hs2) hΛ]

end Live

/-! ## §8 Counts compose (Corollary H5.10) -/

section Counts

variable {B : Type*} [Fintype B]

lemma abs_sub_le_max_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : |a - b| ≤ max a b := by
  rcases le_total a b with h | h
  · rw [abs_of_nonpos (by linarith), max_eq_right h]; linarith
  · rw [abs_of_nonneg (by linarith), max_eq_left h]; linarith

/-- Σ_{i<k} ρ^{k−1−i} r^i ≤ max{ρ, r}^k/|ρ − r| for ρ, r ≥ 0, ρ ≠ r (the geometric case of
h4-thm:stitch(c)). -/
lemma geom_conv_le {ρ r : ℝ} (hρ : 0 ≤ ρ) (hr : 0 ≤ r) (hne : ρ ≠ r) (k : ℕ) :
    ∑ i ∈ range k, ρ ^ (k - 1 - i) * r ^ i ≤ max ρ r ^ k / |ρ - r| := by
  set S := ∑ i ∈ range k, ρ ^ (k - 1 - i) * r ^ i
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have e : S * (r - ρ) = r ^ k - ρ ^ k := by
    rw [← geom_sum₂_mul r ρ k]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hd : 0 < |ρ - r| := abs_pos.2 (sub_ne_zero.2 hne)
  have h1 : S * |ρ - r| = |r ^ k - ρ ^ k| := by
    rw [← e, abs_mul, abs_of_nonneg hS0, abs_sub_comm]
  have h2 : |r ^ k - ρ ^ k| ≤ max ρ r ^ k := by
    refine (abs_sub_le_max_of_nonneg (by positivity) (by positivity)).trans ?_
    exact max_le (pow_le_pow_left₀ hr (le_max_right _ _) k) (pow_le_pow_left₀ hρ (le_max_left _ _) k)
  rw [le_div_iff₀ hd, h1]; exact h2

/-- Scaling: B(θ) at the targets tη̄ (and zero accuracies) is t²·B(θ) at η̄. -/
lemma BF_scale {τ : B → ℝ} {Λ σ c θ t : ℝ} (ht : 0 ≤ t) (ηb : B → ℝ) :
    BF τ Λ σ c θ (fun l => t * ηb l) (fun _ => 0) = t ^ 2 * BF τ Λ σ c θ ηb (fun _ => 0) := by
  have hG : GamF τ (fun l => t * ηb l) (fun _ => 0) = t ^ 2 * GamF τ ηb (fun _ => 0) := by
    unfold GamF; rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  have hs : ∑ l, (t * ηb l) ^ 2 = t ^ 2 * ∑ l, ηb l ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
  have hN : etaN (fun l => t * ηb l) = t * etaN ηb := by
    unfold etaN
    rw [hs, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
  have hQ : QF τ Λ (fun l => t * ηb l) (fun _ => 0) = t * QF τ Λ ηb (fun _ => 0) := by
    unfold QF
    rw [hN, hG, show 2 * (t ^ 2 * GamF τ ηb (fun _ => 0)) = t ^ 2 * (2 * GamF τ ηb (fun _ => 0))
      by ring, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
    ring
  unfold BF
  rw [hG, hQ]
  simp only [Finset.sum_const_zero, add_zero]
  ring

/-- **Corollary H5.10(a).** A stitch whose children are (fb) (reports exact, ε = 0) and meet
geometric targets η_{k,l} ≤ η̄_l q^k (q ∈ (0, 1)), q² ≠ ρ_θ, Ā₀ ≥ a₀, with H4's recursion
a_{k+1} ≤ ρ_θ a_k + (1 − ρ_θ)B_k(θ) as interface: a_k ≤ A_k := max{ρ_θ, q²}^k C_A,
C_A := Ā₀ + (1 − ρ_θ)B̄₀/|ρ_θ − q²|, B̄₀ := B(θ) at (η̄, 0); and with h4-thm:stitch(d)
(‖x^k − x*‖ ≤ (2a_k/σ)^{1/2}), ‖x^k − x*‖ ≤ (2A_k/σ)^{1/2}. -/
theorem cor_a {τ ηb : B → ℝ} {Λ σ c θ ρ q A0 : ℝ} (hτ : ∀ l, 0 < τ l) (hΛ : 0 ≤ Λ)
    (hσ : 0 < σ) (hc : 0 ≤ c) (hθ : 0 < θ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hq0 : 0 < q)
    (hqρ : q ^ 2 ≠ ρ) {a : ℕ → ℝ} {η : ℕ → B → ℝ} (ha : ∀ k, 0 ≤ a k) (ha0 : a 0 ≤ A0)
    (hη0 : ∀ k l, 0 ≤ η k l) (hη : ∀ k l, η k l ≤ ηb l * q ^ k)
    (hrec : ∀ k, a (k + 1) ≤ ρ * a k + (1 - ρ) * BF τ Λ σ c θ (η k) (fun _ => 0)) (k : ℕ) :
    a k ≤ max ρ (q ^ 2) ^ k
      * (A0 + (1 - ρ) * BF τ Λ σ c θ ηb (fun _ => 0) / |ρ - q ^ 2|) ∧
    (∀ d : ℝ, d ≤ √(2 * a k / σ) → d ≤ √(2 * (max ρ (q ^ 2) ^ k
      * (A0 + (1 - ρ) * BF τ Λ σ c θ ηb (fun _ => 0) / |ρ - q ^ 2|)) / σ)) := by
  set B0 := BF τ Λ σ c θ ηb (fun _ => 0)
  have hB0 : 0 ≤ B0 := by
    have := BF_mono (η := fun _ => 0) (η' := ηb) (ε := fun _ => (0 : ℝ)) (ε' := fun _ => 0)
      hτ hΛ hσ hc hθ (fun _ => le_rfl) (fun l => (hη0 0 l).trans (by simpa using hη 0 l))
      (fun _ => le_rfl) (fun _ => le_rfl)
    have h0 : BF τ Λ σ c θ (fun _ => (0 : ℝ)) (fun _ => 0) = 0 := by
      have := BF_scale (τ := τ) (Λ := Λ) (σ := σ) (c := c) (θ := θ) le_rfl ηb
      simpa using this
    linarith
  have hBk : ∀ i, BF τ Λ σ c θ (η i) (fun _ => 0) ≤ (q ^ 2) ^ i * B0 := by
    intro i
    have := BF_mono (ε := fun _ => (0 : ℝ)) (ε' := fun _ => 0) (η' := fun l => q ^ i * ηb l)
      hτ hΛ hσ hc hθ (hη0 i) (fun l => by rw [mul_comm]; exact hη i l) (fun _ => le_rfl)
      (fun _ => le_rfl)
    rw [BF_scale (by positivity)] at this
    rw [← pow_mul, mul_comm 2 i, pow_mul]
    exact this
  have hacc := accum_le hρ0 hρ1.le ha0 hrec hBk k
  have hsum : ∑ i ∈ range k, ρ ^ (k - 1 - i) * ((q ^ 2) ^ i * B0)
      = B0 * ∑ i ∈ range k, ρ ^ (k - 1 - i) * (q ^ 2) ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  have hg := geom_conv_le hρ0 (by positivity : 0 ≤ q ^ 2) (Ne.symm hqρ) k
  have hA0 : 0 ≤ A0 := (ha 0).trans ha0
  have hm1 : ρ ^ k ≤ max ρ (q ^ 2) ^ k := pow_le_pow_left₀ hρ0 (le_max_left _ _) k
  have hfin : a k ≤ max ρ (q ^ 2) ^ k * (A0 + (1 - ρ) * B0 / |ρ - q ^ 2|) := by
    rw [hsum] at hacc
    have h1 : (1 - ρ) * (B0 * ∑ i ∈ range k, ρ ^ (k - 1 - i) * (q ^ 2) ^ i)
        ≤ (1 - ρ) * (B0 * (max ρ (q ^ 2) ^ k / |ρ - q ^ 2|)) := by
      gcongr <;> linarith
    have h2 : ρ ^ k * A0 ≤ max ρ (q ^ 2) ^ k * A0 := mul_le_mul_of_nonneg_right hm1 hA0
    have e : max ρ (q ^ 2) ^ k * (A0 + (1 - ρ) * B0 / |ρ - q ^ 2|)
        = max ρ (q ^ 2) ^ k * A0 + (1 - ρ) * (B0 * (max ρ (q ^ 2) ^ k / |ρ - q ^ 2|)) := by ring
    rw [e]; linarith
  refine ⟨hfin, fun d hd => hd.trans (Real.sqrt_le_sqrt ?_)⟩
  gcongr

/-- The (S5A) count of k_ε as a function of r = ‖R(y₀)‖ (landed; the interface of
Corollary H5.10(b)): 1 if τ = L, else max{0, ⌈log((2L/τ − 1)r/ε)/log(L/(L − τ))⌉}. -/
noncomputable def Kcount (L τ r ε : ℝ) : ℕ :=
  if τ = L then 1 else ⌈Real.log ((2 * L / τ - 1) * r / ε) / Real.log (L / (L - τ))⌉₊

/-- 𝖪_{k,l} of Corollary H5.10(b): 1 if τ_l = L_l, else
max{0, ⌈log((2L_l/τ_l − 1)·4L_l·(2(A_k + q^{2k}Γ̄₀)/τ_l)^{1/2}/(η̄_l q^k))/log(1/q_l)⌉},
q_l = 1 − τ_l/L_l. -/
noncomputable def Kkl (L τ ηl q Ak Γ0 : ℝ) (k : ℕ) : ℕ :=
  if τ = L then 1 else
    ⌈Real.log ((2 * L / τ - 1) * (4 * L) * √(2 * (Ak + q ^ (2 * k) * Γ0) / τ) / (ηl * q ^ k))
      / Real.log (1 / (1 - τ / L))⌉₊

lemma log_ratio_eq {L τ : ℝ} (hτ : 0 < τ) (hτL : τ < L) :
    Real.log (L / (L - τ)) = Real.log (1 / (1 - τ / L)) := by
  congr 1; have : 0 < L := hτ.trans hτL; field_simp

lemma log_ratio_pos {L τ : ℝ} (hτ : 0 < τ) (hτL : τ < L) : 0 < Real.log (1 / (1 - τ / L)) := by
  have hL : 0 < L := hτ.trans hτL
  apply Real.log_pos
  have h1 : 0 < 1 - τ / L := by rw [sub_pos, div_lt_one hL]; exact hτL
  have h2 : 1 - τ / L < 1 := by have : 0 < τ / L := div_pos hτ hL; linarith
  rw [lt_div_iff₀ h1]; linarith

/-- Monotonicity of ⌈log(·)/λ⌉₊ from a nonnegative argument (log 0 = 0 in Lean). -/
lemma ceil_log_mono {a b lam : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hlam : 0 < lam) :
    ⌈Real.log a / lam⌉₊ ≤ ⌈Real.log b / lam⌉₊ := by
  rcases ha.eq_or_lt with h | h
  · rw [← h, Real.log_zero, zero_div, Nat.ceil_zero]; exact Nat.zero_le _
  · exact Nat.ceil_mono (div_le_div_of_nonneg_right (Real.log_le_log h hab) hlam.le)

/-- **Corollary H5.10(b).** One (fb) call (block l, sweep k) on the slice in regime A
(0 < τ_l ≤ L_l) with target η̄_l q^k, interface hypotheses: (S5A) bounds its steps by
`Kcount L τ ‖R(y₀)‖ (η̄_l q^k/2) + 1` (Step 6.1); thm:fb-residual(b) gives
‖R(y₀)‖ ≤ 2L_l‖y₀ − y*‖; (Q) gives (τ_l/2)‖y₀ − y*‖² ≤ Φ(y₀) − Φ(y*); the block line of
h4-thm:stitch(a) with (CS) gives Φ(y₀) − Φ(y*) ≤ a_k + Γ_k; and a_k ≤ A_k (part (a)),
Γ_k ≤ q^{2k}Γ̄₀. Then the call takes at most 𝖪_{k,l} + 1 steps. -/
theorem cor_b {L τ ηl q Ak Γ0 r d G ak Γk : ℝ} {k steps : ℕ} (hτ : 0 < τ) (hτL : τ ≤ L)
    (hηl : 0 < ηl) (hq : 0 < q) (hr0 : 0 ≤ r) (hd0 : 0 ≤ d)
    (hsteps : steps ≤ Kcount L τ r (ηl * q ^ k / 2) + 1) (hR : r ≤ 2 * L * d)
    (hgrow : τ / 2 * d ^ 2 ≤ G) (hG : G ≤ ak + Γk) (hak : ak ≤ Ak)
    (hΓ : Γk ≤ q ^ (2 * k) * Γ0) : steps ≤ Kkl L τ ηl q Ak Γ0 k + 1 := by
  unfold Kcount at hsteps
  unfold Kkl
  split_ifs at hsteps ⊢ with h
  · exact hsteps
  have hτL' : τ < L := lt_of_le_of_ne hτL h
  have hL : 0 < L := hτ.trans hτL'
  have hc : 0 < 2 * L / τ - 1 := by
    have : 2 < 2 * L / τ := by rw [lt_div_iff₀ hτ]; linarith
    linarith
  have hqk : 0 < ηl * q ^ k := by positivity
  have hdd : d ≤ √(2 * (Ak + q ^ (2 * k) * Γ0) / τ) := by
    have h1 : d ^ 2 ≤ 2 * (Ak + q ^ (2 * k) * Γ0) / τ := by
      rw [le_div_iff₀ hτ]; nlinarith
    calc d = √(d ^ 2) := (Real.sqrt_sq hd0).symm
      _ ≤ _ := Real.sqrt_le_sqrt h1
  have harg : (2 * L / τ - 1) * r / (ηl * q ^ k / 2)
      ≤ (2 * L / τ - 1) * (4 * L) * √(2 * (Ak + q ^ (2 * k) * Γ0) / τ) / (ηl * q ^ k) := by
    rw [show (2 * L / τ - 1) * r / (ηl * q ^ k / 2) = (2 * L / τ - 1) * (2 * r) / (ηl * q ^ k) by
      field_simp]
    apply div_le_div_of_nonneg_right _ hqk.le
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hc.le
    nlinarith
  have := ceil_log_mono (by positivity) harg (log_ratio_pos hτ hτL')
  rw [log_ratio_eq hτ hτL'] at hsteps
  omega

/-- **Corollary H5.10(c), part 1.** If q² ≥ ρ_θ (so A_k = q^{2k}C_A), the per-call bound does
not depend on the sweep index: 𝖪_{k,l} = 𝖪_{0,l}. -/
theorem cor_c_uniform {L τ ηl q CA Γ0 : ℝ} (hτ : 0 < τ) (hq : 0 < q) (hηl : 0 < ηl)
    (hCG : 0 ≤ CA + Γ0) (k : ℕ) :
    Kkl L τ ηl q ((q ^ 2) ^ k * CA) Γ0 k = Kkl L τ ηl q CA Γ0 0 := by
  unfold Kkl
  split_ifs with h
  · rfl
  congr 3
  simp only [pow_zero, mul_zero, mul_one, one_mul]
  have hqk : 0 < q ^ k := pow_pos hq k
  rw [show (q ^ 2) ^ k * CA + q ^ (2 * k) * Γ0 = (q ^ k) ^ 2 * (CA + Γ0) by ring_nf,
    show 2 * ((q ^ k) ^ 2 * (CA + Γ0)) / τ = (q ^ k) ^ 2 * (2 * (CA + Γ0) / τ) by ring,
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hqk.le]
  field_simp

/-- **Corollary H5.10(c), part 2 (total work).** If every call of sweep k < K takes at most
𝖪_{0,l} + 1 steps, the K sweeps take at most K·Σ_l(𝖪_{0,l} + 1) steps. -/
theorem cor_c_total {steps : ℕ → B → ℕ} {K0 : B → ℕ} (K : ℕ)
    (h : ∀ k < K, ∀ l, steps k l ≤ K0 l + 1) :
    ∑ k ∈ range K, ∑ l, steps k l ≤ K * ∑ l, (K0 l + 1) := by
  calc ∑ k ∈ range K, ∑ l, steps k l ≤ ∑ k ∈ range K, ∑ l, (K0 l + 1) :=
        Finset.sum_le_sum fun k hk => Finset.sum_le_sum fun l _ => h k (Finset.mem_range.1 hk) l
    _ = K * ∑ l, (K0 l + 1) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **Corollary H5.10(c), part 3.** a_K ≤ q^{2K}C_A ≤ δ once K ≥ log(C_A/δ)/(2 log(1/q))
(0 < δ < C_A, q ∈ (0, 1)): O(log(1/δ)) sweeps, each of bounded work. -/
theorem cor_c_sweeps {q CA δ : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hδ : 0 < δ) (hδC : δ < CA)
    {K : ℕ} (hK : Real.log (CA / δ) / (2 * Real.log (1 / q)) ≤ K) : (q ^ 2) ^ K * CA ≤ δ := by
  have hC : 0 < CA := hδ.trans hδC
  have hl : 0 < Real.log (1 / q) := Real.log_pos (by rw [lt_div_iff₀ hq0]; linarith)
  have h1 : Real.log (CA / δ) ≤ K * (2 * Real.log (1 / q)) := by
    rwa [div_le_iff₀ (by positivity)] at hK
  have hlq : Real.log (1 / q) = -Real.log q := by rw [one_div, Real.log_inv]
  have hpow : Real.log ((q ^ 2) ^ K) = K * (2 * Real.log q) := by
    rw [← pow_mul, Real.log_pow]; push_cast; ring
  have h2 : Real.log ((q ^ 2) ^ K) ≤ Real.log (δ / CA) := by
    rw [hpow, Real.log_div hδ.ne' hC.ne']
    rw [Real.log_div hC.ne' hδ.ne', hlq] at h1
    linarith
  have h3 : (q ^ 2) ^ K ≤ δ / CA :=
    (Real.log_le_log_iff (by positivity) (by positivity)).1 h2
  rwa [le_div_iff₀ hC] at h3

lemma sqrt_pow' {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : √(x ^ n) = √x ^ n := by
  rw [show x ^ n = (√x ^ n) ^ 2 by rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt hx]]
  exact Real.sqrt_sq (by positivity)

/-- **Corollary H5.10(d).** If q² < ρ_θ (so A_k = ρ_θ^k C_A), the per-call bound grows at most
linearly: 𝖪_{k,l} ≤ 𝖪_{0,l} + ⌈k log(√ρ_θ/q)/log(1/q_l)⌉. -/
theorem cor_d {L τ ηl q ρ CA Γ0 : ℝ} (hτ : 0 < τ) (hτL : τ ≤ L) (hq : 0 < q) (hηl : 0 < ηl)
    (hqρ : q ^ 2 < ρ) (hCA : 0 ≤ CA) (hΓ0 : 0 ≤ Γ0) (k : ℕ) :
    Kkl L τ ηl q (ρ ^ k * CA) Γ0 k
      ≤ Kkl L τ ηl q CA Γ0 0 + ⌈k * Real.log (√ρ / q) / Real.log (1 / (1 - τ / L))⌉₊ := by
  unfold Kkl
  split_ifs with h
  · exact Nat.le_add_right _ _
  have hτL' : τ < L := lt_of_le_of_ne hτL h
  have hL : 0 < L := hτ.trans hτL'
  have hlam := log_ratio_pos hτ hτL'
  set lam := Real.log (1 / (1 - τ / L))
  have hc : 0 < (2 * L / τ - 1) * (4 * L) := by
    have : 2 < 2 * L / τ := by rw [lt_div_iff₀ hτ]; linarith
    have : 0 < 2 * L / τ - 1 := by linarith
    positivity
  set c := (2 * L / τ - 1) * (4 * L)
  have hρ : 0 < ρ := (pow_pos hq 2).trans hqρ
  have hsρ : q < √ρ := by
    rw [show q = √(q ^ 2) from (Real.sqrt_sq hq.le).symm]; exact Real.sqrt_lt_sqrt (by positivity) hqρ
  set t := √ρ / q
  have ht : 1 < t := by rw [lt_div_iff₀ hq]; linarith
  set arg0 := c * √(2 * (CA + q ^ (2 * 0) * Γ0) / τ) / (ηl * q ^ 0)
  set argk := c * √(2 * (ρ ^ k * CA + q ^ (2 * k) * Γ0) / τ) / (ηl * q ^ k)
  have hq2k : q ^ (2 * k) ≤ ρ ^ k := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hqρ.le k
  have harg : argk ≤ arg0 * t ^ k := by
    have h1 : ρ ^ k * CA + q ^ (2 * k) * Γ0 ≤ ρ ^ k * (CA + Γ0) := by nlinarith
    have h2 : √(2 * (ρ ^ k * CA + q ^ (2 * k) * Γ0) / τ) ≤ √ρ ^ k * √(2 * (CA + Γ0) / τ) := by
      calc _ ≤ √(ρ ^ k * (2 * (CA + Γ0) / τ)) := Real.sqrt_le_sqrt (by
              rw [show ρ ^ k * (2 * (CA + Γ0) / τ) = 2 * (ρ ^ k * (CA + Γ0)) / τ by ring]
              gcongr)
        _ = √ρ ^ k * √(2 * (CA + Γ0) / τ) := by
              rw [Real.sqrt_mul (by positivity), sqrt_pow' hρ.le]
    have hqk : 0 < q ^ k := pow_pos hq k
    simp only [argk, arg0, pow_zero, mul_zero, one_mul, mul_one, t, div_pow]
    rw [div_le_iff₀ (by positivity)]
    calc c * √(2 * (ρ ^ k * CA + q ^ (2 * k) * Γ0) / τ)
        ≤ c * (√ρ ^ k * √(2 * (CA + Γ0) / τ)) := mul_le_mul_of_nonneg_left h2 hc.le
      _ = c * √(2 * (CA + Γ0) / τ) / ηl * (√ρ ^ k / q ^ k) * (ηl * q ^ k) := by
          field_simp
  have hargk0 : 0 ≤ argk := by positivity
  rcases hargk0.eq_or_lt with h0 | hpos
  · rw [← h0, Real.log_zero, zero_div, Nat.ceil_zero]; exact Nat.zero_le _
  · have hrhs : 0 < arg0 * t ^ k := hpos.trans_le harg
    have harg0 : 0 < arg0 := by
      have : 0 < t ^ k := pow_pos (by linarith) k
      exact pos_of_mul_pos_left hrhs this.le
    have hlog : Real.log argk ≤ Real.log arg0 + k * Real.log t := by
      calc Real.log argk ≤ Real.log (arg0 * t ^ k) := Real.log_le_log hpos harg
        _ = Real.log arg0 + k * Real.log t := by
            rw [Real.log_mul harg0.ne' (pow_pos (by linarith) k).ne', Real.log_pow]
    calc ⌈Real.log argk / lam⌉₊ ≤ ⌈Real.log arg0 / lam + k * Real.log t / lam⌉₊ := by
          apply Nat.ceil_mono; rw [← add_div]; exact div_le_div_of_nonneg_right hlog hlam.le
      _ ≤ ⌈Real.log arg0 / lam⌉₊ + ⌈k * Real.log t / lam⌉₊ := Nat.ceil_add_le _ _

end Counts

/-! ## §7 Soundness for pipelines (Definitions H5.5–H5.7, Theorem H5.9)

The grammar is an inductive type `Node` (rules fb, inx, cons, stitch; a stitch has m block
pipelines, each one term used on the slice at every x — UNI) and a root `pick` over finitely
many nodes (picks below a pick are flattened, `minOver_sigma`; a pick is not admissible below a
stitch, Proposition H5.12(a)). Targets are split targets bundled with their space (`Tgt`),
reports are `Rep t`. Executions are types (`Exec`), each with its report sequence (`out`), so
counts are functions of the execution. The leaf rules enter through interface hypotheses (the
fields of `LeafSem`, the H1 pattern): Lemma H5.3(i)–(iii) (`report`), the landed theorem of
the row (`sound`) and Lemma H5.8(a)–(c) (`livecount`). The stitch rule has NO interface: its
target is a block target (`BlockTgt`), each call runs on the slice at the sweep point built
from the earlier outputs (`StitchEx`), the execution is a stitched run of H4 (`StitchEx.toRun`),
and its clauses are H4's Lean theorems (`BlockTgt.h4Clauses`) with Lemma H5.8(d)
(`StitchEx.apriori`, `StitchEx.live_count`). Lemma H5.2 (A) and the pick theorem are the
theorems proved above. -/

section Pipelines

/-- A split target (SC3) bundled with its space: the target `tgt(𝔔)` of a node. -/
structure Tgt : Type 1 where
  X : Type
  [ng : NormedAddCommGroup X]
  [ip : InnerProductSpace ℝ X]
  [cs : CompleteSpace X]
  N : Type
  [fN : Fintype N]
  F : X → ℝ
  σF : ℝ
  D : N → Set X
  g : N → X → ℝ
  σ : N → ℝ
  split : SplitTarget F σF D g σ

attribute [instance] Tgt.ng Tgt.ip Tgt.cs Tgt.fN

/-- A composite report (x̂, (v_j, ε_j)_j) for t (u = ∇F(x̂) + Σ_j v_j is computed). -/
structure Rep (t : Tgt) where
  xh : t.X
  v : t.N → t.X
  ε : t.N → ℝ

namespace Rep

variable {t : Tgt}

/-- Definition H5.1: r is a composite report of t. -/
def Valid (r : Rep t) : Prop := IsReport t.D t.g r.xh r.v r.ε

/-- ‖u‖. -/
noncomputable def unorm (r : Rep t) : ℝ := ‖uR t.F r.v r.xh‖

/-- ε = Σ_j ε_j. -/
def acc (r : Rep t) : ℝ := accR r.ε

/-- The report meets the target (η̄, ε̄): ‖u‖ ≤ η̄ and ε ≤ ε̄ (Definition H5.6). -/
def Meets (r : Rep t) (η ε : ℝ) : Prop := r.unorm ≤ η ∧ r.acc ≤ ε

/-- Clause (A) at r: if μ_E > 0 and s > 0, then for the minimiser x* (existence classical,
B&C Cor. 11.17: a hypothesis) ‖x̂ − x*‖ ≤ τ_R and ℓ_R ≤ min E ≤ E(x̂). -/
def Cert (r : Rep t) : Prop :=
  0 < muHat t.σF t.σ → 0 < sR t.σF t.σ r.ε → ∀ xs, IsMinD (domE t.D) (Eval t.F t.g) xs →
    ‖r.xh - xs‖ ≤ tauRep t.F t.σF t.σ r.xh r.v r.ε ∧
    ellRep t.F t.σF t.g t.σ r.xh r.v r.ε ≤ Eval t.F t.g xs ∧ Eval t.F t.g xs ≤ Eval t.F t.g r.xh

/-- Lemma H5.2 gives (A) at every composite report. -/
theorem cert_of_valid {r : Rep t} (h : r.Valid) : r.Cert := fun hμ hs xs hxs => by
  obtain ⟨-, ⟨hc, -⟩, ⟨-, hl, hu, -⟩⟩ := lemma_H5_2 t.split h hμ hs hxs
  exact ⟨hc, hl, hu⟩

end Rep

/-- The stopping index of a target rule: n is the first output meeting (η̄, ε̄). -/
def FirstMeet {t : Tgt} (rs : ℕ → Rep t) (η ε : ℝ) (n : ℕ) : Prop :=
  (rs n).Meets η ε ∧ ∀ j < n, ¬ (rs j).Meets η ε

open Classical in
/-- If some output meets the target, the first one does, and it comes no later. -/
lemma exists_firstMeet {t : Tgt} {rs : ℕ → Rep t} {η ε : ℝ} {k : ℕ} (hk : (rs k).Meets η ε) :
    ∃ n ≤ k, FirstMeet rs η ε n := by
  have hex : ∃ j, (rs j).Meets η ε := ⟨k, hk⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hk, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩


/-- The declared part of a block target (Definition H5.5): block spaces, the declared
numbers σ, τ_l, L_{jl}, and for each block the terms g_{l,i} with their declared moduli. A
stitch node carries it; only F (and so the slice φ_{x,l}) varies with the target (UNI). -/
structure BlockDecl (m : ℕ) : Type 1 where
  Xb : Fin m → Type
  [ng : ∀ l, NormedAddCommGroup (Xb l)]
  [ip : ∀ l, InnerProductSpace ℝ (Xb l)]
  [cs : ∀ l, CompleteSpace (Xb l)]
  σ : ℝ
  τ : Fin m → ℝ
  L : Fin m → Fin m → ℝ
  Nl : Fin m → Type
  [fN : ∀ l, Fintype (Nl l)]
  Dl : ∀ l, Nl l → Set (Xb l)
  gl : ∀ l, Nl l → Xb l → ℝ
  σl : ∀ l, Nl l → ℝ

/-- **Definition H5.5, block target (BT)** with m blocks: block spaces `Xb l`, F ∈ C¹ on
ℝ^d = `PiLp 2 Xb` with C(F, σ), σ > 0 (SD4), slice moduli τ_l > 0 (SD5), cross constants
L_{jl} ≥ 0 (SD6), and for each block l the terms g_{l,i} (`gl l i` on `Dl l i`) with their
declarations C(g_{l,i}, σ_{l,i}), σ_{l,i} ≥ 0. g_l := Σ_i g_{l,i}, g(x) := Σ_l g_l(x_l). -/
structure BlockTgt (m : ℕ) : Type 1 where
  Xb : Fin m → Type
  [ng : ∀ l, NormedAddCommGroup (Xb l)]
  [ip : ∀ l, InnerProductSpace ℝ (Xb l)]
  [cs : ∀ l, CompleteSpace (Xb l)]
  F : PiLp 2 Xb → ℝ
  σ : ℝ
  τ : Fin m → ℝ
  L : Fin m → Fin m → ℝ
  Nl : Fin m → Type
  [fN : ∀ l, Fintype (Nl l)]
  Dl : ∀ l, Nl l → Set (Xb l)
  gl : ∀ l, Nl l → Xb l → ℝ
  σl : ∀ l, Nl l → ℝ
  diff : Differentiable ℝ F
  modF : ModC F σ
  sigma_pos : 0 < σ
  slice : H4.SliceMod F τ
  tau_pos : ∀ l, 0 < τ l
  cross : H4.CrossConst F L
  L_nonneg : ∀ j l, 0 ≤ L j l
  curv : ∀ l i, ExtModC (Dl l i) (gl l i) (σl l i)
  sigma_nonneg : ∀ l i, 0 ≤ σl l i

attribute [instance] BlockTgt.ng BlockTgt.ip BlockTgt.cs BlockTgt.fN

/-- A declared modulus s ≥ 0 gives convexity (modulus 0). -/
lemma extModC_zero_of_nonneg {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    {D : Set Y} {g : Y → ℝ} {s : ℝ} (h : ExtModC D g s) (hs : 0 ≤ s) : ExtModC D g 0 := by
  unfold ExtModC at *
  have hq : ConvexOn ℝ D (fun y : Y => s / 2 * ‖y‖ ^ 2) :=
    ((H4.convexOn_norm_sq.subset (subset_univ D) h.1).smul
      (by positivity : (0 : ℝ) ≤ s / 2)).congr fun y _ => by simp [smul_eq_mul]
  exact (h.add hq).congr fun y _ => by simp

namespace BlockTgt

variable {m : ℕ} (B : BlockTgt m)

/-- The declared part of B. -/
def decl : BlockDecl m := ⟨B.Xb, B.σ, B.τ, B.L, B.Nl, B.Dl, B.gl, B.σl⟩

/-- dom g_l = ⋂_i dom g_{l,i}. -/
def Dh (l : Fin m) : Set (B.Xb l) := domE (B.Dl l)
/-- g_l = Σ_i g_{l,i}. -/
def gh (l : Fin m) (y : B.Xb l) : ℝ := ∑ i, B.gl l i y
/-- dom g = dom g₁ × ⋯ × dom g_m. -/
def dom : Set (PiLp 2 B.Xb) := H4.domG B.Dh
/-- The block projection U_lᵀ : x ↦ x_l. -/
noncomputable def prj (l : Fin m) : PiLp 2 B.Xb →L[ℝ] B.Xb l := PiLp.proj (𝕜 := ℝ) 2 B.Xb l

lemma prj_apply (l : Fin m) (x : PiLp 2 B.Xb) : B.prj l x = x l := rfl

lemma curv0 (l : Fin m) (i : B.Nl l) : ExtModC (B.Dl l i) (B.gl l i) 0 :=
  extModC_zero_of_nonneg (B.curv l i) (B.sigma_nonneg l i)

/-- g_l is convex on dom g_l (H4's SD3 for the block target). -/
lemma convex_gh (l : Fin m) : ModCD (B.Dh l) (B.gh l) 0 := by
  have hT : SplitTarget (fun _ : B.Xb l => (0 : ℝ)) 0 (B.Dl l) (B.gl l) (B.σl l) :=
    ⟨differentiable_const 0, by unfold ModC; simpa using convexOn_const (0 : ℝ) convex_univ,
      B.curv l, B.sigma_nonneg l⟩
  have h := extModC_zero_of_nonneg (extModC_Eval hT)
    (by unfold muHat; simpa using Finset.sum_nonneg fun i _ => B.sigma_nonneg l i)
  unfold ModCD; unfold ExtModC at h
  exact h.congr fun y _ => by simp [Eval, gh]

/-- The block target satisfies H4's standing data SD2–SD6. -/
lemma sd : H4.SD B.F B.Dh B.gh B.σ B.τ B.L :=
  ⟨B.diff, B.modF, B.sigma_pos, B.convex_gh, B.slice, B.tau_pos, B.cross, B.L_nonneg⟩

/-- The target E_B of a stitch as a split target (Lemma H5.3(iv)): smooth part F with
σ_F := σ, terms g_{l,i} ∘ U_lᵀ (index set Σ_l N_l) declared with modulus 0. -/
@[reducible] noncomputable def tgt : Tgt where
  X := PiLp 2 B.Xb
  N := Σ l, B.Nl l
  F := B.F
  σF := B.σ
  D := fun j => B.prj j.1 ⁻¹' B.Dl j.1 j.2
  g := fun j y => B.gl j.1 j.2 (B.prj j.1 y)
  σ := fun _ => 0
  split := ⟨B.diff, B.modF, fun j => extModC_comp (B.prj j.1) (B.curv0 j.1 j.2), fun _ => le_rfl⟩

/-- **Lemma H5.4(a), the slice specification** 𝔈_{x,l}: one smooth term
φ_{x,l}(y) = F(x + U_l(y − x_l)) (H4's `slice`) with σ_F := τ_l, and the terms g_{l,i} with
their declarations. -/
@[reducible] noncomputable def sliceT (x : PiLp 2 B.Xb) (l : Fin m) : Tgt where
  X := B.Xb l
  N := B.Nl l
  F := H4.slice B.F x l
  σF := B.τ l
  D := B.Dl l
  g := B.gl l
  σ := B.σl l
  split := ⟨H4.differentiable_slice B.diff x l, B.slice x l, B.curv l, B.sigma_nonneg l⟩

end BlockTgt


/-- The semantics of a leaf rule (fb, inx or cons) and its row's theorems (interface
hypotheses). `Ex a t` is the type of executions of the leaf on t (each records its initial
point, oracle answers and iterates); `out e` is its report sequence. The count of an
execution may depend on the execution (its start: E(x₀), E(x_k̄), D̄₀ in Lemma H5.8). -/
structure LeafSem (A : Type) where
  /-- well typed on t (def:fb-typed; inexact typing; def:h3-consensus with L_j < ∞). -/
  typed : A → Tgt → Prop
  Ex : A → Tgt → Type
  out : {a : A} → {t : Tgt} → Ex a t → ℕ → Rep t
  /-- the run clauses of the row (thm:soundness; h2-thm:inexact-soundness; thm:h3-soundness
  and thm:h3-certificate), with the row's bounds on ‖u‖ and ε. -/
  clauses : (a : A) → (t : Tgt) → Ex a t → Prop
  /-- the live condition of the row for the target (η̄, ε̄). -/
  live : A → Tgt → ℝ → ℝ → Prop
  /-- the count of Lemma H5.8(a)–(c), a function of the execution. -/
  count : (a : A) → (t : Tgt) → Ex a t → ℝ → ℝ → ℕ
  /-- Lemma H5.3(i)–(iii): every output carries a composite report of the target. -/
  report : ∀ a t (e : Ex a t), typed a t → ∀ k, (out e k).Valid
  /-- the landed theorem of the row. -/
  sound : ∀ a t (e : Ex a t), typed a t → clauses a t e
  /-- Lemma H5.8(a)–(c). -/
  livecount : ∀ a t η ε (e : Ex a t), typed a t → live a t η ε →
    ∃ k ≤ count a t e η ε, (out e k).Meets η ε

/-- The semantics of the leaf rules (Definitions H5.6, H5.7). The stitch rule has no
interface: its semantics is concrete and its theorems are H4's. -/
structure Sem (A I C : Type) where
  fb : LeafSem A
  inx : LeafSem I
  cons : LeafSem C

/-- **Definition H5.5 (grammar, non-pick part).** fb(𝔈, T), inx(𝔈, T, 𝒪), cons(𝔈, T, j₀)
(leaf data `A`, `I`, `C`) and stitch(𝔅, (𝔓_l)_{l<m}, (η̄_{k,l}, ε̄_{k,l})) with the declared
part of 𝔅 (`BlockDecl`) and a declared θ (used by the live condition and count of
Lemma H5.8(d)). The block target 𝔅 with that declared part is the target of the node. A block pipeline is one term `ch l`, used on the slice at every x
(UNI). -/
inductive Node (A I C : Type) : Type 1
  | fb : A → Node A I C
  | inx : I → Node A I C
  | cons : C → Node A I C
  | stitch : (m : ℕ) → BlockDecl m → ℝ → (ℕ → Fin m → ℝ) → (ℕ → Fin m → ℝ) →
      (Fin m → Node A I C) → Node A I C

/-- **Definition H5.6, an execution of a stitch** on the block target B, from x⁰ ∈ dom g:
the sweep points x k i = x^{k,i} (H4's indexing, blocks 0-based); the call of block l in sweep
k is an execution `call k l` of the child ON THE SLICE AT x^{k,l} (the point built from the
earlier outputs of the sweep), stopped at the first output `n k l` meeting (η̄_{k,l}, ε̄_{k,l});
its final report's point z gives x^{k,l+1} = x^{k,l} + U_l(z − x^{k,l}_l), and
x^{k+1,0} = x^{k,m}. `Ex`, `out` are the executions and report sequences of the children. The
start y₀ = x^k_l of a call is not constrained (any start). -/
structure StitchEx {m : ℕ} (B : BlockTgt m) (ηb εb : ℕ → Fin m → ℝ)
    (Ex : Fin m → Tgt → Type 1) (out : ∀ l t, Ex l t → ℕ → Rep t) : Type 1 where
  x : ℕ → ℕ → PiLp 2 B.Xb
  start : x 0 0 ∈ B.dom
  call : ∀ k (l : Fin m), Ex l (B.sliceT (x k l.val) l)
  n : ℕ → Fin m → ℕ
  stop : ∀ k l, FirstMeet (out l _ (call k l)) (ηb k l) (εb k l) (n k l)
  step : ∀ k (l : Fin m), x k (l.val + 1) = H4.upd (x k l.val) l (out l _ (call k l) (n k l)).xh
  next : ∀ k, x (k + 1) 0 = x k m

namespace StitchEx

variable {m : ℕ} {B : BlockTgt m} {ηb εb : ℕ → Fin m → ℝ} {Ex : Fin m → Tgt → Type 1}
  {out : ∀ l t, Ex l t → ℕ → Rep t} (se : StitchEx B ηb εb Ex out)

/-- The final report of the call (k, l). -/
noncomputable def fin (k : ℕ) (l : Fin m) : Rep (B.sliceT (se.x k l.val) l) :=
  out l _ (se.call k l) (se.n k l)

/-- The stitch report at x^{k+1} (Lemma H5.3(iv)): (x^{k+1}, (U_l v_{k,l,i}, ε_{k,l,i})), with the
term splits of the children's final reports. -/
noncomputable def rep (k : ℕ) : Rep B.tgt where
  xh := se.x (k + 1) 0
  v := fun j => H4.U j.1 ((se.fin k j.1).v j.2)
  ε := fun j => (se.fin k j.1).ε j.2

end StitchEx

variable {A I C : Type}

/-- **Definition H5.6 (executions).** The executions of a node on t and their report
sequences. A leaf: the executions of its rule. A stitch: a block target B with t = B.tgt and
the node's declared part, and an execution of the stitch on B (`StitchEx`) whose calls are executions of the children. -/
noncomputable def sem (σ : Sem A I C) :
    Node A I C → (t : Tgt) → (Σ E : Type 1, (E → ℕ → Rep t))
  | .fb a, t => ⟨ULift (σ.fb.Ex a t), fun e => σ.fb.out e.down⟩
  | .inx a, t => ⟨ULift (σ.inx.Ex a t), fun e => σ.inx.out e.down⟩
  | .cons a, t => ⟨ULift (σ.cons.Ex a t), fun e => σ.cons.out e.down⟩
  | .stitch m d _ ηb εb ch, t =>
    ⟨Σ B : BlockTgt m, PLift (t = B.tgt ∧ B.decl = d) ×
        StitchEx B ηb εb (fun l t' => (sem σ (ch l) t').1) (fun l t' => (sem σ (ch l) t').2),
     fun e k => cast (congrArg Rep e.2.1.down.1.symm) (e.2.2.rep k)⟩

/-- The executions of P on t. -/
abbrev Exec (σ : Sem A I C) (P : Node A I C) (t : Tgt) : Type 1 := (sem σ P t).1
/-- The report sequence of an execution. -/
noncomputable abbrev out (σ : Sem A I C) {P : Node A I C} {t : Tgt} (e : Exec σ P t) :
    ℕ → Rep t :=
  (sem σ P t).2 e



/-- Σ_l U_l w_l = (w_l)_l. -/
lemma sum_U {m : ℕ} {X : Fin m → Type*} [∀ l, NormedAddCommGroup (X l)]
    [∀ l, InnerProductSpace ℝ (X l)] [∀ l, CompleteSpace (X l)] (w : ∀ l, X l) :
    ∑ l, H4.U l (w l) = WithLp.toLp 2 w := by
  ext j
  simp only [WithLp.ofLp_sum, Finset.sum_apply]
  rw [Finset.sum_eq_single j (fun c _ hc => H4.U_ne (Ne.symm hc) _) (by simp), H4.U_same]

namespace StitchEx

variable {m : ℕ} {B : BlockTgt m} {ηb εb : ℕ → Fin m → ℝ} {Ex : Fin m → Tgt → Type 1}
  {out : ∀ l t, Ex l t → ℕ → Rep t} (se : StitchEx B ηb εb Ex out)

/-- Def. H4.0(d) along an execution: if the final report of every call made at a point of
dom g is valid, every sweep point x^{k,i} (i ≤ m) lies in dom g. -/
lemma mem_of_valid (hv : ∀ k (l : Fin m), se.x k l.val ∈ B.dom → (se.fin k l).Valid) :
    ∀ k i, i ≤ m → se.x k i ∈ B.dom := by
  intro k
  induction k with
  | zero =>
    intro i
    induction i with
    | zero => intro _; exact se.start
    | succ i ih =>
      intro hi
      have hx := ih (by omega)
      rw [show i = (⟨i, by omega⟩ : Fin m).val from rfl] at hx ⊢
      rw [se.step 0 ⟨i, by omega⟩]
      exact H4.upd_mem hx (hv 0 ⟨i, by omega⟩ hx).mem
  | succ k ihk =>
    intro i
    induction i with
    | zero => intro _; rw [se.next]; exact ihk m le_rfl
    | succ i ih =>
      intro hi
      have hx := ih (by omega)
      rw [show i = (⟨i, by omega⟩ : Fin m).val from rfl] at hx ⊢
      rw [se.step (k + 1) ⟨i, by omega⟩]
      exact H4.upd_mem hx (hv (k + 1) ⟨i, by omega⟩ hx).mem

/-- The stitched run (h4-def:report) of the execution, from valid child reports. -/
noncomputable def toRun (hv : ∀ k l, (se.fin k l).Valid) : H4.Run B.Dh B.gh where
  x := se.x
  z := fun k l => (se.fin k l).xh
  v := fun k l => ∑ i, (se.fin k l).v i
  ε := fun k l => (se.fin k l).acc
  start := se.start
  step := se.step
  next := se.next
  report := fun k l => ⟨accR_nonneg (hv k l), epsSubgrad_sum (hv k l)⟩

/-- R is the stitched run of the execution. -/
def IsRun (R : H4.Run B.Dh B.gh) : Prop :=
  R.x = se.x ∧ (∀ k l, R.z k l = (se.fin k l).xh) ∧ (∀ k l, R.v k l = ∑ i, (se.fin k l).v i) ∧
    ∀ k l, R.ε k l = (se.fin k l).acc

/-- `toRun` is a stitched run of the execution. -/
lemma isRun_toRun (hv : ∀ k l, (se.fin k l).Valid) : se.IsRun (se.toRun hv) :=
  ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

/-- The residual η_{k,l} of the stitched run is ‖u‖ of the child's final report
(Lemma H5.4(a)), and ε_{k,l} is its accuracy. -/
lemma eta_eq {R : H4.Run B.Dh B.gh} (hR : se.IsRun R) (k : ℕ) (l : Fin m) :
    R.eta B.F k l = (se.fin k l).unorm ∧ R.ε k l = (se.fin k l).acc := by
  obtain ⟨hx, hz, hv, he⟩ := hR
  refine ⟨?_, he k l⟩
  unfold H4.Run.eta Rep.unorm uR
  rw [hv k l, hx, se.step k l]
  change ‖gradient B.F (H4.upd (se.x k l.val) l (se.fin k l).xh) l + _‖
    = ‖gradient (H4.slice B.F (se.x k l.val) l) (se.fin k l).xh + _‖
  rw [H4.gradient_slice B.diff]

/-- Lemma H5.3(iv) at x^{k+1}: the stitch report is a composite report of E_B, with
‖u‖ = ‖u_k‖ (h4-lem:assembly) and ε = ε_k. -/
lemma rep_valid {R : H4.Run B.Dh B.gh} (hR : se.IsRun R) (hv : ∀ k l, (se.fin k l).Valid)
    (k : ℕ) : (se.rep k).Valid ∧ (se.rep k).unorm = ‖R.uk B.F k‖ ∧ (se.rep k).acc = R.epsk k := by
  have hadj : ∀ l (y : B.Xb l) (w : PiLp 2 B.Xb),
      inner ℝ (H4.U l y) w = inner ℝ y (B.prj l w) := by
    intro l y w
    rw [real_inner_comm, H4.inner_U, B.prj_apply, real_inner_comm]
  have hz : ∀ l, B.prj l (se.x (k + 1) 0) = (se.fin k l).xh := by
    intro l
    have h1 := R.next_block k l
    rw [hR.2.1, hR.1] at h1
    rw [B.prj_apply]; exact h1
  obtain ⟨-, hrep, hu, hacc, -, -⟩ := closure_stitch (B := Fin m) B.prj (fun l => H4.U l) hadj
    (I := B.Nl) (Dl := B.Dl) (gl := B.gl) B.diff B.modF B.curv0 hz
    (v := fun l i => (se.fin k l).v i) (ε := fun l i => (se.fin k l).ε i)
    (fun l i => hv k l i)
  refine ⟨hrep, ?_, ?_⟩
  · unfold Rep.unorm
    change ‖uR B.F (fun j : (Σ l, B.Nl l) => H4.U j.1 ((se.fin k j.1).v j.2)) (se.x (k + 1) 0)‖ = _
    rw [hu, H4.Run.uk, H4.Run.vk, sum_U, hR.1]
    congr 3
    funext l
    rw [hR.2.2.1]
  · unfold Rep.acc
    change accR (fun j : (Σ l, B.Nl l) => (se.fin k j.1).ε j.2) = _
    rw [hacc, H4.Run.epsk]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hR.2.2.2]; rfl

end StitchEx



namespace BlockTgt
variable {m : ℕ} (B : BlockTgt m)

/-- Λ = (Σ_{j<l} L_{jl}²/τ_l)^{1/2}. -/
noncomputable def Λ : ℝ := H4.Lam B.L B.τ
/-- ρ_θ. -/
noncomputable def ρθ (θ : ℝ) : ℝ := H4.rhoth θ B.Λ B.σ
/-- E* = inf E over dom g. -/
noncomputable def Estar : ℝ := sInf (H4.Efun B.F B.gh '' B.dom)

/-- With a minimiser x* (existence classical, B&C Cor. 11.17: a hypothesis), E* = E(x*). -/
lemma Estar_eq {xs : PiLp 2 B.Xb} (hxs : H4.IsMinE B.F B.Dh B.gh xs) :
    B.Estar = H4.Efun B.F B.gh xs :=
  IsLeast.csInf_eq ⟨⟨xs, hxs.1, rfl⟩, by rintro _ ⟨w, hw, rfl⟩; exact hxs.2 w hw⟩

/-- B̄_k(θ): B_k(θ) of h4-def:report at the declared targets (η̄_{k,l}, ε̄_{k,l}). -/
noncomputable def Bbar (θ : ℝ) (ηb εb : ℕ → Fin m → ℝ) (k : ℕ) : ℝ :=
  H4.Bfun B.τ B.Λ B.σ θ (ηb k) (εb k)

/-- A_k := ρ_θ^k Ā₀ + (1 − ρ_θ) Σ_{i<k} ρ_θ^{k−1−i} B̄_i(θ). -/
noncomputable def Aseq (θ : ℝ) (ηb εb : ℕ → Fin m → ℝ) (A0 : ℝ) (k : ℕ) : ℝ :=
  B.ρθ θ ^ k * A0 + (1 - B.ρθ θ) * ∑ i ∈ range k, B.ρθ θ ^ (k - 1 - i) * B.Bbar θ ηb εb i

/-- Ū_k := ‖η̄_k‖ + Λ(√(2(A_k + Γ̄_k)) + √(2Γ̄_k)) (Lemma H5.8(d)). -/
noncomputable def Ubar (θ : ℝ) (ηb εb : ℕ → Fin m → ℝ) (A0 : ℝ) (k : ℕ) : ℝ :=
  etaN (ηb k) + B.Λ * (√(2 * (B.Aseq θ ηb εb A0 k + GamF B.τ (ηb k) (εb k)))
    + √(2 * GamF B.τ (ηb k) (εb k)))

/-- A_{k+1} = ρ_θA_k + (1 − ρ_θ)B̄_k(θ). -/
lemma Aseq_succ (θ : ℝ) (ηb εb : ℕ → Fin m → ℝ) (A0 : ℝ) (k : ℕ) :
    B.Aseq θ ηb εb A0 (k + 1) = B.ρθ θ * B.Aseq θ ηb εb A0 k + (1 - B.ρθ θ) * B.Bbar θ ηb εb k := by
  unfold Aseq
  set ρ := B.ρθ θ
  have hsum : ∑ i ∈ range (k + 1), ρ ^ (k + 1 - 1 - i) * B.Bbar θ ηb εb i
      = ρ * ∑ i ∈ range k, ρ ^ (k - 1 - i) * B.Bbar θ ηb εb i + B.Bbar θ ηb εb k := by
    rw [Finset.sum_range_succ, Finset.mul_sum, show k + 1 - 1 - k = 0 by omega, pow_zero,
      one_mul]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [show k + 1 - 1 - i = (k - 1 - i) + 1 by omega, pow_succ]; ring
  rw [hsum, pow_succ]; ring

/-- B̄_k(θ) ≥ 0 when the declared accuracies are nonnegative. -/
lemma Bbar_nonneg {θ : ℝ} (hθ : 0 < θ) {ηb εb : ℕ → Fin m → ℝ} (hε : ∀ k l, 0 ≤ εb k l)
    (k : ℕ) : 0 ≤ B.Bbar θ ηb εb k := by
  have h1 := H4.cth_nonneg (Λ := B.Λ) hθ B.sigma_pos
  have h2 : 0 ≤ H4.Gfun B.τ (ηb k) (εb k) :=
    Finset.sum_nonneg fun l _ => by have := B.tau_pos l; have := hε k l; positivity
  have h3 : 0 ≤ ∑ l, εb k l := Finset.sum_nonneg fun l _ => hε k l
  have := B.sigma_pos
  unfold Bbar H4.Bfun; positivity

/-- h4-thm:stitch (a)–(d) and h4-lem:assembly(b) for a stitched run R of B, exactly as the
H4 Lean theorems state them (`Run.H4_4_c`, `Run.H4_6`, `Run.H4_7_a`, `Run.H4_7_a_zero`,
`Run.H4_7_b`, `Run.H4_7_c`, `Run.H4_7_c1`–`c3`, `Run.H4_7_d_declared`, `Run.H4_7_d_dist`). -/
def H4Clauses (R : H4.Run B.Dh B.gh) : Prop :=
  (∀ k, ‖R.uk B.F k‖ ≤ R.etan B.F k + B.Λ * R.Dk B.τ k) ∧
  ∀ xs, H4.IsMinE B.F B.Dh B.gh xs →
    (∀ k, (∀ l : Fin m, H4.Efun B.F B.gh (R.x k (l.val + 1))
          ≤ H4.Efun B.F B.gh (R.x k l.val) - B.τ l / 2 * ‖R.hm k l‖ ^ 2
            + R.eta B.F k l * ‖R.hm k l‖ + R.ε k l) ∧
        H4.Efun B.F B.gh (R.x (k + 1) 0) ≤ H4.Efun B.F B.gh (R.x k 0) + R.Gam B.F B.τ k ∧
        0 ≤ R.ak B.F xs k - R.ak B.F xs (k + 1) + R.Gam B.F B.τ k ∧
        R.ak B.F xs (k + 1) ≤ (R.Qk B.F B.τ B.Λ k
            + B.Λ * √(2 * (R.ak B.F xs k - R.ak B.F xs (k + 1) + R.Gam B.F B.τ k))) ^ 2
              / (2 * B.σ) + R.epsk k) ∧
    (∀ k, (∀ l, R.eta B.F k l = 0 ∧ R.ε k l = 0) →
      R.ak B.F xs (k + 1) ≤ H4.rho B.Λ B.σ * R.ak B.F xs k ∧
      (B.Λ = 0 → R.x (k + 1) 0 = xs)) ∧
    (∀ θ, 0 < θ →
      (∀ k, R.ak B.F xs (k + 1) ≤ B.ρθ θ * R.ak B.F xs k
          + (1 - B.ρθ θ) * R.Bk B.F B.τ B.Λ B.σ θ k) ∧
      (∀ k, R.ak B.F xs k ≤ B.ρθ θ ^ k * R.ak B.F xs 0
          + (1 - B.ρθ θ) * ∑ i ∈ range k, B.ρθ θ ^ (k - 1 - i) * R.Bk B.F B.τ B.Λ B.σ θ i) ∧
      (∀ k Bb, (∀ i < k, R.Bk B.F B.τ B.Λ B.σ θ i ≤ Bb) →
          R.ak B.F xs k ≤ B.ρθ θ ^ k * R.ak B.F xs 0 + (1 - B.ρθ θ ^ k) * Bb) ∧
      (∀ B0 q, 0 ≤ q → q < 1 → q ≠ B.ρθ θ → (∀ i, R.Bk B.F B.τ B.Λ B.σ θ i ≤ B0 * q ^ i) →
          ∀ k, R.ak B.F xs k ≤ max (B.ρθ θ) q ^ k
            * (R.ak B.F xs 0 + (1 - B.ρθ θ) * B0 / |B.ρθ θ - q|)) ∧
      (Tendsto (R.Bk B.F B.τ B.Λ B.σ θ) atTop (𝓝 0) →
          Tendsto (R.ak B.F xs) atTop (𝓝 0) ∧ Tendsto (fun k => R.x k 0) atTop (𝓝 xs)) ∧
      (∀ k (ηbar εbar : Fin m → ℝ), (∀ l, R.eta B.F k l ≤ ηbar l) → (∀ l, R.ε k l ≤ εbar l) →
          R.ak B.F xs (k + 1) ≤ B.ρθ θ * R.ak B.F xs k
            + (1 - B.ρθ θ) * H4.Bfun B.τ B.Λ B.σ θ ηbar εbar)) ∧
    (∀ k, ‖R.x k 0 - xs‖ ≤ √(2 * R.ak B.F xs k / B.σ))

/-- Every stitched run of B satisfies H4's theorem (discharged from the H4 Lean file). -/
theorem h4Clauses (R : H4.Run B.Dh B.gh) : B.H4Clauses R :=
  ⟨fun k => R.H4_4_c B.cross B.L_nonneg B.tau_pos k, fun _ hxs =>
    ⟨fun k => R.H4_6 B.sd hxs k,
      fun _ hex => ⟨R.H4_7_a B.sd hxs hex, fun hΛ => R.H4_7_a_zero B.sd hxs hΛ hex⟩,
      fun _ hθ => ⟨R.H4_7_b B.sd hxs hθ, R.H4_7_c B.sd hxs hθ,
        fun _ _ hB => R.H4_7_c1 B.sd hxs hθ hB,
        fun _ _ hq0 hq1 hne hB k => R.H4_7_c2 B.sd hxs hθ hq0 hq1 hne hB k,
        fun hB => R.H4_7_c3 B.sd hxs hθ hB,
        fun _ _ _ hη hε => R.H4_7_d_declared B.sd hxs hθ hη hε⟩,
      fun k => R.H4_7_d_dist B.sd hxs k⟩⟩

/-- The Minkowski step of the proof of h4-thm:stitch(a):
D_k ≤ √(2(a_k − a_{k+1} + Γ_k)) + √(2Γ_k) (from H4's `Run.step_H4_2`). -/
lemma Dk_le (R : H4.Run B.Dh B.gh) {xs : PiLp 2 B.Xb} (k : ℕ) :
    R.Dk B.τ k ≤ √(2 * (R.ak B.F xs k - R.ak B.F xs (k + 1) + R.Gam B.F B.τ k))
      + √(2 * R.Gam B.F B.τ k) := by
  have hτ := B.tau_pos
  have hst := fun l => R.step_H4_2 B.diff B.slice hτ k l
  have hsum : ∑ l : Fin m, (H4.Efun B.F B.gh (R.x k l.val) - H4.Efun B.F B.gh (R.x k (l.val + 1))
      + R.gam B.F B.τ k l) = R.ak B.F xs k - R.ak B.F xs (k + 1) + R.Gam B.F B.τ k := by
    rw [sum_add_distrib, H4.Run.sum_fin_telescope (fun i => H4.Efun B.F B.gh (R.x k i)),
      H4.Run.Gam, H4.Run.ak, H4.Run.ak, R.next]
    ring
  have e1 : R.Dk B.τ k = √(∑ l, (√(B.τ l) * ‖R.hm k l‖) ^ 2) := by
    unfold H4.Run.Dk; congr 1
    exact sum_congr rfl fun l _ => by rw [mul_pow, Real.sq_sqrt (hτ l).le]
  rw [e1]
  refine (H4.sqrt_sum_sq_mono _ (fun l _ => by positivity) (fun l _ => (hst l).2.2)).trans
    ((H4.sqrt_sum_add_sq_le _ _ _).trans (le_of_eq ?_))
  congr 2
  · rw [← hsum, mul_sum]
    exact sum_congr rfl fun l _ => Real.sq_sqrt (by linarith [(hst l).2.1])
  · rw [H4.Run.Gam, mul_sum]
    exact sum_congr rfl fun l _ =>
      Real.sq_sqrt (by have := R.gam_nonneg B.F hτ k l; linarith)

/-- The live condition of Lemma H5.8(d) for the stitch target (η̄, ε̄), with the declared
θ > 0. -/
def StitchLive (θ : ℝ) (ηb εb : ℕ → Fin m → ℝ) (η ε : ℝ) : Prop :=
  0 < θ ∧ 0 < η ∧ (∃ xs, H4.IsMinE B.F B.Dh B.gh xs) ∧
    Tendsto (B.Bbar θ ηb εb) atTop (𝓝 0) ∧ Tendsto (fun k => GamF B.τ (ηb k) (εb k)) atTop (𝓝 0) ∧
    Tendsto (fun k => etaN (ηb k)) atTop (𝓝 0) ∧ ∀ᶠ k in atTop, ∑ l, εb k l ≤ ε

open Classical in
/-- The count of Lemma H5.8(d): the least k with Ū_k ≤ η̄ and ε̄_k ≤ ε̄. -/
noncomputable def stitchCount (θ : ℝ) (ηb εb : ℕ → Fin m → ℝ) (A0 η ε : ℝ) : ℕ :=
  if h : ∃ k, B.Ubar θ ηb εb A0 k ≤ η ∧ ∑ l, εb k l ≤ ε then Nat.find h else 0

end BlockTgt

namespace StitchEx

variable {m : ℕ} {B : BlockTgt m} {ηb εb : ℕ → Fin m → ℝ} {Ex : Fin m → Tgt → Type 1}
  {out : ∀ l t, Ex l t → ℕ → Rep t} (se : StitchEx B ηb εb Ex out)

/-- ‖u‖ and ε of the stitch report are ‖u_k‖ (h4-lem:assembly) and ε_k of the run. -/
lemma rep_unorm_acc {R : H4.Run B.Dh B.gh} (hR : se.IsRun R) (k : ℕ) :
    (se.rep k).unorm = ‖R.uk B.F k‖ ∧ (se.rep k).acc = R.epsk k := by
  constructor
  · unfold Rep.unorm
    change ‖uR B.F (fun j : (Σ l, B.Nl l) => H4.U j.1 ((se.fin k j.1).v j.2)) (se.x (k + 1) 0)‖ = _
    unfold uR
    rw [Fintype.sum_sigma]
    have e : ∑ l, ∑ i, H4.U l ((se.fin k l).v i) = ∑ l, H4.U l (∑ i, (se.fin k l).v i) :=
      Finset.sum_congr rfl fun l _ => (map_sum (H4.U l) _ _).symm
    rw [e, H4.Run.uk, H4.Run.vk, sum_U, hR.1]
    congr 3
    funext l
    rw [hR.2.2.1]
  · unfold Rep.acc
    change accR (fun j : (Σ l, B.Nl l) => (se.fin k j.1).ε j.2) = _
    unfold accR
    rw [Fintype.sum_sigma, H4.Run.epsk]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hR.2.2.2]; rfl

/-- a₀ = E(x⁰) − E*. -/
noncomputable def a0 : ℝ := H4.Efun B.F B.gh (se.x 0 0) - B.Estar

/-- **Lemma H5.8(d) and the a-priori clauses of h4-thm:stitch(c),(d)** for the stitched run R
of the execution: every call met its declared target, so for every θ > 0, every minimiser x*
and every Ā₀ ≥ a₀: a_{k+1} ≤ ρ_θa_k + (1 − ρ_θ)B̄_k(θ), a_k ≤ A_k, and the stitch report at
x^{k+1} has ‖u‖ ≤ Ū_k and ε ≤ ε̄_k = Σ_l ε̄_{k,l}. -/
def Apriori (R : H4.Run B.Dh B.gh) (θ : ℝ) : Prop :=
  ∀ xs, H4.IsMinE B.F B.Dh B.gh xs → ∀ A0, R.ak B.F xs 0 ≤ A0 → ∀ k,
    R.ak B.F xs (k + 1) ≤ B.ρθ θ * R.ak B.F xs k + (1 - B.ρθ θ) * B.Bbar θ ηb εb k ∧
    R.ak B.F xs k ≤ B.Aseq θ ηb εb A0 k ∧
    (se.rep k).unorm ≤ B.Ubar θ ηb εb A0 k ∧ (se.rep k).acc ≤ ∑ l, εb k l

/-- The a-priori clauses, from H4 (`Run.H4_7_b`, `Run.H4_4_c`, `Run.H4_7_d_declared`, the
Minkowski step `Dk_le`) and Lemma H5.8(d) (`live_stitch`, whose three interface hypotheses
are discharged here). -/
theorem apriori {R : H4.Run B.Dh B.gh} (hR : se.IsRun R) {θ : ℝ} (hθ : 0 < θ) :
    se.Apriori R θ := by
  intro xs hxs A0 hA0 k
  have hη : ∀ k l, R.eta B.F k l ≤ ηb k l := fun k l => by
    rw [(se.eta_eq hR k l).1]; exact (se.stop k l).1.1
  have hεb : ∀ k l, R.ε k l ≤ εb k l := fun k l => by
    rw [(se.eta_eq hR k l).2]; exact (se.stop k l).1.2
  have hρ := H4.rhoth_mem (Λ := B.Λ) hθ B.sigma_pos
  have hΛ : 0 ≤ B.Λ := Real.sqrt_nonneg _
  have hL := live_stitch (B := Fin m) B.tau_pos hΛ B.sigma_pos (H4.cth_nonneg hθ B.sigma_pos) hθ
    hρ.1 hρ.2.le (ρ := B.ρθ θ) (a := R.ak B.F xs) (Dk := R.Dk B.τ)
    (unorm := fun k => (se.rep k).unorm) (η := fun k l => R.eta B.F k l) (ε := R.ε)
    (ηb := ηb) (εb := εb) (A0 := A0) (R.ak_nonneg hxs) hA0
    (fun k => R.H4_7_b B.sd hxs hθ k)
    (fun k => by rw [(se.rep_unorm_acc hR k).1]; exact R.H4_4_c B.cross B.L_nonneg B.tau_pos k)
    (fun k => B.Dk_le R k) (fun _ _ => norm_nonneg _) hη (fun k l => (R.report k l).1) hεb k
  refine ⟨R.H4_7_d_declared B.sd hxs hθ (hη k) (hεb k), hL.1, hL.2.1, ?_⟩
  rw [(se.rep_unorm_acc hR k).2]
  exact hL.2.2

/-- (C) at a stitch: the execution is a stitched run of h4-def:report (one exists); for every
stitched run R of it, H4's theorem holds (`H4Clauses`), the residual and accuracy of each block
report are ‖u‖ and ε of the child's final report, the stitch report has ‖u‖ = ‖u_k‖ of
h4-lem:assembly and ε = ε_k, and the a-priori clauses with B̄_k(θ) hold. -/
def Clauses : Prop :=
  (∃ R, se.IsRun R) ∧ ∀ R, se.IsRun R →
    B.H4Clauses R ∧
    (∀ k l, R.eta B.F k l = (se.fin k l).unorm ∧ R.ε k l = (se.fin k l).acc) ∧
    (∀ k, (se.rep k).unorm = ‖R.uk B.F k‖ ∧ (se.rep k).acc = R.epsk k) ∧
    ∀ θ, 0 < θ → se.Apriori R θ

/-- (C) at a stitch holds for every execution whose final child reports are valid. -/
theorem clauses (hv : ∀ k l, (se.fin k l).Valid) : se.Clauses :=
  ⟨⟨_, se.isRun_toRun hv⟩, fun R hR => ⟨B.h4Clauses R, se.eta_eq hR, se.rep_unorm_acc hR,
    fun _ hθ => se.apriori hR hθ⟩⟩

open Classical in
/-- (L) at a stitch (Lemma H5.8(d)): if the stitch is live for (η̄, ε̄), its report at x^{k+1}
meets the target for the least k with Ū_k ≤ η̄ and ε̄_k ≤ ε̄ (Ā₀ := a₀), which exists. -/
theorem live_count (hv : ∀ k l, (se.fin k l).Valid) {θ η ε : ℝ}
    (hL : B.StitchLive θ ηb εb η ε) :
    ∃ k ≤ B.stitchCount θ ηb εb se.a0 η ε, (se.rep k).Meets η ε := by
  obtain ⟨hθ, hη, ⟨xs, hxs⟩, hB, hG, hN, hε⟩ := hL
  have hR := se.isRun_toRun hv
  have ha0 : (se.toRun hv).ak B.F xs 0 ≤ se.a0 := by
    rw [a0, B.Estar_eq hxs]; rfl
  have hA := se.apriori hR hθ xs hxs se.a0 ha0
  have hεb0 : ∀ k l, 0 ≤ εb k l := fun k l => (accR_nonneg (hv k l)).trans (se.stop k l).1.2
  have hρ := H4.rhoth_mem (Λ := B.Λ) hθ B.sigma_pos
  have hAt : Tendsto (B.Aseq θ ηb εb se.a0) atTop (𝓝 0) :=
    H4.accum_tendsto hρ.1 hρ.2 (fun k => (B.Aseq_succ θ ηb εb se.a0 k).le)
      (fun k => ((se.toRun hv).ak_nonneg hxs k).trans (hA k).2.1) (B.Bbar_nonneg hθ hεb0) hB
  have hU0 : Tendsto (fun k => etaN (ηb k) + B.Λ * (√(2 * (B.Aseq θ ηb εb se.a0 k
      + GamF B.τ (ηb k) (εb k))) + √(2 * GamF B.τ (ηb k) (εb k)))) atTop
      (𝓝 (0 + B.Λ * (√(2 * (0 + 0)) + √(2 * 0)))) :=
    hN.add ((((hAt.add hG).const_mul 2).sqrt.add (hG.const_mul 2).sqrt).const_mul B.Λ)
  rw [show (0 : ℝ) + B.Λ * (√(2 * (0 + 0)) + √(2 * 0)) = 0 by simp] at hU0
  have hU : Tendsto (B.Ubar θ ηb εb se.a0) atTop (𝓝 0) := hU0
  have hex : ∃ k, B.Ubar θ ηb εb se.a0 k ≤ η ∧ ∑ l, εb k l ≤ ε :=
    ((hU.eventually (ge_mem_nhds hη)).and hε).exists
  refine ⟨Nat.find hex, by unfold BlockTgt.stitchCount; rw [dif_pos hex], ?_⟩
  obtain ⟨h1, h2⟩ := Nat.find_spec hex
  have := hA (Nat.find hex)
  exact ⟨this.2.2.1.trans h1, this.2.2.2.trans h2⟩

end StitchEx


namespace Node

variable (σ : Sem A I C)

/-- **Definition H5.7** (well typed on t): the row's typing for a leaf; for a stitch, the
block target B with t = B.tgt and the node's declared part (unique: t fixes F) has every block pipeline well typed on its slice at every
x ∈ dom g (UNI; BT is the data of `BlockTgt`). -/
def Typed : Node A I C → Tgt → Prop
  | fb a, t => σ.fb.typed a t
  | inx a, t => σ.inx.typed a t
  | cons a, t => σ.cons.typed a t
  | stitch m d _ _ _ ch, t =>
      ∀ B : BlockTgt m, t = B.tgt → B.decl = d → ∀ x ∈ B.dom, ∀ l, Typed (ch l) (B.sliceT x l)

/-- The run clauses (C) of the row; for a stitch, `StitchEx.Clauses` (H4's theorem for the
stitched run, with the children's report norms and accuracies, and the a-priori clauses). -/
def Clauses : (P : Node A I C) → (t : Tgt) → Exec σ P t → Prop
  | fb a, t, e => σ.fb.clauses a t e.down
  | inx a, t, e => σ.inx.clauses a t e.down
  | cons a, t, e => σ.cons.clauses a t e.down
  | stitch _ _ _ _ _ _, _, e => e.2.2.Clauses

/-- The live condition (LIVE) for (η̄, ε̄); for a stitch, every child live on every slice for
its declared targets, and the condition of Lemma H5.8(d). -/
def Live : Node A I C → Tgt → ℝ → ℝ → Prop
  | fb a, t, η, ε => σ.fb.live a t η ε
  | inx a, t, η, ε => σ.inx.live a t η ε
  | cons a, t, η, ε => σ.cons.live a t η ε
  | stitch m d θ ηb εb ch, t, η, ε => ∀ B : BlockTgt m, t = B.tgt → B.decl = d →
      (∀ x ∈ B.dom, ∀ (l : Fin m) k, Live (ch l) (B.sliceT x l) (ηb k l) (εb k l)) ∧
        B.StitchLive θ ηb εb η ε

/-- The count of the row (Lemma H5.8), a function of the execution; for a stitch, the least
k with Ū_k ≤ η̄ and ε̄_k ≤ ε̄, with Ā₀ := a₀ = E(x⁰) − E* of the execution. -/
noncomputable def Count : (P : Node A I C) → (t : Tgt) → Exec σ P t → ℝ → ℝ → ℕ
  | fb a, t, e, η, ε => σ.fb.count a t e.down η ε
  | inx a, t, e, η, ε => σ.inx.count a t e.down η ε
  | cons a, t, e, η, ε => σ.cons.count a t e.down η ε
  | stitch _ _ θ ηb εb _, _, e, η, ε => e.1.stitchCount θ ηb εb e.2.2.a0 η ε

/-- The height h(𝔓): 0 for leaves, 1 + the largest child height for a stitch. -/
def height : Node A I C → ℕ
  | fb _ => 0
  | inx _ => 0
  | cons _ => 0
  | stitch _ _ _ _ _ ch => 1 + Finset.univ.sup fun l => height (ch l)

/-- The conclusion of Theorem H5.9 at a node 𝔓 with target t: for every execution, (R) every
output carries a composite report of t, (A) Lemma H5.2's distance and value bracket hold there,
(C) the row's clauses hold; and (L) if 𝔓 is live for (η̄, ε̄), in every execution some output
within the count of that execution meets it. -/
def Sound (P : Node A I C) (t : Tgt) : Prop :=
  (∀ e : Exec σ P t, (∀ k, (out σ e k).Valid ∧ (out σ e k).Cert) ∧ Clauses σ P t e) ∧
  ∀ η ε, Live σ P t η ε → ∀ e : Exec σ P t, ∃ k ≤ Count σ P t e η ε, (out σ e k).Meets η ε

lemma sound_leaf {A' : Type} (L : LeafSem A') {a : A'} {t : Tgt} (hT : L.typed a t) :
    (∀ e : L.Ex a t, (∀ k, (L.out e k).Valid ∧ (L.out e k).Cert) ∧ L.clauses a t e) ∧
    ∀ η ε, L.live a t η ε → ∀ e : L.Ex a t, ∃ k ≤ L.count a t e η ε, (L.out e k).Meets η ε :=
  ⟨fun e => ⟨fun k => ⟨L.report a t e hT k, Rep.cert_of_valid (L.report a t e hT k)⟩,
    L.sound a t e hT⟩, fun η ε hl e => L.livecount a t η ε e hT hl⟩

/-- Inside a stitch: if the children are sound on their slices, every sweep point x^{k,i}
lies in dom g and every final child report is valid (induction over the position (k, l)). -/
lemma stitch_valid {m : ℕ} {d : BlockDecl m} {θ : ℝ} {ηb εb : ℕ → Fin m → ℝ} {ch : Fin m → Node A I C} {t : Tgt}
    (hS : ∀ l t', Typed σ (ch l) t' → Sound σ (ch l) t') (hT : Typed σ (stitch m d θ ηb εb ch) t)
    (B : BlockTgt m) (h : t = B.tgt) (hd : B.decl = d)
    (se : StitchEx B ηb εb (fun l t' => Exec σ (ch l) t') (fun _ _ e => out σ e)) :
    (∀ k i, i ≤ m → se.x k i ∈ B.dom) ∧ ∀ k l, (se.fin k l).Valid := by
  have hv : ∀ k (l : Fin m), se.x k l.val ∈ B.dom → (se.fin k l).Valid := fun k l hx =>
    (((hS l _ (hT B h hd _ hx l)).1 (se.call k l)).1 (se.n k l)).1
  have hm := se.mem_of_valid hv
  exact ⟨hm, fun k l => hv k l (hm k l.val l.isLt.le)⟩

/-- **Theorem H5.9 (soundness for pipelines), non-pick nodes.** For every well-typed node 𝔓
and every target t on which it is typed: (R), (A), (C) at every execution and (L). By
structural induction on 𝔓 (= induction on the height); at a stitch, by induction over the
position (k, l) in the run (`stitch_valid`), every call is made at a point of dom g, so it is an
execution of a well-typed child on its slice, and its final report is valid; the stitched run
is then a run of h4-def:report and H4's theorems give (C) and (L). -/
theorem soundness : ∀ (P : Node A I C) (t : Tgt), Typed σ P t → Sound σ P t
  | fb a, t, hT =>
    ⟨fun e => (sound_leaf σ.fb hT).1 e.down, fun η ε hl e => (sound_leaf σ.fb hT).2 η ε hl e.down⟩
  | inx a, t, hT =>
    ⟨fun e => (sound_leaf σ.inx hT).1 e.down, fun η ε hl e => (sound_leaf σ.inx hT).2 η ε hl e.down⟩
  | cons a, t, hT =>
    ⟨fun e => (sound_leaf σ.cons hT).1 e.down, fun η ε hl e => (sound_leaf σ.cons hT).2 η ε hl e.down⟩
  | stitch m d θ ηb εb ch, t, hT => by
    have hS : ∀ l t', Typed σ (ch l) t' → Sound σ (ch l) t' :=
      fun l t' hT' => soundness (ch l) t' hT'
    refine ⟨fun e => ?_, fun η ε hL e => ?_⟩
    · obtain ⟨B, ⟨h, hd⟩, se⟩ := e
      have hv := (stitch_valid σ hS hT B h hd se).2
      subst h
      refine ⟨fun k => ?_, se.clauses hv⟩
      have hval := (se.rep_valid (se.isRun_toRun hv) hv k).1
      exact ⟨hval, Rep.cert_of_valid hval⟩
    · obtain ⟨B, ⟨h, hd⟩, se⟩ := e
      have hv := (stitch_valid σ hS hT B h hd se).2
      have hLs := (hL B h hd).2
      subst h
      exact se.live_count hv hLs

/-- **Theorem H5.9 (L) for the calls of a stitch: every call stops within its count.** If a
stitch is well typed and live, then in every execution the call of block l in sweep k stops
(at its first output meeting (η̄_{k,l}, ε̄_{k,l})) within the child's count for that call. -/
theorem calls_stop {m : ℕ} {d : BlockDecl m} {θ : ℝ} {ηb εb : ℕ → Fin m → ℝ} {ch : Fin m → Node A I C} {t : Tgt}
    {η ε : ℝ} (hT : Typed σ (stitch m d θ ηb εb ch) t) (hL : Live σ (stitch m d θ ηb εb ch) t η ε)
    (e : Exec σ (stitch m d θ ηb εb ch) t) (k : ℕ) (l : Fin m) :
    e.2.2.n k l ≤ Count σ (ch l) _ (e.2.2.call k l) (ηb k l) (εb k l) := by
  obtain ⟨B, ⟨h, hd⟩, se⟩ := e
  show se.n k l ≤ Count σ (ch l) _ (se.call k l) (ηb k l) (εb k l)
  have hm := (stitch_valid σ (fun l t' hT' => soundness σ (ch l) t' hT') hT B h hd se).1
  have hx := hm k l.val l.isLt.le
  obtain ⟨j, hj, hmj⟩ := (soundness σ (ch l) _ (hT B h hd _ hx l)).2 _ _ ((hL B h hd).1 _ hx l k)
    (se.call k l)
  refine le_trans ?_ hj
  by_contra hlt
  exact (se.stop k l).2 j (by omega) hmj

end Node

/-- A stopping rule of a pick child: after K outputs (final output index K), or a target. -/
inductive StopRule
  | after : ℕ → StopRule
  | target : ℝ → ℝ → StopRule

/-- n is the final output index of rs under the stopping rule. -/
def Stops {t : Tgt} (rs : ℕ → Rep t) : StopRule → ℕ → Prop
  | .after K, n => n = K
  | .target η ε, n => FirstMeet rs η ε n

/-- **Theorem H5.9 for a pick (rule pick, Definitions H5.5–H5.7).** A pick over a finite
nonempty set 𝒵 of well-typed nodes `ch z` with targets `ts z` and stopping rules `ς z`
(STOP: every target rule is live). Then (L) every child execution stops; and at the final
reports R_z of any execution, (R) each is a composite report of its target, and (A)/(C):
if μ_E > 0 and s > 0 for every z and x*_z are the minimisers, thm:h1-pick (b), (c), (d) hold
with the brackets L_z = ℓ_{R_z}, U_z = E_z(x̂_z), ρ_z = τ_{R_z} of Lemma H5.4(b). -/
theorem soundness_pick (σ : Sem A I C) {Z : Type} [Fintype Z] [DecidableEq Z] [Nonempty Z]
    (ch : Z → Node A I C) (ts : Z → Tgt) (ς : Z → StopRule)
    (hT : ∀ z, Node.Typed σ (ch z) (ts z))
    (hL : ∀ z η ε, ς z = .target η ε → Node.Live σ (ch z) (ts z) η ε) :
    (∀ z (e : Exec σ (ch z) (ts z)), ∃ n, Stops (out σ e) (ς z) n) ∧
    ∀ (cr : ∀ z, Exec σ (ch z) (ts z)) (n : Z → ℕ),
      (∀ z, Stops (out σ (cr z)) (ς z) (n z)) →
      (∀ z, (out σ (cr z) (n z)).Valid) ∧
      ((∀ z, 0 < muHat (ts z).σF (ts z).σ ∧ 0 < sR (ts z).σF (ts z).σ (out σ (cr z) (n z)).ε) →
        ∀ xs : ∀ z, (ts z).X, (∀ z, IsMinD (domE (ts z).D) (Eval (ts z).F (ts z).g) (xs z)) →
        ∀ zh : Z,
          let D := fun z => domE (ts z).D
          let E := fun z => Eval (ts z).F (ts z).g
          let xh := fun z => (out σ (cr z) (n z)).xh
          let L := fun z => ellRep (ts z).F (ts z).σF (ts z).g (ts z).σ (out σ (cr z) (n z)).xh
            (out σ (cr z) (n z)).v (out σ (cr z) (n z)).ε
          let ρ := fun z => tauRep (ts z).F (ts z).σF (ts z).σ (out σ (cr z) (n z)).xh (out σ (cr z) (n z)).v
            (out σ (cr z) (n z)).ε
          ((∀ q : Σ z, (ts z).X, q.2 ∈ D q.1 → minOver (fun z => E z (xs z)) ≤ E q.1 q.2) ∧
            (∃ z, HybMin D E ⟨z, xs z⟩ ∧ E z (xs z) = minOver (fun z => E z (xs z))) ∧
            E zh (xh zh) - minOver (fun z => E z (xs z)) ≤ E zh (xh zh) - minOver L ∧
            ‖xh zh - xs zh‖ ≤ ρ zh) ∧
          (MarginNonneg L (fun z => E z (xh z)) zh →
            E zh (xs zh) = minOver (fun z => E z (xs z)) ∧ HybMin D E ⟨zh, xs zh⟩ ∧
            E zh (xh zh) - minOver (fun z => E z (xs z)) ≤ E zh (xh zh) - L zh) ∧
          (MarginPos L (fun z => E z (xh z)) zh →
            E zh (xs zh) = minOver (fun z => E z (xs z)) ∧
            (∀ z, z ≠ zh → minOver (fun z => E z (xs z)) < E z (xs z)) ∧
            (∀ p : Σ z, (ts z).X, HybMin D E p ↔ p = ⟨zh, xs zh⟩) ∧
            ‖xh zh - xs zh‖ ≤ ρ zh)) := by
  refine ⟨fun z e => ?_, fun cr n hE => ?_⟩
  · cases hς : ς z with
    | after K => exact ⟨K, rfl⟩
    | target η ε =>
      obtain ⟨j, -, hm⟩ := (Node.soundness σ (ch z) (ts z) (hT z)).2 η ε (hL z η ε hς) e
      obtain ⟨n, -, hF⟩ := exists_firstMeet hm
      exact ⟨n, hF⟩
  have hV : ∀ z, (out σ (cr z) (n z)).Valid := fun z =>
    (((Node.soundness σ (ch z) (ts z) (hT z)).1 (cr z)).1 (n z)).1
  refine ⟨hV, fun hpos xs hxs zh => ?_⟩
  have hB : ∀ z, ExtBracket (domE (ts z).D) (Eval (ts z).F (ts z).g) (out σ (cr z) (n z)).xh
      (ellRep (ts z).F (ts z).σF (ts z).g (ts z).σ (out σ (cr z) (n z)).xh (out σ (cr z) (n z)).v (out σ (cr z) (n z)).ε)
      (tauRep (ts z).F (ts z).σF (ts z).σ (out σ (cr z) (n z)).xh (out σ (cr z) (n z)).v (out σ (cr z) (n z)).ε) :=
    fun z => report_bracket (ts z).split (hV z) (hpos z).1 (hpos z).2 (hxs z)
  exact ⟨pick_b _ _ _ _ _ xs hB hxs zh, fun hm => pick_c _ _ _ _ _ xs hB hxs zh hm,
    fun hm => pick_d _ _ _ _ _ xs hB hxs zh hm⟩

end Pipelines

/-! ## §10 Where the chain breaks (Proposition H5.12(a)–(c)) -/

section Breaks

/-- The two choices of Proposition H5.12(a). -/
inductive AB
  | A
  | B
  deriving DecidableEq

/-- E_A(x) = (x − 2)², E_B(x) = (x + 2)² + 1; E_hyb(z, x) = E_z(x) on {A, B} × ℝ. -/
def Eab : AB → ℝ → ℝ
  | .A, x => (x - 2) ^ 2
  | .B, x => (x + 2) ^ 2 + 1

/-- The exact x-block step: the minimiser of E_z. -/
def xstepAB : AB → ℝ
  | .A => 2
  | .B => -2

open Classical in
/-- The exact z-block step: a minimiser of z ↦ E_z(x) (A on ties). -/
noncomputable def zstepAB (x : ℝ) : AB := if Eab .A x ≤ Eab .B x then .A else .B

/-- One sweep of alternating exact minimisation, x first: (z, x) ↦ (zstep(xstep z), xstep z). -/
noncomputable def sweepAB (p : AB × ℝ) : AB × ℝ := (zstepAB (xstepAB p.1), xstepAB p.1)

lemma zstepAB_neg2 : zstepAB (-2) = .B := by
  unfold zstepAB; rw [if_neg]; simp only [Eab]; norm_num

lemma zstepAB_2 : zstepAB 2 = .A := by
  unfold zstepAB; rw [if_pos]; simp only [Eab]; norm_num

/-- **Proposition H5.12(a) (a pick is not a block).** (i) Both block steps are exact: the
x-step returns the minimiser of E_z, where the x-block report is exact and zero (E_z' = 0,
ε = 0), and the z-step returns a minimiser over z. (ii) From (B, x₀), for every x₀, every
sweep k ≥ 1 is at (B, −2); (A, 2) is fixed as well. (iii) At both (B, −2) and (A, 2) the
block reports are the same (x-block derivative 0, ε = 0; the z-step returns the current z).
(iv) min E_hyb = 0, attained at (A, 2), and E_hyb(B, −2) − min E_hyb = 1. -/
theorem breaks_a :
    (∀ z x, Eab z (xstepAB z) ≤ Eab z x) ∧ (∀ z, HasDerivAt (Eab z) 0 (xstepAB z)) ∧
    (∀ x z, Eab (zstepAB x) x ≤ Eab z x) ∧
    (∀ x0 : ℝ, ∀ k : ℕ, sweepAB^[k + 1] (.B, x0) = (.B, -2)) ∧ sweepAB (.A, 2) = (.A, 2) ∧
    (HasDerivAt (Eab .B) 0 (-2) ∧ zstepAB (-2) = .B) ∧
    (HasDerivAt (Eab .A) 0 2 ∧ zstepAB 2 = .A) ∧
    (∀ z x, Eab .A 2 ≤ Eab z x) ∧ Eab .A 2 = 0 ∧ Eab .B (-2) - Eab .A 2 = 1 := by
  have hx : ∀ z x, Eab z (xstepAB z) ≤ Eab z x := by
    intro z x; cases z <;> simp only [Eab, xstepAB] <;> nlinarith [sq_nonneg (x - 2), sq_nonneg (x + 2)]
  have hd : ∀ z, HasDerivAt (Eab z) 0 (xstepAB z) := by
    intro z
    cases z
    · show HasDerivAt (Eab .A) 0 2
      have e : Eab .A = (fun x => id x - 2) ^ 2 := by funext x; simp [Eab]
      rw [e]
      exact (((hasDerivAt_id (2 : ℝ)).sub_const 2).pow 2).congr_deriv (by norm_num)
    · show HasDerivAt (Eab .B) 0 (-2)
      have e : Eab .B = fun x => ((fun x => id x + 2) ^ 2) x + 1 := by funext x; simp [Eab]
      rw [e]
      exact ((((hasDerivAt_id (-2 : ℝ)).add_const 2).pow 2).add_const 1).congr_deriv (by norm_num)
  have hz : ∀ x z, Eab (zstepAB x) x ≤ Eab z x := by
    intro x z
    unfold zstepAB
    split_ifs with h <;> cases z <;> simp_all <;> linarith
  have hfix : sweepAB (.B, -2) = (.B, -2) := by simp [sweepAB, xstepAB, zstepAB_neg2]
  have hsweep : ∀ x0 : ℝ, ∀ k : ℕ, sweepAB^[k + 1] (.B, x0) = (.B, -2) := by
    intro x0 k
    induction k with
    | zero => simp [sweepAB, xstepAB, zstepAB_neg2]
    | succ k ih => rw [Function.iterate_succ_apply', ih, hfix]
  refine ⟨hx, hd, hz, hsweep, by simp [sweepAB, xstepAB, zstepAB_2], ⟨hd .B, zstepAB_neg2⟩,
    ⟨hd .A, zstepAB_2⟩, fun z x => ?_, by simp [Eab], by norm_num [Eab]⟩
  cases z <;> simp only [Eab] <;> norm_num <;> positivity

/-- The smooth part q_y(w) = ‖w − y‖²/(2α) of Φ_y at α = 1, y = 2 on ℝ. -/
noncomputable def q2 : ℝ → ℝ := fun w => sqf (X := ℝ) 1⁻¹ (w - 2)

/-- f(x) = ½(x − 2)² on ℝ. -/
noncomputable def f2 : ℝ → ℝ := fun w => sqf (X := ℝ) 1 (w - 2)

/-- **Proposition H5.12(b) (a pipeline is not an inexact oracle).** f = ½(· − 2)² declared
(1, 1, void) (C(f, 1) and ∇f 1-Lipschitz), g = |·|, α = 1. (i) For every x₀, y₀ = x₀ − f'(x₀)
= 2, and x* = 1 minimises f + |·|. (ii) For t > 0, (1 + t, t, (1, 0)) is a composite report
of Φ₂ = |·| + ½(· − 2)². (iii) 1 + t is not an answer of accuracy 0 at y₀ (so the
inclusion of h2-def:oracle-accuracy fails), and the (I5) returned-point bound with reported
accuracy 0 reads (q_A‖r₀‖ + √(β̂·0))/μ̂ = 0 (q_A = 1 − 1/1 = 0, μ̂ = 1) while
|x₁ − x*| = t > 0. (iv) The accuracy the parent computes (h2-lem:check(a)) is t(1 + t) for
t ≤ 2: 1 + t is an answer of accuracy t(1 + t), and of no smaller accuracy. (v) The
gradient-error reading: |x₁ − x*| = α|u| = t. -/
theorem breaks_b :
    (ModC f2 1 ∧ LipGrad f2 1) ∧
    (∀ x0 : ℝ, step f2 1 x0 = 2) ∧ (∀ x : ℝ, f2 1 + |1| ≤ f2 x + |x|) ∧
    ∀ t : ℝ, 0 < t →
      (IsReport (fun _ : Unit => (univ : Set ℝ)) (fun _ => fun w : ℝ => |w|) (1 + t)
          (fun _ => 1) (fun _ => 0) ∧ uR q2 (fun _ : Unit => (1 : ℝ)) (1 + t) = t) ∧
      (¬ ProxEps (univ : Set ℝ) (fun w => |w|) 1 0 2 (1 + t) ∧
        ((1 - 1 / 1) * |2 - (1 + t)| + √(1 * 0)) / 1 = 0 ∧ |(1 + t) - 1| = t ∧
        ¬ |(1 + t) - 1| ≤ ((1 - 1 / 1) * |2 - (1 + t)| + √(1 * 0)) / 1) ∧
      (t ≤ 2 → ProxEps (univ : Set ℝ) (fun w => |w|) 1 (t * (1 + t)) 2 (1 + t) ∧
        ∀ ε, ProxEps (univ : Set ℝ) (fun w => |w|) 1 ε 2 (1 + t) → t * (1 + t) ≤ ε) ∧
      |(1 + t) - 1| = 1 * |t| := by
  have hg : ∀ w : ℝ, gradient f2 w = w - 2 := fun w => by
    have := (hasGradientAt_sqf_sub (X := ℝ) 1 2 w).gradient
    simp only [one_smul] at this; exact this
  have hmodC : ModC f2 1 := by
    unfold ModC f2 sqf
    have : (fun x : ℝ => 1 / 2 * ‖x - 2‖ ^ 2 - 1 / 2 * ‖x‖ ^ 2) = fun x => -2 * x + 2 := by
      funext x; simp only [Real.norm_eq_abs, sq_abs]; ring
    rw [this]
    exact (convexOn_const (2 : ℝ) convex_univ).add
      ((LinearMap.lsmul ℝ ℝ (-2 : ℝ)).convexOn convex_univ) |>.congr fun x _ => by simp; ring
  have hlip : LipGrad f2 1 := fun u v => by rw [hg, hg]; simp [Real.norm_eq_abs]
  refine ⟨⟨hmodC, hlip⟩, fun x0 => by simp [step, hg], fun x => ?_, fun t ht => ?_⟩
  · simp only [f2, sqf, Real.norm_eq_abs, sq_abs]
    rcases le_total 0 x with h | h
    · rw [abs_of_nonneg h]; norm_num; nlinarith [sq_nonneg (x - 1)]
    · rw [abs_of_nonpos h]; norm_num; nlinarith [sq_nonneg (x - 2)]
  have h1t : |1 + t| = 1 + t := abs_of_pos (by linarith)
  refine ⟨⟨fun _ => ⟨le_rfl, mem_univ _, fun w _ => ?_⟩, ?_⟩, ⟨?_, by simp, ?_, ?_⟩, fun ht2 => ⟨?_, ?_⟩,
    by rw [one_mul, add_sub_cancel_left]⟩
  · simp only [Real.inner_apply, h1t]
    have := le_abs_self w; linarith
  · rw [uR_unit]
    have := (hasGradientAt_sqf_sub (X := ℝ) 1⁻¹ 2 (1 + t)).gradient
    unfold q2; rw [this]; simp; ring
  · intro hp
    have := hp.2 0 (mem_univ _)
    simp only [Real.inner_apply, h1t, abs_zero, inv_one, one_smul] at this
    nlinarith
  · rw [add_sub_cancel_left, abs_of_pos ht]
  · rw [add_sub_cancel_left, abs_of_pos ht]; simp; linarith
  · refine ⟨mem_univ _, fun w _ => ?_⟩
    simp only [Real.inner_apply, h1t, inv_one, one_smul]
    have hw : (2 - (1 + t)) * w ≤ |w| := by
      have : |2 - (1 + t)| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      calc (2 - (1 + t)) * w ≤ |(2 - (1 + t)) * w| := le_abs_self _
        _ = |2 - (1 + t)| * |w| := abs_mul _ _
        _ ≤ 1 * |w| := mul_le_mul_of_nonneg_right this (abs_nonneg w)
        _ = |w| := one_mul _
    nlinarith
  · intro ε hp
    have := hp.2 0 (mem_univ _)
    simp only [Real.inner_apply, h1t, abs_zero, inv_one, one_smul] at this
    nlinarith

/-- **Proposition H5.12(c) (exact children do not stop).** φ = (τ/2)y² on ℝ declared (L, τ)
(C(φ, τ) and ∇φ L-Lipschitz), 0 < τ < L, g = 0, step α = 1/L, y₀ ≠ 0. The constructed
iteration is y_k = (1 − τ/L)^k y₀, and the report of every output y_{k+1} (Lemma H5.3(i),
N = ∅: u_k = ∇φ(y_{k+1})) has u_k = τ(1 − τ/L)^{k+1} y₀ ≠ 0; so the target η̄ = 0 is never
met. -/
theorem breaks_c {τ L y0 : ℝ} (hτ : 0 < τ) (hτL : τ < L) (hy0 : y0 ≠ 0) :
    (ModC (sqf (X := ℝ) τ) τ ∧ LipGrad (sqf (X := ℝ) τ) L) ∧
    (∀ k : ℕ, (step (sqf (X := ℝ) τ) (1 / L))^[k] y0 = (1 - τ / L) ^ k * y0) ∧
    ∀ k : ℕ, gradient (sqf (X := ℝ) τ) ((step (sqf (X := ℝ) τ) (1 / L))^[k + 1] y0)
        = τ * ((1 - τ / L) ^ (k + 1) * y0) ∧
      gradient (sqf (X := ℝ) τ) ((step (sqf (X := ℝ) τ) (1 / L))^[k + 1] y0) ≠ 0 ∧
      ¬ ‖gradient (sqf (X := ℝ) τ) ((step (sqf (X := ℝ) τ) (1 / L))^[k + 1] y0)‖ ≤ 0 := by
  have hL : 0 < L := hτ.trans hτL
  have hg : ∀ y : ℝ, gradient (sqf (X := ℝ) τ) y = τ * y := fun y => by
    rw [gradient_sqf]; rfl
  have hstep : ∀ y : ℝ, step (sqf (X := ℝ) τ) (1 / L) y = (1 - τ / L) * y := fun y => by
    simp only [step, hg, smul_eq_mul]; field_simp
  have hit : ∀ k : ℕ, (step (sqf (X := ℝ) τ) (1 / L))^[k] y0 = (1 - τ / L) ^ k * y0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, hstep, pow_succ]; ring
  have hq : 1 - τ / L ≠ 0 := by
    have : τ / L < 1 := (div_lt_one hL).2 hτL
    linarith
  have hlip : LipGrad (sqf (X := ℝ) τ) L := fun u v => by
    have := lipGrad_sqf (X := ℝ) hτ.le u v
    exact this.trans (mul_le_mul_of_nonneg_right hτL.le (norm_nonneg _))
  refine ⟨⟨modC_sqf τ, hlip⟩, hit, fun k => ?_⟩
  have hu : gradient (sqf (X := ℝ) τ) ((step (sqf (X := ℝ) τ) (1 / L))^[k + 1] y0)
      = τ * ((1 - τ / L) ^ (k + 1) * y0) := by rw [hit, hg]
  have hne : τ * ((1 - τ / L) ^ (k + 1) * y0) ≠ 0 :=
    mul_ne_zero hτ.ne' (mul_ne_zero (pow_ne_zero _ hq) hy0)
  refine ⟨hu, hu ▸ hne, fun h => ?_⟩
  rw [hu] at h
  exact hne (norm_le_zero_iff.1 h)

end Breaks

end OCF.H5

#print axioms OCF.H5.cert_a
#print axioms OCF.H5.cert_b
#print axioms OCF.H5.extModC_Eval
#print axioms OCF.H5.lemma_H5_2
#print axioms OCF.H5.cert_e1
#print axioms OCF.H5.cert_e2
#print axioms OCF.H5.cert_e3
#print axioms OCF.H5.closure_fb
#print axioms OCF.H5.closure_fb_empty
#print axioms OCF.H5.closure_fb_run
#print axioms OCF.H5.closure_inx
#print axioms OCF.H5.closure_cons
#print axioms OCF.H5.closure_cons_iter
#print axioms OCF.H5.closure_stitch
#print axioms OCF.H5.slice_report_block
#print axioms OCF.H5.slice_moduli_pos
#print axioms OCF.H5.prox_report_iff
#print axioms OCF.H5.prox_report_not_answer
#print axioms OCF.H5.report_bracket
#print axioms OCF.H5.pick_a
#print axioms OCF.H5.pick_b
#print axioms OCF.H5.pick_c
#print axioms OCF.H5.pick_d
#print axioms OCF.H5.pick_d_bound
#print axioms OCF.H5.pick_e
#print axioms OCF.H5.minOver_sigma
#print axioms OCF.H5.aposteriori
#print axioms OCF.H5.aposteriori_a
#print axioms OCF.H5.aposteriori_b
#print axioms OCF.H5.aposteriori_c
#print axioms OCF.H5.live_fb
#print axioms OCF.H5.live_inx
#print axioms OCF.H5.ellRep_lower
#print axioms OCF.H5.live_cons
#print axioms OCF.H5.cons_count
#print axioms OCF.H5.cons_ebar_min
#print axioms OCF.H5.live_stitch
#print axioms OCF.H5.accum_le
#print axioms OCF.H5.BF_mono
#print axioms OCF.H5.cor_a
#print axioms OCF.H5.cor_b
#print axioms OCF.H5.cor_c_uniform
#print axioms OCF.H5.cor_c_total
#print axioms OCF.H5.cor_c_sweeps
#print axioms OCF.H5.cor_d
#print axioms OCF.H5.Rep.cert_of_valid
#print axioms OCF.H5.exists_firstMeet
#print axioms OCF.H5.BlockTgt.h4Clauses
#print axioms OCF.H5.BlockTgt.Dk_le
#print axioms OCF.H5.StitchEx.mem_of_valid
#print axioms OCF.H5.StitchEx.eta_eq
#print axioms OCF.H5.StitchEx.rep_valid
#print axioms OCF.H5.StitchEx.rep_unorm_acc
#print axioms OCF.H5.StitchEx.apriori
#print axioms OCF.H5.StitchEx.clauses
#print axioms OCF.H5.StitchEx.live_count
#print axioms OCF.H5.Node.stitch_valid
#print axioms OCF.H5.Node.soundness
#print axioms OCF.H5.Node.calls_stop
#print axioms OCF.H5.soundness_pick
#print axioms OCF.H5.breaks_a
#print axioms OCF.H5.breaks_b
#print axioms OCF.H5.breaks_c

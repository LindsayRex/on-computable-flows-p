/-
B72-SND, Proposition 2: the certificate of the two-sided margin rule (partial enclosure oracles, reject keeps the
state), from named oracle hypotheses. No floating-point model and no analysis: the points are an abstract type with an
energy `E : α → ℝ`.

Source of truth: project_plan/doing/proof_audits/B72_SND_margin_rule/01_derivation.md, section 7 (Proposition 2, with the
limits that follow it); adjudicated stage 3, 2026-11-02 (rulings and the Lean-ready specification in 03_adjudication.md,
section 4). Dossier sha16 (first 16 hex of sha256sum of 01_derivation.md) at formalisation time: 9b9b1e836a5331b7.
Classification in the dossier: ELEMENTARY logic (the incumbent-and-prune logic of interval branch and bound; no novelty
is claimed for the logic, so no citation is made).

DEFINITIONAL MAP (dossier symbol — Lean name):
* point set 𝒫, energy E : 𝒫 → ℝ — `α`, `E : α → ℝ` (a variable of the file);
* state (z_k, A_k, B_k) — `State α` with fields `z A B`;
* partial enclosure oracle (`none` = "undecided", else an interval (a, b)) — `Oracle α := α → Option (ℝ × ℝ)`;
* `cheap` (Proposition 1(c) when its checks pass, else `none`) — `cheap : Oracle α`;
* `fb(B, z)` (exact rational evaluation, interval arithmetic or a finer format; may depend on the carried bound B and be
  a chain of tiers) — `fb : ℝ → Oracle α`, applied as `fb s.B p`;
* H-orc (inclusion property: whenever an oracle answers (a, b), a ≤ E(z) ≤ b) — `Sound E o`;
* H-init, and the invariant (i) `A_k ≤ E(z_k) ≤ B_k` — `Inv E s`;
* one step of R1–R3 for state s, proposal z⁺, verdict, next state — `Step cheap fb s p v s'` with the verdicts of
  `Verdict`: `accept`, `rejectCert` (certified reject, R2 or the second clause of R3), `rejectOther` (undecided reject,
  including a stop at z⁺ = z_k); R1 = `Step.r1`, R2 = `Step.r2`, R3 = `Step.r3acc` / `Step.r3rej` / `Step.r3und`;
  "reject means the state is unchanged" is built into `r2`, `r3rej`, `r3und`;
* a run (every k reached from s_0 by finitely many steps, proposals arbitrary) — `Reach cheap fb s0`.

NAMED HYPOTHESES (none is proved here, none is a global axiom):
* `hc : Sound E cheap` and `hf : ∀ B, Sound E (fb B)` — H-orc for the two oracles, about the points the rule actually
  asks about (so non-vacuous where Proposition 1 is partial: an oracle that cannot certify returns `none`);
* `hs : Inv E s` / `h0 : Inv E s0` — H-init.

COVERAGE (dossier item — Lean name), no sorry:
* (i) `A_k ≤ E(z_k) ≤ B_k` on every reached step — `inv_step` (one step), `reach_inv` (every run);
* (ii) `B_{k+1} < B_k` at an accept — `accept_lt`; reject keeps the state — `reject_keeps`; `(B_k)` nonincreasing along every
  run — `reach_B_le`; the bounds installed at accepts are strictly decreasing — `accept_lt` (an accepted step may repeat a
  point: nothing in the statement forbids it);
* (iii) a certified reject has `E(z⁺) > B_k ≥ E(z_k)` — `rejectCert_gt` (one step), `reach_rejectCert_gt` (on a reached state);
* (iv) at an accept `E(z_{k+1}) < B_k` and `E(z_{k+1}) − E(z_k) < B_k − A_k` — `accept_bounds`, `reach_accept_bounds`;
* (v) the two clauses of R1/R2 and the two of R3 are mutually exclusive — `excl` (for any sound oracle); and the rule is
  a function: verdict and next state are determined by (state, proposal) — `step_det` (so the relation `Step` is exactly
  the rule, not a weaker over-approximation of it);
* non-vacuity: `Sound` holds for the exact oracle; an accept, a certified reject and an undecided reject (a stop at
  z⁺ = z_k) are each realised at R1, R2, R3 — `idOracle_sound`, `ex_accept`, `ex_rejectCert`, `ex_rejectOther`,
  `ex_r3acc`, `ex_r3rej`.

WHAT THE STATEMENT DOES NOT SAY (dossier limits 1 and 3, kept out on purpose): there is NO theorem `E(z_{k+1}) < E(z_k)`;
the certificate is `E(z_{k+1}) < B_k` and `B_{k+1} < B_k` only (`accept_bounds` gives the rise bound `< B_k − A_k`,
nothing sharper). Limit 1 is witnessed in the dossier by E(z_k)=1, [A,B]=[0.5,3], E(z⁺)=2, [a,b]=[1.5,2.5]; the file
proves the bound on the rise, which that example meets (rise 1 < 2.5).

NOT COVERED (remain PROSE-ONLY): Proposition 1 (the floating-point enclosure of the direct evaluation, with H-chk, H-bd, H-d,
H-NU, H-NO); Lemma A (rounding monotonicity step); Lemma F (weights, cited from Higham–Mary Lemma 2.2); the remark of
section 8 (three conditions under which a one-sided rule fails); the cost remark (section 6); the classifier-mode carry of
the companion experiment (re-install a fresh enclosure of the rejected proposal and move to it) — NOT formalised under this
name, it is a measurement protocol and not the rule (dossier limit 2: it keeps (i), (iii) and the accept-step inequality
but breaks the rest of (ii); a second relation would have `inv_step`, `rejectCert_gt`, `accept_lt` and no `reach_B_le`);
the variant that accepts only if `b < A_k` (a remark in the dossier, not a theorem); the identification of the oracles with
Proposition 1(c), exact rational evaluation or a particular interval library (these are the oracle hypotheses `Sound`).

Status tier: FORMALISED for Proposition 2 (i)–(v) as the dossier states them over abstract oracles (proved in the file from
the named oracle hypotheses, no sorry); the oracle soundness hypotheses are not discharged here (they are Proposition 1,
PROSE-ONLY, and the library correctness). STATUS: COMPLETE.
-/
import Mathlib

namespace OCF.B72

variable {α : Type*} (E : α → ℝ)

/-- Carried state `(z_k, A_k, B_k)`: the current point and an enclosure `[A, B]` of its energy. -/
structure State (α : Type*) where
  z : α
  A : ℝ
  B : ℝ

/-- A partial enclosure oracle answers with an interval, or declines (`none`, "undecided"). -/
abbrev Oracle (α : Type*) := α → Option (ℝ × ℝ)

/-- H-orc, the inclusion property: whenever an oracle answers `(a, b)`, `a ≤ E p ≤ b`. -/
def Sound (o : Oracle α) : Prop :=
  ∀ p a b, o p = some (a, b) → a ≤ E p ∧ E p ≤ b

/-- Verdicts of one step. `rejectCert` is a certified reject (`E p > B`); `rejectOther` an undecided reject. -/
inductive Verdict | accept | rejectCert | rejectOther
  deriving DecidableEq

/-- One step of the rule R1–R3 for state `s`, proposal `p`, verdict `v`, next state `s'`.
`cheap` is the first oracle; `fb s.B` is the fallback, which may depend on the carried bound.
Strict versus non-strict exactly as in the dossier: R1 needs `b < B`, R2 needs `B < a`; equality falls to R3.
R3 is entered when `cheap` is silent, or answered but neither clause fired. A reject keeps the state. -/
inductive Step (cheap : Oracle α) (fb : ℝ → Oracle α) : State α → α → Verdict → State α → Prop
  | r1 {s p a b} : cheap p = some (a, b) → b < s.B → Step cheap fb s p .accept ⟨p, a, b⟩
  | r2 {s p a b} : cheap p = some (a, b) → ¬ b < s.B → s.B < a → Step cheap fb s p .rejectCert s
  | r3acc {s p a' b'} : (cheap p = none ∨ ∃ a b, cheap p = some (a, b) ∧ ¬ b < s.B ∧ ¬ s.B < a) →
      fb s.B p = some (a', b') → b' < s.B → Step cheap fb s p .accept ⟨p, a', b'⟩
  | r3rej {s p a' b'} : (cheap p = none ∨ ∃ a b, cheap p = some (a, b) ∧ ¬ b < s.B ∧ ¬ s.B < a) →
      fb s.B p = some (a', b') → ¬ b' < s.B → s.B < a' → Step cheap fb s p .rejectCert s
  | r3und {s p} : (cheap p = none ∨ ∃ a b, cheap p = some (a, b) ∧ ¬ b < s.B ∧ ¬ s.B < a) →
      (fb s.B p = none ∨ ∃ a' b', fb s.B p = some (a', b') ∧ ¬ b' < s.B ∧ ¬ s.B < a') →
      Step cheap fb s p .rejectOther s

/-- (i) The invariant: the carried interval encloses the energy of the carried point. -/
def Inv (s : State α) : Prop := s.A ≤ E s.z ∧ E s.z ≤ s.B

variable {E} {cheap : Oracle α} {fb : ℝ → Oracle α}

/-- (i), one step: the invariant is preserved. -/
theorem inv_step (hc : Sound E cheap) (hf : ∀ B, Sound E (fb B)) {s p v s'}
    (h : Step cheap fb s p v s') (hs : Inv E s) : Inv E s' := by
  cases h with
  | r1 h1 _ => exact hc _ _ _ h1
  | r2 _ _ _ => exact hs
  | r3acc _ h2 _ => exact hf _ _ _ _ h2
  | r3rej _ _ _ _ => exact hs
  | r3und _ _ => exact hs

/-- (ii) An accept strictly lowers the carried bound. -/
theorem accept_lt {s p s'} (h : Step cheap fb s p .accept s') : s'.B < s.B := by
  cases h with
  | r1 _ h2 => exact h2
  | r3acc _ _ h3 => exact h3

/-- (ii) A reject (certified or undecided) keeps the state. -/
theorem reject_keeps {s p v s'} (h : Step cheap fb s p v s') (hv : v ≠ .accept) : s' = s := by
  cases h with
  | r1 _ _ => exact absurd rfl hv
  | r2 _ _ _ => rfl
  | r3acc _ _ _ => exact absurd rfl hv
  | r3rej _ _ _ _ => rfl
  | r3und _ _ => rfl

/-- An accept moves to the proposal. -/
theorem accept_z {s p s'} (h : Step cheap fb s p .accept s') : s'.z = p := by
  cases h <;> rfl

/-- (iii) A certified reject proves `E(z⁺) > B_k ≥ E(z_k)`. -/
theorem rejectCert_gt (hc : Sound E cheap) (hf : ∀ B, Sound E (fb B)) {s p s'}
    (h : Step cheap fb s p .rejectCert s') (hs : Inv E s) :
    s.B < E p ∧ E s.z ≤ s.B ∧ E s.z < E p := by
  have hb : s.B < E p := by
    cases h with
    | r2 h1 _ h3 => exact lt_of_lt_of_le h3 (hc _ _ _ h1).1
    | r3rej _ h2 _ h4 => exact lt_of_lt_of_le h4 (hf _ _ _ _ h2).1
  exact ⟨hb, hs.2, lt_of_le_of_lt hs.2 hb⟩

/-- (iv) At an accept the new energy is below the old bound, and rises by less than the old width. -/
theorem accept_bounds (hc : Sound E cheap) (hf : ∀ B, Sound E (fb B)) {s p s'}
    (h : Step cheap fb s p .accept s') (hs : Inv E s) :
    E p < s.B ∧ E p - E s.z < s.B - s.A := by
  have h1 : E s'.z ≤ s'.B := (inv_step hc hf h hs).2
  have h2 : s'.B < s.B := accept_lt h
  rw [accept_z h] at h1
  exact ⟨lt_of_le_of_lt h1 h2, by linarith [hs.1]⟩

/-- (v) Exclusivity of the two clauses: an answered interval of a sound oracle is never both `b < B` and `B < a`. -/
theorem excl {o : Oracle α} (ho : Sound E o) {p a b} (h : o p = some (a, b)) {B : ℝ} :
    ¬ (b < B ∧ B < a) := by
  rintro ⟨h1, h2⟩
  have := ho p a b h
  linarith [this.1, this.2]

/-- The rule is a function: verdict and next state are determined by the state and the proposal. -/
theorem step_det {s p v v' s' s''} (h : Step cheap fb s p v s') (h' : Step cheap fb s p v' s'') :
    v = v' ∧ s' = s'' := by
  cases h with
  | r1 h1 h2 =>
    cases h' with
    | r1 h1' _ => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩
    | r2 h1' h2' _ => rw [h1] at h1'; cases h1'; exact absurd h2 h2'
    | r3acc hc' _ _ =>
      rcases hc' with hc' | ⟨a, b, hab, h3, _⟩
      · rw [h1] at hc'; cases hc'
      · rw [h1] at hab; cases hab; exact absurd h2 h3
    | r3rej hc' _ _ _ =>
      rcases hc' with hc' | ⟨a, b, hab, h3, _⟩
      · rw [h1] at hc'; cases hc'
      · rw [h1] at hab; cases hab; exact absurd h2 h3
    | r3und hc' _ =>
      rcases hc' with hc' | ⟨a, b, hab, h3, _⟩
      · rw [h1] at hc'; cases hc'
      · rw [h1] at hab; cases hab; exact absurd h2 h3
  | r2 h1 h2 h3 =>
    cases h' with
    | r1 h1' h2' => rw [h1] at h1'; cases h1'; exact absurd h2' h2
    | r2 _ _ _ => exact ⟨rfl, rfl⟩
    | r3acc hc' _ _ =>
      rcases hc' with hc' | ⟨a, b, hab, _, h4⟩
      · rw [h1] at hc'; cases hc'
      · rw [h1] at hab; cases hab; exact absurd h3 h4
    | r3rej hc' _ _ _ =>
      rcases hc' with hc' | ⟨a, b, hab, _, h4⟩
      · rw [h1] at hc'; cases hc'
      · rw [h1] at hab; cases hab; exact absurd h3 h4
    | r3und hc' _ =>
      rcases hc' with hc' | ⟨a, b, hab, _, h4⟩
      · rw [h1] at hc'; cases hc'
      · rw [h1] at hab; cases hab; exact absurd h3 h4
  | r3acc hc h1 h2 =>
    cases h' with
    | r1 h1' h2' =>
      rcases hc with hc | ⟨a, b, hab, h3, _⟩
      · rw [h1'] at hc; cases hc
      · rw [h1'] at hab; cases hab; exact absurd h2' h3
    | r2 h1' _ h3' =>
      rcases hc with hc | ⟨a, b, hab, _, h4⟩
      · rw [h1'] at hc; cases hc
      · rw [h1'] at hab; cases hab; exact absurd h3' h4
    | r3acc _ h1' _ => rw [h1] at h1'; cases h1'; exact ⟨rfl, rfl⟩
    | r3rej _ h1' h2' _ => rw [h1] at h1'; cases h1'; exact absurd h2 h2'
    | r3und _ hd =>
      rcases hd with hd | ⟨a, b, hab, h3, _⟩
      · rw [h1] at hd; cases hd
      · rw [h1] at hab; cases hab; exact absurd h2 h3
  | r3rej hc h1 h2 h3 =>
    cases h' with
    | r1 h1' h2' =>
      rcases hc with hc | ⟨a, b, hab, h5, _⟩
      · rw [h1'] at hc; cases hc
      · rw [h1'] at hab; cases hab; exact absurd h2' h5
    | r2 h1' _ h3' =>
      rcases hc with hc | ⟨a, b, hab, _, h4⟩
      · rw [h1'] at hc; cases hc
      · rw [h1'] at hab; cases hab; exact absurd h3' h4
    | r3acc _ h1' h2' => rw [h1] at h1'; cases h1'; exact absurd h2' h2
    | r3rej _ _ _ _ => exact ⟨rfl, rfl⟩
    | r3und _ hd =>
      rcases hd with hd | ⟨a, b, hab, _, h4⟩
      · rw [h1] at hd; cases hd
      · rw [h1] at hab; cases hab; exact absurd h3 h4
  | r3und hc hd =>
    cases h' with
    | r1 h1' h2' =>
      rcases hc with hc | ⟨a, b, hab, h5, _⟩
      · rw [h1'] at hc; cases hc
      · rw [h1'] at hab; cases hab; exact absurd h2' h5
    | r2 h1' _ h3' =>
      rcases hc with hc | ⟨a, b, hab, _, h4⟩
      · rw [h1'] at hc; cases hc
      · rw [h1'] at hab; cases hab; exact absurd h3' h4
    | r3acc _ h1' h2' =>
      rcases hd with hd | ⟨a, b, hab, h3, _⟩
      · rw [h1'] at hd; cases hd
      · rw [h1'] at hab; cases hab; exact absurd h2' h3
    | r3rej _ h1' _ h3' =>
      rcases hd with hd | ⟨a, b, hab, _, h4⟩
      · rw [h1'] at hd; cases hd
      · rw [h1'] at hab; cases hab; exact absurd h3' h4
    | r3und _ _ => exact ⟨rfl, rfl⟩

/-- A run: any finite sequence of steps from `s0` (proposals arbitrary, verdicts as produced). -/
def Reach (cheap : Oracle α) (fb : ℝ → Oracle α) (s0 : State α) : State α → Prop :=
  Relation.ReflTransGen (fun s s' => ∃ p v, Step cheap fb s p v s') s0

/-- (i) along every run: at every reached step `A_k ≤ E(z_k) ≤ B_k`. -/
theorem reach_inv (hc : Sound E cheap) (hf : ∀ B, Sound E (fb B)) {s0 s}
    (h0 : Inv E s0) (hr : Reach cheap fb s0 s) : Inv E s := by
  induction hr with
  | refl => exact h0
  | tail _ hstep ih => obtain ⟨p, v, hs⟩ := hstep; exact inv_step hc hf hs ih

/-- (ii) along every run the carried bound never increases. -/
theorem reach_B_le {s0 s} (hr : Reach cheap fb s0 s) : s.B ≤ s0.B := by
  induction hr with
  | refl => exact le_rfl
  | tail _ hstep ih =>
    obtain ⟨p, v, hs⟩ := hstep
    by_cases hv : v = .accept
    · subst hv; exact le_trans (accept_lt hs).le ih
    · rw [reject_keeps hs hv]; exact ih

/-- (iii) at a reached state, a certified reject of any proposal proves `E(z⁺) > B_k ≥ E(z_k)`. -/
theorem reach_rejectCert_gt (hc : Sound E cheap) (hf : ∀ B, Sound E (fb B)) {s0 s p s'}
    (h0 : Inv E s0) (hr : Reach cheap fb s0 s) (h : Step cheap fb s p .rejectCert s') :
    s.B < E p ∧ E s.z ≤ s.B ∧ E s.z < E p :=
  rejectCert_gt hc hf h (reach_inv hc hf h0 hr)

/-- (iv) at a reached state, an accept of any proposal gives `E(z_{k+1}) < B_k` and rise `< B_k − A_k`. -/
theorem reach_accept_bounds (hc : Sound E cheap) (hf : ∀ B, Sound E (fb B)) {s0 s p s'}
    (h0 : Inv E s0) (hr : Reach cheap fb s0 s) (h : Step cheap fb s p .accept s') :
    E p < s.B ∧ E p - E s.z < s.B - s.A :=
  accept_bounds hc hf h (reach_inv hc hf h0 hr)

/-! ## Non-vacuity -/

/-- The exact oracle on `ℝ` with `E = id`. -/
def idOracle : Oracle ℝ := fun z => some (z, z)

/-- The oracle that always declines. -/
def noOracle : Oracle ℝ := fun _ => none

theorem idOracle_sound : Sound (id : ℝ → ℝ) idOracle := by
  intro p a b h
  simp only [idOracle, Option.some.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  simp

theorem noOracle_sound : Sound (id : ℝ → ℝ) noOracle := by
  intro p a b h
  simp [noOracle] at h

/-- State at `z = 2` with exact enclosure `[2, 2]`. -/
def s2 : State ℝ := ⟨2, 2, 2⟩

/-- R1: the proposal `1` is accepted (`1 < 2`). -/
theorem ex_accept : Step idOracle (fun _ => noOracle) s2 1 .accept ⟨1, 1, 1⟩ :=
  .r1 (a := 1) (b := 1) (by simp [idOracle]) (by norm_num [s2])

/-- R2: the proposal `3` is a certified reject (`2 < 3`). -/
theorem ex_rejectCert : Step idOracle (fun _ => noOracle) s2 3 .rejectCert s2 :=
  .r2 (a := 3) (b := 3) (by simp [idOracle]) (by norm_num [s2]) (by norm_num [s2])

/-- R3, undecided reject: the proposal `2` equals the carried point (a stop); equality falls through both clauses. -/
theorem ex_rejectOther : Step idOracle (fun _ => noOracle) s2 2 .rejectOther s2 :=
  .r3und (Or.inr ⟨2, 2, by simp [idOracle], by norm_num [s2], by norm_num [s2]⟩) (Or.inl (by simp [noOracle]))

/-- R3 accept: the cheap oracle declines and the fallback answers `[1, 1]`, `1 < 2`. -/
theorem ex_r3acc : Step noOracle (fun _ => idOracle) s2 1 .accept ⟨1, 1, 1⟩ :=
  .r3acc (a' := 1) (b' := 1) (Or.inl (by simp [noOracle])) (by simp [idOracle]) (by norm_num [s2])

/-- R3 certified reject: the cheap oracle declines and the fallback answers `[3, 3]`, `3 > 2`. -/
theorem ex_r3rej : Step noOracle (fun _ => idOracle) s2 3 .rejectCert s2 :=
  .r3rej (a' := 3) (b' := 3) (Or.inl (by simp [noOracle])) (by simp [idOracle]) (by norm_num [s2])
    (by norm_num [s2])

end OCF.B72

#print axioms OCF.B72.inv_step
#print axioms OCF.B72.accept_lt
#print axioms OCF.B72.reject_keeps
#print axioms OCF.B72.accept_z
#print axioms OCF.B72.rejectCert_gt
#print axioms OCF.B72.accept_bounds
#print axioms OCF.B72.excl
#print axioms OCF.B72.step_det
#print axioms OCF.B72.reach_inv
#print axioms OCF.B72.reach_B_le
#print axioms OCF.B72.reach_rejectCert_gt
#print axioms OCF.B72.reach_accept_bounds
#print axioms OCF.B72.idOracle_sound
#print axioms OCF.B72.noOracle_sound
#print axioms OCF.B72.ex_accept
#print axioms OCF.B72.ex_rejectCert
#print axioms OCF.B72.ex_rejectOther
#print axioms OCF.B72.ex_r3acc
#print axioms OCF.B72.ex_r3rej

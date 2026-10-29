/-
Skepsis 2.0: do not decide by a certainty we do not have.

Formalization of the four operational clauses on the plate.

Proved here, with no `sorry`:
* a claim is guaranteed relative to a model class and data precisely when
  every compatible model satisfies it; the class itself remains a hypothesis;
  the empty class guarantees nothing;
* the multi-model predecessor
  `P_D(V) = {x ∈ K : ∃ a ∈ A(x) ∀ M ∈ M(D) ∀ w ∈ W_M(x,a), F_M(x,a,w) ∈ V}`;
  if `V ⊆ P_D(V)`, the true model is in the class, and a policy picks such an
  action before the circumstance, every admissible run stays in `V`;
* two models are separated by an interface when some policy makes their
  transcript laws differ; agreement on every available policy means this
  interface does not separate them;
* the already-proved sandwich reapplied: `0 ≤ C(T) - L(T) ≤ c⋆`.
  The inequality does not force a positive gap.

Not proved here:
* that a viable `V` exists for an arbitrary class;
* that enlarging the interface produces a separating policy;
* the sandwich itself (imported from `Penalty`);
* that doubt, a wish, or an empty action set produces a safe action.
-/
import CausalSeed.Penalty
import Mathlib.Data.Set.Basic

noncomputable section

open Classical

namespace CausalSpectrum
namespace Skepsis

/-! ## 1. A claim must survive a change of compatible model -/

variable {Model : Type*}

/-- A claim about a model. The class of models is a separate hypothesis. -/
structure Claim (Model : Type*) where
  holds : Model → Prop

/-- Models compatible with data `D`. Compatibility is a parameter, not a theorem. -/
abbrev Compatible (Model : Type*) := Set Model

/-- `Q` is guaranteed relative to the compatible class.
The class itself remains an assumption. An empty class does not count. -/
def guaranteed (cls : Compatible Model) (Q : Claim Model) : Prop :=
  cls.Nonempty ∧ ∀ M ∈ cls, Q.holds M

theorem guaranteed_iff (cls : Compatible Model) (Q : Claim Model) :
    guaranteed cls Q ↔ cls.Nonempty ∧ ∀ M ∈ cls, Q.holds M := Iff.rfl

/-- The empty class guarantees nothing. Emptiness signals a bad class or a bad
compatibility criterion; it is not a proof of `Q`. -/
theorem empty_guarantees_nothing (Q : Claim Model) : ¬ guaranteed (∅ : Set Model) Q := by
  intro h
  exact h.1.ne_empty rfl

/-- A guarantee is only as strong as the class. Shrinking the class preserves it
only if the smaller class is still nonempty. -/
theorem guaranteed_mono {cls cls' : Compatible Model} {Q : Claim Model}
    (h : guaranteed cls Q) (hsub : cls' ⊆ cls) (hne : cls'.Nonempty) :
    guaranteed cls' Q :=
  ⟨hne, fun M hM => h.2 M (hsub hM)⟩

/-! ## 2. A safe action must survive uncertainty about the model -/

variable {X A W : Type*}

/-- A family of models on a common state space, with a common required set `K`.
Disturbances and the update may depend on the model. -/
structure Family (X A W : Type*) where
  Model : Type*
  K : Set X
  act : X → Set A
  /-- Admissible disturbances of model `M` at `(x, a)`. -/
  legal : Model → X → A → Set W
  step : Model → X → A → W → X

/-- Multi-model predecessor. The action is chosen before the model and the
disturbance. Both are universally quantified. -/
def pred (F : Family X A W) (cls : Set F.Model) (V : Set X) : Set X :=
  {x | x ∈ F.K ∧ ∃ a ∈ F.act x, ∀ M ∈ cls, ∀ w ∈ F.legal M x a, F.step M x a w ∈ V}

/-- Actions that keep every compatible model inside `V`. -/
def safe (F : Family X A W) (cls : Set F.Model) (V : Set X) (x : X) : Set A :=
  {a | a ∈ F.act x ∧ ∀ M ∈ cls, ∀ w ∈ F.legal M x a, F.step M x a w ∈ V}

/-- `V` can be held against every model in the class. Existence is a hypothesis. -/
structure Viable (F : Family X A W) (cls : Set F.Model) (V : Set X) : Prop where
  nonempty : V.Nonempty
  holds : V ⊆ pred F cls V

theorem safe_nonempty {F : Family X A W} {cls : Set F.Model} {V : Set X}
    (hV : Viable F cls V) {x : X} (hx : x ∈ V) : (safe F cls V x).Nonempty := by
  obtain ⟨hxK, a, ha, hw⟩ := hV.holds hx
  exact ⟨a, ha, hw⟩

/-- State at time `t`, paired with the history of earlier states. -/
def roll (F : Family X A W) (π : List X → X → A) (M : F.Model) (w : ℕ → W) (x0 : X) :
    ℕ → X × List X
  | 0 => (x0, [])
  | t + 1 =>
    let r := roll F π M w x0 t
    (F.step M r.1 (π r.2 r.1) (w t), r.2 ++ [r.1])

/-- If the true model is in the class, every disturbance it admits is covered,
and the policy picks a safe action before seeing either, the run stays in `V`. -/
theorem roll_mem {F : Family X A W} {cls : Set F.Model} {V : Set X}
    {π : List X → X → A} {M : F.Model} {w : ℕ → W} {x0 : X}
    (hx0 : x0 ∈ V) (hM : M ∈ cls)
    (hchoice : ∀ h x, x ∈ V → π h x ∈ safe F cls V x)
    (hlegal : ∀ t, w t ∈ F.legal M (roll F π M w x0 t).1 (π (roll F π M w x0 t).2 (roll F π M w x0 t).1)) :
    ∀ t, (roll F π M w x0 t).1 ∈ V := by
  intro t
  induction t with
  | zero =>
      simpa [roll] using hx0
  | succ t ih =>
      have hsafe : π (roll F π M w x0 t).2 (roll F π M w x0 t).1 ∈
          safe F cls V (roll F π M w x0 t).1 :=
        hchoice _ _ ih
      have hw := hsafe.2 M hM (w t) (hlegal t)
      simpa [roll] using hw

/-- Protection under model uncertainty. The guarantee holds only for a model
that belongs to the class, and only for disturbances that model admits. -/
theorem stays {F : Family X A W} {cls : Set F.Model} {V : Set X}
    (hV : Viable F cls V)
    {π : List X → X → A} {M : F.Model} {w : ℕ → W} {x0 : X}
    (hx0 : x0 ∈ V) (hM : M ∈ cls)
    (hchoice : ∀ h x, x ∈ V → π h x ∈ safe F cls V x)
    (hlegal : ∀ t, w t ∈ F.legal M (roll F π M w x0 t).1
        (π (roll F π M w x0 t).2 (roll F π M w x0 t).1)) :
    ∀ t, (roll F π M w x0 t).1 ∈ V ∧ (roll F π M w x0 t).1 ∈ F.K := by
  intro t
  have hmem := roll_mem hx0 hM hchoice hlegal t
  exact ⟨hmem, (hV.holds hmem).1⟩

/-- No available action. The protected set may be everything; no viable `V` exists. -/
def wish : Family Unit Unit Unit where
  Model := Unit
  K := Set.univ
  act _ := ∅
  legal _ _ _ := Set.univ
  step _ x _ _ := x

theorem wish_is_not_an_action :
    ¬ ∃ V : Set Unit, Viable wish (Set.univ : Set Unit) V := by
  rintro ⟨V, h⟩
  obtain ⟨x, hx⟩ := h.nonempty
  obtain ⟨a, ha, -⟩ := safe_nonempty h hx
  simp [wish] at ha

/-! ## 3. A new question matters if it can separate unresolved models -/

variable {Policy Transcript : Type*}

/-- Transcript law of a model under a policy. Equality of laws is the criterion. -/
abbrev Law (Model Policy Transcript : Type*) := Model → Policy → Transcript → Prop

/-- Some available policy makes the laws differ. This is a possibility of
statistical separation, not certainty after one sample. -/
def separates (law : Law Model Policy Transcript) (M1 M2 : Model) : Prop :=
  ∃ π : Policy, law M1 π ≠ law M2 π

/-- Agreement on every available policy. This interface does not separate them. -/
def indistinguishable (law : Law Model Policy Transcript) (M1 M2 : Model) : Prop :=
  ∀ π : Policy, law M1 π = law M2 π

theorem separates_iff_not_indistinguishable
    (law : Law Model Policy Transcript) (M1 M2 : Model) :
    separates law M1 M2 ↔ ¬ indistinguishable law M1 M2 := by
  simp [separates, indistinguishable]

/-- Observational agreement is not identification. If every available policy
gives the same law, no transcript statistic of this interface separates the
models with certainty. A distinction requires a policy on which the laws differ. -/
theorem agreement_does_not_separate
    (law : Law Model Policy Transcript) {M1 M2 : Model}
    (h : indistinguishable law M1 M2) : ¬ separates law M1 M2 :=
  (separates_iff_not_indistinguishable law M1 M2).not.mpr (fun hn => hn h)

/-! ## 4. Shannon prices the realization, not the doubt -/

/-- The imported sandwich. `c⋆` is an overhead on exact simulation, not a
measure of epistemic error. The relation is non-strict: equality is permitted
by the inequality, and is not ruled out. -/
theorem realization_gap (T : Tree) :
    0 ≤ causalMin T - envelopeMean T ∧
      causalMin T - envelopeMean T ≤ shannonOverhead := by
  constructor
  · linarith [(ordinaryMin_ge_envelope T).trans (ordinaryMin_le_causalMin T)]
  · linarith [causalMin_le_overhead T]

end Skepsis
end CausalSpectrum

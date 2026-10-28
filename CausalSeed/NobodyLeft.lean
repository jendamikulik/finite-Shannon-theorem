/-
ACE RIMMER: nobody is dropped by the definition.

Robust invariance of a jointly protected set. What is proved:

* if `V` is viable, every adaptive policy that keeps choosing an action
  from `A_V(x)` before the circumstance is known stays in `V`;
* therefore every declared floor `d_i` stays nonnegative;
* the quantifier order in (A) is essential;
* an empty action set is a system in which no viable set exists.

What is not proved:

* that a viable `V` exists for an arbitrary system;
* that a wish produces a safe action;
* that the Shannon sandwich constructs `V`, produces a safe action,
  or prices help.

`supplied_tree_sandwich` only reapplies the already proved finite-tree
bound to a tree that has been supplied separately.
-/
import CausalSeed.Penalty
import Mathlib.Data.Set.Basic

noncomputable section

namespace CausalSpectrum
namespace NobodyLeft

variable {I X A W : Type*}

/-- A finite system of participants, states, actions, and circumstances.
`participants` nonempty matches the note. `floor i x ≥ 0` is a declared
minimum standard for participant `i`, not a measure of a person's worth. -/
structure Model (I X A W : Type*) where
  participants : Nonempty I
  act : X → Set A
  step : X → A → W → X
  floor : I → X → ℝ

/-- States in which every declared floor is met. -/
def protectedSet (M : Model I X A W) : Set X :=
  {x | ∀ i, 0 ≤ M.floor i x}

/-- Actions that stay in `V` no matter which circumstance arrives.
The action is fixed before `w` is known. -/
def safe (M : Model I X A W) (V : Set X) (x : X) : Set A :=
  {a | a ∈ M.act x ∧ ∀ w, M.step x a w ∈ V}

/-- Assumption (A): a nonempty protected set that can be held by an
action chosen before the circumstance. -/
structure Viable (M : Model I X A W) (V : Set X) : Prop where
  nonempty : V.Nonempty
  subset : V ⊆ protectedSet M
  action : ∀ x ∈ V, ∃ a ∈ M.act x, ∀ w, M.step x a w ∈ V

theorem safe_nonempty {M : Model I X A W} {V : Set X} (hV : Viable M V)
    {x : X} (hx : x ∈ V) : (safe M V x).Nonempty := by
  obtain ⟨a, ha, hw⟩ := hV.action x hx
  exact ⟨a, ha, hw⟩

theorem viable_iff_safe {M : Model I X A W} {V : Set X}
    (hne : V.Nonempty) (hsub : V ⊆ protectedSet M) :
    Viable M V ↔ ∀ x ∈ V, (safe M V x).Nonempty := by
  constructor
  · intro h x hx
    exact safe_nonempty h hx
  · intro h
    refine ⟨hne, hsub, ?_⟩
    intro x hx
    obtain ⟨a, ha⟩ := h x hx
    exact ⟨a, ha.1, ha.2⟩

/-- State at time `t`, paired with the history of earlier states.
The policy may read that history. -/
def roll (M : Model I X A W) (π : List X → X → A) (w : ℕ → W) (x0 : X) :
    ℕ → X × List X
  | 0 => (x0, [])
  | t + 1 =>
      let r := roll M π w x0 t
      (M.step r.1 (π r.2 r.1) (w t), r.2 ++ [r.1])

theorem roll_mem {M : Model I X A W} {V : Set X}
    {π : List X → X → A} {w : ℕ → W} {x0 : X} (hx0 : x0 ∈ V)
    (hchoice : ∀ h x, x ∈ V → π h x ∈ safe M V x) :
    ∀ t, (roll M π w x0 t).1 ∈ V := by
  intro t
  induction t with
  | zero =>
      simpa [roll] using hx0
  | succ t ih =>
      have hsafe : π (roll M π w x0 t).2 (roll M π w x0 t).1 ∈
          safe M V (roll M π w x0 t).1 :=
        hchoice _ _ ih
      have hw := hsafe.2 (w t)
      simpa [roll] using hw

/-- Protection under adaptive choice. Any policy that, on the history so
far, picks an action from `safe V` stays inside every declared floor,
for every sequence of circumstances. -/
theorem nobody_left {M : Model I X A W} {V : Set X} (hV : Viable M V)
    {π : List X → X → A} {w : ℕ → W} {x0 : X} (hx0 : x0 ∈ V)
    (hchoice : ∀ h x, x ∈ V → π h x ∈ safe M V x) :
    ∀ t i, 0 ≤ M.floor i (roll M π w x0 t).1 := by
  intro t i
  exact hV.subset (roll_mem hx0 hchoice t) i

/-! The action has to be chosen first. Knowing the circumstance and then
picking the action is a strictly weaker demand. -/

def knowsFirst (M : Model I X A W) (V : Set X) : Prop :=
  V.Nonempty ∧ V ⊆ protectedSet M ∧
    ∀ x ∈ V, ∀ w, ∃ a ∈ M.act x, M.step x a w ∈ V

/-- Inside `true`, the next state equals whether the action matched the
circumstance. From `false` there is no return. -/
def orderSplit : Model Unit Bool Bool Bool where
  participants := ⟨()⟩
  act _ := Set.univ
  step x a w := x && (a == w)
  floor _ _ := 0

theorem order_matters :
    knowsFirst orderSplit ({true} : Set Bool) ∧
      ¬ Viable orderSplit ({true} : Set Bool) := by
  constructor
  · refine ⟨⟨true, rfl⟩, ?_, ?_⟩
    · intro x _ i
      simp [orderSplit]
    · intro x hx w
      have hx' : x = true := by simpa [Set.mem_singleton_iff] using hx
      subst hx'
      refine ⟨w, Set.mem_univ _, ?_⟩
      simp [orderSplit, Set.mem_singleton_iff]
  · intro h
    obtain ⟨a, -, hall⟩ := h.action true (Set.mem_singleton _)
    have hbad := hall (!a)
    have hne : (a == !a) = false := by cases a <;> rfl
    simp [orderSplit, Set.mem_singleton_iff, hne, Bool.and_false] at hbad

/-- No available action. The protected set is everything, and still no
viable `V` exists. -/
def wish : Model Unit Unit Unit Unit where
  participants := ⟨()⟩
  act _ := ∅
  step x _ _ := x
  floor _ _ := 0

theorem wish_is_not_an_action : ¬ ∃ V : Set Unit, Viable wish V := by
  rintro ⟨V, h⟩
  obtain ⟨x, hx⟩ := h.nonempty
  obtain ⟨a, ha, -⟩ := h.action x hx
  simp [wish] at ha

/-! A supplied tree still has the Shannon sandwich. The tree is an extra
hypothesis. Nothing above builds one out of `Viable`. -/

theorem supplied_tree_sandwich (T : Tree) :
    envelopeMean T ≤ causalMin T ∧
      causalMin T ≤ envelopeMean T + shannonOverhead :=
  ⟨(ordinaryMin_ge_envelope T).trans (ordinaryMin_le_causalMin T),
    causalMin_le_overhead T⟩

end NobodyLeft
end CausalSpectrum

#print axioms CausalSpectrum.NobodyLeft.nobody_left
#print axioms CausalSpectrum.NobodyLeft.order_matters
#print axioms CausalSpectrum.NobodyLeft.wish_is_not_an_action
#print axioms CausalSpectrum.NobodyLeft.supplied_tree_sandwich

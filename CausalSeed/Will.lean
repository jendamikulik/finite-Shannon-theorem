/-
Responsibility with love, and the will as an operator.

`0` is a possibility not yet realized. `1` is that possibility realized.
The model assumes a will that carries out the possibility:

  `W : Fin 2 → Fin 2`,   `W 0 = 1`,   `W 1 = 1`.

Then `W 0 = W 1 = 1` and `W ∘ W = W`. Under `W` the two states have one
image. In the quotient by `x ~ y ↔ W x = W y` one has `[0] = [1]`.
The original states stay distinct: `0 ≠ 1`. The quotient identification
is not an identification in `Fin 2`.

The constant value is the hypothesis of the model. A different operator
leaves `0` unrealized. Neither distinctness of the states nor an empty
shared step produces `W`.

A shared step is an action acceptable to every participant who is
present. Responsibility for one's own step is one's own set. It does
not require an action acceptable at every state, and it does not fill
an empty intersection. Making room, where one can, is choosing an
action that remains acceptable to the other. Hearing "no" is that
empty intersection.

Not proved:

* that a human will realizes a given possibility;
* that a shared step exists;
* that love is this operator;
* that one's own step discharges anyone else's;
* anything about the zeros of `ξ`.
-/
import Mathlib.Data.Set.Basic

namespace CausalSpectrum
namespace Will

/-- `0` is not yet realized, `1` is realized.
The operator sends both to realized. That is the model, not a theorem. -/
def W : Fin 2 → Fin 2 := fun _ => 1

theorem realizes_zero : W 0 = 1 := rfl

theorem realizes_one : W 1 = 1 := rfl

theorem same_image : W 0 = W 1 := rfl

theorem idempotent (x : Fin 2) : W (W x) = W x := rfl

theorem comp_self : W ∘ W = W :=
  funext idempotent

/-- The boxed identity of the note. -/
theorem under_will : W 0 = W 1 ∧ W 0 = 1 ∧ W ∘ W = W :=
  ⟨same_image, realizes_zero, comp_self⟩

/-- Same image. -/
def willSetoid : Setoid (Fin 2) where
  r := fun x y => W x = W y
  iseqv := {
    refl := fun _ => rfl
    symm := fun {_ _} h => h.symm
    trans := fun {_ _ _} h₁ h₂ => h₁.trans h₂
  }

abbrev WillSpace := Quotient willSetoid

def imageClass (x : Fin 2) : WillSpace :=
  Quotient.mk willSetoid x

/-- In the quotient, unrealized and realized are one class. -/
theorem classes_equal : imageClass 0 = imageClass 1 :=
  Quotient.sound (s := willSetoid) same_image

/-- The original states are not identified. -/
theorem original_states_distinct : (0 : Fin 2) ≠ 1 := by
  decide

/-- `[0] = [1]` is not `0 = 1`. -/
theorem quotient_is_not_arithmetic :
    imageClass 0 = imageClass 1 ∧ (0 : Fin 2) ≠ 1 :=
  ⟨classes_equal, original_states_distinct⟩

/-- The quotient has one element. -/
theorem quotient_collapses (u v : WillSpace) : u = v := by
  refine Quotient.inductionOn₂ u v ?_
  intro x y
  exact Quotient.sound (s := willSetoid) (show W x = W y from rfl)

/-- An operator that does not carry the possibility out.
Constant realization is chosen, not deduced from `0 ≠ 1`. -/
def leave : Fin 2 → Fin 2 := id

theorem leave_keeps_unrealized : leave 0 = 0 := rfl

theorem realization_is_assumed :
    (0 : Fin 2) ≠ 1 ∧ leave 0 ≠ 1 ∧ W ≠ leave := by
  refine ⟨original_states_distinct, ?_, ?_⟩
  · decide
  · intro h
    have := congrFun h 0
    simp [W, leave] at this

/-
A shared step, one's own step, and room for the other.

The participants are an index type. Each brings a set of acceptable
actions. Nothing below asserts that the intersection is nonempty.
-/
namespace Step

variable {I U : Type*}

/-- Actions acceptable to every participant who is present. -/
def shared (A : I → Set U) : Set U :=
  {a | ∀ i, a ∈ A i}

theorem mem_shared {A : I → Set U} {a : U} :
    a ∈ shared A ↔ ∀ i, a ∈ A i :=
  Iff.rfl

/-- Existence of one action acceptable to all present participants
is nonemptiness of that intersection, and nothing more. -/
theorem common_step_iff (A : I → Set U) :
    (∃ a : U, ∀ i, a ∈ A i) ↔ (shared A).Nonempty := by
  simp [shared, Set.Nonempty]

/-- A shared step, if one exists, is acceptable to this participant. -/
theorem shared_makes_room (A : I → Set U) (j : I) {a : U}
    (ha : a ∈ shared A) : a ∈ A j :=
  ha j

/-- One's own acceptable actions. Not a claim about anyone else. -/
def own (mine : Set U) : Set U := mine

/-- Room for the other: an action still in their set. -/
def room (mine other : Set U) : Set U := mine ∩ other

theorem room_leaves_the_other {mine other : Set U} {a : U}
    (ha : a ∈ room mine other) : a ∈ other :=
  ha.2

/-- Kindness does not require identifying the other with oneself. -/
theorem room_without_identification :
    ∃ mine other : Set Bool, ∃ a : Bool,
      (false : Bool) ≠ true ∧ a ∈ room mine other := by
  refine ⟨Set.univ, Set.univ, true, Bool.false_ne_true, ?_⟩
  simp [room]

/-- Hearing "no". Both have a step of their own. The shared step is empty.
The definition does not fill it. -/
theorem can_hear_no :
    ∃ mine other : Set Bool,
      (own mine).Nonempty ∧ (own other).Nonempty ∧ room mine other = ∅ := by
  refine ⟨{b | b = true}, {b | b = false}, ⟨true, rfl⟩, ⟨false, rfl⟩, ?_⟩
  ext a
  constructor
  · intro h
    have ha : a = true := h.1
    have hb : a = false := h.2
    exact Bool.false_ne_true (hb.symm.trans ha)
  · intro h
    exact h.elim

/-- An action acceptable at my state need not be acceptable at every state.
Responsibility for a step is not guilt for the whole world. -/
def atEveryState {X : Type*} (A : X → Set U) : Set U :=
  {a | ∀ x, a ∈ A x}

theorem own_step_is_not_the_world :
    ∃ (A : Bool → Set Unit) (me : Bool),
      (own (A me)).Nonempty ∧ atEveryState A = ∅ := by
  let A : Bool → Set Unit
    | true => Set.univ
    | false => ∅
  refine ⟨A, true, ⟨(), Set.mem_univ ()⟩, ?_⟩
  ext a
  constructor
  · intro ha
    have hfalse : a ∈ A false := ha false
    simp [A] at hfalse
  · intro h
    exact (Set.notMem_empty a h).elim

/-- My own step can exist while no action is acceptable to everyone present. -/
theorem own_step_is_not_a_shared_step :
    ∃ A : Bool → Set Unit,
      (own (A true)).Nonempty ∧ shared A = ∅ := by
  let A : Bool → Set Unit
    | true => Set.univ
    | false => ∅
  refine ⟨A, ⟨(), Set.mem_univ ()⟩, ?_⟩
  ext a
  constructor
  · intro ha
    have hfalse : a ∈ A false := ha false
    simp [A] at hfalse
  · intro h
    exact (Set.notMem_empty a h).elim

end Step
end Will
end CausalSpectrum

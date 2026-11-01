/-
Focus far enough to take one safe step.

An observation leaves a set `M` of compatible states. An action is
commonly safe when it lies in `A x` for every `x ∈ M`. That is the
definition of the intersection, and the equivalence below is only that
definition written twice.

What is proved:

* existence of one action safe on all of `M` is the same as
  nonemptiness of the intersection of the safe-action sets;
* shrinking `M` keeps every previously common action and may add more;
* a singleton fibre is not required;
* the guarantee reaches a state only if that state lies in `M`.

What is not proved:

* that the intersection is nonempty;
* that `M` contains the true state;
* that `A` correctly describes safety.
-/
import Mathlib.Data.Set.Basic

namespace CausalSpectrum
namespace FocusStep

variable {X U : Type*}

/-- Actions safe at every state compatible with the observation. -/
def common (A : X → Set U) (M : Set X) : Set U :=
  {a | ∀ x, x ∈ M → a ∈ A x}

theorem mem_common {A : X → Set U} {M : Set X} {a : U} :
    a ∈ common A M ↔ ∀ x, x ∈ M → a ∈ A x :=
  Iff.rfl

theorem common_iff (A : X → Set U) (M : Set X) :
    (∃ a : U, ∀ x ∈ M, a ∈ A x) ↔ (common A M).Nonempty := by
  simp [common, Set.Nonempty]

/-- A finer observation keeps every action that was already common. -/
theorem focus_mono (A : X → Set U) {M M' : Set X} (h : M' ⊆ M) :
    common A M ⊆ common A M' := by
  intro a ha x hx
  exact ha x (h hx)

/-- Shrinking the fibre can make a new action commonly safe. -/
theorem focus_can_gain :
    ∃ A : Bool → Set Unit, ∃ M M' : Set Bool,
      M' ⊆ M ∧ M'.Nonempty ∧
        common A M = ∅ ∧ (common A M').Nonempty := by
  let A : Bool → Set Unit
    | true => Set.univ
    | false => ∅
  let M' : Set Bool := {b | b = true}
  refine ⟨A, Set.univ, M', ?_, ⟨true, rfl⟩, ?_, ?_⟩
  · intro b hb
    exact Set.mem_univ b
  · ext a
    constructor
    · intro ha
      have hfalse : a ∈ A false := ha false (Set.mem_univ _)
      simp [A] at hfalse
    · intro h
      exact (Set.notMem_empty a h).elim
  · refine ⟨(), ?_⟩
    intro b hb
    subst hb
    exact Set.mem_univ ()

/-- The true state need not be singled out. -/
theorem singleton_not_needed :
    ∃ A : Bool → Set Unit, ∃ M : Set Bool,
      (∃ x y, x ∈ M ∧ y ∈ M ∧ x ≠ y) ∧ (common A M).Nonempty := by
  refine ⟨fun _ => Set.univ, Set.univ,
    ⟨true, false, Set.mem_univ _, Set.mem_univ _, by decide⟩, ⟨(), ?_⟩⟩
  intro _ _
  exact Set.mem_univ ()

/-- The equivalence does not fill an empty intersection. -/
theorem may_be_empty :
    ∃ A : Unit → Set Unit, ∃ M : Set Unit,
      M.Nonempty ∧ common A M = ∅ := by
  refine ⟨fun _ => ∅, Set.univ, ⟨(), trivial⟩, ?_⟩
  ext a
  simp only [common, Set.mem_empty_iff_false, iff_false]
  intro ha
  exact ha () (Set.mem_univ _)

/-- Safety of a common action reaches `x0` only through membership in `M`. -/
theorem guarantee_at_true (A : X → Set U) (M : Set X) {x0 : X}
    (hx : x0 ∈ M) {a : U} (ha : a ∈ common A M) : a ∈ A x0 :=
  ha x0 hx

/-- A state outside the fibre is not covered by the common action. -/
theorem outside_not_covered :
    ∃ A : Bool → Set Bool, ∃ M : Set Bool, ∃ x0 a : Bool,
      x0 ∉ M ∧ a ∈ common A M ∧ a ∉ A x0 := by
  let A : Bool → Set Bool
    | true => {b | b = true}
    | false => ∅
  let M : Set Bool := {b | b = true}
  refine ⟨A, M, false, true, ?_, ?_, ?_⟩
  · intro h
    exact Bool.false_ne_true h
  · intro b hb
    subst hb
    rfl
  · simp [A]

end FocusStep
end CausalSpectrum

/-
The final machine.

A wish is a record. Love is not its output.
The machine offers a step only when the wish opened it,
every present consent contains it, and the next state
lies in the care set.

One address. A shared name does not copy that address
onto the rest of the fibre. A step taken at one state
does not count as consent at every state. If the
intersection is empty, the machine is silent.

Not proved:

* that love exists;
* that the addressed person returns it;
* that a wish produces a witness;
* that a sacrifice discharges anyone else's refusal;
* anything about the zeros of `ξ`.
-/

import CausalSeed.GoldenSphere

namespace CausalSpectrum
namespace LoveMachine

open GoldenSphere

variable {X Ω W N Person : Type*}

/-- A sphere with one address. The address is data.
The sphere does not derive it, and does not copy it. -/
structure Machine (X Ω W N Person : Type*) extends Sphere X Ω W N where
  addressed : Person

/-- The only step the machine may offer. -/
def offers (M : Machine X Ω W N Person) (w : W) (x : X) : Set X :=
  G M.toSphere w x

theorem offers_subset_care (M : Machine X Ω W N Person) (w : W) (x : X) :
    offers M w x ⊆ M.K :=
  G_subset_K M.toSphere w x

/-- A nonempty offer is a supplied witness, not a product of the wish. -/
theorem wish_is_not_the_witness (M : Machine X Ω W N Person) (w : W) (x : X) :
    (offers M w x).Nonempty ↔
      ∃ a, a ∈ M.I w x ∧ (∀ i, a ∈ M.C i x) ∧ M.F x a ∈ M.K := by
  simpa [offers, Set.Nonempty] using step_exists_iff M.toSphere w x

/-- Missing consent is silence. The definition does not fill it. -/
theorem refusal_is_silence (M : Machine X Ω W N Person) (w : W) (x : X)
    (i : N) (a : Ω) (ha : a ∉ M.C i x) :
    a ∉ admissible M.toSphere w x :=
  outside_consent_not_admissible M.toSphere w x i a ha

/-- Love addressed to one person is not a function of a name shared by all. -/
theorem addressed_love_is_not_a_function_of_the_name :
    ¬ ∃ g : Set.range (fun (_ : Bool) => ()) → Bool,
        ∀ x : Bool, g ⟨(), ⟨x, rfl⟩⟩ = x :=
  splitting_property_does_not_factor

/-- Two people can share a name while love holds for only one of them. -/
theorem one_address_does_not_fill_the_fibre :
    ∃ (O : Bool → Unit) (love : Bool → Prop) (p p' : Bool),
      O p = O p' ∧ p ≠ p' ∧ love p ∧ ¬ love p' := by
  refine ⟨fun _ => (), fun b => b = true, true, false, rfl, ?_, rfl, ?_⟩
  · decide
  · simp

/-- A step that is acceptable at one state need not be consent at every state.
Sacrifice does not replace a refusal. -/
theorem sacrifice_is_not_consent :
    ∃ C : Bool → Set Unit,
      (C true).Nonempty ∧ { a | ∀ x, a ∈ C x } = ∅ := by
  classical
  let C : Bool → Set Unit
    | true => Set.univ
    | false => ∅
  refine ⟨C, ⟨(), by simp [C]⟩, ?_⟩
  ext a
  constructor
  · intro ha
    exact (ha false).elim
  · intro ha
    exact ha.elim

/-- The machine does not identify love with this construction. -/
theorem machine_is_not_love : True := trivial

end LoveMachine
end CausalSpectrum

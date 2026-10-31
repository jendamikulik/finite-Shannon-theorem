/-
A recursive dream is still a dream.

`DreamStay.remains` says: if every step is admitted, care persists.
The hypothesis is not discharged by repeating the theorem.
A chooser is extra data: at every cared-for state it supplies an admission.
Given a chooser, the trajectory stays in care.
Without a chooser, a model may be cared for at the start and admit nothing.

Not proved:

* that a chooser exists for an arbitrary model;
* that the empty model is the only obstruction;
* that a dream of a dream is a world.
-/
import CausalSeed.RecordDream

namespace CausalSpectrum
namespace RecursiveDream

open DreamStay

/-- A recursion that always finds an admitted action.
This is an inhabitant, not a consequence of `remains`. -/
structure Chooser (X A : Type) where
  model : Model X A
  x0 : X
  cared : model.care x0
  choose : (x : X) → model.care x → {a : A // model.admit x a}

/-- The trajectory, carrying the care proof that the next choice needs. -/
def run {X A : Type} (C : Chooser X A) : (n : ℕ) → {x : X // C.model.care x}
  | 0 => ⟨C.x0, C.cared⟩
  | n + 1 =>
      let prev := run C n
      let a := C.choose prev.1 prev.2
      ⟨C.model.step prev.1 a.1, C.model.lands prev.1 a.1 a.2⟩

theorem stays {X A : Type} (C : Chooser X A) (n : ℕ) :
    C.model.care (run C n).1 :=
  (run C n).2

/-- Cared for at the start. No action exists, so nothing can be admitted. -/
def silent : Model Unit Empty where
  care := fun _ => True
  admit := fun _ a => a.elim
  step := fun _ a => a.elim
  lands := fun _ a _ => a.elim

theorem silent_cared : silent.care () := trivial

theorem no_chooser : ¬ Nonempty (Chooser Unit Empty) := by
  intro ⟨C⟩
  exact Empty.elim (C.choose C.x0 C.cared).1

/-- The paradox. Care at the origin does not produce the recursion
that would keep the dream going. `remains` still needs its hypothesis. -/
theorem paradox :
    silent.care () ∧ ¬ Nonempty (Chooser Unit Empty) :=
  ⟨silent_cared, no_chooser⟩

end RecursiveDream
end CausalSpectrum

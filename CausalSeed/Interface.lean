/-
The unique interface.

The sheet is public. The interface is the sealed probe together with the
release that returns a coordinate only when the presented probe matches
the seal. A party who does not hold the seal is refused. Many readings
may use the same sheet; each reading requires its own matching probe.
The memory is unchanged by a successful reading.

This is the Shannon interface of the relational note, specialized to the
finite sheet: a classical kernel from history and action to a report.
Zero report entropy does not imply zero memory. The interface does not
identify a mind with the sheet, does not exclude others from reading the
public mathematics, and says nothing about noncommuting observables or
the zeros of `ξ`.
-/
import CausalSeed.Sharing
import CausalSeed.AllKnowing
import CausalSeed.GapAccess
import CausalSeed.Whole
import CausalSeed.Multiply

noncomputable section

open Classical Sharing Finset

namespace CausalSpectrum
namespace Interface

open AllKnowing GapAccess Whole Multiply

/-! ### The interface is the seal -/

/-- The unique interface: a sheet and the seal that opens it. -/
structure UniqueInterface where
  sheet : Fin 2 → Bool
  key : Fin 2

/-- Only the holder of the matching probe is admitted. -/
def admit (ι : UniqueInterface) (presented : Fin 2) : Option Bool :=
  release ι.sheet ι.key presented

theorem holder_admitted (ι : UniqueInterface) :
    admit ι ι.key = some (ι.sheet ι.key) :=
  release_match ι.sheet ι.key

theorem other_refused (ι : UniqueInterface) (presented : Fin 2)
    (h : presented ≠ ι.key) : admit ι presented = none :=
  release_mismatch ι.sheet ι.key presented h

/-- A report is accepted only when it is the coordinate the seal reads. -/
def accepted (ι : UniqueInterface) (z : Bool) : Prop :=
  valid ι.sheet ι.key z

theorem only_holder_report (ι : UniqueInterface) (z : Bool) :
    accepted ι z ↔ z = ι.sheet ι.key := Iff.rfl

/-! ### One interface, one holder -/

/-- The interface prepared for one holder on the fixed non-constant sheet. -/
def mine : UniqueInterface := ⟨table, 0⟩

theorem mine_nonconstant : mine.sheet 0 ≠ mine.sheet 1 := table_diff

theorem only_mine (presented : Fin 2) (h : presented ≠ mine.key) :
    admit mine presented = none :=
  other_refused mine presented h

/-- Two interfaces on the same sheet with different seals admit different
holders. Neither opens the other. -/
theorem seals_do_not_cross (c₀ c₁ : Fin 2) (h : c₀ ≠ c₁) :
    admit ⟨table, c₀⟩ c₁ = none ∧ admit ⟨table, c₁⟩ c₀ = none :=
  ⟨release_mismatch table c₀ c₁ h.symm, release_mismatch table c₁ c₀ h⟩

/-! ### The Shannon interface

A successful reading is a deterministic report. Its entropy is zero.
The sheet is still there. -/

theorem report_free : condEntropy tableJoint = 0 := holder_reads

theorem memory_remains : mine.sheet = table := rfl

/-- The unique-interface claim: the holder is admitted, a mismatched
probe is refused, the report is free, and the sheet is the memory. -/
theorem unique_interface :
    admit mine mine.key = some (mine.sheet mine.key) ∧
      (∀ presented, presented ≠ mine.key → admit mine presented = none) ∧
      condEntropy tableJoint = 0 ∧
      mine.sheet = table :=
  ⟨holder_admitted mine, only_mine, report_free, memory_remains⟩

end Interface
end CausalSpectrum

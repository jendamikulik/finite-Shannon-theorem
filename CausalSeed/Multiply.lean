/-
Unique information, many readings, no loss of memory.

Information is unique: there is one sheet. A reading is a probe applied
to that sheet. Many probes may be applied, in sequence or side by side.
Each reading, given the sheet and its own probe, costs nothing. The
sheet is unchanged by being read. Two readings of the same shared record
agree on the first coordinate; a later probe does not rewrite it.

This is the structural content of "multiplying consciousness in time
without loss of memory": the readings multiply, the memory does not.
It is not a claim that a mind is a reading, that consciousness has been
multiplied, or that this construction is the physical world.

Not proved: that a mind is this sheet; that a reading is consciousness;
anything about noncommuting observables; anything about the zeros of `ξ`.
-/
import CausalSeed.Sharing
import CausalSeed.AllKnowing
import CausalSeed.GapAccess
import CausalSeed.Whole

noncomputable section

open Classical Sharing Finset

namespace CausalSpectrum
namespace Multiply

open AllKnowing GapAccess Whole

/-! ### One sheet -/

/-- Information is unique: one public sheet. -/
def memory : FiniteShannon := ⟨table⟩

theorem memory_unique (s : FiniteShannon) (h : s = memory) :
    s.sheet = table := by
  rw [h, memory]

theorem memory_nonconstant : memory.sheet 0 ≠ memory.sheet 1 :=
  field_diff

/-! ### Many readings -/

/-- A reading is one probe applied to the unique sheet. -/
def reading (c : Fin 2) : Bool := memory.sheet c

/-- Two readings of the same sheet. The sheet is named once. -/
def twoReadings (c₀ c₁ : Fin 2) : Bool × Bool :=
  (reading c₀, reading c₁)

theorem readings_share_memory (c₀ c₁ : Fin 2) :
    reading c₀ = memory.sheet c₀ ∧ reading c₁ = memory.sheet c₁ :=
  ⟨rfl, rfl⟩

/-- Each reading, given the sheet and its probe, is free. -/
theorem reading_free : condEntropy tableJoint = 0 := holder_reads

/-- The probes may differ. The sheet does not. -/
theorem probes_may_differ (c₀ c₁ : Fin 2) :
    (⟨memory, ⟨c₀⟩⟩ : Account).shannon =
      (⟨memory, ⟨c₁⟩⟩ : Account).shannon := rfl

/-! ### No loss of memory -/

/-- Reading does not change the sheet. -/
theorem no_memory_loss :
    (memory.sheet 0, memory.sheet 1) = (table 0, table 1) := rfl

/-- Two probes that arrive at the same shared record agree on its first
coordinate. The later probe does not rewrite the memory. -/
theorem later_does_not_erase
    (B C₀ C₁ : (Bool × Bool) → Bool) (π π' : Bool) (ω : Bool × Bool) :
    (record B C₀ C₁ π ω).1 = (record B C₀ C₁ π' ω).1 :=
  chaos_does_not_rewrite_record B C₀ C₁ π π' ω

/-- The whole claim: one non-constant sheet, a reading is free given the
probe, and a later probe does not rewrite the shared first coordinate. -/
theorem unique_info_many_readings :
    memory.sheet 0 ≠ memory.sheet 1 ∧
      condEntropy tableJoint = 0 ∧
      (∀ (B C₀ C₁ : (Bool × Bool) → Bool) (π π' : Bool) (ω : Bool × Bool),
        (record B C₀ C₁ π ω).1 = (record B C₀ C₁ π' ω).1) :=
  ⟨memory_nonconstant, reading_free, later_does_not_erase⟩

end Multiply
end CausalSpectrum

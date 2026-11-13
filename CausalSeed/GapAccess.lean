/-
Exclusive access to the gap.

The sheet `N` is public. The probe `C` is private. A seal fixes `C`
before the readout. The answer `Z = N(C)` is released only with a
matching probe. An outsider who sees only the sheet keeps the gap
whenever the sheet is non-constant on the support of `C`. A claimed
answer that is not `N(C)` for the sealed probe is not a valid reading.

Structural analogy, not a physical claim. The Higgs field has a vacuum
expectation present everywhere: that is the public sheet. A particle
acquires its mass only by coupling to that field: that is the private
probe. The boson is the excitation detected when the probe is applied:
`Z = N(C)`. In the diagram the central `H` is the fixed sheet; the
incoming `γ` lines are probes. An observer who sees only the field does
not read the excitation. This module does not say that the information
gap is the Higgs mechanism, nor anything about particle masses, nor
anything about the zeros of `ξ`.

Not proved: that a mind is this sheet; that a commitment hides `C` from
a computationally bounded adversary; that the Higgs field is this
construction.
-/
import CausalSeed.Sharing
import CausalSeed.AllKnowing

noncomputable section

open Classical Sharing Finset

namespace CausalSpectrum
namespace GapAccess

open AllKnowing

/-! ### The field and the probe

The sheet is public, like a vacuum expectation present everywhere.
The probe is private. The seal is the probe index, held by the asker
and not published. -/

/-- The public sheet. Its two entries differ, so one probe bit remains. -/
def field : Fin 2 → Bool := table

theorem field_diff : field 0 ≠ field 1 := table_diff

/-- The seal fixes the probe before the readout. In this finite model
the probeSeal is the probe itself; the protocol does not publish it. -/
def probeSeal (c : Fin 2) : Fin 2 := c

/-- Exclusive release. The coordinate is returned only when the
presented probe matches the probeSeal. Otherwise the reading is refused. -/
def release (sheet : Fin 2 → Bool) (sealedProbe presented : Fin 2) : Option Bool :=
  if presented = sealedProbe then some (sheet presented) else none

theorem release_match (sheet : Fin 2 → Bool) (c : Fin 2) :
    release sheet c c = some (sheet c) := by
  simp [release]

theorem release_mismatch (sheet : Fin 2 → Bool) (c c' : Fin 2) (h : c' ≠ c) :
    release sheet c c' = none := by
  simp [release, h]

/-- A claimed answer is a valid reading of this sheet only when it is
the coordinate the sealed probe reads. -/
def valid (sheet : Fin 2 → Bool) (c : Fin 2) (z : Bool) : Prop :=
  z = sheet c

theorem valid_iff_release (sheet : Fin 2 → Bool) (c : Fin 2) (z : Bool) :
    valid sheet c z ↔ release sheet c c = some z := by
  simp [valid, release, eq_comm]

theorem invalid_rejected (sheet : Fin 2 → Bool) (c : Fin 2) (z : Bool)
    (hz : z ≠ sheet c) : ¬ valid sheet c z :=
  fun h => hz h

/-! ### Holder and outsider

The joint of a fair probe and the bit it reads on the fixed sheet is
`tableJoint` from `AllKnowing`. With the probe the conditional entropy
is zero. Without it the missing bit is one. -/

/-- With the matching probe the answer is free. `H(Z | N, C) = 0`. -/
theorem holder_reads : condEntropy tableJoint = 0 := tableJoint_cond

/-- The public sheet does not contain the probe. On this fixed sheet
the probe is an independent fair bit, so `H(C) = 1`. -/
theorem probe_not_in_field : H coin = 1 := coin_entropy

/-- An outsider who sees only the sheet keeps exactly one bit.
`H(Z | N) - H(Z | N, C) = 1` for this non-constant sheet. -/
theorem outsider_gap :
    H (marginal tableJoint) - condEntropy tableJoint = 1 := table_gap

/-- The three claims of exclusive access, for this sheet. -/
theorem exclusive_access :
    condEntropy tableJoint = 0 ∧
      H coin = 1 ∧
      H (marginal tableJoint) - condEntropy tableJoint = 1 :=
  ⟨holder_reads, probe_not_in_field, outsider_gap⟩

/-! ### The shared past is not rewritten by the probe

A later probe may choose either coordinate. The first recorded
coordinate of a shared experiment stays fixed. This is the one-seed
fact, restated for the two probes that arrive at the central sheet. -/

/-- Two probes may arrive. The first recorded coordinate is the same
for both. -/
theorem probes_share_first
    (B C₀ C₁ : (Bool × Bool) → Bool) (π π' : Bool) (ω : Bool × Bool) :
    (record B C₀ C₁ π ω).1 = (record B C₀ C₁ π' ω).1 :=
  first_shared B C₀ C₁ π π' ω

end GapAccess
end CausalSpectrum

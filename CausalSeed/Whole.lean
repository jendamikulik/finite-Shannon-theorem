/-
The whole: finite Shannon and fundamental chaos.

The finite Shannon part is the sheet and everything determined by it.
A coordinate of the sheet, and the answer once a probe is supplied, cost
nothing more than the sheet. The fundamental chaos is the unasked
question: it is not a coordinate of the sheet, and the sheet does not
shrink it. The whole is the pair of the two. Supplying the chaos to the
sheet yields the answer for free. The chaos does not rewrite the first
recorded coordinate of a shared experiment.

Not proved: that a mind is this pair; that the chaos is free will; that
this construction is the physical world; anything about noncommuting
observables; anything about the zeros of `ξ`.
-/
import CausalSeed.Sharing
import CausalSeed.AllKnowing
import CausalSeed.GapAccess
import Mathlib.Data.Set.Prod

noncomputable section

open Classical Sharing Finset

namespace CausalSpectrum
namespace Whole

open AllKnowing GapAccess

/-! ### The two parts -/

/-- Finite Shannon: the public sheet. Everything it determines is a
function of it. -/
structure FiniteShannon where
  sheet : Fin 2 → Bool

/-- Fundamental chaos: the unasked probe. It is not a coordinate of the
sheet. -/
structure FundamentalChaos where
  probe : Fin 2

/-- The whole is the pair. -/
structure Account where
  shannon : FiniteShannon
  chaos : FundamentalChaos

/-- The set of finite Shannon sheets on two bits. -/
def finiteShannonSet : Set (Fin 2 → Bool) := Set.univ

/-- The set of fundamental chaos probes on two bits. -/
def fundamentalChaosSet : Set (Fin 2) := Set.univ

/-- The whole as a set of pairs. -/
def wholeSet : Set ((Fin 2 → Bool) × Fin 2) := Set.univ

theorem whole_is_product :
    wholeSet = finiteShannonSet ×ˢ fundamentalChaosSet := by
  ext p
  simp [wholeSet, finiteShannonSet, fundamentalChaosSet]

/-! ### What each part costs -/

/-- A coordinate of the sheet is free given the sheet. -/
theorem shannon_coordinate_free (s : FiniteShannon) (q : Fin 2) :
    thought q s.sheet = s.sheet q := rfl

/-- The chaos is not determined by a fixed sheet. On the non-constant
sheet the missing bit is one, and the probe entropy is one. -/
theorem chaos_not_in_shannon :
    H coin = 1 ∧
      H (marginal tableJoint) - condEntropy tableJoint = 1 :=
  ⟨coin_entropy, table_gap⟩

/-- Supplying the chaos to the sheet yields the answer. -/
def readout (w : Account) : Bool := w.shannon.sheet w.chaos.probe

theorem readout_is_release (w : Account) :
    release w.shannon.sheet w.chaos.probe w.chaos.probe =
      some (readout w) := by
  simp [release, readout]

/-- With both parts the answer is free. Without the chaos the gap
remains. -/
theorem whole_accounts :
    condEntropy tableJoint = 0 ∧
      H coin = 1 ∧
      H (marginal tableJoint) - condEntropy tableJoint = 1 :=
  exclusive_access

/-! ### The chaos does not rewrite the Shannon part -/

/-- Two wholes that share the sheet share every coordinate of it.
The chaos may differ; the sheet does not. -/
theorem chaos_does_not_rewrite (w w' : Account)
    (h : w.shannon = w'.shannon) (q : Fin 2) :
    w.shannon.sheet q = w'.shannon.sheet q := by
  rw [h]

/-- Two probes that arrive at the same shared record do not change its
first coordinate. -/
theorem chaos_does_not_rewrite_record
    (B C₀ C₁ : (Bool × Bool) → Bool) (π π' : Bool) (ω : Bool × Bool) :
    (record B C₀ C₁ π ω).1 = (record B C₀ C₁ π' ω).1 :=
  probes_share_first B C₀ C₁ π π' ω

end Whole
end CausalSpectrum

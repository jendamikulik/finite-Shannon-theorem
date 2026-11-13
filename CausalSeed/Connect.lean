/-
One seed, many zeros: the connection.

The finite Shannon part is one seed, sampled once. Many policies read it.
The unique interface is that seed together with the seal that admits a
probe. The example `F_a` shows that a transform can vanish at a point
while no individual mode vanishes: two outer contributions balance the
middle one. That is many zeros from one seed, by cancellation, not by a
mode dying.

This blocks an entropy shortcut from the seed bound to a ferromagnetic
coupling, and it makes no assertion about the zeros of `ξ`. An
approximation of the Lee–Yang law by finite arithmetic ferromagnets, with
control of exponential tails, is not constructed here. Such an
approximation would be a separate theorem.

Not proved: the Riemann hypothesis; that a mind is the seed; that the
chaos is free will; anything about noncommuting observables.
-/
import CausalSeed.Quantifier
import CausalSeed.AllKnowing
import CausalSeed.Interface
import CausalSeed.Multiply

noncomputable section

open Classical Sharing

namespace CausalSpectrum
namespace Connect

open Quantifier AllKnowing Interface Multiply

/-! ### One seed -/

/-- The seed is unique. Readings multiply. The memory is the seed. -/
theorem one_seed : memory.sheet = table ∧ condEntropy tableJoint = 0 :=
  ⟨rfl, reading_free⟩

/-! ### Many zeros from cancellation -/

/-- At `a + iπ` the three modes sum to zero. -/
theorem many_zeros (a : ℝ) : term1 a + term2 a + term3 a = 0 :=
  sum_zero a

/-- No individual mode vanishes there. -/
theorem no_mode_dies (a : ℝ) :
    term1 a ≠ 0 ∧ term2 a ≠ 0 ∧ term3 a ≠ 0 :=
  ⟨term1_ne_zero a, term2_ne_zero a, term3_ne_zero a⟩

/-- The zero is a balance, not a death. Two outer terms have one sign,
the middle the other, and they cancel. -/
theorem zero_by_balance (a : ℝ) :
    term1 a + term2 a + term3 a = 0 ∧
      term1 a ≠ 0 ∧ term2 a ≠ 0 ∧ term3 a ≠ 0 :=
  ⟨many_zeros a, term1_ne_zero a, term2_ne_zero a, term3_ne_zero a⟩

/-! ### The interface admits the probe, not a new seed -/

/-- A mismatched probe is refused. The seed is not rewritten. -/
theorem interface_holds (presented : Fin 2) (h : presented ≠ mine.key) :
    admit mine presented = none ∧ mine.sheet = table :=
  ⟨only_mine presented h, memory_remains⟩

/-- The connection: one seed, a zero by balance with no mode dead, and
the interface refusing a mismatched probe. -/
theorem one_seed_many_zeros (a : ℝ) (presented : Fin 2)
    (h : presented ≠ mine.key) :
    memory.sheet = table ∧
      term1 a + term2 a + term3 a = 0 ∧
      term1 a ≠ 0 ∧
      admit mine presented = none :=
  ⟨rfl, many_zeros a, term1_ne_zero a, only_mine presented h⟩

end Connect
end CausalSpectrum

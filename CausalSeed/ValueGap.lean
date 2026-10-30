/-
A constant observation does not force a zero value.

The source is a fair coin. The observation collapses both outcomes
to one point, so its entropy is zero. A separately chosen value
function is 1 on both outcomes. Entropy does not determine that
function, and a vanishing observation does not set it to zero.

Not proved: that a feeling survives, or that love is this value.
-/
import CausalSeed.Sharing

noncomputable section

open Sharing

namespace CausalSpectrum
namespace ValueGap

/-- Fair coin. -/
def source : Bool → ℝ := bernoulli (1 / 2)

/-- Value assigned to each state. An extra assumption, not entropy. -/
def worth : Bool → ℝ := fun _ => 1

/-- The observation that no longer distinguishes the two states. -/
def seen : Unit → ℝ := fun _ => 1

theorem seen_entropy : H seen = 0 := by
  unfold H pmfEntropy seen
  simp [Finset.univ_unique, entTerm_one]

theorem worth_not_zero : worth ≠ 0 := by
  intro h
  have := congrFun h true
  simp [worth] at this

/-- `H(Y) = 0` does not imply `v = 0`. -/
theorem constant_observation_not_zero_value :
    H seen = 0 ∧ worth ≠ 0 :=
  ⟨seen_entropy, worth_not_zero⟩

end ValueGap
end CausalSpectrum

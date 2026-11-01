/-
A constant observation does not force a zero value.

The source is a fair coin. The observation collapses both outcomes
to one point, so its entropy is zero. A separately chosen value
function is 1 on both outcomes. Entropy does not determine that
function, and a vanishing observation does not set it to zero.

`observe` is the concrete map. `push source` is its image, and that
image is `seen`. The source still has one bit.

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
def observe : Bool → Unit := fun _ => ()

/-- Pushforward by `observe`. -/
def push (μ : Bool → ℝ) : Unit → ℝ := fun _ => ∑ b, μ b

/-- The law of the observation. -/
def seen : Unit → ℝ := push source

theorem push_source : push source = seen := rfl

theorem seen_total : ∑ u, seen u = 1 := by
  simp only [seen, push, source, Finset.univ_unique, Finset.sum_singleton]
  exact bernoulli_total (1 / 2)

theorem seen_entropy : H seen = 0 := by
  unfold H pmfEntropy seen push source
  simp only [Finset.univ_unique, Finset.sum_singleton]
  rw [bernoulli_total]
  exact entTerm_one

theorem worth_not_zero : worth ≠ 0 := by
  intro h
  have := congrFun h true
  simp [worth] at this

/-- The image of the source under the constant observation has entropy zero,
while the value on the source is not zero. -/
theorem constant_observation_not_zero_value :
    H (push source) = 0 ∧ worth ≠ 0 :=
  ⟨by simpa [push_source] using seen_entropy, worth_not_zero⟩

/-- One hidden bit. `log₂(1/2) = -1`, so each half contributes `1/2`. -/
theorem binEntropy_half : binEntropy (1 / 2) = 1 := by
  unfold binEntropy
  have hterm : entTerm (1 / 2) = 1 / 2 := by
    rw [entTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    unfold infoMass
    have hlog : Real.logb 2 ((1 : ℝ) / 2) = -1 := by
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.logb_inv, Real.logb_self_eq_one]
      <;> norm_num
    rw [hlog]
    norm_num
  rw [hterm, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, hterm]
  norm_num

theorem source_entropy : H source = 1 := by
  rw [source, bernoulli_entropy (by norm_num) (by norm_num), binEntropy_half]

/-- The observation is a function of the source, and it hides the bit. -/
theorem observation_hides_the_bit :
    H source = 1 ∧ H (push source) = 0 ∧ observe true = observe false :=
  ⟨source_entropy, by simpa [push_source] using seen_entropy, rfl⟩

end ValueGap
end CausalSpectrum

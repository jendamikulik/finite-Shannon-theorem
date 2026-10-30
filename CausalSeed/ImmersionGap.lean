/-
Observer uncertainty from a non-injective observation.

What is proved, with no sorry:

* a Bernoulli prior on a two-point fiber, pushed by a deterministic
  evolution that separates the fiber, gives a future of binary entropy;
* the joint of (state, future) has conditional entropy zero, because
  the future is a function of the state
  (`Sharing.condEntropy_of_dependent`).

What is not proved:

* that an immersion creates randomness;
* that every evolution separates the fiber;
* a stochastic mechanism turning the identification into a kernel.

The randomness in the prediction is the prior uncertainty about which
point of the fiber occurred. The evolution reveals it.

Encoding: `Bool` is the fiber and the future. `true` is the plus point
and its image; `false` is the minus point and its image. The evolution
that separates the fiber is the identity on this encoding.
-/
import CausalSeed.Sharing

noncomputable section

open Sharing

namespace CausalSpectrum
namespace ImmersionGap

/-- Separating evolution on the encoded fiber. -/
def evolve (x : Bool) : Bool := x

/-- Joint: future equals the state. Masses are the Bernoulli prior. -/
def joint (p : ℝ) : Bool × Bool → ℝ
  | (x, y) => if x = y then bernoulli p x else 0

theorem joint_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    ∀ z : Bool × Bool, 0 ≤ joint p z := by
  intro z
  rcases z with ⟨x, y⟩
  dsimp [joint]
  split_ifs
  · exact bernoulli_nonneg h0 h1 x
  · exact le_refl 0

theorem joint_off {p : ℝ} (x y : Bool) (hy : y ≠ x) :
    joint p (x, y) = 0 := by
  have hxy : x ≠ y := fun h => hy h.symm
  simp [joint, hxy]

theorem entropy_given_state {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    condEntropy (joint p) = 0 :=
  condEntropy_of_dependent (joint_nonneg h0 h1) evolve
    (fun x y hy => joint_off x y hy)

/-- The future law is the Bernoulli prior, hence has binary entropy. -/
theorem entropy_of_future {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    H (bernoulli p) = binEntropy p :=
  bernoulli_entropy h0 h1

/-- Observer gap: binary entropy from the unresolved fiber, zero given the state. -/
theorem observer_gap {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    H (bernoulli p) = binEntropy p ∧ condEntropy (joint p) = 0 :=
  ⟨entropy_of_future h0 h1, entropy_given_state h0 h1⟩

end ImmersionGap
end CausalSpectrum

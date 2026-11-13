/-
The palm and the sketch.

On the palm: `∀ x : ℝ, 1/x = 0 → x = 0`. In this library division by zero
is zero, so `1/0 = 0`, and for `x ≠ 0` one has `1/x ≠ 0`. The antecedent
is true only at zero, where the consequent holds. The implication is
true at every real. This is a convention plus a vacuous case, not a fact
about a reciprocal that vanishes.

On the sketch: a path crosses a vertical line, and `π` is marked. That
height is where `F_a` balances to zero. The zero sits at `a + iπ`. No
mode dies there. The mark `π` is the height of the balance, not a new
seed.

`off e` is the scale step. For a zero of multiplicity `m`, one layer
`r < |s-ρ| < e r` costs `m²/2` in the normalized quadratic account, up
to an error `O(r)`. The sketch does not compute that cost.

Not proved: anything about the zeros of `ξ`; that the path on the sketch
is a trajectory of `η`; that the palm statement is about physics.
-/
import CausalSeed.Quantifier
import CausalSeed.Connect

noncomputable section

open Classical

namespace CausalSpectrum
namespace OffE

open Quantifier Connect

/-! ### The palm -/

/-- In this library, division by zero is zero. -/
theorem one_div_zero : (1 : ℝ) / 0 = 0 := by
  simp

/-- Away from zero the reciprocal does not vanish. -/
theorem one_div_ne_zero_of_ne {x : ℝ} (hx : x ≠ 0) : (1 : ℝ) / x ≠ 0 :=
  one_div_ne_zero hx

/-- The palm statement is true. -/
theorem palm : ∀ x : ℝ, (1 : ℝ) / x = 0 → x = 0 :=
  fun _ h => eq_zero_of_one_div_eq_zero h

/-- It is true, and it is true because the only place the antecedent
holds is zero. -/
theorem palm_true : (∀ x : ℝ, (1 : ℝ) / x = 0 → x = 0) := palm

/-! ### The sketch: π is the height of the balance -/

/-- The balance zero of `F_a` sits at height `π`. -/
theorem sketch_pi (a : ℝ) : term1 a + term2 a + term3 a = 0 :=
  many_zeros a

/-- At that height no mode has died. -/
theorem sketch_no_death (a : ℝ) :
    term1 a ≠ 0 ∧ term2 a ≠ 0 ∧ term3 a ≠ 0 :=
  no_mode_dies a

/-- The two additions, together. -/
theorem palm_and_sketch (a : ℝ) :
    (∀ x : ℝ, (1 : ℝ) / x = 0 → x = 0) ∧
      term1 a + term2 a + term3 a = 0 ∧
      term1 a ≠ 0 :=
  ⟨palm, sketch_pi a, term1_ne_zero a⟩

end OffE
end CausalSpectrum

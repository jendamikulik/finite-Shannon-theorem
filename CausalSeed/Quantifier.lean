/-
The quantifier.

For each real `a` the function
`F_a(z) = (1/2) cosh z + cosh(a) cosh(2z) + (1/2) cosh(3z)`
is built from `a`. At `z = a + iπ` its three terms are real, with signs
`−, +, −`, and none of them is zero. Their sum is zero. If `0 < a < 1/2`,
that zero lies at distance `a` from the axis `Re = 0`, strictly inside the
strip.

The middle weight is `cosh a`. It is not the same number at two different
distances. One triple of weights does not serve the whole family.

Not proved: that the single kernel of the Riemann xi function excludes such
a zero. A family indexed by `a` is not one fixed kernel.
-/

import CausalSeed.Modes

noncomputable section

namespace CausalSpectrum
namespace Quantifier

def pt (a : ℝ) : ℂ := (a : ℂ) + (Real.pi : ℂ) * Complex.I

def term1 (a : ℝ) : ℂ := (1 / 2) * Complex.cosh (pt a)

def term2 (a : ℝ) : ℂ := (Real.cosh a : ℂ) * Complex.cosh (2 * pt a)

def term3 (a : ℝ) : ℂ := (1 / 2) * Complex.cosh (3 * pt a)

theorem first_factor (a : ℝ) :
    Complex.cosh (pt a) = -((Real.cosh a : ℂ)) := by
  have h := Modes.pair_cancels a
  rw [show (a : ℂ) + (Real.pi : ℂ) * Complex.I = pt a from rfl] at h
  exact (eq_neg_iff_add_eq_zero).mpr h

theorem term1_value (a : ℝ) :
    term1 a = ((-(1 / 2) * Real.cosh a : ℝ) : ℂ) := by
  unfold term1
  rw [first_factor]
  push_cast
  ring

theorem term2_value (a : ℝ) :
    term2 a = ((Real.cosh a * Real.cosh (2 * a) : ℝ) : ℂ) := by
  unfold term2 pt
  have harg : 2 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I) =
      ((2 * a : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    simp [Complex.ofReal_mul]
    ring
  rw [harg, Modes.cosh_line, Modes.cos_two_pi, Modes.sin_two_pi]
  push_cast
  ring

theorem term3_value (a : ℝ) :
    term3 a = ((-(1 / 2) * Real.cosh (3 * a) : ℝ) : ℂ) := by
  unfold term3 pt
  have harg : 3 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I) =
      ((3 * a : ℝ) : ℂ) + ((3 * Real.pi : ℝ) : ℂ) * Complex.I := by
    simp [Complex.ofReal_mul]
    ring
  rw [harg, Modes.cosh_line, Modes.cos_three_pi, Modes.sin_three_pi]
  push_cast
  ring

theorem term1_re (a : ℝ) : (term1 a).re = -(1 / 2) * Real.cosh a := by
  rw [term1_value, Complex.ofReal_re]

theorem term2_re (a : ℝ) : (term2 a).re = Real.cosh a * Real.cosh (2 * a) := by
  rw [term2_value, Complex.ofReal_re]

theorem term3_re (a : ℝ) : (term3 a).re = -(1 / 2) * Real.cosh (3 * a) := by
  rw [term3_value, Complex.ofReal_re]

theorem term1_neg (a : ℝ) : (term1 a).re < 0 := by
  rw [term1_re]
  exact mul_neg_of_neg_of_pos (by norm_num : -(1 / 2 : ℝ) < 0) (Real.cosh_pos a)

theorem term2_pos (a : ℝ) : 0 < (term2 a).re := by
  rw [term2_re]
  exact mul_pos (Real.cosh_pos a) (Real.cosh_pos (2 * a))

theorem term3_neg (a : ℝ) : (term3 a).re < 0 := by
  rw [term3_re]
  exact mul_neg_of_neg_of_pos (by norm_num : -(1 / 2 : ℝ) < 0) (Real.cosh_pos (3 * a))

theorem term1_ne_zero (a : ℝ) : term1 a ≠ 0 := by
  intro h
  have : (term1 a).re = 0 := by simp [h]
  linarith [term1_neg a]

theorem term2_ne_zero (a : ℝ) : term2 a ≠ 0 := by
  intro h
  have : (term2 a).re = 0 := by simp [h]
  linarith [term2_pos a]

theorem term3_ne_zero (a : ℝ) : term3 a ≠ 0 := by
  intro h
  have : (term3 a).re = 0 := by simp [h]
  linarith [term3_neg a]

theorem sum_zero (a : ℝ) : term1 a + term2 a + term3 a = 0 := by
  simpa [term1, term2, term3, pt] using Modes.three_modes_vanish a

theorem real_part (a : ℝ) : (pt a).re = a := by
  simp [pt, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im]

/-- For every prescribed distance inside the strip, some positive-weight sum cancels. -/
theorem prescribed_distance (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1 / 2) :
    term1 a + term2 a + term3 a = 0 ∧
      (pt a).re = a ∧
      0 < (pt a).re ∧ (pt a).re < 1 / 2 ∧
      (term1 a).re < 0 ∧ 0 < (term2 a).re ∧ (term3 a).re < 0 ∧
      term1 a ≠ 0 ∧ term2 a ≠ 0 ∧ term3 a ≠ 0 ∧
      Complex.cosh (pt a) ≠ 0 ∧
      Complex.cosh (2 * pt a) ≠ 0 ∧
      Complex.cosh (3 * pt a) ≠ 0 := by
  refine ⟨sum_zero a, real_part a, ?_, ?_, term1_neg a, term2_pos a, term3_neg a,
    term1_ne_zero a, term2_ne_zero a, term3_ne_zero a, ?_⟩
  · rw [real_part]; exact ha0
  · rw [real_part]; exact ha1
  · simpa [pt] using Modes.modes_alive a

/-- The middle weight changes with the distance. One triple is not the whole family. -/
theorem weight_depends (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    Real.cosh a ≠ Real.cosh b := by
  intro h
  exact hab (Real.cosh_strictMonoOn.injOn ha hb h)

end Quantifier
end CausalSpectrum

end

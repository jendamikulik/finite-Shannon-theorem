/-
One mode, and then several.

A single pair `cosh(u(x + it))` is two opposite phases with weights `e^{ux}` and
`e^{-ux}`. Off the axis the weights differ, and the modulus cannot vanish:

  `|cosh(u(x + it))|² = sinh²(ux) + cos²(ut)`.

A positive sum of such modes can still vanish. `cosh z + cosh a` is zero at
`a + iπ`, and multiplying by `cosh(2z)` rewrites that zero as a positive
combination of `cosh z`, `cosh(2z)` and `cosh(3z)`, none of which is zero
there. Positivity of the weights does not stop different modes from
cancelling each other.

Proved, with no sorry: the one-mode identity and the strict floor
`|sinh(ux)|`; the three-mode cancellation with positive coefficients.

Not proved: the Riemann hypothesis, positivity of Riemann's kernel, or any
special property of that kernel which would forbid the cancellation. For the
genuine `ξ`, horizontal strict increase of the modulus on `σ > 1/2` is not
an intermediate step. Sondow and Dumitrescu proved it equivalent to the
hypothesis.
-/

import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

noncomputable section

namespace CausalSpectrum
namespace Modes

theorem cosh_line (x y : ℝ) :
    Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I) =
      ((Real.cosh x * Real.cos y : ℝ) : ℂ) +
        ((Real.sinh x * Real.sin y : ℝ) : ℂ) * Complex.I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp [Complex.ofReal_cosh, Complex.ofReal_sinh, Complex.ofReal_cos, Complex.ofReal_sin]
  ring

theorem normSq_line (x y : ℝ) :
    Complex.normSq (Complex.cosh ((x : ℂ) + (y : ℂ) * Complex.I)) =
      (Real.cosh x * Real.cos y) ^ 2 + (Real.sinh x * Real.sin y) ^ 2 := by
  rw [cosh_line, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_I_re, Complex.mul_I_im, mul_zero, add_zero, zero_mul, sub_zero]
  ring

theorem one_mode (u x t : ℝ) :
    Complex.normSq (Complex.cosh (u * ((x : ℂ) + (t : ℂ) * Complex.I))) =
      Real.sinh (u * x) ^ 2 + Real.cos (u * t) ^ 2 := by
  have harg : u * ((x : ℂ) + (t : ℂ) * Complex.I) =
      ((u * x : ℝ) : ℂ) + ((u * t : ℝ) : ℂ) * Complex.I := by
    simp [Complex.ofReal_mul]
    ring
  rw [harg, normSq_line]
  have htrig : Real.sin (u * t) ^ 2 = 1 - Real.cos (u * t) ^ 2 := by
    have h := Real.sin_sq_add_cos_sq (u * t)
    linarith
  have hhyp : Real.cosh (u * x) ^ 2 - Real.sinh (u * x) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq (u * x)
  calc
    (Real.cosh (u * x) * Real.cos (u * t)) ^ 2
        + (Real.sinh (u * x) * Real.sin (u * t)) ^ 2
      = Real.cosh (u * x) ^ 2 * Real.cos (u * t) ^ 2
        + Real.sinh (u * x) ^ 2 * Real.sin (u * t) ^ 2 := by ring
    _ = Real.cosh (u * x) ^ 2 * Real.cos (u * t) ^ 2
        + Real.sinh (u * x) ^ 2 * (1 - Real.cos (u * t) ^ 2) := by rw [htrig]
    _ = Real.sinh (u * x) ^ 2
        + Real.cos (u * t) ^ 2 * (Real.cosh (u * x) ^ 2 - Real.sinh (u * x) ^ 2) := by ring
    _ = Real.sinh (u * x) ^ 2 + Real.cos (u * t) ^ 2 * 1 := by rw [hhyp]
    _ = Real.sinh (u * x) ^ 2 + Real.cos (u * t) ^ 2 := by ring

/-- Off the axis the floor is `|sinh(ux)|`, not zero. -/
theorem one_mode_floor (u x t : ℝ) :
    Real.sinh (u * x) ^ 2 ≤
      Complex.normSq (Complex.cosh (u * ((x : ℂ) + (t : ℂ) * Complex.I))) := by
  rw [one_mode]
  have : 0 ≤ Real.cos (u * t) ^ 2 := sq_nonneg _
  linarith

theorem one_mode_alive (u x t : ℝ) (hu : u ≠ 0) (hx : x ≠ 0) :
    Complex.cosh (u * ((x : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
  intro hzero
  have hsq : Complex.normSq (Complex.cosh (u * ((x : ℂ) + (t : ℂ) * Complex.I))) = 0 := by
    rw [hzero, Complex.normSq_zero]
  rw [one_mode] at hsq
  have hsh : Real.sinh (u * x) = 0 := by
    have hsh2 : 0 ≤ Real.sinh (u * x) ^ 2 := sq_nonneg _
    have hcos : 0 ≤ Real.cos (u * t) ^ 2 := sq_nonneg _
    have : Real.sinh (u * x) ^ 2 = 0 := by linarith
    exact sq_eq_zero_iff.mp this
  have hux : u * x = 0 := Real.sinh_eq_zero.mp hsh
  exact mul_ne_zero hu hx hux

theorem pair_cancels (a : ℝ) :
    Complex.cosh ((a : ℂ) + (Real.pi : ℂ) * Complex.I) + (Real.cosh a : ℂ) = 0 := by
  rw [cosh_line]
  simp [Real.cos_pi, Real.sin_pi]

theorem cosh_prod (x y : ℂ) :
    Complex.cosh x * Complex.cosh y =
      (Complex.cosh (x + y) + Complex.cosh (x - y)) / 2 := by
  have hsum : Complex.cosh (x + y) + Complex.cosh (x - y) =
      2 * (Complex.cosh x * Complex.cosh y) := by
    rw [Complex.cosh_add, Complex.cosh_sub]
    ring
  calc
    Complex.cosh x * Complex.cosh y = (2 * (Complex.cosh x * Complex.cosh y)) / 2 := by field_simp
    _ = (Complex.cosh (x + y) + Complex.cosh (x - y)) / 2 := by rw [hsum]

/-- `cosh(2z) (cosh z + cosh a)` is a positive combination of three modes. -/
theorem three_modes (a : ℝ) (z : ℂ) :
    Complex.cosh (2 * z) * (Complex.cosh z + (Real.cosh a : ℂ)) =
      (1 / 2) * Complex.cosh z + (Real.cosh a : ℂ) * Complex.cosh (2 * z)
        + (1 / 2) * Complex.cosh (3 * z) := by
  have hprod := cosh_prod (2 * z) z
  have h3 : 2 * z + z = 3 * z := by ring
  have h1 : 2 * z - z = z := by ring
  rw [h3, h1] at hprod
  calc
    Complex.cosh (2 * z) * (Complex.cosh z + (Real.cosh a : ℂ))
      = Complex.cosh (2 * z) * Complex.cosh z + (Real.cosh a : ℂ) * Complex.cosh (2 * z) := by ring
    _ = (Complex.cosh (3 * z) + Complex.cosh z) / 2 + (Real.cosh a : ℂ) * Complex.cosh (2 * z) := by
      rw [hprod]
    _ = (1 / 2) * Complex.cosh z + (Real.cosh a : ℂ) * Complex.cosh (2 * z)
        + (1 / 2) * Complex.cosh (3 * z) := by ring

theorem weights_positive (a : ℝ) :
    0 < (1 / 2 : ℝ) ∧ 0 < Real.cosh a := by
  exact ⟨by norm_num, Real.cosh_pos a⟩

theorem three_modes_vanish (a : ℝ) :
    (1 / 2) * Complex.cosh ((a : ℂ) + (Real.pi : ℂ) * Complex.I)
      + (Real.cosh a : ℂ) * Complex.cosh (2 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I))
      + (1 / 2) * Complex.cosh (3 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) = 0 := by
  rw [← three_modes]
  rw [pair_cancels]
  simp

theorem cos_two_pi : Real.cos (2 * Real.pi) = 1 := by
  rw [show (2 : ℝ) * Real.pi = Real.pi + Real.pi by ring, Real.cos_add, Real.cos_pi, Real.sin_pi]
  norm_num

theorem sin_two_pi : Real.sin (2 * Real.pi) = 0 := by
  rw [show (2 : ℝ) * Real.pi = Real.pi + Real.pi by ring, Real.sin_add, Real.cos_pi, Real.sin_pi]
  norm_num

theorem cos_three_pi : Real.cos (3 * Real.pi) = -1 := by
  rw [show (3 : ℝ) * Real.pi = Real.pi + 2 * Real.pi by ring, Real.cos_add, Real.cos_pi, Real.sin_pi,
    cos_two_pi, sin_two_pi]
  norm_num

theorem sin_three_pi : Real.sin (3 * Real.pi) = 0 := by
  rw [show (3 : ℝ) * Real.pi = Real.pi + 2 * Real.pi by ring, Real.sin_add, cos_two_pi, sin_two_pi,
    Real.sin_pi, Real.cos_pi]
  norm_num

/-- At the zero of the sum, each of the three modes is still alive. -/
theorem modes_alive (a : ℝ) :
    Complex.cosh ((a : ℂ) + (Real.pi : ℂ) * Complex.I) ≠ 0 ∧
      Complex.cosh (2 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) ≠ 0 ∧
      Complex.cosh (3 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I)) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩
  · intro h
    rw [cosh_line, Real.cos_pi, Real.sin_pi] at h
    have h0 : ((-Real.cosh a : ℝ) : ℂ) = 0 := by
      simpa [mul_neg_one, mul_zero, Complex.ofReal_zero, Complex.ofReal_neg, add_zero,
        zero_mul] using h
    have : -Real.cosh a = 0 := by exact_mod_cast h0
    linarith [Real.cosh_pos a]
  · intro h
    have harg : 2 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I) =
        ((2 * a : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
      simp [Complex.ofReal_mul]
      ring
    rw [harg, cosh_line, cos_two_pi, sin_two_pi] at h
    have h0 : ((Real.cosh (2 * a) : ℝ) : ℂ) = 0 := by
      simpa [mul_one, mul_zero, Complex.ofReal_zero, add_zero, zero_mul] using h
    have : Real.cosh (2 * a) = 0 := by exact_mod_cast h0
    exact (Real.cosh_pos (2 * a)).ne' this
  · intro h
    have harg : 3 * ((a : ℂ) + (Real.pi : ℂ) * Complex.I) =
        ((3 * a : ℝ) : ℂ) + ((3 * Real.pi : ℝ) : ℂ) * Complex.I := by
      simp [Complex.ofReal_mul]
      ring
    rw [harg, cosh_line, cos_three_pi, sin_three_pi] at h
    have h0 : ((-Real.cosh (3 * a) : ℝ) : ℂ) = 0 := by
      simpa [mul_neg_one, mul_zero, Complex.ofReal_zero, Complex.ofReal_neg, add_zero,
        zero_mul] using h
    have : -Real.cosh (3 * a) = 0 := by exact_mod_cast h0
    linarith [Real.cosh_pos (3 * a)]

theorem off_the_axis {a : ℝ} (ha : a ≠ 0) :
    ((a : ℂ) + (Real.pi : ℂ) * Complex.I).re ≠ 0 := by
  simp [ha]

end Modes
end CausalSpectrum

end

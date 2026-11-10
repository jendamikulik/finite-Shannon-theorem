/-
The reserve.

For a fixed `a > 0`,
`F_a(z) = (cosh z + cosh a) cosh(2z)`.
On the whole real axis this is at least `1 + cosh a`, and that floor is
strictly positive. At `z = a + iπ` the same function is zero.

Strict positivity on every real input, with a reserve, does not by itself
protect a function from a complex zero. A barrier that something can pass
through is not the missing piece. The missing piece is an identity, read off
the Riemann kernel alone, that would force a zero of `ξ` to mean zero
transport at some real energy, while the equations of that model
independently forbid zero transport.

Not proved: any such identity, or the Riemann hypothesis.
-/

import CausalSeed.Modes

noncomputable section

namespace CausalSpectrum
namespace Reserve

def F (a : ℝ) (z : ℂ) : ℂ :=
  (Complex.cosh z + (Real.cosh a : ℂ)) * Complex.cosh (2 * z)

def pt (a : ℝ) : ℂ := (a : ℂ) + (Real.pi : ℂ) * Complex.I

theorem product_floor (a x : ℝ) :
    1 + Real.cosh a ≤ (Real.cosh x + Real.cosh a) * Real.cosh (2 * x) := by
  have hx : 1 ≤ Real.cosh x := Real.one_le_cosh x
  have hx2 : 1 ≤ Real.cosh (2 * x) := Real.one_le_cosh (2 * x)
  have hsum : 1 + Real.cosh a ≤ Real.cosh x + Real.cosh a := by linarith
  have hfloor : 0 ≤ 1 + Real.cosh a := by linarith [Real.cosh_pos a]
  calc
    1 + Real.cosh a = (1 + Real.cosh a) * 1 := by ring
    _ ≤ (1 + Real.cosh a) * Real.cosh (2 * x) :=
      mul_le_mul_of_nonneg_left hx2 hfloor
    _ ≤ (Real.cosh x + Real.cosh a) * Real.cosh (2 * x) :=
      mul_le_mul_of_nonneg_right hsum (le_trans (by norm_num : (0 : ℝ) ≤ 1) hx2)

theorem F_of_real (a x : ℝ) :
    F a (x : ℂ) = (((Real.cosh x + Real.cosh a) * Real.cosh (2 * x) : ℝ) : ℂ) := by
  simp only [F]
  have h2 : 2 * (x : ℂ) = ((2 * x : ℝ) : ℂ) := by push_cast; ring
  rw [h2, ← Complex.ofReal_cosh, ← Complex.ofReal_cosh]
  push_cast
  ring

theorem real_floor (a x : ℝ) :
    1 + Real.cosh a ≤ (F a (x : ℂ)).re := by
  rw [F_of_real, Complex.ofReal_re]
  exact product_floor a x

theorem floor_pos {a : ℝ} (ha : 0 < a) : 0 < 1 + Real.cosh a := by
  have : 1 < Real.cosh a := Real.one_lt_cosh.mpr ha.ne'
  linarith

theorem complex_zero (a : ℝ) : F a (pt a) = 0 := by
  simp only [F, pt]
  rw [Modes.pair_cancels]
  simp

/-- Positivity on the real axis, with a reserve, does not forbid a complex zero. -/
theorem reserve_does_not_protect {a : ℝ} (ha : 0 < a) :
    (∀ x : ℝ, 1 + Real.cosh a ≤ (F a (x : ℂ)).re) ∧
      0 < 1 + Real.cosh a ∧
      F a (pt a) = 0 :=
  ⟨fun x => real_floor a x, floor_pos ha, complex_zero a⟩

end Reserve
end CausalSpectrum

end

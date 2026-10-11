/-
Stage 6 (numerical part): the exact integer inequalities of the note.
-/
import Mathlib.Tactic

set_option exponentiation.threshold 4000

namespace CausalSpectrum.Sqrt

/-- `H₂(Q) > 3/2` at `q = 0.410`, raised to the 200th power. -/
theorem endpoint_low : (2:ℕ) ^ 300 * 41 ^ 164 * 18 ^ 36 < 100 ^ 200 := by norm_num

/-- `H₂(Q) < 3/2` at `q = 0.411`, raised to the 2000th power. -/
theorem endpoint_high : (1000:ℕ) ^ 2000 < 2 ^ 3000 * 411 ^ 1644 * 178 ^ 356 := by norm_num

/-- `log₂(0.411/0.178) < 5/4`. -/
theorem ratio_bound : (411:ℕ) ^ 4 < 2 ^ 5 * 178 ^ 4 := by norm_num

/-- `2 · 0.411 · 0.18 · (5/4)² < 1/4`. -/
theorem variance_bound : (2:ℚ) * (411/1000) * (18/100) * (5/4) ^ 2 < 1/4 := by norm_num

end CausalSpectrum.Sqrt

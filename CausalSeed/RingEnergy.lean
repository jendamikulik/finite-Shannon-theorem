/-
Infinite energy, one finite ring at a time.

Around a zero of order `m ≥ 1` in the model `F(z) = z^m`, the logarithmic
derivative has magnitude `m/r` at distance `r`. The normalized quadratic
energy between radii `ε` and `R` is

`E(ε, R) = (1/(4π)) ∫_ε^R (m/r)^2 (2π r) dr = (m^2 / 2) log(R/ε)`.

Each halving of the inner radius adds exactly `(m^2 / 2) log 2`. Each
ring from `r` to `e r` adds exactly `m^2 / 2`. Every individual ring has
finite energy. Infinitely many fit around the zero, and the integral
diverges logarithmically as `ε → 0`.

That infinity is the divergent integral, not a source of extractable
physical energy.

Not proved: that this energy is physical; anything about the zeros of `ξ`.
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

open intervalIntegral MeasureTheory Set Filter

namespace CausalSpectrum
namespace RingEnergy

/-- Normalized quadratic energy of one ring, as a closed form.
`E(ε, R) = (m^2 / 2) log(R/ε)`. -/
def E (m ε R : ℝ) : ℝ := (m ^ 2 / 2) * Real.log (R / ε)

/-- The normalized integrand: `(1/(4π)) * (m/r)^2 * (2π r)`. -/
def integrand (m : ℝ) (r : ℝ) : ℝ :=
  (1 / (4 * Real.pi)) * (m / r) ^ 2 * (2 * Real.pi * r)

theorem integrand_eq (m : ℝ) {r : ℝ} (hr : r ≠ 0) :
    integrand m r = (m ^ 2 / 2) * r⁻¹ := by
  unfold integrand
  have hpi : (4 : ℝ) * Real.pi ≠ 0 := by
    have : (0 : ℝ) < Real.pi := Real.pi_pos
    positivity
  field_simp [hr, hpi]
  ring

/-- On the interval `[ε, R]` with `0 < ε` every point is nonzero. -/
theorem mem_nonzero {ε R r : ℝ} (hε : 0 < ε) (hR : ε ≤ R)
    (hr : r ∈ uIcc ε R) : r ≠ 0 := by
  rw [uIcc_of_le hR] at hr
  exact ne_of_gt (lt_of_lt_of_le hε hr.1)

/-- The integral of the normalized integrand equals the closed form. -/
theorem E_eq_integral (m : ℝ) {ε R : ℝ} (hε : 0 < ε) (hR : ε < R) :
    ∫ r in ε..R, integrand m r = E m ε R := by
  have hRpos : 0 < R := lt_trans hε hR
  have hint : ∫ r in ε..R, integrand m r =
      ∫ r in ε..R, (m ^ 2 / 2) * r⁻¹ := by
    apply intervalIntegral.integral_congr
    intro r hr
    exact integrand_eq m (mem_nonzero hε hR.le hr)
  rw [hint, intervalIntegral.integral_const_mul, integral_inv_of_pos hε hRpos]
  unfold E
  ring

/-- Each halving of the inner radius adds exactly `(m^2 / 2) log 2`. -/
theorem halving (m : ℝ) {r : ℝ} (hr : 0 < r) :
    E m (r / 2) r = (m ^ 2 / 2) * Real.log 2 := by
  unfold E
  have hratio : r / (r / 2) = 2 := by field_simp
  rw [hratio]

/-- Each ring from `r` to `e · r` adds exactly `m^2 / 2`. -/
theorem off_e (m : ℝ) {r : ℝ} (hr : 0 < r) :
    E m r (Real.exp 1 * r) = m ^ 2 / 2 := by
  unfold E
  have hrne : r ≠ 0 := ne_of_gt hr
  have he : Real.exp 1 * r / r = Real.exp 1 := by field_simp [hrne]
  rw [he, Real.log_exp]
  ring

/-- A single ring is finite: the closed form is a real number. -/
theorem ring_finite (m ε R : ℝ) : ∃ C : ℝ, E m ε R = C :=
  ⟨E m ε R, rfl⟩

/-- As the inner radius tends to zero from above, the energy tends to
`+∞` whenever `m ≠ 0`. The infinity is logarithmic. -/
theorem diverges (m : ℝ) (hm : m ≠ 0) (R : ℝ) (hR : 0 < R) :
    Tendsto (fun ε => E m ε R) (nhdsWithin 0 (Ioi 0)) atTop := by
  unfold E
  have hcoef : 0 < m ^ 2 / 2 := by
    have : 0 < m ^ 2 := sq_pos_of_ne_zero hm
    positivity
  have hinv : Tendsto (fun ε : ℝ => ε⁻¹) (nhdsWithin 0 (Ioi 0)) atTop :=
    tendsto_inv_nhdsGT_zero
  have hmul : Tendsto (fun ε => R * ε⁻¹) (nhdsWithin 0 (Ioi 0)) atTop :=
    Tendsto.const_mul_atTop hR hinv
  have heq : (fun ε => Real.log (R / ε)) =ᶠ[nhdsWithin 0 (Ioi 0)]
      (fun ε => Real.log (R * ε⁻¹)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have : R / ε = R * ε⁻¹ := by field_simp
    rw [this]
  have hlog : Tendsto (fun ε => Real.log (R / ε)) (nhdsWithin 0 (Ioi 0)) atTop :=
    (Real.tendsto_log_atTop.comp hmul).congr' heq.symm
  exact Tendsto.const_mul_atTop hcoef hlog

end RingEnergy
end CausalSpectrum

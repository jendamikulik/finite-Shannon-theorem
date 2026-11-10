/-
The freedom to ask.

`Σ |Aₖ|²` and `|Σ Aₖ|²` are different questions. The first adds intensities.
The second keeps the interference. Choosing one fixes its value. Nothing
here is a claim about human free will.

Proved, with no sorry, for modes of frequencies `1, 2, 3` with positive
weights `1/2`, `cosh a` and `1/2`:

* at `z = a + iπ` the coherent sum is `0`, while the sum of the three
  intensities is strictly positive;
* convolving that symmetric atomic measure with a centered Gaussian of
  variance `v > 0` multiplies the bilateral Laplace transform by
  `exp(v z² / 2)`. The new density is positive, even and analytic, and the
  same zero survives, because the exponential factor never vanishes.

Not proved: any property of the Riemann kernel that would forbid this.
Positivity, symmetry and analytic smoothness, taken together, do not.
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.Constructions
import CausalSeed.Modes

noncomputable section

open Real MeasureTheory

namespace CausalSpectrum
namespace Interference

def pt (a : ℝ) : ℂ := (a : ℂ) + (Real.pi : ℂ) * Complex.I

/-- Positive-weight sum of three symmetric modes. -/
def F (a : ℝ) (z : ℂ) : ℂ :=
  (1 / 2) * Complex.cosh z + (cosh a : ℂ) * Complex.cosh (2 * z) +
    (1 / 2) * Complex.cosh (3 * z)

theorem F_factor (a : ℝ) (z : ℂ) :
    F a z = Complex.cosh (2 * z) * (Complex.cosh z + (cosh a : ℂ)) := by
  simpa [F] using (Modes.three_modes a z).symm

theorem coherent_zero (a : ℝ) : F a (pt a) = 0 := by
  simpa [F, pt] using Modes.three_modes_vanish a

/-- Sum of the three intensities, with the interference thrown away. -/
def intensity (a : ℝ) : ℝ :=
  Complex.normSq (((1 / 2 : ℝ) : ℂ) * Complex.cosh (pt a)) +
    Complex.normSq ((cosh a : ℂ) * Complex.cosh (2 * pt a)) +
    Complex.normSq (((1 / 2 : ℝ) : ℂ) * Complex.cosh (3 * pt a))

theorem normSq_real_mul (r : ℝ) (z : ℂ) :
    Complex.normSq ((r : ℂ) * z) = r ^ 2 * Complex.normSq z := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← sq]

theorem normSq_pos_of_ne_zero {z : ℂ} (hz : z ≠ 0) : 0 < Complex.normSq z := by
  have hne : Complex.normSq z ≠ 0 := fun h => hz (Complex.normSq_eq_zero.mp h)
  exact lt_of_le_of_ne (Complex.normSq_nonneg z) hne.symm

theorem incoherent_pos (a : ℝ) : 0 < intensity a := by
  have hmodes := Modes.modes_alive a
  have hcoeff1 : (1 / 2 : ℝ) ≠ 0 := by norm_num
  have hcoeff2 : cosh a ≠ 0 := (cosh_pos a).ne'
  have term (r : ℝ) (z : ℂ) (hr : r ≠ 0) (hz : z ≠ 0) :
      0 < Complex.normSq ((r : ℂ) * z) := by
    rw [normSq_real_mul]
    exact mul_pos (sq_pos_of_ne_zero hr) (normSq_pos_of_ne_zero hz)
  have h1 := term (1 / 2) (Complex.cosh (pt a)) hcoeff1 hmodes.1
  have h2 := term (cosh a) (Complex.cosh (2 * pt a)) hcoeff2 hmodes.2.1
  have h3 := term (1 / 2) (Complex.cosh (3 * pt a)) hcoeff1 hmodes.2.2
  dsimp only [intensity]
  linarith

/-- The two questions do not have the same answer. -/
theorem questions_differ (a : ℝ) :
    Complex.normSq (F a (pt a)) ≠ intensity a := by
  rw [coherent_zero, Complex.normSq_zero]
  exact Ne.symm (incoherent_pos a).ne'

def gauss (v t : ℝ) : ℝ :=
  exp (-t ^ 2 / (2 * v)) / sqrt (2 * Real.pi * v)

theorem gauss_pos {v t : ℝ} (hv : 0 < v) : 0 < gauss v t := by
  unfold gauss
  exact div_pos (exp_pos _) (sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hv))

theorem gauss_even (v t : ℝ) : gauss v (-t) = gauss v t := by
  unfold gauss
  rw [neg_sq]

/-- Density of the symmetric atomic measure convolved with `N(0, v)`. -/
def density (a v t : ℝ) : ℝ :=
  (1 / 4) * (gauss v (t - 1) + gauss v (t + 1)) +
    (cosh a / 2) * (gauss v (t - 2) + gauss v (t + 2)) +
    (1 / 4) * (gauss v (t - 3) + gauss v (t + 3))

theorem density_pos {a v t : ℝ} (hv : 0 < v) : 0 < density a v t := by
  have pair (c k : ℝ) (hc : 0 < c) :
      0 < c * (gauss v (t - k) + gauss v (t + k)) := by
    refine mul_pos hc (add_pos (gauss_pos hv) (gauss_pos hv))
  have h12 : 0 < (1 / 4) * (gauss v (t - 1) + gauss v (t + 1)) +
      (cosh a / 2) * (gauss v (t - 2) + gauss v (t + 2)) :=
    add_pos (pair (1 / 4) 1 (by norm_num))
      (pair (cosh a / 2) 2 (div_pos (cosh_pos a) (by norm_num)))
  exact add_pos h12 (pair (1 / 4) 3 (by norm_num))

theorem density_even (a v t : ℝ) : density a v (-t) = density a v t := by
  unfold density
  have pair (k : ℝ) :
      gauss v (-t - k) + gauss v (-t + k) = gauss v (t - k) + gauss v (t + k) := by
    rw [show -t - k = -(t + k) by ring, show -t + k = -(t - k) by ring,
      gauss_even, gauss_even, add_comm]
  rw [pair 1, pair 2, pair 3]

theorem gauss_analytic {v : ℝ} (hv : 0 < v) (k : ℝ) :
    AnalyticOn ℝ (fun t => gauss v (t - k)) Set.univ := by
  have hden : (2 * v : ℝ) ≠ 0 := by linarith
  have hquad : AnalyticOn ℝ (fun t : ℝ => -((t - k) ^ 2) / (2 * v)) Set.univ :=
    AnalyticOn.div (AnalyticOn.neg ((analyticOn_id.sub analyticOn_const).pow 2))
      analyticOn_const (fun _ _ => hden)
  have hexp : AnalyticOn ℝ (fun t : ℝ => exp (-((t - k) ^ 2) / (2 * v))) Set.univ :=
    hquad.rexp
  simpa [gauss, div_eq_mul_inv] using hexp.mul analyticOn_const

theorem density_analytic {a v : ℝ} (hv : 0 < v) :
    AnalyticOn ℝ (density a v) Set.univ := by
  unfold density
  have h1 := AnalyticOn.const_smul (c := (1 / 4 : ℝ))
    ((gauss_analytic hv 1).add (gauss_analytic hv (-1)))
  have h2 := AnalyticOn.const_smul (c := cosh a / 2)
    ((gauss_analytic hv 2).add (gauss_analytic hv (-2)))
  have h3 := AnalyticOn.const_smul (c := (1 / 4 : ℝ))
    ((gauss_analytic hv 3).add (gauss_analytic hv (-3)))
  refine (h1.add (h2.add h3)).congr ?_
  intro t _
  simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, sub_neg_eq_add]
  ring

theorem bump_integrable {v : ℝ} (hv : 0 < v) (z : ℂ) (k : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (z * t) * (gauss v (t - k) : ℂ)) := by
  let b : ℂ := (-1 / (2 * v) : ℝ)
  have hb : b.re < 0 := by
    simp only [b, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) (by linarith : 0 < 2 * v)
  set s : ℂ := (sqrt (2 * Real.pi * v) : ℂ)
  have hspos : 0 < sqrt (2 * Real.pi * v) :=
    sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hv)
  have hfun : ∀ t : ℝ, Complex.exp (z * t) * (gauss v (t - k) : ℂ) =
      Complex.exp (b * t ^ 2 + (z + (k : ℂ) / v) * t + (-(k : ℂ) ^ 2 / (2 * v))) / s := by
    intro t
    have hquad : -(t - k) ^ 2 / (2 * v) =
        (-1 / (2 * v)) * t ^ 2 + (k / v) * t - k ^ 2 / (2 * v) := by
      field_simp
      ring
    unfold gauss
    rw [hquad, Complex.ofReal_div, Complex.ofReal_exp, div_eq_mul_inv, ← mul_assoc,
      ← Complex.exp_add, ← div_eq_mul_inv]
    congr 1
    simp only [b]
    push_cast
    congr 1
    simp only [field]
    ring
  have hg : Integrable (fun t : ℝ =>
      Complex.exp (b * t ^ 2 + (z + (k : ℂ) / v) * t + (-(k : ℂ) ^ 2 / (2 * v))) * s⁻¹) :=
    (integrable_cexp_quadratic' hb (z + (k : ℂ) / v) (-(k : ℂ) ^ 2 / (2 * v))).mul_const _
  refine hg.congr ?_
  filter_upwards with t
  rw [div_eq_mul_inv]
  exact (hfun t).symm

/-- One Gaussian bump, shifted by `k`. -/
theorem bump_laplace {v : ℝ} (hv : 0 < v) (z : ℂ) (k : ℝ) :
    ∫ t : ℝ, Complex.exp (z * t) * (gauss v (t - k) : ℂ) =
      Complex.exp ((k : ℂ) * z) * Complex.exp ((v : ℂ) * z ^ 2 / 2) := by
  let b : ℂ := (-1 / (2 * v) : ℝ)
  have hb : b.re < 0 := by
    simp only [b, Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (by norm_num : (-1 : ℝ) < 0) (by linarith : 0 < 2 * v)
  set s : ℂ := (sqrt (2 * Real.pi * v) : ℂ)
  have hspos : 0 < sqrt (2 * Real.pi * v) :=
    sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) Real.pi_pos) hv)
  have hs : s ≠ 0 := by
    simpa [s] using Complex.ofReal_ne_zero.mpr hspos.ne'
  have hfun : ∀ t : ℝ, Complex.exp (z * t) * (gauss v (t - k) : ℂ) =
      Complex.exp (b * t ^ 2 + (z + (k : ℂ) / v) * t + (-(k : ℂ) ^ 2 / (2 * v))) / s := by
    intro t
    have hquad : -(t - k) ^ 2 / (2 * v) =
        (-1 / (2 * v)) * t ^ 2 + (k / v) * t - k ^ 2 / (2 * v) := by
      field_simp
      ring
    unfold gauss
    rw [hquad, Complex.ofReal_div, Complex.ofReal_exp, div_eq_mul_inv, ← mul_assoc,
      ← Complex.exp_add, ← div_eq_mul_inv]
    congr 1
    simp only [b]
    push_cast
    congr 1
    simp only [field]
    ring
  have houter : ∀ t : ℝ,
      Complex.exp (b * t ^ 2 + (z + (k : ℂ) / v) * t + (-(k : ℂ) ^ 2 / (2 * v))) / s =
        Complex.exp (b * t ^ 2 + (z + (k : ℂ) / v) * t + (-(k : ℂ) ^ 2 / (2 * v))) * s⁻¹ := by
    intro t
    rw [div_eq_mul_inv]
  simp_rw [hfun, houter, integral_mul_const]
  rw [integral_cexp_quadratic hb (z + (k : ℂ) / v) (-(k : ℂ) ^ 2 / (2 * v))]
  have hb_form : b = -1 / (2 * (v : ℂ)) := by
    simp only [b]
    push_cast
    ring
  have hexp : -(k : ℂ) ^ 2 / (2 * v) - (z + (k : ℂ) / v) ^ 2 / (4 * b) =
      (k : ℂ) * z + (v : ℂ) * z ^ 2 / 2 := by
    have hvC : (v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
    rw [hb_form]
    simp only [field, hvC]
    ring
  have hpref : (Real.pi / -b) ^ (1 / 2 : ℂ) * s⁻¹ = 1 := by
    have hbase : (Real.pi : ℂ) / -b = ((2 * Real.pi * v : ℝ) : ℂ) := by
      rw [hb_form]
      push_cast
      simp only [field]
    have hpow : ((2 * Real.pi * v : ℝ) : ℂ) ^ (1 / 2 : ℂ) = s := by
      have hnonneg : 0 ≤ 2 * Real.pi * v :=
        mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) hv.le
      have hhalf : ((1 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) := by
        push_cast
        rfl
      rw [← hhalf, ← Complex.ofReal_cpow hnonneg (1 / 2)]
      simp [Real.sqrt_eq_rpow, s]
    rw [hbase, hpow, mul_inv_cancel₀ hs]
  rw [hexp, Complex.exp_add, mul_right_comm, hpref, one_mul]

theorem pair_integrable {v : ℝ} (hv : 0 < v) (z : ℂ) (k w : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (z * t) *
      (((w / 2) * (gauss v (t - k) + gauss v (t + k)) : ℝ) : ℂ)) := by
  have hcast : ∀ t : ℝ,
      (((w / 2) * (gauss v (t - k) + gauss v (t + k)) : ℝ) : ℂ) =
        (w / 2 : ℂ) * ((gauss v (t - k) : ℂ) + gauss v (t + k)) := by
    intro t
    push_cast
    ring
  simp_rw [hcast, mul_add, mul_left_comm (Complex.exp (z * _))]
  refine Integrable.add ?_ ?_
  · exact (bump_integrable hv z k).const_mul _
  · have hshift : (fun t : ℝ =>
        (w / 2 : ℂ) * (Complex.exp (z * t) * (gauss v (t + k) : ℂ))) =
        fun t : ℝ => (w / 2 : ℂ) * (Complex.exp (z * t) * (gauss v (t - (-k)) : ℂ)) := by
      ext t
      rw [show t + k = t - (-k) by ring]
    rw [hshift]
    exact (bump_integrable hv z (-k)).const_mul _

theorem pair_laplace {v : ℝ} (hv : 0 < v) (z : ℂ) (k w : ℝ) :
    ∫ t : ℝ, Complex.exp (z * t) *
        (((w / 2) * (gauss v (t - k) + gauss v (t + k)) : ℝ) : ℂ) =
      (w : ℂ) * Complex.cosh ((k : ℂ) * z) * Complex.exp ((v : ℂ) * z ^ 2 / 2) := by
  have hcast : ∀ t : ℝ,
      (((w / 2) * (gauss v (t - k) + gauss v (t + k)) : ℝ) : ℂ) =
        (w / 2 : ℂ) * ((gauss v (t - k) : ℂ) + gauss v (t + k)) := by
    intro t
    push_cast
    ring
  simp_rw [hcast, mul_add, mul_left_comm (Complex.exp (z * _))]
  have i1 : Integrable (fun t : ℝ =>
      (w / 2 : ℂ) * (Complex.exp (z * t) * (gauss v (t - k) : ℂ))) :=
    (bump_integrable hv z k).const_mul _
  have i2 : Integrable (fun t : ℝ =>
      (w / 2 : ℂ) * (Complex.exp (z * t) * (gauss v (t + k) : ℂ))) := by
    simpa only [show ∀ t : ℝ, t - (-k) = t + k by intro t; ring] using
      (bump_integrable hv z (-k)).const_mul (w / 2 : ℂ)
  rw [integral_add i1 i2]
  rw [integral_const_mul, integral_const_mul, bump_laplace hv z k]
  have hsecond : ∫ t : ℝ, Complex.exp (z * t) * (gauss v (t + k) : ℂ) =
      Complex.exp (((-k : ℝ) : ℂ) * z) * Complex.exp ((v : ℂ) * z ^ 2 / 2) := by
    simpa only [show ∀ t : ℝ, t - (-k) = t + k by intro t; ring] using bump_laplace hv z (-k)
  rw [hsecond]
  have hneg : Complex.exp (((-k : ℝ) : ℂ) * z) = Complex.exp (-(k : ℂ) * z) := by
    congr 1
    push_cast
    ring
  rw [hneg]
  have hcosh : (w / 2 : ℂ) * (Complex.exp ((k : ℂ) * z) + Complex.exp (-(k : ℂ) * z)) =
      (w : ℂ) * Complex.cosh ((k : ℂ) * z) := by
    rw [Complex.cosh]
    field_simp
  calc
    (w / 2 : ℂ) * (Complex.exp ((k : ℂ) * z) * Complex.exp ((v : ℂ) * z ^ 2 / 2)) +
        (w / 2 : ℂ) * (Complex.exp (-(k : ℂ) * z) * Complex.exp ((v : ℂ) * z ^ 2 / 2))
      = ((w / 2 : ℂ) * (Complex.exp ((k : ℂ) * z) + Complex.exp (-(k : ℂ) * z))) *
          Complex.exp ((v : ℂ) * z ^ 2 / 2) := by ring
    _ = (w : ℂ) * Complex.cosh ((k : ℂ) * z) * Complex.exp ((v : ℂ) * z ^ 2 / 2) := by
      rw [hcosh]

/-- The smoothed density has Laplace transform `exp(v z² / 2) · F(z)`. -/
theorem density_laplace {v : ℝ} (hv : 0 < v) (a : ℝ) (z : ℂ) :
    ∫ t : ℝ, Complex.exp (z * t) * (density a v t : ℂ) =
      Complex.exp ((v : ℂ) * z ^ 2 / 2) * F a z := by
  have hsplit : ∀ t : ℝ, (density a v t : ℂ) =
      (((1 / 2 / 2) * (gauss v (t - 1) + gauss v (t + 1)) : ℝ) : ℂ) +
        (((cosh a / 2) * (gauss v (t - 2) + gauss v (t + 2)) : ℝ) : ℂ) +
        (((1 / 2 / 2) * (gauss v (t - 3) + gauss v (t + 3)) : ℝ) : ℂ) := by
    intro t
    unfold density
    push_cast
    ring
  have i1 := pair_integrable hv z 1 (1 / 2)
  have i2 := pair_integrable hv z 2 (cosh a)
  have i3 := pair_integrable hv z 3 (1 / 2)
  have heq :
      ∫ t : ℝ, Complex.exp (z * t) * (density a v t : ℂ) =
        (∫ t : ℝ, Complex.exp (z * t) *
            (((1 / 2 / 2) * (gauss v (t - 1) + gauss v (t + 1)) : ℝ) : ℂ)) +
          ((∫ t : ℝ, Complex.exp (z * t) *
              (((cosh a / 2) * (gauss v (t - 2) + gauss v (t + 2)) : ℝ) : ℂ)) +
            ∫ t : ℝ, Complex.exp (z * t) *
              (((1 / 2 / 2) * (gauss v (t - 3) + gauss v (t + 3)) : ℝ) : ℂ)) := by
    have hpoint : ∀ t : ℝ, Complex.exp (z * t) * (density a v t : ℂ) =
        Complex.exp (z * t) *
            (((1 / 2 / 2) * (gauss v (t - 1) + gauss v (t + 1)) : ℝ) : ℂ) +
          (Complex.exp (z * t) *
              (((cosh a / 2) * (gauss v (t - 2) + gauss v (t + 2)) : ℝ) : ℂ) +
            Complex.exp (z * t) *
              (((1 / 2 / 2) * (gauss v (t - 3) + gauss v (t + 3)) : ℝ) : ℂ)) := by
      intro t
      rw [hsplit t, mul_add, mul_add, add_assoc]
    have hInt :
        ∫ t : ℝ, Complex.exp (z * t) * (density a v t : ℂ) =
          ∫ t : ℝ, Complex.exp (z * t) *
              (((1 / 2 / 2) * (gauss v (t - 1) + gauss v (t + 1)) : ℝ) : ℂ) +
            (Complex.exp (z * t) *
                (((cosh a / 2) * (gauss v (t - 2) + gauss v (t + 2)) : ℝ) : ℂ) +
              Complex.exp (z * t) *
                (((1 / 2 / 2) * (gauss v (t - 3) + gauss v (t + 3)) : ℝ) : ℂ)) :=
      integral_congr_ae (ae_of_all _ hpoint)
    rw [hInt]
    exact (integral_add i1 (i2.add i3)).trans (congrArg _ (integral_add i2 i3))
  rw [heq, pair_laplace hv z 1 (1 / 2), pair_laplace hv z 2 (cosh a), pair_laplace hv z 3 (1 / 2)]
  unfold F
  push_cast
  simp only [field, one_mul]
  ring

theorem smoothed_zero {v : ℝ} (hv : 0 < v) (a : ℝ) :
    ∫ t : ℝ, Complex.exp ((pt a) * t) * (density a v t : ℂ) = 0 := by
  rw [density_laplace hv a (pt a), coherent_zero, mul_zero]

theorem factor_ne_zero (v : ℝ) (z : ℂ) :
    Complex.exp ((v : ℂ) * z ^ 2 / 2) ≠ 0 :=
  Complex.exp_ne_zero _

end Interference
end CausalSpectrum

end

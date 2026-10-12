/-
Hoeffding's lemma for a finite weighted average, in the form used by the maximal-entropy
comparison: for weights `w` summing to one and values in `[0, M]`,
`∑ w_y e^{t v_y} ≤ exp(t ∑ w_y v_y + t² M² / 8)`.
-/
import Mathlib.Probability.Moments.SubGaussian

noncomputable section
open MeasureTheory ProbabilityTheory Finset

namespace CausalSpectrum.MaxEntropy

theorem finite_hoeffding {n : ℕ} (w v : Fin n → ℝ) (hw : ∀ y, 0 ≤ w y) (hs : ∑ y, w y = 1)
    {M : ℝ} (hv : ∀ y, 0 ≤ v y ∧ v y ≤ M) (t : ℝ) :
    ∑ y, w y * Real.exp (t * v y) ≤ Real.exp (t * ∑ y, w y * v y + t ^ 2 * M ^ 2 / 8) := by
  let μ : Measure (Fin n) := ∑ y, ENNReal.ofReal (w y) • Measure.dirac y
  have hint : ∀ f : Fin n → ℝ, ∫ x, f x ∂μ = ∑ y, w y * f y := by
    intro f
    rw [integral_finsetSum_measure (fun y _ => by
      have : IsFiniteMeasure (ENNReal.ofReal (w y) • Measure.dirac y) := by
        constructor; simp
      exact Integrable.of_finite)]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hw y), smul_eq_mul]
  have hprob : IsProbabilityMeasure μ := by
    constructor
    simp only [μ, Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
      measure_univ, mul_one]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => hw y), hs, ENNReal.ofReal_one]
  have hsub := hasSubgaussianMGF_of_mem_Icc (μ := μ) (X := v) (a := 0) (b := M)
    (Measurable.of_discrete).aemeasurable (Filter.Eventually.of_forall fun y => hv y)
  have h1 := hsub.mgf_le t
  rw [mgf, hint, hint] at h1
  have hM : 0 ≤ M := (hv ⟨0, by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp at hs
    · exact h⟩).1.trans (hv _).2
  have hc : ((‖M - 0‖₊ / 2 : NNReal) ^ 2 : NNReal) = (M / 2) ^ 2 := by
    simp [abs_of_nonneg hM]
  rw [hc] at h1
  have key : ∑ y, w y * Real.exp (t * v y) =
      Real.exp (t * ∑ y, w y * v y) * ∑ y, w y * Real.exp (t * (v y - ∑ y, w y * v y)) := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun y _ => ?_
    rw [mul_sub, Real.exp_sub]; field_simp
  rw [key, Real.exp_add]
  refine mul_le_mul_of_nonneg_left (h1.trans (le_of_eq ?_)) (Real.exp_pos _).le
  congr 1; ring

end CausalSpectrum.MaxEntropy

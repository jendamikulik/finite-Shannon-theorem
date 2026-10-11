/-
A Fourier lower bound for the increments of the Bellman envelope.

`G_n` is the CDF of a probability measure `μ_n`. For two actions `j, k`, the difference
`R = E_j G_n - E_k G_n` of their one-step averages satisfies
`∫ R(x) e^{itx} dx = -(φ_j(t) - φ_k(t)) μ̂_n(t) / (it)`, where `φ_j` is the
characteristic function of the centered information of action `j`. Hence
`∫ |R| ≥ |φ_j(t) - φ_k(t)| |μ̂_n(t)| / |t|`.
-/
import CausalSeed.SqrtDefect
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Filter Topology Complex
open scoped ENNReal

namespace CausalSpectrum.Sqrt

/-! ## Step functions -/

/-- `s_c(x) = 1{c ≤ x} - 1{0 ≤ x}`. -/
def step (c x : ℝ) : ℝ := (Ici c).indicator 1 x - (Ici 0).indicator 1 x

theorem step_eq_of_nonneg {c : ℝ} (hc : 0 ≤ c) : step c = fun x => -(Ico 0 c).indicator 1 x := by
  funext x
  simp only [step, indicator, mem_Ici, mem_Ico, Pi.one_apply]
  by_cases h1 : c ≤ x <;> by_cases h2 : 0 ≤ x <;> simp [h1, h2] <;> linarith

theorem step_eq_of_neg {c : ℝ} (hc : c < 0) : step c = fun x => (Ico c 0).indicator 1 x := by
  funext x
  simp only [step, indicator, mem_Ici, mem_Ico, Pi.one_apply]
  by_cases h1 : c ≤ x <;> by_cases h2 : 0 ≤ x <;> simp [h1, h2] <;> linarith

theorem abs_step_le (c x : ℝ) : |step c x| ≤ (Icc (-|c|) |c|).indicator 1 x := by
  have hI : 0 ≤ (Icc (-|c|) |c|).indicator (1 : ℝ → ℝ) x :=
    indicator_nonneg (fun _ _ => zero_le_one) _
  rcases le_or_gt 0 c with hc | hc
  · rw [step_eq_of_nonneg hc]
    by_cases h : x ∈ Ico 0 c
    · have hm : x ∈ Icc (-|c|) |c| := by
        rw [abs_of_nonneg hc]; exact ⟨by linarith [h.1], h.2.le⟩
      simp [indicator, h, hm]
    · simpa [indicator, h] using hI
  · rw [step_eq_of_neg hc]
    by_cases h : x ∈ Ico c 0
    · have hm : x ∈ Icc (-|c|) |c| := by
        rw [abs_of_neg hc]; exact ⟨by linarith [h.1], by linarith [h.2]⟩
      simp [indicator, h, hm]
    · simpa [indicator, h] using hI

theorem measurable_step (c : ℝ) : Measurable (step c) :=
  (measurable_one.indicator measurableSet_Ici).sub (measurable_one.indicator measurableSet_Ici)

theorem integrable_step (c : ℝ) : Integrable (step c) := by
  rcases le_or_gt 0 c with hc | hc
  · rw [step_eq_of_nonneg hc]
    exact ((integrable_indicator_iff measurableSet_Ico).2
      (integrableOn_const (by simp) (by simp))).neg
  · rw [step_eq_of_neg hc]
    exact (integrable_indicator_iff measurableSet_Ico).2 (integrableOn_const (by simp) (by simp))

/-- `∫ s_c(x) f(x) dx = -∫_0^c f`. -/
theorem integral_step_smul (c : ℝ) {f : ℝ → ℂ} (_hf : Continuous f) :
    ∫ x, (step c x : ℂ) * f x = -∫ x in (0:ℝ)..c, f x := by
  rcases le_or_gt 0 c with hc | hc
  · have : (fun x => (step c x : ℂ) * f x) = fun x => -(Ico 0 c).indicator f x := by
      funext x; rw [step_eq_of_nonneg hc]
      by_cases h : x ∈ Ico 0 c <;> simp [indicator, h]
    rw [this, integral_neg, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_of_le hc]
  · have : (fun x => (step c x : ℂ) * f x) = fun x => (Ico c 0).indicator f x := by
      funext x; rw [step_eq_of_neg hc]
      by_cases h : x ∈ Ico c 0 <;> simp [indicator, h]
    rw [this, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
      ← integral_Ioc_eq_integral_Ioo, intervalIntegral.integral_symm,
      intervalIntegral.integral_of_le hc.le, neg_neg]

theorem integral_step_exp (c : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, (step c x : ℂ) * Complex.exp (↑t * I * x) =
      -((Complex.exp (↑t * I * c) - 1) / (↑t * I)) := by
  have hc : (↑t * I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
  rw [integral_step_smul c (by fun_prop), integral_exp_mul_complex hc]
  simp

theorem integral_step (c : ℝ) : ∫ x, step c x = -c := by
  have h := integral_step_smul c (f := fun _ => (1:ℂ)) continuous_const
  simp only [mul_one, intervalIntegral.integral_const, sub_zero, real_smul, mul_one] at h
  have h2 : ((∫ x, step c x : ℝ) : ℂ) = ∫ x, (step c x : ℂ) := integral_ofReal.symm
  have : ((∫ x, step c x : ℝ) : ℂ) = ((-c : ℝ) : ℂ) := by rw [h2, h]; push_cast; ring
  exact_mod_cast this


namespace IncFamily
variable (F : IncFamily)

/-! ## The envelope law -/

def GS (n : ℕ) : StieltjesFunction ℝ where
  toFun := F.G n
  mono' := (F.G_cdf n).1
  right_continuous' := (F.G_cdf n).2.1

theorem G_atBot (n : ℕ) : Tendsto (F.G n) atBot (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_lt_atBot (-(n * F.M))] with x hx
    exact ((F.G_cdf n).2.2.2.1 x hx).symm)

theorem G_atTop (n : ℕ) : Tendsto (F.G n) atTop (𝓝 1) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop (n * F.M)] with x hx
    exact ((F.G_cdf n).2.2.2.2 x hx).symm)

/-- The envelope law `μ_n`: the probability measure with CDF `G_n`. -/
def law (n : ℕ) : Measure ℝ := (F.GS n).measure

instance (n : ℕ) : IsProbabilityMeasure (F.law n) :=
  ⟨by rw [law, (F.GS n).measure_univ (F.G_atBot n) (F.G_atTop n)]; simp⟩

theorem G_eq_law (n : ℕ) (z : ℝ) : F.G n z = (F.law n).real (Iic z) := by
  have := cdf_measure_stieltjesFunction (F.GS n) (F.G_atBot n) (F.G_atTop n)
  rw [← cdf_eq_real]
  exact (congrFun (congrArg (fun f : StieltjesFunction ℝ => (f : ℝ → ℝ)) this) z).symm

/-! ## The step profile of an action -/

/-- `ρ_j(x) = Σ_y P_j(y) s_{X_j(y)}(x)`. -/
def rho (j : Fin F.nA) (x : ℝ) : ℝ := ∑ y, F.P j y * step (F.X j y) x

theorem measurable_rho (j) : Measurable (F.rho j) :=
  Finset.measurable_sum _ fun y _ => measurable_const.mul (measurable_step _)

theorem integrable_rho (j) : Integrable (F.rho j) :=
  integrable_finsetSum _ fun y _ => (integrable_step _).const_mul _

/-- Characteristic function of the centered information of action `j`. -/
def phi (j : Fin F.nA) (t : ℝ) : ℂ := ∑ y, (F.P j y : ℂ) * Complex.exp (↑t * I * F.X j y)

theorem fourier_rho (j) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, (F.rho j x : ℂ) * Complex.exp (↑t * I * x) = -((F.phi j t - 1) / (↑t * I)) := by
  have hint : ∀ y, Integrable fun x => (F.P j y : ℂ) * ((step (F.X j y) x : ℂ) *
      Complex.exp (↑t * I * x)) := fun y => by
    refine Integrable.const_mul ?_ _
    refine ((integrable_step (F.X j y)).ofReal.mul_bdd (c := 1) ?_ ?_)
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (↑t * I * x)).aestronglyMeasurable
    · exact ae_of_all _ fun x => by
        rw [show (↑t * I * ↑x : ℂ) = ↑(t * x) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have : (fun x => (F.rho j x : ℂ) * Complex.exp (↑t * I * x)) =
      fun x => ∑ y, (F.P j y : ℂ) * ((step (F.X j y) x : ℂ) * Complex.exp (↑t * I * x)) := by
    funext x; simp only [rho]; push_cast; rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun y _ => by ring
  rw [this, integral_finsetSum _ fun y _ => hint y]
  simp only [integral_const_mul, integral_step_exp _ ht]
  have hP : ∑ y, (F.P j y : ℂ) = 1 := by exact_mod_cast F.Psum j
  have hc : (↑t * I : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast ht) I_ne_zero
  simp only [phi]
  have hs : ∑ y, (F.P j y : ℂ) * (Complex.exp (↑t * I * F.X j y) - 1) =
      ∑ y, (F.P j y : ℂ) * Complex.exp (↑t * I * F.X j y) - 1 := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hP]
  rw [← hs, Finset.sum_div, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  ring


theorem integral_step_law (n : ℕ) (c x : ℝ) :
    ∫ a, step c (x - a) ∂(F.law n) = F.G n (x - c) - F.G n x := by
  have e : ∀ c' : ℝ, (fun a => (Ici c').indicator (1 : ℝ → ℝ) (x - a)) =
      (Iic (x - c')).indicator 1 := fun c' => by
    funext a; simp only [indicator, mem_Ici, mem_Iic, Pi.one_apply]
    congr 1; exact propext ⟨fun h => by linarith, fun h => by linarith⟩
  have hi : ∀ c', Integrable (fun a => (Ici c').indicator (1 : ℝ → ℝ) (x - a)) (F.law n) :=
    fun c' => by rw [e]; exact (integrable_const 1).indicator measurableSet_Iic
  simp only [step]
  rw [integral_sub (hi c) (hi 0), e, e, integral_indicator_one measurableSet_Iic,
    integral_indicator_one measurableSet_Iic, ← F.G_eq_law, ← F.G_eq_law, sub_zero]

theorem integral_rho_law (n : ℕ) (j) (x : ℝ) :
    ∫ a, F.rho j (x - a) ∂(F.law n) = F.expect j (F.G n) x - F.G n x := by
  simp only [rho]
  rw [integral_finsetSum _ fun y _ => (by
    have : Integrable (fun a => step (F.X j y) (x - a)) (F.law n) :=
      Integrable.of_bound (C := 1) ((measurable_step _).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
        (ae_of_all _ fun a => by
          have := abs_step_le (F.X j y) (x - a)
          rw [Real.norm_eq_abs]; refine this.trans ?_
          simp only [indicator]; split_ifs <;> norm_num)
    exact this.const_mul _)]
  simp only [integral_const_mul, integral_step_law, expect, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, F.Psum j, one_mul]

/-- `R_{jk} = E_j G_n - E_k G_n`. -/
def R (n : ℕ) (j k : Fin F.nA) (x : ℝ) : ℝ := F.expect j (F.G n) x - F.expect k (F.G n) x

theorem abs_rho_le (j) (x : ℝ) : |F.rho j x| ≤ (Icc (-F.M) F.M).indicator 1 x := by
  simp only [rho]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ y, |F.P j y * step (F.X j y) x| ≤ F.P j y * (Icc (-F.M) F.M).indicator 1 x := fun y => by
    rw [abs_mul, abs_of_pos (F.Ppos j y)]
    refine mul_le_mul_of_nonneg_left ((abs_step_le _ _).trans ?_) (F.Ppos j y).le
    have h := F.abs_X_le j y
    exact indicator_le_indicator_of_subset (Icc_subset_Icc (by linarith) h)
      (fun _ => zero_le_one) x
  refine (Finset.sum_le_sum fun y _ => this y).trans ?_
  rw [← Finset.sum_mul, F.Psum j, one_mul]

theorem abs_rho_le_one (j) (x : ℝ) : |F.rho j x| ≤ 1 :=
  (F.abs_rho_le j x).trans (by simp only [indicator]; split_ifs <;> norm_num)

theorem integrable_rho_law (n : ℕ) (j) (x : ℝ) : Integrable (fun a => F.rho j (x - a)) (F.law n) :=
  Integrable.of_bound (C := 1) ((F.measurable_rho j).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact F.abs_rho_le_one j _)

theorem R_eq (n : ℕ) (j k) (x : ℝ) :
    F.R n j k x = ∫ a, (F.rho j - F.rho k) (x - a) ∂(F.law n) := by
  simp only [Pi.sub_apply]
  rw [integral_sub (F.integrable_rho_law n j x) (F.integrable_rho_law n k x),
    integral_rho_law, integral_rho_law, R]
  ring

/-- **Fourier transform of `R_{jk}`**:
`∫ R(x) e^{itx} dx = μ̂_n(t) · (-(φ_j(t) - φ_k(t)) / (it))`. -/
theorem fourier_R (n : ℕ) (j k) {t : ℝ} (ht : t ≠ 0) :
    ∫ x, (F.R n j k x : ℂ) * Complex.exp (↑t * I * x) =
      (∫ a, Complex.exp (↑t * I * a) ∂(F.law n)) * (-((F.phi j t - F.phi k t) / (↑t * I))) := by
  set ρ := F.rho j - F.rho k
  have hρm : Measurable ρ := (F.measurable_rho j).sub (F.measurable_rho k)
  have hρi : Integrable ρ := (F.integrable_rho j).sub (F.integrable_rho k)
  set f : ℝ → ℝ → ℂ := fun x a => (ρ (x - a) : ℂ) * Complex.exp (↑t * I * x)
  have hnorm : ∀ u : ℝ, ‖Complex.exp (↑t * I * u)‖ = 1 := fun u => by
    rw [show (↑t * I * ↑u : ℂ) = ↑(t * u) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have hfm : AEStronglyMeasurable (Function.uncurry f) ((volume : Measure ℝ).prod (F.law n)) := by
    refine (Measurable.mul ?_ ?_).aestronglyMeasurable
    · exact Complex.measurable_ofReal.comp (hρm.comp (measurable_fst.sub measurable_snd))
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (↑t * I * x)).measurable.comp measurable_fst
  have hsec : ∀ a, Integrable (fun x => f x a) := fun a => by
    refine Integrable.mul_bdd (c := 1) ?_ ?_ ?_
    · exact (hρi.comp_sub_right a).ofReal
    · exact (by fun_prop : Continuous fun x : ℝ => Complex.exp (↑t * I * x)).aestronglyMeasurable
    · exact ae_of_all _ fun x => (hnorm x).le
  have hint : Integrable (Function.uncurry f) ((volume : Measure ℝ).prod (F.law n)) := by
    rw [integrable_prod_iff' hfm]
    refine ⟨ae_of_all _ hsec, ?_⟩
    show Integrable (fun a => ∫ x, ‖f x a‖) _
    have : (fun a => ∫ x, ‖f x a‖) = fun _ => ∫ x, ‖(ρ x : ℂ)‖ := by
      funext a
      simp only [f, norm_mul, hnorm, mul_one]
      exact integral_sub_right_eq_self (fun x => ‖(ρ x : ℂ)‖) a
    rw [this]; exact integrable_const _
  have hR : ∀ x, (F.R n j k x : ℂ) * Complex.exp (↑t * I * x) = ∫ a, f x a ∂(F.law n) := fun x => by
    rw [F.R_eq]
    show ((∫ a, ρ (x - a) ∂(F.law n) : ℝ) : ℂ) * _ = _
    rw [← integral_complex_ofReal, ← integral_mul_const]
  simp_rw [hR]
  rw [integral_integral_swap hint, ← integral_mul_const]
  refine integral_congr_ae (ae_of_all _ fun a => ?_)
  have h1 : ∫ x, f x a = ∫ x, (ρ x : ℂ) * Complex.exp (↑t * I * (x + a)) := by
    have := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun x : ℝ => (ρ x : ℂ) * Complex.exp (↑t * I * ((x : ℝ) + a : ℝ))) a
    simp only [sub_add_cancel] at this
    push_cast at this
    exact this
  simp only at h1 ⊢
  rw [h1]
  have h2 : (fun x : ℝ => (ρ x : ℂ) * Complex.exp (↑t * I * (↑x + ↑a))) =
      fun x => Complex.exp (↑t * I * a) * ((F.rho j x : ℂ) * Complex.exp (↑t * I * x) -
        (F.rho k x : ℂ) * Complex.exp (↑t * I * x)) := by
    funext x; simp only [ρ, Pi.sub_apply]; push_cast
    rw [show (↑t * I * (↑x + ↑a) : ℂ) = ↑t * I * x + ↑t * I * a by ring, Complex.exp_add]; ring
  have hi : ∀ i, Integrable fun x => (F.rho i x : ℂ) * Complex.exp (↑t * I * x) := fun i =>
    Integrable.mul_bdd (c := 1) (F.integrable_rho i).ofReal
      (by fun_prop : Continuous fun x : ℝ => Complex.exp (↑t * I * x)).aestronglyMeasurable
      (ae_of_all _ fun x => (hnorm x).le)
  rw [h2, integral_const_mul, integral_sub (hi j) (hi k), F.fourier_rho j ht, F.fourier_rho k ht]
  ring


/-- `∫ |R_{jk}| ≥ |μ̂_n(t)| |φ_j(t) - φ_k(t)| / |t|`. -/
theorem integral_abs_R_ge (n : ℕ) (j k) {t : ℝ} (ht : t ≠ 0) :
    ‖∫ a, Complex.exp (↑t * I * a) ∂(F.law n)‖ * ‖F.phi j t - F.phi k t‖ / |t| ≤
      ∫ x, |F.R n j k x| := by
  have hnorm : ∀ u : ℝ, ‖Complex.exp (↑t * I * u)‖ = 1 := fun u => by
    rw [show (↑t * I * ↑u : ℂ) = ↑(t * u) * I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  have h := norm_integral_le_integral_norm (μ := (volume : Measure ℝ))
    (fun x => (F.R n j k x : ℂ) * Complex.exp (↑t * I * x))
  rw [F.fourier_R n j k ht] at h
  simp only [norm_mul, hnorm, mul_one, Complex.norm_real, Real.norm_eq_abs, norm_neg, norm_div,
    Complex.norm_I] at h
  calc _ = ‖∫ a, Complex.exp (↑t * I * a) ∂(F.law n)‖ * (‖F.phi j t - F.phi k t‖ / |t|) := by ring
    _ ≤ _ := h

/-! ## The characteristic function of `μ_n` near zero -/

theorem exp_neg_nine_half : Real.exp (-(9 / 2)) ≤ 1 / 14 := by
  have h1 : (5 / 2 : ℝ) ≤ Real.exp (3 / 2) := by linarith [Real.add_one_le_exp (3 / 2 : ℝ)]
  have h3 : Real.exp (9 / 2) = Real.exp (3 / 2) ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have : (14 : ℝ) ≤ Real.exp (9 / 2) := by
    rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num) h1 3]
  rw [Real.exp_neg]
  exact inv_le_of_inv_le₀ (by norm_num) (by simpa using this)

/-- `|μ̂_n(t)| ≥ 1/2` at `t = 1/(6 M √n)`. -/
theorem norm_charFun_ge (hc : F.Centered) (hM : 0 < F.M) {n : ℕ} (hn : 0 < n) :
    1 / 2 ≤ ‖∫ a, Complex.exp (↑(1 / (6 * F.M * Real.sqrt n)) * I * a) ∂(F.law n)‖ := by
  set t := 1 / (6 * F.M * Real.sqrt n)
  set K := 3 * F.M * Real.sqrt n
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have ht : 0 < t := by positivity
  have hK : 0 < K := by positivity
  have htK : t * K = 1 / 2 := by simp only [t, K]; field_simp; ring
  -- real part
  have hre : (∫ a, Complex.exp (↑t * I * a) ∂(F.law n)).re = ∫ a, Real.cos (t * a) ∂(F.law n) := by
    rw [← RCLike.re_eq_complex_re, ← integral_re]
    · congr 1; funext a
      rw [show (↑t * I * ↑a : ℂ) = ↑(t * a) * I by push_cast; ring]
      exact Complex.exp_ofReal_mul_I_re _
    · exact Integrable.of_bound (C := 1) (by fun_prop : Continuous fun a : ℝ =>
        Complex.exp (↑t * I * a)).aestronglyMeasurable (ae_of_all _ fun a => by
          rw [show (↑t * I * ↑a : ℂ) = ↑(t * a) * I by push_cast; ring,
            Complex.norm_exp_ofReal_mul_I])
  set S := Ioc (-K) K
  have hS : MeasurableSet S := measurableSet_Ioc
  -- lower bound on cos
  have hcos : ∀ a, 3 / 4 - 7 / 4 * Sᶜ.indicator 1 a ≤ Real.cos (t * a) := fun a => by
    by_cases ha : a ∈ S
    · have hin : a ∉ Sᶜ := fun h => h ha
      simp only [indicator_of_notMem hin, mul_zero, sub_zero]
      have hta : |t * a| ≤ 1 / 2 := by
        rw [abs_mul, abs_of_pos ht, ← htK]
        exact mul_le_mul_of_nonneg_left (abs_le.2 ⟨ha.1.le, ha.2⟩) ht.le
      have := Real.one_sub_sq_div_two_le_cos (x := t * a)
      have h2 : (t * a) ^ 2 ≤ 1 / 4 := by
        rw [← sq_abs]; nlinarith [abs_nonneg (t * a)]
      linarith
    · simp only [indicator_of_mem (show a ∈ Sᶜ from ha), Pi.one_apply]
      linarith [Real.neg_one_le_cos (t * a)]
  have hint1 : Integrable (fun a => 3 / 4 - 7 / 4 * Sᶜ.indicator (1 : ℝ → ℝ) a) (F.law n) :=
    (integrable_const _).sub (((integrable_const 1).indicator hS.compl).const_mul _)
  have hint2 : Integrable (fun a => Real.cos (t * a)) (F.law n) :=
    Integrable.of_bound (C := 1) (by fun_prop : Continuous fun a : ℝ => Real.cos (t * a)).aestronglyMeasurable
      (ae_of_all _ fun a => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have hmono := integral_mono hint1 hint2 hcos
  rw [integral_sub (integrable_const _) (((integrable_const 1).indicator hS.compl).const_mul _),
    integral_const_mul, integral_indicator_one hS.compl] at hmono
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at hmono
  -- the mass outside `S`
  have hSc : (F.law n).real Sᶜ = 1 - (F.G n K - F.G n (-K)) := by
    rw [measureReal_compl hS, probReal_univ]
    congr 1
    simp only [Measure.real, law, S]
    rw [StieltjesFunction.measure_Ioc]
    exact ENNReal.toReal_ofReal (sub_nonneg.2 ((F.G_cdf n).1 (show -K ≤ K by linarith)))
  have hup := F.G_upper_tail hc hn (x := 3 * F.M) (by positivity)
  have hlo := F.G_lower_tail hc hn (x := 3 * F.M) (by positivity)
  have hE : (3 * F.M) ^ 2 / (2 * F.M ^ 2) = 9 / 2 := by field_simp; ring
  rw [hE] at hup hlo
  have e9 := exp_neg_nine_half
  have hK' : 3 * F.M * Real.sqrt n = K := rfl
  rw [hK'] at hup hlo
  have : 1 / 2 ≤ (∫ a, Complex.exp (↑t * I * a) ∂(F.law n)).re := by
    rw [hre]; rw [hSc] at hmono; linarith
  exact this.trans (Complex.re_le_norm _)


/-! ## The characteristic functions of two actions near zero -/

/-- Third moment of the centered information of action `j`. -/
def m3 (j : Fin F.nA) : ℝ := ∑ y, F.P j y * F.X j y ^ 3

theorem phi_poly (hc : F.Centered) (j) (t : ℝ) :
    ∑ y, (F.P j y : ℂ) * ∑ m ∈ Finset.range 4, (↑t * I * F.X j y) ^ m / (m.factorial : ℂ) =
      1 + (↑t * I) ^ 2 / 2 * (F.sig2 j : ℂ) + (↑t * I) ^ 3 / 6 * (F.m3 j : ℂ) := by
  have e : ∀ y, (F.P j y : ℂ) * ∑ m ∈ Finset.range 4, (↑t * I * F.X j y) ^ m / (m.factorial : ℂ) =
      (F.P j y : ℂ) + (↑t * I) * ((F.P j y * F.X j y : ℝ) : ℂ) +
        (↑t * I) ^ 2 / 2 * ((F.P j y * F.X j y ^ 2 : ℝ) : ℂ) +
        (↑t * I) ^ 3 / 6 * ((F.P j y * F.X j y ^ 3 : ℝ) : ℂ) := fun y => by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    push_cast; ring
  simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 : ∑ y, (F.P j y : ℂ) = 1 := by exact_mod_cast F.Psum j
  have h2 : ∑ y, ((F.P j y * F.X j y : ℝ) : ℂ) = 0 := by exact_mod_cast hc j
  have h3 : ∑ y, ((F.P j y * F.X j y ^ 2 : ℝ) : ℂ) = (F.sig2 j : ℂ) := by
    simp only [sig2]; push_cast; rfl
  have h4 : ∑ y, ((F.P j y * F.X j y ^ 3 : ℝ) : ℂ) = (F.m3 j : ℂ) := by
    simp only [m3]; push_cast; rfl
  rw [h1, h2, h3, h4]; ring

theorem phi_remainder (j) {t : ℝ} (ht : |t| * F.M ≤ 1) :
    ‖F.phi j t - ∑ y, (F.P j y : ℂ) * ∑ m ∈ Finset.range 4, (↑t * I * F.X j y) ^ m /
        (m.factorial : ℂ)‖ ≤ (|t| * F.M) ^ 4 * (5 / 96) := by
  simp only [phi, ← Finset.sum_sub_distrib, ← mul_sub]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ y, ‖(F.P j y : ℂ) * (Complex.exp (↑t * I * F.X j y) -
      ∑ m ∈ Finset.range 4, (↑t * I * F.X j y) ^ m / (m.factorial : ℂ))‖ ≤
      F.P j y * ((|t| * F.M) ^ 4 * (5 / 96)) := fun y => by
    have hn : ‖(↑t * I * F.X j y : ℂ)‖ = |t| * |F.X j y| := by
      simp [Complex.norm_real]
    have hX := F.abs_X_le j y
    have hle : ‖(↑t * I * F.X j y : ℂ)‖ ≤ |t| * F.M := by
      rw [hn]; exact mul_le_mul_of_nonneg_left hX (abs_nonneg t)
    have := Complex.exp_bound (hle.trans ht) (n := 4) (by norm_num)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (F.Ppos j y)]
    refine mul_le_mul_of_nonneg_left (this.trans ?_) (F.Ppos j y).le
    norm_num [Nat.factorial]
    rw [← hn]; exact pow_le_pow_left₀ (norm_nonneg _) hle 4
  refine (Finset.sum_le_sum fun y _ => hb y).trans ?_
  rw [← Finset.sum_mul, F.Psum j, one_mul]

/-- **Third-order separation of characteristic functions.** If actions `j, k` have equal
variances, then for `|t| M ≤ 1`,
`|φ_j(t) - φ_k(t)| ≥ |t|³ |m₃(j) - m₃(k)| / 6 - (5/48) (|t| M)⁴`. -/
theorem phi_sub_ge (hc : F.Centered) {j k} (hσ : F.sig2 j = F.sig2 k) {t : ℝ}
    (ht : |t| * F.M ≤ 1) :
    |t| ^ 3 * |F.m3 j - F.m3 k| / 6 - (|t| * F.M) ^ 4 * (5 / 48) ≤ ‖F.phi j t - F.phi k t‖ := by
  set Tj := ∑ y, (F.P j y : ℂ) * ∑ m ∈ Finset.range 4, (↑t * I * F.X j y) ^ m / (m.factorial : ℂ)
  set Tk := ∑ y, (F.P k y : ℂ) * ∑ m ∈ Finset.range 4, (↑t * I * F.X k y) ^ m / (m.factorial : ℂ)
  have hT : Tj - Tk = (↑t * I) ^ 3 / 6 * ((F.m3 j - F.m3 k : ℝ) : ℂ) := by
    simp only [Tj, Tk, F.phi_poly hc, hσ]; push_cast; ring
  have hnT : ‖Tj - Tk‖ = |t| ^ 3 * |F.m3 j - F.m3 k| / 6 := by
    rw [hT, norm_mul, norm_div, norm_pow, norm_mul, Complex.norm_real, Complex.norm_real,
      Complex.norm_I]
    simp [Real.norm_eq_abs]; ring
  have rj := F.phi_remainder j ht
  have rk := F.phi_remainder k ht
  have : ‖Tj - Tk‖ ≤ ‖F.phi j t - F.phi k t‖ + ‖F.phi j t - Tj‖ + ‖F.phi k t - Tk‖ := by
    have e : Tj - Tk = (F.phi j t - F.phi k t) - (F.phi j t - Tj) + (F.phi k t - Tk) := by ring
    rw [e]
    exact (norm_add_le _ _).trans (by linarith [norm_sub_le (F.phi j t - F.phi k t) (F.phi j t - Tj)])
  linarith


theorem M_pos_of_m3 {j k} (h3 : F.m3 j ≠ F.m3 k) : 0 < F.M := by
  rcases F.M_nonneg.lt_or_eq with h | h
  · exact h
  · exfalso; apply h3
    have : ∀ i y, F.X i y = 0 := fun i y => abs_nonpos_iff.1 (h ▸ F.abs_X_le i y)
    simp [m3, this]

/-- **Fourier lower bound.** If two actions `j, k` have equal variances but different third
moments, then `∫ |E_j G_n - E_k G_n| ≥ c / n` for all large `n`. -/
theorem integral_abs_R_lower (hc : F.Centered) {j k} (hσ : F.sig2 j = F.sig2 k)
    (h3 : F.m3 j ≠ F.m3 k) :
    ∃ c > 0, ∃ N : ℕ, ∀ n ≥ N, c / n ≤ ∫ x, |F.R n j k x| := by
  have hM := F.M_pos_of_m3 h3
  set δ := |F.m3 j - F.m3 k|
  have hδ : 0 < δ := abs_pos.2 (sub_ne_zero.2 h3)
  refine ⟨δ / (864 * F.M ^ 2), by positivity, ⌈(5 * F.M ^ 3 / (24 * δ)) ^ 2⌉₊ + 1, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : 0 < n := by omega
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have hs1 : 1 ≤ Real.sqrt n := by rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hn1
  have hsN : 5 * F.M ^ 3 / (24 * δ) ≤ Real.sqrt n := by
    rw [← Real.sqrt_sq (show 0 ≤ 5 * F.M ^ 3 / (24 * δ) by positivity)]
    refine Real.sqrt_le_sqrt ?_
    have := Nat.le_ceil ((5 * F.M ^ 3 / (24 * δ)) ^ 2)
    have h2 : ((⌈(5 * F.M ^ 3 / (24 * δ)) ^ 2⌉₊ : ℕ) : ℝ) ≤ n := by exact_mod_cast (by omega)
    linarith
  set t := 1 / (6 * F.M * Real.sqrt n)
  have ht : 0 < t := by positivity
  have htM : |t| * F.M ≤ 1 := by
    rw [abs_of_pos ht]; simp only [t]
    rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
    nlinarith
  have hphi := F.phi_sub_ge hc hσ htM
  have hchar := F.norm_charFun_ge hc hM hn0
  have hR := F.integral_abs_R_ge n j k ht.ne'
  rw [abs_of_pos ht] at hphi hR
  -- `(t M)^4 (5/48) ≤ t³ δ / 12`
  have hsmall : (t * F.M) ^ 4 * (5 / 48) ≤ t ^ 3 * δ / 12 := by
    have : t * F.M ^ 4 * 5 ≤ 4 * δ := by
      simp only [t]
      rw [div_mul_eq_mul_div, one_mul, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hsN (show 0 ≤ 24 * δ by positivity)
      rw [mul_div_cancel₀ _ (by positivity)] at this
      nlinarith [sq_nonneg F.M]
    have e : (t * F.M) ^ 4 * (5 / 48) = t ^ 3 * (t * F.M ^ 4 * 5) / 48 := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left this (show 0 ≤ t ^ 3 by positivity)
    linarith
  have hphi2 : t ^ 3 * δ / 12 ≤ ‖F.phi j t - F.phi k t‖ := by linarith
  have key : 1 / 2 * (t ^ 3 * δ / 12) / t ≤ ∫ x, |F.R n j k x| := by
    refine le_trans ?_ hR
    exact div_le_div_of_nonneg_right (mul_le_mul hchar hphi2 (by positivity) (norm_nonneg _)) ht.le
  have e2 : 1 / 2 * (t ^ 3 * δ / 12) / t = δ / (864 * F.M ^ 2) / n := by
    simp only [t]; field_simp
    rw [Real.sq_sqrt (by linarith)]; ring
  rwa [e2] at key

end IncFamily
end CausalSpectrum.Sqrt

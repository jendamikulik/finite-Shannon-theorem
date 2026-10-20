/-
Stage 2 of the logarithmic-coefficient formalization: the standard Gaussian density, its
first two derivatives, their exact `L¹` norms, and the scaling rules for `L¹` norms of
derivatives of rescaled profiles `g((x - m)/s)`.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral

open MeasureTheory Set Filter Topology Real

namespace CausalSpectrum.LogGauss

/-- The standard Gaussian density `φ(z) = e^{-z²/2}/√(2π)`. -/
noncomputable def phi (z : ℝ) : ℝ := (√(2 * π))⁻¹ * exp (-(z ^ 2 / 2))

/-- `φ'(z) = -z φ(z)`. -/
noncomputable def dphi (z : ℝ) : ℝ := -z * phi z

/-- `φ''(z) = (z² - 1) φ(z)`. -/
noncomputable def ddphi (z : ℝ) : ℝ := (z ^ 2 - 1) * phi z

theorem phi_pos (z : ℝ) : 0 < phi z :=
  mul_pos (inv_pos.2 (sqrt_pos.2 (by positivity))) (exp_pos _)

theorem hasDerivAt_phi (z : ℝ) : HasDerivAt phi (dphi z) z := by
  have h : HasDerivAt (fun z : ℝ => -(z ^ 2 / 2)) (-z) z := by
    have := ((hasDerivAt_pow 2 z).div_const 2).neg
    convert this using 1; push_cast; ring
  have := (h.exp).const_mul (√(2 * π))⁻¹
  unfold dphi phi; convert this using 1; ring

theorem hasDerivAt_dphi (z : ℝ) : HasDerivAt dphi (ddphi z) z := by
  have := ((hasDerivAt_id z).neg).mul (hasDerivAt_phi z)
  have e : dphi = fun z => -id z * phi z := funext fun z => by simp [dphi]
  rw [e]; convert this using 1; simp only [ddphi, dphi, Pi.neg_apply, id]; ring

theorem continuous_phi : Continuous phi :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_phi z).continuousAt

theorem continuous_dphi : Continuous dphi :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_dphi z).continuousAt

theorem continuous_ddphi : Continuous ddphi := by
  unfold ddphi; exact (by fun_prop : Continuous fun z : ℝ => z ^ 2 - 1).mul continuous_phi

private theorem ex (z : ℝ) : exp (-(z ^ 2 / 2)) = exp (-(1 / 2) * z ^ 2) := by ring_nf

theorem integrable_phi : Integrable phi := by
  have := (integrable_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul (√(2 * π))⁻¹
  refine this.congr (ae_of_all _ fun z => ?_); simp [phi, ex]

theorem integrable_dphi : Integrable dphi := by
  have := ((integrable_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)).const_mul
    (-(√(2 * π))⁻¹))
  refine this.congr (ae_of_all _ fun z => ?_); simp only [dphi, phi, ex]; ring

theorem integrable_ddphi : Integrable ddphi := by
  have h2 := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    (s := 2) (by norm_num)).const_mul (√(2 * π))⁻¹
  have := h2.sub integrable_phi
  refine this.congr (ae_of_all _ fun z => ?_)
  simp only [Pi.sub_apply, ddphi, phi, ex, Real.rpow_two]; ring

theorem tendsto_phi_atTop : Tendsto phi atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun z _ => hasDerivAt_phi z)
    integrable_dphi.integrableOn integrable_phi.integrableOn
theorem tendsto_phi_atBot : Tendsto phi atBot (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun z _ => hasDerivAt_phi z)
    integrable_dphi.integrableOn integrable_phi.integrableOn
theorem tendsto_dphi_atTop : Tendsto dphi atTop (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun z _ => hasDerivAt_dphi z)
    integrable_ddphi.integrableOn integrable_dphi.integrableOn
theorem tendsto_dphi_atBot : Tendsto dphi atBot (𝓝 0) :=
  tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun z _ => hasDerivAt_dphi z)
    integrable_ddphi.integrableOn integrable_dphi.integrableOn

/-- `∫ φ = 1`. -/
theorem integral_phi : ∫ z, phi z = 1 := by
  simp only [phi, ex]
  rw [integral_const_mul, integral_gaussian]
  have : π / (1 / 2) = 2 * π := by ring
  rw [this, inv_mul_cancel₀ (sqrt_pos.2 (by positivity)).ne']

theorem integral_dphi : ∫ z, dphi z = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_phi integrable_dphi tendsto_phi_atBot
    tendsto_phi_atTop]; simp

theorem integral_ddphi : ∫ z, ddphi z = 0 := by
  rw [integral_of_hasDerivAt_of_tendsto hasDerivAt_dphi integrable_ddphi tendsto_dphi_atBot
    tendsto_dphi_atTop]; simp

/-- `∫ |φ'| = 2 φ(0)`. -/
theorem integral_abs_dphi : ∫ z, |dphi z| = 2 * phi 0 := by
  -- `|φ'| = φ' + 2 · 1_{z>0} z φ`
  have hsplit : ∀ z, |dphi z| = dphi z + 2 * (Ioi (0:ℝ)).indicator (fun z => -dphi z) z := by
    intro z
    by_cases hz : 0 < z
    · have : dphi z < 0 := by simp only [dphi]; nlinarith [phi_pos z]
      rw [indicator_of_mem (by exact hz), abs_of_neg this]; ring
    · have : 0 ≤ dphi z := by simp only [dphi]; nlinarith [phi_pos z]
      rw [indicator_of_notMem (by simpa using hz), abs_of_nonneg this]; ring
  have hI : IntegrableOn (fun z => -dphi z) (Ioi 0) := integrable_dphi.neg.integrableOn
  rw [integral_congr_ae (ae_of_all _ hsplit), integral_add integrable_dphi
    ((hI.integrable_indicator measurableSet_Ioi).const_mul 2), integral_dphi,
    integral_const_mul, integral_indicator measurableSet_Ioi]
  have hd : ∀ x ∈ Ioi (0:ℝ), HasDerivAt (fun z => -phi z) (-dphi x) x :=
    fun x _ => (hasDerivAt_phi x).neg
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (f := fun z => -phi z)
    continuous_phi.neg.continuousWithinAt hd hI (by simpa using tendsto_phi_atTop.neg)]
  ring

/-- `∫ |φ''| = 4 φ(1)`. -/
theorem integral_abs_ddphi : ∫ z, |ddphi z| = 4 * phi 1 := by
  have hsplit : ∀ z, |ddphi z| = ddphi z + 2 * (Icc (-1:ℝ) 1).indicator (fun z => -ddphi z) z := by
    intro z
    by_cases hz : z ∈ Icc (-1:ℝ) 1
    · have : ddphi z ≤ 0 := by
        simp only [ddphi]; apply mul_nonpos_of_nonpos_of_nonneg _ (phi_pos z).le
        obtain ⟨h1, h2⟩ := hz; nlinarith
      rw [indicator_of_mem hz, abs_of_nonpos this]; ring
    · have : 0 ≤ ddphi z := by
        simp only [ddphi]; apply mul_nonneg _ (phi_pos z).le
        simp only [mem_Icc, not_and_or, not_le] at hz
        rcases hz with h | h <;> nlinarith
      rw [indicator_of_notMem hz, abs_of_nonneg this]; ring
  have hI : IntegrableOn (fun z => -ddphi z) (Icc (-1) 1) := integrable_ddphi.neg.integrableOn
  rw [integral_congr_ae (ae_of_all _ hsplit), integral_add integrable_ddphi
    ((hI.integrable_indicator measurableSet_Icc).const_mul 2), integral_ddphi,
    integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun z => -dphi z)
    (fun x _ => (hasDerivAt_dphi x).neg) (integrable_ddphi.neg.intervalIntegrable)]
  have : phi (-1) = phi 1 := by simp [phi]
  simp only [dphi, this]; ring

/-! ### Scaling -/

/-- Translation and dilation of an `L¹` norm: `∫ |g((x - m)/s)| dx = s ∫ |g|` for `s > 0`. -/
theorem integral_abs_comp_affine (g : ℝ → ℝ) (m : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, |g ((x - m) / s)| = s * ∫ z, |g z| := by
  rw [integral_sub_right_eq_self (fun x => |g (x / s)|) m, Measure.integral_comp_div
    (fun z => |g z|) s, abs_of_pos hs, smul_eq_mul]

theorem hasDerivAt_comp_affine {g g' : ℝ → ℝ} (hg : ∀ z, HasDerivAt g (g' z) z) (m : ℝ)
    {s : ℝ} (x : ℝ) :
    HasDerivAt (fun x => g ((x - m) / s)) (g' ((x - m) / s) / s) x := by
  have h : HasDerivAt (fun x : ℝ => (x - m) / s) (1 / s) x :=
    ((hasDerivAt_id x).sub_const m).div_const s
  have := (hg ((x - m) / s)).comp x h
  rw [show g' ((x - m) / s) / s = g' ((x - m) / s) * (1 / s) by ring]; exact this

/-- **Gaussian derivative norms under scaling.** For the rescaled normal distribution
function `Φ((x-m)/s)` (`s > 0`), the first three `x`-derivatives `φ(z)/s`, `φ'(z)/s²` and
`φ''(z)/s³` (`z = (x-m)/s`) have `L¹` norms `1`, `2φ(0)/s` and `4φ(1)/s²`. -/
theorem gauss_scaled_norms (m : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫ x, |phi ((x - m) / s) / s| = 1) ∧
    (∫ x, |dphi ((x - m) / s) / s ^ 2| = 2 * phi 0 / s) ∧
    (∫ x, |ddphi ((x - m) / s) / s ^ 3| = 4 * phi 1 / s ^ 2) := by
  have k : ∀ (g : ℝ → ℝ) (k : ℕ), ∫ x, |g ((x - m) / s) / s ^ k| =
      s * (∫ z, |g z|) / s ^ k := by
    intro g k
    simp_rw [abs_div, abs_of_pos (pow_pos hs k)]
    rw [integral_div, integral_abs_comp_affine g m hs]
  refine ⟨?_, ?_, ?_⟩
  · have := k phi 1; simp only [pow_one] at this
    rw [this, integral_congr_ae (ae_of_all _ fun z => abs_of_pos (phi_pos z)), integral_phi]
    field_simp
  · rw [k dphi 2, integral_abs_dphi]; field_simp
  · rw [k ddphi 3, integral_abs_ddphi]; field_simp

end CausalSpectrum.LogGauss

/-
Stage 3 of the logarithmic-coefficient formalization: the explicit resonant corrector.

For real parameters `β ≤ α` (in the application `α = κ₊/(6v^{3/2})`, `β = κ₋/(6v^{3/2})`)
put
  `f(z) = min(-α φ''(z), -β φ''(z))`,  `a = ∫ f = -2(α-β) φ(1)`,
  `g = 2(aφ - f)`,  `J(z) = ∫_{-∞}^z g`,  `B(z) = φ(z) ∫_0^z J/φ`.
Then `B' + zB = J`, `B'' + zB' + B = g`, and `B, B', B''` (and `J`, `g`) are bounded by
polynomials times `φ`; in particular they are integrable.
-/
import CausalSeed.LogGauss

open MeasureTheory Set Filter Topology Real

namespace CausalSpectrum.LogGauss

/-! ### Polynomially weighted Gaussians -/

theorem integrable_pow_mul_phi (k : ℕ) : Integrable fun z => z ^ k * phi z := by
  have h := (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num)
    (s := (k : ℝ)) (by have := k.cast_nonneg (α := ℝ); linarith)).const_mul (√(2 * π))⁻¹
  refine h.congr (ae_of_all _ fun z => ?_)
  simp only [phi, Real.rpow_natCast]; rw [show -(1 / 2) * z ^ 2 = -(z ^ 2 / 2) by ring]; ring

theorem one_add_abs_pow_le (z : ℝ) (k : ℕ) : (1 + |z|) ^ k ≤ 2 ^ k * (1 + |z ^ k|) := by
  rw [abs_pow]
  rcases le_total |z| 1 with h | h
  · calc (1 + |z|) ^ k ≤ 2 ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ ≤ 2 ^ k * (1 + |z| ^ k) := le_mul_of_one_le_right (by positivity)
          (by linarith [pow_nonneg (abs_nonneg z) k])
  · calc (1 + |z|) ^ k ≤ (2 * |z|) ^ k := pow_le_pow_left₀ (by positivity) (by linarith) k
      _ = 2 ^ k * |z| ^ k := mul_pow _ _ _
      _ ≤ 2 ^ k * (1 + |z| ^ k) := by gcongr; linarith

/-- The weight `(1 + |z|)^k φ(z)` is integrable. -/
theorem integrable_wphi (k : ℕ) : Integrable fun z => (1 + |z|) ^ k * phi z := by
  have h : Integrable fun z => 2 ^ k * (phi z + |z ^ k * phi z|) :=
    (integrable_phi.add (integrable_pow_mul_phi k).abs).const_mul _
  refine h.mono' ((by fun_prop : Continuous fun z : ℝ => (1 + |z|) ^ k).mul
    continuous_phi).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  have hp := phi_pos z
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul, abs_of_pos hp]
  nlinarith [one_add_abs_pow_le z k]

theorem wphi_mono {z : ℝ} {k m : ℕ} (h : k ≤ m) :
    (1 + |z|) ^ k * phi z ≤ (1 + |z|) ^ m * phi z :=
  mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by linarith [abs_nonneg z]) h) (phi_pos z).le

theorem phi_ge_one {z : ℝ} (hz : |z| ≤ 1) : phi 1 ≤ phi z := by
  have : z ^ 2 ≤ 1 := by nlinarith [abs_nonneg z, sq_abs z]
  unfold phi
  exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by nlinarith)) (by positivity)

/-! ### The corrector -/

section Corrector
variable (α β : ℝ)

/-- The forcing `f(z) = min(-α φ''(z), -β φ''(z))`. -/
noncomputable def cf (z : ℝ) : ℝ := min (-α * ddphi z) (-β * ddphi z)

/-- `a = ∫ f`. -/
noncomputable def ca : ℝ := ∫ z, cf α β z

/-- `g = 2(aφ - f)`. -/
noncomputable def cg (z : ℝ) : ℝ := 2 * (ca α β * phi z - cf α β z)

/-- `J(z) = ∫_{-∞}^z g`. -/
noncomputable def cJ (z : ℝ) : ℝ := ∫ y in Iic z, cg α β y

/-- The corrector `B(z) = φ(z) ∫_0^z J/φ`. -/
noncomputable def cB (z : ℝ) : ℝ := phi z * ∫ y in (0:ℝ)..z, cJ α β y / phi y

/-- `B' = J - zB`. -/
noncomputable def cdB (z : ℝ) : ℝ := cJ α β z - z * cB α β z

/-- `B'' = g - B - zB'`. -/
noncomputable def cddB (z : ℝ) : ℝ := cg α β z - cB α β z - z * cdB α β z

theorem continuous_cf : Continuous (cf α β) := by
  unfold cf; exact (continuous_const.mul continuous_ddphi).min (continuous_const.mul continuous_ddphi)

theorem abs_cf_le (z : ℝ) : |cf α β z| ≤ (|α| + |β|) * |ddphi z| := by
  unfold cf
  have h1 : |-α * ddphi z| ≤ (|α| + |β|) * |ddphi z| := by
    rw [abs_mul, abs_neg]; gcongr; linarith [abs_nonneg β]
  have h2 : |-β * ddphi z| ≤ (|α| + |β|) * |ddphi z| := by
    rw [abs_mul, abs_neg]; gcongr; linarith [abs_nonneg α]
  rcases min_choice (-α * ddphi z) (-β * ddphi z) with h | h <;> rw [h] <;> assumption

theorem integrable_cf : Integrable (cf α β) :=
  (integrable_ddphi.abs.const_mul (|α| + |β|)).mono' (continuous_cf α β).aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using abs_cf_le α β z)

/-- `f = -α φ'' + (α - β) 1_{[-1,1]} φ''` when `β ≤ α`. -/
theorem cf_eq (h : β ≤ α) (z : ℝ) :
    cf α β z = -α * ddphi z + (α - β) * (Icc (-1:ℝ) 1).indicator ddphi z := by
  unfold cf
  by_cases hz : z ∈ Icc (-1:ℝ) 1
  · have : ddphi z ≤ 0 := by
      simp only [ddphi]; apply mul_nonpos_of_nonpos_of_nonneg _ (phi_pos z).le
      obtain ⟨h1, h2⟩ := hz; nlinarith
    rw [indicator_of_mem hz, min_eq_right (by nlinarith)]; ring
  · have : 0 ≤ ddphi z := by
      simp only [ddphi]; apply mul_nonneg _ (phi_pos z).le
      simp only [mem_Icc, not_and_or, not_le] at hz
      rcases hz with h | h <;> nlinarith
    rw [indicator_of_notMem hz, min_eq_left (by nlinarith)]; ring

/-- **The resonant mass.** `a = ∫ f = -2(α - β) φ(1)`. -/
theorem ca_eq (h : β ≤ α) : ca α β = -2 * (α - β) * phi 1 := by
  unfold ca
  have hI : IntegrableOn ddphi (Icc (-1) 1) := integrable_ddphi.integrableOn
  rw [integral_congr_ae (ae_of_all _ (cf_eq α β h)), integral_add
    (integrable_ddphi.const_mul _) ((hI.integrable_indicator measurableSet_Icc).const_mul _),
    integral_const_mul, integral_const_mul, integral_ddphi, integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hasDerivAt_dphi x)
      integrable_ddphi.intervalIntegrable]
  have : phi (-1) = phi 1 := by simp [phi]
  simp only [dphi, this]; ring

theorem continuous_cg : Continuous (cg α β) := by
  unfold cg; exact continuous_const.mul ((continuous_const.mul continuous_phi).sub (continuous_cf α β))

theorem integrable_cg : Integrable (cg α β) :=
  ((integrable_phi.const_mul _).sub (integrable_cf α β)).const_mul 2

/-- `∫ g = 0`. -/
theorem integral_cg : ∫ z, cg α β z = 0 := by
  unfold cg
  rw [integral_const_mul, integral_sub (integrable_phi.const_mul _) (integrable_cf α β),
    integral_const_mul, integral_phi]
  simp [ca]

theorem abs_cg_le : ∃ K, ∀ z, |cg α β z| ≤ K * ((1 + |z|) ^ 2 * phi z) := by
  refine ⟨2 * |ca α β| + 2 * (|α| + |β|), fun z => ?_⟩
  have hp := phi_pos z
  have h1 : |ddphi z| ≤ (1 + |z|) ^ 2 * phi z := by
    rw [ddphi, abs_mul, abs_of_pos hp]; gcongr
    rw [abs_le]; constructor <;> nlinarith [abs_nonneg z, sq_abs z]
  have h0 : phi z ≤ (1 + |z|) ^ 2 * phi z :=
    le_mul_of_one_le_left hp.le (one_le_pow₀ (by linarith [abs_nonneg z]))
  have := abs_cf_le α β z
  unfold cg
  calc |2 * (ca α β * phi z - cf α β z)| ≤ 2 * (|ca α β| * phi z + |cf α β z|) := by
        rw [abs_mul, abs_two]; gcongr
        refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_of_pos hp]
    _ ≤ _ := by nlinarith [abs_nonneg (ca α β), abs_nonneg α, abs_nonneg β]

/-! ### `J` -/

theorem cJ_eq (z : ℝ) : cJ α β z = cJ α β 0 + ∫ y in (0:ℝ)..z, cg α β y := by
  rw [← intervalIntegral.integral_Iic_sub_Iic (integrable_cg α β).integrableOn
    (integrable_cg α β).integrableOn]
  simp [cJ]

theorem hasDerivAt_cJ (z : ℝ) : HasDerivAt (cJ α β) (cg α β z) z := by
  have h := ((continuous_cg α β).integral_hasStrictDerivAt 0 z).hasDerivAt.const_add (cJ α β 0)
  have e : cJ α β = fun z => cJ α β 0 + ∫ y in (0:ℝ)..z, cg α β y := funext (cJ_eq α β)
  rw [e]; exact h

theorem continuous_cJ : Continuous (cJ α β) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_cJ α β z).continuousAt

theorem cJ_eq_neg_Ioi (z : ℝ) : cJ α β z = -∫ y in Ioi z, cg α β y := by
  have := intervalIntegral.integral_Iic_add_Ioi (b := z) (integrable_cg α β).integrableOn
    (integrable_cg α β).integrableOn
  rw [integral_cg] at this; unfold cJ; linarith

/-- Antiderivative of `y³ φ`: `(-(y² + 2) φ)' = y³ φ`. -/
theorem hasDerivAt_cube (y : ℝ) :
    HasDerivAt (fun y => -((y ^ 2 + 2) * phi y)) (y ^ 3 * phi y) y := by
  have := (((hasDerivAt_pow 2 y).add_const 2).mul (hasDerivAt_phi y)).neg
  convert this using 1; simp only [dphi]; push_cast; ring

theorem tendsto_cube_prim_atTop : Tendsto (fun y => -((y ^ 2 + 2) * phi y)) atTop (𝓝 0) := by
  have hint : Integrable fun y => -((y ^ 2 + 2) * phi y) := by
    have := ((integrable_pow_mul_phi 2).add (integrable_phi.const_mul 2)).neg
    refine this.congr (ae_of_all _ fun y => ?_); simp; ring
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := 0) (fun y _ => hasDerivAt_cube y)
    (integrable_pow_mul_phi 3).integrableOn hint.integrableOn

theorem tendsto_cube_prim_atBot : Tendsto (fun y => -((y ^ 2 + 2) * phi y)) atBot (𝓝 0) := by
  have hint : Integrable fun y => -((y ^ 2 + 2) * phi y) := by
    have := ((integrable_pow_mul_phi 2).add (integrable_phi.const_mul 2)).neg
    refine this.congr (ae_of_all _ fun y => ?_); simp; ring
  exact tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun y _ => hasDerivAt_cube y)
    (integrable_pow_mul_phi 3).integrableOn hint.integrableOn

/-- `∫_z^∞ y³ φ = (z² + 2) φ(z)`. -/
theorem integral_Ioi_cube (z : ℝ) : ∫ y in Ioi z, y ^ 3 * phi y = (z ^ 2 + 2) * phi z := by
  rw [integral_Ioi_of_hasDerivAt_of_tendsto (hasDerivAt_cube z).continuousAt.continuousWithinAt
    (fun y _ => hasDerivAt_cube y) (integrable_pow_mul_phi 3).integrableOn tendsto_cube_prim_atTop]
  ring

/-- `∫_{-∞}^z y³ φ = -(z² + 2) φ(z)`. -/
theorem integral_Iic_cube (z : ℝ) : ∫ y in Iic z, y ^ 3 * phi y = -((z ^ 2 + 2) * phi z) := by
  rw [integral_Iic_of_hasDerivAt_of_tendsto (hasDerivAt_cube z).continuousAt.continuousWithinAt
    (fun y _ => hasDerivAt_cube y) (integrable_pow_mul_phi 3).integrableOn tendsto_cube_prim_atBot]
  ring

/-- **Tail bound for `J`.** `|J(z)| ≤ K (1 + |z|)² φ(z)`. -/
theorem abs_cJ_le : ∃ K, ∀ z, |cJ α β z| ≤ K * ((1 + |z|) ^ 2 * phi z) := by
  obtain ⟨Kg, hKg⟩ := abs_cg_le α β
  have hKg0 : 0 ≤ Kg := by
    have := (abs_nonneg _).trans (hKg 0); have hp := phi_pos 0
    exact nonneg_of_mul_nonneg_left this (by positivity)
  set N := ∫ y, |cg α β y|
  refine ⟨max (8 * Kg) (N / phi 1), fun z => ?_⟩
  have hp := phi_pos z
  have hw : 0 ≤ (1 + |z|) ^ 2 * phi z := by positivity
  have hcube : ∀ y, 1 ≤ |y| → (1 + |y|) ^ 2 * phi y ≤ 4 * (|y| ^ 3 * phi y) := by
    intro y hy
    have : (1 + |y|) ^ 2 ≤ 4 * |y| ^ 3 := by
      have h2 : (1 + |y|) ^ 2 ≤ (2 * |y|) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
      have h3 : |y| ^ 2 ≤ |y| ^ 3 := pow_le_pow_right₀ hy (by norm_num)
      nlinarith
    nlinarith [phi_pos y]
  rcases le_or_gt 1 |z| with hz | hz
  · rcases le_or_gt 0 z with hz0 | hz0
    · -- right tail
      have hz1 : 1 ≤ z := by rwa [abs_of_nonneg hz0] at hz
      rw [cJ_eq_neg_Ioi, abs_neg]
      calc |∫ y in Ioi z, cg α β y| ≤ ∫ y in Ioi z, |cg α β y| := by
            simpa using norm_integral_le_integral_norm (μ := volume.restrict (Ioi z)) (cg α β)
        _ ≤ ∫ y in Ioi z, Kg * (4 * (y ^ 3 * phi y)) := by
            refine setIntegral_mono_on (integrable_cg α β).abs.integrableOn
              ((integrable_pow_mul_phi 3).const_mul 4 |>.const_mul Kg).integrableOn
              measurableSet_Ioi fun y hy => ?_
            have hy1 : 1 ≤ y := hz1.trans (le_of_lt hy)
            have := hcube y (by rw [abs_of_nonneg (by linarith)]; exact hy1)
            have e : |y| = y := abs_of_nonneg (by linarith)
            refine (hKg y).trans ?_
            have := mul_le_mul_of_nonneg_left this hKg0
            rw [e] at this ⊢; exact this
        _ = Kg * 4 * ((z ^ 2 + 2) * phi z) := by
            rw [integral_const_mul, integral_const_mul, integral_Ioi_cube]; ring
        _ ≤ 8 * Kg * ((1 + |z|) ^ 2 * phi z) := by
            have : z ^ 2 + 2 ≤ 2 * (1 + |z|) ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
            have := mul_le_mul_of_nonneg_right this hp.le
            nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
    · -- left tail
      have hz1 : z ≤ -1 := by rw [abs_of_neg hz0] at hz; linarith
      unfold cJ
      calc |∫ y in Iic z, cg α β y| ≤ ∫ y in Iic z, |cg α β y| := by
            simpa using norm_integral_le_integral_norm (μ := volume.restrict (Iic z)) (cg α β)
        _ ≤ ∫ y in Iic z, -(Kg * (4 * (y ^ 3 * phi y))) := by
            refine setIntegral_mono_on (integrable_cg α β).abs.integrableOn
              ((integrable_pow_mul_phi 3).const_mul 4 |>.const_mul Kg).neg.integrableOn
              measurableSet_Iic fun y hy => ?_
            have hy1 : y ≤ -1 := (show y ≤ z from hy).trans hz1
            have := hcube y (by rw [abs_of_neg (by linarith)]; linarith)
            have e : -(Kg * (4 * (y ^ 3 * phi y))) = Kg * (4 * (|y| ^ 3 * phi y)) := by
              rw [abs_of_neg (by linarith : y < 0)]; ring
            rw [e]; exact (hKg y).trans (mul_le_mul_of_nonneg_left this hKg0)
        _ = Kg * 4 * ((z ^ 2 + 2) * phi z) := by
            rw [integral_neg, integral_const_mul, integral_const_mul, integral_Iic_cube]; ring
        _ ≤ 8 * Kg * ((1 + |z|) ^ 2 * phi z) := by
            have : z ^ 2 + 2 ≤ 2 * (1 + |z|) ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
            have := mul_le_mul_of_nonneg_right this hp.le
            nlinarith
        _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hw
  · -- middle
    have h1 : |cJ α β z| ≤ N := by
      unfold cJ
      calc |∫ y in Iic z, cg α β y| ≤ ∫ y in Iic z, |cg α β y| := by
            simpa using norm_integral_le_integral_norm (μ := volume.restrict (Iic z)) (cg α β)
        _ ≤ N := setIntegral_le_integral (integrable_cg α β).abs (ae_of_all _ fun _ => abs_nonneg _)
    have hN : 0 ≤ N := integral_nonneg fun _ => abs_nonneg _
    have hp1 := phi_pos 1
    have hge := phi_ge_one hz.le
    calc |cJ α β z| ≤ N := h1
      _ ≤ N / phi 1 * phi z := by
          rw [div_mul_eq_mul_div, le_div_iff₀ hp1]; exact mul_le_mul_of_nonneg_left hge hN
      _ ≤ N / phi 1 * ((1 + |z|) ^ 2 * phi z) := by
          gcongr; exact le_mul_of_one_le_left hp.le (one_le_pow₀ (by linarith [abs_nonneg z]))
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hw

/-! ### `B` and its derivatives -/

theorem continuous_cJ_div : Continuous fun y => cJ α β y / phi y :=
  (continuous_cJ α β).div continuous_phi fun y => (phi_pos y).ne'

theorem hasDerivAt_cB (z : ℝ) : HasDerivAt (cB α β) (cdB α β z) z := by
  have hI := ((continuous_cJ_div α β).integral_hasStrictDerivAt 0 z).hasDerivAt
  have := (hasDerivAt_phi z).mul hI
  unfold cB cdB; convert this using 1
  simp only [dphi, cB]; rw [mul_div_cancel₀ _ (phi_pos z).ne']; ring

theorem hasDerivAt_cdB (z : ℝ) : HasDerivAt (cdB α β) (cddB α β z) z := by
  have := (hasDerivAt_cJ α β z).sub ((hasDerivAt_id z).mul (hasDerivAt_cB α β z))
  have e : cdB α β = fun z => cJ α β z - id z * cB α β z := rfl
  rw [e]; convert this using 1; simp only [cddB, cdB, id]; ring

/-- `B' + zB = J`. -/
theorem cB_first_order (z : ℝ) : cdB α β z + z * cB α β z = cJ α β z := by
  unfold cdB; ring

/-- **The corrector ODE.** `B'' + zB' + B = 2(aφ - f)`. -/
theorem cB_ode (z : ℝ) :
    cddB α β z + z * cdB α β z + cB α β z = 2 * (ca α β * phi z - cf α β z) := by
  unfold cddB; simp only [cg]; ring

theorem continuous_cB : Continuous (cB α β) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_cB α β z).continuousAt

theorem continuous_cdB : Continuous (cdB α β) :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_cdB α β z).continuousAt

theorem continuous_cddB : Continuous (cddB α β) := by
  unfold cddB
  exact ((continuous_cg α β).sub (continuous_cB α β)).sub (continuous_id.mul (continuous_cdB α β))

private theorem K_nonneg {F : ℝ → ℝ} {K : ℝ} {k : ℕ} (h : ∀ z, |F z| ≤ K * ((1 + |z|) ^ k * phi z)) :
    0 ≤ K := by
  have := (abs_nonneg _).trans (h 0); have hp := phi_pos 0
  exact nonneg_of_mul_nonneg_left this (by positivity)

private theorem abs_le_one_add (z : ℝ) : |z| ≤ 1 + |z| := by linarith

/-- **Tail bound for `B`.** `|B(z)| ≤ K (1 + |z|)³ φ(z)`. -/
theorem abs_cB_le : ∃ K, ∀ z, |cB α β z| ≤ K * ((1 + |z|) ^ 3 * phi z) := by
  obtain ⟨K, hK⟩ := abs_cJ_le α β
  have hK0 := K_nonneg hK
  refine ⟨K, fun z => ?_⟩
  have hp := phi_pos z
  have hI : ‖∫ y in (0:ℝ)..z, cJ α β y / phi y‖ ≤ K * (1 + |z|) ^ 2 * |z - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := z)
      (f := fun y => cJ α β y / phi y) fun y hy => ?_
    have hyz : |y| ≤ |z| := by
      rcases Set.mem_uIoc.1 hy with h | h
      · rw [abs_of_pos h.1, abs_of_pos (h.1.trans_le h.2)]; exact h.2
      · rw [abs_of_nonpos h.2, abs_of_neg (by linarith [h.1, h.2] : z < 0)]; linarith [h.1]
    have hpy := phi_pos y
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hpy, div_le_iff₀ hpy]
    calc |cJ α β y| ≤ K * ((1 + |y|) ^ 2 * phi y) := hK y
      _ ≤ K * (1 + |z|) ^ 2 * phi y := by
          rw [← mul_assoc]; gcongr
  rw [sub_zero, Real.norm_eq_abs] at hI
  unfold cB
  rw [abs_mul, abs_of_pos hp]
  calc phi z * |∫ y in (0:ℝ)..z, cJ α β y / phi y| ≤ phi z * (K * (1 + |z|) ^ 2 * |z|) :=
        mul_le_mul_of_nonneg_left hI hp.le
    _ ≤ phi z * (K * (1 + |z|) ^ 2 * (1 + |z|)) := by gcongr; exact abs_le_one_add z
    _ = K * ((1 + |z|) ^ 3 * phi z) := by ring

/-- **Tail bound for `B'`.** `|B'(z)| ≤ K (1 + |z|)⁴ φ(z)`. -/
theorem abs_cdB_le : ∃ K, ∀ z, |cdB α β z| ≤ K * ((1 + |z|) ^ 4 * phi z) := by
  obtain ⟨K1, h1⟩ := abs_cJ_le α β
  obtain ⟨K2, h2⟩ := abs_cB_le α β
  have := K_nonneg h1; have := K_nonneg h2
  refine ⟨K1 + K2, fun z => ?_⟩
  have hp := phi_pos z
  have ha := abs_le_one_add z
  have hw2 := wphi_mono (z := z) (show 2 ≤ 4 by norm_num)
  have hw3 : (1 + |z|) * ((1 + |z|) ^ 3 * phi z) = (1 + |z|) ^ 4 * phi z := by ring
  unfold cdB
  calc |cJ α β z - z * cB α β z| ≤ |cJ α β z| + |z| * |cB α β z| := by
        rw [← abs_mul]; exact abs_sub _ _
    _ ≤ K1 * ((1 + |z|) ^ 2 * phi z) + (1 + |z|) * (K2 * ((1 + |z|) ^ 3 * phi z)) := by
        gcongr
        · exact h1 z
        · exact h2 z
    _ ≤ _ := by nlinarith

/-- **Tail bound for `B''`.** `|B''(z)| ≤ K (1 + |z|)⁵ φ(z)`. -/
theorem abs_cddB_le : ∃ K, ∀ z, |cddB α β z| ≤ K * ((1 + |z|) ^ 5 * phi z) := by
  obtain ⟨K1, h1⟩ := abs_cg_le α β
  obtain ⟨K2, h2⟩ := abs_cB_le α β
  obtain ⟨K3, h3⟩ := abs_cdB_le α β
  have := K_nonneg h1; have := K_nonneg h2; have := K_nonneg h3
  refine ⟨K1 + K2 + K3, fun z => ?_⟩
  have hp := phi_pos z
  have ha := abs_le_one_add z
  have hw2 := wphi_mono (z := z) (show 2 ≤ 5 by norm_num)
  have hw3 := wphi_mono (z := z) (show 3 ≤ 5 by norm_num)
  have hw4 : (1 + |z|) * ((1 + |z|) ^ 4 * phi z) = (1 + |z|) ^ 5 * phi z := by ring
  unfold cddB
  calc |cg α β z - cB α β z - z * cdB α β z|
        ≤ |cg α β z| + |cB α β z| + |z| * |cdB α β z| := by
        rw [← abs_mul]
        exact (abs_sub _ _).trans (by gcongr; exact abs_sub _ _)
    _ ≤ K1 * ((1 + |z|) ^ 2 * phi z) + K2 * ((1 + |z|) ^ 3 * phi z) +
          (1 + |z|) * (K3 * ((1 + |z|) ^ 4 * phi z)) := by
        gcongr
        · exact h1 z
        · exact h2 z
        · exact h3 z
    _ ≤ _ := by nlinarith

theorem integrable_of_wbound {F : ℝ → ℝ} (hF : Continuous F) {K : ℝ} {k : ℕ}
    (h : ∀ z, |F z| ≤ K * ((1 + |z|) ^ k * phi z)) : Integrable F :=
  ((integrable_wphi k).const_mul K).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using h z)

theorem integrable_cB : Integrable (cB α β) :=
  let ⟨_, h⟩ := abs_cB_le α β; integrable_of_wbound (continuous_cB α β) h
theorem integrable_cdB : Integrable (cdB α β) :=
  let ⟨_, h⟩ := abs_cdB_le α β; integrable_of_wbound (continuous_cdB α β) h
theorem integrable_cddB : Integrable (cddB α β) :=
  let ⟨_, h⟩ := abs_cddB_le α β; integrable_of_wbound (continuous_cddB α β) h

end Corrector
end CausalSpectrum.LogGauss

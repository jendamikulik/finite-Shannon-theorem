/-
Stage 5: propagation, initial comparison, choice of `t₀` and the final asymptotics.

The step `H` is compared with the truncated Gaussian start profile `b̃`, which equals `0`
below `-A`, the Gaussian `p_{t₀}` on `[-A, A)` and `1` from `A` on. Then
`T^n b̃(· - A) ≤ G_n ≤ T^n b̃(· + A)` holds exactly, and for monotone profiles with values
in `[0,1]` the increment integral `∫ (β(x + h) - β(x)) dx` is at most `h`. The Gaussian
tails of `b̃ - p_{t₀}` are dominated with the Chernoff bound `Φ(z) ≤ e^{-z²/2}` (`z ≤ 0`).
-/
import CausalSeed.LogResidual

open MeasureTheory Set Filter Topology Real
open scoped ENNReal

namespace CausalSpectrum.Sqrt.IncFamily
variable (F : IncFamily)

theorem Tit_mono {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) : ∀ (n : ℕ) (x : ℝ), F.Tit n f x ≤ F.Tit n g x
  | 0, x => h x
  | n + 1, x => F.T_mono (Tit_mono h n) x

theorem Tit_translate (f : ℝ → ℝ) (c : ℝ) :
    ∀ (n : ℕ) (x : ℝ), F.Tit n (fun z => f (z + c)) x = F.Tit n f (x + c)
  | 0, _ => rfl
  | n + 1, x => by
    have e : F.Tit n (fun z => f (z + c)) = fun z => F.Tit n f (z + c) :=
      funext (Tit_translate f c n)
    simp only [Tit, e]; exact F.T_translate _ c x

theorem Tit_monotone {f : ℝ → ℝ} (hf : Monotone f) : ∀ n, Monotone (F.Tit n f)
  | 0 => hf
  | n + 1 => F.T_monotone (Tit_monotone hf n)

theorem Tit_bounds {f : ℝ → ℝ} (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    ∀ (n : ℕ) (x : ℝ), 0 ≤ F.Tit n f x ∧ F.Tit n f x ≤ 1
  | 0, x => ⟨h0 x, h1 x⟩
  | n + 1, x => F.T_bounds (fun y => (Tit_bounds h0 h1 n y).1) (fun y => (Tit_bounds h0 h1 n y).2) x

theorem measurable_Tit {f : ℝ → ℝ} (hf : Measurable f) : ∀ n, Measurable (F.Tit n f)
  | 0 => hf
  | n + 1 => by
    have e : F.Tit (n + 1) f = Finset.univ.inf' F.univ_nonempty (fun j => F.expect j (F.Tit n f)) := by
      funext x; simp only [Tit, T, Finset.inf'_apply]
    rw [e]
    refine Finset.inf'_induction F.univ_nonempty _ (fun _ hf _ hg => hf.inf hg) fun j _ => ?_
    have : F.expect j (F.Tit n f) = Decay.act (F.measOf j) (F.Tit n f) :=
      funext fun x => F.expect_eq_act j _ x
    rw [this]; exact Decay.measurable_act _ (measurable_Tit hf n)

end CausalSpectrum.Sqrt.IncFamily

namespace CausalSpectrum.LogGauss

/-! ### Increment integrals of monotone profiles -/

/-- For a nondecreasing `β` with values in `[0,1]` and `h ≥ 0`,
`∫ (β(x + h) - β(x)) dx ≤ h`. -/
theorem lintegral_shift_le {β : ℝ → ℝ} (hβ : Monotone β) (h0 : ∀ x, 0 ≤ β x)
    (h1 : ∀ x, β x ≤ 1) {h : ℝ} (hh : 0 ≤ h) :
    ∫⁻ x, ENNReal.ofReal (β (x + h) - β x) ≤ ENNReal.ofReal h := by
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (β (x + h) - β x)
  have hmeas : Measurable f :=
    ENNReal.measurable_ofReal.comp (((hβ.comp fun a b hab => by
      show a + h ≤ b + h; linarith).measurable).sub hβ.measurable)
  have hsup : f = fun x => ⨆ N : ℕ, (Icc (-(N:ℝ)) N).indicator f x := by
    funext x
    apply le_antisymm
    · obtain ⟨N, hN⟩ := exists_nat_ge |x|
      refine le_iSup_of_le N ?_
      rw [indicator_of_mem (by rw [mem_Icc]; constructor <;> linarith [neg_abs_le x, le_abs_self x])]
    · exact iSup_le fun N => indicator_le_self _ _ x
  rw [hsup, lintegral_iSup (fun N => hmeas.indicator measurableSet_Icc)
    (fun N M hNM x => indicator_le_indicator_of_subset (Icc_subset_Icc (by
      simp only [neg_le_neg_iff, Nat.cast_le]; exact hNM) (by exact_mod_cast hNM)) (fun _ => bot_le) x)]
  refine iSup_le fun N => ?_
  rw [lintegral_indicator measurableSet_Icc]
  have hint : IntegrableOn (fun x => β (x + h) - β x) (Icc (-(N:ℝ)) N) := by
    have h1' : IntervalIntegrable (fun x => β (x + h)) volume (-(N:ℝ)) N :=
      Monotone.intervalIntegrable (fun a b hab => hβ (by linarith))
    have h2' : IntervalIntegrable β volume (-(N:ℝ)) N := hβ.intervalIntegrable
    have := (h1'.sub h2')
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [(N.cast_nonneg : (0:ℝ) ≤ N)])] at this
    exact this
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => sub_nonneg.2 (hβ (by linarith)))]
  apply ENNReal.ofReal_le_ofReal
  have hN : (-(N:ℝ)) ≤ N := by linarith [(N.cast_nonneg : (0:ℝ) ≤ N)]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hN,
    intervalIntegral.integral_sub (Monotone.intervalIntegrable (fun a b hab => hβ (by linarith)))
      hβ.intervalIntegrable, intervalIntegral.integral_comp_add_right (fun x => β x) h,
    intervalIntegral.integral_interval_sub_interval_comm hβ.intervalIntegrable
      hβ.intervalIntegrable hβ.intervalIntegrable]
  have e1 : ∫ x in (-(N:ℝ) + h)..(-(N:ℝ)), β x = -∫ x in (-(N:ℝ))..(-(N:ℝ) + h), β x :=
    intervalIntegral.integral_symm _ _
  have e2 : ∫ x in ((N:ℝ) + h)..(N:ℝ), β x = -∫ x in (N:ℝ)..((N:ℝ) + h), β x :=
    intervalIntegral.integral_symm _ _
  rw [e1, e2]
  have a1 : 0 ≤ ∫ x in (-(N:ℝ))..(-(N:ℝ) + h), β x :=
    intervalIntegral.integral_nonneg (by linarith) fun x _ => h0 x
  have a2 : ∫ x in (N:ℝ)..((N:ℝ) + h), β x ≤ ∫ x in (N:ℝ)..((N:ℝ) + h), (1:ℝ) :=
    intervalIntegral.integral_mono_on (by linarith) hβ.intervalIntegrable
      intervalIntegrable_const fun x _ => h1 x
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at a2
  linarith

/-! ### The normal distribution function -/

theorem continuous_Phi : Continuous Phi :=
  continuous_iff_continuousAt.2 fun z => (hasDerivAt_Phi z).continuousAt

theorem Phi_monotone : Monotone Phi := by
  intro a b hab
  exact setIntegral_mono_set integrable_phi.integrableOn (ae_of_all _ fun y => (phi_pos y).le)
    (Iic_subset_Iic.2 hab).eventuallyLE

theorem Phi_nonneg (z : ℝ) : 0 ≤ Phi z := setIntegral_nonneg measurableSet_Iic fun y _ => (phi_pos y).le

theorem one_sub_Phi (z : ℝ) : 1 - Phi z = ∫ y in Ioi z, phi y := by
  have := intervalIntegral.integral_Iic_add_Ioi (b := z) integrable_phi.integrableOn
    integrable_phi.integrableOn
  rw [integral_phi] at this; unfold Phi; linarith

theorem Phi_le_one (z : ℝ) : Phi z ≤ 1 := by
  have := one_sub_Phi z
  have : 0 ≤ ∫ y in Ioi z, phi y := setIntegral_nonneg measurableSet_Ioi fun y _ => (phi_pos y).le
  linarith

theorem phi_shift (y l : ℝ) : phi y = phi (y + l) * exp (l * y + l ^ 2 / 2) := by
  unfold phi; rw [mul_assoc, ← exp_add]; congr 2; ring

theorem integral_phi_shift (l : ℝ) : ∫ y, phi (y + l) = 1 := by
  rw [integral_add_right_eq_self (fun y => phi y) l, integral_phi]

/-- **Exponential (Chernoff) bound, lower tail.** `Φ(z) ≤ e^{λz + λ²/2}` for `λ ≥ 0`. -/
theorem Phi_le_exp_mgf {l : ℝ} (hl : 0 ≤ l) (z : ℝ) : Phi z ≤ exp (l * z + l ^ 2 / 2) := by
  have hi : Integrable fun y => phi (y + l) := integrable_phi.comp_add_right l
  calc Phi z = ∫ y in Iic z, phi y := rfl
    _ ≤ ∫ y in Iic z, exp (l * z + l ^ 2 / 2) * phi (y + l) := by
        refine setIntegral_mono_on integrable_phi.integrableOn (hi.const_mul _).integrableOn
          measurableSet_Iic fun y hy => ?_
        rw [phi_shift y l, mul_comm]
        have hy' : y ≤ z := hy
        exact mul_le_mul_of_nonneg_right (exp_le_exp.2 (by nlinarith)) (phi_pos _).le
    _ ≤ ∫ y, exp (l * z + l ^ 2 / 2) * phi (y + l) :=
        setIntegral_le_integral (hi.const_mul _) (ae_of_all _ fun y => by
          have := phi_pos (y + l); positivity)
    _ = exp (l * z + l ^ 2 / 2) := by rw [integral_const_mul, integral_phi_shift, mul_one]

/-- **Exponential (Chernoff) bound, upper tail.** `1 - Φ(z) ≤ e^{-λz + λ²/2}` for `λ ≥ 0`. -/
theorem one_sub_Phi_le_exp_mgf {l : ℝ} (hl : 0 ≤ l) (z : ℝ) :
    1 - Phi z ≤ exp (-l * z + l ^ 2 / 2) := by
  have hi : Integrable fun y => phi (y + -l) := integrable_phi.comp_add_right (-l)
  rw [one_sub_Phi]
  calc ∫ y in Ioi z, phi y ≤ ∫ y in Ioi z, exp (-l * z + l ^ 2 / 2) * phi (y + -l) := by
        refine setIntegral_mono_on integrable_phi.integrableOn (hi.const_mul _).integrableOn
          measurableSet_Ioi fun y hy => ?_
        rw [phi_shift y (-l), mul_comm]
        have hy' : z < y := hy
        exact mul_le_mul_of_nonneg_right (exp_le_exp.2 (by nlinarith)) (phi_pos _).le
    _ ≤ ∫ y, exp (-l * z + l ^ 2 / 2) * phi (y + -l) :=
        setIntegral_le_integral (hi.const_mul _) (ae_of_all _ fun y => by
          have := phi_pos (y + -l); positivity)
    _ = exp (-l * z + l ^ 2 / 2) := by rw [integral_const_mul, integral_phi_shift, mul_one]

/-- Gaussian tails: `Φ(z) ≤ e^{-z²/2}` for `z ≤ 0` and `1 - Φ(z) ≤ e^{-z²/2}` for `z ≥ 0`. -/
theorem Phi_le_gauss {z : ℝ} (hz : z ≤ 0) : Phi z ≤ exp (-(z ^ 2 / 2)) := by
  have := Phi_le_exp_mgf (l := -z) (by linarith) z
  convert this using 2; ring

theorem one_sub_Phi_le_gauss {z : ℝ} (hz : 0 ≤ z) : 1 - Phi z ≤ exp (-(z ^ 2 / 2)) := by
  have := one_sub_Phi_le_exp_mgf (l := z) hz z
  convert this using 2; ring

/-! ### The mean of a Gaussian distribution function -/

/-- `A(z) = zΦ(z) + φ(z)` has derivative `Φ`. -/
theorem hasDerivAt_PhiPrimL (z : ℝ) : HasDerivAt (fun z => z * Phi z + phi z) (Phi z) z := by
  have := ((hasDerivAt_id z).mul (hasDerivAt_Phi z)).add (hasDerivAt_phi z)
  exact this.congr_deriv (by simp only [dphi, id]; ring)

/-- `B(z) = z(Φ(z) - 1) + φ(z)` has derivative `Φ - 1`. -/
theorem hasDerivAt_PhiPrimR (z : ℝ) :
    HasDerivAt (fun z => z * (Phi z - 1) + phi z) (Phi z - 1) z := by
  have := ((hasDerivAt_id z).mul ((hasDerivAt_Phi z).sub_const 1)).add (hasDerivAt_phi z)
  exact this.congr_deriv (by simp only [dphi, id]; ring)

theorem tendsto_mul_Phi_atBot : Tendsto (fun z => z * Phi z) atBot (𝓝 0) := by
  have hd : Tendsto (fun z => √(2 * π) * |dphi z|) atBot (𝓝 0) := by
    simpa using (tendsto_dphi_atBot.abs).const_mul (√(2 * π))
  refine squeeze_zero_norm' ?_ hd
  filter_upwards [eventually_le_atBot 0] with z hz
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Phi_nonneg z)]
  have h1 := Phi_le_gauss hz
  have e : √(2 * π) * |dphi z| = |z| * exp (-(z ^ 2 / 2)) := by
    rw [dphi, phi, abs_mul, abs_mul, abs_neg, abs_of_pos (exp_pos _),
      abs_of_pos (inv_pos.2 (sqrt_pos.2 (by positivity)))]
    field_simp
  rw [e]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg z)

theorem tendsto_mul_one_sub_Phi_atTop : Tendsto (fun z => z * (Phi z - 1)) atTop (𝓝 0) := by
  have hd : Tendsto (fun z => √(2 * π) * |dphi z|) atTop (𝓝 0) := by
    simpa using (tendsto_dphi_atTop.abs).const_mul (√(2 * π))
  refine squeeze_zero_norm' ?_ hd
  filter_upwards [eventually_ge_atTop 0] with z hz
  rw [Real.norm_eq_abs, abs_mul, show |Phi z - 1| = 1 - Phi z by
    rw [abs_sub_comm]; exact abs_of_nonneg (by linarith [Phi_le_one z])]
  have h1 := one_sub_Phi_le_gauss hz
  have e : √(2 * π) * |dphi z| = |z| * exp (-(z ^ 2 / 2)) := by
    rw [dphi, phi, abs_mul, abs_mul, abs_neg, abs_of_pos (exp_pos _),
      abs_of_pos (inv_pos.2 (sqrt_pos.2 (by positivity)))]
    field_simp
  rw [e]; exact mul_le_mul_of_nonneg_left h1 (abs_nonneg z)

theorem integrableOn_Phi_Iic (m : ℝ) {s : ℝ} (hs : 0 < s) (c : ℝ) :
    IntegrableOn (fun x => Phi ((x - m) / s)) (Iic c) := by
  have he := (integrableOn_exp_mul_Iic (a := 1 / s) (by positivity) c).const_mul
    (exp (-m / s + 1 / 2))
  refine he.mono' ((continuous_Phi.comp (by fun_prop)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Phi_nonneg _), ← exp_add]
  refine (Phi_le_exp_mgf zero_le_one _).trans (le_of_eq ?_)
  congr 1; field_simp; ring

theorem integrableOn_one_sub_Phi_Ioi (m : ℝ) {s : ℝ} (hs : 0 < s) (c : ℝ) :
    IntegrableOn (fun x => 1 - Phi ((x - m) / s)) (Ioi c) := by
  have he := (integrableOn_exp_mul_Ioi (a := -(1 / s)) (by
    have : 0 < 1 / s := by positivity
    linarith) c).const_mul (exp (m / s + 1 / 2))
  refine he.mono' ((continuous_const.sub (continuous_Phi.comp (by fun_prop))).aestronglyMeasurable)
    (ae_of_all _ fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [Phi_le_one ((x - m) / s)]), ← exp_add]
  refine (one_sub_Phi_le_exp_mgf zero_le_one _).trans (le_of_eq ?_)
  congr 1; field_simp; ring

/-- The step function `H = 1_{[0,∞)}`. -/
noncomputable def Hs (x : ℝ) : ℝ := if 0 ≤ x then 1 else 0

theorem integrable_H_sub_Phi (m : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable fun x => Hs x - Phi ((x - m) / s) := by
  rw [← integrableOn_univ, ← Iio_union_Ici (a := (0:ℝ)), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  constructor
  · refine ((integrableOn_Phi_Iic m hs 0).mono_set Iio_subset_Iic_self).neg.congr_fun
      (fun x hx => ?_) measurableSet_Iio
    simp [Hs, not_le.2 (show x < 0 from hx)]
  · refine (integrableOn_one_sub_Phi_Ioi m hs 0).congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp [Hs, le_of_lt (show (0:ℝ) < x from hx)]

/-- **The mean of `N(m, s²)`.** `∫ (H(x) - Φ((x - m)/s)) dx = m`. -/
theorem integral_H_sub_Phi (m : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, (Hs x - Phi ((x - m) / s)) = m := by
  have hI := integrable_H_sub_Phi m hs
  rw [← intervalIntegral.integral_Iic_add_Ioi (b := 0) hI.integrableOn hI.integrableOn,
    integral_Iic_eq_integral_Iio]
  have e1 : ∫ x in Iio 0, (Hs x - Phi ((x - m) / s)) = -∫ x in Iic 0, Phi ((x - m) / s) := by
    rw [integral_Iic_eq_integral_Iio, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Iio fun x hx => ?_
    simp [Hs, not_le.2 (show x < 0 from hx)]
  have e2 : ∫ x in Ioi 0, (Hs x - Phi ((x - m) / s)) = ∫ x in Ioi 0, (1 - Phi ((x - m) / s)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    simp [Hs, le_of_lt (show (0:ℝ) < x from hx)]
  rw [e1, e2]
  have hz : ∀ x, HasDerivAt (fun x : ℝ => (x - m) / s) (1 / s) x := fun x =>
    ((hasDerivAt_id x).sub_const m).div_const s
  -- left piece
  have dL : ∀ x, HasDerivAt (fun x => s * (((x - m) / s) * Phi ((x - m) / s) + phi ((x - m) / s)))
      (Phi ((x - m) / s)) x := fun x => by
    have := ((hasDerivAt_PhiPrimL _).comp x (hz x)).const_mul s
    exact this.congr_deriv (by field_simp)
  have tL : Tendsto (fun x => s * (((x - m) / s) * Phi ((x - m) / s) + phi ((x - m) / s))) atBot (𝓝 0) := by
    have hzt : Tendsto (fun x : ℝ => (x - m) / s) atBot atBot :=
      (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hs |>.congr fun x => by
        simp only [id]; ring
    have := ((tendsto_mul_Phi_atBot.add tendsto_phi_atBot).comp hzt).const_mul s
    simpa using this
  have iL := integral_Iic_of_hasDerivAt_of_tendsto (dL 0).continuousAt.continuousWithinAt
    (fun x _ => dL x) (integrableOn_Phi_Iic m hs 0) tL
  -- right piece
  have dR : ∀ x, HasDerivAt (fun x => s * (((x - m) / s) * (Phi ((x - m) / s) - 1) + phi ((x - m) / s)))
      (-(1 - Phi ((x - m) / s))) x := fun x => by
    have := ((hasDerivAt_PhiPrimR _).comp x (hz x)).const_mul s
    exact this.congr_deriv (by field_simp; ring)
  have tR : Tendsto (fun x => s * (((x - m) / s) * (Phi ((x - m) / s) - 1) + phi ((x - m) / s))) atTop (𝓝 0) := by
    have hzt : Tendsto (fun x : ℝ => (x - m) / s) atTop atTop :=
      (tendsto_atTop_add_const_right _ (-m) tendsto_id).atTop_div_const hs |>.congr fun x => by
        simp only [id]; ring
    have := ((tendsto_mul_one_sub_Phi_atTop.add tendsto_phi_atTop).comp hzt).const_mul s
    simpa using this
  have iR := integral_Ioi_of_hasDerivAt_of_tendsto (dR 0).continuousAt.continuousWithinAt
    (fun x _ => dR x) (integrableOn_one_sub_Phi_Ioi m hs 0).neg tR
  rw [integral_neg] at iR
  rw [iL]
  have : ∫ x in Ioi 0, (1 - Phi ((x - m) / s)) = s * ((0 - m) / s * (Phi ((0 - m) / s) - 1)
      + phi ((0 - m) / s)) := by linarith
  rw [this]; field_simp; ring

/-! ### `L¹` comparison tools -/

theorem lintegral_tri {f g h : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, ENNReal.ofReal |f x - h x| ≤
      (∫⁻ x, ENNReal.ofReal |f x - g x|) + ∫⁻ x, ENNReal.ofReal |g x - h x| := by
  have hm : Measurable fun x => ENNReal.ofReal |f x - g x| :=
    ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp (hf.sub hg))
  rw [← lintegral_add_left hm]
  refine lintegral_mono fun x => ?_
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_sub_le _ _ _)

theorem Phi_sub (a b : ℝ) : Phi b - Phi a = ∫ y in a..b, phi y :=
  (intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_Phi y)
    (continuous_phi.intervalIntegrable _ _)).symm

theorem phi_le_of_sq_le {u w : ℝ} (h : u ^ 2 ≤ w ^ 2) : phi w ≤ phi u := by
  unfold phi; gcongr

/-- Pointwise scale comparison: `|Φ(y/s₂) - Φ(y/s₁)| ≤ (s₂ - s₁)/s₁ · |φ'(y/s₂)|`. -/
theorem abs_Phi_scale_le {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (y : ℝ) :
    |Phi (y / s₂) - Phi (y / s₁)| ≤ (s₂ - s₁) / s₁ * |dphi (y / s₂)| := by
  have h2 : 0 < s₂ := h1.trans_le h12
  rw [Phi_sub, ← Real.norm_eq_abs]
  have hb : ∀ w ∈ uIoc (y / s₁) (y / s₂), ‖phi w‖ ≤ phi (y / s₂) := by
    intro w hw
    rw [Real.norm_eq_abs, abs_of_pos (phi_pos w)]
    apply phi_le_of_sq_le
    have hw' := uIoc_subset_uIcc hw
    rw [mem_uIcc] at hw'
    rcases le_total 0 y with hy | hy
    · have a1 : y / s₂ ≤ y / s₁ := div_le_div_of_nonneg_left hy h1 h12
      have a2 : 0 ≤ y / s₂ := div_nonneg hy h2.le
      rcases hw' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> nlinarith
    · have a1 : y / s₁ ≤ y / s₂ := by
        rw [div_le_div_iff₀ h1 h2]; nlinarith
      have a2 : y / s₂ ≤ 0 := div_nonpos_of_nonpos_of_nonneg hy h2.le
      rcases hw' with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> nlinarith
  refine (intervalIntegral.norm_integral_le_of_norm_le_const hb).trans (le_of_eq ?_)
  have e : y / s₂ - y / s₁ = -(y / s₂) * ((s₂ - s₁) / s₁) := by field_simp; ring
  rw [e, dphi, abs_mul, abs_mul, abs_of_pos (phi_pos _),
    abs_of_nonneg (div_nonneg (by linarith) h1.le)]
  ring

/-- **Scale comparison in `L¹`.** -/
theorem lintegral_Phi_scale {s₁ s₂ : ℝ} (h1 : 0 < s₁) (h12 : s₁ ≤ s₂) (m : ℝ) :
    ∫⁻ x, ENNReal.ofReal |Phi ((x - m) / s₂) - Phi ((x - m) / s₁)| ≤
      ENNReal.ofReal ((s₂ - s₁) / s₁ * s₂ * (2 * phi 0)) := by
  have h2 : 0 < s₂ := h1.trans_le h12
  have hi : Integrable fun x => (s₂ - s₁) / s₁ * |dphi ((x - m) / s₂)| := by
    have : Integrable fun x => dphi (s₂⁻¹ * x) :=
      (integrable_comp_mul_left_iff dphi (inv_ne_zero h2.ne')).2 integrable_dphi
    exact ((this.comp_sub_right m).abs.const_mul ((s₂ - s₁) / s₁)).congr (ae_of_all _ fun x => by
      simp only [div_eq_inv_mul (x - m)])
  refine (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (abs_Phi_scale_le h1 h12 (x - m))).trans
    (le_of_eq ?_)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by
    have : 0 ≤ (s₂ - s₁) / s₁ := div_nonneg (by linarith) h1.le
    positivity), integral_const_mul, integral_abs_comp_affine dphi m h2, integral_abs_dphi]
  ring_nf

theorem lintegral_Phi_shift_aux {m₁ m₂ : ℝ} (h : m₁ ≤ m₂) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, ENNReal.ofReal |Phi ((x - m₁) / s) - Phi ((x - m₂) / s)| ≤ ENNReal.ofReal (m₂ - m₁) := by
  set β := fun x => Phi ((x - m₂) / s)
  have hβ : Monotone β := fun a b hab => Phi_monotone (by
    show (a - m₂) / s ≤ (b - m₂) / s; gcongr)
  refine le_trans (le_of_eq (lintegral_congr fun x => ?_))
    (lintegral_shift_le hβ (fun x => Phi_nonneg _) (fun x => Phi_le_one _) (h := m₂ - m₁) (by linarith))
  have e : (x - m₁) / s = (x + (m₂ - m₁) - m₂) / s := by ring
  have hle : β x ≤ β (x + (m₂ - m₁)) := hβ (by linarith)
  simp only [β] at hle ⊢
  rw [e, abs_of_nonneg (by linarith)]

/-- **Shift comparison in `L¹`.** -/
theorem lintegral_Phi_shift (m₁ m₂ : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫⁻ x, ENNReal.ofReal |Phi ((x - m₁) / s) - Phi ((x - m₂) / s)| ≤ ENNReal.ofReal |m₁ - m₂| := by
  rcases le_total m₁ m₂ with h | h
  · rw [abs_of_nonpos (by linarith), neg_sub]; exact lintegral_Phi_shift_aux h hs
  · rw [abs_of_nonneg (by linarith)]
    simp_rw [abs_sub_comm (Phi ((_ - m₁) / s))]
    exact lintegral_Phi_shift_aux h hs

/-- `Σ_{j<n} (a + j)^{-3/2} ≤ 2 (a - 1)^{-1/2}` for `a ≥ 2`. -/
theorem sum_pow_three_halves {a : ℝ} (ha : 2 ≤ a) (n : ℕ) :
    ∑ j ∈ Finset.range n, 1 / ((a + j) * √(a + j)) ≤ 2 / √(a - 1) := by
  have key : ∀ b : ℝ, 2 ≤ b → 1 / (b * √b) ≤ 2 / √(b - 1) - 2 / √b := by
    intro b hb
    have hp := sqrt_pos.2 (show 0 < b - 1 by linarith)
    have hq := sqrt_pos.2 (show 0 < b by linarith)
    have hp2 := sq_sqrt (show 0 ≤ b - 1 by linarith)
    have hq2 := sq_sqrt (show 0 ≤ b by linarith)
    have hpq : √(b - 1) ≤ √b := sqrt_le_sqrt (by linarith)
    set p := √(b - 1); set q := √b
    have e : 2 / p - 2 / q = 2 / (p * q * (q + p)) := by
      field_simp; nlinarith
    rw [e, show b = q ^ 2 by rw [hq2], div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hp hq]
  have hs := Finset.sum_le_sum fun j (_ : j ∈ Finset.range n) =>
    key (a + j) (by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith)
  refine hs.trans ?_
  have := Finset.sum_range_sub' (fun j : ℕ => 2 / √(a + j - 1)) n
  have e : ∀ j : ℕ, 2 / √(a + ↑j - 1) - 2 / √(a + ↑(j + 1) - 1) = 2 / √(a + j - 1) - 2 / √(a + j) :=
    fun j => by push_cast; ring_nf
  simp only [e] at this
  rw [this]; simp only [Nat.cast_zero, add_zero]
  have : 0 ≤ 2 / √(a + n - 1) := by positivity
  linarith

/-- The corrector is dominated by the majorant profile. -/
theorem abs_cB_le_Emaj (α β : ℝ) : ∃ K, 0 ≤ K ∧ ∀ z, |cB α β z| ≤ K * Emaj z := by
  obtain ⟨K, hK⟩ := abs_cB_le α β
  have hK0 : 0 ≤ K := by
    have := (abs_nonneg _).trans (hK 0)
    have hp : 0 < (1 + |(0:ℝ)|) ^ 3 * phi 0 := by have := phi_pos 0; positivity
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨K * CW 0, mul_nonneg hK0 (CW_nonneg le_rfl), fun z => (hK z).trans ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (window_seg (k := 3) (w := z) le_rfl (by norm_num) (by simp) left_mem_uIcc) hK0

/-- Gaussian tails beyond `R` are dominated by `e^{-3R²/8} E`. -/
theorem gauss_tail_le {R z : ℝ} (hR : R ^ 2 ≤ z ^ 2) :
    exp (-(z ^ 2 / 2)) ≤ exp (-(3 * R ^ 2 / 8)) * Emaj z := by
  unfold Emaj
  have h1 : 1 ≤ (1 + z ^ 2) ^ 4 := one_le_pow₀ (by nlinarith)
  calc exp (-(z ^ 2 / 2)) = exp (-(3 * z ^ 2 / 8)) * exp (-(z ^ 2 / 8)) := by
        rw [← exp_add]; ring_nf
    _ ≤ exp (-(3 * R ^ 2 / 8)) * ((1 + z ^ 2) ^ 4 * exp (-(z ^ 2 / 8))) := by
        exact mul_le_mul (exp_le_exp.2 (by linarith)) (le_mul_of_one_le_left (exp_pos _).le h1)
          (exp_pos _).le (exp_pos _).le

/-! ### The truncated start profile -/

/-- `b̃ = 0` below `-A`, `Φ((x - m)/s)` on `[-A, A)`, and `1` from `A` on. -/
noncomputable def bt (A m s x : ℝ) : ℝ := if x < -A then 0 else if x < A then Phi ((x - m) / s) else 1

theorem bt_bounds (A m s x : ℝ) : 0 ≤ bt A m s x ∧ bt A m s x ≤ 1 := by
  unfold bt; split_ifs
  · norm_num
  · exact ⟨Phi_nonneg _, Phi_le_one _⟩
  · norm_num

theorem bt_monotone {A m s : ℝ} (hs : 0 < s) : Monotone (bt A m s) := by
  intro x y hxy
  unfold bt
  split_ifs <;> first
    | (exfalso; linarith) | exact le_rfl | exact Phi_nonneg _ | exact Phi_le_one _
    | exact Phi_monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy m) hs.le) | norm_num

theorem bt_sandwich {A : ℝ} (hA : 0 ≤ A) (m s x : ℝ) :
    Hs (x - A) ≤ bt A m s x ∧ bt A m s x ≤ Hs (x + A) := by
  unfold bt Hs
  constructor
  · split_ifs <;> first | (exfalso; linarith) | exact le_rfl | exact Phi_nonneg _
  · split_ifs <;> first | (exfalso; linarith) | exact le_rfl | exact Phi_le_one _

/-- The truncation error is a Gaussian tail beyond `R`. -/
theorem abs_bt_sub_le {A m s R : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (hA : s * R + |m| ≤ A) (x : ℝ) :
    |bt A m s x - Phi ((x - m) / s)| ≤ exp (-(3 * R ^ 2 / 8)) * Emaj ((x - m) / s) := by
  have hE : 0 ≤ exp (-(3 * R ^ 2 / 8)) * Emaj ((x - m) / s) :=
    mul_nonneg (exp_pos _).le (Emaj_nonneg _)
  have hm := le_abs_self m; have hm' := neg_abs_le m
  unfold bt
  split_ifs with h1 h2
  · have hz : (x - m) / s ≤ -R := by
      rw [div_le_iff₀ hs]; nlinarith
    rw [zero_sub, abs_neg, abs_of_nonneg (Phi_nonneg _)]
    exact (Phi_le_gauss (by linarith)).trans (gauss_tail_le (by nlinarith))
  · simpa using hE
  · have hz : R ≤ (x - m) / s := by
      rw [le_div_iff₀ hs]; nlinarith
    rw [abs_of_nonneg (by linarith [Phi_le_one ((x - m) / s)])]
    exact (one_sub_Phi_le_gauss (by linarith)).trans (gauss_tail_le (by nlinarith))

theorem G0_eq_Hs (F : Sqrt.IncFamily) : F.G 0 = Hs := by
  funext x; rw [F.G0_eq]; simp [Hs, indicator]

/-- **Initial comparison, sandwich part.** `‖G_n - T^n b̃‖₁ ≤ 2A`. -/
theorem lintegral_G_sub_Tit_bt (F : Sqrt.IncFamily) {A : ℝ} (hA : 0 ≤ A) (m : ℝ) {s : ℝ}
    (hs : 0 < s) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |F.G n x - F.Tit n (bt A m s) x| ≤ ENNReal.ofReal (2 * A) := by
  set β := F.Tit n (bt A m s)
  have hβ : Monotone β := F.Tit_monotone (bt_monotone hs) n
  have hb := F.Tit_bounds (fun x => (bt_bounds A m s x).1) (fun x => (bt_bounds A m s x).2) n
  have up : ∀ y, F.G n y ≤ β (y + A) := fun y => by
    rw [← F.Tit_H]; simp only [β]; rw [← F.Tit_translate]
    exact F.Tit_mono (fun z => by
      rw [G0_eq_Hs]; have := (bt_sandwich hA m s (z + A)).1; simpa using this) n y
  have lo : ∀ y, β (y - A) ≤ F.G n y := fun y => by
    rw [← F.Tit_H, sub_eq_add_neg]; simp only [β]; rw [← F.Tit_translate]
    exact F.Tit_mono (fun z => by
      rw [G0_eq_Hs]; have := (bt_sandwich hA m s (z + -A)).2; simpa using this) n y
  calc ∫⁻ x, ENNReal.ofReal |F.G n x - β x|
      ≤ ∫⁻ x, ENNReal.ofReal (β ((x - A) + 2 * A) - β (x - A)) := by
        refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
        have e : x - A + 2 * A = x + A := by ring
        rw [e, abs_le]
        have := up x; have := lo x
        have := hβ (show x - A ≤ x by linarith); have := hβ (show x ≤ x + A by linarith)
        constructor <;> linarith
    _ = ∫⁻ x, ENNReal.ofReal (β (x + 2 * A) - β x) :=
        lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (β (x + 2 * A) - β x)) A
    _ ≤ ENNReal.ofReal (2 * A) :=
        lintegral_shift_le hβ (fun x => (hb x).1) (fun x => (hb x).2) (by linarith)

/-! ### Choice of `t₀` and the final asymptotics -/

theorem log_facts {n : ℕ} (hn : 16 ≤ n) :
    exp 1 < log n ∧ 1 < log (log n) ∧ log (log n) ≤ log n ∧ log n + 1 ≤ n := by
  have hn' : (16:ℝ) ≤ n := by exact_mod_cast hn
  have h16 : log 16 = 4 * log 2 := by
    rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
  have hL : exp 1 < log n := by
    have := Real.log_le_log (by norm_num) hn'
    linarith [Real.log_two_gt_d9, Real.exp_one_lt_d9]
  have hpos : 0 < log n := (exp_pos 1).trans hL
  refine ⟨hL, ?_, ?_, ?_⟩
  · rw [Real.lt_log_iff_exp_lt hpos]; exact hL
  · linarith [Real.log_le_sub_one_of_pos hpos]
  · linarith [Real.log_le_sub_one_of_pos (show (0:ℝ) < n by linarith)]

section Final
variable (F : Sqrt.IncFamily) (v : ℝ)

set_option maxHeartbeats 1000000 in
/-- **Main theorem, `L¹`-CDF form.** For `n ≥ 16`,
`∫ |G_n(x) - Φ((x - c ln n)/√(vn))| dx ≤ C √(ln n · ln ln n)`.
The left side is the Wasserstein-1 distance between `ν_n` and `N(c ln n, vn)` in its
one-dimensional CDF form `W₁(μ,ν) = ∫ |F_μ - F_ν|`. -/
theorem main_L1 (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ C, ∀ n : ℕ, 16 ≤ n →
      ∫⁻ x, ENNReal.ofReal |F.G n x - Phi ((x - cdrift F v * log n) / √(v * n))| ≤
        ENNReal.ofReal (C * √(log n * log (log n))) := by
  obtain ⟨Cw, hW⟩ := F.width_log_upper hc hv hσ
  obtain ⟨Kr, K1, K2, hKr, hK1, hK2, hres⟩ := residual_majorant F v hc hv hσ
  obtain ⟨KB, hKB, hB⟩ := abs_cB_le_Emaj (calpha F v) (cbeta F v)
  set c := cdrift F v
  set IE := ∫ z, Emaj z
  set IdE := ∫ z, |dEmaj z|
  have hIE : 0 ≤ IE := integral_nonneg Emaj_nonneg
  have hIdE : 0 ≤ IdE := integral_nonneg fun _ => abs_nonneg _
  set Cw' := |Cw|
  have hCw' : 0 ≤ Cw' := abs_nonneg _
  have hsv := sqrt_pos.2 hv
  have hp0 := phi_pos 0
  refine ⟨2 * (√(8 * v / 3) + |c|) + √v * IE * (1 + KB) + IdE * Cw' * (2 + 2 * KB) +
    4 * (K1 + 2 * K2 * Cw') + KB * √v * IE + 4 * phi 0 * √v + |c|, fun n hn => ?_⟩
  obtain ⟨hLe, hℓ1, hℓL, hLn⟩ := log_facts hn
  set L := log (n:ℝ)
  set ℓ := log L
  have hL2 : 2 ≤ L := by linarith [Real.exp_one_gt_d9]
  have hL0 : 0 < L := by linarith
  have hn0 : (0:ℝ) < n := by linarith
  -- width bound for all `k ≤ n`
  have hWk : ∀ k, k ≤ n → F.Wint k ≤ ENNReal.ofReal (Cw' * (1 + L)) := fun k hk => by
    refine (hW k).2.trans (ENNReal.ofReal_le_ofReal ?_)
    have hlk : log (k:ℝ) ≤ L := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]; linarith
      · exact Real.log_le_log (by exact_mod_cast h) (by exact_mod_cast hk)
    have h0 : 0 ≤ 1 + log (k:ℝ) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · simp [h]
      · have := Real.log_nonneg (show (1:ℝ) ≤ k by exact_mod_cast h); linarith
    calc Cw * (1 + log (k:ℝ)) ≤ Cw' * (1 + log (k:ℝ)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) h0
      _ ≤ Cw' * (1 + L) := mul_le_mul_of_nonneg_left (by linarith) hCw'
  -- parameters of the start profile
  set s0 := √(v * L)
  have hs0 : 0 < s0 := sqrt_pos.2 (by positivity)
  set m0 := c * ℓ
  set R := √(8 * ℓ / 3)
  have hR0 : 0 ≤ R := sqrt_nonneg _
  have hR2 : R ^ 2 = 8 * ℓ / 3 := sq_sqrt (by linarith)
  set A := s0 * R + |m0|
  have hA0 : 0 ≤ A := by positivity
  have htail : exp (-(3 * R ^ 2 / 8)) = 1 / L := by
    rw [hR2, show -(3 * (8 * ℓ / 3) / 8) = -ℓ by ring, exp_neg, exp_log hL0, one_div]
  set Ks := 1 / L + KB / √L
  have hKs : 0 ≤ Ks := by positivity
  have hsL := sqrt_pos.2 hL0
  -- (1) sandwich
  have E1 := lintegral_G_sub_Tit_bt F hA0 m0 hs0 n
  -- (2) initial stability
  have hSmaj := majorant_scaled hKs m0 hs0
  have hdom : ∀ x, |bt A m0 s0 x - prof F v L x| ≤ Ks * Emaj ((x - m0) / s0) := fun x => by
    have h1 := abs_bt_sub_le hs0 hR0 (le_refl A) x
    rw [htail] at h1
    have h2 := hB ((x - m0) / s0)
    have hz : zt F v L x = (x - m0) / s0 := rfl
    unfold prof; rw [hz]
    have e : bt A m0 s0 x - (Phi ((x - m0) / s0) + cB (calpha F v) (cbeta F v) ((x - m0) / s0) / √L)
        = (bt A m0 s0 x - Phi ((x - m0) / s0)) - cB (calpha F v) (cbeta F v) ((x - m0) / s0) / √L := by
      ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_div, abs_of_pos hsL]
    have h3 : |cB (calpha F v) (cbeta F v) ((x - m0) / s0)| / √L ≤ KB / √L * Emaj ((x - m0) / s0) := by
      rw [div_le_iff₀ hsL]
      calc _ ≤ KB * Emaj ((x - m0) / s0) := h2
        _ = _ := by field_simp
    have : Ks * Emaj ((x - m0) / s0) = 1 / L * Emaj ((x - m0) / s0) + KB / √L * Emaj ((x - m0) / s0) := by
      ring
    linarith
  have E2 := F.stability_lintegral hSmaj hdom n
  obtain ⟨n1, n2⟩ := lintegral_majorant_scaled hKs m0 hs0
  rw [n1, n2] at E2
  change _ ≤ ENNReal.ofReal (Ks * s0 * IE) + ENNReal.ofReal (Ks * IdE) * F.Wint n at E2
  -- (3) propagation
  set u : ℕ → ℝ → ℝ := fun j => prof F v (L + j)
  have hτ : ∀ j : ℕ, 1 ≤ L + j := fun j => by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
  have hprop := F.propagation_lintegral u
    (fun j x => Kr / (L + j) ^ 2 * Emaj ((x - c * log (L + j)) / √(v * (L + j))))
    (fun j x => Kr / (L + j) ^ 2 * (dEmaj ((x - c * log (L + j)) / √(v * (L + j))) / √(v * (L + j))))
    (fun j => (hres (L + j) (hτ j)).1)
    (fun j x => by
      have := (hres (L + j) (hτ j)).2.1 x
      simp only [u]; push_cast; rwa [← add_assoc]) n
  have E3 : ∫⁻ x, ENNReal.ofReal |F.Tit n (prof F v L) x - prof F v (L + n) x| ≤
      ENNReal.ofReal ((K1 + K2 * (Cw' * (1 + L))) * (2 / √(L - 1))) := by
    have hu0 : u 0 = prof F v L := by simp [u]
    rw [← hu0]
    refine hprop.trans ?_
    have hterm : ∀ j ∈ Finset.range n,
        (∫⁻ x, ‖Kr / (L + j) ^ 2 * Emaj ((x - c * log (L + j)) / √(v * (L + j)))‖ₑ) +
        (∫⁻ x, ‖Kr / (L + j) ^ 2 * (dEmaj ((x - c * log (L + j)) / √(v * (L + j))) /
          √(v * (L + j)))‖ₑ) * F.Wint (n - 1 - j) ≤
        ENNReal.ofReal ((K1 + K2 * (Cw' * (1 + L))) * (1 / ((L + j) * √(L + j)))) := by
      intro j _
      have hj := hτ j
      rw [(hres (L + j) hj).2.2.1, (hres (L + j) hj).2.2.2]
      have hsj := sqrt_pos.2 (show 0 < L + j by linarith)
      have hsle : √(L + j) ≤ L + j := by
        rw [sqrt_le_left (by linarith)]; nlinarith
      calc ENNReal.ofReal (K1 / ((L + j) * √(L + j))) + ENNReal.ofReal (K2 / (L + j) ^ 2) *
            F.Wint (n - 1 - j)
          ≤ ENNReal.ofReal (K1 / ((L + j) * √(L + j))) + ENNReal.ofReal (K2 / (L + j) ^ 2) *
            ENNReal.ofReal (Cw' * (1 + L)) := by gcongr; exact hWk _ (by omega)
        _ = ENNReal.ofReal (K1 / ((L + j) * √(L + j)) + K2 / (L + j) ^ 2 * (Cw' * (1 + L))) := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
              (by positivity)]
        _ ≤ _ := by
            apply ENNReal.ofReal_le_ofReal
            have : K2 / (L + j) ^ 2 ≤ K2 * (1 / ((L + j) * √(L + j))) := by
              rw [mul_one_div]
              exact div_le_div_of_nonneg_left hK2 (by positivity) (by nlinarith)
            have hW0 : 0 ≤ Cw' * (1 + L) := by positivity
            have h := mul_le_mul_of_nonneg_right this hW0
            calc K1 / ((L + j) * √(L + j)) + K2 / (L + j) ^ 2 * (Cw' * (1 + L))
                ≤ K1 / ((L + j) * √(L + j)) + K2 * (1 / ((L + j) * √(L + j))) * (Cw' * (1 + L)) :=
                  add_le_add le_rfl h
              _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => by
      have := hτ j; have := sqrt_pos.2 (show 0 < L + j by linarith); positivity),
      ← Finset.mul_sum]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sum_pow_three_halves hL2 n)
      (by positivity))
  -- (4) remove the corrector at time `t₀ + n`
  set τ := L + n
  have hτ0 : 0 < τ := by linarith
  have hsτ := sqrt_pos.2 hτ0
  set s2 := √(v * τ)
  have hs2 : 0 < s2 := sqrt_pos.2 (by positivity)
  set m2 := c * log τ
  have E4 : ∫⁻ x, ENNReal.ofReal |prof F v τ x - Phi ((x - m2) / s2)| ≤
      ENNReal.ofReal (KB * √v * IE) := by
    have hK : 0 ≤ KB / √τ := by positivity
    obtain ⟨q1, -⟩ := lintegral_majorant_scaled hK m2 hs2
    calc _ ≤ ∫⁻ x, ‖KB / √τ * Emaj ((x - m2) / s2)‖ₑ := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_norm, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hK (Emaj_nonneg _))]
          apply ENNReal.ofReal_le_ofReal
          have hz : zt F v τ x = (x - m2) / s2 := rfl
          unfold prof; rw [hz, add_sub_cancel_left, abs_div, abs_of_pos hsτ, div_le_iff₀ hsτ]
          calc _ ≤ KB * Emaj ((x - m2) / s2) := hB _
            _ = _ := by field_simp
      _ = _ := by
          rw [q1]; congr 1
          simp only [s2]; rw [sqrt_mul hv.le]; field_simp; rfl
  -- (5) scale and (6) shift
  set s1 := √(v * n)
  have hs1 : 0 < s1 := sqrt_pos.2 (by positivity)
  have h12 : s1 ≤ s2 := sqrt_le_sqrt (by nlinarith)
  have E5 := lintegral_Phi_scale hs1 h12 m2
  have E6 := lintegral_Phi_shift m2 (c * log n) hs1
  -- measurability
  have mG : Measurable (F.G n) := F.measurable_G n
  have mprof : ∀ t, Measurable (prof F v t) := fun t => by
    unfold prof zt
    exact ((continuous_Phi.comp (by fun_prop)).add
      (((continuous_cB _ _).comp (by fun_prop)).div_const _)).measurable
  have mβ : Measurable (F.Tit n (bt A m0 s0)) := (F.Tit_monotone (bt_monotone hs0) n).measurable
  have mTu : Measurable (F.Tit n (prof F v L)) := F.measurable_Tit (mprof L) n
  have mP : ∀ m s, Measurable fun x => Phi ((x - m) / s) := fun m s =>
    (continuous_Phi.comp (by fun_prop)).measurable
  -- chain
  have chain := (lintegral_tri (h := fun x => Phi ((x - c * log n) / s1)) mG mβ).trans
    (add_le_add E1 ((lintegral_tri mβ mTu).trans (add_le_add E2 ((lintegral_tri mTu (mprof τ)).trans
      (add_le_add E3 ((lintegral_tri (mprof τ) (mP m2 s2)).trans (add_le_add E4
        ((lintegral_tri (mP m2 s2) (mP m2 s1)).trans (add_le_add E5 E6)))))))))
  refine chain.trans ?_
  -- real bounds
  set Q := √(L * ℓ)
  have hQ1 : 1 ≤ Q := Real.one_le_sqrt.2 (by nlinarith)
  have hrQ : √L ≤ Q := sqrt_le_sqrt (by nlinarith)
  have hℓQ : ℓ ≤ Q := Real.le_sqrt_of_sq_le (by nlinarith)
  have hr1 : 1 ≤ √L := Real.one_le_sqrt.2 (by linarith)
  have hrr : √L ^ 2 = L := sq_sqrt hL0.le
  have hW := hWk n le_rfl
  have hWb : ENNReal.ofReal (Ks * IdE) * F.Wint n ≤ ENNReal.ofReal (Ks * IdE * (Cw' * (1 + L))) := by
    rw [ENNReal.ofReal_mul (show 0 ≤ Ks * IdE by positivity)]; gcongr
  -- bounds on the individual real terms
  have b1 : 2 * A ≤ 2 * (√(8 * v / 3) + |c|) * Q := by
    have e : s0 * R = √(8 * v / 3) * Q := by
      simp only [s0, R, Q]; rw [← sqrt_mul (by positivity), ← sqrt_mul (by positivity)]
      congr 1; ring
    have : |m0| ≤ |c| * Q := by
      simp only [m0]; rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ ℓ)]
      exact mul_le_mul_of_nonneg_left hℓQ (abs_nonneg _)
    simp only [A]; rw [e]; nlinarith
  have b2a : Ks * s0 * IE ≤ √v * IE * (1 + KB) * Q := by
    have e : Ks * s0 = √v * (1 / √L + KB) := by
      simp only [Ks, s0]; rw [sqrt_mul hv.le]; field_simp; linear_combination hrr
    rw [e]
    have : 1 / √L ≤ 1 := by rw [div_le_one hsL]; exact hr1
    have h0 : 0 ≤ √v * IE * (1 + KB) := by positivity
    calc √v * (1 / √L + KB) * IE ≤ √v * IE * (1 + KB) * 1 := by nlinarith [mul_nonneg hsv.le hIE]
      _ ≤ _ := mul_le_mul_of_nonneg_left hQ1 h0
  have b2b : Ks * IdE * (Cw' * (1 + L)) ≤ IdE * Cw' * (2 + 2 * KB) * Q := by
    have e1 : 1 / L * (1 + L) = 1 / L + 1 := by field_simp
    have e2 : KB / √L * (1 + L) = KB * (1 / √L + √L) := by
      rw [show (1 + L) = 1 + √L ^ 2 by rw [hrr]]; field_simp
    have e : Ks * (1 + L) = 1 / L + 1 + KB * (1 / √L + √L) := by
      simp only [Ks]; rw [add_mul, e1, e2]
    have h1 : 1 / L ≤ 1 := by rw [div_le_one hL0]; linarith
    have h2 : 1 / √L ≤ √L := by rw [div_le_iff₀ hsL]; nlinarith
    have : Ks * (1 + L) ≤ (2 + 2 * KB) * Q := by
      rw [e]; nlinarith [mul_le_mul_of_nonneg_left h2 hKB]
    have h0 : 0 ≤ IdE * Cw' := by positivity
    calc Ks * IdE * (Cw' * (1 + L)) = IdE * Cw' * (Ks * (1 + L)) := by ring
      _ ≤ IdE * Cw' * ((2 + 2 * KB) * Q) := mul_le_mul_of_nonneg_left this h0
      _ = _ := by ring
  have b3 : (K1 + K2 * (Cw' * (1 + L))) * (2 / √(L - 1)) ≤ 4 * (K1 + 2 * K2 * Cw') * Q := by
    have hl1 := sqrt_pos.2 (show 0 < L - 1 by linarith)
    have hhalf : √L / 2 ≤ √(L - 1) := by
      rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2), show √(L - 1) * 2 = √((L - 1) * 4) by
        rw [sqrt_mul (by linarith), show (4:ℝ) = 2 ^ 2 by norm_num, sqrt_sq (by norm_num)]]
      exact sqrt_le_sqrt (by linarith)
    have h2 : 2 / √(L - 1) ≤ 4 / √L := by
      rw [div_le_div_iff₀ hl1 hsL]; linarith
    have h3 : (K1 + K2 * (Cw' * (1 + L))) * (4 / √L) ≤ 4 * (K1 + 2 * K2 * Cw') * √L := by
      have e : (K1 + K2 * (Cw' * (1 + L))) * (4 / √L) = 4 * (K1 / √L + K2 * Cw' * (1 / √L + √L)) := by
        field_simp; rw [hrr]
      rw [e]
      have a1 : K1 / √L ≤ K1 * √L := by
        rw [div_le_iff₀ hsL]; nlinarith
      have a2 : 1 / √L + √L ≤ 2 * √L := by
        have : 1 / √L ≤ √L := by rw [div_le_iff₀ hsL]; nlinarith
        linarith
      have h0 : 0 ≤ K2 * Cw' := by positivity
      nlinarith [mul_le_mul_of_nonneg_left a2 h0]
    calc _ ≤ (K1 + K2 * (Cw' * (1 + L))) * (4 / √L) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ ≤ 4 * (K1 + 2 * K2 * Cw') * √L := h3
      _ ≤ _ := mul_le_mul_of_nonneg_left hrQ (by positivity)
  have b4 : KB * √v * IE ≤ KB * √v * IE * Q := le_mul_of_one_le_right (by positivity) hQ1
  have b5 : (s2 - s1) / s1 * s2 * (2 * phi 0) ≤ 4 * phi 0 * √v * Q := by
    have hsub : s2 - s1 ≤ √v * √L := by
      have : s2 ≤ √v * √L + s1 := by
        simp only [s2, s1, τ]
        rw [sqrt_le_left (by positivity)]
        have := sq_sqrt (show 0 ≤ v * n by positivity)
        nlinarith [mul_pos hsv hsL, sq_sqrt hv.le, mul_nonneg (mul_nonneg hsv.le hsL.le) hs1.le]
      linarith
    have hrat : s2 ≤ 2 * s1 := by
      simp only [s2, s1, τ]
      rw [sqrt_le_left (by positivity)]
      nlinarith [sq_sqrt (show 0 ≤ v * n by positivity)]
    have : (s2 - s1) / s1 * s2 ≤ 2 * (√v * √L) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hs1]
      nlinarith [sub_nonneg.2 h12]
    calc _ ≤ 2 * (√v * √L) * (2 * phi 0) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = 4 * phi 0 * √v * √L := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hrQ (by positivity)
  have b6 : |m2 - c * log n| ≤ |c| * Q := by
    simp only [m2]
    rw [← mul_sub, abs_mul]
    have hlog : |log τ - log n| ≤ 1 := by
      have h1 : log (n:ℝ) ≤ log τ := Real.log_le_log hn0 (by linarith)
      rw [abs_of_nonneg (by linarith), ← Real.log_div hτ0.ne' hn0.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < τ / n by positivity)
      have : τ / n ≤ 2 := by rw [div_le_iff₀ hn0]; linarith
      linarith
    exact mul_le_mul_of_nonneg_left (hlog.trans hQ1) (abs_nonneg c)
  -- combine
  have hfin := ENNReal.ofReal_le_ofReal (show 2 * A + (Ks * s0 * IE + Ks * IdE * (Cw' * (1 + L)) +
      ((K1 + K2 * (Cw' * (1 + L))) * (2 / √(L - 1)) + (KB * √v * IE +
      ((s2 - s1) / s1 * s2 * (2 * phi 0) + |m2 - c * log n|)))) ≤
      (2 * (√(8 * v / 3) + |c|) + √v * IE * (1 + KB) + IdE * Cw' * (2 + 2 * KB) +
        4 * (K1 + 2 * K2 * Cw') + KB * √v * IE + 4 * phi 0 * √v + |c|) * Q by linarith)
  have p1 : 0 ≤ 2 * A := by positivity
  have p2a : 0 ≤ Ks * s0 * IE := by positivity
  have p2b : 0 ≤ Ks * IdE * (Cw' * (1 + L)) := by positivity
  have p3 : 0 ≤ (K1 + K2 * (Cw' * (1 + L))) * (2 / √(L - 1)) := by
    have := sqrt_nonneg (L - 1); positivity
  have p4 : 0 ≤ KB * √v * IE := by positivity
  have p5 : 0 ≤ (s2 - s1) / s1 * s2 * (2 * phi 0) := by
    have := sub_nonneg.2 h12; positivity
  have p6 : 0 ≤ |m2 - c * log n| := abs_nonneg _
  have n6 := add_nonneg p5 p6
  have n5 := add_nonneg p4 n6
  have n4 := add_nonneg p3 n5
  have n2 := add_nonneg p2a p2b
  have n3 := add_nonneg n2 n4
  clear_value Q s1 s2 m2 τ Ks A R m0 s0 IE IdE Cw' u
  calc _ ≤ ENNReal.ofReal (2 * A) + (ENNReal.ofReal (Ks * s0 * IE) +
        ENNReal.ofReal (Ks * IdE * (Cw' * (1 + L))) +
        (ENNReal.ofReal ((K1 + K2 * (Cw' * (1 + L))) * (2 / √(L - 1))) +
          (ENNReal.ofReal (KB * √v * IE) +
            (ENNReal.ofReal ((s2 - s1) / s1 * s2 * (2 * phi 0)) +
              ENNReal.ofReal |m2 - c * log n|)))) := by
        gcongr
    _ = ENNReal.ofReal (2 * A + (Ks * s0 * IE + Ks * IdE * (Cw' * (1 + L)) +
        ((K1 + K2 * (Cw' * (1 + L))) * (2 / √(L - 1)) + (KB * √v * IE +
        ((s2 - s1) / s1 * s2 * (2 * phi 0) + |m2 - c * log n|))))) := by
        rw [ENNReal.ofReal_add p1 n3, ENNReal.ofReal_add n2 n4,
          ENNReal.ofReal_add p2a p2b, ENNReal.ofReal_add p3 n5,
          ENNReal.ofReal_add p4 n6, ENNReal.ofReal_add p5 p6]
    _ ≤ _ := hfin

/-- **Main theorem, mean form.** `e_n = c ln n + O(√(ln n ln ln n))`: for `n ≥ 16`,
`|e_n - c ln n| ≤ C √(ln n · ln ln n)`. -/
theorem main_mean (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ C, ∀ n : ℕ, 16 ≤ n →
      |F.eG (F.G n) - cdrift F v * log n| ≤ C * √(log n * log (log n)) := by
  obtain ⟨C, hC⟩ := main_L1 F v hc hv hσ
  refine ⟨|C|, fun n hn => ?_⟩
  set p := fun x => Phi ((x - cdrift F v * log n) / √(v * n))
  have hs : 0 < √(v * n) := sqrt_pos.2 (mul_pos hv (by have : (16:ℝ) ≤ n := by exact_mod_cast hn
                                                       linarith))
  have hQ : 0 ≤ |C| * √(log n * log (log n)) := mul_nonneg (abs_nonneg _) (sqrt_nonneg _)
  have hL := (hC n hn).trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C)
    (sqrt_nonneg _)))
  have hmeas : AEStronglyMeasurable (fun x => p x - F.G n x) volume :=
    (((continuous_Phi.comp (by fun_prop)).measurable).sub (F.measurable_G n)).aestronglyMeasurable
  have hfin : ∫⁻ x, ‖p x - F.G n x‖ₑ < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (hL.trans_lt ENNReal.ofReal_lt_top)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_sub_comm]
  have hint : Integrable (fun x => p x - F.G n x) := ⟨hmeas, hfin⟩
  have hH : Integrable (fun x => Hs x - p x) := integrable_H_sub_Phi (cdrift F v * log n) hs
  have hm : ∫ x, (Hs x - p x) = cdrift F v * log n := integral_H_sub_Phi _ hs
  have e : F.eG (F.G n) = (∫ x, (Hs x - p x)) + ∫ x, (p x - F.G n x) := by
    rw [← integral_add hH hint]; unfold Sqrt.IncFamily.eG; rw [G0_eq_Hs]
    congr 1; funext x; ring
  rw [e, hm, add_sub_cancel_left]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => abs_nonneg _)
    hint.abs.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hQ (le_trans (le_of_eq (lintegral_congr fun x => ?_)) hL)
  rw [abs_sub_comm]

end Final

end CausalSpectrum.LogGauss

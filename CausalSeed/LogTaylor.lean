/-
Stage 4, part 1: analytic tools for the residual lemma.

* the normal distribution function `Φ` and the third derivative `φ'''` of the density;
* a mean-value "ladder": a derivative bound `C |w - x|^k` on a segment integrates to
  `C |y - x|^{k+1}`, which yields Taylor remainders of any order without iterated
  derivatives;
* a window lemma: if `w = λ z + δ` with `λ² ≥ 1/2`, `0 ≤ λ ≤ 1`, `|δ| ≤ D`, then
  `(1 + |w|)^k φ(w) ≤ C_D E(z)` for `k ≤ 8`, where `E(z) = (1 + z²)⁴ e^{-z²/8}`;
* `E` is a `C¹` majorant profile: nonnegative, with continuous integrable derivative.
-/
import CausalSeed.LogCorrector
import CausalSeed.LogAmp

open MeasureTheory Set Filter Topology Real

namespace CausalSpectrum.LogGauss

/-! ### `Φ` and `φ'''` -/

/-- The standard normal distribution function `Φ(z) = ∫_{-∞}^z φ`. -/
noncomputable def Phi (z : ℝ) : ℝ := ∫ y in Iic z, phi y

theorem Phi_eq (z : ℝ) : Phi z = Phi 0 + ∫ y in (0:ℝ)..z, phi y := by
  rw [← intervalIntegral.integral_Iic_sub_Iic integrable_phi.integrableOn
    integrable_phi.integrableOn]
  simp [Phi]

theorem hasDerivAt_Phi (z : ℝ) : HasDerivAt Phi (phi z) z := by
  have h := (continuous_phi.integral_hasStrictDerivAt 0 z).hasDerivAt.const_add (Phi 0)
  have e : Phi = fun z => Phi 0 + ∫ y in (0:ℝ)..z, phi y := funext Phi_eq
  rw [e]; exact h

/-- `φ'''(z) = (3z - z³) φ(z)`. -/
noncomputable def dddphi (z : ℝ) : ℝ := (3 * z - z ^ 3) * phi z

theorem hasDerivAt_ddphi (z : ℝ) : HasDerivAt ddphi (dddphi z) z := by
  have := ((hasDerivAt_pow 2 z).sub_const 1).mul (hasDerivAt_phi z)
  exact this.congr_deriv (by simp only [dddphi, dphi]; push_cast; ring)

/-! ### Mean-value ladder -/

theorem mvt_abs {r r' : ℝ → ℝ} {x y C : ℝ} (hd : ∀ w ∈ uIcc x y, HasDerivAt r (r' w) w)
    (hb : ∀ w ∈ uIcc x y, |r' w| ≤ C) : |r y - r x| ≤ C * |y - x| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun w hw => (hd w hw).hasDerivWithinAt) (fun w hw => by simpa using hb w hw)
    (convex_uIcc x y) left_mem_uIcc right_mem_uIcc
  simpa [Real.norm_eq_abs] using this

theorem abs_sub_le_of_mem_uIcc {x y w : ℝ} (hw : w ∈ uIcc x y) : |w - x| ≤ |y - x| := by
  rcases le_total x y with h | h
  · rw [uIcc_of_le h] at hw
    rw [abs_of_nonneg (by linarith [hw.1]), abs_of_nonneg (by linarith)]; linarith [hw.2]
  · rw [uIcc_of_ge h] at hw
    rw [abs_of_nonpos (by linarith [hw.2]), abs_of_nonpos (by linarith)]; linarith [hw.1]

/-- **Ladder.** If `r(x) = 0` and `|r'(w)| ≤ C |w - x|^k` on `[x, y]`, then
`|r(y)| ≤ C |y - x|^{k+1}`. -/
theorem ladder {r r' : ℝ → ℝ} {x y C : ℝ} (k : ℕ) (h0 : r x = 0)
    (hd : ∀ w ∈ uIcc x y, HasDerivAt r (r' w) w)
    (hb : ∀ w ∈ uIcc x y, |r' w| ≤ C * |w - x| ^ k) (hC : 0 ≤ C) :
    |r y| ≤ C * |y - x| ^ (k + 1) := by
  have := mvt_abs (C := C * |y - x| ^ k) hd fun w hw =>
    (hb w hw).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (abs_sub_le_of_mem_uIcc hw) k) hC)
  rw [h0, sub_zero] at this; rw [pow_succ, ← mul_assoc]; exact this

/-! ### The window lemma and the majorant profile `E` -/

/-- The majorant profile `E(z) = (1 + z²)⁴ e^{-z²/8}`. -/
noncomputable def Emaj (z : ℝ) : ℝ := (1 + z ^ 2) ^ 4 * exp (-(z ^ 2 / 8))

/-- `E'(z)`. -/
noncomputable def dEmaj (z : ℝ) : ℝ :=
  (8 * z * (1 + z ^ 2) ^ 3 - z / 4 * (1 + z ^ 2) ^ 4) * exp (-(z ^ 2 / 8))

theorem Emaj_nonneg (z : ℝ) : 0 ≤ Emaj z := by unfold Emaj; positivity

theorem hasDerivAt_Emaj (z : ℝ) : HasDerivAt Emaj (dEmaj z) z := by
  have h1 : HasDerivAt (fun z : ℝ => (1 + z ^ 2) ^ 4) (4 * (1 + z ^ 2) ^ 3 * (2 * z)) z := by
    have := ((hasDerivAt_pow 2 z).const_add 1).pow 4
    convert this using 1; push_cast; ring
  have hin : HasDerivAt (fun z : ℝ => -(z ^ 2 / 8)) (-(z / 4)) z := by
    have := ((hasDerivAt_pow 2 z).div_const 8).neg
    convert this using 1; push_cast; ring
  have h2 := hin.exp
  show HasDerivAt (fun z => (1 + z ^ 2) ^ 4 * exp (-(z ^ 2 / 8))) _ z
  exact (h1.mul h2).congr_deriv (by simp only [dEmaj]; ring)

theorem continuous_dEmaj : Continuous dEmaj :=
  continuous_iff_continuousAt.2 fun z => by
    show ContinuousAt (fun z : ℝ => (8 * z * (1 + z ^ 2) ^ 3 - z / 4 * (1 + z ^ 2) ^ 4) *
      exp (-(z ^ 2 / 8))) z
    fun_prop

theorem phi_le_exp (w : ℝ) : phi w ≤ exp (-(w ^ 2 / 2)) := by
  unfold phi
  have h1 : 1 ≤ √(2 * π) := by
    rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt (by linarith [Real.two_le_pi])
  have : (√(2 * π))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1
  have := exp_pos (-(w ^ 2 / 2))
  nlinarith

/-- **Window lemma.** -/
theorem window {D : ℝ} (hD : 0 ≤ D) {k : ℕ} (hk : k ≤ 8) {z w lam : ℝ} (hl0 : 0 ≤ lam)
    (hl1 : lam ≤ 1) (hl2 : 1 / 2 ≤ lam ^ 2) (hw : |w - lam * z| ≤ D) :
    (1 + |w|) ^ k * phi w ≤ 16 * (1 + D) ^ 8 * exp (D ^ 2 / 2) * Emaj z := by
  have hp := phi_pos w
  have hwz : |w| ≤ |z| + D := by
    have : |lam * z| ≤ |z| := by
      rw [abs_mul, abs_of_nonneg hl0]; exact mul_le_of_le_one_left (abs_nonneg _) hl1
    have := abs_sub_abs_le_abs_sub w (lam * z)
    linarith
  have hpow : (1 + |w|) ^ k ≤ 16 * (1 + D) ^ 8 * (1 + z ^ 2) ^ 4 := by
    calc (1 + |w|) ^ k ≤ (1 + |w|) ^ 8 := pow_le_pow_right₀ (by linarith [abs_nonneg w]) hk
      _ ≤ ((1 + D) * (1 + |z|)) ^ 8 := by
          apply pow_le_pow_left₀ (by positivity); nlinarith [abs_nonneg z]
      _ = (1 + D) ^ 8 * ((1 + |z|) ^ 2) ^ 4 := by ring
      _ ≤ (1 + D) ^ 8 * (2 * (1 + z ^ 2)) ^ 4 := by
          gcongr; nlinarith [sq_abs z, abs_nonneg z, sq_nonneg (|z| - 1)]
      _ = 16 * (1 + D) ^ 8 * (1 + z ^ 2) ^ 4 := by ring
  have hexp : phi w ≤ exp (D ^ 2 / 2) * exp (-(z ^ 2 / 8)) := by
    rw [← exp_add]
    refine (phi_le_exp w).trans (exp_le_exp.2 ?_)
    have h1 : (lam * z) ^ 2 ≤ 2 * w ^ 2 + 2 * D ^ 2 := by
      have : (w - lam * z) ^ 2 ≤ D ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hw 2
      nlinarith [sq_nonneg (w + (w - lam * z))]
    have h2 : z ^ 2 / 2 ≤ (lam * z) ^ 2 := by rw [mul_pow]; nlinarith [sq_nonneg z]
    nlinarith
  calc (1 + |w|) ^ k * phi w ≤ (16 * (1 + D) ^ 8 * (1 + z ^ 2) ^ 4) *
        (exp (D ^ 2 / 2) * exp (-(z ^ 2 / 8))) :=
        mul_le_mul hpow hexp hp.le (by positivity)
    _ = _ := by unfold Emaj; ring

/-! ### Integrability of `E` and `E'` -/

theorem integrable_wexp (k : ℕ) : Integrable fun z => (1 + |z|) ^ k * exp (-(z ^ 2 / 8)) := by
  have hz : ∀ j : ℕ, Integrable fun z => z ^ j * exp (-(z ^ 2 / 8)) := fun j => by
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := 1 / 8) (by norm_num)
      (s := (j : ℝ)) (by have := j.cast_nonneg (α := ℝ); linarith)
    refine h.congr (ae_of_all _ fun z => ?_)
    simp only [Real.rpow_natCast]; rw [show -(1 / 8) * z ^ 2 = -(z ^ 2 / 8) by ring]
  have h0 : Integrable fun z => exp (-(z ^ 2 / 8)) := by simpa using hz 0
  have h : Integrable fun z => 2 ^ k * (exp (-(z ^ 2 / 8)) + |z ^ k * exp (-(z ^ 2 / 8))|) :=
    (h0.add (hz k).abs).const_mul _
  refine h.mono' (Continuous.aestronglyMeasurable (by fun_prop)) (ae_of_all _ fun z => ?_)
  have hp := exp_pos (-(z ^ 2 / 8))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), abs_mul, abs_of_pos hp]
  nlinarith [one_add_abs_pow_le z k]

theorem one_add_sq_le (z : ℝ) : 1 + z ^ 2 ≤ (1 + |z|) ^ 2 := by
  nlinarith [sq_abs z, abs_nonneg z]

theorem abs_Emaj_le (z : ℝ) : |Emaj z| ≤ 1 * ((1 + |z|) ^ 8 * exp (-(z ^ 2 / 8))) := by
  rw [abs_of_nonneg (Emaj_nonneg z), one_mul]; unfold Emaj
  gcongr
  calc (1 + z ^ 2) ^ 4 ≤ ((1 + |z|) ^ 2) ^ 4 := by gcongr; exact one_add_sq_le z
    _ = (1 + |z|) ^ 8 := by ring

theorem abs_dEmaj_le (z : ℝ) : |dEmaj z| ≤ 9 * ((1 + |z|) ^ 9 * exp (-(z ^ 2 / 8))) := by
  unfold dEmaj
  have hp := exp_pos (-(z ^ 2 / 8))
  rw [abs_mul, abs_of_pos hp]
  have ha : |z| ≤ 1 + |z| := by linarith
  have h1 : 1 + z ^ 2 ≤ (1 + |z|) ^ 2 := one_add_sq_le z
  have h0 : 0 ≤ 1 + z ^ 2 := by positivity
  have hq : 1 ≤ 1 + |z| := by linarith [abs_nonneg z]
  have e3 : (1 + z ^ 2) ^ 3 ≤ (1 + |z|) ^ 6 := by
    calc (1 + z ^ 2) ^ 3 ≤ ((1 + |z|) ^ 2) ^ 3 := by gcongr
      _ = _ := by ring
  have e4 : (1 + z ^ 2) ^ 4 ≤ (1 + |z|) ^ 8 := by
    calc (1 + z ^ 2) ^ 4 ≤ ((1 + |z|) ^ 2) ^ 4 := by gcongr
      _ = _ := by ring
  have hb : |8 * z * (1 + z ^ 2) ^ 3 - z / 4 * (1 + z ^ 2) ^ 4| ≤ 9 * (1 + |z|) ^ 9 := by
    refine (abs_sub _ _).trans ?_
    have eA : |8 * z * (1 + z ^ 2) ^ 3| = 8 * |z| * (1 + z ^ 2) ^ 3 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg h0 3)]; norm_num
    have eB : |z / 4 * (1 + z ^ 2) ^ 4| = |z| / 4 * (1 + z ^ 2) ^ 4 := by
      rw [abs_mul, abs_div, abs_of_nonneg (pow_nonneg h0 4)]; norm_num
    rw [eA, eB]
    have : (1 + |z|) ^ 7 ≤ (1 + |z|) ^ 9 := pow_le_pow_right₀ hq (by norm_num)
    have : 8 * |z| * (1 + z ^ 2) ^ 3 ≤ 8 * (1 + |z|) ^ 7 := by
      calc 8 * |z| * (1 + z ^ 2) ^ 3 ≤ 8 * (1 + |z|) * (1 + |z|) ^ 6 := by gcongr
        _ = _ := by ring
    have : |z| / 4 * (1 + z ^ 2) ^ 4 ≤ (1 + |z|) ^ 9 := by
      calc |z| / 4 * (1 + z ^ 2) ^ 4 ≤ (1 + |z|) * (1 + |z|) ^ 8 := by
            gcongr; linarith [abs_nonneg z]
        _ = _ := by ring
    linarith
  nlinarith

theorem integrable_of_wexp {F : ℝ → ℝ} (hF : Continuous F) {K : ℝ} {k : ℕ}
    (h : ∀ z, |F z| ≤ K * ((1 + |z|) ^ k * exp (-(z ^ 2 / 8)))) : Integrable F :=
  ((integrable_wexp k).const_mul K).mono' hF.aestronglyMeasurable
    (ae_of_all _ fun z => by simpa [Real.norm_eq_abs] using h z)

theorem continuous_Emaj : Continuous Emaj := by unfold Emaj; fun_prop

theorem integrable_Emaj : Integrable Emaj := integrable_of_wexp continuous_Emaj abs_Emaj_le
theorem integrable_dEmaj : Integrable dEmaj := integrable_of_wexp continuous_dEmaj abs_dEmaj_le

/-- **Scaled majorant.** For `K ≥ 0`, `m` and `s > 0`, `x ↦ K E((x - m)/s)` is a `C¹`
majorant in the sense of `Sqrt.IncFamily.Majorant`, with `L¹` norms `K s ∫E` and `K ∫|E'|`. -/
theorem majorant_scaled {K : ℝ} (hK : 0 ≤ K) (m : ℝ) {s : ℝ} (hs : 0 < s) :
    Sqrt.IncFamily.Majorant (fun x => K * Emaj ((x - m) / s))
      (fun x => K * (dEmaj ((x - m) / s) / s)) := by
  refine ⟨fun y => (hasDerivAt_comp_affine hasDerivAt_Emaj m y).const_mul K,
    continuous_const.mul ((continuous_dEmaj.comp (by fun_prop :
      Continuous fun x : ℝ => (x - m) / s)).div_const s), ?_, ?_,
    fun y => mul_nonneg hK (Emaj_nonneg _)⟩
  · refine Integrable.const_mul ?_ K
    have : Integrable fun x => dEmaj (s⁻¹ * x) / s :=
      ((integrable_comp_mul_left_iff dEmaj (inv_ne_zero hs.ne')).2 integrable_dEmaj).div_const s
    have := this.comp_sub_right m
    refine this.congr (ae_of_all _ fun x => ?_)
    show dEmaj (s⁻¹ * (x - m)) / s = dEmaj ((x - m) / s) / s
    rw [div_eq_inv_mul (x - m)]
  · have hE : Tendsto Emaj atBot (𝓝 0) :=
      tendsto_zero_of_hasDerivAt_of_integrableOn_Iic (a := 0) (fun z _ => hasDerivAt_Emaj z)
        integrable_dEmaj.integrableOn integrable_Emaj.integrableOn
    have hz : Tendsto (fun x => (x - m) / s) atBot atBot :=
      (tendsto_atBot_add_const_right _ (-m) tendsto_id).atBot_div_const hs |>.congr
        fun x => by simp only [id]; ring
    simpa using (hE.comp hz).const_mul K

theorem lintegral_majorant_scaled {K : ℝ} (hK : 0 ≤ K) (m : ℝ) {s : ℝ} (hs : 0 < s) :
    (∫⁻ x, ‖K * Emaj ((x - m) / s)‖ₑ) = ENNReal.ofReal (K * s * ∫ z, Emaj z) ∧
    (∫⁻ x, ‖K * (dEmaj ((x - m) / s) / s)‖ₑ) = ENNReal.ofReal (K * ∫ z, |dEmaj z|) := by
  have hi1 : Integrable fun x => K * Emaj ((x - m) / s) := by
    have : Integrable fun x => Emaj (s⁻¹ * x) :=
      (integrable_comp_mul_left_iff Emaj (inv_ne_zero hs.ne')).2 integrable_Emaj
    exact ((this.comp_sub_right m).const_mul K).congr (ae_of_all _ fun x => by
      show K * Emaj (s⁻¹ * (x - m)) = K * Emaj ((x - m) / s)
      rw [div_eq_inv_mul (x - m)])
  have hi2 := (majorant_scaled hK m hs).integ
  constructor
  · rw [← ofReal_integral_norm_eq_lintegral_enorm hi1]; congr 1
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK]
    rw [integral_const_mul, integral_abs_comp_affine Emaj m hs]
    simp_rw [abs_of_nonneg (Emaj_nonneg _)]; ring
  · rw [← ofReal_integral_norm_eq_lintegral_enorm hi2]; congr 1
    simp_rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hK, abs_div, abs_of_pos hs]
    rw [integral_const_mul, integral_div, integral_abs_comp_affine dEmaj m hs]
    field_simp

end CausalSpectrum.LogGauss

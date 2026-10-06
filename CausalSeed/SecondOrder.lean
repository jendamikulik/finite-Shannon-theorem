/-
Second order of Theorem 1 in the 5 October 2026 note.

Proved here, with no `sorry`:
* `∫_{0}^{∞} x exp(-x²/2) dx = 1`
* `∫_{0}^{∞} ∫_{t}^{∞} exp(-x²/2) dx dt = 1`
* the mean of profile (13) is `√(2/π) (a - b)`, for `0 < b` and for `b = 0 < a`
* an additive gap of at most `c⋆` does not change a `√n` coefficient.
  This is the last step of the proof of Theorem 1: once the envelope mean
  has that second order, so does every seed between the envelope and the
  envelope plus `c⋆`, in particular the greedy seed

Not proved here: `Gₙ(x√n) → F(x)`, dominated convergence of the means, and
the Fan–Grama–Liu logarithm.
-/
import CausalSeed.Note
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.Basic

noncomputable section
open Classical MeasureTheory Set Filter intervalIntegral
namespace CausalSpectrum

/-- `√(2/π) (a - b)`, the coefficient of `√n` in Theorem 1. -/
noncomputable def secondOrderCoeff (a b : ℝ) : ℝ :=
  Real.sqrt (2 / Real.pi) * (a - b)

/-- Unnormalized Gaussian `exp(-x²/2)`. -/
noncomputable def gaussRaw (x : ℝ) : ℝ := Real.exp (-(x ^ 2) / 2)

/-- Tail `∫_{t}^{∞} exp(-x²/2) dx`. -/
noncomputable def gaussTail (t : ℝ) : ℝ := ∫ x in Ioi t, gaussRaw x

lemma hasDerivAt_neg_gaussRaw (x : ℝ) :
    HasDerivAt (fun y : ℝ => -gaussRaw y) (x * gaussRaw x) x := by
  unfold gaussRaw
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have hinner : HasDerivAt (fun y : ℝ => -(y ^ 2) / 2) (-x) x := by
    have h := hsq.neg.div_const (2 : ℝ)
    simpa [neg_div, mul_comm, mul_left_comm, mul_assoc] using h
  have hexp : HasDerivAt (fun y => Real.exp (-(y ^ 2) / 2))
      (Real.exp (-(x ^ 2) / 2) * -x) x := by
    have hcomp := (Real.hasDerivAt_exp (-(x ^ 2) / 2)).comp x hinner
    have hfun : (fun y => Real.exp (-(y ^ 2) / 2)) =
        Real.exp ∘ fun y => -(y ^ 2) / 2 := by
      ext y; rfl
    rw [hfun]
    exact hcomp
  have hneg := hexp.neg
  have hd : -(Real.exp (-(x ^ 2) / 2) * -x) = x * Real.exp (-(x ^ 2) / 2) := by ring
  have hfun : (fun y => -Real.exp (-(y ^ 2) / 2)) =
      -fun y => Real.exp (-(y ^ 2) / 2) := by
    ext y; rfl
  rw [hfun, ← hd]
  exact hneg

lemma gaussRaw_tendsto_zero : Tendsto gaussRaw atTop (nhds 0) := by
  unfold gaussRaw
  refine (Real.tendsto_exp_atBot.comp ?_).congr fun _ => rfl
  exact (tendsto_neg_atTop_atBot.comp
    (tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0))).atBot_div_const (by norm_num)

lemma continuous_gaussRaw : Continuous gaussRaw := by
  unfold gaussRaw
  exact Real.continuous_exp.comp <| (continuous_id.pow 2).neg.div_const 2

lemma integrable_x_gaussRaw : Integrable fun x : ℝ => x * gaussRaw x := by
  have h := integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr (Eventually.of_forall fun x => ?_)
  unfold gaussRaw
  change x * Real.exp (-(1 / 2) * x ^ 2) = x * Real.exp (-(x ^ 2) / 2)
  have hexp : -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 := by ring
  rw [hexp]

lemma gaussRaw_integrable : Integrable gaussRaw := by
  have h := integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)
  refine h.congr (Eventually.of_forall fun x => ?_)
  unfold gaussRaw
  change Real.exp (-(1 / 2) * x ^ 2) = Real.exp (-(x ^ 2) / 2)
  have hexp : -(1 / 2 : ℝ) * x ^ 2 = -(x ^ 2) / 2 := by ring
  rw [hexp]

theorem integral_x_gaussRaw :
    ∫ x in Ioi (0 : ℝ), x * gaussRaw x = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ),
      HasDerivAt (fun y => -gaussRaw y) (x * gaussRaw x) x :=
    fun x _ => hasDerivAt_neg_gaussRaw x
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrable_x_gaussRaw.integrableOn
    gaussRaw_tendsto_zero.neg]
  simp [gaussRaw, Real.exp_zero]

lemma integral_x_gaussRaw_Ioi (t : ℝ) :
    ∫ x in Ioi t, x * gaussRaw x = gaussRaw t := by
  have hderiv : ∀ x ∈ Ici t, HasDerivAt (fun y => -gaussRaw y) (x * gaussRaw x) x :=
    fun x _ => hasDerivAt_neg_gaussRaw x
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv integrable_x_gaussRaw.integrableOn
    gaussRaw_tendsto_zero.neg]
  simp [gaussRaw]

lemma gaussTail_eq_sub (A : ℝ) :
    gaussTail A = gaussTail 0 - ∫ x in (0 : ℝ)..A, gaussRaw x := by
  have h := integral_Ioi_sub_Ioi' (a := (0 : ℝ)) (b := A) (f := gaussRaw)
    (gaussRaw_integrable.integrableOn (s := Ioi (0 : ℝ)))
    (gaussRaw_integrable.integrableOn (s := Ioi A))
  unfold gaussTail at h ⊢
  linarith

lemma continuous_gaussTail : Continuous gaussTail := by
  have hprim : Continuous fun A : ℝ => ∫ x in (0 : ℝ)..A, gaussRaw x :=
    gaussRaw_integrable.continuous_primitive 0
  convert continuous_const.sub hprim using 1
  ext A
  simp only [Pi.sub_apply]
  exact gaussTail_eq_sub A

lemma gaussTail_nonneg (t : ℝ) : 0 ≤ gaussTail t :=
  integral_nonneg fun _ => Real.exp_nonneg _

lemma gaussTail_antitone : Antitone gaussTail := by
  intro s t hst
  have h := integral_Ioi_sub_Ioi gaussRaw_integrable.integrableOn hst
  have hnn : 0 ≤ ∫ x in s..t, gaussRaw x := by
    rw [integral_of_le hst]
    exact integral_nonneg fun _ => Real.exp_nonneg _
  have : gaussTail s - gaussTail t = ∫ x in s..t, gaussRaw x := by
    simpa [gaussTail] using h
  linarith

lemma gaussTail_le (t : ℝ) (ht : 0 < t) : gaussTail t ≤ gaussRaw t / t := by
  have hpoint : ∀ x ∈ Ioi t, gaussRaw x ≤ (x / t) * gaussRaw x := by
    intro x hx
    have hle : (1 : ℝ) ≤ x / t := (one_le_div ht).mpr (le_of_lt hx)
    exact le_mul_of_one_le_left (Real.exp_nonneg _) hle
  have hbound : IntegrableOn (fun x => (x / t) * gaussRaw x) (Ioi t) := by
    have hI : IntegrableOn (fun x => (1 / t) * (x * gaussRaw x)) (Ioi t) :=
      (integrable_x_gaussRaw.integrableOn (s := Ioi t)).const_mul (1 / t)
    refine hI.congr_fun (fun x _ => ?_) measurableSet_Ioi
    ring
  have hmono := setIntegral_mono_on gaussRaw_integrable.integrableOn hbound
    measurableSet_Ioi hpoint
  have hscale : ∫ x in Ioi t, (x / t) * gaussRaw x = gaussRaw t / t := by
    have hmul : ∫ x in Ioi t, (1 / t) * (x * gaussRaw x) =
        (1 / t) * ∫ x in Ioi t, x * gaussRaw x :=
      MeasureTheory.integral_const_mul _ _
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, integral_x_gaussRaw_Ioi] using hmul
  unfold gaussTail
  exact le_trans hmono (le_of_eq hscale)

lemma gaussTail_integrableOn : IntegrableOn gaussTail (Ioi (0 : ℝ)) := by
  have hnear : IntegrableOn gaussTail (Ioc (0 : ℝ) 1) := by
    have hcc : IntegrableOn gaussTail (Icc (0 : ℝ) 1) :=
      continuous_gaussTail.continuousOn.integrableOn_Icc
    exact hcc.mono_set Ioc_subset_Icc_self
  have hfar : IntegrableOn gaussTail (Ioi (1 : ℝ)) := by
    refine Integrable.mono' (gaussRaw_integrable.integrableOn (s := Ioi (1 : ℝ)))
      (continuous_gaussTail.aestronglyMeasurable (μ := volume.restrict (Ioi 1))) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussTail_nonneg t)]
    have ht1 : (1 : ℝ) < t := ht
    have hle := gaussTail_le t (lt_trans zero_lt_one ht1)
    have hdiv : gaussRaw t / t ≤ gaussRaw t := by
      rw [div_le_iff₀ (lt_trans zero_lt_one ht1)]
      unfold gaussRaw
      simpa [mul_one] using
        mul_le_mul_of_nonneg_left (le_of_lt ht1) (Real.exp_nonneg (-(t ^ 2) / 2))
    exact le_trans hle hdiv
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)]
  exact hnear.union hfar

theorem integral_gaussTail : ∫ t in Ioi (0 : ℝ), gaussTail t = 1 := by
  let mass : ℝ → ℝ := fun A => ∫ t in (0 : ℝ)..A, gaussTail t
  let moment : ℝ → ℝ := fun A =>
    (∫ x in (0 : ℝ)..A, x * gaussRaw x) + A * gaussTail A
  have hmass : ∀ A, HasDerivAt mass (gaussTail A) A := by
    intro A
    exact integral_hasDerivAt_right (continuous_gaussTail.intervalIntegrable 0 A)
      (continuous_gaussTail.stronglyMeasurableAtFilter volume (nhds A))
      continuous_gaussTail.continuousAt
  have hcontx : Continuous fun x => x * gaussRaw x := continuous_id.mul continuous_gaussRaw
  have hid : ∀ A, HasDerivAt (fun A => ∫ x in (0 : ℝ)..A, x * gaussRaw x)
      (A * gaussRaw A) A := by
    intro A
    exact integral_hasDerivAt_right (hcontx.intervalIntegrable 0 A)
      (hcontx.stronglyMeasurableAtFilter volume (nhds A)) hcontx.continuousAt
  have htail : ∀ A, HasDerivAt gaussTail (-gaussRaw A) A := by
    intro A
    have hprim : HasDerivAt (fun B => ∫ x in (0 : ℝ)..B, gaussRaw x) (gaussRaw A) A :=
      integral_hasDerivAt_right (continuous_gaussRaw.intervalIntegrable 0 A)
        (continuous_gaussRaw.stronglyMeasurableAtFilter volume (nhds A))
        continuous_gaussRaw.continuousAt
    have hfun : HasDerivAt (fun B => gaussTail 0 - ∫ x in (0 : ℝ)..B, gaussRaw x)
        (-gaussRaw A) A := by
      have hsub := (hasDerivAt_const A (gaussTail 0)).sub hprim
      have heqfun :
          (fun B => gaussTail 0 - ∫ x in (0 : ℝ)..B, gaussRaw x) =
            (fun _ => gaussTail 0) - fun B => ∫ x in (0 : ℝ)..B, gaussRaw x := by
        funext B; rfl
      rw [heqfun, ← zero_sub (gaussRaw A)]
      exact hsub
    have heq : gaussTail = fun B => gaussTail 0 - ∫ x in (0 : ℝ)..B, gaussRaw x := by
      funext B
      exact gaussTail_eq_sub B
    rw [heq]
    exact hfun
  have hmoment : ∀ A, HasDerivAt moment (gaussTail A) A := by
    intro A
    have hprod : HasDerivAt (fun B => B * gaussTail B)
        (1 * gaussTail A + A * -gaussRaw A) A :=
      (hasDerivAt_id' A).mul (htail A)
    have hsum := (hid A).add hprod
    have hcoeff : A * gaussRaw A + (1 * gaussTail A + A * -gaussRaw A) = gaussTail A := by
      ring
    rw [hcoeff] at hsum
    have heqfun : moment =
        (fun A => ∫ x in (0 : ℝ)..A, x * gaussRaw x) + fun B => B * gaussTail B := by
      funext A; rfl
    rw [heqfun]
    exact hsum
  have hmassCont : Continuous mass :=
    continuous_primitive (fun a b => continuous_gaussTail.intervalIntegrable a b) 0
  have hmomentCont : Continuous moment :=
    (integrable_x_gaussRaw.continuous_primitive 0).add (continuous_id.mul continuous_gaussTail)
  have heqOn : ∀ B, 0 ≤ B → ∀ y ∈ Icc (0 : ℝ) B, mass y = moment y := by
    intro B hB
    refine eq_of_has_deriv_right_eq (f' := gaussTail)
      (fun x _ => (hmass x).hasDerivWithinAt)
      (fun x _ => (hmoment x).hasDerivWithinAt)
      (hmassCont.continuousOn.mono (subset_univ (Icc (0 : ℝ) B)))
      (hmomentCont.continuousOn.mono (subset_univ (Icc (0 : ℝ) B))) ?_
    simp [mass, moment, integral_same]
  have heqB : mass =ᶠ[atTop] moment := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with B hB
    exact heqOn B hB B ⟨hB, le_rfl⟩
  have hmom : Tendsto moment atTop (nhds 1) := by
    have hint : Tendsto (fun A => ∫ x in (0 : ℝ)..A, x * gaussRaw x) atTop (nhds 1) := by
      simpa [integral_x_gaussRaw] using
        intervalIntegral_tendsto_integral_Ioi (0 : ℝ) integrable_x_gaussRaw.integrableOn tendsto_id
    have hprod : Tendsto (fun A => A * gaussTail A) atTop (nhds 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds gaussRaw_tendsto_zero ?_ ?_
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
        exact mul_nonneg hA.le (gaussTail_nonneg A)
      · filter_upwards [eventually_gt_atTop (0 : ℝ)] with A hA
        have hle := gaussTail_le A hA
        have : A * gaussTail A ≤ A * (gaussRaw A / A) :=
          mul_le_mul_of_nonneg_left hle hA.le
        simpa [mul_div_cancel₀ _ hA.ne'] using this
    simpa [moment] using hint.add hprod
  have hmassLim : Tendsto mass atTop (nhds (∫ t in Ioi (0 : ℝ), gaussTail t)) :=
    intervalIntegral_tendsto_integral_Ioi 0 gaussTail_integrableOn tendsto_id
  have hmass1 : Tendsto mass atTop (nhds 1) := Tendsto.congr' heqB.symm hmom
  exact tendsto_nhds_unique hmassLim hmass1

/-- Scaling the tail: `∫₀^∞ gaussTail(t/c) dt = c`. -/
lemma integral_gaussTail_scale (c : ℝ) (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), gaussTail (t / c) = c := by
  have h := integral_comp_mul_right_Ioi (fun u : ℝ => gaussTail u) (0 : ℝ) (inv_pos.mpr hc)
  have hfun : (fun t : ℝ => gaussTail (t / c)) = fun t => gaussTail (t * c⁻¹) := by
    funext t
    rw [div_eq_mul_inv]
  rw [hfun]
  simpa [inv_inv, zero_mul, smul_eq_mul, integral_gaussTail] using h

/-- `∫₀^∞ (1 - Φ(t/c)) dt = c / √(2π)`, the evaluated tail in Lemma 13. -/
theorem integral_normalTail_scale (c : ℝ) (hc : 0 < c) :
    ∫ t in Ioi (0 : ℝ), gaussTail (t / c) / Real.sqrt (2 * Real.pi) =
      c / Real.sqrt (2 * Real.pi) := by
  rw [MeasureTheory.integral_div, integral_gaussTail_scale c hc]

lemma two_div_sqrt_two_pi :
    (2 : ℝ) / Real.sqrt (2 * Real.pi) = Real.sqrt (2 / Real.pi) := by
  have hL : 0 ≤ (2 : ℝ) / Real.sqrt (2 * Real.pi) := by positivity
  have hR : 0 ≤ Real.sqrt (2 / Real.pi) := Real.sqrt_nonneg _
  refine (sq_eq_sq₀ hL hR).mp ?_
  rw [div_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)]
  field_simp

/-- `1 - F(t)` for `t > 0`, with `F` the profile (13). -/
noncomputable def profilePos (a b t : ℝ) : ℝ :=
  (2 * a / (a + b)) * (gaussTail (t / a) / Real.sqrt (2 * Real.pi))

/-- `F(-t)` for `t > 0`. -/
noncomputable def profileNeg (a b t : ℝ) : ℝ :=
  (2 * b / (a + b)) * (gaussTail (t / b) / Real.sqrt (2 * Real.pi))

/-- Half-normal profile `1 - F_{a,0}(t) = 2(1 - Φ(t/a))`. -/
noncomputable def profileHalf (a t : ℝ) : ℝ :=
  2 * (gaussTail (t / a) / Real.sqrt (2 * Real.pi))

/-- Mean of profile (13) for `0 < b ≤ a` is not assumed in the order of `a, b`:
both scales are positive. `profilePos` is `1 - F(t)` and `profileNeg` is `F(-t)`. -/
theorem profile_mean (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), profilePos a b t) - (∫ t in Ioi (0 : ℝ), profileNeg a b t) =
      secondOrderCoeff a b := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  have hab : a + b ≠ 0 := by linarith
  have hpos : ∫ t in Ioi (0 : ℝ), profilePos a b t =
      (2 * a / (a + b)) * (a / Real.sqrt (2 * Real.pi)) := by
    simp only [profilePos]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
      integral_gaussTail_scale a ha]
  have hneg : ∫ t in Ioi (0 : ℝ), profileNeg a b t =
      (2 * b / (a + b)) * (b / Real.sqrt (2 * Real.pi)) := by
    simp only [profileNeg]
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
      integral_gaussTail_scale b hb]
  rw [hpos, hneg, secondOrderCoeff, ← two_div_sqrt_two_pi]
  field_simp [hab, hs.ne']
  ring

/-- The same mean when `b = 0 < a`: the negative half of `F_{a,0}` vanishes. -/
theorem profile_mean_zero (a : ℝ) (ha : 0 < a) :
    ∫ t in Ioi (0 : ℝ), profileHalf a t = secondOrderCoeff a 0 := by
  have hs : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  simp only [profileHalf, secondOrderCoeff, sub_zero]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_div,
    integral_gaussTail_scale a ha, ← two_div_sqrt_two_pi]
  field_simp [hs.ne']

/-- Last line of the proof of Theorem 1. An additive gap of at most `c⋆` does not
change a `√n` coefficient. This does not identify the envelope mean with
`profile_mean`: that step is `Gₙ(x√n) → F`, which is not proved here. -/
theorem second_order_transfer {h c : ℝ} {L H : ℕ → ℝ}
    (hlo : ∀ n, L n ≤ H n) (hhi : ∀ n, H n ≤ L n + shannonOverhead)
    (hlim : Tendsto (fun n : ℕ => (L n - (n : ℝ) * h) / Real.sqrt (n : ℝ)) atTop (nhds c)) :
    Tendsto (fun n : ℕ => (H n - (n : ℝ) * h) / Real.sqrt (n : ℝ)) atTop (nhds c) := by
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    refine ⟨Nat.ceil (max b 0), fun n hn => ?_⟩
    have h1 : b ≤ max b 0 := le_max_left _ _
    have h2 : max b 0 ≤ (Nat.ceil (max b 0) : ℝ) := Nat.le_ceil _
    have h3 : (Nat.ceil (max b 0) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hnat
  have hupper : Tendsto (fun n : ℕ => shannonOverhead / Real.sqrt (n : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hsqrt
  have hpiece : Tendsto (fun n : ℕ => (H n - L n) / Real.sqrt (n : ℝ)) atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
      (Eventually.of_forall fun n => div_nonneg (sub_nonneg.mpr (hlo n)) (Real.sqrt_nonneg _))
      (Eventually.of_forall fun n => ?_)
    have hgap : H n - L n ≤ shannonOverhead := by linarith [hhi n]
    exact div_le_div_of_nonneg_right hgap (Real.sqrt_nonneg _)
  have hsum := hlim.add hpiece
  simp only [add_zero] at hsum
  refine Tendsto.congr ?_ hsum
  intro n
  by_cases hn : Real.sqrt (n : ℝ) = 0
  · simp [hn]
  · field_simp [hn]
    ring

end CausalSpectrum

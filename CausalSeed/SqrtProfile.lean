/-
The explicit diffusion profile `F_{a,b}` of the square-root asymptotic.
`F z = (2b/(a+b)) Φ(z/b)` for `z ≤ 0`, `1 - (2a/(a+b)) Φ(-z/a)` for `z > 0`,
with `Φ(-y) = gaussTail y / √(2π)`.
Proved: continuity at the junction, `F' = (2/(a+b)) φ(z/s)`,
`F'' = -(2z/((a+b)s²)) φ(z/s)` everywhere (including `z = 0`), `F ∈ C²`,
the PDE `u_t = min_j σ_j²/2 u_xx` for `u(t,x) = F(x/√t)`, and the mean.
-/
import CausalSeed.SecondOrder
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum.Sqrt

/-! ### The Gaussian tail -/

theorem gaussTail_zero : gaussTail 0 = Real.sqrt (2 * Real.pi) / 2 := by
  have h := integral_gaussian_Ioi (1 / 2)
  have he : (fun x : ℝ => Real.exp (-(1 / 2) * x ^ 2)) = gaussRaw := by
    funext x; simp only [gaussRaw]; congr 1; ring
  rw [he] at h
  unfold gaussTail
  rw [h]
  congr 2
  field_simp

theorem hasDerivAt_gaussTail (t : ℝ) : HasDerivAt gaussTail (-gaussRaw t) t := by
  have hp : HasDerivAt (fun A => ∫ x in (0:ℝ)..A, gaussRaw x) (gaussRaw t) t :=
    (intervalIntegral.integral_hasStrictDerivAt_right
      (continuous_gaussRaw.intervalIntegrable _ _)
      (continuous_gaussRaw.stronglyMeasurableAtFilter _ _)
      continuous_gaussRaw.continuousAt).hasDerivAt
  have hf : gaussTail = fun A => gaussTail 0 - ∫ x in (0:ℝ)..A, gaussRaw x := by
    funext A; exact gaussTail_eq_sub A
  rw [hf]
  exact (hasDerivAt_const t _).sub hp |>.congr_deriv (by ring)

theorem gaussRaw_neg (x : ℝ) : gaussRaw (-x) = gaussRaw x := by simp [gaussRaw]

theorem hasDerivAt_gaussRaw (x : ℝ) : HasDerivAt gaussRaw (-x * gaussRaw x) x := by
  have h := (hasDerivAt_neg_gaussRaw x).neg
  convert h using 1
  · funext y; simp
  · ring

/-! ### Piecewise differentiation at the junction `0` -/

theorem piecewise_hasDerivAt {FL FR DL DR : ℝ → ℝ}
    (hL : ∀ z, HasDerivAt FL (DL z) z) (hR : ∀ z, HasDerivAt FR (DR z) z)
    (h0 : FL 0 = FR 0) (hd0 : DL 0 = DR 0) (z : ℝ) :
    HasDerivAt (fun z => if z ≤ 0 then FL z else FR z) (if z ≤ 0 then DL z else DR z) z := by
  rcases lt_trichotomy z 0 with hz | rfl | hz
  · rw [if_pos hz.le]
    apply (hL z).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hz] with y hy
    rw [if_pos hy.le]
  · rw [if_pos le_rfl]
    have h1 : HasDerivWithinAt (fun z => if z ≤ 0 then FL z else FR z) (DL 0) (Iic 0) 0 :=
      (hL 0).hasDerivWithinAt.congr (fun y hy => if_pos hy) (if_pos le_rfl)
    have h2 : HasDerivWithinAt (fun z => if z ≤ 0 then FL z else FR z) (DL 0) (Ici 0) 0 := by
      rw [hd0]
      refine (hR 0).hasDerivWithinAt.congr (fun y hy => ?_) (by rw [if_pos le_rfl, h0])
      rcases eq_or_lt_of_le (mem_Ici.mp hy) with h | h
      · subst h; rw [if_pos le_rfl, h0]
      · rw [if_neg (not_le.mpr h)]
    have := h1.union h2
    rw [Iic_union_Ici] at this
    exact this.hasDerivAt univ_mem
  · rw [if_neg (not_le.mpr hz)]
    apply (hR z).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hz] with y hy
    rw [if_neg (not_le.mpr hy)]

/-! ### The profile -/

variable (a b : ℝ)

/-- Standard normal density `φ`. -/
def phi (y : ℝ) : ℝ := gaussRaw y / Real.sqrt (2 * Real.pi)

def FL (z : ℝ) : ℝ := 2 * b / (a + b) * (gaussTail (-z / b) / Real.sqrt (2 * Real.pi))
def FR (z : ℝ) : ℝ := 1 - 2 * a / (a + b) * (gaussTail (z / a) / Real.sqrt (2 * Real.pi))

/-- The profile `F_{a,b}`. -/
def prof (z : ℝ) : ℝ := if z ≤ 0 then FL a b z else FR a b z

def dL (z : ℝ) : ℝ := 2 / (a + b) * phi (z / b)
def dR (z : ℝ) : ℝ := 2 / (a + b) * phi (z / a)
/-- `F'`. -/
def prof' (z : ℝ) : ℝ := if z ≤ 0 then dL a b z else dR a b z

def ddL (z : ℝ) : ℝ := -(2 * z / ((a + b) * b ^ 2)) * phi (z / b)
def ddR (z : ℝ) : ℝ := -(2 * z / ((a + b) * a ^ 2)) * phi (z / a)
/-- `F''`. -/
def prof'' (z : ℝ) : ℝ := if z ≤ 0 then ddL a b z else ddR a b z

variable {a b}

theorem sqrt2pi_pos : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)

theorem FL_zero_eq_FR_zero (ha : 0 < a) (hb : 0 < b) : FL a b 0 = FR a b 0 := by
  have hs := sqrt2pi_pos
  simp only [FL, FR, neg_zero, zero_div, gaussTail_zero]
  field_simp
  ring

theorem prof_zero (ha : 0 < a) (hb : 0 < b) : prof a b 0 = b / (a + b) := by
  have hs := sqrt2pi_pos
  simp only [prof, le_refl, if_true, FL, neg_zero, zero_div, gaussTail_zero]
  field_simp

theorem hasDerivAt_FL (hb : 0 < b) (z : ℝ) : HasDerivAt (FL a b) (dL a b z) z := by
  have h1 : HasDerivAt (fun z => -z / b) (-1 / b) z := by
    simpa using ((hasDerivAt_id z).neg.div_const b)
  have h2 := (hasDerivAt_gaussTail (-z / b)).comp z h1
  have h3 := (h2.div_const (Real.sqrt (2 * Real.pi))).const_mul (2 * b / (a + b))
  have e : dL a b z = 2 * b / (a + b) * (-gaussRaw (-z / b) * (-1 / b) / Real.sqrt (2 * Real.pi)) := by
    unfold dL phi
    rw [show -z / b = -(z / b) by ring, gaussRaw_neg]
    field_simp
  rw [e]; exact h3

theorem hasDerivAt_FR (ha : 0 < a) (z : ℝ) : HasDerivAt (FR a b) (dR a b z) z := by
  have h1 : HasDerivAt (fun z => z / a) (1 / a) z := by
    simpa using ((hasDerivAt_id z).div_const a)
  have h2 := (hasDerivAt_gaussTail (z / a)).comp z h1
  have h3 := ((h2.div_const (Real.sqrt (2 * Real.pi))).const_mul (2 * a / (a + b))).const_sub 1
  have e : dR a b z = -(2 * a / (a + b) * (-gaussRaw (z / a) * (1 / a) / Real.sqrt (2 * Real.pi))) := by
    unfold dR phi
    field_simp
  rw [e]; exact h3

theorem hasDerivAt_dL (hb : 0 < b) (z : ℝ) : HasDerivAt (dL a b) (ddL a b z) z := by
  have h1 : HasDerivAt (fun z => z / b) (1 / b) z := by
    simpa using ((hasDerivAt_id z).div_const b)
  have h2 := (hasDerivAt_gaussRaw (z / b)).comp z h1
  have h3 := (h2.div_const (Real.sqrt (2 * Real.pi))).const_mul (2 / (a + b))
  have e : ddL a b z = 2 / (a + b) * (-(z / b) * gaussRaw (z / b) * (1 / b) / Real.sqrt (2 * Real.pi)) := by
    unfold ddL phi
    field_simp
  rw [e]; exact h3

theorem hasDerivAt_dR (ha : 0 < a) (z : ℝ) : HasDerivAt (dR a b) (ddR a b z) z := by
  have h1 : HasDerivAt (fun z => z / a) (1 / a) z := by
    simpa using ((hasDerivAt_id z).div_const a)
  have h2 := (hasDerivAt_gaussRaw (z / a)).comp z h1
  have h3 := (h2.div_const (Real.sqrt (2 * Real.pi))).const_mul (2 / (a + b))
  have e : ddR a b z = 2 / (a + b) * (-(z / a) * gaussRaw (z / a) * (1 / a) / Real.sqrt (2 * Real.pi)) := by
    unfold ddR phi
    field_simp
  rw [e]; exact h3

theorem hasDerivAt_prof (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    HasDerivAt (prof a b) (prof' a b z) z :=
  piecewise_hasDerivAt (hasDerivAt_FL hb) (hasDerivAt_FR ha) (FL_zero_eq_FR_zero ha hb)
    (by simp [dL, dR]) z

theorem hasDerivAt_prof' (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    HasDerivAt (prof' a b) (prof'' a b z) z :=
  piecewise_hasDerivAt (hasDerivAt_dL hb) (hasDerivAt_dR ha) (by simp [dL, dR])
    (by simp [ddL, ddR]) z

theorem continuous_phi : Continuous phi := continuous_gaussRaw.div_const _

theorem continuous_prof'' (ha : 0 < a) (hb : 0 < b) : Continuous (prof'' a b) := by
  unfold prof''
  apply Continuous.if_le
  · unfold ddL; exact (continuous_const.mul continuous_id |>.div_const _).neg.mul
      (continuous_phi.comp (continuous_id.div_const _))
  · unfold ddR; exact (continuous_const.mul continuous_id |>.div_const _).neg.mul
      (continuous_phi.comp (continuous_id.div_const _))
  · exact continuous_id
  · exact continuous_const
  · intro x hx; simp [ddL, ddR, hx]

/-- `F ∈ C²(ℝ)`. -/
theorem prof_contDiff (ha : 0 < a) (hb : 0 < b) : ContDiff ℝ 2 (prof a b) := by
  have hd : deriv (prof a b) = prof' a b := funext fun z => (hasDerivAt_prof ha hb z).deriv
  have hdd : deriv (prof' a b) = prof'' a b := funext fun z => (hasDerivAt_prof' ha hb z).deriv
  rw [show (2 : WithTop ℕ∞) = 1 + 1 from rfl, contDiff_succ_iff_deriv]
  refine ⟨fun z => (hasDerivAt_prof ha hb z).differentiableAt, by simp, ?_⟩
  rw [hd, contDiff_one_iff_deriv, hdd]
  exact ⟨fun z => (hasDerivAt_prof' ha hb z).differentiableAt, continuous_prof'' ha hb⟩

theorem prof''_zero : prof'' a b 0 = 0 := by simp [prof'', ddL]

/-! ### The PDE -/

theorem prof''_eq (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    prof'' a b z = -(z / (if z ≤ 0 then b else a) ^ 2) * prof' a b z := by
  unfold prof'' prof' ddL ddR dL dR
  split_ifs <;> field_simp

theorem prof''_nonneg_of_nonpos (ha : 0 < a) (hb : 0 < b) {z : ℝ} (hz : z ≤ 0) :
    0 ≤ prof'' a b z := by
  simp only [prof'', if_pos hz, ddL]
  have : 0 ≤ phi (z / b) := div_nonneg (Real.exp_nonneg _) sqrt2pi_pos.le
  have h2 : 2 * z / ((a + b) * b ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  nlinarith

theorem prof''_nonpos_of_pos (ha : 0 < a) (hb : 0 < b) {z : ℝ} (hz : 0 < z) :
    prof'' a b z ≤ 0 := by
  simp only [prof'', if_neg (not_le.mpr hz), ddR]
  have : 0 ≤ phi (z / a) := div_nonneg (Real.exp_nonneg _) sqrt2pi_pos.le
  have h2 : 0 ≤ 2 * z / ((a + b) * a ^ 2) := by positivity
  nlinarith

/-- Space derivative of `u(t,x) = F(x/√t)`. -/
theorem hasDerivAt_u_x (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x => prof a b (x / Real.sqrt t))
      (prof' a b (x / Real.sqrt t) / Real.sqrt t) x := by
  have h := (hasDerivAt_prof ha hb (x / Real.sqrt t)).comp x
    ((hasDerivAt_id x).div_const (Real.sqrt t))
  exact h.congr_deriv (by simp [div_eq_mul_inv])

theorem hasDerivAt_u_xx (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun x => prof' a b (x / Real.sqrt t) / Real.sqrt t)
      (prof'' a b (x / Real.sqrt t) / t) x := by
  have hs : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht).ne'
  have h := ((hasDerivAt_prof' ha hb (x / Real.sqrt t)).comp x
    ((hasDerivAt_id x).div_const (Real.sqrt t))).div_const (Real.sqrt t)
  refine h.congr_deriv ?_
  rw [mul_one_div, div_div, Real.mul_self_sqrt ht.le]

theorem hasDerivAt_u_t (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun t => prof a b (x / Real.sqrt t))
      (-(x / Real.sqrt t) * prof' a b (x / Real.sqrt t) / (2 * t)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 := (hasDerivAt_const t x).div (Real.hasDerivAt_sqrt ht.ne') hs.ne'
  have h := (hasDerivAt_prof ha hb (x / Real.sqrt t)).comp t h1
  refine h.congr_deriv ?_
  have ht' : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  rw [Real.sq_sqrt ht.le]
  field_simp
  ring_nf

/-- The PDE `u_t = min_j σ_j²/2 u_xx`, for any finite family of scales with
least element `b` and largest element `a`. -/
theorem pde (ha : 0 < a) (hb : 0 < b) (S : Finset ℝ) (hbS : b ∈ S) (haS : a ∈ S)
    (hS : ∀ σ ∈ S, b ≤ σ ∧ σ ≤ a) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    -(x / Real.sqrt t) * prof' a b (x / Real.sqrt t) / (2 * t) =
      S.inf' ⟨b, hbS⟩ (fun σ => σ ^ 2 / 2 * (prof'' a b (x / Real.sqrt t) / t)) := by
  set z := x / Real.sqrt t
  have hpe := prof''_eq ha hb z
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ prof'' a b z / t := div_nonneg (prof''_nonneg_of_nonpos ha hb hz) ht.le
    apply le_antisymm
    · apply Finset.le_inf'; intro σ hσ
      have hbs := (hS σ hσ).1
      have : b ^ 2 ≤ σ ^ 2 := pow_le_pow_left₀ hb.le hbs 2
      have e : -z * prof' a b z / (2 * t) = b ^ 2 / 2 * (prof'' a b z / t) := by
        rw [hpe, if_pos hz]; field_simp
      rw [e]; nlinarith
    · refine (Finset.inf'_le _ hbS).trans (le_of_eq ?_)
      rw [hpe, if_pos hz]; field_simp
  · have hzp : 0 < z := lt_of_not_ge hz
    have hn : prof'' a b z / t ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (prof''_nonpos_of_pos ha hb hzp) ht.le
    apply le_antisymm
    · apply Finset.le_inf'; intro σ hσ
      have h1 := (hS σ hσ)
      have : σ ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ (hb.le.trans h1.1) h1.2 2
      have e : -z * prof' a b z / (2 * t) = a ^ 2 / 2 * (prof'' a b z / t) := by
        rw [hpe, if_neg hz]; field_simp
      rw [e]; nlinarith
    · refine (Finset.inf'_le _ haS).trans (le_of_eq ?_)
      rw [hpe, if_neg hz]; field_simp

/-! ### The mean -/

theorem one_sub_prof (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    1 - prof a b t = profilePos a b t := by
  simp [prof, not_le.mpr ht, FR, profilePos]

theorem prof_neg (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) :
    prof a b (-t) = profileNeg a b t := by
  simp [prof, show -t ≤ 0 by linarith, FL, profileNeg]

/-- The mean of `F_{a,b}` is `√(2/π)(a-b)`. -/
theorem prof_mean (ha : 0 < a) (hb : 0 < b) :
    (∫ t in Ioi (0:ℝ), (1 - prof a b t)) - (∫ t in Ioi (0:ℝ), prof a b (-t)) =
      secondOrderCoeff a b := by
  rw [← profile_mean a b ha hb]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi fun t ht => one_sub_prof ha hb ht
  · exact setIntegral_congr_fun measurableSet_Ioi fun t ht => prof_neg ha hb ht

#print axioms prof_contDiff
#print axioms pde
#print axioms prof_mean

end CausalSpectrum.Sqrt

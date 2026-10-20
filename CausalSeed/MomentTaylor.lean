/-
Taylor factorisation bound for differences of averages.

For a chain `f 0, f 1, …, f m` with `f i' = f (i+1)` and `f m` continuous, the Taylor
remainder `rem f m x y = f 0 (x - y) - Σ_{i<m} (-y)^i/i! f i x` satisfies
`∫ |rem f m x y| dx ≤ |y|^m ∫ |f m|`. Consequently, if two actions have the same moments
of orders `< m`, then `∫ |E_j f - E_k f| ≤ (E|X_j|^m + E|X_k|^m) ∫ |f m|`; this is the
estimate `‖D * f‖₁ ≤ ‖Γ_m‖ ‖f^{(m)}‖₁` with a cruder constant.
-/
import CausalSeed.MomentLower

noncomputable section
open Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum.Sqrt.Taylor

/-- The Taylor remainder of order `m`. -/
def rem (f : ℕ → ℝ → ℝ) (m : ℕ) (x y : ℝ) : ℝ :=
  f 0 (x - y) - ∑ i ∈ Finset.range m, (-y) ^ i / (i.factorial : ℝ) * f i x

theorem rem_at_zero (f : ℕ → ℝ → ℝ) (m : ℕ) (x : ℝ) : rem f (m + 1) x 0 = 0 := by
  simp only [rem, Finset.sum_range_succ', neg_zero, sub_zero]
  simp

theorem hasDerivAt_rem (f : ℕ → ℝ → ℝ) (m : ℕ)
    (hd : ∀ i < m + 1, ∀ x, HasDerivAt (f i) (f (i + 1) x) x) (x y : ℝ) :
    HasDerivAt (fun y => rem f (m + 1) x y) (-rem (fun i => f (i + 1)) m x y) y := by
  have h0 : HasDerivAt (fun y => f 0 (x - y)) (-f 1 (x - y)) y := by
    have := (hd 0 (by omega) (x - y)).comp y ((hasDerivAt_id y).const_sub x)
    simpa [Function.comp_def] using this
  have hs : HasDerivAt (fun y => ∑ i ∈ Finset.range m, (-y) ^ (i + 1) /
      ((i + 1).factorial : ℝ) * f (i + 1) x)
      (∑ i ∈ Finset.range m, -((-y) ^ i / (i.factorial : ℝ) * f (i + 1) x)) y := by
    refine HasDerivAt.fun_sum fun i _ => ?_
    have hp : HasDerivAt (fun y : ℝ => (-y) ^ (i + 1)) (((i + 1 : ℕ) : ℝ) * (-y) ^ i * (-1)) y := by
      simpa [Function.comp_def] using ((hasDerivAt_pow (i + 1) (-y)).comp y (hasDerivAt_neg y))
    have := (hp.div_const ((i + 1).factorial : ℝ)).mul_const (f (i + 1) x)
    convert this using 1
    rw [Nat.factorial_succ]; push_cast
    have : (i.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have e : (fun y => rem f (m + 1) x y) = fun y => f 0 (x - y) - (f 0 x +
      ∑ i ∈ Finset.range m, (-y) ^ (i + 1) / ((i + 1).factorial : ℝ) * f (i + 1) x) := by
    funext y; simp only [rem, Finset.sum_range_succ']; simp; ring
  rw [e]
  convert h0.sub ((hasDerivAt_const y (f 0 x)).add hs) using 1
  simp only [rem, Finset.sum_neg_distrib, zero_add]
  ring

theorem continuous_rem (f : ℕ → ℝ → ℝ) (m : ℕ) (hc : ∀ i ≤ m, Continuous (f i)) :
    Continuous (Function.uncurry (rem f m)) := by
  unfold rem
  refine ((hc 0 (by omega)).comp (continuous_fst.sub continuous_snd)).sub ?_
  refine continuous_finsetSum _ fun i hi => ?_
  have := hc i (Finset.mem_range.1 hi).le
  exact ((continuous_snd.neg.pow i).div_const _).mul (this.comp continuous_fst)

/-- **`∫ |rem f m x y| dx ≤ |y|^m ∫ |f m|`.** -/
theorem lintegral_rem_le : ∀ (m : ℕ) (f : ℕ → ℝ → ℝ),
    (∀ i < m, ∀ x, HasDerivAt (f i) (f (i + 1) x) x) → Continuous (f m) → ∀ y : ℝ,
    ∫⁻ x, ‖rem f m x y‖ₑ ≤ ENNReal.ofReal (|y| ^ m) * ∫⁻ x, ‖f m x‖ₑ
  | 0, f, _, _, y => by
    simp only [rem, Finset.range_zero, Finset.sum_empty, sub_zero, pow_zero,
      ENNReal.ofReal_one, one_mul]
    exact (lintegral_sub_right_eq_self (fun x => ‖f 0 x‖ₑ) y).le
  | m + 1, f, hd, hc, y => by
    set g : ℕ → ℝ → ℝ := fun i => f (i + 1)
    have hdg : ∀ i < m, ∀ x, HasDerivAt (g i) (g (i + 1) x) x := fun i hi x => hd (i + 1) (by omega) x
    have ih := lintegral_rem_le m g hdg hc
    have hcont : ∀ i ≤ m, Continuous (g i) := fun i hi => by
      rcases hi.lt_or_eq with h | h
      · exact continuous_iff_continuousAt.2 fun x => (hd (i + 1) (by omega) x).continuousAt
      · subst h; exact hc
    have hrc := continuous_rem g m hcont
    -- FTC in the second variable
    have hftc : ∀ x, rem f (m + 1) x y = -∫ s in (0:ℝ)..y, rem g m x s := fun x => by
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := 0) (b := y)
        (fun s _ => hasDerivAt_rem f m hd x s)
        ((hrc.comp (continuous_const.prodMk continuous_id)).neg.intervalIntegrable _ _)
      rw [intervalIntegral.integral_neg, rem_at_zero, sub_zero] at this
      linarith
    have hpt : ∀ x, ‖rem f (m + 1) x y‖ₑ ≤ ∫⁻ s in uIoc 0 y, ‖rem g m x s‖ₑ := fun x => by
      rw [hftc x, enorm_neg]
      have h1 := intervalIntegral.norm_integral_le_integral_norm_uIoc
        (f := fun s => rem g m x s) (a := 0) (b := y) (μ := volume)
      have hi : IntegrableOn (fun s => rem g m x s) (uIoc 0 y) :=
        ((hrc.comp (continuous_const.prodMk continuous_id)).integrableOn_Icc
          (a := min 0 y) (b := max 0 y)).mono_set uIoc_subset_uIcc
      rw [← ofReal_integral_norm_eq_lintegral_enorm hi, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal h1
    calc ∫⁻ x, ‖rem f (m + 1) x y‖ₑ ≤ ∫⁻ x, ∫⁻ s in uIoc 0 y, ‖rem g m x s‖ₑ := lintegral_mono hpt
      _ = ∫⁻ s in uIoc 0 y, ∫⁻ x, ‖rem g m x s‖ₑ := by
          refine lintegral_lintegral_swap ?_
          exact (hrc.enorm.measurable.aemeasurable)
      _ ≤ ∫⁻ s in uIoc 0 y, ENNReal.ofReal (|y| ^ m) * ∫⁻ x, ‖g m x‖ₑ := by
          refine setLIntegral_mono' measurableSet_uIoc fun s hs => (ih s).trans ?_
          refine mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal ?_) (zero_le')
          have : |s| ≤ |y| := by
            rcases mem_uIoc.1 hs with h | h
            · rw [abs_of_pos h.1, abs_of_pos (h.1.trans_le h.2)]; exact h.2
            · rw [abs_of_nonpos h.2, abs_of_neg (h.1.trans_le h.2)]; linarith [h.1]
          exact pow_le_pow_left₀ (abs_nonneg _) this m
      _ = ENNReal.ofReal (|y| ^ (m + 1)) * ∫⁻ x, ‖f (m + 1) x‖ₑ := by
          rw [setLIntegral_const, Real.volume_uIoc, sub_zero, pow_succ,
            ENNReal.ofReal_mul (by positivity)]
          simp only [g]; ring

end CausalSpectrum.Sqrt.Taylor

namespace CausalSpectrum.Sqrt.IncFamily
open Taylor
variable (F : IncFamily)

/-- Moments `Σ_y P_j(y) X_j(y)^i`. -/
def mom (j : Fin F.nA) (i : ℕ) : ℝ := ∑ y, F.P j y * F.X j y ^ i

/-- Absolute moments `Σ_y P_j(y) |X_j(y)|^m`. -/
def amom (j : Fin F.nA) (m : ℕ) : ℝ := ∑ y, F.P j y * |F.X j y| ^ m

theorem amom_nonneg (j) (m : ℕ) : 0 ≤ F.amom j m :=
  Finset.sum_nonneg fun y _ => mul_nonneg (F.Ppos j y).le (by positivity)

theorem expect_taylor (j) (f : ℕ → ℝ → ℝ) (m : ℕ) (x : ℝ) :
    F.expect j (f 0) x = ∑ y, F.P j y * rem f m x (F.X j y) +
      ∑ i ∈ Finset.range m, (-1) ^ i * F.mom j i / (i.factorial : ℝ) * f i x := by
  simp only [expect, rem, mom, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ) (t := Finset.range m)]
  have : ∀ i ∈ Finset.range m, ∀ y ∈ (Finset.univ : Finset (Fin (F.nY j))),
      F.P j y * ((-F.X j y) ^ i / (i.factorial : ℝ) * f i x) =
        (-1) ^ i * (F.P j y * F.X j y ^ i) / (i.factorial : ℝ) * f i x := fun i _ y _ => by
    rw [neg_pow]; ring
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl (this i hi)]
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
  ring

/-- **Taylor factorisation bound.** If actions `j, k` have equal moments of orders `< m`, then
`∫ |E_j f - E_k f| ≤ (E|X_j|^m + E|X_k|^m) ∫ |f^{(m)}|` for a `C^m` chain `f`. -/
theorem lintegral_expect_sub_le {j k} (m : ℕ) (hmom : ∀ i < m, F.mom j i = F.mom k i)
    (f : ℕ → ℝ → ℝ) (hd : ∀ i < m, ∀ x, HasDerivAt (f i) (f (i + 1) x) x)
    (hc : Continuous (f m)) :
    ∫⁻ x, ‖F.expect j (f 0) x - F.expect k (f 0) x‖ₑ ≤
      ENNReal.ofReal (F.amom j m + F.amom k m) * ∫⁻ x, ‖f m x‖ₑ := by
  have hcont : ∀ i ≤ m, Continuous (f i) := fun i hi => by
    rcases hi.lt_or_eq with h | h
    · exact continuous_iff_continuousAt.2 fun x => (hd i h x).continuousAt
    · subst h; exact hc
  have hrc := continuous_rem f m hcont
  have hmeas : ∀ z : ℝ, Measurable fun x => rem f m x z := fun z =>
    (hrc.comp (continuous_id.prodMk continuous_const)).measurable
  have hdiff : ∀ x, F.expect j (f 0) x - F.expect k (f 0) x =
      ∑ y, F.P j y * rem f m x (F.X j y) - ∑ y, F.P k y * rem f m x (F.X k y) := fun x => by
    rw [F.expect_taylor j f m x, F.expect_taylor k f m x]
    have : ∑ i ∈ Finset.range m, (-1) ^ i * F.mom j i / (i.factorial : ℝ) * f i x =
        ∑ i ∈ Finset.range m, (-1) ^ i * F.mom k i / (i.factorial : ℝ) * f i x :=
      Finset.sum_congr rfl fun i hi => by rw [hmom i (Finset.mem_range.1 hi)]
    rw [this]; ring
  have hbound : ∀ (i : Fin F.nA), ∫⁻ x, ‖∑ y, F.P i y * rem f m x (F.X i y)‖ₑ ≤
      ENNReal.ofReal (F.amom i m) * ∫⁻ x, ‖f m x‖ₑ := fun i => by
    calc ∫⁻ x, ‖∑ y, F.P i y * rem f m x (F.X i y)‖ₑ
        ≤ ∫⁻ x, ∑ y, ENNReal.ofReal (F.P i y) * ‖rem f m x (F.X i y)‖ₑ := by
          refine lintegral_mono fun x => (enorm_sum_le _ _).trans (le_of_eq ?_)
          refine Finset.sum_congr rfl fun y _ => ?_
          rw [enorm_mul, Real.enorm_of_nonneg (F.Ppos i y).le]
      _ = ∑ y, ENNReal.ofReal (F.P i y) * ∫⁻ x, ‖rem f m x (F.X i y)‖ₑ := by
          rw [lintegral_finset_sum _ fun y _ => ((hmeas _).enorm.const_mul _)]
          exact Finset.sum_congr rfl fun y _ => lintegral_const_mul _ (hmeas _).enorm
      _ ≤ ∑ y, ENNReal.ofReal (F.P i y) * (ENNReal.ofReal (|F.X i y| ^ m) * ∫⁻ x, ‖f m x‖ₑ) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left
            (lintegral_rem_le m f hd hc _) (zero_le')
      _ = ENNReal.ofReal (F.amom i m) * ∫⁻ x, ‖f m x‖ₑ := by
          simp only [← mul_assoc, ← Finset.sum_mul]
          congr 1
          rw [amom, ENNReal.ofReal_sum_of_nonneg fun y _ =>
            mul_nonneg (F.Ppos i y).le (by positivity)]
          exact Finset.sum_congr rfl fun y _ => (ENNReal.ofReal_mul (F.Ppos i y).le).symm
  calc ∫⁻ x, ‖F.expect j (f 0) x - F.expect k (f 0) x‖ₑ
      ≤ ∫⁻ x, (‖∑ y, F.P j y * rem f m x (F.X j y)‖ₑ +
          ‖∑ y, F.P k y * rem f m x (F.X k y)‖ₑ) := by
        refine lintegral_mono fun x => ?_
        rw [hdiff]; exact enorm_sub_le
    _ ≤ _ := by
        rw [lintegral_add_left' (by
          refine (Measurable.enorm ?_).aemeasurable
          exact Finset.measurable_sum _ fun y _ => (hmeas _).const_mul _)]
        refine (add_le_add (hbound j) (hbound k)).trans (le_of_eq ?_)
        rw [ENNReal.ofReal_add (F.amom_nonneg j m) (F.amom_nonneg k m), add_mul]

end CausalSpectrum.Sqrt.IncFamily

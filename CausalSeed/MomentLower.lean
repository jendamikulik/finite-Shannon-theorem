/-
The `Ω(log n)` lower bound of the moment classification.

`e(G) = ∫ (G_0 - G)` is the mean of the law with CDF `G`. Each Bellman step raises it by
at least `½ ∫ |E_j G_n - E_k G_n|`; with the Fourier lower bound of `MomentFourier` this gives
`e(G_n) ≥ c log n` whenever two actions have equal variances but different third moments.
Since `L_n - n h = e(G_n)`, the same holds for `L_n - n h` and for `C_n - n h`.
-/
import CausalSeed.MomentFourier
import CausalSeed.SqrtMain
import CausalSeed.ZeroCost

noncomputable section
open Classical MeasureTheory Set Filter Topology

namespace CausalSpectrum.Sqrt
namespace IncFamily
variable (F : IncFamily)

/-- `e(f) = ∫ (G_0 - f)`: the mean of the law with CDF `f`. -/
def eG (f : ℝ → ℝ) : ℝ := ∫ x, (F.G 0 x - f x)

theorem G0_eq (x : ℝ) : F.G 0 x = (Ici 0).indicator 1 x := by
  simp [G, indicator]

theorem G0_sub_shift (c x : ℝ) : F.G 0 x - F.G 0 (x - c) = -step c x := by
  simp only [G0_eq, step, indicator, mem_Ici, Pi.one_apply, sub_nonneg]
  ring

theorem measurable_G (n : ℕ) : Measurable (F.G n) := (F.G_cdf n).1.measurable

theorem integrable_G0_sub_G (n : ℕ) : Integrable fun x => F.G 0 x - F.G n x := by
  refine Integrable.mono' (g := (Icc (-(n * F.M)) (n * F.M)).indicator fun _ => (1:ℝ))
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp)))
    ((F.measurable_G 0).sub (F.measurable_G n)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hnM : 0 ≤ (n : ℝ) * F.M := mul_nonneg (Nat.cast_nonneg n) F.M_nonneg
  have b0 := (F.G_cdf 0).2.2.1 x
  have bn := (F.G_cdf n).2.2.1 x
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-(n * F.M)) (n * F.M)
  · rw [indicator_of_mem hx]; rw [abs_le]; constructor <;> linarith [b0.1, b0.2, bn.1, bn.2]
  · rw [indicator_of_notMem hx]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [(F.G_cdf n).2.2.2.1 x hx, G0_eq, indicator_of_notMem (by simp; linarith)]; simp
    · rw [(F.G_cdf n).2.2.2.2 x hx.le, G0_eq, indicator_of_mem (by simp; linarith)]; simp

theorem G0_sub_expect (n : ℕ) (j) (x : ℝ) :
    F.G 0 x - F.expect j (F.G n) x =
      ∑ y, F.P j y * (-step (F.X j y) x + (F.G 0 (x - F.X j y) - F.G n (x - F.X j y))) := by
  have : F.G 0 x = ∑ y, F.P j y * F.G 0 x := by rw [← Finset.sum_mul, F.Psum j, one_mul]
  rw [expect, this, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← F.G0_sub_shift (F.X j y) x]; ring

theorem integrable_G0_sub_expect (n : ℕ) (j) : Integrable fun x => F.G 0 x - F.expect j (F.G n) x := by
  simp_rw [F.G0_sub_expect n j]
  refine integrable_finsetSum _ fun y _ => Integrable.const_mul ?_ _
  exact (integrable_step _).neg.add ((F.integrable_G0_sub_G n).comp_sub_right _)

theorem eG_expect (hc : F.Centered) (n : ℕ) (j) :
    F.eG (F.expect j (F.G n)) = F.eG (F.G n) := by
  simp only [eG]
  simp_rw [F.G0_sub_expect n j]
  rw [integral_finsetSum _ fun y _ => (show Integrable (fun x => F.P j y * (-step (F.X j y) x +
    (F.G 0 (x - F.X j y) - F.G n (x - F.X j y)))) from Integrable.const_mul
    ((integrable_step _).neg.add ((F.integrable_G0_sub_G n).comp_sub_right _)) _)]
  simp only [integral_const_mul]
  have : ∀ y, ∫ x, (-step (F.X j y) x + (F.G 0 (x - F.X j y) - F.G n (x - F.X j y))) =
      F.X j y + ∫ x, (F.G 0 x - F.G n x) := fun y => by
    have i1 : Integrable (fun x => -step (F.X j y) x) := (integrable_step _).neg
    have i2 : Integrable (fun x => F.G 0 (x - F.X j y) - F.G n (x - F.X j y)) :=
      (F.integrable_G0_sub_G n).comp_sub_right _
    rw [integral_add i1 i2, integral_neg, integral_step, neg_neg,
      integral_sub_right_eq_self (fun x => F.G 0 x - F.G n x)]
  simp only [this, mul_add, Finset.sum_add_distrib, hc j, zero_add]
  rw [← Finset.sum_mul, F.Psum j, one_mul]

theorem integrable_R (n : ℕ) (j k) : Integrable (F.R n j k) := by
  have := (F.integrable_G0_sub_expect n k).sub (F.integrable_G0_sub_expect n j)
  refine this.congr (ae_of_all _ fun x => ?_)
  simp only [Pi.sub_apply, R]; ring

theorem integral_R (hc : F.Centered) (n : ℕ) (j k) : ∫ x, F.R n j k x = 0 := by
  have h := integral_sub (F.integrable_G0_sub_expect n k) (F.integrable_G0_sub_expect n j)
  have e1 := F.eG_expect hc n j
  have e2 := F.eG_expect hc n k
  simp only [eG] at e1 e2
  rw [e1, e2, sub_self] at h
  rw [← h]; congr 1; funext x; simp only [R]; ring

/-- **One Bellman step raises the mean by at least `½ ∫ |E_j G_n - E_k G_n|`.** -/
theorem eG_step (hc : F.Centered) (n : ℕ) (j k) :
    F.eG (F.G n) + (1 / 2) * ∫ x, |F.R n j k x| ≤ F.eG (F.G (n + 1)) := by
  have hj := F.integrable_G0_sub_expect n j
  have hn1 := F.integrable_G0_sub_G (n + 1)
  have hdiff : F.eG (F.G (n + 1)) - F.eG (F.G n) = ∫ x, (F.expect j (F.G n) x - F.G (n + 1) x) := by
    rw [← F.eG_expect hc n j, eG, eG, ← integral_sub hn1 hj]
    congr 1; funext x; ring
  have hRi := F.integrable_R n j k
  have hpt : ∀ x, (F.R n j k x + |F.R n j k x|) / 2 ≤ F.expect j (F.G n) x - F.G (n + 1) x := fun x => by
    have hTk : F.G (n + 1) x ≤ F.expect k (F.G n) x := Finset.inf'_le _ (Finset.mem_univ k)
    have hTj : F.G (n + 1) x ≤ F.expect j (F.G n) x := Finset.inf'_le _ (Finset.mem_univ j)
    simp only [R]
    rcases le_or_gt 0 (F.expect j (F.G n) x - F.expect k (F.G n) x) with h | h
    · rw [abs_of_nonneg h]; linarith
    · rw [abs_of_neg h]; linarith
  have hmono := integral_mono ((hRi.add hRi.abs).div_const 2)
    ((hn1.sub hj).congr (ae_of_all _ fun x => by simp only [Pi.sub_apply]; ring)) hpt
  simp only [Pi.add_apply] at hmono
  rw [integral_div, integral_add hRi hRi.abs, F.integral_R hc] at hmono
  linarith

theorem eG_zero : F.eG (F.G 0) = 0 := by simp [eG]

theorem eG_mono (hc : F.Centered) (n : ℕ) : F.eG (F.G n) ≤ F.eG (F.G (n + 1)) := by
  have := F.eG_step hc n ⟨0, F.hA⟩ ⟨0, F.hA⟩
  have h0 : 0 ≤ ∫ x, |F.R n ⟨0, F.hA⟩ ⟨0, F.hA⟩ x| := integral_nonneg fun _ => abs_nonneg _
  linarith

theorem eG_nonneg (hc : F.Centered) : ∀ n, 0 ≤ F.eG (F.G n)
  | 0 => by rw [eG_zero]
  | n + 1 => (eG_nonneg hc n).trans (F.eG_mono hc n)

theorem log_succ_sub_le {m : ℕ} (hm : 1 ≤ m) : Real.log (m + 1) - Real.log m ≤ 1 / m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← Real.log_div (by positivity) hm0.ne']
  refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
  field_simp; ring

/-- **`e(G_n) ≥ c log n`** when two actions have equal variances but different third moments. -/
theorem eG_log_lower (hc : F.Centered) {j k} (hσ : F.sig2 j = F.sig2 k) (h3 : F.m3 j ≠ F.m3 k) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ F.eG (F.G n) := by
  obtain ⟨c, hc0, N0, hN⟩ := F.integral_abs_R_lower hc hσ h3
  set N := max N0 1
  have hN1 : 1 ≤ N := le_max_right _ _
  -- `e(G_n) ≥ (c/2) (log n - log N)` for `n ≥ N`
  have key : ∀ m : ℕ, c / 2 * (Real.log (N + m) - Real.log N) ≤ F.eG (F.G (N + m)) := by
    intro m
    induction m with
    | zero => simpa using F.eG_nonneg hc N
    | succ m ih =>
      have hs := F.eG_step hc (N + m) j k
      have hb := hN (N + m) (by omega)
      have hl := log_succ_sub_le (m := N + m) (by omega)
      push_cast at hb hl ⊢
      rw [show (N : ℝ) + (m + 1) = (N + m : ℝ) + 1 by ring, show N + (m + 1) = N + m + 1 by ring]
      have h1 := mul_le_mul_of_nonneg_left hl (show 0 ≤ c / 2 by positivity)
      have h2 : c / 2 * (1 / ((N : ℝ) + m)) = 1 / 2 * (c / ((N : ℝ) + m)) := by ring
      linarith
  refine ⟨c / 4, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (N ^ 2)] with n hn
  have hnN : N ≤ n := le_trans (Nat.le_self_pow two_ne_zero N) hn
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hnN
  have := key m
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hlogN : 2 * Real.log N ≤ Real.log ((N + m : ℕ) : ℝ) := by
    rw [show (2:ℝ) * Real.log N = Real.log ((N:ℝ) ^ 2) by rw [Real.log_pow]; norm_num]
    exact Real.log_le_log (by positivity) (by exact_mod_cast hn)
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
  push_cast at this hlogN ⊢
  nlinarith

end IncFamily
end CausalSpectrum.Sqrt

namespace CausalSpectrum.Kernel
variable (κ : Kernel)

/-- `L_n - n h = e(G_n)`. -/
theorem envelope_sub_eq_eG {h : ℝ} (hh : κ.EqualEntropy h) {n : ℕ} (hn : 1 ≤ n) :
    envelopeMean (κ.rounds n) - n * h = (κ.fam h).eG ((κ.fam h).G n) := by
  set F := κ.fam h
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hmi := κ.mean_identity hh hn
  rw [div_eq_iff hs.ne'] at hmi
  rw [hmi]
  simp only [Sqrt.IncFamily.Mn]
  rw [integral_comp_mul_right_Ioi (fun x => 1 - F.G n x) 0 hs,
    integral_comp_mul_right_Ioi (fun x => F.G n (-x)) 0 hs, zero_mul,
    integral_comp_neg_Ioi, neg_zero, smul_eq_mul, smul_eq_mul, ← mul_sub,
    inv_mul_eq_div, div_mul_cancel₀ _ hs.ne']
  -- split `e(G_n)` at `0`
  have hi := F.integrable_G0_sub_G n
  simp only [Sqrt.IncFamily.eG]
  rw [← intervalIntegral.integral_Iic_add_Ioi (hi.integrableOn) (hi.integrableOn)]
  have h1 : ∫ x in Ioi (0:ℝ), (F.G 0 x - F.G n x) = ∫ x in Ioi (0:ℝ), (1 - F.G n x) :=
    setIntegral_congr_fun measurableSet_Ioi fun x hx => by
      simp [Sqrt.IncFamily.G, (mem_Ioi.1 hx).le]
  have h2 : ∫ x in Iic (0:ℝ), (F.G 0 x - F.G n x) = -∫ x in Iic (0:ℝ), F.G n x := by
    rw [integral_Iic_eq_integral_Iio, integral_Iic_eq_integral_Iio, ← integral_neg]
    exact setIntegral_congr_fun measurableSet_Iio fun x hx => by
      simp [Sqrt.IncFamily.G, not_le.2 (mem_Iio.1 hx)]
  rw [h1, h2]; ring

/-- **`Ω(log n)` lower bound.** If two actions have information laws with equal variances but
different third central moments, then `L_n - n h ≥ c log n` and `C_n - n h ≥ c log n` for
all large `n`. -/
theorem excess_log_lower {h : ℝ} (hh : κ.EqualEntropy h) {j k : Fin κ.nA}
    (hσ : (κ.fam h).sig2 j = (κ.fam h).sig2 k) (h3 : (κ.fam h).m3 j ≠ (κ.fam h).m3 k) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop,
      c * Real.log n ≤ envelopeMean (κ.rounds n) - n * h ∧ c * Real.log n ≤ κ.costBits n - n * h := by
  obtain ⟨c, hc, hev⟩ := (κ.fam h).eG_log_lower (κ.fam_centered hh) hσ h3
  refine ⟨c, hc, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  rw [κ.envelope_sub_eq_eG hh hn1]
  exact ⟨hn, hn.trans (by
    rw [← κ.envelope_sub_eq_eG hh hn1]; linarith [(κ.costBits_sandwich n).1])⟩

end CausalSpectrum.Kernel

namespace CausalSpectrum.Zero.NNKernel
variable (κ : NNKernel)

/-- **`Ω(log n)` for nonnegative kernels**, via the reduction `C_n(κ) = C_n(κ_red)`. -/
theorem excess_log_lower {h : ℝ} (hh : κ.red.EqualEntropy h) {j k : Fin κ.red.nA}
    (hσ : (κ.red.fam h).sig2 j = (κ.red.fam h).sig2 k)
    (h3 : (κ.red.fam h).m3 j ≠ (κ.red.fam h).m3 k) :
    ∃ c > 0, ∀ᶠ n : ℕ in atTop, c * Real.log n ≤ κ.costBits n - n * h := by
  obtain ⟨c, hc, hev⟩ := κ.red.excess_log_lower hh hσ h3
  exact ⟨c, hc, hev.mono fun n hn => by rw [κ.costBits_eq_red]; exact hn.2⟩

end CausalSpectrum.Zero.NNKernel

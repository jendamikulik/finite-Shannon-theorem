/-
Stage 4 (end): the rate `O(n^{-1/4} log n)` for the normalized envelope mean when
`b > 0`, and the convergence to `√(2/π)(a-b)`.
-/
import CausalSeed.SqrtMean
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.ExponentialBounds

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum.Sqrt

theorem one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

theorem rate_algebra {M A B D L q s : ℝ} (hM : 0 < M) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hL : 0 ≤ L) (hq : 1 ≤ q) (hs : 1 ≤ s) :
    2 * (M * Real.sqrt 2 * s) * (1 / q ^ 2 + 3 * A / q + B / q ^ 2 + L * s * (1 / q) + D / q ^ 2)
      + 2 * (M ^ 2 / (M * Real.sqrt 2 * s)) * (1 / q ^ 4) ≤
      Real.sqrt 2 * M * (2 * (1 + B + D + 3 * A + L) + 1) * (s ^ 2 / q) := by
  have hq0 : 0 < q := by linarith
  have hs0 : 0 < s := by linarith
  have h2 : 0 < Real.sqrt 2 := by positivity
  have h22 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  set i := 1 / q with hi
  have hi0 : 0 < i := by positivity
  have hi1 : i ≤ 1 := by rw [hi, div_le_one hq0]; exact hq
  have e2 : 1 / q ^ 2 = i ^ 2 := by rw [hi]; ring
  have e4 : 1 / q ^ 4 = i ^ 4 := by rw [hi]; ring
  have e1 : ∀ c, c / q = c * i := fun c => by rw [hi]; ring
  have e1' : ∀ c, c / q ^ 2 = c * i ^ 2 := fun c => by rw [hi]; ring
  rw [e2, e4, e1, e1', e1', e1]
  have hm : M ^ 2 / (M * Real.sqrt 2 * s) = Real.sqrt 2 * M / 2 * (1 / s) := by
    field_simp; nlinarith [h22]
  rw [hm]
  have hs1 : 1 / s ≤ 1 := by rw [div_le_one hs0]; exact hs
  have hsi : 0 < 1 / s := by positivity
  have hii : i ^ 2 ≤ i := by nlinarith
  have hi4 : i ^ 4 ≤ i := by nlinarith [pow_le_one₀ hi0.le hi1 (n := 3)]
  have hss : s ≤ s ^ 2 := by nlinarith
  have hss1 : 1 / s ≤ s ^ 2 := by nlinarith
  set c := M * Real.sqrt 2
  have hc : 0 < c := by positivity
  have key1 : 2 * (c * s) * (i ^ 2 + 3 * A * i + B * i ^ 2 + L * s * i + D * i ^ 2) ≤
      2 * c * (1 + B + D + 3 * A + L) * (s ^ 2 * i) := by
    have a1 : s * i ^ 2 ≤ s ^ 2 * i := by nlinarith
    have a2 : s * i ≤ s ^ 2 * i := by nlinarith
    have a3 : s * (s * i) = s ^ 2 * i := by ring
    have : 2 * (c * s) * (i ^ 2 + 3 * A * i + B * i ^ 2 + L * s * i + D * i ^ 2) =
        2 * c * ((1 + B + D) * (s * i ^ 2) + 3 * A * (s * i) + L * (s ^ 2 * i)) := by ring
    rw [this]
    have hsi2 : 0 ≤ s ^ 2 * i := by positivity
    have : (1 + B + D) * (s * i ^ 2) + 3 * A * (s * i) + L * (s ^ 2 * i) ≤
        (1 + B + D + 3 * A + L) * (s ^ 2 * i) := by nlinarith
    nlinarith
  have key2 : 2 * (Real.sqrt 2 * M / 2 * (1 / s)) * i ^ 4 ≤ c * (s ^ 2 * i) := by
    have : (1 / s) * i ^ 4 ≤ s ^ 2 * i :=
      mul_le_mul hss1 hi4 (by positivity) (by positivity)
    have e : 2 * (Real.sqrt 2 * M / 2 * (1 / s)) * i ^ 4 = c * ((1 / s) * i ^ 4) := by
      simp only [c]; ring
    rw [e]; exact mul_le_mul_of_nonneg_left this hc.le
  have e : Real.sqrt 2 * M * (2 * (1 + B + D + 3 * A + L) + 1) * (s ^ 2 * i) =
      2 * c * (1 + B + D + 3 * A + L) * (s ^ 2 * i) + c * (s ^ 2 * i) := by simp only [c]; ring
  rw [e]
  linarith

namespace IncFamily
variable (F : IncFamily)

/-- **Rate for `b > 0`.** `|Mn - √(2/π)(a-b)| ≤ K · log n / n^{1/4}` for `n ≥ 3`. -/
theorem mean_rate (hc : F.Centered) (hb : 0 < F.sB) :
    ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n →
      |F.Mn n - secondOrderCoeff F.sA F.sB| ≤ K * (Real.log n / Real.sqrt (Real.sqrt n)) := by
  set a := F.sA
  set b := F.sB
  have hab : b ≤ a := F.sB_le_sA
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hM : 0 < F.M := lt_of_lt_of_le ha F.sA_le_M
  have hA : 0 ≤ F.constA a b := by
    unfold constA; have := lipF_nonneg ha hb; have := F.M_nonneg; positivity
  have hB : 0 ≤ constB a b := by unfold constB; have := sqrt2pi_pos; positivity
  have hD : 0 ≤ constD a b := by unfold constD; have := sqrt2pi_pos; positivity
  have hL : 0 ≤ constL a b * a := by unfold constL; have := sqrt2pi_pos; positivity
  refine ⟨Real.sqrt 2 * F.M * (2 * (1 + constB a b + constD a b + 3 * F.constA a b +
    constL a b * a) + 1), fun n hn => ?_⟩
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hlog := one_le_log_of_three_le hn3
  set q := Real.sqrt (Real.sqrt n)
  set s := Real.sqrt (Real.log n)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hq2 : q ^ 2 = Real.sqrt n := Real.sq_sqrt hsn.le
  have hn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
  have hq4 : q ^ 4 = n := by rw [show q ^ 4 = (q ^ 2) ^ 2 by ring, hq2, hn2]
  have hs2 : s ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlog
  have hsqn1 : 1 ≤ Real.sqrt n := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hq1 : 1 ≤ q := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hsqn1
  have hq0 : 0 < q := by linarith
  set r := F.M * Real.sqrt 2 * s
  have hr : 0 < r := by positivity
  have hmb := F.mean_bound hc hb (by omega : 1 ≤ n) hsqn1 (by positivity : 0 ≤ s) hr
  -- bound the pieces of `e_n`
  have p1 : 2 * PhiNeg s ≤ 1 / q ^ 2 := by
    refine (two_PhiNeg_le (by positivity)).trans (le_of_eq ?_)
    rw [hs2, hq2, neg_div, Real.exp_neg, one_div]
    congr 1
    rw [← Real.log_sqrt hn0.le, Real.exp_log hsn]
  have p2 : 3 * F.constA a b / Real.sqrt (Real.sqrt n) = 3 * F.constA a b / q := rfl
  have p3 : constB a b / Real.sqrt n = constB a b / q ^ 2 := by rw [hq2]
  have p4 : constL a b * a * s * Real.sqrt (Real.sqrt n / (n + Real.sqrt n)) ≤
      constL a b * a * s * (1 / q) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [show 1 / q = Real.sqrt (1 / Real.sqrt n) by
      rw [Real.sqrt_div' 1 hsn.le, Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) hsn]
    nlinarith
  have p5 : constD a b * Real.log (1 + Real.sqrt n / n) ≤ constD a b / q ^ 2 := by
    rw [div_eq_mul_one_div (constD a b)]
    apply mul_le_mul_of_nonneg_left _ hD
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    rw [hq2]; field_simp; nlinarith [hn2]
  have hgM : gM F.M r = 1 / q ^ 4 := by
    unfold gM
    rw [hq4, show r ^ 2 = F.M ^ 2 * 2 * s ^ 2 by
      simp only [r]; rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num)]]
    rw [hs2, show F.M ^ 2 * 2 * Real.log n / (2 * F.M ^ 2) = Real.log n by field_simp,
      Real.exp_neg, Real.exp_log hn0, one_div]
  have hE : F.cdfErr n (Real.sqrt n) s ≤
      1 / q ^ 2 + 3 * F.constA a b / q + constB a b / q ^ 2 + constL a b * a * s * (1 / q) +
        constD a b / q ^ 2 := by
    unfold cdfErr
    rw [p2, p3]
    linarith
  have halg := rate_algebra hM hA hB hD hL hq1 hs1
  rw [hgM] at hmb
  have hmono : 2 * r * F.cdfErr n (Real.sqrt n) s ≤ 2 * r * (1 / q ^ 2 + 3 * F.constA a b / q +
      constB a b / q ^ 2 + constL a b * a * s * (1 / q) + constD a b / q ^ 2) :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have e : Real.log n / Real.sqrt (Real.sqrt n) = s ^ 2 / q := by rw [hs2]
  rw [e]
  simp only [r] at hmono hmb
  linarith

/-- Convergence of the normalized envelope mean to `√(2/π)(a - b)` for `b > 0`. -/
theorem mean_tendsto (hc : F.Centered) (hb : 0 < F.sB) :
    Tendsto F.Mn atTop (𝓝 (secondOrderCoeff F.sA F.sB)) := by
  obtain ⟨K, hK⟩ := F.mean_rate hc hb
  have hlim : Tendsto (fun n : ℕ => Real.log n / Real.sqrt (Real.sqrt n)) atTop (𝓝 0) := by
    have h1 := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
    have h2 := h1.comp tendsto_natCast_atTop_atTop
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp only [Function.comp]
    congr 1
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hK' : Tendsto (fun n : ℕ => K * (Real.log n / Real.sqrt (Real.sqrt n))) atTop (𝓝 0) := by
    simpa using hlim.const_mul K
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) _ hK'
  filter_upwards [eventually_ge_atTop 3] with n hn
  rw [Real.norm_eq_abs]
  exact hK n hn

#print axioms mean_rate
#print axioms mean_tendsto

end IncFamily
end CausalSpectrum.Sqrt

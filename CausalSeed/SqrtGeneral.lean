/-
The square-root asymptotic in general: `b = 0 < a` via the perturbation,
`a = b = 0`, and `(L_n - n h)/√n → √(2/π)(a - b)`, hence the same for `C_n`
and for the greedy seed.
-/
import CausalSeed.SqrtPerturb
import CausalSeed.SqrtMain

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum.Sqrt

theorem log_div_quarter_tendsto :
    Tendsto (fun n : ℕ => Real.log n / Real.sqrt (Real.sqrt n)) atTop (𝓝 0) := by
  have h1 := (isLittleO_log_rpow_atTop (show (0:ℝ) < 1 / 4 by norm_num)).tendsto_div_nhds_zero
  have h2 := h1.comp tendsto_natCast_atTop_atTop
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp only [Function.comp]
  congr 1
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
  norm_num

/-- The half-normal limit profile `F_{a,0}`. -/
def F0 (a x : ℝ) : ℝ := if x ≤ 0 then 0 else 1 - 2 * PhiNeg (x / a)

namespace IncFamily
variable (F : IncFamily)

/-- `e_n → 0` along `m = √n`, `R = √(ln n)`. -/
theorem cdfErr_eventually (hc : F.Centered) (hb : 0 < F.sB) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, F.cdfErr n (Real.sqrt n) (Real.sqrt (Real.log n)) ≤ δ := by
  set a := F.sA
  set b := F.sB
  have hab : b ≤ a := F.sB_le_sA
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hA : 0 ≤ F.constA a b := by
    unfold constA; have := lipF_nonneg ha hb; have := F.M_nonneg; positivity
  have hB : 0 ≤ constB a b := by unfold constB; have := sqrt2pi_pos; positivity
  have hD : 0 ≤ constD a b := by unfold constD; have := sqrt2pi_pos; positivity
  have hL : 0 ≤ constL a b * a := by unfold constL; have := sqrt2pi_pos; positivity
  set C := 1 + constB a b + constD a b + 3 * F.constA a b + constL a b * a
  have hC : 0 < C := by positivity
  have hev := (log_div_quarter_tendsto.eventually (gt_mem_nhds (show (0:ℝ) < δ / C by positivity)))
  filter_upwards [hev, eventually_ge_atTop 3] with n hlt hn
  have hn3 : (3:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hlog := one_le_log_of_three_le hn3
  set q := Real.sqrt (Real.sqrt n)
  set s := Real.sqrt (Real.log n)
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hq2 : q ^ 2 = Real.sqrt n := Real.sq_sqrt hsn.le
  have hs2 : s ^ 2 = Real.log n := Real.sq_sqrt (by linarith)
  have hs1 : 1 ≤ s := by rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hlog
  have hsqn1 : 1 ≤ Real.sqrt n := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hq1 : 1 ≤ q := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hsqn1
  have hq0 : 0 < q := by linarith
  have p1 : 2 * PhiNeg s ≤ 1 / q ^ 2 := by
    refine (two_PhiNeg_le (by positivity)).trans (le_of_eq ?_)
    rw [hs2, hq2, neg_div, Real.exp_neg, one_div]
    congr 1
    rw [← Real.log_sqrt hn0.le, Real.exp_log hsn]
  have p4 : constL a b * a * s * Real.sqrt (Real.sqrt n / (n + Real.sqrt n)) ≤
      constL a b * a * s * (1 / q) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [show 1 / q = Real.sqrt (1 / Real.sqrt n) by
      rw [Real.sqrt_div' 1 hsn.le, Real.sqrt_one]]
    apply Real.sqrt_le_sqrt
    rw [div_le_div_iff₀ (by positivity) hsn]
    have hn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
    nlinarith
  have p5 : constD a b * Real.log (1 + Real.sqrt n / n) ≤ constD a b / q ^ 2 := by
    rw [div_eq_mul_one_div (constD a b)]
    apply mul_le_mul_of_nonneg_left _ hD
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans (le_of_eq ?_)
    have hn2 : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn0.le
    rw [hq2]; field_simp; nlinarith [hn2]
  have hE : F.cdfErr n (Real.sqrt n) s ≤
      1 / q ^ 2 + 3 * F.constA a b / q + constB a b / q ^ 2 + constL a b * a * s * (1 / q) +
        constD a b / q ^ 2 := by
    unfold cdfErr
    rw [show constB a b / Real.sqrt n = constB a b / q ^ 2 by rw [hq2]]
    linarith
  -- each piece is at most `(log n)/q`
  have hi : 1 / q ≤ 1 := by rw [div_le_one hq0]; exact hq1
  have hii : 1 / q ^ 2 ≤ 1 / q := by
    rw [div_le_div_iff₀ (by positivity) hq0]; nlinarith
  have hss : s ≤ s ^ 2 := by nlinarith
  have hlq : 1 / q ≤ Real.log n / q := by
    rw [div_le_div_iff_of_pos_right hq0]; exact hlog
  have hsq : s / q ≤ Real.log n / q := by
    rw [div_le_div_iff_of_pos_right hq0, ← hs2]; exact hss
  have hbound : F.cdfErr n (Real.sqrt n) s ≤ C * (Real.log n / q) := by
    refine hE.trans ?_
    have e1 : 3 * F.constA a b / q = 3 * F.constA a b * (1 / q) := by ring
    have e2 : constB a b / q ^ 2 = constB a b * (1 / q ^ 2) := by ring
    have e3 : constD a b / q ^ 2 = constD a b * (1 / q ^ 2) := by ring
    have e4 : constL a b * a * s * (1 / q) = constL a b * a * (s / q) := by ring
    rw [e1, e2, e3, e4]
    have := mul_le_mul_of_nonneg_left (hii.trans hlq) hB
    have := mul_le_mul_of_nonneg_left (hii.trans hlq) hD
    have := mul_le_mul_of_nonneg_left hlq (show 0 ≤ 3 * F.constA a b by positivity)
    have := mul_le_mul_of_nonneg_left hsq hL
    have := hii.trans hlq
    simp only [C]; nlinarith
  calc _ ≤ C * (Real.log n / q) := hbound
    _ ≤ C * (δ / C) := by gcongr
    _ = δ := by field_simp

/-! ### Zero least variance -/

theorem tendsto_sA_perturb :
    Tendsto (fun ε => (F.perturb ε).sA) (𝓝[>] 0) (𝓝 F.sA) := by
  have hup : Tendsto (fun ε : ℝ => Real.sqrt (F.sA ^ 2 + ε ^ 2)) (𝓝[>] 0) (𝓝 F.sA) := by
    have : Tendsto (fun ε : ℝ => Real.sqrt (F.sA ^ 2 + ε ^ 2)) (𝓝 0)
        (𝓝 (Real.sqrt (F.sA ^ 2 + 0 ^ 2))) :=
      ((continuous_const.add (continuous_pow 2)).sqrt).tendsto 0
    have hA : 0 ≤ F.sA := (Real.sqrt_nonneg _).trans (F.sigma_le_sA ⟨0, F.hA⟩)
    rw [show Real.sqrt (F.sA ^ 2 + 0 ^ 2) = F.sA by simp [Real.sqrt_sq hA]] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun ε => (F.perturb_sA_bounds ε).1) (fun ε => (F.perturb_sA_bounds ε).2)

theorem tendsto_sB_perturb (hb0 : F.sB = 0) :
    Tendsto (fun ε => (F.perturb ε).sB) (𝓝[>] 0) (𝓝 0) := by
  have hup : Tendsto (fun ε : ℝ => Real.sqrt (F.sB ^ 2 + ε ^ 2)) (𝓝[>] 0) (𝓝 0) := by
    have : Tendsto (fun ε : ℝ => Real.sqrt (F.sB ^ 2 + ε ^ 2)) (𝓝 0)
        (𝓝 (Real.sqrt (F.sB ^ 2 + 0 ^ 2))) :=
      ((continuous_const.add (continuous_pow 2)).sqrt).tendsto 0
    rw [show Real.sqrt (F.sB ^ 2 + 0 ^ 2) = 0 by simp [hb0]] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_
    (Eventually.of_forall fun ε => F.perturb_sB_bounds ε)
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (F.perturb_sB_pos hε).le

theorem tendsto_q :
    Tendsto (fun ε : ℝ => Real.exp (-(Real.sqrt ε ^ 2 / (2 * ε ^ 2)))) (𝓝[>] 0) (𝓝 0) := by
  have h1 : Tendsto (fun ε : ℝ => -(1 / 2 * ε⁻¹)) (𝓝[>] 0) atBot :=
    tendsto_neg_atTop_atBot.comp (tendsto_inv_nhdsGT_zero.const_mul_atTop (by norm_num))
  refine (Real.tendsto_exp_atBot.comp h1).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : 0 < ε := hε
  simp only [Function.comp]
  congr 1
  rw [Real.sq_sqrt hε'.le]; field_simp

/-- The right-branch value `F_{a',b'}(z)`, `z > 0`, as `ε → 0`. -/
theorem tendsto_FR (hb0 : F.sB = 0) (ha : 0 < F.sA) {x : ℝ} {g : ℝ → ℝ}
    (hg : Tendsto g (𝓝[>] 0) (𝓝 x)) :
    Tendsto (fun ε => FR (F.perturb ε).sA (F.perturb ε).sB (g ε)) (𝓝[>] 0)
      (𝓝 (1 - 2 * PhiNeg (x / F.sA))) := by
  have ta := F.tendsto_sA_perturb
  have tb := F.tendsto_sB_perturb hb0
  have hsum : Tendsto (fun ε => (F.perturb ε).sA + (F.perturb ε).sB) (𝓝[>] 0) (𝓝 (F.sA + 0)) :=
    ta.add tb
  have hcoef := (tendsto_const_nhds (x := (2:ℝ))).mul ta |>.div hsum (by simp; exact ha.ne')
  have harg := hg.div ta ha.ne'
  have hgt := ((continuous_gaussTail.tendsto _).comp harg).div_const (Real.sqrt (2 * Real.pi))
  have := tendsto_const_nhds (x := (1:ℝ)) |>.sub (hcoef.mul hgt)
  have e : 1 - 2 * PhiNeg (x / F.sA) =
      1 - 2 * F.sA / (F.sA + 0) * (gaussTail (x / F.sA) / Real.sqrt (2 * Real.pi)) := by
    unfold PhiNeg; field_simp; ring
  rw [e]; unfold FR; exact this

theorem pointwise_b0 (hc : F.Centered) (hb0 : F.sB = 0) (ha : 0 < F.sA) (x : ℝ) :
    Tendsto (fun n : ℕ => F.G n (x * Real.sqrt n)) atTop (𝓝 (F0 F.sA x)) := by
  rw [Metric.tendsto_atTop]
  intro δ hδ
  set a := F.sA
  -- choose `ε`
  set q := fun ε : ℝ => Real.exp (-(Real.sqrt ε ^ 2 / (2 * ε ^ 2)))
  have hU : ∀ᶠ ε in 𝓝[>] (0:ℝ),
      prof (F.perturb ε).sA (F.perturb ε).sB (x + Real.sqrt ε) + q ε < F0 a x + δ / 2 := by
    have hpos : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε := self_mem_nhdsWithin
    rcases lt_or_ge x 0 with hx | hx
    · -- `x < 0`: bounded by `F(0) = b'/(a'+b') → 0`
      have hs : Tendsto (fun ε : ℝ => Real.sqrt ε) (𝓝[>] 0) (𝓝 0) := by
        have := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using this
      have hneg : ∀ᶠ ε in 𝓝[>] (0:ℝ), x + Real.sqrt ε ≤ 0 :=
        (hs.eventually (ge_mem_nhds (show (0:ℝ) < -x by linarith))).mono fun ε h => by linarith
      have ta := F.tendsto_sA_perturb
      have tb := F.tendsto_sB_perturb hb0
      have hfrac : Tendsto (fun ε => (F.perturb ε).sB / ((F.perturb ε).sA + (F.perturb ε).sB) + q ε)
          (𝓝[>] 0) (𝓝 (0 / (a + 0) + 0)) :=
        (tb.div (ta.add tb) (by simp; exact ha.ne')).add tendsto_q
      rw [show (0:ℝ) / (a + 0) + 0 = 0 by simp] at hfrac
      have hlt := hfrac.eventually (gt_mem_nhds (show (0:ℝ) < δ / 2 by positivity))
      filter_upwards [hpos, hneg, hlt] with ε hε hn hl
      have hbε := F.perturb_sB_pos hε
      have haε : 0 < (F.perturb ε).sA := lt_of_lt_of_le hbε (F.perturb ε).sB_le_sA
      have := prof_monotone haε hbε hn
      rw [prof_zero haε hbε] at this
      simp only [F0, if_pos hx.le]
      linarith
    · -- `x ≥ 0`: the right branch, limit `1 - 2Φ(-x/a) = F_{a,0}(x)` (also at `x = 0`)
      have hs : Tendsto (fun ε : ℝ => x + Real.sqrt ε) (𝓝[>] 0) (𝓝 x) := by
        have h0 := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using (tendsto_const_nhds (x := x)).add h0
      have hlim := (F.tendsto_FR hb0 ha hs).add tendsto_q
      have hval : 1 - 2 * PhiNeg (x / a) + 0 = F0 a x := by
        rcases eq_or_lt_of_le hx with h | h
        · subst h; simp [F0, PhiNeg_zero]
        · simp [F0, not_le.mpr h]
      rw [hval] at hlim
      have hlt := hlim.eventually (gt_mem_nhds (show F0 a x < F0 a x + δ / 2 by linarith))
      filter_upwards [hpos, hlt] with ε hε hl
      have hz : 0 < x + Real.sqrt ε := by have := Real.sqrt_pos.mpr hε; linarith
      simp only [prof, if_neg (not_le.mpr hz)]
      exact hl
  have hL : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < x →
      F0 a x - δ / 2 < prof (F.perturb ε).sA (F.perturb ε).sB (x - Real.sqrt ε) - q ε := by
    rcases le_or_gt x 0 with hx | hx
    · exact Eventually.of_forall fun ε h => absurd h (not_lt.mpr hx)
    · have hs : Tendsto (fun ε : ℝ => x - Real.sqrt ε) (𝓝[>] 0) (𝓝 x) := by
        have h0 := (Real.continuous_sqrt.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi 0))
        simpa using (tendsto_const_nhds (x := x)).sub h0
      have hlim := (F.tendsto_FR hb0 ha hs).sub tendsto_q
      rw [show 1 - 2 * PhiNeg (x / a) - 0 = F0 a x by simp [F0, not_le.mpr hx]] at hlim
      have hlt := hlim.eventually (lt_mem_nhds (show F0 a x - δ / 2 < F0 a x by linarith))
      have hpos : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < x - Real.sqrt ε :=
        hs.eventually (lt_mem_nhds hx)
      filter_upwards [hlt, hpos] with ε hl hp _
      simp only [prof, if_neg (not_le.mpr hp)]
      exact hl
  obtain ⟨ε, ⟨hU', hL'⟩, hε⟩ := ((hU.and hL).and self_mem_nhdsWithin).exists
  have hε' : 0 < ε := hε
  -- then `n → ∞`
  set Fe := F.perturb ε
  have hce := F.perturb_centered hc ε
  have hbe := F.perturb_sB_pos hε'
  have hev := Fe.cdfErr_eventually hce hbe (show (0:ℝ) < δ / 2 by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 3))
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨he, hn3⟩ := hN n hn
  have hn1 : 1 ≤ n := by omega
  have hsqn1 : 1 ≤ Real.sqrt n := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  have hlog0 : 0 ≤ Real.sqrt (Real.log n) := Real.sqrt_nonneg _
  have hη : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε'
  obtain ⟨nlo, nhi⟩ := F.noise_compare hε' hη (show 0 < n by omega) x
  have cu := Fe.cdf_comparison hce hbe hn1 hsqn1 hlog0 (x + Real.sqrt ε)
  have cl := Fe.cdf_comparison hce hbe hn1 hsqn1 hlog0 (x - Real.sqrt ε)
  rw [Real.dist_eq, abs_lt]
  constructor
  · rcases le_or_gt x 0 with hx | hx
    · have := ((F.G_cdf n).2.2.1 (x * Real.sqrt n)).1
      simp only [F0, if_pos hx]; linarith
    · have := hL' hx
      have := (abs_le.mp cl).1
      simp only [q] at *
      linarith
  · have := (abs_le.mp cu).2
    simp only [q] at *
    linarith

/-- Mean convergence for `b = 0 < a` by dominated convergence. -/
theorem mean_tendsto_b0 (hc : F.Centered) (hb0 : F.sB = 0) (ha : 0 < F.sA) :
    Tendsto F.Mn atTop (𝓝 (secondOrderCoeff F.sA F.sB)) := by
  set a := F.sA
  have hM : 0 < F.M := lt_of_lt_of_le ha F.sA_le_M
  have hGb := fun n x => (F.G_cdf n).2.2.1 x
  have hmeas : ∀ n, Measurable (F.G n) := F.G_measurable
  have h1 : Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ), (1 - F.G n (x * Real.sqrt n))) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), profileHalf a x)) := by
    have hlim := tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
      (F := fun (n : ℕ) (x : ℝ) => 1 - F.G n (x * Real.sqrt n))
      (f := fun x => profileHalf a x) (gM F.M)
      (Eventually.of_forall fun n =>
        (measurable_const.sub ((hmeas n).comp (measurable_id.mul_const _))).aestronglyMeasurable)
      (by
        filter_upwards [eventually_ge_atTop 1] with n hn
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine ae_of_all _ fun x hx => ?_
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [(hGb n (x * Real.sqrt n)).2])]
        exact F.G_upper_tail hc (by omega) hx)
      (integrable_gM hM).integrableOn
      (by
        rw [ae_restrict_iff' measurableSet_Ioi]
        refine ae_of_all _ fun x hx => ?_
        have := (tendsto_const_nhds (x := (1:ℝ))).sub (F.pointwise_b0 hc hb0 ha x)
        convert this using 2
        simp only [F0, if_neg (not_le.mpr (mem_Ioi.mp hx)), profileHalf, PhiNeg]; ring)
    exact hlim
  have h2 : Tendsto (fun n : ℕ => ∫ x in Ioi (0:ℝ), F.G n (-(x * Real.sqrt n))) atTop
      (𝓝 (∫ x in Ioi (0:ℝ), (0:ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence (μ := volume.restrict (Ioi 0))
      (F := fun (n : ℕ) (x : ℝ) => F.G n (-(x * Real.sqrt n))) (gM F.M)
      (Eventually.of_forall fun n =>
        ((hmeas n).comp ((measurable_id.mul_const _).neg)).aestronglyMeasurable) ?_
      (integrable_gM hM).integrableOn ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun x hx => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hGb n _).1]
      exact F.G_lower_tail hc (by omega) hx
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine ae_of_all _ fun x hx => ?_
      have := F.pointwise_b0 hc hb0 ha (-x)
      simp only [F0, if_pos (show -x ≤ 0 by linarith [mem_Ioi.mp hx]), neg_mul] at this
      exact this
  have := h1.sub h2
  rw [integral_zero, sub_zero, profile_mean_zero a ha] at this
  rw [hb0]; exact this

/-- `a = b = 0`: every increment vanishes, `G_n = G_0`, and the normalized mean is `0`. -/
theorem mean_tendsto_zero (ha : F.sA = 0) :
    Tendsto F.Mn atTop (𝓝 (secondOrderCoeff F.sA F.sB)) := by
  have hb : F.sB = 0 := le_antisymm (ha ▸ F.sB_le_sA) (by
      obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' F.univ_nonempty F.sigma
      unfold sB; rw [hj]; exact Real.sqrt_nonneg _)
  have hX : ∀ j y, F.X j y = 0 := by
    intro j y
    have h1 : F.sigma j = 0 := le_antisymm (ha ▸ F.sigma_le_sA j) (Real.sqrt_nonneg _)
    have h2 : F.sig2 j = 0 := by rw [← F.sigma_sq, h1]; ring
    unfold sig2 at h2
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun y _ =>
      mul_nonneg (F.Ppos j y).le (sq_nonneg (F.X j y)))).mp h2 y (Finset.mem_univ y)
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h (F.Ppos j y).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
  have hT : ∀ f : ℝ → ℝ, F.T f = f := by
    intro f; funext x
    obtain ⟨j, hj⟩ := F.T_attained f x
    rw [hj]; unfold expect; simp [hX, ← Finset.sum_mul, F.Psum]
  have hG : ∀ n, F.G n = F.G 0 := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => rw [G_succ, hT, ih]
  have hMn : ∀ n : ℕ, 1 ≤ n → F.Mn n = 0 := by
    intro n hn
    have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    unfold Mn
    rw [hG n]
    have e1 : ∫ x in Ioi (0:ℝ), (1 - F.G 0 (x * Real.sqrt n)) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℝ)) (fun x hx => by
        simp only [G, if_pos (mul_pos (mem_Ioi.mp hx) hs).le]; ring)]
      simp
    have e2 : ∫ x in Ioi (0:ℝ), F.G 0 (-(x * Real.sqrt n)) = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioi (g := fun _ => (0:ℝ)) (fun x hx => by
        simp only [G]; rw [if_neg]; have := mul_pos (mem_Ioi.mp hx) hs; linarith)]
      simp
    rw [e1, e2]; ring
  rw [ha, hb, show secondOrderCoeff 0 0 = 0 by simp [secondOrderCoeff]]
  exact tendsto_const_nhds.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn; exact (hMn n hn).symm)

/-- **The normalized envelope mean converges to `√(2/π)(a - b)`, in general.** -/
theorem mean_tendsto_general (hc : F.Centered) :
    Tendsto F.Mn atTop (𝓝 (secondOrderCoeff F.sA F.sB)) := by
  have hb0 : 0 ≤ F.sB := by
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' F.univ_nonempty F.sigma
    unfold sB; rw [hj]; exact Real.sqrt_nonneg _
  rcases eq_or_lt_of_le hb0 with hb | hb
  · rcases eq_or_lt_of_le ((le_of_eq hb).trans F.sB_le_sA) with ha | ha
    · exact F.mean_tendsto_zero ha.symm
    · exact F.mean_tendsto_b0 hc hb.symm ha
  · exact F.mean_tendsto hc hb

#print axioms mean_tendsto_general

end IncFamily
end CausalSpectrum.Sqrt

namespace CausalSpectrum.Kernel
open Sqrt

variable (κ : Kernel)

/-- **Theorem (main), general case, for `L_n`.** -/
theorem envelope_tendsto {h : ℝ} (hh : κ.EqualEntropy h) :
    Tendsto (fun n : ℕ => (envelopeMean (κ.rounds n) - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff (κ.fam h).sA (κ.fam h).sB)) := by
  refine ((κ.fam h).mean_tendsto_general (κ.fam_centered hh)).congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact (κ.mean_identity hh hn).symm

/-- **Theorem (main), general case, for `C_n` (bits).** -/
theorem cost_tendsto {h : ℝ} (hh : κ.EqualEntropy h) :
    Tendsto (fun n : ℕ => (κ.costBits n - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff (κ.fam h).sA (κ.fam h).sB)) :=
  second_order_transfer (fun n => (κ.costBits_sandwich n).1) (fun n => (κ.costBits_sandwich n).2)
    (κ.envelope_tendsto hh)

/-- **Theorem (main), general case, for the greedy seed** (any choice of greedy seeds). -/
theorem greedy_tendsto {h : ℝ} (hh : κ.EqualEntropy h)
    (atoms : ∀ n, List (Atom (κ.rounds n)))
    (hlo : ∀ n, envelopeMean (κ.rounds n) ≤ seedShannon (atoms n))
    (hhi : ∀ n, seedShannon (atoms n) ≤ envelopeMean (κ.rounds n) + shannonOverhead) :
    Tendsto (fun n : ℕ => (seedShannon (atoms n) - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff (κ.fam h).sA (κ.fam h).sB)) :=
  second_order_transfer hlo hhi (κ.envelope_tendsto hh)

end CausalSpectrum.Kernel

#print axioms CausalSpectrum.Kernel.envelope_tendsto
#print axioms CausalSpectrum.Kernel.cost_tendsto
#print axioms CausalSpectrum.Kernel.greedy_tendsto
#print axioms CausalSpectrum.Kernel.cost_rate
#print axioms CausalSpectrum.Kernel.greedy_rate

/-
`W₁` universality with the optimal-transport Wasserstein distance.

The limit profile `F_{a,b}` is the CDF of a probability measure `limitLaw`, and the
normalized information `(J_n - n h)/√n` of a countable seed has the law `normLaw`.
With `W1` defined as an infimum over couplings (`CausalSpectrum.OT.W1`), the
universality theorem reads `W1 (law of (J_n - nh)/√n) (limitLaw) → 0`.
-/
import CausalSeed.SqrtUniversalityCountable
import CausalSeed.Wasserstein

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum.Sqrt.IncFamily
variable (F : IncFamily)

theorem Flim_mono (hc : F.Centered) (ha : 0 < F.sA) : Monotone F.Flim := fun x y hxy =>
  le_of_tendsto_of_tendsto' (F.pointwise hc ha x) (F.pointwise hc ha y) fun n =>
    (F.G_cdf n).1 (mul_le_mul_of_nonneg_right hxy (Real.sqrt_nonneg _))

theorem continuous_F0 {a : ℝ} (ha : 0 < a) : Continuous (F0 a) := by
  unfold F0
  refine Continuous.if_le continuous_const ?_ continuous_id continuous_const ?_
  · exact continuous_const.sub (continuous_const.mul
      ((continuous_gaussTail.comp (continuous_id.div_const a)).div_const _))
  · intro x hx
    rw [hx, zero_div, PhiNeg, gaussTail_zero]
    field_simp [sqrt2pi_pos.ne']
    ring

theorem Flim_continuous (ha : 0 < F.sA) : Continuous F.Flim := by
  unfold Flim
  split_ifs with hb
  · exact continuous_iff_continuousAt.2 fun z =>
      (hasDerivAt_prof ha hb z).continuousAt
  · exact continuous_F0 ha

theorem gM_tendsto (hM : 0 < F.M) : Tendsto (gM F.M) atTop (𝓝 0) := by
  unfold gM
  refine Real.tendsto_exp_atBot.comp ?_
  refine tendsto_neg_atTop_atBot.comp ?_
  refine Tendsto.atTop_div_const (by positivity) ?_
  exact tendsto_pow_atTop (by norm_num)

theorem Flim_atTop (hc : F.Centered) (ha : 0 < F.sA) : Tendsto F.Flim atTop (𝓝 1) := by
  have hM : 0 < F.M := lt_of_lt_of_le ha F.sA_le_M
  have h0 : Tendsto (fun x => 1 - F.Flim x) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun x => by linarith [(F.Flim_mem hc ha x).2])
      ((eventually_gt_atTop 0).mono fun x hx => F.Flim_upper hc ha hx) (F.gM_tendsto hM)
  have := (tendsto_const_nhds (x := (1:ℝ))).sub h0
  simpa using this

theorem Flim_atBot (hc : F.Centered) (ha : 0 < F.sA) : Tendsto F.Flim atBot (𝓝 0) := by
  have hM : 0 < F.M := lt_of_lt_of_le ha F.sA_le_M
  have h0 : Tendsto (fun x => F.Flim (-x)) atTop (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall fun x => (F.Flim_mem hc ha _).1)
      ((eventually_gt_atTop 0).mono fun x hx => F.Flim_lower hc ha hx) (F.gM_tendsto hM)
  have := h0.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this

/-- `F_{a,b}` as a Stieltjes function. -/
def FlimS (hc : F.Centered) (ha : 0 < F.sA) : StieltjesFunction ℝ where
  toFun := F.Flim
  mono' := F.Flim_mono hc ha
  right_continuous' x := (F.Flim_continuous ha).continuousWithinAt

/-- The limit law: the probability measure with CDF `F_{a,b}`. -/
def limitLaw (hc : F.Centered) (ha : 0 < F.sA) : Measure ℝ := (F.FlimS hc ha).measure

theorem cdf_limitLaw (hc : F.Centered) (ha : 0 < F.sA) :
    (cdf (F.limitLaw hc ha) : ℝ → ℝ) = F.Flim := by
  rw [limitLaw, cdf_measure_stieltjesFunction _ (F.Flim_atBot hc ha) (F.Flim_atTop hc ha)]
  rfl

instance (hc : F.Centered) (ha : 0 < F.sA) : IsProbabilityMeasure (F.limitLaw hc ha) :=
  ⟨by rw [limitLaw, (F.FlimS hc ha).measure_univ (F.Flim_atBot hc ha) (F.Flim_atTop hc ha)]
      simp⟩

end CausalSpectrum.Sqrt.IncFamily

namespace CausalSpectrum.Completion.CountableSeed
variable {ι : ITree}

/-- The law of `(J - c)/s`, where `J = -log₂ w_i` with probability `w_i`. -/
def normLaw (G : CountableSeed ι) (c s : ℝ) : Measure ℝ :=
  Measure.sum fun i => ENNReal.ofReal (G.weight i) • Measure.dirac ((infoMass (G.weight i) - c) / s)

theorem normLaw_apply (G : CountableSeed ι) (c s : ℝ) {A : Set ℝ} (hA : MeasurableSet A) :
    G.normLaw c s A = ∑' i, ENNReal.ofReal (G.weight i) *
      A.indicator 1 ((infoMass (G.weight i) - c) / s) := by
  rw [normLaw, Measure.sum_apply _ hA]
  refine tsum_congr fun i => ?_
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA, smul_eq_mul]

theorem tsum_ofReal_weight (G : CountableSeed ι) : ∑' i, ENNReal.ofReal (G.weight i) = 1 := by
  rw [← ENNReal.ofReal_tsum_of_nonneg G.nonneg G.mass.summable, G.mass.tsum_eq]; simp

instance (G : CountableSeed ι) (c s : ℝ) : IsProbabilityMeasure (G.normLaw c s) :=
  ⟨by rw [normLaw_apply _ _ _ MeasurableSet.univ]; simp [tsum_ofReal_weight]⟩

theorem cdf_normLaw (G : CountableSeed ι) (c : ℝ) {s : ℝ} (hs : 0 < s) (x : ℝ) :
    cdf (G.normLaw c s) x = G.cCDF (c + x * s) := by
  have hle : ∀ i, (infoMass (G.weight i) - c) / s ≤ x ↔ ¬ (c + x * s < infoMass (G.weight i)) := by
    intro i; rw [div_le_iff₀ hs, not_lt]; constructor <;> intro h <;> linarith
  have hsum : HasSum (fun i => if c + x * s < infoMass (G.weight i) then 0 else G.weight i)
      (1 - G.cTail (c + x * s)) := by
    have := G.mass.sub (G.term_summable (c + x * s)).hasSum
    convert this using 1
    all_goals first | rfl | (funext i; split_ifs <;> ring)
  have hnn : ∀ i, 0 ≤ (if c + x * s < infoMass (G.weight i) then 0 else G.weight i) := fun i => by
    split_ifs; exacts [le_rfl, G.nonneg i]
  have hE : G.normLaw c s (Iic x) = ENNReal.ofReal (1 - G.cTail (c + x * s)) := by
    rw [normLaw_apply _ _ _ measurableSet_Iic, ← hsum.tsum_eq,
      ENNReal.ofReal_tsum_of_nonneg hnn hsum.summable]
    refine tsum_congr fun i => ?_
    by_cases h : c + x * s < infoMass (G.weight i)
    · have : ¬ (infoMass (G.weight i) - c) / s ≤ x := fun h' => (hle i).1 h' h
      simp [h, indicator, this]
    · have : (infoMass (G.weight i) - c) / s ≤ x := (hle i).2 h
      simp [h, indicator, this]
  have h1 : 0 ≤ cdf (G.normLaw c s) x := cdf_nonneg _ _
  have h2 : 0 ≤ 1 - G.cTail (c + x * s) := by linarith [G.cTail_le_one (c + x * s)]
  rw [cCDF, ← ENNReal.ofReal_eq_ofReal_iff h1 h2, ofReal_cdf, hE]

end CausalSpectrum.Completion.CountableSeed

namespace CausalSpectrum.Kernel
open Completion
variable (κ : Kernel)

/-- **`W₁` universality, optimal-transport form.** For a stationary kernel with common
entropy `h` and `a > 0`, and countable seeds `S_n` exact to horizon `n` with finite
entropy and `H(S_n) - C_n = o(√n)`, the Wasserstein-1 distance (infimum over couplings)
between the law of `(J_n - nh)/√n` and the probability law with CDF `F_{a,b}` tends to 0. -/
theorem universality_W1 {h : ℝ} (hh : κ.EqualEntropy h) (ha : 0 < (κ.fam h).sA)
    (G : ℕ → CountableSeed κ.toITree) (hG : ∀ n, (G n).ExactTo n) (hfin : ∀ n, (G n).entropy ≠ ⊤)
    (hopt : Tendsto (fun n : ℕ => ((G n).bits - κ.costBits n) / Real.sqrt n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => OT.W1 ((G n).normLaw (n * h) (Real.sqrt n))
      ((κ.fam h).limitLaw (κ.fam_centered hh) ha)) atTop (𝓝 0) := by
  obtain ⟨hint, hlim⟩ := κ.universality_countable hh ha G hG hfin hopt
  have hc := κ.fam_centered hh
  have heq : ∀ n : ℕ, 1 ≤ n → OT.W1 ((G n).normLaw (n * h) (Real.sqrt n))
      ((κ.fam h).limitLaw hc ha) = ENNReal.ofReal
        (∫ x, |(G n).cCDF (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|) := by
    intro n hn
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    rw [OT.W1_eq_cdfDist, OT.cdfDist, ofReal_integral_eq_lintegral_ofReal (hint n hn)
      (Eventually.of_forall fun _ => abs_nonneg _)]
    refine lintegral_congr fun x => ?_
    rw [(G n).cdf_normLaw _ hs, (κ.fam h).cdf_limitLaw hc ha]
  have : Tendsto (fun n : ℕ => ENNReal.ofReal
      (∫ x, |(G n).cCDF (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|)) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal hlim)
  exact this.congr' ((eventually_ge_atTop 1).mono fun n hn => (heq n hn).symm)

end CausalSpectrum.Kernel

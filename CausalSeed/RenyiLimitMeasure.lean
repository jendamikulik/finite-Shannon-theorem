/-
The limit envelope law as an actual measure.

`F_∞ = FInf ι` is right-continuous (`FInf_rightCont`), so it is a Stieltjes function;
`muInf ι` is its Lebesgue–Stieltjes measure on `ℝ` (total mass `atomQ ι`, supported on
`[0,∞)`), and `lawZ ι := map coe (muInf ι) + (1 - atomQ ι) • δ_⊤` is a probability
measure on `EReal` with `lawZ {z | t < z} = 1 - F_∞(t)` for `t ≥ 0`: the law of the limit
variable `Z ∈ [0, ∞]`.  Its moments, as Lebesgue integrals, equal the tail-formula values
`zMomLaw`, `zMomLawR`, `zMeanLaw` of `RenyiLimitLaw`.
-/
import CausalSeed.RenyiLimitLaw
import CausalSeed.SqrtUniversality

noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal Topology
namespace CausalSpectrum.RenyiInf
open CausalSpectrum.Completion CausalSpectrum.Renyi

/-- A monotone function that is an infimum of functions right-upper-semicontinuous at `t`
is right-continuous at `t`. -/
theorem rightCont_of_inf {f : ℝ → ℝ} (hf : Monotone f) {ι' : Type*} (g : ι' → ℝ → ℝ)
    (hle : ∀ i s, f s ≤ g i s) (t : ℝ)
    (happ : ∀ b, f t < b → ∃ i, g i t < b)
    (hg : ∀ i, ContinuousWithinAt (g i) (Ici t) t) : ContinuousWithinAt f (Ici t) t := by
  rw [ContinuousWithinAt, tendsto_order]
  refine ⟨fun b hb => ?_, fun b hb => ?_⟩
  · exact eventually_nhdsWithin_of_forall fun s hs => lt_of_lt_of_le hb (hf hs)
  · obtain ⟨i, hi⟩ := happ b hb
    have := (tendsto_order.mp (hg i)).2 b hi
    filter_upwards [this] with s hs using lt_of_le_of_lt (hle i s) hs

theorem ite_rightCont (I m t : ℝ) :
    ContinuousWithinAt (fun s : ℝ => if I ≤ s then m else 0) (Ici t) t := by
  by_cases h : I ≤ t
  · refine (continuousWithinAt_const (b := m)).congr (fun s hs => ?_) (by simp [h])
    simp [le_trans h hs]
  · push_neg at h
    refine (continuousWithinAt_const (b := (0:ℝ))).congr_of_eventuallyEq ?_ (by simp [not_le.mpr h])
    filter_upwards [Ico_mem_nhdsGE h] with s hs
    simp [not_le.mpr hs.2]

theorem policyCDF_rightCont {T : Tree} (π : Policy T) (t : ℝ) :
    ContinuousWithinAt (policyCDF T π) (Ici t) t := by
  have e : policyCDF T π = fun s => ∑ ℓ ∈ (Finset.univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π),
      (if infoMass (leafMass ℓ) ≤ s then leafMass ℓ else 0) := funext fun s => policyCDF_eq π s
  rw [e]
  exact tendsto_finset_sum _ fun ℓ _ => ite_rightCont _ _ t

theorem Fstar_rightCont (T : Tree) (t : ℝ) : ContinuousWithinAt (Fstar T) (Ici t) t :=
  rightCont_of_inf (Fstar_mono T) (fun π => policyCDF T π) (fun π s => Fstar_le T s π) t
    (fun b hb => ⟨envelopePolicy T t, hb⟩) (fun π => policyCDF_rightCont π t)

variable (ι : ITree)

theorem FInf_rightCont (t : ℝ) : ContinuousWithinAt (FInf ι) (Ici t) t :=
  rightCont_of_inf (FInf_mono ι) (fun n => Fstar (trunc ι n []))
    (fun n s => FInf_le ι s n) t
    (fun b hb => by
      obtain ⟨n, hn⟩ := exists_lt_of_ciInf_lt (f := fun n => Fstar (trunc ι n []) t) hb
      exact ⟨n, hn⟩)
    (fun n => Fstar_rightCont _ t)

/-- `F_∞` as a Stieltjes function. -/
def FInfS : StieltjesFunction ℝ := ⟨FInf ι, FInf_mono ι, FInf_rightCont ι⟩

/-- The finite part of the law of `Z`. -/
def muInf : Measure ℝ := (FInfS ι).measure

theorem FInf_neg {t : ℝ} (ht : t < 0) : FInf ι t = 0 :=
  le_antisymm ((FInf_le ι t 0).trans (le_of_eq (Kernel.Fstar_neg _ ht))) (FInf_nonneg ι t)

theorem FInf_atBot : Tendsto (FInf ι) atBot (𝓝 0) :=
  tendsto_const_nhds.congr' (by
    filter_upwards [eventually_lt_atBot 0] with t ht using (FInf_neg ι ht).symm)

theorem atomQ_le_one : atomQ ι ≤ 1 :=
  le_of_tendsto' (atomQ_eq_lim_FInf ι) (FInf_le_one ι)

theorem atomQ_nonneg : 0 ≤ atomQ ι :=
  ge_of_tendsto' (atomQ_eq_lim_FInf ι) (FInf_nonneg ι)

theorem muInf_Ioi (t : ℝ) : muInf ι (Ioi t) = ENNReal.ofReal (atomQ ι - FInf ι t) :=
  (FInfS ι).measure_Ioi (atomQ_eq_lim_FInf ι) t

theorem muInf_univ : muInf ι univ = ENNReal.ofReal (atomQ ι) := by
  have := (FInfS ι).measure_univ (FInf_atBot ι) (atomQ_eq_lim_FInf ι)
  simpa [muInf] using this

instance : IsFiniteMeasure (muInf ι) := ⟨by rw [muInf_univ]; exact ENNReal.ofReal_lt_top⟩

theorem muInf_Iio : muInf ι (Iio 0) = 0 := by
  have e : Iio (0:ℝ) = ⋃ n : ℕ, Iic (-(1 / ((n:ℝ) + 1))) := by
    ext x; simp only [mem_Iio, mem_iUnion, mem_Iic]
    constructor
    · intro hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (neg_pos.mpr hx)
      exact ⟨n, by linarith⟩
    · rintro ⟨n, hn⟩; have : 0 < 1 / ((n:ℝ) + 1) := by positivity
      linarith
  rw [e]
  refine measure_iUnion_null fun n => ?_
  have h := (FInfS ι).measure_Iic (FInf_atBot ι) (-(1 / ((n:ℝ) + 1)))
  rw [muInf, h]
  have : FInf ι (-(1 / ((n:ℝ) + 1))) = 0 := FInf_neg ι (by
    have : 0 < 1 / ((n:ℝ) + 1) := by positivity
    linarith)
  show ENNReal.ofReal (FInf ι _ - 0) = 0
  rw [this]; simp

theorem muInf_nonneg : ∀ᵐ x ∂(muInf ι), 0 ≤ x := by
  rw [ae_iff]
  simp only [not_le]
  exact muInf_Iio ι

/-- **The law of the limit variable `Z` on `[0, ∞] ⊆ EReal`.** -/
def lawZ : Measure EReal :=
  (muInf ι).map (fun x : ℝ => (x : EReal)) + ENNReal.ofReal (1 - atomQ ι) • Measure.dirac ⊤

theorem coe_meas : Measurable (fun x : ℝ => (x : EReal)) := measurable_coe_real_ereal

instance : IsProbabilityMeasure (lawZ ι) := by
  constructor
  rw [lawZ, Measure.add_apply, Measure.map_apply (coe_meas) MeasurableSet.univ, preimage_univ,
    muInf_univ, Measure.smul_apply, Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one,
    ← ENNReal.ofReal_add (atomQ_nonneg ι) (by linarith [atomQ_le_one ι])]
  simp

/-- The tail of `Z`: `P(Z > t) = 1 - F_∞(t)`. -/
theorem lawZ_tail (t : ℝ) : lawZ ι {z | (t : EReal) < z} = ENNReal.ofReal (1 - FInf ι t) := by
  have hm : MeasurableSet {z : EReal | (t : EReal) < z} := measurableSet_Ioi
  rw [lawZ, Measure.add_apply, Measure.map_apply coe_meas hm, Measure.smul_apply,
    Measure.dirac_apply_of_mem (show (⊤ : EReal) ∈ {z | (t:EReal) < z} from EReal.coe_lt_top t),
    smul_eq_mul, mul_one]
  have : (fun x : ℝ => (x : EReal)) ⁻¹' {z | (t : EReal) < z} = Ioi t := by
    ext x; simp [EReal.coe_lt_coe_iff]
  rw [this, muInf_Ioi, ← ENNReal.ofReal_add (by linarith [FInf_le ι t 0,
      (show FInf ι t ≤ atomQ ι from ge_of_tendsto (atomQ_eq_lim_FInf ι)
        (eventually_atTop.mpr ⟨t, fun s hs => FInf_mono ι hs⟩))])
    (by linarith [atomQ_le_one ι])]
  congr 1; ring

/-! ### Moments of `Z` as Lebesgue integrals -/

/-- `2^{l z}` on `[0,∞]`, with `2^{l·∞} = ∞` for `l > 0` and `0` for `l ≤ 0`. -/
def powE (l : ℝ) (z : EReal) : ℝ≥0∞ :=
  if z = ⊤ then (if 0 < l then ⊤ else 0) else ENNReal.ofReal ((2:ℝ) ^ (l * z.toReal))

/-- `z ↦ z` as an element of `[0,∞]`. -/
def meanE (z : EReal) : ℝ≥0∞ := if z = ⊤ then ⊤ else ENNReal.ofReal z.toReal

theorem lintegral_lawZ (φ : EReal → ℝ≥0∞) :
    ∫⁻ z, φ z ∂(lawZ ι) = ∫⁻ x, φ (x : EReal) ∂(muInf ι) + ENNReal.ofReal (1 - atomQ ι) * φ ⊤ := by
  rw [lawZ, lintegral_add_measure, EReal.measurableEmbedding_coe.lintegral_map,
    lintegral_smul_measure, lintegral_dirac, smul_eq_mul]

/-- Layer cake for `muInf`. -/
theorem layer {g : ℝ → ℝ} (gi : ∀ t > 0, IntervalIntegrable g volume 0 t)
    (gnn : ∀ t, 0 < t → 0 ≤ g t) :
    ∫⁻ x, ENNReal.ofReal (∫ t in (0:ℝ)..x, g t) ∂(muInf ι) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((atomQ ι - FInf ι t) * g t) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (muInf ι) (f := id) (muInf_nonneg ι)
    aemeasurable_id gi ((ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun t ht => gnn t ht))
  simp only [id] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show {a : ℝ | t < a} = Ioi t from rfl, muInf_Ioi, ← ENNReal.ofReal_mul]
  have : FInf ι t ≤ atomQ ι := ge_of_tendsto (atomQ_eq_lim_FInf ι)
    (eventually_atTop.mpr ⟨t, fun s hs => FInf_mono ι hs⟩)
  linarith

theorem FInf_le_atomQ' (t : ℝ) : FInf ι t ≤ atomQ ι :=
  ge_of_tendsto (atomQ_eq_lim_FInf ι) (eventually_atTop.mpr ⟨t, fun s hs => FInf_mono ι hs⟩)

/-- `∫⁻_{t>0} ofReal(c·g t) = ∞` when `∫_0^N g → ∞` linearly. -/
theorem lint_gw_top {l c : ℝ} (hl : 0 < l) (hc : 0 < c) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (c * gw l t) = ⊤ := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ENNReal.eq_top_of_forall_nnreal_le fun r => ?_
  set N := (r:ℝ) / (c * (l * Real.log 2)) + 1
  have hN : 0 ≤ N := by positivity
  calc (r : ℝ≥0∞) ≤ ENNReal.ofReal (∫ t in Ioc 0 N, c * gw l t) := by
        rw [integral_const_mul, setIntegral_Ioc_gw l hN, mul_zero, Real.rpow_zero]
        rw [← ENNReal.ofReal_coe_nnreal]
        apply ENNReal.ofReal_le_ofReal
        have h1 := Real.add_one_le_exp (Real.log 2 * (l * N))
        rw [← rpow_two_eq] at h1
        have : (r:ℝ) ≤ c * (l * Real.log 2) * N := by
          simp only [N]; rw [mul_add, mul_div_cancel₀ _ (by positivity)]
          have : 0 < c * (l * Real.log 2) := by positivity
          linarith
        nlinarith
    _ = ∫⁻ t in Ioc 0 N, ENNReal.ofReal (c * gw l t) :=
        ofReal_integral_eq_lintegral_ofReal
          (((continuous_gw l).const_mul c).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
          ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ fun t _ =>
            mul_nonneg hc.le (gw_nonneg hl.le t)))
    _ ≤ _ := lintegral_mono_set Ioc_subset_Ioi_self

/-- **`α < 1`:** `E 2^{(1-α)Z} = zMomLaw`. -/
theorem moment_lt {α : ℝ} (hα : α < 1) :
    ∫⁻ z, powE (1 - α) z ∂(lawZ ι) = zMomLaw ι α := by
  have hl : 0 < 1 - α := by linarith
  set l := 1 - α
  have hq1 := atomQ_le_one ι
  rw [lintegral_lawZ]
  have hfin : ∫⁻ x, powE l (x : EReal) ∂(muInf ι) =
      ENNReal.ofReal (atomQ ι) + ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((atomQ ι - FInf ι t) * gw l t) := by
    rw [← layer ι (fun t _ => (continuous_gw l).intervalIntegrable _ _)
      (fun t _ => gw_nonneg hl.le t), ← muInf_univ, ← lintegral_one, ← lintegral_add_left' aemeasurable_const]
    refine lintegral_congr_ae ?_
    filter_upwards [muInf_nonneg ι] with x hx
    simp only [powE, EReal.coe_ne_top, if_false, EReal.toReal_coe, interval_gw, mul_zero,
      Real.rpow_zero]
    have : 1 ≤ (2:ℝ) ^ (l * x) := Real.one_le_rpow (by norm_num) (by positivity)
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (by linarith)]
    congr 1; ring
  rw [hfin, zMomLaw]
  simp only [powE, if_pos rfl, if_true, if_pos hl]
  rcases eq_or_lt_of_le hq1 with hq | hq
  · rw [hq, sub_self, ENNReal.ofReal_zero, zero_mul, add_zero, ENNReal.ofReal_one]
    congr 1
    refine setLIntegral_congr_fun measurableSet_Ioi fun t _ => by rw [mul_comm]
  · have hpos : 0 < ENNReal.ofReal (1 - atomQ ι) := ENNReal.ofReal_pos.mpr (by linarith)
    rw [ENNReal.mul_top hpos.ne', add_top]
    symm
    refine top_unique ?_
    rw [← lint_gw_top hl (show 0 < 1 - atomQ ι by linarith)]
    refine le_add_left (setLIntegral_mono' measurableSet_Ioi fun t _ => ?_)
    apply ENNReal.ofReal_le_ofReal
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (by linarith [FInf_le_atomQ' ι t]) (gw_nonneg hl.le t)

/-- **`α = 1`:** `E Z = zMeanLaw = L_∞`. -/
theorem moment_one : ∫⁻ z, meanE z ∂(lawZ ι) = zMeanLaw ι := by
  have hq1 := atomQ_le_one ι
  rw [lintegral_lawZ]
  have hfin : ∫⁻ x, meanE (x : EReal) ∂(muInf ι) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (atomQ ι - FInf ι t) := by
    have h := lintegral_eq_lintegral_meas_lt (muInf ι) (f := id) (muInf_nonneg ι) aemeasurable_id
    simp only [meanE, EReal.coe_ne_top, if_false, EReal.toReal_coe, id] at h ⊢
    rw [h]
    exact setLIntegral_congr_fun measurableSet_Ioi fun t _ => muInf_Ioi ι t
  rw [hfin, zMeanLaw]
  simp only [meanE, if_pos rfl, if_true]
  rcases eq_or_lt_of_le hq1 with hq | hq
  · rw [hq, sub_self, ENNReal.ofReal_zero, zero_mul, add_zero]
  · have hpos : 0 < ENNReal.ofReal (1 - atomQ ι) := ENNReal.ofReal_pos.mpr (by linarith)
    rw [ENNReal.mul_top hpos.ne', add_top]
    symm
    refine top_unique ?_
    calc ⊤ = ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 - atomQ ι) := by
          rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top hpos.ne']
      _ ≤ _ := setLIntegral_mono' measurableSet_Ioi fun t _ =>
          ENNReal.ofReal_le_ofReal (by linarith [FInf_le_atomQ' ι t])

theorem integral_gw_Ioi {l : ℝ} (hl : l < 0) : ∫ t in Ioi (0:ℝ), gw l t = -1 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h := integral_Ioi_of_hasDerivAt_of_tendsto (f := fun t => (2:ℝ) ^ (l * t)) (m := 0)
    ((Real.continuous_const_rpow (by norm_num : (2:ℝ) ≠ 0)).comp (continuous_const.mul continuous_id)).continuousWithinAt
    (fun t _ => hasDerivAt_pow2 l t) (integrableOn_gw hl) ?_
  · simpa using h
  · simp_rw [rpow_two_eq]
    refine Real.tendsto_exp_atBot.comp ?_
    refine (Tendsto.const_mul_atTop_of_neg (mul_neg_of_pos_of_neg hl2 hl) tendsto_id).congr
      fun t => ?_
    simp only [id]; ring

/-- **`α > 1`:** `E 2^{(1-α)Z} = zMomLawR` (a finite number). -/
theorem moment_gt {α : ℝ} (hα : 1 < α) :
    ∫⁻ z, powE (1 - α) z ∂(lawZ ι) = ENNReal.ofReal (zMomLawR ι α) := by
  have hl : 1 - α < 0 := by linarith
  set l := 1 - α
  have hq1 := atomQ_le_one ι
  have hq0 := atomQ_nonneg ι
  rw [lintegral_lawZ]
  simp only [powE, if_pos rfl, if_true, if_neg (not_lt.mpr hl.le), mul_zero, add_zero, EReal.coe_ne_top,
    if_false, EReal.toReal_coe]
  set g := fun t => -gw l t
  have hg0 : ∀ t, 0 ≤ g t := fun t => neg_nonneg.mpr (gw_nonpos hl.le t)
  have hgi : IntegrableOn g (Ioi 0) := (integrableOn_gw hl).neg
  set I := ∫ t in Ioi (0:ℝ), (atomQ ι - FInf ι t) * g t
  have hIi : IntegrableOn (fun t => (atomQ ι - FInf ι t) * g t) (Ioi 0) := by
    refine (hgi.bdd_mul (c := 1) ((measurable_const.sub (FInf_meas ι)).aestronglyMeasurable)
      (Eventually.of_forall fun t => ?_))
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith [FInf_nonneg ι t, FInf_le_atomQ' ι t]
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi fun t _ =>
    mul_nonneg (by linarith [FInf_le_atomQ' ι t]) (hg0 t)
  have hlay := layer ι (g := g) (fun t _ => ((continuous_gw l).neg).intervalIntegrable _ _)
    (fun t _ => hg0 t)
  rw [← ofReal_integral_eq_lintegral_ofReal hIi ((ae_restrict_iff' measurableSet_Ioi).mpr
    (ae_of_all _ fun t _ => mul_nonneg (by linarith [FInf_le_atomQ' ι t]) (hg0 t)))] at hlay
  have hsum : ∫⁻ x, ENNReal.ofReal ((2:ℝ) ^ (l * x)) ∂(muInf ι) + ENNReal.ofReal I =
      ENNReal.ofReal (atomQ ι) := by
    rw [← hlay, ← muInf_univ, ← lintegral_one, ← lintegral_add_left' (by
      exact (ENNReal.measurable_ofReal.comp ((Real.continuous_const_rpow (by norm_num :
        (2:ℝ) ≠ 0)).comp (continuous_const.mul continuous_id)).measurable).aemeasurable)]
    refine lintegral_congr_ae ?_
    filter_upwards [muInf_nonneg ι] with x hx
    have h1 : (2:ℝ) ^ (l * x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
      (mul_nonpos_of_nonpos_of_nonneg hl.le hx)
    have h0 : 0 ≤ (2:ℝ) ^ (l * x) := by positivity
    have e : ∫ t in (0:ℝ)..x, g t = 1 - (2:ℝ) ^ (l * x) := by
      simp only [g, intervalIntegral.integral_neg, interval_gw, mul_zero, Real.rpow_zero]; ring
    rw [e, ← ENNReal.ofReal_add h0 (by linarith)]
    simp
  have hIq : I ≤ atomQ ι := by
    have := le_of_add_le_right hsum.le
    exact (ENNReal.ofReal_le_ofReal_iff hq0).mp this
  have hval : zMomLawR ι α = atomQ ι - I := by
    unfold zMomLawR
    have e1 : ∫ t in Ioi (0:ℝ), gw l t * (1 - FInf ι t) =
        ∫ t in Ioi (0:ℝ), ((1 - atomQ ι) * gw l t - (atomQ ι - FInf ι t) * g t) := by
      congr 1; funext t; simp only [g]; ring
    rw [e1, integral_sub ((integrableOn_gw hl).const_mul _) hIi, integral_const_mul,
      integral_gw_Ioi hl]
    ring
  rw [hval]
  rw [ENNReal.ofReal_sub _ hI0]
  exact ENNReal.eq_sub_of_add_eq ENNReal.ofReal_ne_top hsum

/-- `R_α(Z)` computed from the moments of the measure `lawZ` (Lebesgue integrals). -/
def RZmeas (α : ℝ) : ℝ≥0∞ :=
  if α = 1 then ∫⁻ z, meanE z ∂(lawZ ι)
  else if α < 1 then
    (if ∫⁻ z, powE (1 - α) z ∂(lawZ ι) = ⊤ then ⊤
     else ENNReal.ofReal (Real.logb 2 (∫⁻ z, powE (1 - α) z ∂(lawZ ι)).toReal / (1 - α)))
  else
    (if (∫⁻ z, powE (1 - α) z ∂(lawZ ι)).toReal ≤ 0 then ⊤
     else ENNReal.ofReal (Real.logb 2 (∫⁻ z, powE (1 - α) z ∂(lawZ ι)).toReal / (1 - α)))

theorem zMomLawR_nonneg {α : ℝ} (hα : 1 < α) : 0 ≤ zMomLawR ι α :=
  ge_of_tendsto' (zMomLawR_tendsto ι hα) fun n => (zMoment_pos _ _).le

/-- **`R_α(Z)` of the measure equals `sup_n R_α(Z_n)`**, for every `α > 0`. -/
theorem RZmeas_eq {α : ℝ} (hα : 0 < α) : RZmeas ι α = RZ ι α := by
  rw [← RZlaw_eq ι hα]
  unfold RZmeas RZlaw
  by_cases h1 : α = 1
  · simp only [if_pos h1]; exact moment_one ι
  simp only [if_neg h1]
  by_cases h2 : α < 1
  · simp only [if_pos h2, moment_lt ι h2]
  · simp only [if_neg h2]
    have hgt : 1 < α := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm h1)
    rw [moment_gt ι hgt, ENNReal.toReal_ofReal (zMomLawR_nonneg ι hgt)]

/-- **Main theorem with `R_α(Z)` from the actual law of `Z`.** -/
theorem one_seed_all_orders_meas (hU : Nonempty (OrdSource ι)) :
    ∃ S : CountableSeed ι, S.Exact ∧
      (∀ α : ℝ, 0 < α →
        RZmeas ι α ≤ Oα ι α ∧ Oα ι α ≤ Cα ι α ∧ Cα ι α ≤ H α S.weight ∧
          H α S.weight ≤ RZmeas ι α + ENNReal.ofReal (dA α)) ∧
      Hinf S.weight = Cinf ι ∧ Cinf ι = Oinf ι := by
  obtain ⟨S, hS, hall, h2⟩ := one_seed_all_orders hU
  exact ⟨S, hS, fun α hα => by rw [RZmeas_eq ι hα]; exact hall α hα, h2⟩

end CausalSpectrum.RenyiInf

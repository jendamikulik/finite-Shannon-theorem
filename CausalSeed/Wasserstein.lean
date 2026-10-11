/-
The Wasserstein-1 distance on the real line, defined by optimal transport.

`W1 μ ν` is the infimum of `E|X - Y|` over all couplings of `μ` and `ν`, with values in
`[0, ∞]` (no moment assumption is needed in this form). For probability measures,
`W1 μ ν = ∫ |F_μ - F_ν|`: every coupling costs at least the CDF distance, and the
quantile coupling `(Q_μ(U), Q_ν(U))`, `U` uniform on `(0,1)`, attains it.
-/
import Mathlib.Probability.CDF
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum.OT

/-- `γ` is a coupling of `μ` and `ν`. -/
structure IsCoupling (μ ν : Measure ℝ) (γ : Measure (ℝ × ℝ)) : Prop where
  fst : γ.map Prod.fst = μ
  snd : γ.map Prod.snd = ν

/-- Transport cost `E|X - Y|` of a coupling. -/
def cost (γ : Measure (ℝ × ℝ)) : ℝ≥0∞ := ∫⁻ p, ENNReal.ofReal |p.1 - p.2| ∂γ

/-- The Wasserstein-1 distance: infimum of the transport cost over couplings. -/
def W1 (μ ν : Measure ℝ) : ℝ≥0∞ := ⨅ (γ : Measure (ℝ × ℝ)) (_ : IsCoupling μ ν γ), cost γ

/-- The CDF distance `∫ |F_μ - F_ν|`. -/
def cdfDist (μ ν : Measure ℝ) : ℝ≥0∞ := ∫⁻ t, ENNReal.ofReal |cdf μ t - cdf ν t|

/-! ## The length identity `|x - y| = ∫ 1{t between x and y} dt` -/

/-- Points `t` separating `x` and `y`. -/
def D (x y : ℝ) : Set ℝ := Ico x y ∪ Ico y x

theorem volume_D (x y : ℝ) : volume (D x y) = ENNReal.ofReal |x - y| := by
  rcases le_total x y with h | h
  · rw [D, Ico_eq_empty_of_le h, union_empty, Real.volume_Ico, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr h)]
  · rw [D, Ico_eq_empty_of_le h, empty_union, Real.volume_Ico, abs_of_nonneg (sub_nonneg.mpr h)]

theorem mem_D {x y t : ℝ} : t ∈ D x y ↔ (x ≤ t ∧ ¬ y ≤ t) ∨ (y ≤ t ∧ ¬ x ≤ t) := by
  simp [D, not_le]

theorem measurableSet_D2 {α : Type*} [MeasurableSpace α] {f g : α → ℝ} (hf : Measurable f)
    (hg : Measurable g) : MeasurableSet {q : α × ℝ | q.2 ∈ D (f q.1) (g q.1)} := by
  simp only [mem_D, ofPred_or, ofPred_and]
  refine ((measurableSet_le (hf.comp measurable_fst) measurable_snd).inter
    (measurableSet_le (hg.comp measurable_fst) measurable_snd).compl).union
    ((measurableSet_le (hg.comp measurable_fst) measurable_snd).inter
    (measurableSet_le (hf.comp measurable_fst) measurable_snd).compl)

/-- `∫ |f - g| dρ = ∫_t ρ{a : t ∈ D (f a) (g a)} dt` (Tonelli). -/
theorem lintegral_abs_eq {α : Type*} [MeasurableSpace α] (ρ : Measure α) [SFinite ρ]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, ENNReal.ofReal |f a - g a| ∂ρ = ∫⁻ t, ρ {a | t ∈ D (f a) (g a)} := by
  have hS := measurableSet_D2 hf hg
  have h1 : ∀ a, ENNReal.ofReal |f a - g a| =
      ∫⁻ t, (({q : α × ℝ | q.2 ∈ D (f q.1) (g q.1)}).indicator 1 (a, t)) := by
    intro a
    rw [← volume_D, ← lintegral_indicator_one (measurableSet_D2 hf hg |>.preimage
      (measurable_prodMk_left (m := inferInstance)) |> fun h => by simpa using h)]
    rfl
  have h2 : ∀ t, ρ {a | t ∈ D (f a) (g a)} =
      ∫⁻ a, (({q : α × ℝ | q.2 ∈ D (f q.1) (g q.1)}).indicator 1 (a, t)) ∂ρ := by
    intro t
    have hm : MeasurableSet {a | t ∈ D (f a) (g a)} := by
      have := hS.preimage (measurable_prodMk_right (m := inferInstance) (y := t))
      simpa using this
    rw [← lintegral_indicator_one hm]
    rfl
  simp_rw [h1, h2]
  exact lintegral_lintegral_swap ((measurable_one.indicator hS).aemeasurable)

/-! ## Every coupling costs at least the CDF distance -/

theorem cdfDist_le_cost {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {γ : Measure (ℝ × ℝ)} (hγ : IsCoupling μ ν γ) : cdfDist μ ν ≤ cost γ := by
  have hprob : IsProbabilityMeasure γ := by
    constructor
    have := congrArg (fun m : Measure ℝ => m univ) hγ.fst
    simpa [Measure.map_apply measurable_fst MeasurableSet.univ] using this
  rw [cost, lintegral_abs_eq γ measurable_fst measurable_snd, cdfDist]
  refine lintegral_mono fun t => ?_
  set A : Set (ℝ × ℝ) := {p | p.1 ≤ t}
  set B : Set (ℝ × ℝ) := {p | p.2 ≤ t}
  have hA : MeasurableSet A := measurableSet_le measurable_fst measurable_const
  have hB : MeasurableSet B := measurableSet_le measurable_snd measurable_const
  have hFA : cdf μ t = γ.real A := by
    rw [cdf_eq_real, ← hγ.fst, measureReal_def, measureReal_def,
      Measure.map_apply measurable_fst measurableSet_Iic]; rfl
  have hFB : cdf ν t = γ.real B := by
    rw [cdf_eq_real, ← hγ.snd, measureReal_def, measureReal_def,
      Measure.map_apply measurable_snd measurableSet_Iic]; rfl
  have hset : {p : ℝ × ℝ | t ∈ D p.1 p.2} = (A \ B) ∪ (B \ A) := by
    ext p; simp [mem_D, A, B]
  have hdisj : Disjoint (A \ B) (B \ A) :=
    disjoint_sdiff_sdiff
  rw [hset, measure_union hdisj (hB.diff hA)]
  have e1 : γ.real A ≤ γ.real (A \ B) + γ.real B := by
    calc γ.real A ≤ γ.real ((A \ B) ∪ B) := measureReal_mono (by intro p hp; by_cases h : p ∈ B <;> simp_all)
      _ ≤ _ := measureReal_union_le _ _
  have e2 : γ.real B ≤ γ.real (B \ A) + γ.real A := by
    calc γ.real B ≤ γ.real ((B \ A) ∪ A) := measureReal_mono (by intro p hp; by_cases h : p ∈ A <;> simp_all)
      _ ≤ _ := measureReal_union_le _ _
  rw [hFA, hFB, ← ofReal_measureReal (s := A \ B), ← ofReal_measureReal (s := B \ A),
    ← ENNReal.ofReal_add measureReal_nonneg measureReal_nonneg]
  have n1 : 0 ≤ γ.real (A \ B) := measureReal_nonneg
  have n2 : 0 ≤ γ.real (B \ A) := measureReal_nonneg
  exact ENNReal.ofReal_le_ofReal (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩)

theorem cdfDist_le_W1 (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    cdfDist μ ν ≤ W1 μ ν :=
  le_iInf₂ fun _ hγ => cdfDist_le_cost hγ


/-! ## The quantile coupling -/

section Quantile
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- The quantile function `Q(u) = inf {t : u ≤ F(t)}` on `(0,1)`, and `0` elsewhere. -/
def quantile (u : ℝ) : ℝ := if u ∈ Ioo (0:ℝ) 1 then sInf {t | u ≤ cdf μ t} else 0

variable {μ}

theorem quantile_set_nonempty {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : {t | u ≤ cdf μ t}.Nonempty := by
  obtain ⟨t, ht⟩ := ((tendsto_order.1 (tendsto_cdf_atTop μ)).1 u hu.2).exists
  exact ⟨t, ht.le⟩

theorem quantile_set_bdd {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) : BddBelow {t | u ≤ cdf μ t} := by
  obtain ⟨t0, ht0⟩ := (eventually_atBot.1 ((tendsto_order.1 (tendsto_cdf_atBot μ)).2 u hu.1))
  refine ⟨t0, fun t ht => ?_⟩
  by_contra h
  push Not at h
  have := ht0 t h.le
  exact absurd ht (not_le.mpr this)

/-- The Galois connection `Q(u) ≤ t ↔ u ≤ F(t)` for `u ∈ (0,1)`. -/
theorem quantile_le_iff {u : ℝ} (hu : u ∈ Ioo (0:ℝ) 1) (t : ℝ) :
    quantile μ u ≤ t ↔ u ≤ cdf μ t := by
  rw [quantile, if_pos hu]
  constructor
  · intro h
    set q := sInf {t | u ≤ cdf μ t}
    have hq : u ≤ cdf μ q := by
      have hT : Tendsto (cdf μ) (𝓝[>] q) (𝓝 (cdf μ q)) :=
        ((cdf μ).right_continuous q).tendsto.mono_left (nhdsWithin_mono _ Ioi_subset_Ici_self)
      refine ge_of_tendsto hT (eventually_nhdsWithin_of_forall fun s hs => ?_)
      obtain ⟨x, hx, hxs⟩ := (csInf_lt_iff (quantile_set_bdd hu) (quantile_set_nonempty hu)).1 hs
      exact le_trans hx (monotone_cdf μ hxs.le)
    exact le_trans hq (monotone_cdf μ h)
  · intro h
    exact csInf_le (quantile_set_bdd hu) h

theorem measurable_quantile : Measurable (quantile μ) := by
  refine measurable_of_Iic fun t => ?_
  have : quantile μ ⁻¹' Iic t =
      (Ioo (0:ℝ) 1 ∩ Iic (cdf μ t)) ∪ ((Ioo (0:ℝ) 1)ᶜ ∩ {_u | (0:ℝ) ≤ t}) := by
    ext u
    by_cases hu : u ∈ Ioo (0:ℝ) 1
    · simp [hu, quantile_le_iff hu]
    · rw [mem_preimage, mem_Iic, quantile, if_neg hu]; simp [hu]
  rw [this]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_Ioo.compl.inter (MeasurableSet.const _))

/-- `vol((0,1) ∩ (-∞, c]) = c` for `c ∈ [0,1]`. -/
theorem volume_unit_Iic {c : ℝ} (_h0 : 0 ≤ c) (h1 : c ≤ 1) :
    volume (Ioo (0:ℝ) 1 ∩ Iic c) = ENNReal.ofReal c := by
  apply le_antisymm
  · calc volume (Ioo (0:ℝ) 1 ∩ Iic c) ≤ volume (Ioc 0 c) :=
          measure_mono (by intro u hu; exact ⟨hu.1.1, hu.2⟩)
      _ = _ := by simp
  · calc ENNReal.ofReal c = volume (Ioo 0 c) := by simp
      _ ≤ _ := measure_mono (by intro u hu; exact ⟨⟨hu.1, lt_of_lt_of_le hu.2 h1⟩, hu.2.le⟩)

/-- The quantile transform of the uniform law on `(0,1)` is `μ`. -/
theorem map_quantile : (volume.restrict (Ioo (0:ℝ) 1)).map (quantile μ) = μ := by
  have : IsFiniteMeasure (volume.restrict (Ioo (0:ℝ) 1)) :=
    ⟨by simp⟩
  refine (Measure.ext_of_Iic _ _ fun t => ?_)
  rw [Measure.map_apply measurable_quantile measurableSet_Iic,
    Measure.restrict_apply (measurable_quantile measurableSet_Iic), ← ofReal_cdf]
  have : quantile μ ⁻¹' Iic t ∩ Ioo 0 1 = Ioo (0:ℝ) 1 ∩ Iic (cdf μ t) := by
    ext u; constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, (quantile_le_iff h2 t).1 h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨(quantile_le_iff h2 t).2 h1, h2⟩
  rw [this, volume_unit_Iic (cdf_nonneg μ t) (cdf_le_one μ t)]

end Quantile

variable {μ ν : Measure ℝ} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The quantile (comonotone) coupling. -/
def qCoupling (μ ν : Measure ℝ) : Measure (ℝ × ℝ) :=
  (volume.restrict (Ioo (0:ℝ) 1)).map (fun u => (quantile μ u, quantile ν u))

theorem measurable_qpair : Measurable (fun u => (quantile μ u, quantile ν u)) :=
  measurable_quantile.prodMk measurable_quantile

theorem qCoupling_isCoupling : IsCoupling μ ν (qCoupling μ ν) where
  fst := by
    rw [qCoupling, Measure.map_map measurable_fst measurable_qpair]; exact map_quantile
  snd := by
    rw [qCoupling, Measure.map_map measurable_snd measurable_qpair]; exact map_quantile

theorem volume_unit_sep {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1) :
    volume (Ioo (0:ℝ) 1 ∩ {u | (u ≤ a ∧ ¬ u ≤ b) ∨ (u ≤ b ∧ ¬ u ≤ a)}) =
      ENNReal.ofReal |a - b| := by
  rcases le_total a b with h | h
  · have hs : {u : ℝ | (u ≤ a ∧ ¬ u ≤ b) ∨ (u ≤ b ∧ ¬ u ≤ a)} = Ioc a b := by
      ext u; simp only [mem_ofPred_eq, mem_Ioc, not_le]; constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩); · linarith
        · exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩; exact Or.inr ⟨h2, h1⟩
    rw [hs, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h)]
    apply le_antisymm
    · calc _ ≤ volume (Ioc a b) := measure_mono inter_subset_right
        _ = _ := by simp
    · calc ENNReal.ofReal (b - a) = volume (Ioo a b) := by simp
        _ ≤ _ := measure_mono (by
          intro u hu; exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, hu.1, hu.2.le⟩)
  · have hs : {u : ℝ | (u ≤ a ∧ ¬ u ≤ b) ∨ (u ≤ b ∧ ¬ u ≤ a)} = Ioc b a := by
      ext u; simp only [mem_ofPred_eq, mem_Ioc, not_le]; constructor
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩); · exact ⟨h2, h1⟩
        · linarith
      · rintro ⟨h1, h2⟩; exact Or.inl ⟨h2, h1⟩
    rw [hs, abs_of_nonneg (sub_nonneg.mpr h)]
    apply le_antisymm
    · calc _ ≤ volume (Ioc b a) := measure_mono inter_subset_right
        _ = _ := by simp
    · calc ENNReal.ofReal (a - b) = volume (Ioo b a) := by simp
        _ ≤ _ := measure_mono (by
          intro u hu; exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, hu.1, hu.2.le⟩)

/-- The quantile coupling costs exactly the CDF distance. -/
theorem cost_qCoupling : cost (qCoupling μ ν) = cdfDist μ ν := by
  rw [cost, qCoupling, lintegral_map (by fun_prop) measurable_qpair,
    lintegral_abs_eq _ measurable_quantile measurable_quantile, cdfDist]
  refine lintegral_congr fun t => ?_
  have hm : MeasurableSet {a : ℝ | t ∈ D (quantile μ a) (quantile ν a)} := by
    have := (measurableSet_D2 (measurable_quantile (μ := μ)) (measurable_quantile (μ := ν))).preimage
      (measurable_prodMk_right (m := inferInstance) (y := t))
    simpa using this
  rw [Measure.restrict_apply hm, inter_comm]
  have : Ioo (0:ℝ) 1 ∩ {a | t ∈ D (quantile μ a) (quantile ν a)} =
      Ioo (0:ℝ) 1 ∩ {u | (u ≤ cdf μ t ∧ ¬ u ≤ cdf ν t) ∨ (u ≤ cdf ν t ∧ ¬ u ≤ cdf μ t)} := by
    ext u
    constructor
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      simp only [mem_ofPred_eq, mem_D, quantile_le_iff hu] at h ⊢; exact h
    · rintro ⟨hu, h⟩
      refine ⟨hu, ?_⟩
      simp only [mem_ofPred_eq, mem_D, quantile_le_iff hu] at h ⊢; exact h
  rw [this, volume_unit_sep (cdf_nonneg μ t) (cdf_le_one μ t) (cdf_nonneg ν t) (cdf_le_one ν t)]

/-- **`W1 = ∫ |F_μ - F_ν|`** for probability measures on `ℝ`. -/
theorem W1_eq_cdfDist (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    W1 μ ν = cdfDist μ ν :=
  le_antisymm ((iInf₂_le _ qCoupling_isCoupling).trans cost_qCoupling.le) (cdfDist_le_W1 μ ν)

/-- The quantile coupling is optimal. -/
theorem qCoupling_optimal (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IsCoupling μ ν (qCoupling μ ν) ∧ cost (qCoupling μ ν) = W1 μ ν :=
  ⟨qCoupling_isCoupling, by rw [cost_qCoupling, W1_eq_cdfDist]⟩

end CausalSpectrum.OT

/-
The finite-tree Wasserstein identity with the optimal-transport `W₁`.

For an exact finite seed with positive atoms, the law of its information `J` and the
envelope law (the probability measure with CDF `F*`) are at Wasserstein-1 distance
exactly `H(S) - L(T)` (bits).
-/
import CausalSeed.Gap
import CausalSeed.SqrtUniversality
import CausalSeed.RenyiLimitMeasure
import CausalSeed.Wasserstein

noncomputable section
open Classical MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum

/-- The law of the information `J = -log₂ w` of a finite seed. -/
def seedLaw {T : Tree} (atoms : List (Atom T)) : Measure ℝ :=
  (atoms.map fun a => ENNReal.ofReal a.1 • Measure.dirac (infoMass a.1)).sum

theorem seedLaw_apply {T : Tree} : ∀ (atoms : List (Atom T)), (∀ a ∈ atoms, 0 < a.1) →
    ∀ {A : Set ℝ}, MeasurableSet A → seedLaw atoms A = ENNReal.ofReal
      (atoms.map fun a => if infoMass a.1 ∈ A then a.1 else 0).sum
  | [], _, A, _ => by simp [seedLaw]
  | a :: rest, hpos, A, hA => by
      have ih := seedLaw_apply rest (fun b hb => hpos b (List.mem_cons_of_mem _ hb)) hA
      have ha : 0 < a.1 := hpos a (List.mem_cons_self ..)
      have hnn : 0 ≤ (rest.map fun a => if infoMass a.1 ∈ A then a.1 else 0).sum :=
        List.sum_nonneg (by
          intro x hx; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
          have := hpos b (List.mem_cons_of_mem _ hb); split_ifs <;> linarith)
      simp only [seedLaw, List.map_cons, List.sum_cons, Measure.add_apply, Measure.smul_apply,
        Measure.dirac_apply' _ hA, smul_eq_mul] at ih ⊢
      have e : ENNReal.ofReal a.1 * A.indicator 1 (infoMass a.1) =
          ENNReal.ofReal (if infoMass a.1 ∈ A then a.1 else 0) := by
        by_cases h : infoMass a.1 ∈ A <;> simp [h]
      rw [ih, e, ← ENNReal.ofReal_add (by split_ifs <;> linarith) hnn]

theorem isProb_seedLaw {T : Tree} {atoms : List (Atom T)} (hpos : ∀ a ∈ atoms, 0 < a.1)
    (htot : totalWeight atoms = 1) : IsProbabilityMeasure (seedLaw atoms) :=
  ⟨by rw [seedLaw_apply atoms hpos MeasurableSet.univ]; simpa [totalWeight] using
      congrArg ENNReal.ofReal htot⟩

theorem cdf_seedLaw {T : Tree} {atoms : List (Atom T)} (hpos : ∀ a ∈ atoms, 0 < a.1)
    (htot : totalWeight atoms = 1) (t : ℝ) : cdf (seedLaw atoms) t = seedCDF atoms t := by
  haveI := isProb_seedLaw hpos htot
  have hnn : 0 ≤ seedCDF atoms t := List.sum_nonneg (by
    intro x hx; obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hx
    have := hpos b hb; split_ifs <;> linarith)
  rw [← ENNReal.ofReal_eq_ofReal_iff (cdf_nonneg _ _) hnn, ofReal_cdf,
    seedLaw_apply atoms hpos measurableSet_Iic]
  rfl

theorem Fstar_atTop (T : Tree) : Tendsto (Fstar T) atTop (𝓝 1) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop ((infoValues T)[(infoValues T).length - 1]'(by
      have h := infoValues_length_pos T; omega))] with t ht
  exact (le_antisymm (RenyiInf.Fstar_le_one T t)
    ((Fstar_last T).symm.le.trans (Fstar_mono T ht))).symm

theorem Fstar_atBot (T : Tree) : Tendsto (Fstar T) atBot (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_lt_atBot 0] with t ht
  exact (Kernel.Fstar_neg T ht).symm

/-- `F*` as a Stieltjes function. -/
def FstarS (T : Tree) : StieltjesFunction ℝ where
  toFun := Fstar T
  mono' := Fstar_mono T
  right_continuous' := RenyiInf.Fstar_rightCont T

/-- The envelope law: the probability measure with CDF `F*`. -/
def envLaw (T : Tree) : Measure ℝ := (FstarS T).measure

theorem cdf_envLaw (T : Tree) : (cdf (envLaw T) : ℝ → ℝ) = Fstar T := by
  rw [envLaw, cdf_measure_stieltjesFunction _ (Fstar_atBot T) (Fstar_atTop T)]; rfl

instance (T : Tree) : IsProbabilityMeasure (envLaw T) :=
  ⟨by rw [envLaw, (FstarS T).measure_univ (Fstar_atBot T) (Fstar_atTop T)]; simp⟩

/-- **Wasserstein identity, optimal-transport form.** For an exact finite seed with
positive atoms of total mass one, `W₁(law of J, envelope law) = H(S) - L(T)` (bits). -/
theorem wasserstein_gap_W1 {T : Tree} {atoms : List (Atom T)}
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    haveI := isProb_seedLaw hpos htot
    OT.W1 (seedLaw atoms) (envLaw T) = ENNReal.ofReal (seedShannon atoms - envelopeMean T) := by
  haveI := isProb_seedLaw hpos htot
  rw [OT.W1_eq_cdfDist, OT.cdfDist, ← wasserstein_gap hexact hpos hle htot,
    ofReal_integral_eq_lintegral_ofReal
      ((integrableOn_cdfGap atoms hpos hle htot).abs)
      (Eventually.of_forall fun _ => abs_nonneg _)]
  have hae : ∀ᵐ t ∂(volume : Measure ℝ),
      ENNReal.ofReal |cdf (seedLaw atoms) t - cdf (envLaw T) t| =
        (Ioi (0:ℝ)).indicator (fun t => ENNReal.ofReal |Fstar T t - seedCDF atoms t|) t := by
    have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [ae_iff]; simp
    filter_upwards [h0] with t ht
    rw [cdf_seedLaw hpos htot, cdf_envLaw, abs_sub_comm]
    rcases lt_or_gt_of_ne ht with h | h
    · rw [indicator_of_notMem (by simpa using h.le), Kernel.seedCDF_neg atoms hpos hle h,
        Kernel.Fstar_neg T h]; simp
    · rw [indicator_of_mem (show t ∈ Ioi (0:ℝ) from h)]
  rw [lintegral_congr_ae hae, lintegral_indicator measurableSet_Ioi]

end CausalSpectrum

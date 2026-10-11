/-
Atomic capacity: ordinary-source converse and attainment by the constructed causal measure.
Atomic mass is the sum of singleton masses, including on uncountable spaces.
-/
import CausalSeed.MeasureCompletion

noncomputable section
open Classical MeasureTheory Finset
open scoped ENNReal
namespace CausalSpectrum
namespace Completion

def atomicMass {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) : ℝ≥0∞ :=
  ∑' x : Ω, μ {x}

abbrev Transcript (ι : ITree) (n : ℕ) (π : Policy (trunc ι n [])) :=
  {ℓ : Leaf (trunc ι n []) // CompatiblePolicy ℓ π}

/- No causal compatibility between different readouts is assumed here. -/
structure OrdinarySource (ι : ITree) (Ω : Type*) [MeasurableSpace Ω]
    (μ : Measure Ω) where
  read : ∀ n (π : Policy (trunc ι n [])), Ω → Transcript ι n π
  measurable_fiber : ∀ n π ℓ, MeasurableSet (read n π ⁻¹' {ℓ})
  exact_fiber : ∀ n π ℓ,
    μ (read n π ⁻¹' {ℓ}) = ENNReal.ofReal (leafMass ℓ.val)

theorem ordinary_finite_bound {ι : ITree} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (R : OrdinarySource ι Ω μ) (A : Finset Ω)
    (n : ℕ) (π : Policy (trunc ι n [])) :
    μ (A : Set Ω) ≤ ENNReal.ofReal (topMass (trunc ι n []) π A.card) := by
  let D : Finset (Transcript ι n π) := A.image (R.read n π)
  let E : Finset (Leaf (trunc ι n [])) := D.image Subtype.val
  have hsub : (A : Set Ω) ⊆ R.read n π ⁻¹' (D : Set (Transcript ι n π)) := by
    intro x hx
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  have hcard : E.card ≤ A.card :=
    (Finset.card_image_le).trans (Finset.card_image_le)
  have hcompat : ∀ ℓ ∈ E, CompatiblePolicy ℓ π := by
    intro ℓ hℓ
    obtain ⟨z,_,rfl⟩ := Finset.mem_image.mp hℓ
    exact z.property
  have hsum : ∑ ℓ ∈ D, leafMass ℓ.val = ∑ ℓ ∈ E, leafMass ℓ := by
    have hinj : Set.InjOn Subtype.val (D : Set (Transcript ι n π)) := by
      intro x _hx y _hy hxy
      exact Subtype.ext hxy
    simpa [E] using (Finset.sum_image (f := fun ℓ : Leaf (trunc ι n []) => leafMass ℓ) hinj).symm
  calc
    μ (A : Set Ω) ≤ μ (R.read n π ⁻¹' (D : Set (Transcript ι n π))) :=
      measure_mono hsub
    _ = ∑ ℓ ∈ D, μ (R.read n π ⁻¹' {ℓ}) :=
      (sum_measure_preimage_singleton D (fun ℓ _ => R.measurable_fiber n π ℓ)).symm
    _ = ∑ ℓ ∈ D, ENNReal.ofReal (leafMass ℓ.val) := by
      apply Finset.sum_congr rfl
      intro ℓ _
      exact R.exact_fiber n π ℓ
    _ = ENNReal.ofReal (∑ ℓ ∈ D, leafMass ℓ.val) := by
      rw [ENNReal.ofReal_sum_of_nonneg]
      intro ℓ _
      exact (leafMass_pos ℓ.val).le
    _ = ENNReal.ofReal (∑ ℓ ∈ E, leafMass ℓ) := congrArg ENNReal.ofReal hsum
    _ ≤ ENNReal.ofReal (topMass (trunc ι n []) π A.card) :=
      ENNReal.ofReal_le_ofReal (topMass_le_of_set π A.card hcard hcompat)

theorem ordinary_finite_uniform {ι : ITree} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (R : OrdinarySource ι Ω μ)
    (A : Finset Ω) : μ (A : Set Ω) ≤ ENNReal.ofReal (atomA ι A.card) := by
  have hreal : (μ (A : Set Ω)).toReal ≤ atomA ι A.card := by
    apply le_csInf (atomA_nonempty ι A.card)
    rintro t ⟨n,π,rfl⟩
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (ordinary_finite_bound μ R A n π)
    simpa [ENNReal.toReal_ofReal (topMass_nonneg _ _ _)] using hh
  have hh := ENNReal.ofReal_le_ofReal hreal
  simpa [ENNReal.ofReal_toReal (measure_ne_top μ (A : Set Ω))] using hh

theorem ordinary_atomic_upper {ι : ITree} {Ω : Type*} [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : OrdinarySource ι Ω μ) : atomicMass μ ≤ ENNReal.ofReal (atomQ ι) := by
  rw [atomicMass, ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro A
  rw [sum_measure_singleton]
  exact (ordinary_finite_uniform μ R A).trans
    (ENNReal.ofReal_le_ofReal (atomA_le_atomQ ι A.card))

def policyRead (ι : ITree) (n : ℕ) (π : Policy (trunc ι n []))
    (s : IStrategy ι) : Transcript ι n π :=
  ⟨run (restrict ι n [] s) π, run_compatible_policy _ _⟩

theorem policyRead_fiber (ι : ITree) (n : ℕ) (π : Policy (trunc ι n []))
    (ℓ : Transcript ι n π) :
    policyRead ι n π ⁻¹' {ℓ} = cylinder ι (truncPath ι n [] ℓ.val) := by
  ext s
  have hh : iAgree ι s (truncPath ι n [] ℓ.val) ↔
      CompatibleStrategy ℓ.val (restrict ι n [] s) := by
    unfold iAgree
    rw [truncPath_length, ← leafPath_eq_truncPath, stratAgrees_iff_compat]
  simpa only [Set.mem_preimage, Set.mem_singleton_iff, policyRead,
    Subtype.ext_iff, run_eq_iff, ℓ.property, and_true,
    cylinder, Set.mem_setOf_eq] using hh.symm

def sourceOfCylinders (ι : ITree) (μ : Measure (IStrategy ι))
    (hexact : ∀ h, μ (cylinder ι h) = ENNReal.ofReal (pathMass ι h)) :
    OrdinarySource ι (IStrategy ι) μ where
  read := policyRead ι
  measurable_fiber := by
    intro n π ℓ
    rw [policyRead_fiber]
    exact measurable_cylinder ι _
  exact_fiber := by
    intro n π ℓ
    rw [policyRead_fiber, hexact, pathMass_leaf]

theorem atomMeasure_atomicMass (ι : ITree) :
    atomicMass (atomMeasure ι) = ENNReal.ofReal (atomQ ι) := by
  unfold atomicMass atomMeasure
  simp only [Measure.sum_apply _ (measurableSet_singleton _),
    Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_comm]
  have ht : ∀ i, (∑' s : IStrategy ι,
      ENNReal.ofReal (diagWeight ι i) * Measure.dirac (capStrat ι i) {s}) =
        ENNReal.ofReal (diagWeight ι i) := by
    intro i
    rw [tsum_eq_single (capStrat ι i)]
    · simp
    · intro s hs
      simp [Measure.dirac_apply, hs, Ne.symm hs]
  simp_rw [ht]
  rw [← ENNReal.ofReal_tsum_of_nonneg (diagWeight_nonneg ι) (diag_summable ι),
    diagMass_eq_tsum_atomQ]

theorem fullMeasure_atomicMass (ι : ITree) :
    atomicMass (fullMeasure ι) = ENNReal.ofReal (atomQ ι) := by
  apply le_antisymm
  · exact ordinary_atomic_upper (fullMeasure ι)
      (sourceOfCylinders ι _ (fullMeasure_cylinder ι))
  · rw [← atomMeasure_atomicMass ι]
    apply ENNReal.tsum_le_tsum
    intro s
    change atomMeasure ι {s} ≤
      (atomMeasure ι + ENNReal.ofReal (resMass ι []) • residualMeasure ι) {s}
    rw [Measure.add_apply]
    exact le_add_right le_rfl

/- The main attainment theorem: an actual probability on strategies,
   all finite cylinder laws exact, and atomic mass exactly q. -/
theorem causal_atomic_capacity_attained (ι : ITree) :
    ∃ μ : Measure (IStrategy ι), IsProbabilityMeasure μ ∧
      (∀ h, μ (cylinder ι h) = ENNReal.ofReal (pathMass ι h)) ∧
      atomicMass μ = ENNReal.ofReal (atomQ ι) := by
  exact ⟨fullMeasure ι, inferInstance, fullMeasure_cylinder ι,
    fullMeasure_atomicMass ι⟩

/- If q=1, the explicitly constructed countable atomic measure alone
   is exact. No residual product measure is needed. -/
theorem discrete_seed_of_atomQ_one (ι : ITree) (hq : atomQ ι = 1) :
    IsProbabilityMeasure (atomMeasure ι) ∧
      (∀ h, atomMeasure ι (cylinder ι h) = ENNReal.ofReal (pathMass ι h)) ∧
      atomMeasure ι (atomicSupport ι) = 1 := by
  have hr : resMass ι [] = 0 := by rw [resMass_root, hq]; ring
  refine ⟨⟨by simp [atomMeasure_univ, hq]⟩, ?_, by simp [atomMeasure_support, hq]⟩
  intro h
  rw [atomMeasure_cylinder]
  have hh := exact_split ι h
  simpa [hr] using congrArg ENNReal.ofReal hh

/- A general countable source; no ordering of weights is required. -/
def countableMeasure (ι : ITree) (w : ℕ → ℝ) (s : ℕ → IStrategy ι) :
    Measure (IStrategy ι) :=
  Measure.sum fun i => ENNReal.ofReal (w i) • Measure.dirac (s i)

theorem countableMeasure_atomicMass (ι : ITree) (w : ℕ → ℝ)
    (s : ℕ → IStrategy ι) (hw : ∀ i, 0 ≤ w i) (hm : HasSum w 1) :
    atomicMass (countableMeasure ι w s) = 1 := by
  unfold atomicMass countableMeasure
  simp only [Measure.sum_apply _ (measurableSet_singleton _),
    Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.tsum_comm]
  have ht : ∀ i, (∑' x : IStrategy ι,
      ENNReal.ofReal (w i) * Measure.dirac (s i) {x}) = ENNReal.ofReal (w i) := by
    intro i
    rw [tsum_eq_single (s i)]
    · simp
    · intro x hx
      simp [Measure.dirac_apply, hx, Ne.symm hx]
  simp_rw [ht]
  rw [← ENNReal.ofReal_tsum_of_nonneg hw hm.summable, hm.tsum_eq]
  simp

theorem countableMeasure_cylinder (ι : ITree) (w : ℕ → ℝ)
    (s : ℕ → IStrategy ι) (hw : ∀ i, 0 ≤ w i) (hm : HasSum w 1)
    (h : List (ℕ × ℕ)) :
    countableMeasure ι w s (cylinder ι h) =
      ENNReal.ofReal (∑' i, w i * indAgree ι (s i) h) := by
  have hn : ∀ i, 0 ≤ w i * indAgree ι (s i) h :=
    fun i => mul_nonneg (hw i) (indAgree_nonneg ι _ h)
  have hs : Summable (fun i => w i * indAgree ι (s i) h) := by
    apply summable_of_sum_range_le hn
    intro K
    calc
      (∑ i ∈ range K, w i * indAgree ι (s i) h) ≤ ∑ i ∈ range K, w i := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right (hw i) (indAgree_le_one ι _ h)
      _ ≤ 1 := sum_le_hasSum _ (fun i _ => hw i) hm
  rw [countableMeasure, Measure.sum_apply _ (measurable_cylinder ι h),
    ENNReal.ofReal_tsum_of_nonneg hn hs]
  apply tsum_congr
  intro i
  by_cases hi : iAgree ι (s i) h
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurable_cylinder ι h),
      cylinder, indAgree, hi]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurable_cylinder ι h),
      cylinder, indAgree, hi]

theorem countable_seed_iff_atomQ_one (ι : ITree) :
    (∃ (w : ℕ → ℝ) (s : ℕ → IStrategy ι),
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
      ∀ h, (∑' i, w i * indAgree ι (s i) h) = pathMass ι h) ↔ atomQ ι = 1 := by
  constructor
  · rintro ⟨w,s,hw,hm,hex⟩
    let μ := countableMeasure ι w s
    letI : IsProbabilityMeasure μ :=
      HasSum.isProbabilityMeasure_sum_dirac hw hm
    have hc : ∀ h, μ (cylinder ι h) = ENNReal.ofReal (pathMass ι h) := by
      intro h
      rw [countableMeasure_cylinder ι w s hw hm h, hex h]
    have hu := ordinary_atomic_upper μ (sourceOfCylinders ι μ hc)
    rw [countableMeasure_atomicMass ι w s hw hm] at hu
    have hlo : 1 ≤ atomQ ι := by
      exact (ENNReal.ofReal_le_ofReal_iff (atomQ_nonneg ι)).mp (by simpa using hu)
    have hhi : atomQ ι ≤ 1 := by
      apply csSup_le (Set.range_nonempty _)
      rintro x ⟨K,rfl⟩
      exact atomA_le_one ι K
    exact le_antisymm hhi hlo
  · intro hq
    refine ⟨diagWeight ι,capStrat ι,diagWeight_nonneg ι,?_,?_⟩
    · have hh : (∑' i, diagWeight ι i) = 1 := by
        rw [diagMass_eq_tsum_atomQ, hq]
      exact hh ▸ (diag_summable ι).hasSum
    · intro h
      have hh := exact_split ι h
      have hr : resMass ι [] = 0 := by rw [resMass_root,hq]; ring
      simpa [hr,cylMass] using hh

#print axioms ordinary_atomic_upper
#print axioms causal_atomic_capacity_attained
#print axioms discrete_seed_of_atomQ_one
#print axioms countable_seed_iff_atomQ_one

end Completion
end CausalSpectrum
end

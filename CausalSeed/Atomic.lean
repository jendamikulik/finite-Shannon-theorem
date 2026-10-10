/-
Concentration of greedy causal extraction.

If every policy on a finite controlled tree carries mass at least `a` on some
`K` transcripts, the first `M` greedy weights sum to at least
`a (1 - (1 - 1/K)^M)`. The same lower bound holds at every finite horizon of a
locally finite tree, with `a` replaced by `atomA`, the infimum of that
transcript mass. The first `M` greedy weights are also at most the mass of any
`M` transcripts of any policy.

Along horizons, `atomA` is the infimum of the horizon infima. A diagonal
subsequence of the ordered greedy weights converges, and the sum of the limit
weights is exactly `atomQ = sup_K atomA`. This identifies two numbers. It does
not produce limiting strategies, a residual flow, or an exact causal
representation.

Not proved here: equality of ordinary and causal atomic capacities, the
projective entropy identity `C_∞ = sup_n C_n`, and the finite gap `G_*`.
No publication priority is claimed. Ordinary infinite-family concentration is
prior work and is not reproved.
-/
import CausalSeed.Spectrum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Tactic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Sequences

noncomputable section
open Classical
open Finset
open Filter
open scoped Topology
namespace CausalSpectrum

set_option backward.isDefEq.respectTransparency false

/-! ## Mass of at most `K` transcripts -/

def massSets (T : Tree) (π : Policy T) (K : ℕ) : Finset (Finset (Leaf T)) := by
  classical
  exact univ.filter fun D => D.card ≤ K ∧ ∀ ℓ ∈ D, CompatiblePolicy ℓ π

theorem massSets_empty {T : Tree} (π : Policy T) (K : ℕ) :
    ∅ ∈ massSets T π K := by
  classical
  simp [massSets]

theorem massSets_mono {T : Tree} (π : Policy T) {K K' : ℕ} (hK : K ≤ K') :
    massSets T π K ⊆ massSets T π K' := by
  classical
  intro D hD
  simp only [massSets, mem_filter, mem_univ, true_and] at hD ⊢
  exact ⟨le_trans hD.1 hK, hD.2⟩

noncomputable def topSet (T : Tree) (π : Policy T) (K : ℕ) : Finset (Leaf T) :=
  Classical.choose (exists_max_image (massSets T π K)
    (fun D => ∑ ℓ ∈ D, leafMass ℓ) ⟨∅, massSets_empty π K⟩)

theorem topSet_mem (T : Tree) (π : Policy T) (K : ℕ) :
    topSet T π K ∈ massSets T π K ∧
      ∀ D ∈ massSets T π K,
        ∑ ℓ ∈ D, leafMass ℓ ≤ ∑ ℓ ∈ topSet T π K, leafMass ℓ :=
  Classical.choose_spec (exists_max_image (massSets T π K)
    (fun D => ∑ ℓ ∈ D, leafMass ℓ) ⟨∅, massSets_empty π K⟩)

noncomputable def topMass (T : Tree) (π : Policy T) (K : ℕ) : ℝ :=
  ∑ ℓ ∈ topSet T π K, leafMass ℓ

theorem topMass_nonneg (T : Tree) (π : Policy T) (K : ℕ) : 0 ≤ topMass T π K := by
  classical
  refine Finset.sum_nonneg ?_
  intro ℓ hℓ
  exact (leafMass_pos ℓ).le

theorem card_topSet (T : Tree) (π : Policy T) (K : ℕ) :
    (topSet T π K).card ≤ K ∧ ∀ ℓ ∈ topSet T π K, CompatiblePolicy ℓ π := by
  classical
  have h := (topSet_mem T π K).1
  simp only [massSets, mem_filter, mem_univ, true_and] at h
  exact h

theorem topMass_le_of_set {T : Tree} (π : Policy T) (K : ℕ)
    {D : Finset (Leaf T)} (hD : D.card ≤ K) (hc : ∀ ℓ ∈ D, CompatiblePolicy ℓ π) :
    ∑ ℓ ∈ D, leafMass ℓ ≤ topMass T π K := by
  classical
  have hmem : D ∈ massSets T π K := by
    simp only [massSets, mem_filter, mem_univ, true_and]
    exact ⟨hD, hc⟩
  exact (topSet_mem T π K).2 D hmem

theorem topMass_mono {T : Tree} (π : Policy T) {K K' : ℕ} (hK : K ≤ K') :
    topMass T π K ≤ topMass T π K' := by
  classical
  have hc := card_topSet T π K
  exact topMass_le_of_set π K' (le_trans hc.1 hK) hc.2

/-! ## Summing a policy over its compatible leaves -/

theorem leafSum_psigma {α : Type} {β : α → Type} [Fintype α] [∀ a, Fintype (β a)]
    (f : (Σ' a, β a) → ℝ) :
    ∑ x, f x = ∑ a, ∑ b, f ⟨a, b⟩ := by
  classical
  let e : (Σ' a, β a) ≃ Σ a, β a := Equiv.psigmaEquivSigma β
  have hs : ∑ x, f x = ∑ s : Σ a, β a, f (e.symm s) :=
    Fintype.sum_equiv e f (fun s => f (e.symm s)) (fun x => by simp [e])
  rw [hs, ← univ_sigma_univ, sum_sigma]
  refine sum_congr rfl ?_
  intro a _
  -- `e.symm ⟨a, b⟩ = ⟨a, b⟩`
  apply sum_congr rfl
  intro b _
  rfl

theorem policySum_eq_compatible {T : Tree} (f : Leaf T → ℝ) (π : Policy T) :
    policySum f π =
      ∑ ℓ ∈ univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π, f ℓ := by
  classical
  induction T with
  | leaf =>
      simp only [policySum, CompatiblePolicy]
      change f PUnit.unit = ∑ ℓ ∈ univ.filter (fun _ : PUnit => True), f ℓ
      have hfilter : univ.filter (fun _ : PUnit => True) = ({PUnit.unit} : Finset PUnit) := by
        ext x
        simp
      rw [hfilter, sum_singleton]
  | node nA hA nY hY K Kpos Ksum child ih =>
      have hsplit : ∑ ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child),
          (if CompatiblePolicy ℓ π then f ℓ else 0) =
          ∑ a : Fin nA, ∑ y : Fin (nY a), ∑ ℓc : Leaf (child a y),
            if a = π.1 ∧ CompatiblePolicy ℓc (π.2 a y) then f ⟨a, y, ℓc⟩ else 0 := by
        simp only [Leaf]
        rw [leafSum_psigma]
        refine sum_congr rfl ?_
        intro a _
        rw [leafSum_psigma]
        refine sum_congr rfl ?_
        intro y _
        refine sum_congr rfl ?_
        intro ℓc _
        simp [CompatiblePolicy]
      have hLHS : policySum f π =
          ∑ y : Fin (nY π.1), policySum (fun ℓc => f ⟨π.1, y, ℓc⟩) (π.2 π.1 y) := by
        rfl
      rw [hLHS]
      have hfilter : ∑ ℓ ∈ univ.filter fun ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) =>
            CompatiblePolicy ℓ π, f ℓ =
          ∑ ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child),
            if CompatiblePolicy ℓ π then f ℓ else 0 := by
        rw [sum_filter]
      rw [hfilter, hsplit]
      have hform : ∀ a : Fin nA,
          (∑ y : Fin (nY a), ∑ ℓc : Leaf (child a y),
            if a = π.1 ∧ CompatiblePolicy ℓc (π.2 a y) then f ⟨a, y, ℓc⟩ else 0) =
          if a = π.1 then
            ∑ y : Fin (nY π.1), ∑ ℓc : Leaf (child π.1 y),
              if CompatiblePolicy ℓc (π.2 π.1 y) then f ⟨π.1, y, ℓc⟩ else 0
          else 0 := by
        intro a
        by_cases ha : a = π.1
        · subst ha
          simp
        · simp [ha]
      have hrewrite :
          (∑ a : Fin nA, ∑ y : Fin (nY a), ∑ ℓc : Leaf (child a y),
            if a = π.1 ∧ CompatiblePolicy ℓc (π.2 a y) then f ⟨a, y, ℓc⟩ else 0) =
          ∑ a : Fin nA, if a = π.1 then
            ∑ y : Fin (nY π.1), ∑ ℓc : Leaf (child π.1 y),
              if CompatiblePolicy ℓc (π.2 π.1 y) then f ⟨π.1, y, ℓc⟩ else 0
          else 0 := by
        refine sum_congr rfl ?_
        intro a _
        exact hform a
      rw [hrewrite]
      have hflip : (∑ a : Fin nA, if a = π.1 then
            ∑ y : Fin (nY π.1), ∑ ℓc : Leaf (child π.1 y),
              if CompatiblePolicy ℓc (π.2 π.1 y) then f ⟨π.1, y, ℓc⟩ else 0
          else 0) =
          ∑ a : Fin nA, if π.1 = a then
            ∑ y : Fin (nY π.1), ∑ ℓc : Leaf (child π.1 y),
              if CompatiblePolicy ℓc (π.2 π.1 y) then f ⟨π.1, y, ℓc⟩ else 0
          else 0 := by
        refine sum_congr rfl ?_
        intro a _
        by_cases ha : a = π.1
        · simp [ha]
        · simp [ha, Ne.symm ha]
      rw [hflip, sum_ite_eq, if_pos (mem_univ _)]
      refine sum_congr rfl ?_
      intro y _
      rw [ih π.1 y (fun ℓc => f ⟨π.1, y, ℓc⟩) (π.2 π.1 y), sum_filter]

theorem compatible_mass {T : Tree} (π : Policy T) :
    ∑ ℓ ∈ univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π, leafMass ℓ = 1 := by
  have h := policySum_eq_compatible (fun ℓ => leafMass ℓ) π
  have hp : policySum (leafValue (Field.p T)) π = 1 := by
    simpa using policySum_flow (Field.p T) π (Field.p_isFlow T)
  have hleaf : leafValue (Field.p T) = leafMass := by
    funext ℓ
    simpa [Field.p] using leafValue_probability T 1 ℓ
  rw [← hleaf] at h
  rw [← hleaf]
  exact h.symm.trans hp

theorem topMass_le_one {T : Tree} (π : Policy T) (K : ℕ) : topMass T π K ≤ 1 := by
  classical
  have hc := card_topSet T π K
  have hsub : topSet T π K ⊆ univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π := by
    intro ℓ hℓ
    simp only [mem_filter, mem_univ, true_and]
    exact hc.2 ℓ hℓ
  have hle : ∑ ℓ ∈ topSet T π K, leafMass ℓ ≤
      ∑ ℓ ∈ univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π, leafMass ℓ := by
    refine sum_le_sum_of_subset_of_nonneg hsub ?_
    intro ℓ _ _
    exact (leafMass_pos ℓ).le
  rw [compatible_mass] at hle
  exact hle

/-! ## Greedy head after `M` extractions -/

noncomputable def peel {T : Tree} (r : Field T) : ℕ → Field T
  | 0 => r
  | m + 1 =>
      let s := peel r m
      if 0 < Field.root s then extract s (maximizingStrategy s) (bottleneck s) else s

noncomputable def wAt {T : Tree} (r : Field T) (m : ℕ) : ℝ :=
  let s := peel r m
  if 0 < Field.root s then bottleneck s else 0

theorem peel_good {T : Tree} (r : Field T) (hf : Field.IsFlow r) (hn : Field.Nonneg r) :
    ∀ m, Field.IsFlow (peel r m) ∧ Field.Nonneg (peel r m) := by
  intro m
  induction m with
  | zero => exact ⟨hf, hn⟩
  | succ m ih =>
      simp only [peel]
      split_ifs with hr
      · exact ⟨extract_isFlow _ _ _ ih.1,
          extract_nonneg _ _ _ ih.1 ih.2 (le_of_eq (maximizingStrategy_attains _).symm)⟩
      · exact ih

theorem root_peel_head {T : Tree} (r : Field T) (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (m : ℕ) :
    Field.root (peel r m) + ∑ i ∈ range m, wAt r i = Field.root r := by
  induction m with
  | zero => simp [peel]
  | succ m ih =>
      have hg := peel_good r hf hn m
      rw [sum_range_succ]
      simp only [peel]
      by_cases hr : 0 < Field.root (peel r m)
      · simp only [hr, ite_true]
        have hex := root_extract (peel r m) (maximizingStrategy (peel r m))
          (bottleneck (peel r m))
        have hw : wAt r m = bottleneck (peel r m) := by simp [wAt, hr]
        rw [hw]
        linarith
      · simp only [hr, ite_false]
        have hz : Field.root (peel r m) = 0 :=
          le_antisymm (le_of_not_gt hr) hg.2.root_nonneg
        have hw : wAt r m = 0 := by simp [wAt, hr]
        rw [hz] at ih ⊢
        rw [hw]
        linarith

theorem peel_leaf_le {T : Tree} (m : ℕ) (ℓ : Leaf T) :
    leafValue (peel (Field.p T) m) ℓ ≤ leafMass ℓ := by
  have h0 : ∀ ℓ : Leaf T, leafValue (Field.p T) ℓ = leafMass ℓ := by
    intro ℓ'
    simpa [Field.p] using leafValue_probability T 1 ℓ'
  induction m with
  | zero => simpa [peel] using (h0 ℓ).le
  | succ m ih =>
      simp only [peel]
      split_ifs with hr
      · rw [leafValue_extract]
        have hw : 0 ≤ bottleneck (peel (Field.p T) m) :=
          (bottleneck_pos (peel_good _ (Field.p_isFlow T) (Field.p_nonneg T) m).1
            (peel_good _ (Field.p_isFlow T) (Field.p_nonneg T) m).2 hr).le
        by_cases hc : CompatibleStrategy ℓ (maximizingStrategy (peel (Field.p T) m))
        · simp only [if_pos hc]
          linarith [ih]
        · simp only [if_neg hc, sub_zero]
          exact ih
      · exact ih

theorem wAt_nonneg {T : Tree} (r : Field T) (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (m : ℕ) : 0 ≤ wAt r m := by
  simp only [wAt]
  split_ifs with hr
  · exact (bottleneck_pos (peel_good r hf hn m).1 (peel_good r hf hn m).2 hr).le
  · exact le_rfl

theorem wAt_antitone {T : Tree} (m : ℕ) :
    wAt (Field.p T) (m + 1) ≤ wAt (Field.p T) m := by
  have hg := peel_good (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T) m
  unfold wAt
  by_cases hr : 0 < Field.root (peel (Field.p T) m)
  · have hw : 0 ≤ bottleneck (peel (Field.p T) m) := (bottleneck_pos hg.1 hg.2 hr).le
    have hnext : peel (Field.p T) (m + 1) =
        extract (peel (Field.p T) m) (maximizingStrategy (peel (Field.p T) m))
          (bottleneck (peel (Field.p T) m)) := by
      simp [peel, hr]
    rw [hnext]
    by_cases hr' : 0 < Field.root (extract (peel (Field.p T) m)
        (maximizingStrategy (peel (Field.p T) m)) (bottleneck (peel (Field.p T) m)))
    · simp only [hr, hr', ite_true]
      exact bottleneck_mono _ _ (extract_le _ _ _ hw)
    · simp only [hr, hr', ite_true, ite_false]
      exact hw
  · have hstay : peel (Field.p T) (m + 1) = peel (Field.p T) m := by simp [peel, hr]
    simp [hstay, hr]

/-- If every policy carries mass at least `a` on some `K` transcripts, the first
`M` greedy weights sum to at least `a (1 - (1 - 1/K)^M)`. -/
theorem greedy_head_lower {T : Tree} {K : ℕ} {a : ℝ}
    (hK : 0 < K) (_ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hcov : ∀ π : Policy T, a ≤ topMass T π K) (M : ℕ) :
    a * (1 - (1 - 1 / (K : ℝ)) ^ M) ≤ ∑ i ∈ range M, wAt (Field.p T) i := by
  classical
  set ρ : ℝ := 1 - 1 / (K : ℝ)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hρ0 : 0 ≤ ρ := by
    have h1 : (1 : ℝ) ≤ K := by exact_mod_cast (Nat.succ_le_of_lt hK)
    have : 1 / (K : ℝ) ≤ 1 := by
      rw [div_le_one hK0]
      exact h1
    exact sub_nonneg.mpr this
  have hρ1 : ρ ≤ 1 := by
    have : 0 ≤ 1 / (K : ℝ) := by positivity
    exact sub_le_self 1 this
  let e : ℕ → ℝ := fun m => Field.root (peel (Field.p T) m) - (1 - a)
  have hstep : ∀ m, e (m + 1) ≤ ρ * e m := by
    intro m
    have hg := peel_good (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T) m
    by_cases hr : 0 < Field.root (peel (Field.p T) m)
    · set s := peel (Field.p T) m
      set w := bottleneck s
      have hwpos : 0 < w := bottleneck_pos hg.1 hg.2 hr
      let π := minimizingPolicy s
      have hceil : policyCeil s π = w := minimizingPolicy_attains s
      let D := topSet T π K
      have hDcard : D.card ≤ K := (card_topSet T π K).1
      have hDcomp : ∀ ℓ ∈ D, CompatiblePolicy ℓ π := (card_topSet T π K).2
      have hDa : a ≤ ∑ ℓ ∈ D, leafMass ℓ := by
        have htop : a ≤ topMass T π K := hcov π
        simpa [topMass, D] using htop
      have hroot : policySum (leafValue s) π = Field.root s :=
        policySum_flow s π hg.1
      have hsumV : ∑ ℓ ∈ univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π, leafValue s ℓ =
          Field.root s := by
        simpa using (policySum_eq_compatible (leafValue s) π).symm.trans hroot
      have hDsub : D ⊆ univ.filter fun ℓ : Leaf T => CompatiblePolicy ℓ π := by
        intro ℓ hℓ
        simp only [mem_filter, mem_univ, true_and]
        exact hDcomp ℓ hℓ
      have hsplit := sum_sdiff hDsub (f := leafValue s)
      -- `sum_sdiff` : sum on the complement plus sum on D equals the filter sum
      have hout_le : ∑ ℓ ∈ (univ.filter fun ℓ => CompatiblePolicy ℓ π) \ D, leafValue s ℓ ≤
          ∑ ℓ ∈ (univ.filter fun ℓ => CompatiblePolicy ℓ π) \ D, leafMass ℓ := by
        refine sum_le_sum ?_
        intro ℓ _
        exact peel_leaf_le m ℓ
      have hDval : ∑ ℓ ∈ D, leafValue s ℓ ≤ (K : ℝ) * w := by
        have hpt : ∀ ℓ ∈ D, leafValue s ℓ ≤ w := by
          intro ℓ hℓ
          have hle := leaf_le_policyCeil s π ℓ (hDcomp ℓ hℓ)
          simpa [hceil] using hle
        have hsumw : ∑ ℓ ∈ D, leafValue s ℓ ≤ ∑ ℓ ∈ D, w := sum_le_sum hpt
        simp only [sum_const, nsmul_eq_mul] at hsumw
        have hcard : (D.card : ℝ) ≤ K := by exact_mod_cast hDcard
        have hw0 : 0 ≤ w := hwpos.le
        exact le_trans hsumw (mul_le_mul_of_nonneg_right hcard hw0)
      have hmass : ∑ ℓ ∈ (univ.filter fun ℓ => CompatiblePolicy ℓ π) \ D, leafMass ℓ =
          1 - ∑ ℓ ∈ D, leafMass ℓ := by
        have hsplitM := sum_sdiff hDsub (f := leafMass)
        have hall := compatible_mass π
        linarith
      have hR : Field.root s ≤ (K : ℝ) * w + (1 - a) := by
        have houtside : ∑ ℓ ∈ (univ.filter fun ℓ => CompatiblePolicy ℓ π) \ D,
            leafValue s ℓ ≤ 1 - a := by
          calc
            _ ≤ ∑ ℓ ∈ (univ.filter fun ℓ => CompatiblePolicy ℓ π) \ D, leafMass ℓ := hout_le
            _ = 1 - ∑ ℓ ∈ D, leafMass ℓ := hmass
            _ ≤ 1 - a := by linarith
        linarith
      have he : e m ≤ (K : ℝ) * w := by
        simp only [e, s]
        linarith
      have hR' : Field.root (peel (Field.p T) (m + 1)) = Field.root s - w := by
        simp only [peel, s, hr, if_pos]
        exact root_extract _ _ _
      have he' : e (m + 1) = e m - w := by
        simp only [e, hR']
        ring
      have hwge : e m / (K : ℝ) ≤ w :=
        (div_le_iff₀ hK0).mpr (by simpa [mul_comm] using he)
      have hdiff : e m - w ≤ e m - e m / (K : ℝ) := by linarith
      have hfactor : e m - e m / (K : ℝ) = ρ * e m := by
        simp only [ρ]
        ring
      linarith
    · have hz : Field.root (peel (Field.p T) m) = 0 :=
        le_antisymm (le_of_not_gt hr) hg.2.root_nonneg
      have hstay : peel (Field.p T) (m + 1) = peel (Field.p T) m := by
        simp [peel, hr]
      have heq : e (m + 1) = e m := by simp [e, hstay]
      have hneg : e m ≤ 0 := by
        simp only [e, hz]
        linarith
      have hmul : e m ≤ ρ * e m := by
        have h1ρ : 0 ≤ 1 - ρ := by linarith
        have := mul_nonpos_of_nonpos_of_nonneg hneg h1ρ
        -- `(e m) * (1 - ρ) ≤ 0`, so `e m ≤ ρ * e m`
        linarith
      simpa [heq] using hmul
  have hgeom : ∀ M, e M ≤ ρ ^ M * e 0 := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
        calc
          e (M + 1) ≤ ρ * e M := hstep M
          _ ≤ ρ * (ρ ^ M * e 0) := by
            have hρn : 0 ≤ ρ ^ M := pow_nonneg hρ0 M
            exact mul_le_mul_of_nonneg_left ih hρ0
          _ = ρ ^ (M + 1) * e 0 := by ring
  have he0 : e 0 = a := by simp [e, peel]
  have hRM : Field.root (peel (Field.p T) M) ≤ 1 - a + a * ρ ^ M := by
    have h := hgeom M
    rw [he0] at h
    simp only [e] at h
    linarith
  have hhead := root_peel_head (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T) M
  have hsum : ∑ i ∈ range M, wAt (Field.p T) i = 1 - Field.root (peel (Field.p T) M) := by
    have hone : Field.root (Field.p T) = 1 := Field.root_p T
    rw [hone] at hhead
    linarith
  have hpow : a * (1 - ρ ^ M) ≤ 1 - Field.root (peel (Field.p T) M) := by
    have hroot0 : 0 ≤ Field.root (peel (Field.p T) M) :=
      (peel_good _ (Field.p_isFlow T) (Field.p_nonneg T) M).2.root_nonneg
    linarith
  simpa [hsum, ρ] using hpow

/-! ## The extracted weights are a greedy trace, nonincreasing -/

noncomputable def greedyList (T : Tree) : List (Atom T) :=
  Classical.choose (greedyTrace_exists (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T))

theorem greedyList_trace (T : Tree) : GreedyTrace (Field.p T) (greedyList T) :=
  Classical.choose_spec (greedyTrace_exists (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T))

def atomWeight {T : Tree} (atoms : List (Atom T)) (i : ℕ) : ℝ :=
  if h : i < atoms.length then (atoms[i]).1 else 0

theorem peel_shift {T : Tree} (r : Field T) (hr : 0 < Field.root r) :
    ∀ j, peel r (j + 1) = peel (extract r (maximizingStrategy r) (bottleneck r)) j := by
  intro j
  induction j with
  | zero => simp [peel, hr]
  | succ j ih =>
      have hdef : peel r ((j + 1) + 1) =
          (let s := peel r (j + 1)
           if 0 < Field.root s then
             extract s (maximizingStrategy s) (bottleneck s) else s) := rfl
      rw [hdef, ih]
      rfl

theorem wAt_eq_atomWeight {T : Tree} (r : Field T) (atoms : List (Atom T))
    (ht : GreedyTrace r atoms) (hf : Field.IsFlow r) (hn : Field.Nonneg r) :
    ∀ i, atomWeight atoms i = wAt r i := by
  classical
  intro i
  induction ht generalizing i with
  | done r hz =>
      have hnot : ¬ 0 < Field.root r := by simpa [hz]
      have hpeel : ∀ j, peel r j = r := by
        intro j
        induction j with
        | zero => rfl
        | succ j ihj => simp [peel, ihj, hnot]
      simp [atomWeight, wAt, hpeel, hnot]
  | step r tail hr ht ih =>
      cases i with
      | zero => simp [atomWeight, wAt, peel, hr]
      | succ i =>
          have hg := greedy_step r hf hn hr
          have hshift := peel_shift r hr i
          have htail := ih hg.2.1 hg.2.2.1 i
          have hw : wAt r (i + 1) = wAt (extract r (maximizingStrategy r) (bottleneck r)) i := by
            simp only [wAt, hshift]
          by_cases hi : i < tail.length
          · have hi' : i + 1 < tail.length + 1 := by omega
            simp only [atomWeight, List.length_cons, List.getElem_cons_succ, hi', dite_true, hw]
            simpa [atomWeight, hi] using htail
          · have hi' : ¬ i + 1 < tail.length + 1 := by omega
            simp only [atomWeight, List.length_cons, hi', dite_false, hw]
            simpa [atomWeight, hi] using htail

theorem greedy_wAt (T : Tree) (i : ℕ) :
    atomWeight (greedyList T) i = wAt (Field.p T) i :=
  wAt_eq_atomWeight (Field.p T) (greedyList T) (greedyList_trace T)
    (Field.p_isFlow T) (Field.p_nonneg T) i

/-! ## Locally finite trees, as compatible finite horizons -/

structure ITree where
  nA : List (ℕ × ℕ) → ℕ
  hA : ∀ h, 0 < nA h
  nY : ∀ h, Fin (nA h) → ℕ
  hY : ∀ h a, 0 < nY h a
  kern : ∀ h, (a : Fin (nA h)) → Fin (nY h a) → ℝ
  kpos : ∀ h a y, 0 < kern h a y
  ksum : ∀ h a, ∑ y, kern h a y = 1

noncomputable def trunc (ι : ITree) : ℕ → List (ℕ × ℕ) → Tree
  | 0, _ => .leaf
  | n + 1, h =>
      .node (ι.nA h) (ι.hA h) (ι.nY h) (ι.hY h) (ι.kern h) (ι.kpos h) (ι.ksum h)
        (fun a y => trunc ι n (h ++ [(a.val, y.val)]))

noncomputable def atomA (ι : ITree) (K : ℕ) : ℝ :=
  sInf { t : ℝ | ∃ n : ℕ, ∃ π : Policy (trunc ι n []), t = topMass (trunc ι n []) π K }

theorem atomA_bddBelow (ι : ITree) (K : ℕ) :
    BddBelow { t : ℝ | ∃ n : ℕ, ∃ π : Policy (trunc ι n []), t = topMass (trunc ι n []) π K } := by
  refine ⟨0, ?_⟩
  intro t ht
  rcases ht with ⟨n, π, rfl⟩
  exact topMass_nonneg _ π K

theorem atomA_nonempty (ι : ITree) (K : ℕ) :
    { t : ℝ | ∃ n : ℕ, ∃ π : Policy (trunc ι n []), t = topMass (trunc ι n []) π K }.Nonempty := by
  refine ⟨topMass (trunc ι 0 []) PUnit.unit K, 0, PUnit.unit, rfl⟩

theorem atomA_le_top (ι : ITree) (K n : ℕ) (π : Policy (trunc ι n [])) :
    atomA ι K ≤ topMass (trunc ι n []) π K :=
  csInf_le (atomA_bddBelow ι K) ⟨n, π, rfl⟩

theorem atomA_nonneg (ι : ITree) (K : ℕ) : 0 ≤ atomA ι K :=
  le_csInf (atomA_nonempty ι K) (fun t ht => by
    rcases ht with ⟨n, π, rfl⟩
    exact topMass_nonneg _ π K)

theorem atomA_le_one (ι : ITree) (K : ℕ) : atomA ι K ≤ 1 := by
  have h := atomA_le_top ι K 0 PUnit.unit
  exact le_trans h (topMass_le_one _ K)

theorem atomA_mono (ι : ITree) {K K' : ℕ} (hK : K ≤ K') : atomA ι K ≤ atomA ι K' := by
  refine le_csInf (atomA_nonempty ι K') ?_
  intro t ht
  rcases ht with ⟨n, π, rfl⟩
  exact le_trans (atomA_le_top ι K n π) (topMass_mono π hK)

noncomputable def atomQ (ι : ITree) : ℝ :=
  sSup (Set.range (atomA ι))

theorem atomQ_bdd (ι : ITree) : BddAbove (Set.range (atomA ι)) :=
  ⟨1, fun t ht => by
    rcases ht with ⟨K, rfl⟩
    exact atomA_le_one ι K⟩

theorem atomA_le_atomQ (ι : ITree) (K : ℕ) : atomA ι K ≤ atomQ ι :=
  le_csSup (atomQ_bdd ι) ⟨K, rfl⟩

theorem atomQ_nonneg (ι : ITree) : 0 ≤ atomQ ι :=
  le_trans (atomA_nonneg ι 0) (atomA_le_atomQ ι 0)

/-- On every finite horizon the greedy head obeys the concentration bound
with the uniform transcript mass `atomA`. -/
theorem horizon_head (ι : ITree) {K : ℕ} (hK : 0 < K) (n M : ℕ) :
    atomA ι K * (1 - (1 - 1 / (K : ℝ)) ^ M) ≤
      ∑ i ∈ range M, wAt (Field.p (trunc ι n [])) i := by
  refine greedy_head_lower hK (atomA_nonneg ι K) (atomA_le_one ι K) ?_ M
  intro π
  exact atomA_le_top ι K n π

theorem wAt_le_one (T : Tree) (m : ℕ) : wAt (Field.p T) m ≤ 1 := by
  have hg := peel_good (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T) m
  have hle : wAt (Field.p T) m ≤ Field.root (peel (Field.p T) m) := by
    simp only [wAt]
    split_ifs with hr
    · exact bottleneck_le_root hg.1 hg.2
    · exact hg.2.root_nonneg
  have hhead := root_peel_head (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T) m
  have hone : Field.root (Field.p T) = 1 := Field.root_p T
  have hsum : 0 ≤ ∑ i ∈ range m, wAt (Field.p T) i := by
    refine sum_nonneg ?_
    intro i _
    exact wAt_nonneg _ (Field.p_isFlow T) (Field.p_nonneg T) i
  linarith

/-! ## The greedy head is at most any transcript mass of size `M` -/

theorem topMass_zero {T : Tree} (π : Policy T) : topMass T π 0 = 0 := by
  classical
  have hcard : (topSet T π 0).card = 0 := Nat.le_zero.mp (card_topSet T π 0).1
  simp [topMass, card_eq_zero.mp hcard]

theorem map_take_sum_le {α : Type} (l : List α) (f : α → ℝ) (M : ℕ)
    (hf : ∀ a ∈ l, 0 ≤ f a) : ((l.take M).map f).sum ≤ (l.map f).sum := by
  induction l generalizing M with
  | nil => simp
  | cons a t ih =>
      cases M with
      | zero =>
          simp only [List.take_zero, List.map_nil, List.sum_nil]
          refine List.sum_nonneg ?_
          intro x hx
          simp only [List.mem_map] at hx
          rcases hx with ⟨b, hb, rfl⟩
          exact hf b hb
      | succ M =>
          simp only [List.take_succ_cons, List.map_cons, List.sum_cons]
          linarith [ih M (fun b hb => hf b (List.mem_cons_of_mem a hb))]

theorem represented_take_le {T : Tree} (atoms : List (Atom T)) (M : ℕ) (ℓ : Leaf T)
    (hw : ∀ a ∈ atoms, 0 ≤ a.1) :
    representedLeaf (atoms.take M) ℓ ≤ representedLeaf atoms ℓ := by
  classical
  simpa [representedLeaf] using
    map_take_sum_le atoms (fun a => if CompatibleStrategy ℓ a.2 then a.1 else 0) M
      (fun a ha => by
        by_cases hc : CompatibleStrategy ℓ a.2 <;> simp [hc, hw a ha])

theorem represented_greedy (T : Tree) (ℓ : Leaf T) :
    representedLeaf (greedyList T) ℓ = leafMass ℓ := by
  have hprop := greedyTrace_properties (greedyList_trace T) (Field.p_isFlow T) (Field.p_nonneg T)
  have hleaf : leafValue (Field.p T) ℓ = leafMass ℓ := by
    simpa [Field.p] using leafValue_probability T 1 ℓ
  rw [← hleaf]
  exact hprop.2.2.2 ℓ

theorem greedy_mem_nonneg (T : Tree) {a : Atom T} (ha : a ∈ greedyList T) : 0 ≤ a.1 :=
  le_of_lt ((greedyTrace_properties (greedyList_trace T) (Field.p_isFlow T)
    (Field.p_nonneg T)).1 a ha).1

theorem transcript_take_le (T : Tree) (π : Policy T) (M : ℕ) (ℓ : Leaf T) :
    transcriptWeight ((greedyList T).take M) π ℓ ≤ leafMass ℓ := by
  classical
  rw [transcriptWeight_eq]
  by_cases hp : CompatiblePolicy ℓ π
  · simp only [hp, ite_true]
    exact le_trans
      (represented_take_le (greedyList T) M ℓ (fun a ha => greedy_mem_nonneg T ha))
      (le_of_eq (represented_greedy T ℓ))
  · simp only [hp, ite_false]
    exact (leafMass_pos ℓ).le

theorem real_list_sum_zero {l : List ℝ} (h : ∀ x ∈ l, x = 0) : l.sum = 0 := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp [List.sum_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem total_eq_transcript {T : Tree} (atoms : List (Atom T)) (π : Policy T) :
    totalWeight atoms = ∑ ℓ : Leaf T, transcriptWeight atoms π ℓ := by
  classical
  induction atoms with
  | nil => simp [totalWeight, transcriptWeight]
  | cons a t ih =>
      have hsplit : ∀ ℓ, transcriptWeight (a :: t) π ℓ =
          (if run a.2 π = ℓ then a.1 else 0) + transcriptWeight t π ℓ := by
        intro ℓ
        simp [transcriptWeight, List.map_cons, List.sum_cons]
      simp_rw [hsplit, sum_add_distrib]
      have hhead : totalWeight (a :: t) = a.1 + totalWeight t := by simp [totalWeight]
      rw [hhead, ih]
      have hhit : ∑ ℓ : Leaf T, (if run a.2 π = ℓ then a.1 else 0) = a.1 := by
        rw [sum_ite_eq, if_pos (mem_univ _)]
      linarith

theorem transcript_zero_of_not_hit {T : Tree} (atoms : List (Atom T)) (π : Policy T)
    (ℓ : Leaf T) (h : ℓ ∉ (atoms.map fun a => run a.2 π).toFinset) :
    transcriptWeight atoms π ℓ = 0 := by
  classical
  have hmiss : ∀ a ∈ atoms, run a.2 π ≠ ℓ := by
    intro a ha heq
    apply h
    rw [List.mem_toFinset, List.mem_map]
    exact ⟨a, ha, heq⟩
  unfold transcriptWeight
  refine real_list_sum_zero ?_
  intro x hx
  simp only [List.mem_map] at hx
  rcases hx with ⟨a, ha, rfl⟩
  simp [hmiss a ha]

theorem sum_atomWeight_eq {T : Tree} (atoms : List (Atom T)) (M : ℕ) :
    ∑ i ∈ range M, atomWeight atoms i = totalWeight (atoms.take M) := by
  induction M with
  | zero => simp [totalWeight]
  | succ M ih =>
      rw [sum_range_succ, ih]
      by_cases h : M < atoms.length
      · have htake := List.take_concat_get' atoms M h
        have hw : atomWeight atoms M = (atoms[M]).1 := by simp [atomWeight, h]
        have htot : totalWeight (atoms.take (M + 1)) =
            totalWeight (atoms.take M) + (atoms[M]).1 := by
          rw [← htake]
          simp only [totalWeight, List.map_append, List.sum_append, List.map_singleton,
            List.sum_singleton]
        rw [hw]
        linarith
      · have hw : atomWeight atoms M = 0 := by simp [atomWeight, h]
        have htake : atoms.take (M + 1) = atoms.take M := by
          have hle : atoms.length ≤ M := Nat.le_of_not_lt h
          rw [List.take_of_length_le (le_trans hle (Nat.le_succ _)),
            List.take_of_length_le hle]
        rw [hw, htake]
        ring

theorem greedy_prefix_le_topMass (T : Tree) (π : Policy T) (M : ℕ) :
    ∑ i ∈ range M, wAt (Field.p T) i ≤ topMass T π M := by
  classical
  have hsum : ∑ i ∈ range M, wAt (Field.p T) i =
      totalWeight ((greedyList T).take M) := by
    simp_rw [← greedy_wAt]
    exact sum_atomWeight_eq (greedyList T) M
  rw [hsum]
  set atoms : List (Atom T) := (greedyList T).take M
  let D : Finset (Leaf T) := (atoms.map fun a => run a.2 π).toFinset
  have htot := total_eq_transcript atoms π
  have hrest : ∑ ℓ : Leaf T, transcriptWeight atoms π ℓ =
      ∑ ℓ ∈ D, transcriptWeight atoms π ℓ := by
    symm
    refine sum_subset (subset_univ D) ?_
    intro ℓ _ hℓ
    exact transcript_zero_of_not_hit atoms π ℓ hℓ
  have hpt : ∑ ℓ ∈ D, transcriptWeight atoms π ℓ ≤ ∑ ℓ ∈ D, leafMass ℓ := by
    refine sum_le_sum ?_
    intro ℓ _
    exact transcript_take_le T π M ℓ
  have hcard : D.card ≤ M := by
    have h1 : D.card ≤ atoms.length := by
      simpa [D, List.length_map] using
        List.toFinset_card_le (atoms.map fun a => run a.2 π)
    exact le_trans h1 (by simpa [atoms] using List.length_take_le M (greedyList T))
  have hcomp : ∀ ℓ ∈ D, CompatiblePolicy ℓ π := by
    intro ℓ hℓ
    rw [List.mem_toFinset, List.mem_map] at hℓ
    rcases hℓ with ⟨a, _, rfl⟩
    exact run_compatible_policy a.2 π
  have hmass : ∑ ℓ ∈ D, leafMass ℓ ≤ topMass T π M :=
    topMass_le_of_set π M hcard hcomp
  linarith

theorem trunc_succ (ι : ITree) (h : List (ℕ × ℕ)) (n : ℕ) :
    trunc ι (n + 1) h =
      .node (ι.nA h) (ι.hA h) (ι.nY h) (ι.hY h) (ι.kern h) (ι.kpos h) (ι.ksum h)
        (fun a y => trunc ι n (h ++ [(a.val, y.val)])) := rfl

noncomputable def anyPolicy (ι : ITree) (h : List (ℕ × ℕ)) : ∀ n, Policy (trunc ι n h)
  | 0 => PUnit.unit
  | n + 1 => ⟨⟨0, ι.hA h⟩, fun a y => anyPolicy ι (h ++ [(a.val, y.val)]) n⟩

noncomputable def deepenPolicy (ι : ITree) (h : List (ℕ × ℕ)) :
    ∀ n, Policy (trunc ι n h) → Policy (trunc ι (n + 1) h)
  | 0, _ => ⟨⟨0, ι.hA h⟩, fun _ _ => PUnit.unit⟩
  | n + 1, π => ⟨π.1, fun a y => deepenPolicy ι (h ++ [(a.val, y.val)]) n (π.2 a y)⟩

noncomputable def projectLeaf (ι : ITree) (h : List (ℕ × ℕ)) :
    ∀ n, Leaf (trunc ι (n + 1) h) → Leaf (trunc ι n h)
  | 0, _ => PUnit.unit
  | n + 1, ℓ => ⟨ℓ.1, ℓ.2.1, projectLeaf ι (h ++ [(ℓ.1.val, ℓ.2.1.val)]) n ℓ.2.2⟩

theorem project_compatible (ι : ITree) (h : List (ℕ × ℕ)) :
    ∀ n, ∀ π : Policy (trunc ι n h), ∀ ℓ : Leaf (trunc ι (n + 1) h),
      CompatiblePolicy ℓ (deepenPolicy ι h n π) →
        CompatiblePolicy (projectLeaf ι h n ℓ) π
  | 0, π, _, _ => by
      cases π
      trivial
  | n + 1, π, ℓ, hℓ => by
      simp only [trunc] at π ℓ hℓ
      rcases π with ⟨a0, cont⟩
      rcases ℓ with ⟨a, y, ℓc⟩
      simp only [deepenPolicy, CompatiblePolicy] at hℓ
      rcases hℓ with ⟨ha, hc⟩
      subst ha
      have hchild := project_compatible ι (h ++ [(a.val, y.val)]) n (cont a y) ℓc hc
      exact ⟨rfl, hchild⟩

theorem fiber_le (ι : ITree) (h : List (ℕ × ℕ)) :
    ∀ n, ∀ π : Policy (trunc ι n h), ∀ D : Finset (Leaf (trunc ι (n + 1) h)),
      (∀ ℓ ∈ D, CompatiblePolicy ℓ (deepenPolicy ι h n π)) →
      ∀ σ : Leaf (trunc ι n h), CompatiblePolicy σ π →
        ∑ ℓ ∈ D.filter fun ℓ => projectLeaf ι h n ℓ = σ, leafMass ℓ ≤ leafMass σ
  | 0, π, D, hD, σ, _ => by
      cases σ
      have hfilter : D.filter (fun ℓ => projectLeaf ι h 0 ℓ = PUnit.unit) = D := by
        ext ℓ
        simp [projectLeaf]
      rw [hfilter]
      have hsub : D ⊆ univ.filter fun ℓ => CompatiblePolicy ℓ (deepenPolicy ι h 0 π) := by
        intro ℓ hℓ
        exact mem_filter.mpr ⟨mem_univ _, hD ℓ hℓ⟩
      have hle := sum_le_sum_of_subset_of_nonneg hsub (fun ℓ _ _ => (leafMass_pos ℓ).le)
      rw [compatible_mass] at hle
      simpa [trunc, leafMass] using hle
  | n + 1, π, D, hD, σ, hσ => by
      classical
      simp only [trunc] at π σ D hD hσ
      rcases π with ⟨a0, cont⟩
      rcases σ with ⟨aσ, yσ, σc⟩
      simp only [CompatiblePolicy] at hσ
      rcases hσ with ⟨haσ, hσc⟩
      let parent : Leaf (.node (ι.nA h) (ι.hA h) (ι.nY h) (ι.hY h) (ι.kern h) (ι.kpos h)
          (ι.ksum h) (fun a y => trunc ι (n + 1) (h ++ [(a.val, y.val)]))) → Prop :=
        fun ℓ => projectLeaf ι h (n + 1) ℓ = ⟨aσ, yσ, σc⟩
      let childTree := trunc ι (n + 1) (h ++ [(aσ.val, yσ.val)])
      let Dchild : Finset (Leaf childTree) :=
        univ.filter fun ℓc => (⟨aσ, yσ, ℓc⟩ :
          Leaf (.node (ι.nA h) (ι.hA h) (ι.nY h) (ι.hY h) (ι.kern h) (ι.kpos h) (ι.ksum h)
            (fun a y => trunc ι (n + 1) (h ++ [(a.val, y.val)])))) ∈ D
      have hchildD : ∀ ℓc ∈ Dchild,
          CompatiblePolicy ℓc (deepenPolicy ι (h ++ [(aσ.val, yσ.val)]) n (cont aσ yσ)) := by
        intro ℓc hℓc
        have hc := hD _ (mem_filter.mp hℓc).2
        simp only [deepenPolicy, CompatiblePolicy, haσ] at hc
        exact hc.2
      have hσc' : CompatiblePolicy σc (cont aσ yσ) := by simpa [haσ] using hσc
      have hfib := fiber_le ι (h ++ [(aσ.val, yσ.val)]) n (cont aσ yσ) Dchild hchildD σc hσc'
      let src := Dchild.filter fun ℓc =>
        projectLeaf ι (h ++ [(aσ.val, yσ.val)]) n ℓc = σc
      let emb : Leaf childTree ↪ Leaf (.node (ι.nA h) (ι.hA h) (ι.nY h) (ι.hY h) (ι.kern h)
          (ι.kpos h) (ι.ksum h) (fun a y => trunc ι (n + 1) (h ++ [(a.val, y.val)]))) :=
        ⟨fun ℓc => ⟨aσ, yσ, ℓc⟩, by
          intro a b hab
          injection hab with _ hrest
          injection hrest⟩
      have him : src.map emb = D.filter parent := by
        ext ℓ
        constructor
        · intro hm
          rcases mem_map.mp hm with ⟨ℓc, hsrc, rfl⟩
          obtain ⟨hDc, hproj⟩ := mem_filter.mp hsrc
          refine mem_filter.mpr ⟨(mem_filter.mp hDc).2, ?_⟩
          simp [projectLeaf, emb, parent, hproj]
        · intro hm
          obtain ⟨hℓ, hproj⟩ := mem_filter.mp hm
          rcases ℓ with ⟨a, y, ℓc⟩
          have hproj' := hproj
          unfold parent at hproj'
          dsimp [projectLeaf] at hproj'
          have hinj := PSigma.mk.inj hproj'
          have ha : a = aσ := hinj.1
          subst ha
          have hinj2 := PSigma.mk.inj (eq_of_heq hinj.2)
          have hy : y = yσ := hinj2.1
          subst hy
          have hleaf : projectLeaf ι (h ++ [(a.val, y.val)]) n ℓc = σc := eq_of_heq hinj2.2
          exact mem_map.mpr ⟨ℓc, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hℓ⟩, hleaf⟩, rfl⟩
      have hmul : ∑ ℓ ∈ D.filter parent, leafMass ℓ =
          ι.kern h aσ yσ * ∑ ℓc ∈ src, leafMass ℓc := by
        have hleaf : ∀ ℓc, leafMass (emb ℓc) = ι.kern h aσ yσ * leafMass ℓc := by
          intro ℓc
          simp [emb, leafMass]
        rw [← him, sum_map]
        simp only [hleaf]
        exact (mul_sum src (fun ℓc => leafMass ℓc) (ι.kern h aσ yσ)).symm
      have hgoal : ∑ ℓ ∈ D.filter parent, leafMass ℓ ≤
          ι.kern h aσ yσ * leafMass σc :=
        le_trans (le_of_eq hmul) (mul_le_mul_of_nonneg_left hfib (ι.kpos h aσ yσ).le)
      let shallow : Leaf (.node (ι.nA h) (ι.hA h) (ι.nY h) (ι.hY h) (ι.kern h) (ι.kpos h)
          (ι.ksum h) (fun a y => trunc ι n (h ++ [(a.val, y.val)]))) :=
        ⟨aσ, yσ, σc⟩
      have hmass : leafMass shallow = ι.kern h aσ yσ * leafMass σc := by
        simp [shallow, leafMass]
      exact le_trans hgoal (le_of_eq hmass.symm)

theorem topMass_deepen (ι : ITree) (h : List (ℕ × ℕ)) (n K : ℕ)
    (π : Policy (trunc ι n h)) :
    topMass (trunc ι (n + 1) h) (deepenPolicy ι h n π) K ≤
      topMass (trunc ι n h) π K := by
  classical
  let ρ := deepenPolicy ι h n π
  let D := topSet (trunc ι (n + 1) h) ρ K
  let g := projectLeaf ι h n
  have hD : ∀ ℓ ∈ D, CompatiblePolicy ℓ ρ := (card_topSet _ ρ K).2
  have hsum := sum_fiberwise_of_maps_to
    (s := D) (t := D.image g) (g := g) (fun ℓ hℓ => mem_image_of_mem g hℓ) leafMass
  have hinner : ∀ σ ∈ D.image g,
      ∑ ℓ ∈ D.filter fun ℓ => g ℓ = σ, leafMass ℓ ≤ leafMass σ := by
    intro σ hσ
    have hcomp : CompatiblePolicy σ π := by
      rcases mem_image.mp hσ with ⟨ℓ, hℓ, rfl⟩
      exact project_compatible ι h n π ℓ (hD ℓ hℓ)
    simpa [g, ρ] using fiber_le ι h n π D hD σ hcomp
  have hle1 : ∑ ℓ ∈ D, leafMass ℓ ≤ ∑ σ ∈ D.image g, leafMass σ := by
    rw [← hsum]
    exact sum_le_sum hinner
  have hcompE : ∀ σ ∈ D.image g, CompatiblePolicy σ π := by
    intro σ hσ
    rcases mem_image.mp hσ with ⟨ℓ, hℓ, rfl⟩
    exact project_compatible ι h n π ℓ (hD ℓ hℓ)
  have hcard : (D.image g).card ≤ K :=
    le_trans card_image_le (card_topSet _ ρ K).1
  have hle2 := topMass_le_of_set π K hcard hcompE
  simpa [topMass, D] using le_trans hle1 hle2

noncomputable def horizonA (ι : ITree) (n K : ℕ) : ℝ :=
  sInf { t : ℝ | ∃ π : Policy (trunc ι n []), t = topMass (trunc ι n []) π K }

theorem horizonA_nonempty (ι : ITree) (n K : ℕ) :
    { t : ℝ | ∃ π : Policy (trunc ι n []), t = topMass (trunc ι n []) π K }.Nonempty :=
  ⟨topMass (trunc ι n []) (anyPolicy ι [] n) K, ⟨anyPolicy ι [] n, rfl⟩⟩

theorem horizonA_bddBelow (ι : ITree) (n K : ℕ) :
    BddBelow { t : ℝ | ∃ π : Policy (trunc ι n []), t = topMass (trunc ι n []) π K } :=
  ⟨0, fun t ht => by
    rcases ht with ⟨π, rfl⟩
    exact topMass_nonneg _ π K⟩

theorem horizonA_le_top (ι : ITree) (n K : ℕ) (π : Policy (trunc ι n [])) :
    horizonA ι n K ≤ topMass (trunc ι n []) π K :=
  csInf_le (horizonA_bddBelow ι n K) ⟨π, rfl⟩

theorem horizonA_nonneg (ι : ITree) (n K : ℕ) : 0 ≤ horizonA ι n K :=
  le_csInf (horizonA_nonempty ι n K) (fun t ht => by
    rcases ht with ⟨π, rfl⟩
    exact topMass_nonneg _ π K)

theorem horizonA_succ_le (ι : ITree) (n K : ℕ) : horizonA ι (n + 1) K ≤ horizonA ι n K := by
  refine le_csInf (horizonA_nonempty ι n K) ?_
  intro t ht
  rcases ht with ⟨π, rfl⟩
  exact le_trans (horizonA_le_top ι (n + 1) K (deepenPolicy ι [] n π))
    (topMass_deepen ι [] n K π)

theorem horizonA_antitone (ι : ITree) (K : ℕ) : Antitone fun n => horizonA ι n K :=
  antitone_nat_of_succ_le fun n => horizonA_succ_le ι n K

theorem atomA_eq_iInf (ι : ITree) (K : ℕ) : atomA ι K = ⨅ n, horizonA ι n K := by
  apply le_antisymm
  · refine le_ciInf fun n => ?_
    refine le_csInf (horizonA_nonempty ι n K) ?_
    intro t ht
    rcases ht with ⟨π, rfl⟩
    exact atomA_le_top ι K n π
  · refine le_csInf (atomA_nonempty ι K) ?_
    intro t ht
    rcases ht with ⟨n, π, rfl⟩
    exact le_trans
      (ciInf_le ⟨0, fun r hr => by
        rcases hr with ⟨m, rfl⟩
        exact horizonA_nonneg ι m K⟩ n)
      (horizonA_le_top ι n K π)

/-! ## Diagonal of greedy weights

The objects below are sequences of real weights. A convergent subsequence is
chosen once, by compactness of `[0,1]^ℕ`, and then reused. Nothing here builds
a strategy or a measure on the infinite tree.
-/

theorem le_of_two_tendsto {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b))
    (hle : ∀ n, f n ≤ g n) : a ≤ b := by
  have hsub : Tendsto (fun n => f n - g n) atTop (𝓝 (a - b)) := hf.sub hg
  have hnonpos : ∀ n, f n - g n ≤ 0 := fun n => sub_nonpos.mpr (hle n)
  linarith [le_of_tendsto' hsub hnonpos]

noncomputable def gWeight (ι : ITree) (n i : ℕ) : ℝ :=
  wAt (Field.p (trunc ι n [])) i

theorem gWeight_mem_Icc (ι : ITree) (n i : ℕ) :
    gWeight ι n i ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨?_, ?_⟩
  · simpa [gWeight] using
      wAt_nonneg (Field.p (trunc ι n [])) (Field.p_isFlow _) (Field.p_nonneg _) i
  · simpa [gWeight] using wAt_le_one (trunc ι n []) i

structure DiagPack (ι : ITree) where
  limit : ℕ → ℝ
  index : ℕ → ℕ
  mono : StrictMono index
  tend : Tendsto (fun n i => gWeight ι (index n) i) atTop (𝓝 limit)
  mem : ∀ i, limit i ∈ Set.Icc (0 : ℝ) 1

noncomputable def diagPack (ι : ITree) : DiagPack ι :=
  Classical.choice <| by
    have hs : IsCompact {f : ℕ → ℝ | ∀ i, f i ∈ Set.Icc (0 : ℝ) 1} :=
      isCompact_pi_infinite fun _ => isCompact_Icc
    obtain ⟨a, ha, φ, hφ, htend⟩ :=
      hs.tendsto_subseq (fun n i => gWeight_mem_Icc ι n i)
    exact ⟨⟨a, φ, hφ, htend, ha⟩⟩

noncomputable def diagWeight (ι : ITree) (i : ℕ) : ℝ :=
  (diagPack ι).limit i

noncomputable def diagIndex (ι : ITree) : ℕ → ℕ :=
  (diagPack ι).index

theorem diag_coord_tendsto (ι : ITree) (i : ℕ) :
    Tendsto (fun n => gWeight ι (diagIndex ι n) i) atTop (𝓝 (diagWeight ι i)) := by
  have h := (diagPack ι).tend
  rw [tendsto_pi_nhds] at h
  simpa [diagIndex, diagWeight] using h i

noncomputable def diagPartial (ι : ITree) (M : ℕ) : ℝ :=
  ∑ i ∈ range M, diagWeight ι i

theorem diag_sum_tendsto (ι : ITree) (M : ℕ) :
    Tendsto (fun n => ∑ i ∈ range M, gWeight ι (diagIndex ι n) i) atTop
      (𝓝 (diagPartial ι M)) := by
  simpa [diagPartial] using
    tendsto_finsetSum (f := fun i n => gWeight ι (diagIndex ι n) i)
      (a := diagWeight ι) (range M) (fun i _ => diag_coord_tendsto ι i)

theorem head_le_horizon (ι : ITree) (n M : ℕ) :
    ∑ i ∈ range M, gWeight ι n i ≤ horizonA ι n M := by
  refine le_csInf (horizonA_nonempty ι n M) ?_
  intro t ht
  rcases ht with ⟨π, rfl⟩
  simpa [gWeight] using greedy_prefix_le_topMass (trunc ι n []) π M

theorem horizon_tendsto (ι : ITree) (K : ℕ) :
    Tendsto (fun n => horizonA ι n K) atTop (𝓝 (atomA ι K)) := by
  rw [atomA_eq_iInf]
  exact tendsto_atTop_ciInf (horizonA_antitone ι K)
    ⟨0, fun t ht => by
      rcases ht with ⟨n, rfl⟩
      exact horizonA_nonneg ι n K⟩

theorem diagPartial_le_atomA (ι : ITree) (M : ℕ) :
    diagPartial ι M ≤ atomA ι M := by
  refine le_of_two_tendsto (diag_sum_tendsto ι M)
    ((horizon_tendsto ι M).comp (diagPack ι).mono.tendsto_atTop) ?_
  intro n
  simpa [diagIndex] using head_le_horizon ι (diagIndex ι n) M

theorem diagPartial_ge (ι : ITree) {K : ℕ} (hK : 0 < K) (M : ℕ) :
    atomA ι K * (1 - (1 - 1 / (K : ℝ)) ^ M) ≤ diagPartial ι M := by
  refine ge_of_tendsto' (diag_sum_tendsto ι M) ?_
  intro n
  simpa [gWeight, diagIndex] using horizon_head ι hK (diagIndex ι n) M

theorem diagPartial_le_atomQ (ι : ITree) (M : ℕ) :
    diagPartial ι M ≤ atomQ ι :=
  le_trans (diagPartial_le_atomA ι M) (atomA_le_atomQ ι M)

noncomputable def diagMass (ι : ITree) : ℝ :=
  sSup (Set.range (diagPartial ι))

theorem diagPartial_bdd (ι : ITree) : BddAbove (Set.range (diagPartial ι)) :=
  ⟨atomQ ι, fun t ht => by
    rcases ht with ⟨M, rfl⟩
    exact diagPartial_le_atomQ ι M⟩

theorem diagMass_le_atomQ (ι : ITree) : diagMass ι ≤ atomQ ι :=
  csSup_le (Set.range_nonempty _) fun t ht => by
    rcases ht with ⟨M, rfl⟩
    exact diagPartial_le_atomQ ι M

theorem atomA_le_diagMass (ι : ITree) {K : ℕ} (hK : 0 < K) : atomA ι K ≤ diagMass ι := by
  let ρ : ℝ := 1 - 1 / (K : ℝ)
  have hρ0 : 0 ≤ ρ := by
    have hcast : (0 : ℝ) < K := by exact_mod_cast hK
    have hone : (1 : ℝ) ≤ K := by exact_mod_cast Nat.succ_le_of_lt hK
    exact sub_nonneg.mpr ((div_le_one hcast).mpr hone)
  have hρ1 : ρ < 1 := by
    have hpos : 0 < (1 : ℝ) / K := div_pos one_pos (by exact_mod_cast hK)
    exact sub_lt_self 1 hpos
  have hpow : Tendsto (fun M : ℕ => ρ ^ M) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hρ0 hρ1
  have hcoeff : Tendsto (fun M => atomA ι K * (1 - ρ ^ M)) atTop (𝓝 (atomA ι K)) := by
    have hsub : Tendsto (fun M : ℕ => (1 : ℝ) - ρ ^ M) atTop (𝓝 ((1 : ℝ) - 0)) :=
      tendsto_const_nhds.sub hpow
    have hmul : Tendsto (fun M => atomA ι K * ((1 : ℝ) - ρ ^ M)) atTop
        (𝓝 (atomA ι K * ((1 : ℝ) - 0))) :=
      hsub.const_mul (atomA ι K)
    simp only [sub_zero, mul_one] at hmul
    exact hmul
  refine le_of_tendsto' hcoeff ?_
  intro M
  exact le_trans (diagPartial_ge ι hK M) (le_csSup (diagPartial_bdd ι) ⟨M, rfl⟩)

theorem atomQ_le_diagMass (ι : ITree) : atomQ ι ≤ diagMass ι := by
  refine csSup_le (Set.range_nonempty _) ?_
  intro t ht
  rcases ht with ⟨K, rfl⟩
  cases K with
  | zero =>
      exact le_trans (atomA_mono ι (Nat.zero_le 1)) (atomA_le_diagMass ι Nat.one_pos)
  | succ K =>
      exact atomA_le_diagMass ι (Nat.succ_pos K)

theorem diagMass_eq_atomQ (ι : ITree) : diagMass ι = atomQ ι :=
  le_antisymm (diagMass_le_atomQ ι) (atomQ_le_diagMass ι)

#print axioms greedy_head_lower
#print axioms horizon_head
#print axioms greedy_prefix_le_topMass
#print axioms atomA_eq_iInf
#print axioms diagMass_eq_atomQ

end CausalSpectrum
end


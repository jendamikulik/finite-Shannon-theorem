/-
Focusing a compact space of candidate models.

Closed conditions give a nested sequence of nonempty compact sets.
Their intersection is nonempty. It is a single point if and only if
the diameters tend to zero.

The intersection theorem is Mathlib's Cantor theorem for compact sets.
The diameter criterion is proved here: two points in the intersection
cannot stay a fixed distance apart once every set is smaller than that
distance, and a diameter bounded away from zero produces two such points.

Not proved: that the conditions are the right ones, or that the point
is the world.
-/
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.Order.Filter.AtTopBot.Basic

open Filter Metric Set
open scoped Topology

namespace CausalSpectrum
namespace Focus

variable {X : Type*} [MetricSpace X] [CompactSpace X]

/-- Candidate sets after the first `n` closed conditions. -/
def candidates (A : ℕ → Set X) : ℕ → Set X
  | 0 => univ
  | n + 1 => candidates A n ∩ A n

theorem candidates_anti (A : ℕ → Set X) (n : ℕ) :
    candidates A (n + 1) ⊆ candidates A n :=
  fun _ hx => hx.1

theorem candidates_le (A : ℕ → Set X) {m n : ℕ} (h : m ≤ n) :
    candidates A n ⊆ candidates A m := by
  induction n, h using Nat.le_induction with
  | base => exact subset_rfl
  | succ n _ ih => exact (candidates_anti A n).trans ih

theorem candidates_closed (A : ℕ → Set X) (hA : ∀ n, IsClosed (A n)) (n : ℕ) :
    IsClosed (candidates A n) := by
  induction n with
  | zero => exact isClosed_univ
  | succ n ih => exact ih.inter (hA n)

/-- Nested nonempty closed sets in a compact space have nonempty intersection. -/
theorem focus_nonempty (A : ℕ → Set X) (hA : ∀ n, IsClosed (A n))
    (hne : ∀ n, (candidates A n).Nonempty) :
    (⋂ n, candidates A n).Nonempty :=
  IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (candidates A) (candidates_anti A) hne (by simpa [candidates] using isCompact_univ)
    (candidates_closed A hA)

theorem diam_anti (A : ℕ → Set X) {m n : ℕ} (h : m ≤ n) :
    diam (candidates A n) ≤ diam (candidates A m) :=
  diam_mono (candidates_le A h) (isCompact_univ.isBounded.subset (subset_univ _))

/-- If every diameter is small, two points of the intersection coincide. -/
theorem unique_of_diam (A : ℕ → Set X) (hA : ∀ n, IsClosed (A n))
    (hne : ∀ n, (candidates A n).Nonempty)
    (hdiam : Tendsto (fun n => diam (candidates A n)) atTop (𝓝 0)) :
    ∃ x, ⋂ n, candidates A n = {x} := by
  obtain ⟨x, hx⟩ := focus_nonempty A hA hne
  refine ⟨x, ?_⟩
  ext y
  constructor
  · intro hy
    rw [Metric.tendsto_atTop] at hdiam
    have hdist : dist x y = 0 := by
      refine le_antisymm ?_ dist_nonneg
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨N, hN⟩ := hdiam ε hε
      have hxN : x ∈ candidates A N := mem_iInter.mp hx N
      have hyN : y ∈ candidates A N := mem_iInter.mp hy N
      have hbdd : Bornology.IsBounded (candidates A N) :=
        isCompact_univ.isBounded.subset (subset_univ _)
      have hle := dist_le_diam_of_mem hbdd hxN hyN
      have hsmall : diam (candidates A N) < ε := by
        have := hN N le_rfl
        simpa [Real.dist_0_eq_abs, abs_of_nonneg (diam_nonneg (s := candidates A N))] using this
      linarith
    exact (dist_eq_zero.mp hdist) ▸ mem_singleton x
  · intro hy
    rw [mem_singleton_iff.mp hy]
    exact hx

/-- A diameter bounded away from zero leaves two points in the intersection. -/
theorem diam_of_unique (A : ℕ → Set X) (hA : ∀ n, IsClosed (A n))
    (_hne : ∀ n, (candidates A n).Nonempty)
    (hsing : ∃ x, ⋂ n, candidates A n = {x}) :
    Tendsto (fun n => diam (candidates A n)) atTop (𝓝 0) := by
  classical
  rw [Metric.tendsto_atTop]
  intro ε hε
  by_contra h
  push Not at h
  have hstay : ∀ n, ε ≤ diam (candidates A n) := by
    intro n
    obtain ⟨m, hm, hdiam⟩ := h n
    have hdiam' : ε ≤ diam (candidates A m) := by
      simpa [Real.dist_0_eq_abs, abs_of_nonneg (diam_nonneg (s := candidates A m))] using hdiam
    exact le_trans hdiam' (diam_anti A hm)
  have hpair : ∀ n, ∃ x ∈ candidates A n, ∃ y ∈ candidates A n, ε / 2 < dist x y := by
    intro n
    by_contra hnone
    push Not at hnone
    have hle : diam (candidates A n) ≤ ε / 2 :=
      diam_le_of_forall_dist_le (by linarith : (0 : ℝ) ≤ ε / 2)
        fun x hx y hy => hnone x hx y hy
    linarith [hstay n]
  choose x hx y hy hdist using hpair
  obtain ⟨p, -, φ, hφ, hp⟩ :=
    (isCompact_univ (X := X × X)).isSeqCompact.subseq_of_frequently_in
      (show ∃ᶠ n in atTop, (x n, y n) ∈ (univ : Set (X × X)) from
        Frequently.of_forall fun _ => mem_univ _)
  rcases p with ⟨a, b⟩
  have ha : Tendsto (fun k => x (φ k)) atTop (𝓝 a) :=
    (continuous_fst.tendsto (a, b)).comp hp
  have hb : Tendsto (fun k => y (φ k)) atTop (𝓝 b) :=
    (continuous_snd.tendsto (a, b)).comp hp
  have hxa : ∀ m, a ∈ candidates A m := by
    intro m
    apply (candidates_closed A hA m).mem_of_tendsto ha
    refine eventually_atTop.mpr ⟨m, ?_⟩
    intro k hk
    have hφk : k ≤ φ k := hφ.le_apply
    exact candidates_le A (le_trans hk hφk) (hx (φ k))
  have hyb : ∀ m, b ∈ candidates A m := by
    intro m
    apply (candidates_closed A hA m).mem_of_tendsto hb
    refine eventually_atTop.mpr ⟨m, ?_⟩
    intro k hk
    have hφk : k ≤ φ k := hφ.le_apply
    exact candidates_le A (le_trans hk hφk) (hy (φ k))
  have hlim : ε / 2 ≤ dist a b := by
    have hpair_tend : Tendsto (fun k => (x (φ k), y (φ k))) atTop (𝓝 (a, b)) := by
      simpa [nhds_prod_eq] using ha.prodMk hb
    exact ge_of_tendsto ((continuous_dist.tendsto (a, b)).comp hpair_tend)
      (Filter.Eventually.of_forall fun k => le_of_lt (hdist (φ k)))
  obtain ⟨z, hz⟩ := hsing
  have ha' : a = z := by
    have : a ∈ ⋂ n, candidates A n := mem_iInter.mpr hxa
    simpa [hz] using this
  have hb' : b = z := by
    have : b ∈ ⋂ n, candidates A n := mem_iInter.mpr hyb
    simpa [hz] using this
  have : dist a b = 0 := by simpa [ha', hb'] using dist_self z
  linarith

/-- Unique focus if and only if the diameters vanish. -/
theorem unique_iff_diam (A : ℕ → Set X) (hA : ∀ n, IsClosed (A n))
    (hne : ∀ n, (candidates A n).Nonempty) :
    (∃ x, ⋂ n, candidates A n = {x}) ↔
      Tendsto (fun n => diam (candidates A n)) atTop (𝓝 0) :=
  ⟨diam_of_unique A hA hne, unique_of_diam A hA hne⟩

end Focus
end CausalSpectrum

/-
The finite-tree consequences that sit directly on `one_seed_shannon`.

This is the 1:1 transfer of the distributional comparison, the Wasserstein
identity, and exact min-entropy from `causal_spectrum.pdf` (5 October 2026),
Lemma 8 and Theorem 5. The square-root asymptotic, the logarithmic regime,
and the crash-pair certificate are not in this file.

`W₁` is the one-dimensional identity used in the note:
`∫ |F - G| =` the entropy gap, once `seedCDF ≤ F⋆`.
-/
import CausalSeed.Entropy

noncomputable section
open Classical MeasureTheory Set
namespace CausalSpectrum

theorem cdfGap_eq {T : Tree} (atoms : List (Atom T)) (t : ℝ) :
    Fstar T t - seedCDF atoms t =
      (1 - seedCDF atoms t) - (1 - Fstar T t) := by
  ring

theorem cdfGap_nonneg {T : Tree} {atoms : List (Atom T)}
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (t : ℝ) :
    0 ≤ Fstar T t - seedCDF atoms t :=
  sub_nonneg.mpr (seedCDF_le_Fstar hexact hpos t)

theorem integrableOn_cdfGap {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    IntegrableOn (fun t : ℝ => Fstar T t - seedCDF atoms t) (Ioi (0 : ℝ)) := by
  have hsub : IntegrableOn
      (fun t : ℝ => (1 - seedCDF atoms t) - (1 - Fstar T t)) (Ioi (0 : ℝ)) :=
    (integrableOn_one_sub_seed atoms hpos hle htot).sub (integrableOn_one_sub_Fstar T)
  refine hsub.congr_fun ?_ measurableSet_Ioi
  intro t _
  exact (cdfGap_eq atoms t).symm

theorem integral_cdfGap {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    ∫ t in Ioi (0 : ℝ), (Fstar T t - seedCDF atoms t) =
      seedShannon atoms - envelopeMean T := by
  have hfun : EqOn (fun t : ℝ => Fstar T t - seedCDF atoms t)
      (fun t : ℝ => (1 - seedCDF atoms t) - (1 - Fstar T t)) (Ioi 0) := by
    intro t _
    exact cdfGap_eq atoms t
  rw [setIntegral_congr_fun measurableSet_Ioi hfun]
  rw [integral_sub (integrableOn_one_sub_seed atoms hpos hle htot).integrable
      (integrableOn_one_sub_Fstar T).integrable]
  rw [integral_one_sub_seed atoms hpos hle htot, integral_one_sub_Fstar]

/-- Lemma 8. For an exact seed the entropy excess equals the L¹ distance of the
distribution functions. On the line that distance is `W₁`. -/
theorem wasserstein_gap {T : Tree} {atoms : List (Atom T)}
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    ∫ t in Ioi (0 : ℝ), |Fstar T t - seedCDF atoms t| =
      seedShannon atoms - envelopeMean T := by
  have hfun : EqOn (fun t : ℝ => |Fstar T t - seedCDF atoms t|)
      (fun t : ℝ => Fstar T t - seedCDF atoms t) (Ioi 0) := by
    intro t _
    exact abs_of_nonneg (cdfGap_nonneg hexact hpos t)
  rw [setIntegral_congr_fun measurableSet_Ioi hfun]
  exact integral_cdfGap atoms hpos hle htot

/-- The same greedy seed as `one_seed_shannon`, with the Wasserstein identity. -/
theorem one_seed_wasserstein (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧
      (∀ a ∈ atoms, 0 < a.1) ∧
      totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ =
          if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      ∫ t in Ioi (0 : ℝ), |Fstar T t - seedCDF atoms t| =
        seedShannon atoms - envelopeMean T := by
  obtain ⟨atoms, ht⟩ :=
    greedyTrace_exists (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T)
  have hbounds := greedy_atom_bounds ht
  obtain ⟨-, -, hsum, hrep⟩ :=
    greedyTrace_properties ht (Field.p_isFlow T) (Field.p_nonneg T)
  have htot : totalWeight atoms = 1 := by simpa using hsum
  have hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ =
        if CompatiblePolicy ℓ π then leafMass ℓ else 0 := by
    intro π ℓ
    rw [transcriptWeight_eq, hrep]
    have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
      simpa [Field.p] using leafValue_probability T 1 ℓ
    rw [hp]
  refine ⟨atoms, ht, hbounds.1, htot, hexact, ?_⟩
  exact wasserstein_gap hexact hbounds.1 hbounds.2 htot

/-! Survival function of `W = A(1+E)` from the note, written without a
probability space: mass `1/2` at `0`, none on `(0,1)`, and `2^{-s}` after `1`. -/

noncomputable def wSurvival (s : ℝ) : ℝ :=
  if s ≤ 0 then 1 else if s < 1 then 1 / 2 else (2 : ℝ) ^ (-s)

theorem wSurvival_eq_psi (s : ℝ) :
    wSurvival s = psi ((2 : ℝ) ^ (-s)) := by
  unfold wSurvival psi
  by_cases hs : s ≤ 0
  · have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (-s) := by
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-s)]
      refine (Real.one_le_exp_iff).2 ?_
      exact mul_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)) (neg_nonneg.mpr hs)
    rw [if_pos hs]
    have hnot : ¬ (2 : ℝ) ^ (-s) ≤ 1 / 2 := by
      have : (1 / 2 : ℝ) < 1 := by norm_num
      linarith
    rw [if_neg hnot, if_neg (not_lt.mpr hge)]
  · rw [if_neg hs]
    by_cases hs1 : s < 1
    · rw [if_pos hs1]
      have hlt : (1 / 2 : ℝ) < (2 : ℝ) ^ (-s) := by
        have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num
        rw [← hhalf]
        exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith : (-1 : ℝ) < -s)
      rw [if_neg (not_le.mpr hlt)]
      have hlt1 : (2 : ℝ) ^ (-s) < 1 := by
        rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-s)]
        refine (Real.exp_lt_one_iff).2 ?_
        exact mul_neg_of_pos_of_neg (Real.log_pos (by norm_num : (1 : ℝ) < 2))
          (by linarith : -s < 0)
      rw [if_pos hlt1]
    · rw [if_neg hs1]
      have hle : (2 : ℝ) ^ (-s) ≤ 1 / 2 := by
        have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num
        rw [← hhalf]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith : -s ≤ -1)
      rw [if_pos hle]

/-- Upper half of the stochastic sandwich, at the dyadic cutoff `δ = 2^{-t}`.
`smallWeight` is `P(J ≥ t)`. The right-hand side is `E[ψ(2^{Z-t})]`,
which the note identifies with `P(Z+W ≥ t)`. -/
theorem survival_le_wMixture {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) (t : ℝ) :
    smallWeight atoms ((2 : ℝ) ^ (-t)) ≤
      (Finset.range (infoValues T).length).sum (fun i =>
        envInc T i * wSurvival (t -
          if h : i < (infoValues T).length then (infoValues T)[i] else 0)) := by
  have hδ : 0 ≤ (2 : ℝ) ^ (-t) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) (-t))
  have hmaj := smallWeight_le_envelope ht ((2 : ℝ) ^ (-t)) hδ
  refine le_trans hmaj ?_
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i < (infoValues T).length := Finset.mem_range.mp hi
  have hpsi : majorantAt T ((2 : ℝ) ^ (-t)) i =
      psi ((2 : ℝ) ^ (-t) * (2 : ℝ) ^ ((infoValues T)[i])) := by
    simp [majorantAt, hi']
  rw [hpsi]
  have hpow : (2 : ℝ) ^ (-t) * (2 : ℝ) ^ ((infoValues T)[i]) =
      (2 : ℝ) ^ ((infoValues T)[i] - t) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2) (-t) ((infoValues T)[i])]
    congr 1
    ring
  rw [hpow]
  have hsurv : psi ((2 : ℝ) ^ ((infoValues T)[i] - t)) =
      wSurvival (t - (infoValues T)[i]) := by
    rw [wSurvival_eq_psi (t - (infoValues T)[i])]
    congr 1
    rw [show -(t - (infoValues T)[i]) = (infoValues T)[i] - t by ring]
  rw [hsurv]
  simp [hi']

/-! Theorem 5. No exact atom is heavier than the root bottleneck, and the
greedy seed attains it. Min-entropy is `infoMass` of that weight. -/

theorem representedLeaf_nonneg {T : Tree} (atoms : List (Atom T)) (ℓ : Leaf T)
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) :
    0 ≤ representedLeaf atoms ℓ := by
  classical
  induction atoms with
  | nil =>
      unfold representedLeaf
      simp
  | cons b tail ih =>
      have hb : 0 ≤ b.1 := hnn b (by simp)
      have htail : ∀ a ∈ tail, 0 ≤ a.1 := fun a ha => hnn a (by simp [ha])
      unfold representedLeaf
      simp only [List.map_cons, List.sum_cons]
      have hterm : 0 ≤ (if CompatibleStrategy ℓ b.2 then b.1 else 0) := by
        split_ifs <;> linarith
      exact add_nonneg hterm (ih htail)

theorem representedLeaf_ge_atom {T : Tree} (atoms : List (Atom T)) (ℓ : Leaf T)
    {a : Atom T} (ha : a ∈ atoms) (hnn : ∀ b ∈ atoms, 0 ≤ b.1)
    (hc : CompatibleStrategy ℓ a.2) :
    a.1 ≤ representedLeaf atoms ℓ := by
  classical
  induction atoms with
  | nil => cases ha
  | cons b tail ih =>
      have hb : 0 ≤ b.1 := hnn b (by simp)
      have htail : ∀ c ∈ tail, 0 ≤ c.1 := fun c hc => hnn c (by simp [hc])
      have hsplit : representedLeaf (b :: tail) ℓ =
          (if CompatibleStrategy ℓ b.2 then b.1 else 0) + representedLeaf tail ℓ := by
        unfold representedLeaf
        simp [List.map_cons, List.sum_cons]
      rw [hsplit]
      rcases List.mem_cons.mp ha with rfl | ha
      · simp [hc]
        exact representedLeaf_nonneg tail ℓ htail
      · have hterm : 0 ≤ (if CompatibleStrategy ℓ b.2 then b.1 else 0) := by
          split_ifs <;> linarith
        exact le_trans (ih ha htail) (le_add_of_nonneg_left hterm)

theorem exact_atom_le_bottleneck {T : Tree} {atoms : List (Atom T)}
    (hrep : ∀ ℓ : Leaf T, representedLeaf atoms ℓ = leafValue (Field.p T) ℓ)
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) {a : Atom T} (ha : a ∈ atoms) :
    a.1 ≤ bottleneck (Field.p T) := by
  obtain ⟨ℓ, hc, he⟩ := strategyFloor_attained_leaf (Field.p T) a.2
  have hge := representedLeaf_ge_atom atoms ℓ ha hnn hc
  rw [hrep ℓ, he] at hge
  exact le_trans hge (strategyFloor_le_bottleneck (Field.p T) a.2)

theorem greedy_attains_bottleneck {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) :
    ∃ a ∈ atoms, a.1 = bottleneck (Field.p T) := by
  cases ht with
  | done r hz =>
      simp [Field.root_p] at hz
  | step tail hr next =>
      exact ⟨(bottleneck (Field.p T), maximizingStrategy (Field.p T)), by simp, rfl⟩

theorem bottleneck_p_pos (T : Tree) : 0 < bottleneck (Field.p T) :=
  positive_root_implies_positive_bottleneck (Field.p_isFlow T) (Field.p_nonneg T)
    (by simp [Field.p])

theorem bottleneck_p_le_one (T : Tree) : bottleneck (Field.p T) ≤ 1 := by
  simpa [Field.root_p] using
    bottleneck_le_root (Field.p_isFlow T) (Field.p_nonneg T)

/-- Theorem 5, first claim. The greedy atom of weight `B_p(∅)` realises
min-entropy, and every atom of every exact decomposition is at most that heavy. -/
theorem exact_min_entropy (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧
      (∃ a ∈ atoms, a.1 = bottleneck (Field.p T)) ∧
      (∀ a ∈ atoms, a.1 ≤ bottleneck (Field.p T)) ∧
      infoMass (bottleneck (Field.p T)) =
        -Real.logb 2 (bottleneck (Field.p T)) ∧
      ∀ atoms' : List (Atom T),
        (∀ ℓ, representedLeaf atoms' ℓ = leafValue (Field.p T) ℓ) →
        (∀ a ∈ atoms', 0 ≤ a.1) →
        ∀ a ∈ atoms', a.1 ≤ bottleneck (Field.p T) := by
  obtain ⟨atoms, ht⟩ :=
    greedyTrace_exists (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T)
  obtain ⟨hpos, -, -, -⟩ :=
    greedyTrace_properties ht (Field.p_isFlow T) (Field.p_nonneg T)
  refine ⟨atoms, ht, greedy_attains_bottleneck ht, ?_, ?_, ?_⟩
  · intro a ha
    exact (hpos a ha).2
  · rfl
  · intro atoms' hrep hnn a ha
    exact exact_atom_le_bottleneck hrep hnn ha

#print axioms wasserstein_gap
#print axioms one_seed_wasserstein
#print axioms survival_le_wMixture
#print axioms exact_min_entropy

end CausalSpectrum

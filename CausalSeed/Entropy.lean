/-
Finite Shannon theorem for one exact causal seed.
Depends on the compiled kernel in `Spectrum.lean`.
-/
import CausalSeed.Spectrum
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Classical
namespace CausalSpectrum

noncomputable instance : DecidableEq ℝ := fun a b => propDecidable (a = b)

noncomputable instance : DecidableRel ((· ≤ ·) : ℝ → ℝ → Prop) :=
  fun a b => propDecidable (a ≤ b)

noncomputable instance : DecidableRel ((· < ·) : ℝ → ℝ → Prop) :=
  fun a b => propDecidable (a < b)

/-! Policies are finite, by the same structural recursion as leaves. -/

noncomputable instance policyFintype : (T : Tree) → Fintype (Policy T)
  | .leaf => by
      unfold Policy
      exact Fintype.ofSubsingleton PUnit.unit
  | .node nA hA nY hY K Kpos Ksum child => by
      letI : ∀ a y, Fintype (Policy (child a y)) :=
        fun a y => policyFintype (child a y)
      unfold Policy
      infer_instance

def defaultPolicy : (T : Tree) → Policy T
  | .leaf => PUnit.unit
  | .node nA hA nY hY _ _ _ child =>
      (⟨0, hA⟩, fun a y => defaultPolicy (child a y))

def defaultLeaf : (T : Tree) → Leaf T
  | .leaf => PUnit.unit
  | .node nA hA nY hY _ _ _ child =>
      let a : Fin nA := ⟨0, hA⟩
      ⟨a, ⟨0, hY a⟩, defaultLeaf (child a ⟨0, hY a⟩)⟩

/-! Self-information and the ordered list of values that actually occur. -/

noncomputable def infoMass (q : ℝ) : ℝ := -Real.logb 2 q

theorem leafMass_le_one {T : Tree} (ℓ : Leaf T) : leafMass ℓ ≤ 1 := by
  have h := leafValue_le_root (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T) ℓ
  have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
    simpa [Field.p] using leafValue_probability T 1 ℓ
  simpa [hp, Field.root_p] using h

theorem infoMass_nonneg {T : Tree} (ℓ : Leaf T) : 0 ≤ infoMass (leafMass ℓ) := by
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2)
    (leafMass_pos ℓ) (leafMass_le_one ℓ)
  rw [Real.logb_one] at hlog
  simpa [infoMass] using neg_nonneg.mpr hlog

theorem div_eq_rpow_info {p : ℝ} (hp : 0 < p) (δ : ℝ) :
    δ / p = δ * (2 : ℝ) ^ infoMass p := by
  unfold infoMass
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hp,
    div_eq_mul_inv]

noncomputable def infoValues (T : Tree) : List ℝ :=
  (((Finset.univ : Finset (Leaf T)).toList).map (fun ℓ => infoMass (leafMass ℓ))).dedup.insertionSort
    (· ≤ ·)

theorem mem_infoValues {T : Tree} {z : ℝ} :
    z ∈ infoValues T ↔ ∃ ℓ : Leaf T, infoMass (leafMass ℓ) = z := by
  unfold infoValues
  rw [List.mem_insertionSort, List.mem_dedup, List.mem_map]
  constructor
  · rintro ⟨ℓ, hℓ, rfl⟩
    exact ⟨ℓ, rfl⟩
  · rintro ⟨ℓ, rfl⟩
    exact ⟨ℓ, Finset.mem_toList.mpr (Finset.mem_univ ℓ), rfl⟩

theorem nodup_infoValues (T : Tree) : (infoValues T).Nodup := by
  unfold infoValues
  exact (List.perm_insertionSort _ _).nodup_iff.mpr (List.nodup_dedup _)

theorem sortedLE_infoValues (T : Tree) : (infoValues T).SortedLE := by
  unfold infoValues
  exact List.sortedLE_insertionSort
    (l := ((((Finset.univ : Finset (Leaf T)).toList).map
      (fun ℓ => infoMass (leafMass ℓ))).dedup))

theorem sortedLT_infoValues (T : Tree) : (infoValues T).SortedLT :=
  (List.sortedLT_iff_nodup_and_sortedLE).2 ⟨nodup_infoValues T, sortedLE_infoValues T⟩

theorem infoValues_ne_nil (T : Tree) : infoValues T ≠ [] := by
  intro h
  have hmem : infoMass (leafMass (defaultLeaf T)) ∈ infoValues T :=
    (mem_infoValues).2 ⟨defaultLeaf T, rfl⟩
  simp [h] at hmem

theorem infoValues_length_pos (T : Tree) : 0 < (infoValues T).length :=
  List.length_pos_of_ne_nil (infoValues_ne_nil T)

theorem info_get_strictMono (T : Tree) {i j : ℕ}
    (hi : i < (infoValues T).length) (hj : j < (infoValues T).length) (hij : i < j) :
    (infoValues T)[i] < (infoValues T)[j] :=
  (List.sortedLT_iff_getElem_lt_getElem_of_lt (l := infoValues T)).1
    (sortedLT_infoValues T) hij

/-! Linear combinations of a policy sum. -/

theorem policySum_zero : ∀ {T : Tree} (π : Policy T),
    policySum (fun _ : Leaf T => (0 : ℝ)) π = 0 := by
  intro T
  induction T with
  | leaf => intro π; rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro π
      simp only [policySum]
      apply Finset.sum_eq_zero
      intro y _
      exact ih π.1 y (π.2 π.1 y)

theorem policySum_add : ∀ {T : Tree} (f g : Leaf T → ℝ) (π : Policy T),
    policySum (fun ℓ => f ℓ + g ℓ) π = policySum f π + policySum g π := by
  intro T
  induction T with
  | leaf => intro f g π; rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro f g π
      simp only [policySum]
      have h := fun y =>
        ih π.1 y (fun ℓ => f ⟨π.1, y, ℓ⟩) (fun ℓ => g ⟨π.1, y, ℓ⟩) (π.2 π.1 y)
      simp_rw [h]
      exact Finset.sum_add_distrib

theorem policySum_mul : ∀ {T : Tree} (c : ℝ) (f : Leaf T → ℝ) (π : Policy T),
    policySum (fun ℓ => c * f ℓ) π = c * policySum f π := by
  intro T
  induction T with
  | leaf => intro c f π; rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro c f π
      simp only [policySum]
      have h := fun y =>
        ih π.1 y c (fun ℓ => f ⟨π.1, y, ℓ⟩) (π.2 π.1 y)
      simp_rw [h, Finset.mul_sum]

theorem policySum_range : ∀ {T : Tree} (n : ℕ) (f : ℕ → Leaf T → ℝ) (π : Policy T),
    policySum (fun ℓ => (Finset.range n).sum (fun i => f i ℓ)) π =
      (Finset.range n).sum (fun i => policySum (f i) π) := by
  intro T n
  induction n with
  | zero =>
      intro f π
      simp [policySum_zero]
  | succ n ih =>
      intro f π
      simp only [Finset.sum_range_succ]
      rw [policySum_add, ih]

theorem policySum_nonneg : ∀ {T : Tree} (f : Leaf T → ℝ) (π : Policy T),
    (∀ ℓ, 0 ≤ f ℓ) → 0 ≤ policySum f π := by
  intro T
  induction T with
  | leaf => intro f π hf; exact hf _
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro f π hf
      simp only [policySum]
      apply Finset.sum_nonneg
      intro y _
      exact ih π.1 y (fun ℓ => f ⟨π.1, y, ℓ⟩) (π.2 π.1 y) (fun ℓ => hf _)

theorem policySum_leafMass {T : Tree} (π : Policy T) :
    policySum (fun ℓ : Leaf T => leafMass ℓ) π = 1 := by
  have h := policySum_flow (Field.p T) π (Field.p_isFlow T)
  have hfun : (fun ℓ => leafValue (Field.p T) ℓ) = fun ℓ => leafMass ℓ := by
    funext ℓ
    simpa [Field.p] using leafValue_probability T 1 ℓ
  simpa [hfun, Field.root_p] using h

/-! Transcript CDFs and their lower envelope. -/

noncomputable def policyCDF (T : Tree) (π : Policy T) (t : ℝ) : ℝ :=
  policySum (fun ℓ => if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) π

noncomputable def levelMass (T : Tree) (π : Policy T) (z : ℝ) : ℝ :=
  policySum (fun ℓ => if infoMass (leafMass ℓ) = z then leafMass ℓ else 0) π

theorem policyCDF_mono {T : Tree} (π : Policy T) : Monotone (policyCDF T π) := by
  intro s t hst
  apply policySum_mono
  intro ℓ _
  by_cases hs : infoMass (leafMass ℓ) ≤ s
  · have ht : infoMass (leafMass ℓ) ≤ t := le_trans hs hst
    simp [hs, ht]
  · simp only [hs, ite_false]
    split_ifs with ht
    · exact (leafMass_pos ℓ).le
    · exact le_rfl

theorem policyCDF_nonneg {T : Tree} (π : Policy T) (t : ℝ) : 0 ≤ policyCDF T π t := by
  apply policySum_nonneg
  intro ℓ
  split_ifs
  · exact (leafMass_pos ℓ).le
  · exact le_rfl

theorem exists_min_policy (T : Tree) (t : ℝ) :
    ∃ π : Policy T, ∀ σ : Policy T, policyCDF T π t ≤ policyCDF T σ t := by
  have hne : (Finset.univ : Finset (Policy T)).Nonempty :=
    ⟨defaultPolicy T, Finset.mem_univ _⟩
  obtain ⟨π, -, hπ⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Policy T)) (fun σ => policyCDF T σ t) hne
  exact ⟨π, fun σ => hπ σ (Finset.mem_univ _)⟩

noncomputable def envelopePolicy (T : Tree) (t : ℝ) : Policy T :=
  Classical.choose (exists_min_policy T t)

noncomputable def Fstar (T : Tree) (t : ℝ) : ℝ :=
  policyCDF T (envelopePolicy T t) t

theorem Fstar_le (T : Tree) (t : ℝ) (π : Policy T) : Fstar T t ≤ policyCDF T π t :=
  Classical.choose_spec (exists_min_policy T t) π

theorem Fstar_nonneg (T : Tree) (t : ℝ) : 0 ≤ Fstar T t :=
  policyCDF_nonneg _ _

theorem Fstar_mono (T : Tree) : Monotone (Fstar T) := by
  intro s t hst
  exact le_trans (Fstar_le T s (envelopePolicy T t))
    (policyCDF_mono (envelopePolicy T t) hst)

theorem policyCDF_last {T : Tree} (π : Policy T) :
    policyCDF T π ((infoValues T)[(infoValues T).length - 1]'(by
      have h := infoValues_length_pos T
      omega)) = 1 := by
  have hz : ∀ ℓ : Leaf T,
      infoMass (leafMass ℓ) ≤
        (infoValues T)[(infoValues T).length - 1]'(by
          have h := infoValues_length_pos T
          omega) := by
    intro ℓ
    have hmem : infoMass (leafMass ℓ) ∈ infoValues T :=
      (mem_infoValues).2 ⟨ℓ, rfl⟩
    obtain ⟨j, hj, hjz⟩ := List.mem_iff_getElem.mp hmem
    have hlast : j ≤ (infoValues T).length - 1 := by
      have h := infoValues_length_pos T
      omega
    by_cases hje : j = (infoValues T).length - 1
    · subst hje
      exact le_of_eq hjz.symm
    · rw [← hjz]
      exact le_of_lt (info_get_strictMono T hj (by
        have h := infoValues_length_pos T
        omega) (by omega))
  have hfun : (fun ℓ : Leaf T =>
      if infoMass (leafMass ℓ) ≤
          (infoValues T)[(infoValues T).length - 1]'(by
            have h := infoValues_length_pos T
            omega)
        then leafMass ℓ else 0) = fun ℓ => leafMass ℓ := by
    funext ℓ
    simp [hz ℓ]
  simpa [policyCDF, hfun] using policySum_leafMass π

theorem Fstar_last (T : Tree) :
    Fstar T ((infoValues T)[(infoValues T).length - 1]'(by
      have h := infoValues_length_pos T
      omega)) = 1 := by
  simpa [Fstar] using policyCDF_last
    (envelopePolicy T ((infoValues T)[(infoValues T).length - 1]'(by
      have h := infoValues_length_pos T
      omega)))

/-! Abel summation for a nondecreasing weight. -/

def cumsum (μ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => cumsum μ n + μ n

theorem abel_identity (m : ℕ) (G μ : ℕ → ℝ) :
    (Finset.range m).sum (fun i => μ i * G i) =
      cumsum μ m * (if m = 0 then 0 else G (m - 1)) -
        (Finset.range (m - 1)).sum (fun k =>
          cumsum μ (k + 1) * (G (k + 1) - G k)) := by
  induction m with
  | zero =>
      simp [cumsum]
  | succ m ih =>
      by_cases hm : m = 0
      · subst hm
        simp [cumsum, Finset.sum_range_succ, Finset.sum_range_zero]
      · rw [Finset.sum_range_succ, ih]
        have hif : (if m = 0 then 0 else G (m - 1)) = G (m - 1) := by simp [hm]
        have hif2 : (if m + 1 = 0 then 0 else G (m + 1 - 1)) = G m := by simp
        have hrng : Finset.range (m + 1 - 1) = Finset.range m := by
          congr 1
        simp only [hif, hif2, hrng]
        have hsplit :
            (Finset.range m).sum (fun k => cumsum μ (k + 1) * (G (k + 1) - G k)) =
              (Finset.range (m - 1)).sum
                (fun k => cumsum μ (k + 1) * (G (k + 1) - G k)) +
              cumsum μ m * (G m - G (m - 1)) := by
          have ihm : m = (m - 1) + 1 := by omega
          conv_lhs => rw [ihm]
          rw [Finset.sum_range_succ]
          simp [show (m - 1) + 1 = m from by omega]
        rw [cumsum, hsplit]
        ring

theorem sum_le_of_larger_partials (m : ℕ) (G μ ν : ℕ → ℝ)
    (hG : ∀ i, i + 1 < m → G i ≤ G (i + 1))
    (hpart : ∀ k, k ≤ m → cumsum ν k ≤ cumsum μ k)
    (hend : cumsum μ m = cumsum ν m) :
    (Finset.range m).sum (fun i => μ i * G i) ≤
      (Finset.range m).sum (fun i => ν i * G i) := by
  rw [abel_identity m G μ, abel_identity m G ν, hend]
  have hterm : ∀ k, k < m - 1 →
      cumsum μ (k + 1) * (G (k + 1) - G k) ≥
        cumsum ν (k + 1) * (G (k + 1) - G k) := by
    intro k hk
    have hΔ : 0 ≤ G (k + 1) - G k := by
      have hlt : k + 1 < m := by omega
      linarith [hG k hlt]
    have hS : cumsum ν (k + 1) ≤ cumsum μ (k + 1) := hpart (k + 1) (by omega)
    exact mul_le_mul_of_nonneg_right hS hΔ
  have hsum :
      (Finset.range (m - 1)).sum (fun k => cumsum ν (k + 1) * (G (k + 1) - G k)) ≤
        (Finset.range (m - 1)).sum (fun k => cumsum μ (k + 1) * (G (k + 1) - G k)) := by
    apply Finset.sum_le_sum
    intro k hk
    exact hterm k (Finset.mem_range.mp hk)
  linarith

/-! Increments of the envelope, and the policy masses at the same points. -/

noncomputable def envInc (T : Tree) (i : ℕ) : ℝ :=
  if h : i < (infoValues T).length then
    Fstar T ((infoValues T)[i]) -
      (if hi : i = 0 then 0 else
        Fstar T ((infoValues T)[i - 1]'(by omega)))
  else 0

noncomputable def levelAt (T : Tree) (π : Policy T) (i : ℕ) : ℝ :=
  if h : i < (infoValues T).length then levelMass T π ((infoValues T)[i]) else 0

theorem envInc_nonneg (T : Tree) (i : ℕ) : 0 ≤ envInc T i := by
  unfold envInc
  by_cases h : i < (infoValues T).length
  · rw [dif_pos h]
    by_cases hi : i = 0
    · rw [dif_pos hi]
      simpa using Fstar_nonneg T ((infoValues T)[i])
    · rw [dif_neg hi]
      have hpred : i - 1 < (infoValues T).length := by omega
      have hlt : i - 1 < i := by omega
      exact sub_nonneg.mpr (Fstar_mono T (le_of_lt (info_get_strictMono T hpred h hlt)))
  · rw [dif_neg h]

theorem cumsum_envInc (T : Tree) (k : ℕ) (hk : k ≤ (infoValues T).length) :
    cumsum (envInc T) k =
      if k = 0 then 0 else
        Fstar T ((infoValues T)[k - 1]'(by
          have hlen := infoValues_length_pos T
          omega)) := by
  induction k with
  | zero => simp [cumsum]
  | succ k ih =>
      have hk' : k ≤ (infoValues T).length := by omega
      rw [cumsum, ih hk']
      by_cases hk0 : k = 0
      · subst hk0
        have hlt : 0 < (infoValues T).length := by omega
        simp [envInc, hlt]
      · have hlt : k < (infoValues T).length := by omega
        simp [envInc, hlt]

theorem cumsum_envInc_last (T : Tree) :
    cumsum (envInc T) (infoValues T).length = 1 := by
  rw [cumsum_envInc T _ le_rfl]
  have hpos := infoValues_length_pos T
  simp only [if_neg (by omega : (infoValues T).length ≠ 0)]
  simpa using Fstar_last T

theorem cumsum_eq_sum (μ : ℕ → ℝ) (n : ℕ) :
    cumsum μ n = (Finset.range n).sum μ := by
  induction n with
  | zero => simp [cumsum]
  | succ n ih => rw [cumsum, ih, Finset.sum_range_succ]

noncomputable def infoIndex (T : Tree) (ℓ : Leaf T) : ℕ :=
  (infoValues T).idxOf (infoMass (leafMass ℓ))

theorem infoIndex_lt (T : Tree) (ℓ : Leaf T) :
    infoIndex T ℓ < (infoValues T).length :=
  List.idxOf_lt_length_of_mem ((mem_infoValues).2 ⟨ℓ, rfl⟩)

theorem infoValues_get_index (T : Tree) (ℓ : Leaf T) :
    (infoValues T)[infoIndex T ℓ]'(infoIndex_lt T ℓ) = infoMass (leafMass ℓ) := by
  simpa [infoIndex] using (List.getElem_idxOf (infoIndex_lt T ℓ))

theorem info_get_le_iff (T : Tree) {i j : ℕ}
    (hi : i < (infoValues T).length) (hj : j < (infoValues T).length) :
    (infoValues T)[i] ≤ (infoValues T)[j] ↔ i ≤ j := by
  constructor
  · intro h
    by_contra hlt
    have : j < i := by omega
    exact not_le_of_gt (info_get_strictMono T hj hi this) h
  · intro hij
    rcases lt_or_eq_of_le hij with hlt | rfl
    · exact (info_get_strictMono T hi hj hlt).le
    · exact le_rfl

theorem level_term_eq (T : Tree) (ℓ : Leaf T) (i : ℕ) :
    (if hi : i < (infoValues T).length then
        if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
      else 0) =
    if i = infoIndex T ℓ then leafMass ℓ else 0 := by
  by_cases hi : i < (infoValues T).length
  · simp only [hi, dite_true]
    by_cases he : infoMass (leafMass ℓ) = (infoValues T)[i]
    · have hinj : i = infoIndex T ℓ :=
        (List.Nodup.getElem_inj_iff (nodup_infoValues T) (hi := hi)
          (hj := infoIndex_lt T ℓ)).1 <| by
            calc
              (infoValues T)[i] = infoMass (leafMass ℓ) := he.symm
              _ = (infoValues T)[infoIndex T ℓ]'(infoIndex_lt T ℓ) :=
                (infoValues_get_index T ℓ).symm
      simp [he, hinj]
    · have hne : i ≠ infoIndex T ℓ := by
        intro h
        subst h
        exact he (infoValues_get_index T ℓ).symm
      simp [he, hne]
  · have hne : i ≠ infoIndex T ℓ := by
      intro h
      exact hi (h ▸ infoIndex_lt T ℓ)
    simp [hi, hne]

theorem leaf_prefix_sum (T : Tree) (ℓ : Leaf T) (k : ℕ)
    (hk : k ≤ (infoValues T).length) (hk0 : k ≠ 0) :
    (Finset.range k).sum (fun i =>
        if hi : i < (infoValues T).length then
          if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
        else 0) =
      if infoMass (leafMass ℓ) ≤
          (infoValues T)[k - 1]'(by
            have hlen := infoValues_length_pos T
            omega)
        then leafMass ℓ else 0 := by
  have hterm : ∀ i, (if hi : i < (infoValues T).length then
      if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0 else 0) =
      if i = infoIndex T ℓ then leafMass ℓ else 0 :=
    fun i => level_term_eq T ℓ i
  simp_rw [hterm]
  rw [Finset.sum_ite_eq']
  have hj : infoIndex T ℓ < (infoValues T).length := infoIndex_lt T ℓ
  have hlast : k - 1 < (infoValues T).length := by
    have hlen := infoValues_length_pos T
    omega
  by_cases hjk : infoIndex T ℓ < k
  · have hmem : infoIndex T ℓ ∈ Finset.range k := Finset.mem_range.mpr hjk
    simp only [hmem, ite_true]
    have hle : infoMass (leafMass ℓ) ≤ (infoValues T)[k - 1] := by
      rw [← infoValues_get_index]
      exact (info_get_le_iff T hj hlast).2 (by omega)
    simp [hle]
  · have hnot : infoIndex T ℓ ∉ Finset.range k := by
      simpa [Finset.mem_range] using hjk
    simp only [hnot, ite_false]
    have hgt : ¬ infoMass (leafMass ℓ) ≤ (infoValues T)[k - 1] := by
      rw [← infoValues_get_index]
      exact not_le_of_gt <| info_get_strictMono T hlast hj (by omega)
    simp [hgt]

theorem cumsum_levelAt {T : Tree} (π : Policy T) (k : ℕ)
    (hk : k ≤ (infoValues T).length) :
    cumsum (levelAt T π) k =
      if k = 0 then 0 else
        policyCDF T π ((infoValues T)[k - 1]'(by
          have hlen := infoValues_length_pos T
          omega)) := by
  rw [cumsum_eq_sum]
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [if_neg hk0]
    unfold policyCDF
    calc
      (Finset.range k).sum (levelAt T π)
          = (Finset.range k).sum (fun i =>
              policySum (fun ℓ =>
                if hi : i < (infoValues T).length then
                  if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
                else 0) π) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hik : i < k := Finset.mem_range.mp hi
            have hi' : i < (infoValues T).length := by omega
            simp [levelAt, levelMass, hi']
      _ = policySum (fun ℓ =>
            (Finset.range k).sum (fun i =>
              if hi : i < (infoValues T).length then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
              else 0)) π := by
          symm
          exact policySum_range k (fun i ℓ =>
            if hi : i < (infoValues T).length then
              if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
            else 0) π
      _ = policySum (fun ℓ =>
            if infoMass (leafMass ℓ) ≤
                (infoValues T)[k - 1]'(by
                  have hlen := infoValues_length_pos T
                  omega)
              then leafMass ℓ else 0) π := by
          apply congrArg (fun f => policySum f π)
          funext ℓ
          exact leaf_prefix_sum T ℓ k hk hk0

theorem psi_scaled_mono (δ : ℝ) (hδ : 0 ≤ δ) :
    Monotone (fun x : ℝ => psi (δ * (2 : ℝ) ^ x)) := by
  intro x y hxy
  apply psi_mono
  apply mul_le_mul_of_nonneg_left _ hδ
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) x,
    Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) y]
  exact (Real.exp_le_exp).2 <|
    mul_le_mul_of_nonneg_left hxy (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))

noncomputable def majorantAt (T : Tree) (δ : ℝ) (i : ℕ) : ℝ :=
  if h : i < (infoValues T).length then
    psi (δ * (2 : ℝ) ^ ((infoValues T)[i]))
  else 0

theorem leaf_majorant_split (T : Tree) (ℓ : Leaf T) (δ : ℝ) :
    leafMass ℓ * psi (δ / leafMass ℓ) =
      (Finset.range (infoValues T).length).sum (fun i =>
        (if hi : i < (infoValues T).length then
            if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
          else 0) * majorantAt T δ i) := by
  have hdiv : δ / leafMass ℓ = δ * (2 : ℝ) ^ infoMass (leafMass ℓ) :=
    div_eq_rpow_info (leafMass_pos ℓ) δ
  have hterm : ∀ i,
      (if hi : i < (infoValues T).length then
          if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
        else 0) * majorantAt T δ i =
      if i = infoIndex T ℓ then
        leafMass ℓ * psi (δ * (2 : ℝ) ^ infoMass (leafMass ℓ)) else 0 := by
    intro i
    rw [level_term_eq]
    by_cases h : i = infoIndex T ℓ
    · subst h
      have hj := infoIndex_lt T ℓ
      rw [if_pos rfl]
      simp only [majorantAt, hj, dite_true]
      rw [infoValues_get_index]
      simp
    · rw [if_neg h, if_neg h, zero_mul]
  simp_rw [hterm, Finset.sum_ite_eq']
  have hmem : infoIndex T ℓ ∈ Finset.range (infoValues T).length :=
    Finset.mem_range.mpr (infoIndex_lt T ℓ)
  simp only [hmem, ite_true]
  rw [← hdiv]

theorem policy_majorant_levels {T : Tree} (π : Policy T) (δ : ℝ) :
    policySum (fun ℓ => leafMass ℓ * psi (δ / leafMass ℓ)) π =
      (Finset.range (infoValues T).length).sum
        (fun i => levelAt T π i * majorantAt T δ i) := by
  calc
    policySum (fun ℓ => leafMass ℓ * psi (δ / leafMass ℓ)) π
      = policySum (fun ℓ =>
          (Finset.range (infoValues T).length).sum (fun i =>
            (if hi : i < (infoValues T).length then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
              else 0) * majorantAt T δ i)) π := by
        apply congrArg (fun f => policySum f π)
        funext ℓ
        exact leaf_majorant_split T ℓ δ
    _ = (Finset.range (infoValues T).length).sum (fun i =>
          policySum (fun ℓ =>
            (if hi : i < (infoValues T).length then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
              else 0) * majorantAt T δ i) π) := by
        rw [policySum_range]
    _ = (Finset.range (infoValues T).length).sum
          (fun i => levelAt T π i * majorantAt T δ i) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi' : i < (infoValues T).length := Finset.mem_range.mp hi
        have hcomm : (fun ℓ : Leaf T =>
            (if hi : i < (infoValues T).length then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
              else 0) * majorantAt T δ i) =
            fun ℓ => majorantAt T δ i *
              (if hi : i < (infoValues T).length then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ else 0
              else 0) := by
          funext ℓ; ring
        rw [hcomm, policySum_mul]
        simp only [levelAt, hi', levelMass]
        rw [mul_comm]
        apply congrArg (fun s => s * majorantAt T δ i)
        apply congrArg (fun f => policySum f π)
        funext ℓ
        simp [hi']

theorem smallWeight_le_envelope {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) (δ : ℝ) (hδ : 0 ≤ δ) :
    smallWeight atoms δ ≤
      (Finset.range (infoValues T).length).sum
        (fun i => envInc T i * majorantAt T δ i) := by
  obtain ⟨π, hπ⟩ := greedy_refined_bound ht δ hδ
  rw [policy_majorant_levels] at hπ
  refine le_trans hπ ?_
  apply sum_le_of_larger_partials (infoValues T).length (majorantAt T δ)
      (levelAt T π) (envInc T)
  · intro i hi
    have hi0 : i < (infoValues T).length := by omega
    have hi1 : i + 1 < (infoValues T).length := hi
    have hle : (infoValues T)[i] ≤ (infoValues T)[i + 1] :=
      (info_get_le_iff T hi0 hi1).2 (by omega)
    simpa [majorantAt, hi0, hi1] using psi_scaled_mono δ hδ hle
  · intro k hk
    rw [cumsum_envInc T k hk, cumsum_levelAt π k hk]
    by_cases hk0 : k = 0
    · simp [hk0]
    · rw [if_neg hk0, if_neg hk0]
      exact Fstar_le T _ π
  · rw [cumsum_levelAt π (infoValues T).length le_rfl, cumsum_envInc_last]
    have hlen := infoValues_length_pos T
    rw [if_neg (by omega : (infoValues T).length ≠ 0)]
    exact policyCDF_last π

/-! One-dimensional integrals. The overhead is the integral of `ψ`. -/

open MeasureTheory Set

noncomputable def shannonOverhead : ℝ := (1 + 1 / Real.log 2) / 2

noncomputable def seedShannon {T : Tree} (atoms : List (Atom T)) : ℝ :=
  (atoms.map (fun a => a.1 * infoMass a.1)).sum

noncomputable def envelopeMean (T : Tree) : ℝ :=
  (Finset.range (infoValues T).length).sum (fun i =>
    envInc T i * if h : i < (infoValues T).length then (infoValues T)[i] else 0)

theorem weight_le_dyadic_iff {w t : ℝ} (hw : 0 < w) :
    w ≤ (2 : ℝ) ^ (-t) ↔ t ≤ infoMass w := by
  have hpow : 0 < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) (-t)
  have hlog : Real.logb 2 ((2 : ℝ) ^ (-t)) = -t :=
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := -t)
  rw [← Real.logb_le_logb (b := 2) (by norm_num : (1 : ℝ) < 2) hw hpow, hlog]
  unfold infoMass
  constructor <;> intro h <;> linarith

theorem weight_lt_dyadic_iff {w t : ℝ} (hw : 0 < w) :
    w < (2 : ℝ) ^ (-t) ↔ t < infoMass w := by
  have hpow : 0 < (2 : ℝ) ^ (-t) := Real.rpow_pos_of_pos (by norm_num) (-t)
  have hlog : Real.logb 2 ((2 : ℝ) ^ (-t)) = -t :=
    Real.logb_rpow (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) (x := -t)
  rw [← Real.logb_lt_logb_iff (b := 2) (by norm_num : (1 : ℝ) < 2) hw hpow, hlog]
  unfold infoMass
  constructor <;> intro h <;> linarith

theorem infoMass_of_unit_interval {w : ℝ} (hw : 0 < w) (hw1 : w ≤ 1) :
    0 ≤ infoMass w := by
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2) hw hw1
  rw [Real.logb_one] at hlog
  simpa [infoMass] using neg_nonneg.mpr hlog

theorem infoMass_anti {w p : ℝ} (hw : 0 < w) (hp : 0 < p) (hwle : w ≤ p) :
    infoMass p ≤ infoMass w := by
  have hlog := Real.logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2) hw hwle
  simpa [infoMass] using neg_le_neg hlog

theorem integrableOn_le_cutoff {z c : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun t : ℝ => if t ≤ z then c else 0) (Ioi (0 : ℝ)) := by
  have hU : Ioc 0 z ∪ Ioi z = Ioi 0 := Ioc_union_Ioi_eq_Ioi hz
  rw [← hU]
  refine IntegrableOn.union ?_ ?_
  · have hvol : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    refine (integrableOn_const (s := Ioc (0 : ℝ) z) (C := c) hvol).congr_fun ?_
      measurableSet_Ioc
    intro t ht
    simp [ht.2]
  · refine (integrableOn_zero (s := Ioi z) (μ := volume)).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp [not_le.mpr (mem_Ioi.mp ht)]

theorem integral_le_cutoff {z c : ℝ} (hz : 0 ≤ z) :
    ∫ t in Ioi (0 : ℝ), (if t ≤ z then c else 0) = c * z := by
  have hint := integrableOn_le_cutoff (c := c) hz
  have hU : Ioc 0 z ∪ Ioi z = Ioi 0 := Ioc_union_Ioi_eq_Ioi hz
  have hdis : Disjoint (Ioc 0 z) (Ioi z) := Ioc_disjoint_Ioi_same
  have hf1 : IntegrableOn (fun t : ℝ => if t ≤ z then c else 0) (Ioc 0 z) :=
    hint.mono_set (by rw [← hU]; exact subset_union_left)
  have hf2 : IntegrableOn (fun t : ℝ => if t ≤ z then c else 0) (Ioi z) :=
    hint.mono_set (by rw [← hU]; exact subset_union_right)
  rw [← hU, setIntegral_union hdis measurableSet_Ioi hf1 hf2]
  have h1 : ∫ t in Ioc 0 z, (if t ≤ z then c else 0) = ∫ _t in Ioc 0 z, c := by
    refine setIntegral_congr_fun measurableSet_Ioc ?_
    intro t ht
    simp [ht.2]
  have h2 : ∫ t in Ioi z, (if t ≤ z then c else 0) = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_), integral_zero]
    simp [not_le.mpr (mem_Ioi.mp ht)]
  rw [h1, h2, setIntegral_const, Real.volume_real_Ioc_of_le hz, smul_eq_mul]
  ring

theorem integrableOn_lt_cutoff {z c : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun t : ℝ => if t < z then c else 0) (Ioi (0 : ℝ)) := by
  rcases hz.eq_or_lt with rfl | hz
  · refine (integrableOn_zero (s := Ioi (0 : ℝ))).congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp [not_lt.mpr (le_of_lt (mem_Ioi.mp ht))]
  · have hU : Ioo 0 z ∪ Ici z = Ioi 0 := Ioo_union_Ici_eq_Ioi hz
    rw [← hU]
    refine IntegrableOn.union ?_ ?_
    · have hvol : volume (Ioo (0 : ℝ) z) ≠ ⊤ := by
        rw [Real.volume_Ioo]
        exact ENNReal.ofReal_ne_top
      refine (integrableOn_const (s := Ioo (0 : ℝ) z) (C := c) hvol).congr_fun ?_
        measurableSet_Ioo
      intro t ht
      simp [ht.2]
    · refine (integrableOn_zero (s := Ici z)).congr_fun ?_ measurableSet_Ici
      intro t ht
      simp [not_lt.mpr (mem_Ici.mp ht)]

theorem integral_lt_cutoff {z c : ℝ} (hz : 0 ≤ z) :
    ∫ t in Ioi (0 : ℝ), (if t < z then c else 0) = c * z := by
  rcases hz.eq_or_lt with rfl | hz
  · have hzero : EqOn (fun t : ℝ => if t < (0 : ℝ) then c else 0) (fun _ => (0 : ℝ)) (Ioi 0) := by
      intro t ht
      simp [not_lt.mpr (le_of_lt (mem_Ioi.mp ht))]
    rw [setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero, mul_zero]
  · have hint := integrableOn_lt_cutoff (c := c) hz.le
    have hU : Ioo 0 z ∪ Ici z = Ioi 0 := Ioo_union_Ici_eq_Ioi hz
    have hdis : Disjoint (Ioo (0 : ℝ) z) (Ici z) :=
      (Iio_disjoint_Ici (le_refl z)).mono Ioo_subset_Iio_self le_rfl
    have hf1 : IntegrableOn (fun t : ℝ => if t < z then c else 0) (Ioo 0 z) :=
      hint.mono_set (by rw [← hU]; exact subset_union_left)
    have hf2 : IntegrableOn (fun t : ℝ => if t < z then c else 0) (Ici z) :=
      hint.mono_set (by rw [← hU]; exact subset_union_right)
    rw [← hU, setIntegral_union hdis measurableSet_Ici hf1 hf2]
    have h1 : ∫ t in Ioo 0 z, (if t < z then c else 0) = ∫ _t in Ioo 0 z, c := by
      refine setIntegral_congr_fun measurableSet_Ioo ?_
      intro t ht
      simp [ht.2]
    have h2 : ∫ t in Ici z, (if t < z then c else 0) = 0 := by
      have hzero : EqOn (fun t : ℝ => if t < z then c else 0) (fun _ => (0 : ℝ)) (Ici z) := by
        intro t ht
        simp [not_lt.mpr (mem_Ici.mp ht)]
      rw [setIntegral_congr_fun measurableSet_Ici hzero, integral_zero]
    rw [h1, h2, setIntegral_const, Real.volume_real_Ioo_of_le hz.le, smul_eq_mul]
    ring

theorem integral_atom (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    ∫ t in Ioi (0 : ℝ), (if w ≤ (2 : ℝ) ^ (-t) then w else 0) = w * infoMass w := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?eq)]
  · exact integral_le_cutoff (c := w) (infoMass_of_unit_interval hw hw1)
  case eq =>
    by_cases h : w ≤ (2 : ℝ) ^ (-t)
    · simp [h, (weight_le_dyadic_iff hw).1 h]
    · have hnot : ¬ t ≤ infoMass w := by
        intro ht
        exact h ((weight_le_dyadic_iff hw).2 ht)
      simp [h, hnot]

theorem integrableOn_atom (w : ℝ) (hw : 0 < w) (hw1 : w ≤ 1) :
    IntegrableOn (fun t : ℝ => if w ≤ (2 : ℝ) ^ (-t) then w else 0) (Ioi (0 : ℝ)) := by
  refine (integrableOn_le_cutoff (c := w) (infoMass_of_unit_interval hw hw1)).congr_fun
    ?_ measurableSet_Ioi
  intro t _
  by_cases h : w ≤ (2 : ℝ) ^ (-t)
  · simp [h, (weight_le_dyadic_iff hw).1 h]
  · have hnot : ¬ t ≤ infoMass w := by
      intro ht
      exact h ((weight_le_dyadic_iff hw).2 ht)
    simp [h, hnot]

theorem smallWeight_cons {T : Tree} (a : Atom T) (tail : List (Atom T)) (δ : ℝ) :
    smallWeight (a :: tail) δ = (if a.1 ≤ δ then a.1 else 0) + smallWeight tail δ := by
  simp [smallWeight]

theorem seedShannon_cons {T : Tree} (a : Atom T) (tail : List (Atom T)) :
    seedShannon (a :: tail) = a.1 * infoMass a.1 + seedShannon tail := by
  simp [seedShannon]

theorem integrableOn_smallWeight {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1) :
    IntegrableOn (fun t : ℝ => smallWeight atoms ((2 : ℝ) ^ (-t))) (Ioi (0 : ℝ)) := by
  induction atoms with
  | nil => simp [smallWeight, integrableOn_zero]
  | cons a tail ih =>
      simp_rw [smallWeight_cons]
      exact (integrableOn_atom a.1 (hpos a (by simp)) (hle a (by simp))).add
        (ih (fun b hb => hpos b (by simp [hb])) (fun b hb => hle b (by simp [hb])))

theorem seedShannon_eq_integral {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1) :
    seedShannon atoms =
      ∫ t in Ioi (0 : ℝ), smallWeight atoms ((2 : ℝ) ^ (-t)) := by
  induction atoms with
  | nil =>
      simp [seedShannon, smallWeight, integral_zero]
  | cons a tail ih =>
      have hpos' : ∀ b ∈ tail, 0 < b.1 := fun b hb => hpos b (by simp [hb])
      have hle' : ∀ b ∈ tail, b.1 ≤ 1 := fun b hb => hle b (by simp [hb])
      have ha0 : 0 < a.1 := hpos a (by simp)
      have ha1 : a.1 ≤ 1 := hle a (by simp)
      simp_rw [seedShannon_cons, smallWeight_cons, ih hpos' hle']
      rw [integral_add (integrableOn_atom a.1 ha0 ha1).integrable
          (integrableOn_smallWeight tail hpos' hle').integrable,
        integral_atom a.1 ha0 ha1]

theorem psi_rpow_piece (z t : ℝ) :
    psi ((2 : ℝ) ^ (z - t)) =
      if t ≤ z then (1 : ℝ)
      else if t ≤ z + 1 then 1 / 2
      else (2 : ℝ) ^ (z - t) := by
  unfold psi
  set u : ℝ := (2 : ℝ) ^ (z - t)
  by_cases h1 : t ≤ z
  · have hone : (1 : ℝ) ≤ u :=
      Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by linarith : (0 : ℝ) ≤ z - t)
    have hhalf : ¬ u ≤ (1 : ℝ) / 2 := by
      have : (1 : ℝ) / 2 < 1 := by norm_num
      linarith
    have hlt : ¬ u < 1 := not_lt.mpr hone
    rw [if_pos h1, if_neg hhalf, if_neg hlt]
  · rw [if_neg h1]
    by_cases h2 : t ≤ z + 1
    · have hlt1 : u < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ) < 2)
          (by linarith : z - t < 0)
      have hge : (1 : ℝ) / 2 ≤ u := by
        have hpow : (2 : ℝ) ^ (-1 : ℝ) ≤ u :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
            (by linarith : (-1 : ℝ) ≤ z - t)
        rw [Real.rpow_neg_one] at hpow
        have hinv : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
        linarith
      rw [if_pos h2]
      by_cases hh : u ≤ (1 : ℝ) / 2
      · have heq : u = (1 : ℝ) / 2 := le_antisymm hh hge
        rw [if_pos hh, heq]
      · rw [if_neg hh, if_pos hlt1]
    · have hpow : u < (2 : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
          (by linarith : z - t < -1)
      rw [Real.rpow_neg_one] at hpow
      have hinv : (2 : ℝ)⁻¹ = (1 : ℝ) / 2 := by norm_num
      have hh : u ≤ (1 : ℝ) / 2 := by linarith
      rw [if_neg h2, if_pos hh]

theorem shannonOverhead_expand :
    shannonOverhead = 1 / 2 + 1 / (2 * Real.log 2) := by
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'
  unfold shannonOverhead
  field_simp [hlog]

theorem integral_exp_tail (z : ℝ) :
    ∫ t in Ioi (z + 1), (2 : ℝ) ^ (z - t) = 1 / (2 * Real.log 2) := by
  have hlogpos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha : -Real.log 2 < 0 := neg_lt_zero.mpr hlogpos
  have hfun : EqOn (fun t : ℝ => (2 : ℝ) ^ (z - t))
      (fun t => (2 : ℝ) ^ z * Real.exp (-Real.log 2 * t)) (Ioi (z + 1)) := by
    intro t _
    dsimp
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (z - t)]
    rw [show Real.log 2 * (z - t) = Real.log 2 * z + (-Real.log 2) * t by ring]
    rw [Real.exp_add]
    rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) z]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun]
  rw [integral_const_mul ((2 : ℝ) ^ z) (fun t : ℝ => Real.exp (-Real.log 2 * t))
    (μ := volume.restrict (Ioi (z + 1)))]
  rw [integral_exp_mul_Ioi ha (z + 1)]
  have hneg : -Real.log 2 ≠ 0 := ne_of_lt ha
  have hrewrite : -Real.exp ((-Real.log 2) * (z + 1)) / (-Real.log 2) =
      Real.exp ((-Real.log 2) * (z + 1)) / Real.log 2 := by
    field_simp [hneg]
  rw [hrewrite]
  have hexp : Real.exp ((-Real.log 2) * (z + 1)) = (2 : ℝ) ^ (-(z + 1)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  rw [hexp]
  have hmul : (2 : ℝ) ^ z * ((2 : ℝ) ^ (-(z + 1)) / Real.log 2) =
      ((2 : ℝ) ^ z * (2 : ℝ) ^ (-(z + 1))) / Real.log 2 := by
    field_simp [hlogpos.ne']
  rw [hmul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hadd : z + -(z + 1) = -1 := by ring
  rw [hadd, Real.rpow_neg_one]
  field_simp [hlogpos.ne']

theorem integrableOn_psi_ray {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun t : ℝ => psi ((2 : ℝ) ^ (z - t))) (Ioi (0 : ℝ)) := by
  let f : ℝ → ℝ := fun t => psi ((2 : ℝ) ^ (z - t))
  have hA : EqOn f (fun _ => (1 : ℝ)) (Ioc 0 z) := by
    intro t ht
    have ht' : t ≤ z := ht.2
    simp [f, psi_rpow_piece, ht']
  have hB : EqOn f (fun _ => (1 : ℝ) / 2) (Ioc z (z + 1)) := by
    intro t ht
    have hnot : ¬ t ≤ z := not_le.mpr ht.1
    have hle : t ≤ z + 1 := ht.2
    simp [f, psi_rpow_piece, hnot, hle]
  have hC : EqOn f (fun t => (2 : ℝ) ^ (z - t)) (Ioi (z + 1)) := by
    intro t ht
    have ht' : z + 1 < t := mem_Ioi.mp ht
    have hnot1 : ¬ t ≤ z := by linarith
    have hnot2 : ¬ t ≤ z + 1 := not_le.mpr ht'
    simp [f, psi_rpow_piece, hnot1, hnot2]
  have hvolA : volume (Ioc (0 : ℝ) z) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hvolB : volume (Ioc z (z + 1)) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hintA : IntegrableOn f (Ioc 0 z) :=
    (integrableOn_const (s := Ioc (0 : ℝ) z) (C := (1 : ℝ)) hvolA).congr_fun
      hA.symm measurableSet_Ioc
  have hintB : IntegrableOn f (Ioc z (z + 1)) :=
    (integrableOn_const (s := Ioc z (z + 1)) (C := (1 : ℝ) / 2) hvolB).congr_fun
      hB.symm measurableSet_Ioc
  have hintExp : IntegrableOn (fun t : ℝ => Real.exp (-Real.log 2 * t)) (Ioi (z + 1)) :=
    integrableOn_exp_mul_Ioi (by
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      linarith) (z + 1)
  have hintPow : IntegrableOn (fun t : ℝ => (2 : ℝ) ^ (z - t)) (Ioi (z + 1)) := by
    have hmul : Integrable (fun t : ℝ => (2 : ℝ) ^ z * Real.exp (-Real.log 2 * t))
        (volume.restrict (Ioi (z + 1))) :=
      Integrable.const_mul hintExp.integrable ((2 : ℝ) ^ z)
    refine IntegrableOn.congr_fun (by simpa [IntegrableOn] using hmul) ?_ measurableSet_Ioi
    intro t _
    dsimp
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (z - t),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) z]
    rw [show Real.log 2 * (z - t) = Real.log 2 * z + (-Real.log 2) * t by ring,
      Real.exp_add]
    ring
  have hintC : IntegrableOn f (Ioi (z + 1)) :=
    hintPow.congr_fun hC.symm measurableSet_Ioi
  have hU1 : Ioc 0 z ∪ Ioc z (z + 1) = Ioc 0 (z + 1) :=
    Ioc_union_Ioc_eq_Ioc hz (by linarith)
  have hU2 : Ioc 0 (z + 1) ∪ Ioi (z + 1) = Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ z + 1)
  have hintAB : IntegrableOn f (Ioc 0 (z + 1)) := by
    rw [← hU1]
    exact hintA.union hintB
  rw [← hU2]
  exact hintAB.union hintC

theorem integral_psi_ray {z : ℝ} (hz : 0 ≤ z) :
    ∫ t in Ioi (0 : ℝ), psi ((2 : ℝ) ^ (z - t)) = z + shannonOverhead := by
  let f : ℝ → ℝ := fun t => psi ((2 : ℝ) ^ (z - t))
  have hA : EqOn f (fun _ => (1 : ℝ)) (Ioc 0 z) := by
    intro t ht
    simp [f, psi_rpow_piece, ht.2]
  have hB : EqOn f (fun _ => (1 : ℝ) / 2) (Ioc z (z + 1)) := by
    intro t ht
    simp [f, psi_rpow_piece, not_le.mpr ht.1, ht.2]
  have hC : EqOn f (fun t => (2 : ℝ) ^ (z - t)) (Ioi (z + 1)) := by
    intro t ht
    have ht' : z + 1 < t := mem_Ioi.mp ht
    simp [f, psi_rpow_piece, (by linarith : ¬ t ≤ z), not_le.mpr ht']
  have hintA : IntegrableOn f (Ioc 0 z) :=
    (integrableOn_psi_ray hz).mono_set Ioc_subset_Ioi_self
  have hintB : IntegrableOn f (Ioc z (z + 1)) :=
    (integrableOn_psi_ray hz).mono_set (fun t ht => by
      have : 0 < t := lt_of_le_of_lt hz ht.1
      exact mem_Ioi.mpr this)
  have hintC : IntegrableOn f (Ioi (z + 1)) :=
    (integrableOn_psi_ray hz).mono_set (fun t ht => by
      have ht' : z + 1 < t := mem_Ioi.mp ht
      exact mem_Ioi.mpr (by linarith))
  have hU1 : Ioc 0 z ∪ Ioc z (z + 1) = Ioc 0 (z + 1) :=
    Ioc_union_Ioc_eq_Ioc hz (by linarith)
  have hU2 : Ioc 0 (z + 1) ∪ Ioi (z + 1) = Ioi 0 :=
    Ioc_union_Ioi_eq_Ioi (by linarith : (0 : ℝ) ≤ z + 1)
  have hdis1 : Disjoint (Ioc 0 z) (Ioc z (z + 1)) := Ioc_disjoint_Ioc_of_le le_rfl
  have hdis2 : Disjoint (Ioc 0 (z + 1)) (Ioi (z + 1)) := Ioc_disjoint_Ioi_same
  have hintIoc : IntegrableOn f (Ioc 0 (z + 1)) := by
    rw [← hU1]
    exact hintA.union hintB
  rw [← hU2, setIntegral_union hdis2 measurableSet_Ioi hintIoc hintC, ← hU1,
    setIntegral_union hdis1 measurableSet_Ioc hintA hintB]
  have iA : ∫ t in Ioc 0 z, f t = z := by
    rw [setIntegral_congr_fun measurableSet_Ioc hA, setIntegral_const,
      Real.volume_real_Ioc_of_le hz, smul_eq_mul]
    ring
  have iB : ∫ t in Ioc z (z + 1), f t = 1 / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc hB, setIntegral_const,
      Real.volume_real_Ioc_of_le (by linarith : z ≤ z + 1), smul_eq_mul]
    ring
  have iC : ∫ t in Ioi (z + 1), f t = 1 / (2 * Real.log 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hC, integral_exp_tail]
  rw [iA, iB, iC, shannonOverhead_expand]
  ring

theorem info_nonneg_get (T : Tree) {i : ℕ} (hi : i < (infoValues T).length) :
    0 ≤ (infoValues T)[i] := by
  have hmem : (infoValues T)[i] ∈ infoValues T :=
    List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩
  obtain ⟨ℓ, hℓ⟩ := (mem_infoValues).1 hmem
  rw [← hℓ]
  exact infoMass_nonneg ℓ

theorem majorant_dyadic (T : Tree) (t : ℝ) {i : ℕ} (hi : i < (infoValues T).length) :
    majorantAt T ((2 : ℝ) ^ (-t)) i =
      psi ((2 : ℝ) ^ ((infoValues T)[i] - t)) := by
  simp only [majorantAt, hi, dite_true]
  congr 1
  rw [mul_comm, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  ring

theorem greedy_atom_bounds {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) :
    (∀ a ∈ atoms, 0 < a.1) ∧ (∀ a ∈ atoms, a.1 ≤ 1) := by
  have hp := greedyTrace_properties ht (Field.p_isFlow T) (Field.p_nonneg T)
  refine ⟨fun a ha => (hp.1 a ha).1, fun a ha => ?_⟩
  exact le_trans (hp.1 a ha).2
    (by simpa [Field.root_p] using
      bottleneck_le_root (Field.p_isFlow T) (Field.p_nonneg T))

noncomputable def envPiece (T : Tree) (i : ℕ) (t : ℝ) : ℝ :=
  if h : i < (infoValues T).length then
    envInc T i * psi ((2 : ℝ) ^ ((infoValues T)[i] - t))
  else 0

theorem integrableOn_envPiece (T : Tree) (i : ℕ) :
    IntegrableOn (envPiece T i) (Ioi (0 : ℝ)) := by
  by_cases hi : i < (infoValues T).length
  · refine IntegrableOn.congr_fun
      (by simpa [IntegrableOn] using
        Integrable.const_mul (integrableOn_psi_ray (info_nonneg_get T hi)).integrable (envInc T i))
      ?_ measurableSet_Ioi
    intro t _
    simp [envPiece, hi]
  · refine (integrableOn_zero (s := Ioi (0 : ℝ))).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp [envPiece, hi]

theorem seedShannon_le_envelope {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1) :
    seedShannon atoms ≤ envelopeMean T + shannonOverhead := by
  let n := (infoValues T).length
  rw [seedShannon_eq_integral atoms hpos hle]
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      smallWeight atoms ((2 : ℝ) ^ (-t)) ≤
        (Finset.range n).sum (fun i => envPiece T i t) := by
    intro t _
    have hδ : 0 ≤ (2 : ℝ) ^ (-t) := (Real.rpow_pos_of_pos (by norm_num) (-t)).le
    refine le_trans (smallWeight_le_envelope ht _ hδ) ?_
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi' : i < (infoValues T).length := by
      simpa [n] using Finset.mem_range.mp hi
    rw [majorant_dyadic T t hi']
    unfold envPiece
    rw [dif_pos hi']
  have hintSW : IntegrableOn (fun t : ℝ => smallWeight atoms ((2 : ℝ) ^ (-t))) (Ioi (0 : ℝ)) :=
    integrableOn_smallWeight atoms hpos hle
  have hintSum : IntegrableOn
      (fun t : ℝ => (Finset.range n).sum (fun i => envPiece T i t)) (Ioi (0 : ℝ)) := by
    simpa [IntegrableOn] using
      integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) (Finset.range n)
        (f := fun i (t : ℝ) => envPiece T i t)
        (fun i _ => (integrableOn_envPiece T i).integrable)
  have hmono :
      (∫ t in Ioi (0 : ℝ), smallWeight atoms ((2 : ℝ) ^ (-t))) ≤
        ∫ t in Ioi (0 : ℝ), (Finset.range n).sum (fun i => envPiece T i t) :=
    setIntegral_mono_on hintSW hintSum measurableSet_Ioi hpoint
  have hinter :
      (∫ t in Ioi (0 : ℝ), (Finset.range n).sum (fun i => envPiece T i t)) =
        (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envPiece T i t) := by
    simpa using integral_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) (Finset.range n)
      (f := fun i (t : ℝ) => envPiece T i t)
      (fun i _ => (integrableOn_envPiece T i).integrable)
  have hsum :
      (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envPiece T i t) =
        envelopeMean T + shannonOverhead := by
    have hterm : (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envPiece T i t) =
        (Finset.range n).sum (fun i =>
          envInc T i * (if h : i < (infoValues T).length then (infoValues T)[i] else 0) +
            shannonOverhead * envInc T i) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      have hi' : i < (infoValues T).length := by
        simpa [n] using Finset.mem_range.mp hi
      simp only [envPiece, hi', dite_true]
      rw [integral_const_mul (envInc T i)
          (fun t : ℝ => psi ((2 : ℝ) ^ ((infoValues T)[i] - t)))
          (μ := volume.restrict (Ioi (0 : ℝ))),
        integral_psi_ray (info_nonneg_get T hi')]
      ring
    rw [hterm, Finset.sum_add_distrib]
    have hem : (Finset.range n).sum (fun i =>
        envInc T i * (if h : i < (infoValues T).length then (infoValues T)[i] else 0)) =
        envelopeMean T := by
      unfold envelopeMean
      dsimp [n]
    have hov : (Finset.range n).sum (fun i => shannonOverhead * envInc T i) =
        shannonOverhead := by
      rw [← Finset.mul_sum]
      dsimp [n]
      rw [← cumsum_eq_sum, cumsum_envInc_last, mul_one]
    rw [hem, hov]
  linarith

/-! Lower bound: the envelope mean is the layer-cake integral of `1 - F⋆`. -/

theorem policyCDF_le_one {T : Tree} (π : Policy T) (t : ℝ) : policyCDF T π t ≤ 1 := by
  have hle : policyCDF T π t ≤ policySum (fun ℓ => leafMass ℓ) π := by
    apply policySum_mono
    intro ℓ _
    split_ifs
    · exact le_rfl
    · exact (leafMass_pos ℓ).le
  simpa [policySum_leafMass] using hle

noncomputable def countLe : List ℝ → ℝ → ℕ
  | [], _ => 0
  | a :: l, t => countLe l t + if a ≤ t then 1 else 0

theorem countLe_zero_of_gt (l : List ℝ) (t : ℝ) (h : ∀ x ∈ l, t < x) : countLe l t = 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      have ha : ¬ a ≤ t := not_le.mpr (h a (by simp))
      simp [countLe, ha, ih (fun x hx => h x (by simp [hx]))]

theorem countLe_iff (l : List ℝ)
    (hl : ∀ {i j : ℕ} (hi : i < l.length) (hj : j < l.length), i < j → l[i] < l[j])
    (t : ℝ) {i : ℕ} (hi : i < l.length) :
    l[i] ≤ t ↔ i < countLe l t := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a as ih =>
      have htail : ∀ {i j : ℕ} (hi : i < as.length) (hj : j < as.length),
          i < j → as[i] < as[j] := by
        intro i j hi hj hij
        have hlt := hl (i := i + 1) (j := j + 1)
          (hi := by simp; omega) (hj := by simp; omega) (by omega)
        simpa [List.getElem_cons_succ] using hlt
      have ha_lt : ∀ {j : ℕ} (hj : j < as.length), a < as[j] := by
        intro j hj
        have hlt := hl (i := 0) (j := j + 1)
          (hi := by simp) (hj := by simp; omega) (by omega)
        simpa [List.getElem_cons_zero, List.getElem_cons_succ] using hlt
      cases i with
      | zero =>
          simp only [List.getElem_cons_zero, countLe]
          by_cases ha : a ≤ t
          · simp [ha]
          · have hgt : ∀ x ∈ as, t < x := by
              intro x hx
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
              have : a < as[j] := ha_lt hj
              exact lt_trans (lt_of_not_ge ha) this
            simp [ha, countLe_zero_of_gt as t hgt]
      | succ i =>
          have hi' : i < as.length := by simp at hi; omega
          simp only [List.getElem_cons_succ, countLe]
          by_cases ha : a ≤ t
          · simp [ha, ih htail hi']
          · have hgt : ∀ x ∈ as, t < x := by
              intro x hx
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hx
              have : a < as[j] := ha_lt hj
              exact lt_trans (lt_of_not_ge ha) this
            have hzero := countLe_zero_of_gt as t hgt
            have hnot : ¬ as[i] ≤ t := not_le.mpr (hgt _ (List.getElem_mem hi'))
            simp [ha, hzero, hnot]

noncomputable def infoRank (T : Tree) (t : ℝ) : ℕ := countLe (infoValues T) t

theorem info_rank_iff (T : Tree) (t : ℝ) {i : ℕ} (hi : i < (infoValues T).length) :
    (infoValues T)[i] ≤ t ↔ i < infoRank T t := by
  simpa [infoRank] using countLe_iff (infoValues T)
    (fun hi hj hij => info_get_strictMono T hi hj hij) t hi

theorem infoRank_le_length (T : Tree) (t : ℝ) :
    infoRank T t ≤ (infoValues T).length := by
  have h := fun i (hi : i < (infoValues T).length) => (info_rank_iff T t hi)
  -- every index counted is < length, so the count is ≤ length
  suffices countLe (infoValues T) t ≤ (infoValues T).length by simpa [infoRank] using this
  induction (infoValues T) with
  | nil => simp [countLe]
  | cons a as ih =>
      simp only [countLe, List.length_cons]
      have : countLe as t ≤ as.length := by
        -- not the same induction hypothesis; prove a direct bound instead
        clear ih h
        induction as with
        | nil => simp [countLe]
        | cons b bs ihb =>
            simp only [countLe, List.length_cons]
            split_ifs <;> omega
      split_ifs <;> omega

theorem Fstar_eq_cumsum (T : Tree) (t : ℝ) :
    Fstar T t = cumsum (envInc T) (infoRank T t) := by
  set n := (infoValues T).length
  set k := infoRank T t
  have hk : k ≤ n := infoRank_le_length T t
  have hiff : ∀ {i : ℕ} (hi : i < n), (infoValues T)[i] ≤ t ↔ i < k :=
    fun hi => by simpa [n, k] using info_rank_iff T t hi
  by_cases hk0 : k = 0
  · rw [hk0, cumsum]
    have hzero : ∀ ℓ : Leaf T, ¬ infoMass (leafMass ℓ) ≤ t := by
      intro ℓ
      have hj := infoIndex_lt T ℓ
      rw [← infoValues_get_index T ℓ]
      exact (hiff hj).not.mpr (by simp [hk0])
    have hfun : (fun ℓ : Leaf T =>
        if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) = fun _ => 0 := by
      funext ℓ
      simp [hzero ℓ]
    simp [Fstar, policyCDF, hfun, policySum_zero]
  · by_cases hlast : k = n
    · rw [hlast, cumsum_envInc_last]
      have hz : (infoValues T)[n - 1]'(by
          have := infoValues_length_pos T
          omega) ≤ t := by
        have hi : n - 1 < n := by
          have := infoValues_length_pos T
          omega
        exact (hiff hi).2 (by simp [hlast, k]; omega)
      have hge : 1 ≤ Fstar T t := by
        have hmono := Fstar_mono T hz
        simpa [Fstar_last, n] using hmono
      have hle : Fstar T t ≤ 1 := by
        simpa [Fstar] using policyCDF_le_one (envelopePolicy T t) t
      linarith
    · have hkpos : 0 < k := by omega
      have hklt : k < n := by omega
      have hzlo : (infoValues T)[k - 1]'(by omega) ≤ t :=
        (hiff (by omega)).2 (by omega)
      have hconst : ∀ π, policyCDF T π t =
          policyCDF T π ((infoValues T)[k - 1]'(by omega)) := by
        intro π
        unfold policyCDF
        apply congrArg (fun f => policySum f π)
        funext ℓ
        have hj := infoIndex_lt T ℓ
        have hiffℓ : infoMass (leafMass ℓ) ≤ t ↔
            infoMass (leafMass ℓ) ≤ (infoValues T)[k - 1]'(by omega) := by
          rw [← infoValues_get_index T ℓ]
          constructor
          · intro hle
            have hi : infoIndex T ℓ < k := (hiff hj).1 hle
            exact (info_get_le_iff T hj (by omega)).2 (by omega)
          · intro hle
            exact le_trans hle hzlo
        by_cases h : infoMass (leafMass ℓ) ≤ t
        · simp [h, (hiffℓ.1 h)]
        · have h' : ¬ infoMass (leafMass ℓ) ≤ (infoValues T)[k - 1] := by
            intro hle
            exact h (hiffℓ.2 hle)
          simp [h, h']
      have hF : Fstar T t = Fstar T ((infoValues T)[k - 1]'(by omega)) := by
        have h1 : Fstar T t ≤ Fstar T ((infoValues T)[k - 1]'(by omega)) := by
          have hle1 := Fstar_le T t (envelopePolicy T ((infoValues T)[k - 1]'(by omega)))
          rw [hconst] at hle1
          simpa [Fstar] using hle1
        have h2 : Fstar T ((infoValues T)[k - 1]'(by omega)) ≤ Fstar T t := by
          have hle2 := Fstar_le T ((infoValues T)[k - 1]'(by omega)) (envelopePolicy T t)
          rw [← hconst] at hle2
          simpa [Fstar] using hle2
        linarith
      rw [cumsum_envInc T k hk, if_neg hk0, hF]

theorem sum_range_sub (μ : ℕ → ℝ) {k n : ℕ} (hk : k ≤ n) :
    (Finset.range n).sum μ - (Finset.range k).sum μ =
      (Finset.range n).sum (fun i => if i < k then 0 else μ i) := by
  induction n with
  | zero =>
      have : k = 0 := by omega
      simp [this]
  | succ n ih =>
      by_cases hkn : k ≤ n
      · have hnk : ¬ n < k := by omega
        calc
          (Finset.range (n + 1)).sum μ - (Finset.range k).sum μ
              = (Finset.range n).sum μ + μ n - (Finset.range k).sum μ := by
                rw [Finset.sum_range_succ]
          _ = (Finset.range n).sum (fun i => if i < k then 0 else μ i) + μ n := by
                rw [← ih hkn]
                ring
          _ = (Finset.range (n + 1)).sum (fun i => if i < k then 0 else μ i) := by
                rw [Finset.sum_range_succ]
                simp [hnk]
      · have hk' : k = n + 1 := by omega
        subst hk'
        simp only [sub_self]
        symm
        apply Finset.sum_eq_zero
        intro i hi
        simp [Finset.mem_range.mp hi]

noncomputable def envTail (T : Tree) (i : ℕ) (t : ℝ) : ℝ :=
  if h : i < (infoValues T).length then
    if t < (infoValues T)[i] then envInc T i else 0
  else 0

theorem one_sub_Fstar_sum (T : Tree) (t : ℝ) :
    1 - Fstar T t =
      (Finset.range (infoValues T).length).sum (fun i => envTail T i t) := by
  set n := (infoValues T).length
  set k := infoRank T t
  have hk : k ≤ n := infoRank_le_length T t
  have hiff : ∀ {i : ℕ} (hi : i < n), t < (infoValues T)[i] ↔ ¬ i < k := by
    intro i hi
    rw [← not_le]
    exact (info_rank_iff T t hi).not
  rw [Fstar_eq_cumsum, cumsum_eq_sum]
  have hone : (1 : ℝ) = (Finset.range n).sum (envInc T) := by
    rw [← cumsum_eq_sum, cumsum_envInc_last]
  rw [hone, sum_range_sub (envInc T) hk]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hi' : i < n := Finset.mem_range.mp hi
  by_cases hik : i < k
  · have hnot : ¬ t < (infoValues T)[i] := by
      intro hlt
      exact (hiff hi').mp hlt hik
    unfold envTail
    rw [dif_pos hi', if_neg hnot, if_pos hik]
  · have hlt : t < (infoValues T)[i] := (hiff hi').mpr hik
    unfold envTail
    rw [dif_pos hi', if_pos hlt, if_neg hik]

theorem integrableOn_envTail (T : Tree) (i : ℕ) :
    IntegrableOn (envTail T i) (Ioi (0 : ℝ)) := by
  by_cases hi : i < (infoValues T).length
  · refine IntegrableOn.congr_fun
      (integrableOn_lt_cutoff (c := envInc T i) (info_nonneg_get T hi)) ?_ measurableSet_Ioi
    intro t _
    simp [envTail, hi]
  · refine (integrableOn_zero (s := Ioi (0 : ℝ))).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp [envTail, hi]

theorem integral_envTail (T : Tree) {i : ℕ} (hi : i < (infoValues T).length) :
    ∫ t in Ioi (0 : ℝ), envTail T i t = envInc T i * (infoValues T)[i] := by
  have hfun : EqOn (envTail T i)
      (fun t : ℝ => if t < (infoValues T)[i] then envInc T i else 0) (Ioi 0) := by
    intro t _
    simp [envTail, hi]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun,
    integral_lt_cutoff (c := envInc T i) (info_nonneg_get T hi)]

theorem integral_one_sub_Fstar (T : Tree) :
    ∫ t in Ioi (0 : ℝ), (1 - Fstar T t) = envelopeMean T := by
  let n := (infoValues T).length
  have hfun : EqOn (fun t : ℝ => 1 - Fstar T t)
      (fun t => (Finset.range n).sum (fun i => envTail T i t)) (Ioi 0) := by
    intro t _
    simpa [n] using one_sub_Fstar_sum T t
  rw [setIntegral_congr_fun measurableSet_Ioi hfun]
  have hinter :
      (∫ t in Ioi (0 : ℝ), (Finset.range n).sum (fun i => envTail T i t)) =
        (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envTail T i t) := by
    simpa using integral_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) (Finset.range n)
      (f := fun i (t : ℝ) => envTail T i t)
      (fun i _ => (integrableOn_envTail T i).integrable)
  rw [hinter]
  have hterm : (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envTail T i t) =
      (Finset.range n).sum (fun i =>
        envInc T i * (if h : i < n then (infoValues T)[i] else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    rw [integral_envTail T hi']
    simp [hi']
  rw [hterm]
  unfold envelopeMean
  dsimp [n]

/-! The same layer cake for the seed, and the comparison `seedCDF ≤ F⋆`. -/

noncomputable def seedCDF {T : Tree} (atoms : List (Atom T)) (t : ℝ) : ℝ :=
  (atoms.map (fun a => if infoMass a.1 ≤ t then a.1 else 0)).sum

noncomputable def seedTail {T : Tree} (atoms : List (Atom T)) (t : ℝ) : ℝ :=
  (atoms.map (fun a => if t < infoMass a.1 then a.1 else 0)).sum

theorem seed_partition {T : Tree} (atoms : List (Atom T)) (t : ℝ) :
    seedCDF atoms t + seedTail atoms t = totalWeight atoms := by
  induction atoms with
  | nil => simp [seedCDF, seedTail, totalWeight]
  | cons a tail ih =>
      have hc : seedCDF (a :: tail) t =
          (if infoMass a.1 ≤ t then a.1 else 0) + seedCDF tail t := by
        simp [seedCDF, List.map_cons, List.sum_cons]
      have ht : seedTail (a :: tail) t =
          (if t < infoMass a.1 then a.1 else 0) + seedTail tail t := by
        simp [seedTail, List.map_cons, List.sum_cons]
      have hw : totalWeight (a :: tail) = a.1 + totalWeight tail := by
        simp [totalWeight, List.map_cons, List.sum_cons]
      rw [hc, ht, hw]
      have hdisj : (if infoMass a.1 ≤ t then a.1 else 0) +
          (if t < infoMass a.1 then a.1 else 0) = a.1 := by
        by_cases h : infoMass a.1 ≤ t
        · simp [h, not_lt.mpr h]
        · simp [h, lt_of_not_ge h]
      calc
        (if infoMass a.1 ≤ t then a.1 else 0) + seedCDF tail t +
            ((if t < infoMass a.1 then a.1 else 0) + seedTail tail t)
          = ((if infoMass a.1 ≤ t then a.1 else 0) +
              (if t < infoMass a.1 then a.1 else 0)) +
              (seedCDF tail t + seedTail tail t) := by ring
        _ = a.1 + totalWeight tail := by rw [hdisj, ih]

theorem seedTail_cons {T : Tree} (a : Atom T) (tail : List (Atom T)) (t : ℝ) :
    seedTail (a :: tail) t =
      (if t < infoMass a.1 then a.1 else 0) + seedTail tail t := by
  simp [seedTail, List.map_cons, List.sum_cons]

theorem integrableOn_seedTail {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1) :
    IntegrableOn (seedTail atoms) (Ioi (0 : ℝ)) := by
  induction atoms with
  | nil =>
      rw [show seedTail ([] : List (Atom T)) = fun _ => 0 by
        funext t
        simp [seedTail]]
      exact integrableOn_zero
  | cons a tail ih =>
      have ha0 : 0 < a.1 := hpos a (by simp)
      have ha1 : a.1 ≤ 1 := hle a (by simp)
      refine IntegrableOn.congr_fun
        ((integrableOn_lt_cutoff (c := a.1) (infoMass_of_unit_interval ha0 ha1)).add
          (ih (fun b hb => hpos b (by simp [hb])) (fun b hb => hle b (by simp [hb]))))
        ?_ measurableSet_Ioi
      intro t _
      simp [seedTail_cons]

theorem integral_seedTail {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1) :
    ∫ t in Ioi (0 : ℝ), seedTail atoms t = seedShannon atoms := by
  induction atoms with
  | nil => simp [seedTail, seedShannon, integral_zero]
  | cons a tail ih =>
      have hpos' : ∀ b ∈ tail, 0 < b.1 := fun b hb => hpos b (by simp [hb])
      have hle' : ∀ b ∈ tail, b.1 ≤ 1 := fun b hb => hle b (by simp [hb])
      have ha0 : 0 < a.1 := hpos a (by simp)
      have ha1 : a.1 ≤ 1 := hle a (by simp)
      have hfun : EqOn (seedTail (a :: tail))
          (fun t : ℝ => (if t < infoMass a.1 then a.1 else 0) + seedTail tail t) (Ioi 0) := by
        intro t _
        simp [seedTail_cons]
      rw [setIntegral_congr_fun measurableSet_Ioi hfun,
        integral_add (integrableOn_lt_cutoff (c := a.1)
          (infoMass_of_unit_interval ha0 ha1)).integrable
          (integrableOn_seedTail tail hpos' hle').integrable,
        integral_lt_cutoff (c := a.1) (infoMass_of_unit_interval ha0 ha1),
        ih hpos' hle', seedShannon_cons]

noncomputable instance {T : Tree} : DecidableEq (Leaf T) := Classical.decEq _

theorem sum_psigma {α : Type*} {σ : α → Type*} [Fintype α] [∀ a, Fintype (σ a)]
    (g : (Σ' a, σ a) → ℝ) :
    (∑ x : Σ' a, σ a, g x) = ∑ a, ∑ s, g ⟨a, s⟩ := by
  let e : (Σ' a, σ a) ≃ Σ a, σ a := Equiv.psigmaEquivSigma σ
  have h := e.sum_comp (fun s => g (e.symm s))
  simp only [Equiv.symm_apply_apply] at h
  rw [h]
  rw [← Finset.univ_sigma_univ]
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro a _
  refine Finset.sum_congr rfl ?_
  intro s _
  rfl

def leafPair
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ} {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (a : Fin nA) (s : (y : Fin (nY a)) ×' Leaf (child a y)) :
    Leaf (.node nA hA nY hY K Kpos Ksum child) :=
  ⟨a, s⟩

/-! A policy sum is exactly the sum over the histories compatible with that policy. -/

theorem policySum_eq_finset :
    ∀ (T : Tree) (f : Leaf T → ℝ) (π : Policy T),
      policySum f π = ∑ ℓ : Leaf T, if CompatiblePolicy ℓ π then f ℓ else 0 := by
  intro T
  induction T with
  | leaf =>
      intro f π
      unfold policySum
      have hsum : (∑ ℓ : Leaf Tree.leaf, if CompatiblePolicy ℓ π then f ℓ else 0) =
          if CompatiblePolicy (defaultLeaf Tree.leaf) π then f (defaultLeaf Tree.leaf) else 0 := by
        refine Finset.sum_eq_single_of_mem (defaultLeaf Tree.leaf) (Finset.mem_univ _) ?_
        intro ℓ _ hne
        cases ℓ
        unfold defaultLeaf at hne
        exact (hne rfl).elim
      simpa [CompatiblePolicy, defaultLeaf] using hsum.symm
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro f π
      have hsplit := sum_psigma
        (fun p : Leaf (.node nA hA nY hY K Kpos Ksum child) => if CompatiblePolicy p π then f p else 0)
      have hIH : ∀ y : Fin (nY π.1),
          policySum (fun ℓ => f ⟨π.1, y, ℓ⟩) (π.2 π.1 y) =
            ∑ ℓ : Leaf (child π.1 y),
              if CompatiblePolicy ℓ (π.2 π.1 y) then f ⟨π.1, y, ℓ⟩ else 0 :=
        fun y => ih π.1 y (fun ℓ => f ⟨π.1, y, ℓ⟩) (π.2 π.1 y)
      have hzero : ∀ b : Fin nA, b ≠ π.1 →
          (∑ s : (y : Fin (nY b)) ×' Leaf (child b y),
            if CompatiblePolicy (leafPair b s) π then f (leafPair b s) else 0) = 0 := by
        intro b hb
        apply Finset.sum_eq_zero
        intro s _
        rcases s with ⟨y, ℓ⟩
        have hbad : ¬ CompatiblePolicy (leafPair b ⟨y, ℓ⟩) π := by
          intro hcomp
          dsimp [leafPair] at hcomp
          simp [CompatiblePolicy] at hcomp
          exact hb hcomp.1
        simp [hbad]
      have hsingle := Finset.sum_eq_single_of_mem (s := Finset.univ)
        (f := fun a : Fin nA =>
          ∑ s : (y : Fin (nY a)) ×' Leaf (child a y),
            if CompatiblePolicy (leafPair a s) π then f (leafPair a s) else 0)
        π.1 (Finset.mem_univ _) (fun b _ hb => hzero b hb)
      have hsig := sum_psigma
        (fun s : (y : Fin (nY π.1)) ×' Leaf (child π.1 y) =>
          if CompatiblePolicy (leafPair π.1 s) π then f (leafPair π.1 s) else 0)
      have hpoint :
          (∑ y, ∑ ℓ, if CompatiblePolicy ℓ (π.2 π.1 y) then f ⟨π.1, y, ℓ⟩ else 0) =
            ∑ y, ∑ ℓ,
              if CompatiblePolicy (leafPair π.1 ⟨y, ℓ⟩) π then f (leafPair π.1 ⟨y, ℓ⟩) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro y _
        refine Finset.sum_congr rfl ?_
        intro ℓ _
        dsimp [leafPair]
        simp [CompatiblePolicy]
      have hpol : policySum f π =
          ∑ y, ∑ ℓ, if CompatiblePolicy ℓ (π.2 π.1 y) then f ⟨π.1, y, ℓ⟩ else 0 := by
        simp only [policySum]
        simp_rw [hIH]
      exact hpol.trans (hpoint.trans (hsig.symm.trans (hsingle.symm.trans hsplit.symm)))

theorem policyCDF_eq_finset (T : Tree) (π : Policy T) (t : ℝ) :
    policyCDF T π t =
      ∑ ℓ : Leaf T,
        if CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0 := by
  rw [policyCDF, policySum_eq_finset]
  refine Finset.sum_congr rfl ?_
  intro ℓ _
  by_cases hc : CompatiblePolicy ℓ π <;> by_cases hi : infoMass (leafMass ℓ) ≤ t <;>
    simp [hc, hi]

theorem transcriptWeight_cons {T : Tree} (a : Atom T) (tail : List (Atom T))
    (π : Policy T) (ℓ : Leaf T) :
    transcriptWeight (a :: tail) π ℓ =
      (if run a.2 π = ℓ then a.1 else 0) + transcriptWeight tail π ℓ := by
  simp [transcriptWeight, List.map_cons, List.sum_cons]

theorem transcript_nonneg {T : Tree} (atoms : List (Atom T)) (π : Policy T) (ℓ : Leaf T)
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) : 0 ≤ transcriptWeight atoms π ℓ := by
  induction atoms with
  | nil => simp [transcriptWeight]
  | cons a tail ih =>
      rw [transcriptWeight_cons]
      have h0 : 0 ≤ (if run a.2 π = ℓ then a.1 else 0) := by
        by_cases hr : run a.2 π = ℓ
        · simp [hr, hnn a (by simp)]
        · simp [hr]
      exact add_nonneg h0 (ih (fun b hb => hnn b (by simp [hb])))

theorem atom_le_transcript {T : Tree} (atoms : List (Atom T)) (π : Policy T) (ℓ : Leaf T)
    (a : Atom T) (ha : a ∈ atoms) (hr : run a.2 π = ℓ) (hnn : ∀ b ∈ atoms, 0 ≤ b.1) :
    a.1 ≤ transcriptWeight atoms π ℓ := by
  induction atoms generalizing a with
  | nil => simp at ha
  | cons b tail ih =>
      rw [transcriptWeight_cons]
      simp only [List.mem_cons] at ha
      have hnn' : ∀ c ∈ tail, 0 ≤ c.1 := fun c hc => hnn c (by simp [hc])
      have h0 : 0 ≤ (if run b.2 π = ℓ then b.1 else 0) := by
        by_cases hb : run b.2 π = ℓ
        · simp [hb, hnn b (by simp)]
        · simp [hb]
      rcases ha with rfl | ha
      · rw [if_pos hr]
        exact le_add_of_nonneg_right (transcript_nonneg tail π ℓ hnn')
      · exact le_trans (ih a ha hr hnn') (le_add_of_nonneg_left h0)

theorem filtered_le_transcript {T : Tree} (atoms : List (Atom T)) (π : Policy T)
    (ℓ : Leaf T) (t : ℝ) (hnn : ∀ a ∈ atoms, 0 ≤ a.1) :
    (atoms.map (fun a => if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0)).sum ≤
      transcriptWeight atoms π ℓ := by
  induction atoms with
  | nil => simp [transcriptWeight]
  | cons a tail ih =>
      rw [transcriptWeight_cons]
      simp only [List.map_cons, List.sum_cons]
      have hnn' : ∀ b ∈ tail, 0 ≤ b.1 := fun b hb => hnn b (by simp [hb])
      have h0 : 0 ≤ (if run a.2 π = ℓ then a.1 else 0) := by
        by_cases hr : run a.2 π = ℓ
        · simp [hr, hnn a (by simp)]
        · simp [hr]
      by_cases h : run a.2 π = ℓ ∧ infoMass a.1 ≤ t
      · rw [if_pos h, if_pos h.1]
        have htail := add_le_add_left (ih hnn') a.1
        simpa [add_comm] using htail
      · rw [if_neg h, zero_add]
        exact le_trans (ih hnn') (le_add_of_nonneg_left h0)

theorem map_ite_sum_zero {T : Tree} (l : List (Atom T)) (π : Policy T) (ℓ : Leaf T) (t : ℝ)
    (h : ∀ a ∈ l, (if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0) = 0) :
    (l.map (fun a => if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0)).sum = 0 := by
  induction l with
  | nil => simp
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [h a (by simp), ih (fun b hb => h b (by simp [hb])), zero_add]

theorem leaf_contrib_le {T : Tree} (atoms : List (Atom T)) (π : Policy T) (ℓ : Leaf T) (t : ℝ)
    (hexact : transcriptWeight atoms π ℓ =
      if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) :
    (atoms.map (fun a => if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0)).sum ≤
      if CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0 := by
  have hnn : ∀ a ∈ atoms, 0 ≤ a.1 := fun a ha => (hpos a ha).le
  have hle := filtered_le_transcript atoms π ℓ t hnn
  rw [hexact] at hle
  by_cases hc : CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t
  · rcases hc with ⟨hcomp, hinfo⟩
    simp only [hcomp, ite_true] at hle
    simpa [hcomp, hinfo] using hle
  · by_cases hcomp : CompatiblePolicy ℓ π
    · have hgt : t < infoMass (leafMass ℓ) :=
        lt_of_not_ge (fun hinfo => hc ⟨hcomp, hinfo⟩)
      have hterm : ∀ a ∈ atoms,
          (if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0) = 0 := by
        intro a ha
        by_cases hrun : run a.2 π = ℓ ∧ infoMass a.1 ≤ t
        · exfalso
          have ha_le : a.1 ≤ transcriptWeight atoms π ℓ :=
            atom_le_transcript atoms π ℓ a ha hrun.1 hnn
          rw [hexact, if_pos hcomp] at ha_le
          exact lt_irrefl t (lt_of_lt_of_le hgt
            (le_trans (infoMass_anti (hpos a ha) (leafMass_pos ℓ) ha_le) hrun.2))
        · simp [hrun]
      simpa [hc] using le_of_eq (map_ite_sum_zero atoms π ℓ t hterm)
    · simp only [hcomp, ite_false] at hle
      simpa [hc] using hle

theorem seedCDF_leafSum {T : Tree} (atoms : List (Atom T)) (π : Policy T) (t : ℝ) :
    seedCDF atoms t =
      ∑ ℓ : Leaf T,
        (atoms.map (fun a => if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0)).sum := by
  induction atoms with
  | nil => simp [seedCDF]
  | cons a tail ih =>
      have hc : seedCDF (a :: tail) t =
          (if infoMass a.1 ≤ t then a.1 else 0) + seedCDF tail t := by
        simp [seedCDF, List.map_cons, List.sum_cons]
      have hcons : ∀ ℓ,
          ((a :: tail).map (fun b =>
            if run b.2 π = ℓ ∧ infoMass b.1 ≤ t then b.1 else 0)).sum =
            (if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0) +
              (tail.map (fun b =>
                if run b.2 π = ℓ ∧ infoMass b.1 ≤ t then b.1 else 0)).sum := by
        intro ℓ
        simp [List.map_cons, List.sum_cons]
      have hhead : (if infoMass a.1 ≤ t then a.1 else 0) =
          ∑ ℓ : Leaf T, if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0 := by
        by_cases hinfo : infoMass a.1 ≤ t
        · simp only [hinfo, true_and, ite_true]
          have hsum := Finset.sum_eq_single_of_mem (s := Finset.univ)
            (f := fun ℓ : Leaf T => if run a.2 π = ℓ then a.1 else 0)
            (run a.2 π) (Finset.mem_univ _) (fun ℓ _ hne => by simp [Ne.symm hne])
          simpa using hsum.symm
        · simp only [hinfo, ite_false]
          symm
          apply Finset.sum_eq_zero
          intro ℓ _
          simp [hinfo]
      rw [hc, ih, hhead]
      simp_rw [hcons]
      rw [Finset.sum_add_distrib]

theorem seedCDF_le_Fstar {T : Tree} {atoms : List (Atom T)}
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (t : ℝ) : seedCDF atoms t ≤ Fstar T t := by
  let π := envelopePolicy T t
  calc
    seedCDF atoms t
        = ∑ ℓ, (atoms.map (fun a =>
            if run a.2 π = ℓ ∧ infoMass a.1 ≤ t then a.1 else 0)).sum :=
          seedCDF_leafSum atoms π t
    _ ≤ ∑ ℓ, if CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0 := by
          apply Finset.sum_le_sum
          intro ℓ _
          exact leaf_contrib_le atoms π ℓ t (hexact π ℓ) hpos
    _ = policyCDF T π t := (policyCDF_eq_finset T π t).symm
    _ = Fstar T t := rfl

theorem one_sub_seedCDF {T : Tree} (atoms : List (Atom T)) (t : ℝ)
    (h : totalWeight atoms = 1) : 1 - seedCDF atoms t = seedTail atoms t := by
  linarith [seed_partition atoms t, h]

theorem integrableOn_one_sub_Fstar (T : Tree) :
    IntegrableOn (fun t : ℝ => 1 - Fstar T t) (Ioi (0 : ℝ)) := by
  let n := (infoValues T).length
  have hint : IntegrableOn
      (fun t : ℝ => (Finset.range n).sum (fun i => envTail T i t)) (Ioi (0 : ℝ)) := by
    simpa [IntegrableOn] using
      integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) (Finset.range n)
        (f := fun i (t : ℝ) => envTail T i t)
        (fun i _ => (integrableOn_envTail T i).integrable)
  refine hint.congr_fun ?_ measurableSet_Ioi
  intro t _
  simpa [n] using (one_sub_Fstar_sum T t).symm

theorem integrableOn_one_sub_seed {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    IntegrableOn (fun t : ℝ => 1 - seedCDF atoms t) (Ioi (0 : ℝ)) := by
  refine IntegrableOn.congr_fun (integrableOn_seedTail atoms hpos hle) ?_ measurableSet_Ioi
  intro t _
  exact (one_sub_seedCDF atoms t htot).symm

theorem integral_one_sub_seed {T : Tree} (atoms : List (Atom T))
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    ∫ t in Ioi (0 : ℝ), (1 - seedCDF atoms t) = seedShannon atoms := by
  have hfun : EqOn (fun t : ℝ => 1 - seedCDF atoms t) (seedTail atoms) (Ioi 0) := by
    intro t _
    exact one_sub_seedCDF atoms t htot
  rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_seedTail atoms hpos hle]

theorem envelope_le_seedShannon {T : Tree} {atoms : List (Atom T)}
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) : envelopeMean T ≤ seedShannon atoms := by
  have hpoint : ∀ t ∈ Ioi (0 : ℝ), 1 - Fstar T t ≤ 1 - seedCDF atoms t := by
    intro t _
    linarith [seedCDF_le_Fstar hexact hpos t]
  have hmono := setIntegral_mono_on (integrableOn_one_sub_Fstar T)
    (integrableOn_one_sub_seed atoms hpos hle htot) measurableSet_Ioi hpoint
  rw [integral_one_sub_Fstar, integral_one_sub_seed atoms hpos hle htot] at hmono
  exact hmono

theorem one_seed_shannon (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧
      (∀ a ∈ atoms, 0 < a.1) ∧
      totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ =
          if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      envelopeMean T ≤ seedShannon atoms ∧
      seedShannon atoms ≤ envelopeMean T + shannonOverhead := by
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
  refine ⟨atoms, ht, hbounds.1, htot, hexact, ?_, ?_⟩
  · exact envelope_le_seedShannon hexact hbounds.1 hbounds.2 htot
  · exact seedShannon_le_envelope ht hbounds.1 hbounds.2

/-! Stochastic realization. `Z` is the envelope `F⋆` and `J` is the greedy seed.
    `coupleSurv t` is `P(Z + E > t)` for an exponential `E` of rate `ln 2`,
    independent of `Z`: `P(E > t - z) = min(1, 2^(z - t))`. -/

noncomputable def coupleFactor (T : Tree) (t : ℝ) (i : ℕ) : ℝ :=
  if h : i < (infoValues T).length then
    min 1 ((2 : ℝ) ^ ((infoValues T)[i] - t))
  else 0

noncomputable def coupleSurv (T : Tree) (t : ℝ) : ℝ :=
  (Finset.range (infoValues T).length).sum fun i => envInc T i * coupleFactor T t i

theorem coupleFactor_mono (T : Tree) (t : ℝ) {i : ℕ}
    (hi : i + 1 < (infoValues T).length) :
    coupleFactor T t i ≤ coupleFactor T t (i + 1) := by
  have hi0 : i < (infoValues T).length := by omega
  unfold coupleFactor
  rw [dif_pos hi0, dif_pos hi]
  have hz : (infoValues T)[i] ≤ (infoValues T)[i + 1] :=
    (info_get_strictMono T hi0 hi (by omega)).le
  have hexp :
      (2 : ℝ) ^ ((infoValues T)[i] - t) ≤ (2 : ℝ) ^ ((infoValues T)[i + 1] - t) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (sub_le_sub_right hz t)
  exact min_le_min le_rfl hexp

theorem coupleFactor_index (T : Tree) (t : ℝ) (ℓ : Leaf T) :
    coupleFactor T t (infoIndex T ℓ) =
      min 1 ((2 : ℝ) ^ (infoMass (leafMass ℓ) - t)) := by
  have hi := infoIndex_lt T ℓ
  unfold coupleFactor
  rw [dif_pos hi, infoValues_get_index]

theorem aDelta_le_min (δ p : ℝ) : aDelta δ p ≤ min p δ := by
  unfold aDelta
  by_cases h : p ≤ δ
  · rw [if_pos h, min_eq_left h]
  · rw [if_neg h, min_eq_right (le_of_lt (lt_of_not_ge h))]
    exact min_le_left _ _

theorem min_eq_scaled {p δ : ℝ} (hp : 0 < p) :
    min p δ = p * min (1 : ℝ) (δ / p) := by
  by_cases h : δ ≤ p
  · have hdiv : δ / p ≤ 1 := (div_le_one₀ hp).mpr h
    rw [min_eq_right h, min_eq_right hdiv]
    field_simp
  · have hlt : p < δ := lt_of_not_ge h
    have hdiv : 1 ≤ δ / p := (one_le_div hp).mpr hlt.le
    rw [min_eq_left hlt.le, min_eq_left hdiv]
    ring

theorem min_eq_dyadic {p δ : ℝ} (hp : 0 < p) :
    min p δ = p * min (1 : ℝ) (δ * (2 : ℝ) ^ infoMass p) := by
  rw [min_eq_scaled hp, div_eq_rpow_info hp]

theorem dyadic_shift (z t : ℝ) :
    (2 : ℝ) ^ (-t) * (2 : ℝ) ^ z = (2 : ℝ) ^ (z - t) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem smallWeight_le_truncated {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ π : Policy T, smallWeight atoms δ ≤
      policySum (fun ℓ => min (leafMass ℓ) δ) π := by
  obtain ⟨π, hπ⟩ := greedy_advanced_bound ht δ hδ
  refine ⟨π, le_trans hπ ?_⟩
  apply policySum_mono
  intro ℓ _
  exact aDelta_le_min δ (leafMass ℓ)

theorem levelAt_mul (T : Tree) (π : Policy T) (i : ℕ) (c : ℝ) :
    levelAt T π i * c =
      policySum (fun ℓ =>
        if hi : i < (infoValues T).length then
          if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ * c else 0
        else 0) π := by
  unfold levelAt
  by_cases hi : i < (infoValues T).length
  · simp only [hi, dite_true]
    unfold levelMass
    rw [mul_comm, ← policySum_mul]
    refine congrArg (fun f => policySum f π) ?_
    funext ℓ
    by_cases he : infoMass (leafMass ℓ) = (infoValues T)[i]
    · simp [he, mul_comm]
    · simp [he]
  · simp only [hi, dite_false, zero_mul]
    exact (policySum_zero (π := π)).symm

theorem level_weighted (T : Tree) (π : Policy T) (G : ℕ → ℝ) :
    (Finset.range (infoValues T).length).sum (fun i => levelAt T π i * G i) =
      policySum (fun ℓ => leafMass ℓ * G (infoIndex T ℓ)) π := by
  set n := (infoValues T).length
  calc
    (Finset.range n).sum (fun i => levelAt T π i * G i)
        = (Finset.range n).sum (fun i =>
            policySum (fun ℓ =>
              if hi : i < n then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ * G i else 0
              else 0) π) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simpa using levelAt_mul T π i (G i)
    _ = policySum (fun ℓ =>
          (Finset.range n).sum (fun i =>
            if hi : i < n then
              if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ * G i else 0
            else 0)) π := by
          rw [policySum_range]
    _ = policySum (fun ℓ => leafMass ℓ * G (infoIndex T ℓ)) π := by
          refine congrArg (fun f => policySum f π) ?_
          funext ℓ
          have hsum : (Finset.range n).sum (fun i =>
              if hi : i < n then
                if infoMass (leafMass ℓ) = (infoValues T)[i] then leafMass ℓ * G i else 0
              else 0) =
              (Finset.range n).sum (fun i =>
                if i = infoIndex T ℓ then leafMass ℓ * G i else 0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            have ht := level_term_eq T ℓ i
            by_cases hi : i < n
            · simp only [hi, dite_true] at ht ⊢
              by_cases he : infoMass (leafMass ℓ) = (infoValues T)[i]
              · have hinj : i = infoIndex T ℓ :=
                  (List.Nodup.getElem_inj_iff (nodup_infoValues T) (hi := hi)
                    (hj := infoIndex_lt T ℓ)).1
                    ((he.symm).trans (infoValues_get_index T ℓ).symm)
                simp [he, hinj]
              · have hne : i ≠ infoIndex T ℓ := by
                  intro h
                  subst h
                  exact he (infoValues_get_index T ℓ).symm
                simp [he, hne]
            · have hne : i ≠ infoIndex T ℓ := by
                intro h
                exact hi (h ▸ infoIndex_lt T ℓ)
              simp [hi, hne]
          rw [hsum, Finset.sum_ite_eq']
          have hmem : infoIndex T ℓ ∈ Finset.range n :=
            Finset.mem_range.mpr (infoIndex_lt T ℓ)
          simp [hmem]

theorem cumsum_env_le_level (T : Tree) (π : Policy T) (k : ℕ)
    (hk : k ≤ (infoValues T).length) :
    cumsum (envInc T) k ≤ cumsum (levelAt T π) k := by
  rw [cumsum_envInc T k hk, cumsum_levelAt π k hk]
  by_cases hk0 : k = 0
  · simp [hk0]
  · simp only [hk0, ite_false]
    exact Fstar_le T _ π

theorem cumsum_level_last (T : Tree) (π : Policy T) :
    cumsum (levelAt T π) (infoValues T).length = 1 := by
  have h := cumsum_levelAt π (infoValues T).length le_rfl
  have hpos := infoValues_length_pos T
  rw [if_neg (by omega : (infoValues T).length ≠ 0)] at h
  rw [h]
  exact policyCDF_last π

theorem policy_factor_le_couple (T : Tree) (π : Policy T) (t : ℝ) :
    policySum (fun ℓ => leafMass ℓ * coupleFactor T t (infoIndex T ℓ)) π ≤
      coupleSurv T t := by
  set n := (infoValues T).length
  have hsum := sum_le_of_larger_partials n (coupleFactor T t) (levelAt T π) (envInc T)
    (fun i hi => coupleFactor_mono T t hi)
    (fun k hk => cumsum_env_le_level T π k hk)
    ?_
  have hleft := level_weighted T π (coupleFactor T t)
  have hright : (Finset.range n).sum (fun i => envInc T i * coupleFactor T t i) =
      coupleSurv T t := rfl
  linarith
  · rw [cumsum_level_last T π, cumsum_envInc_last]

theorem seedTail_le_smallWeight {T : Tree} (atoms : List (Atom T)) (t : ℝ)
    (hpos : ∀ a ∈ atoms, 0 < a.1) :
    seedTail atoms t ≤ smallWeight atoms ((2 : ℝ) ^ (-t)) := by
  induction atoms with
  | nil => simp [seedTail, smallWeight]
  | cons a tail ih =>
      have htail := ih (fun b hb => hpos b (List.mem_cons_of_mem a hb))
      simp only [seedTail, smallWeight, List.map_cons, List.sum_cons] at htail ⊢
      have ha : 0 < a.1 := hpos a (by simp)
      by_cases ht : t < infoMass a.1
      · have hw : a.1 ≤ (2 : ℝ) ^ (-t) :=
          (weight_le_dyadic_iff ha).2 (le_of_lt ht)
        simp only [ht, hw, ite_true]
        linarith
      · simp only [ht, ite_false, zero_add]
        refine le_trans htail ?_
        by_cases hw : a.1 ≤ (2 : ℝ) ^ (-t)
        · simp only [hw, ite_true]
          exact le_add_of_nonneg_left ha.le
        · simp only [hw, ite_false, zero_add]
          exact le_rfl

theorem truncated_le_couple {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) (t : ℝ) :
    ∃ π : Policy T, smallWeight atoms ((2 : ℝ) ^ (-t)) ≤
      policySum (fun ℓ => leafMass ℓ * coupleFactor T t (infoIndex T ℓ)) π := by
  have hδ : 0 ≤ (2 : ℝ) ^ (-t) := (Real.rpow_pos_of_pos (by norm_num) (-t)).le
  obtain ⟨π, hπ⟩ := smallWeight_le_truncated ht ((2 : ℝ) ^ (-t)) hδ
  refine ⟨π, le_trans hπ ?_⟩
  apply policySum_mono
  intro ℓ _
  have hp := leafMass_pos ℓ
  rw [min_eq_dyadic (δ := (2 : ℝ) ^ (-t)) hp]
  refine mul_le_mul_of_nonneg_left ?_ hp.le
  rw [coupleFactor_index, dyadic_shift (infoMass (leafMass ℓ)) t]

/-- The discovery: one greedy seed, exact for every policy, lies between the
    adaptive envelope and that envelope shifted by an exponential of rate `ln 2`.
    `seedCDF ≤ F⋆` is `Z ≼st J`. `seedTail ≤ coupleSurv` is `J ≼st Z + E`. -/
theorem causal_realization (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧
      (∀ a ∈ atoms, 0 < a.1) ∧
      totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ =
          if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      (∀ t : ℝ, seedCDF atoms t ≤ Fstar T t) ∧
      (∀ t : ℝ, seedTail atoms t ≤ coupleSurv T t) := by
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
  refine ⟨atoms, ht, hbounds.1, htot, hexact, ?_, ?_⟩
  · intro t
    exact seedCDF_le_Fstar hexact hbounds.1 t
  · intro t
    have htail := seedTail_le_smallWeight atoms t hbounds.1
    obtain ⟨π, hπ⟩ := truncated_le_couple ht t
    exact le_trans htail (le_trans hπ (policy_factor_le_couple T π t))

#print axioms one_seed_shannon
#print axioms causal_realization

end CausalSpectrum


/-
Exact penalty. The largest gap between causal and ordinary coupling
entropy is the least universal coefficient that forces compatibility.
-/
import CausalSeed.Entropy
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fintype.Pi

noncomputable section
open Classical
open Set
namespace CausalSpectrum

noncomputable instance {T : Tree} : DecidableEq (Leaf T) :=
  fun a b => Classical.propDecidable (a = b)

noncomputable instance {T : Tree} : DecidableEq (Policy T) :=
  fun a b => Classical.propDecidable (a = b)

noncomputable instance strategyFintype : (T : Tree) → Fintype (Strategy T)
  | .leaf => by
      unfold Strategy
      exact Fintype.ofSubsingleton PUnit.unit
  | .node nA hA nY hY K Kpos Ksum child => by
      letI : ∀ a y, Fintype (Strategy (child a y)) :=
        fun a y => strategyFintype (child a y)
      unfold Strategy
      infer_instance

/-- One compatible transcript for every policy. -/
def Assignment (T : Tree) : Type :=
  ∀ π : Policy T, {ℓ : Leaf T // CompatiblePolicy ℓ π}

noncomputable instance assignmentFintype (T : Tree) : Fintype (Assignment T) := by
  unfold Assignment
  infer_instance

def realizes {T : Tree} (d : Strategy T) : Assignment T :=
  fun π => ⟨run d π, run_compatible_policy d π⟩

def realizable {T : Tree} (α : Assignment T) : Prop :=
  ∃ d : Strategy T, realizes d = α

noncomputable def chosenStrategy {T : Tree} (α : Assignment T) (h : realizable α) :
    Strategy T := Classical.choose h

theorem realizes_chosen {T : Tree} (α : Assignment T) (h : realizable α) :
    realizes (chosenStrategy α h) = α := Classical.choose_spec h

/-! Self-information term, zero at mass zero. -/

noncomputable def entTerm (w : ℝ) : ℝ :=
  if w = 0 then 0 else w * infoMass w

theorem entTerm_zero : entTerm 0 = 0 := by simp [entTerm]

theorem entTerm_of_pos {w : ℝ} (hw : 0 < w) : entTerm w = w * infoMass w := by
  simp [entTerm, ne_of_gt hw]

theorem entTerm_nonneg {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) : 0 ≤ entTerm w := by
  by_cases h : w = 0
  · simp [h, entTerm]
  · have hw' : 0 < w := lt_of_le_of_ne hw (Ne.symm h)
    rw [entTerm_of_pos hw']
    exact mul_nonneg hw'.le (infoMass_of_unit_interval hw' hw1)

theorem entTerm_mul {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entTerm (x * y) = y * entTerm x + x * entTerm y := by
  by_cases hx0 : x = 0
  · simp [hx0, entTerm]
  by_cases hy0 : y = 0
  · simp [hy0, entTerm, mul_zero]
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hxy : 0 < x * y := mul_pos hx' hy'
  rw [entTerm_of_pos hx', entTerm_of_pos hy', entTerm_of_pos hxy]
  have hlog : infoMass (x * y) = infoMass x + infoMass y := by
    unfold infoMass
    rw [Real.logb_mul (ne_of_gt hx') (ne_of_gt hy')]
    ring
  rw [hlog]
  ring

theorem entTerm_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    entTerm (x + y) ≤ entTerm x + entTerm y := by
  by_cases hx0 : x = 0
  · simp [hx0, entTerm]
  by_cases hy0 : y = 0
  · simp [hy0, entTerm]
  have hx' : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hy' : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hs : 0 < x + y := add_pos hx' hy'
  rw [entTerm_of_pos hx', entTerm_of_pos hy', entTerm_of_pos hs]
  unfold infoMass
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hdiv : Real.log 2 ≠ 0 := by
    have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    exact ne_of_gt this
  -- x (-logb x) + y (-logb y) - (x+y) (-logb (x+y)) ≥ 0
  have hkey :
      x * (-Real.logb 2 x) + y * (-Real.logb 2 y) ≥
        (x + y) * (-Real.logb 2 (x + y)) := by
    have hxlog : 0 ≤ Real.logb 2 ((x + y) / x) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by rw [one_le_div hx']; linarith)
    have hylog : 0 ≤ Real.logb 2 ((x + y) / y) :=
      Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by rw [one_le_div hy']; linarith)
    have hxeq : Real.logb 2 ((x + y) / x) = Real.logb 2 (x + y) - Real.logb 2 x :=
      Real.logb_div (ne_of_gt hs) (ne_of_gt hx')
    have hyeq : Real.logb 2 ((x + y) / y) = Real.logb 2 (x + y) - Real.logb 2 y :=
      Real.logb_div (ne_of_gt hs) (ne_of_gt hy')
    have hxnonneg : 0 ≤ x * (Real.logb 2 (x + y) - Real.logb 2 x) := by
      rw [← hxeq]; exact mul_nonneg hx'.le hxlog
    have hynonneg : 0 ≤ y * (Real.logb 2 (x + y) - Real.logb 2 y) := by
      rw [← hyeq]; exact mul_nonneg hy'.le hylog
    linarith
  linarith

noncomputable def pmfEntropy {α : Type} [Fintype α] (μ : α → ℝ) : ℝ :=
  ∑ a, entTerm (μ a)

theorem pmfEntropy_nonneg {α : Type} [Fintype α] {μ : α → ℝ}
    (h0 : ∀ a, 0 ≤ μ a) (h1 : ∀ a, μ a ≤ 1) : 0 ≤ pmfEntropy μ := by
  apply Finset.sum_nonneg
  intro a _
  exact entTerm_nonneg (h0 a) (h1 a)

theorem binaryEntropy_split {α : Type} [Fintype α] (μ : α → ℝ) (p : α → Prop)
    [DecidablePred p] (h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1)
    (η : ℝ) (hη : η = ∑ a, if p a then μ a else 0)
    (hη0 : 0 < η) (hη1 : η < 1) :
    pmfEntropy μ =
      entTerm η + entTerm (1 - η) +
        (1 - η) * pmfEntropy (fun a => if p a then 0 else μ a / (1 - η)) +
        η * pmfEntropy (fun a => if p a then μ a / η else 0) := by
  have hηle : 0 ≤ η := hη0.le
  have hcomp : 0 ≤ 1 - η := by linarith
  have hcomp' : 0 < 1 - η := by linarith
  have hsumRest : ∑ a, (if p a then 0 else μ a) = 1 - η := by
    have hall : ∑ a, μ a =
        (∑ a, if p a then μ a else 0) + (∑ a, if p a then 0 else μ a) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hp : p a <;> simp [hp]
    linarith [htot, hη, hall]
  have hgoodSum : ∑ a, (if p a then (0 : ℝ) else μ a / (1 - η)) = 1 := by
    have hrew : ∀ a, (if p a then (0 : ℝ) else μ a / (1 - η)) =
        (if p a then 0 else μ a) / (1 - η) := by
      intro a; by_cases hp : p a <;> simp [hp, zero_div]
    simp_rw [hrew, ← Finset.sum_div, hsumRest]
    field_simp
  have hbadSum : ∑ a, (if p a then μ a / η else (0 : ℝ)) = 1 := by
    have hrew : ∀ a, (if p a then μ a / η else (0 : ℝ)) =
        (if p a then μ a else 0) / η := by
      intro a; by_cases hp : p a <;> simp [hp, zero_div]
    simp_rw [hrew, ← Finset.sum_div]
    have : ∑ a, (if p a then μ a else (0 : ℝ)) = η := hη.symm
    rw [this]
    field_simp
  have hpiece : ∀ a, entTerm (μ a) =
      (if p a then (μ a / η) * entTerm η + η * entTerm (μ a / η)
        else (μ a / (1 - η)) * entTerm (1 - η) + (1 - η) * entTerm (μ a / (1 - η))) := by
    intro a
    by_cases hp : p a
    · have hmul := entTerm_mul hηle (div_nonneg (h0 a) hηle)
      have hid : η * (μ a / η) = μ a := by field_simp
      simp only [hp, ite_true]
      simpa [hid] using hmul
    · have hmul := entTerm_mul hcomp (div_nonneg (h0 a) hcomp)
      have hid : (1 - η) * (μ a / (1 - η)) = μ a := by field_simp
      simp only [hp, ite_false]
      simpa [hid] using hmul
  unfold pmfEntropy
  rw [Finset.sum_congr rfl fun a _ => hpiece a]
  have hsplit : ∑ a, (if p a then (μ a / η) * entTerm η + η * entTerm (μ a / η)
        else (μ a / (1 - η)) * entTerm (1 - η) + (1 - η) * entTerm (μ a / (1 - η))) =
      ∑ a, (if p a then (μ a / η) * entTerm η else 0) +
      ∑ a, (if p a then η * entTerm (μ a / η) else 0) +
      ∑ a, (if p a then 0 else (μ a / (1 - η)) * entTerm (1 - η)) +
      ∑ a, (if p a then 0 else (1 - η) * entTerm (μ a / (1 - η))) := by
    repeat rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : p a <;> simp [hp]
  rw [hsplit]
  have h1 : ∑ a, (if p a then (μ a / η) * entTerm η else 0) = entTerm η := by
    have : ∑ a, (if p a then (μ a / η) * entTerm η else 0) =
        entTerm η * ∑ a, (if p a then μ a / η else 0) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hp : p a <;> simp [hp, mul_comm]
    rw [this, hbadSum, mul_one]
  have h2 : ∑ a, (if p a then η * entTerm (μ a / η) else 0) =
      η * ∑ a, (if p a then entTerm (μ a / η) else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : p a <;> simp [hp]
  have h3 : ∑ a, (if p a then 0 else (μ a / (1 - η)) * entTerm (1 - η)) = entTerm (1 - η) := by
    have : ∑ a, (if p a then (0 : ℝ) else (μ a / (1 - η)) * entTerm (1 - η)) =
        entTerm (1 - η) * ∑ a, (if p a then 0 else μ a / (1 - η)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      by_cases hp : p a <;> simp [hp, mul_comm]
    rw [this, hgoodSum, mul_one]
  have h4 : ∑ a, (if p a then 0 else (1 - η) * entTerm (μ a / (1 - η))) =
      (1 - η) * ∑ a, (if p a then 0 else entTerm (μ a / (1 - η))) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : p a <;> simp [hp]
  have hgoodEnt : ∑ a, (if p a then (0 : ℝ) else entTerm (μ a / (1 - η))) =
      ∑ a, entTerm (if p a then 0 else μ a / (1 - η)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : p a <;> simp [hp, entTerm]
  have hbadEnt : ∑ a, (if p a then entTerm (μ a / η) else (0 : ℝ)) =
      ∑ a, entTerm (if p a then μ a / η else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : p a <;> simp [hp, entTerm]
  rw [h1, h2, h3, h4, hgoodEnt, hbadEnt]
  ring

/-! Couplings of all deterministic transcripts. -/

structure Coupling (T : Tree) where
  mass : Assignment T → ℝ
  nonneg : ∀ α, 0 ≤ mass α
  total : ∑ α, mass α = 1
  marginal : ∀ (π : Policy T) (ℓ : Leaf T), CompatiblePolicy ℓ π →
    ∑ α, (if (α π).1 = ℓ then mass α else 0) = leafMass ℓ

def Coupling.causal {T : Tree} (Γ : Coupling T) : Prop :=
  ∀ α, Γ.mass α ≠ 0 → realizable α

noncomputable def Coupling.entropy {T : Tree} (Γ : Coupling T) : ℝ :=
  pmfEntropy Γ.mass

noncomputable def Coupling.badMass {T : Tree} (Γ : Coupling T) : ℝ :=
  ∑ α, if realizable α then 0 else Γ.mass α

theorem mass_le_leaf {T : Tree} (Γ : Coupling T) (α : Assignment T) (π : Policy T) :
    Γ.mass α ≤ leafMass (α π).1 := by
  classical
  let s : Finset (Assignment T) :=
    Finset.univ.filter fun β => (β π).1 = (α π).1
  have hα : α ∈ s := by simp [s]
  have hsum : ∑ β ∈ s, Γ.mass β = leafMass (α π).1 := by
    rw [Finset.sum_filter]
    exact Γ.marginal π (α π).1 (α π).2
  calc
    Γ.mass α ≤ ∑ β ∈ s, Γ.mass β := Finset.single_le_sum (fun β _ => Γ.nonneg β) hα
    _ = leafMass (α π).1 := hsum

theorem mass_le_one {T : Tree} (Γ : Coupling T) (α : Assignment T) : Γ.mass α ≤ 1 := by
  exact le_trans (mass_le_leaf Γ α (defaultPolicy T)) (leafMass_le_one _)

theorem entropy_nonneg {T : Tree} (Γ : Coupling T) : 0 ≤ Γ.entropy := by
  unfold Coupling.entropy
  exact pmfEntropy_nonneg Γ.nonneg (fun α => mass_le_one Γ α)

theorem badMass_nonneg {T : Tree} (Γ : Coupling T) : 0 ≤ Γ.badMass := by
  unfold Coupling.badMass
  apply Finset.sum_nonneg
  intro α _
  split_ifs
  · exact le_rfl
  · exact Γ.nonneg α

theorem badMass_le_one {T : Tree} (Γ : Coupling T) : Γ.badMass ≤ 1 := by
  unfold Coupling.badMass
  have : ∑ α, (if realizable α then (0 : ℝ) else Γ.mass α) ≤ ∑ α, Γ.mass α := by
    apply Finset.sum_le_sum
    intro α _
    split_ifs
    · exact Γ.nonneg α
    · exact le_rfl
  linarith [Γ.total]

theorem badMass_eq_zero_of_causal {T : Tree} {Γ : Coupling T} (h : Γ.causal) :
    Γ.badMass = 0 := by
  unfold Coupling.badMass
  apply Finset.sum_eq_zero
  intro α _
  by_cases hr : realizable α
  · simp [hr]
  · have hm : Γ.mass α = 0 := by
      by_contra hne
      exact hr (h α hne)
    simp [hr, hm]

theorem goodMass_eq {T : Tree} (Γ : Coupling T) :
    ∑ α, (if realizable α then Γ.mass α else 0) = 1 - Γ.badMass := by
  have hall : ∑ α, Γ.mass α =
      (∑ α, if realizable α then Γ.mass α else 0) +
        (∑ α, if realizable α then 0 else Γ.mass α) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hr : realizable α <;> simp [hr]
  have htot : ∑ α, Γ.mass α = 1 := Γ.total
  unfold Coupling.badMass
  linarith [hall, htot]

open MeasureTheory

theorem policy_info_tail (T : Tree) (π : Policy T) (t : ℝ) :
    ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else 0) =
      1 - policyCDF T π t := by
  classical
  have htot : ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π then leafMass ℓ else 0) = 1 := by
    simpa using (policySum_eq_finset T (fun ℓ => leafMass ℓ) π).symm.trans (policySum_leafMass π)
  have hcdf :
      ∑ ℓ : Leaf T,
        (if CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) =
        policyCDF T π t :=
    (policyCDF_eq_finset T π t).symm
  have hsplit : ∀ ℓ : Leaf T,
      (if CompatiblePolicy ℓ π then leafMass ℓ else 0) =
        (if CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) +
          (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else 0) := by
    intro ℓ
    by_cases hc : CompatiblePolicy ℓ π
    · by_cases hi : infoMass (leafMass ℓ) ≤ t
      · simp [hc, hi, not_lt.mpr hi]
      · simp [hc, hi, lt_of_not_ge hi]
    · simp [hc]
  have hsum :
      ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π then leafMass ℓ else 0) =
        ∑ ℓ : Leaf T,
          ((if CompatiblePolicy ℓ π ∧ infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) +
            (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else 0)) :=
    Finset.sum_congr rfl fun ℓ _ => hsplit ℓ
  rw [Finset.sum_add_distrib] at hsum
  linarith

/-- Every coupling is at least the envelope. A positive atom is no heavier than any
transcript it selects, so its self-information dominates that transcript. -/
theorem entropy_ge_envelope {T : Tree} (Γ : Coupling T) : envelopeMean T ≤ Γ.entropy := by
  classical
  let z : Assignment T → ℝ := fun α =>
    (Finset.univ : Finset (Policy T)).sup' ⟨defaultPolicy T, Finset.mem_univ _⟩
      fun π => infoMass (leafMass (α π).1)
  have hz : ∀ α, 0 ≤ z α := by
    intro α
    exact le_trans (infoMass_nonneg (α (defaultPolicy T)).1)
      (Finset.le_sup' (fun π => infoMass (leafMass (α π).1)) (Finset.mem_univ (defaultPolicy T)))
  have hdom : ∀ α, Γ.mass α ≠ 0 → z α ≤ infoMass (Γ.mass α) := by
    intro α hne
    have hpos : 0 < Γ.mass α := lt_of_le_of_ne (Γ.nonneg α) (Ne.symm hne)
    refine Finset.sup'_le _ _ ?_
    intro π _
    exact infoMass_anti hpos (leafMass_pos _) (mass_le_leaf Γ α π)
  have hent : ∑ α, Γ.mass α * z α ≤ Γ.entropy := by
    unfold Coupling.entropy pmfEntropy
    refine Finset.sum_le_sum fun α _ => ?_
    by_cases h0 : Γ.mass α = 0
    · simp [h0, entTerm]
    · rw [entTerm_of_pos (lt_of_le_of_ne (Γ.nonneg α) (Ne.symm h0))]
      exact mul_le_mul_of_nonneg_left (hdom α h0) (Γ.nonneg α)
  have hpiece : ∀ α,
      IntegrableOn (fun t : ℝ => if t < z α then Γ.mass α else 0) (Ioi (0 : ℝ)) :=
    fun α => integrableOn_lt_cutoff (hz α)
  have hlayer : ∑ α, Γ.mass α * z α =
      ∫ t in Ioi (0 : ℝ), (∑ α, (if t < z α then Γ.mass α else (0 : ℝ))) := by
    have hswap :
        ∫ t in Ioi (0 : ℝ), (∑ α, (if t < z α then Γ.mass α else (0 : ℝ))) =
          ∑ α, ∫ t in Ioi (0 : ℝ), (if t < z α then Γ.mass α else (0 : ℝ)) := by
      simpa using
        (integral_finsetSum (μ := volume.restrict (Ioi (0 : ℝ)))
          (Finset.univ : Finset (Assignment T))
          (f := fun α (t : ℝ) => if t < z α then Γ.mass α else (0 : ℝ))
          (fun α _ => (hpiece α).integrable))
    rw [hswap]
    refine Finset.sum_congr rfl fun α _ => ?_
    exact (integral_lt_cutoff (c := Γ.mass α) (hz α)).symm
  have htail : ∀ t : ℝ, 1 - Fstar T t ≤ ∑ α, (if t < z α then Γ.mass α else (0 : ℝ)) := by
    intro t
    let π : Policy T := envelopePolicy T t
    have hrec : ∀ ℓ : Leaf T,
        (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else (0 : ℝ)) =
          ∑ α, (if (α π).1 = ℓ ∧ t < infoMass (leafMass ℓ) ∧ CompatiblePolicy ℓ π then
            Γ.mass α else (0 : ℝ)) := by
      intro ℓ
      by_cases hc : CompatiblePolicy ℓ π
      · by_cases ht : t < infoMass (leafMass ℓ)
        · have hm := Γ.marginal π ℓ hc
          have hsame :
              ∑ α, (if (α π).1 = ℓ then Γ.mass α else (0 : ℝ)) =
                ∑ α, (if (α π).1 = ℓ ∧ t < infoMass (leafMass ℓ) ∧ CompatiblePolicy ℓ π then
                  Γ.mass α else (0 : ℝ)) := by
            refine Finset.sum_congr rfl fun α _ => ?_
            by_cases he : (α π).1 = ℓ
            · simp only [he, ht, hc, true_and, and_true, ite_true]
            · simp only [he, false_and, ite_false]
          calc
            (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else (0 : ℝ))
                = leafMass ℓ := by simp [hc, ht]
            _ = ∑ α, (if (α π).1 = ℓ then Γ.mass α else (0 : ℝ)) := hm.symm
            _ = ∑ α, (if (α π).1 = ℓ ∧ t < infoMass (leafMass ℓ) ∧ CompatiblePolicy ℓ π then
                Γ.mass α else (0 : ℝ)) := hsame
        · simp only [ht, and_false, ite_false]
          exact (Finset.sum_eq_zero fun α _ => by simp [ht]).symm
      · simp only [hc, false_and, ite_false]
        exact (Finset.sum_eq_zero fun α _ => by simp [hc]).symm
    have hpart :
        ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else (0 : ℝ)) =
          ∑ α, (if t < infoMass (leafMass (α π).1) then Γ.mass α else (0 : ℝ)) := by
      have hswap :
          ∑ ℓ : Leaf T,
              (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else (0 : ℝ)) =
            ∑ ℓ : Leaf T,
              (∑ α, (if (α π).1 = ℓ ∧ t < infoMass (leafMass ℓ) ∧ CompatiblePolicy ℓ π then
                Γ.mass α else (0 : ℝ))) :=
        Finset.sum_congr rfl fun ℓ _ => hrec ℓ
      rw [hswap, Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hcα : CompatiblePolicy (α π).1 π := (α π).2
      have hfun : ∀ ℓ : Leaf T,
          (if (α π).1 = ℓ ∧ t < infoMass (leafMass ℓ) ∧ CompatiblePolicy ℓ π then Γ.mass α else (0 : ℝ)) =
            if (α π).1 = ℓ then
              (if t < infoMass (leafMass (α π).1) then Γ.mass α else (0 : ℝ)) else 0 := by
        intro ℓ
        by_cases he : (α π).1 = ℓ
        · subst he
          by_cases ht : t < infoMass (leafMass (α π).1) <;> simp [ht, hcα]
        · simp [he]
      have hsum := Finset.sum_congr rfl fun ℓ (_ : ℓ ∈ Finset.univ) => hfun ℓ
      rw [hsum, Finset.sum_ite_eq]
      simp [hcα]
    have hcmp : ∑ α, (if t < infoMass (leafMass (α π).1) then Γ.mass α else (0 : ℝ)) ≤
        ∑ α, (if t < z α then Γ.mass α else (0 : ℝ)) := by
      refine Finset.sum_le_sum fun α _ => ?_
      by_cases ht : t < infoMass (leafMass (α π).1)
      · have hzα : t < z α :=
          lt_of_lt_of_le ht
            (Finset.le_sup' (fun σ => infoMass (leafMass (α σ).1)) (Finset.mem_univ π))
        simp [ht, hzα]
      · simp only [ht, ite_false, ge_iff_le]
        split_ifs
        · exact Γ.nonneg α
        · exact le_rfl
    have hF : 1 - Fstar T t =
        ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else 0) := by
      have hstar : Fstar T t = policyCDF T π t := rfl
      rw [hstar]
      exact (policy_info_tail T π t).symm
    exact le_trans (le_of_eq hF) (le_trans (le_of_eq hpart) hcmp)
  have hintTail :
      IntegrableOn (fun t : ℝ => ∑ α, (if t < z α then Γ.mass α else (0 : ℝ))) (Ioi (0 : ℝ)) := by
    have hint :=
      integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ)))
        (Finset.univ : Finset (Assignment T))
        (f := fun α (t : ℝ) => if t < z α then Γ.mass α else (0 : ℝ))
        (fun α _ => (hpiece α).integrable)
    simpa [IntegrableOn] using hint
  have hmono :=
    setIntegral_mono_on (integrableOn_one_sub_Fstar T) hintTail measurableSet_Ioi
      fun t _ => htail t
  rw [integral_one_sub_Fstar] at hmono
  linarith [hmono, hent, hlayer]

noncomputable instance {T : Tree} : DecidableEq (Assignment T) :=
  fun a b => Classical.propDecidable (a = b)

noncomputable instance {T : Tree} : DecidableEq (Strategy T) :=
  fun a b => Classical.propDecidable (a = b)

/-! Push an exact atom list onto the finitely many transcripts it realises. -/

noncomputable def atomMass {T : Tree} (atoms : List (Atom T)) (α : Assignment T) : ℝ :=
  (atoms.map fun a => if realizes a.2 = α then a.1 else 0).sum

theorem atomMass_nonneg {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) (α : Assignment T) : 0 ≤ atomMass atoms α := by
  induction atoms with
  | nil => simp [atomMass]
  | cons a tail ih =>
      simp only [atomMass, List.map_cons, List.sum_cons]
      exact add_nonneg (by split_ifs <;> simp [hnn a (by simp)])
        (ih fun b hb => hnn b (by simp [hb]))

theorem atomMass_cons {T : Tree} (a : Atom T) (tail : List (Atom T)) (α : Assignment T) :
    atomMass (a :: tail) α =
      (if realizes a.2 = α then a.1 else 0) + atomMass tail α := by
  simp [atomMass, List.map_cons, List.sum_cons]

theorem atomMass_total {T : Tree} (atoms : List (Atom T)) :
    ∑ α, atomMass atoms α = totalWeight atoms := by
  induction atoms with
  | nil => simp [atomMass, totalWeight]
  | cons a tail ih =>
      simp_rw [atomMass_cons, Finset.sum_add_distrib, ih]
      have hhead : ∑ α, (if realizes a.2 = α then a.1 else (0 : ℝ)) = a.1 := by
        rw [Finset.sum_ite_eq]
        simp
      rw [hhead]
      simp [totalWeight, List.map_cons, List.sum_cons]

theorem atomMass_marginal {T : Tree} (atoms : List (Atom T)) (π : Policy T) (ℓ : Leaf T) :
    ∑ α, (if (α π).1 = ℓ then atomMass atoms α else (0 : ℝ)) =
      transcriptWeight atoms π ℓ := by
  induction atoms with
  | nil => simp [atomMass, transcriptWeight]
  | cons a tail ih =>
      simp_rw [atomMass_cons, transcriptWeight_cons]
      have hsplit : ∀ α,
          (if (α π).1 = ℓ then
            (if realizes a.2 = α then a.1 else (0 : ℝ)) + atomMass tail α else 0) =
          (if (α π).1 = ℓ ∧ realizes a.2 = α then a.1 else 0) +
            (if (α π).1 = ℓ then atomMass tail α else 0) := by
        intro α
        by_cases hℓ : (α π).1 = ℓ <;> by_cases hr : realizes a.2 = α <;> simp [hℓ, hr]
      simp_rw [hsplit, Finset.sum_add_distrib, ih]
      have hhead :
          ∑ α, (if (α π).1 = ℓ ∧ realizes a.2 = α then a.1 else (0 : ℝ)) =
            if run a.2 π = ℓ then a.1 else 0 := by
        have hfun : ∀ α,
            (if (α π).1 = ℓ ∧ realizes a.2 = α then a.1 else (0 : ℝ)) =
              if realizes a.2 = α then (if run a.2 π = ℓ then a.1 else 0) else 0 := by
          intro α
          by_cases hr : realizes a.2 = α
          · subst hr
            simp [realizes]
          · simp [hr]
        rw [Finset.sum_congr rfl fun α _ => hfun α, Finset.sum_ite_eq]
        simp
      rw [hhead]

theorem exists_realizing_atom {T : Tree} (atoms : List (Atom T)) (α : Assignment T)
    (hne : atomMass atoms α ≠ 0) : ∃ a ∈ atoms, realizes a.2 = α := by
  induction atoms with
  | nil => simp [atomMass] at hne
  | cons a tail ih =>
      rw [atomMass_cons] at hne
      by_cases hr : realizes a.2 = α
      · exact ⟨a, by simp, hr⟩
      · simp only [hr, ite_false, zero_add] at hne
        obtain ⟨b, hb, hrb⟩ := ih hne
        exact ⟨b, by simp [hb], hrb⟩

theorem pmf_atomMass_le {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) :
    pmfEntropy (atomMass atoms) ≤ (atoms.map fun a => entTerm a.1).sum := by
  induction atoms with
  | nil => simp [pmfEntropy, atomMass, entTerm]
  | cons a tail ih =>
      have hnnTail : ∀ b ∈ tail, 0 ≤ b.1 := fun b hb => hnn b (by simp [hb])
      have hstep : ∀ α, entTerm (atomMass (a :: tail) α) ≤
          entTerm (if realizes a.2 = α then a.1 else 0) + entTerm (atomMass tail α) := by
        intro α
        rw [atomMass_cons]
        exact entTerm_add_le
          (by split_ifs <;> simp [hnn a (by simp)])
          (atomMass_nonneg tail hnnTail α)
      have hsum : pmfEntropy (atomMass (a :: tail)) ≤
          ∑ α, entTerm (if realizes a.2 = α then a.1 else (0 : ℝ)) +
            pmfEntropy (atomMass tail) := by
        unfold pmfEntropy
        have := Finset.sum_le_sum fun α (_ : α ∈ Finset.univ) => hstep α
        simpa [Finset.sum_add_distrib] using this
      have hhead : ∑ α, entTerm (if realizes a.2 = α then a.1 else (0 : ℝ)) = entTerm a.1 := by
        have hfun : ∀ α, entTerm (if realizes a.2 = α then a.1 else (0 : ℝ)) =
            if realizes a.2 = α then entTerm a.1 else 0 := by
          intro α
          by_cases hr : realizes a.2 = α
          · subst hr; simp [entTerm]
          · simp [hr, entTerm]
        rw [Finset.sum_congr rfl fun α _ => hfun α, Finset.sum_ite_eq]
        simp
      have htail : pmfEntropy (atomMass tail) ≤ (tail.map fun b => entTerm b.1).sum := ih hnnTail
      have hlist : ((a :: tail).map fun b => entTerm b.1).sum =
          entTerm a.1 + (tail.map fun b => entTerm b.1).sum := by
        simp
      linarith

noncomputable def couplingOfAtoms {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) (htot : totalWeight atoms = 1)
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    Coupling T where
  mass := atomMass atoms
  nonneg := atomMass_nonneg atoms hnn
  total := by rw [atomMass_total, htot]
  marginal := fun π ℓ hc => by rw [atomMass_marginal, hexact, if_pos hc]

theorem couplingOfAtoms_causal {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) (htot : totalWeight atoms = 1)
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    (couplingOfAtoms atoms hnn htot hexact).causal := by
  intro α hne
  obtain ⟨a, -, hr⟩ := exists_realizing_atom atoms α hne
  exact ⟨a.2, hr⟩

theorem couplingOfAtoms_badMass {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) (htot : totalWeight atoms = 1)
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    (couplingOfAtoms atoms hnn htot hexact).badMass = 0 :=
  badMass_eq_zero_of_causal (couplingOfAtoms_causal atoms hnn htot hexact)

theorem entTerm_list_eq {T : Tree} (atoms : List (Atom T)) (hpos : ∀ a ∈ atoms, 0 < a.1) :
    (atoms.map fun a => entTerm a.1).sum =
      (atoms.map fun a => a.1 * infoMass a.1).sum := by
  induction atoms with
  | nil => simp
  | cons a tail ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [entTerm_of_pos (hpos a (by simp))]
      exact congrArg (fun t => a.1 * infoMass a.1 + t)
        (ih fun b hb => hpos b (by simp [hb]))

theorem couplingOfAtoms_entropy_le {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) (hpos : ∀ a ∈ atoms, 0 < a.1) (htot : totalWeight atoms = 1)
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    (couplingOfAtoms atoms hnn htot hexact).entropy ≤ seedShannon atoms := by
  unfold Coupling.entropy
  refine le_trans (pmf_atomMass_le atoms hnn) ?_
  rw [entTerm_list_eq atoms hpos]
  rfl

/-! Causal and ordinary minima, and the gap they determine. -/

def couplingEntropySet (T : Tree) : Set ℝ :=
  {x | ∃ Γ : Coupling T, x = Γ.entropy}

def causalEntropySet (T : Tree) : Set ℝ :=
  {x | ∃ Γ : Coupling T, Γ.badMass = 0 ∧ x = Γ.entropy}

noncomputable def ordinaryMin (T : Tree) : ℝ := sInf (couplingEntropySet T)

noncomputable def causalMin (T : Tree) : ℝ := sInf (causalEntropySet T)

theorem couplingEntropySet_nonempty (T : Tree) : (couplingEntropySet T).Nonempty := by
  obtain ⟨atoms, -, hpos, htot, hexact, -, -⟩ := one_seed_shannon T
  have hnn : ∀ a ∈ atoms, 0 ≤ a.1 := fun a ha => (hpos a ha).le
  exact ⟨_, ⟨couplingOfAtoms atoms hnn htot hexact, rfl⟩⟩

theorem causalEntropySet_nonempty (T : Tree) : (causalEntropySet T).Nonempty := by
  obtain ⟨atoms, -, hpos, htot, hexact, -, -⟩ := one_seed_shannon T
  have hnn : ∀ a ∈ atoms, 0 ≤ a.1 := fun a ha => (hpos a ha).le
  exact ⟨(couplingOfAtoms atoms hnn htot hexact).entropy,
    ⟨couplingOfAtoms atoms hnn htot hexact,
      couplingOfAtoms_badMass atoms hnn htot hexact, rfl⟩⟩

theorem couplingEntropySet_bddBelow (T : Tree) : BddBelow (couplingEntropySet T) :=
  ⟨0, fun _ ⟨Γ, hx⟩ => hx ▸ entropy_nonneg Γ⟩

theorem causalEntropySet_bddBelow (T : Tree) : BddBelow (causalEntropySet T) :=
  ⟨0, fun _ ⟨Γ, _, hx⟩ => hx ▸ entropy_nonneg Γ⟩

theorem ordinaryMin_le_entropy {T : Tree} (Γ : Coupling T) :
    ordinaryMin T ≤ Γ.entropy :=
  csInf_le (couplingEntropySet_bddBelow T) ⟨Γ, rfl⟩

theorem causalMin_le_entropy_of_badMass {T : Tree} {Γ : Coupling T} (h : Γ.badMass = 0) :
    causalMin T ≤ Γ.entropy :=
  csInf_le (causalEntropySet_bddBelow T) ⟨Γ, h, rfl⟩

theorem entropy_ge_ordinaryMin {T : Tree} {x : ℝ} (hx : x ∈ couplingEntropySet T) :
    ordinaryMin T ≤ x :=
  csInf_le (couplingEntropySet_bddBelow T) hx

theorem ordinaryMin_ge_envelope (T : Tree) : envelopeMean T ≤ ordinaryMin T := by
  refine le_csInf (couplingEntropySet_nonempty T) ?_
  intro x hx
  obtain ⟨Γ, hx⟩ := hx
  simpa [hx] using entropy_ge_envelope Γ

theorem causalMin_le_overhead (T : Tree) :
    causalMin T ≤ envelopeMean T + shannonOverhead := by
  obtain ⟨atoms, -, hpos, htot, hexact, -, hhi⟩ := one_seed_shannon T
  have hnn : ∀ a ∈ atoms, 0 ≤ a.1 := fun a ha => (hpos a ha).le
  let Γ := couplingOfAtoms atoms hnn htot hexact
  have hle : causalMin T ≤ Γ.entropy :=
    causalMin_le_entropy_of_badMass (couplingOfAtoms_badMass atoms hnn htot hexact)
  exact le_trans hle (le_trans (couplingOfAtoms_entropy_le atoms hnn hpos htot hexact) hhi)

theorem causalEntropySet_subset (T : Tree) :
    causalEntropySet T ⊆ couplingEntropySet T := by
  intro x ⟨Γ, _, hx⟩
  exact ⟨Γ, hx⟩

theorem ordinaryMin_le_causalMin (T : Tree) : ordinaryMin T ≤ causalMin T := by
  have hsub : causalEntropySet T ⊆ couplingEntropySet T := causalEntropySet_subset T
  exact csInf_le_csInf (couplingEntropySet_bddBelow T) (causalEntropySet_nonempty T) hsub

noncomputable def gapOf (T : Tree) : ℝ := causalMin T - ordinaryMin T

theorem gapOf_nonneg (T : Tree) : 0 ≤ gapOf T := by
  unfold gapOf
  linarith [ordinaryMin_le_causalMin T]

theorem gapOf_le_overhead (T : Tree) : gapOf T ≤ shannonOverhead := by
  unfold gapOf
  linarith [causalMin_le_overhead T, ordinaryMin_ge_envelope T]

def gapSet : Set ℝ := {x | ∃ T : Tree, x = gapOf T}

noncomputable def gapSup : ℝ := sSup gapSet

theorem gapSet_nonempty : gapSet.Nonempty :=
  ⟨gapOf Tree.leaf, Tree.leaf, rfl⟩

theorem gapSet_bddAbove : BddAbove gapSet :=
  ⟨shannonOverhead, fun _ ⟨T, hx⟩ => hx ▸ gapOf_le_overhead T⟩

theorem gapOf_le_gapSup (T : Tree) : gapOf T ≤ gapSup :=
  le_csSup gapSet_bddAbove ⟨T, rfl⟩

theorem gapSup_nonneg : 0 ≤ gapSup :=
  le_trans (gapOf_nonneg Tree.leaf) (gapOf_le_gapSup Tree.leaf)

theorem gapSup_le_shannonOverhead : gapSup ≤ shannonOverhead :=
  csSup_le gapSet_nonempty fun _ ⟨T, hx⟩ => hx ▸ gapOf_le_overhead T

/-- `H(Γ) + κ Γ(B)`, for an arbitrary coefficient `κ`. -/
noncomputable def penalised {T : Tree} (κ : ℝ) (Γ : Coupling T) : ℝ :=
  Γ.entropy + κ * Γ.badMass

def penaltySet (κ : ℝ) (T : Tree) : Set ℝ :=
  {x | ∃ Γ : Coupling T, x = penalised κ Γ}

noncomputable def penaltyMin (κ : ℝ) (T : Tree) : ℝ := sInf (penaltySet κ T)

theorem penaltySet_nonempty (κ : ℝ) (T : Tree) : (penaltySet κ T).Nonempty := by
  obtain ⟨atoms, -, hpos, htot, hexact, -, -⟩ := one_seed_shannon T
  have hnn : ∀ a ∈ atoms, 0 ≤ a.1 := fun a ha => (hpos a ha).le
  let Γ := couplingOfAtoms atoms hnn htot hexact
  exact ⟨penalised κ Γ, Γ, rfl⟩

theorem exists_gap_gt {κ : ℝ} (hκ : κ < gapSup) : ∃ T : Tree, κ < gapOf T := by
  by_contra h
  push_neg at h
  have : gapSup ≤ κ := csSup_le gapSet_nonempty fun _ ⟨T, hx⟩ => hx ▸ h T
  linarith

/-- A nonnegative coefficient strictly below the gap is not universal. -/
theorem penalty_shortfall {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ : κ < gapSup) :
    ∃ T : Tree, penaltyMin κ T < causalMin T := by
  obtain ⟨T, hT⟩ := exists_gap_gt hκ
  have hroom : ordinaryMin T + κ < causalMin T := by
    unfold gapOf at hT
    linarith
  let ε : ℝ := (causalMin T - (ordinaryMin T + κ)) / 2
  have hε : 0 < ε := by
    unfold ε
    linarith
  have hex : ∃ Γ : Coupling T, Γ.entropy < ordinaryMin T + ε := by
    by_contra hnone
    push_neg at hnone
    have : ordinaryMin T + ε ≤ ordinaryMin T :=
      le_csInf (couplingEntropySet_nonempty T) fun x hx => by
        obtain ⟨Γ, hx⟩ := hx
        simpa [hx] using hnone Γ
    linarith
  obtain ⟨Γ, hH⟩ := hex
  have hpen : penalised κ Γ < causalMin T := by
    unfold penalised
    have hη : Γ.badMass ≤ 1 := badMass_le_one Γ
    have hκη : κ * Γ.badMass ≤ κ := by
      simpa using mul_le_mul_of_nonneg_left hη hκ0
    have hstep : Γ.entropy + κ < ordinaryMin T + ε + κ := by linarith [hH]
    have hmid : ordinaryMin T + ε + κ = (ordinaryMin T + κ + causalMin T) / 2 := by
      unfold ε; ring
    have hlast : (ordinaryMin T + κ + causalMin T) / 2 < causalMin T := by linarith [hroom]
    calc
      Γ.entropy + κ * Γ.badMass ≤ Γ.entropy + κ := by linarith
      _ < ordinaryMin T + ε + κ := hstep
      _ = (ordinaryMin T + κ + causalMin T) / 2 := hmid
      _ < causalMin T := hlast
  have hbdd : BddBelow (penaltySet κ T) :=
    ⟨0, fun x ⟨Δ, hx⟩ => hx ▸ add_nonneg (entropy_nonneg Δ) (mul_nonneg hκ0 (badMass_nonneg Δ))⟩
  exact ⟨T, lt_of_le_of_lt (csInf_le hbdd ⟨Γ, rfl⟩) hpen⟩

/-! A nonnegative flow, with zero branches deleted, is again a controlled tree.
The transparent pruned tree and the leaf-mass transport are in
`CausalSeed/Transport.lean`. The identity at every bad mass is
`causalMin_le_penalised`. -/

noncomputable def supportOf {n : ℕ} (mass : Fin n → ℝ) : Finset (Fin n) :=
  Finset.univ.filter fun y => 0 < mass y

noncomputable def yOf {n : ℕ} (mass : Fin n → ℝ) (i : Fin (supportOf mass).card) : Fin n :=
  ((supportOf mass).equivFin.symm i).1

noncomputable def indexOf {n : ℕ} (mass : Fin n → ℝ) {y : Fin n}
    (hy : y ∈ supportOf mass) : Fin (supportOf mass).card :=
  (supportOf mass).equivFin ⟨y, hy⟩

theorem supportOf_card_pos {n : ℕ} {mass : Fin n → ℝ}
    (hsum : 0 < ∑ y, mass y) (hnn : ∀ y, 0 ≤ mass y) :
    0 < (supportOf mass).card := by
  have hex : ∃ y, 0 < mass y := by
    by_contra h
    have hall : ∀ y, mass y ≤ 0 := by
      intro y
      have : ¬ 0 < mass y := by
        intro hy
        exact h ⟨y, hy⟩
      exact le_of_not_gt this
    have hle : ∑ y, mass y ≤ 0 := Finset.sum_nonpos fun y _ => hall y
    linarith
  obtain ⟨y, hy⟩ := hex
  exact Finset.card_pos.mpr ⟨y, by simp [supportOf, hy]⟩

theorem yOf_indexOf {n : ℕ} (mass : Fin n → ℝ) {y : Fin n}
    (hy : y ∈ supportOf mass) : yOf mass (indexOf mass hy) = y := by
  simp [yOf, indexOf]

theorem sum_yOf {n : ℕ} (mass : Fin n → ℝ) (hnn : ∀ y, 0 ≤ mass y) :
    ∑ i, mass (yOf mass i) = ∑ y, mass y := by
  classical
  have hzero : ∀ y, y ∉ supportOf mass → mass y = 0 := by
    intro y hy
    exact le_antisymm
      (le_of_not_gt fun hpos => hy (by simp [supportOf, hpos])) (hnn y)
  have hfull : ∑ y, mass y = ∑ y, (if y ∈ supportOf mass then mass y else (0 : ℝ)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hy : y ∈ supportOf mass
    · simp [hy]
    · simp [hy, hzero y hy]
  have hfilter : ∑ y, (if y ∈ supportOf mass then mass y else (0 : ℝ)) =
      ∑ y ∈ supportOf mass, mass y := by
    symm
    simpa using
      (Finset.sum_filter (Finset.univ : Finset (Fin n)) (fun y => y ∈ supportOf mass) mass)
  have hsub : ∑ y ∈ supportOf mass, mass y =
      ∑ z : {y // y ∈ supportOf mass}, mass z.val := by
    simpa using (Finset.sum_attach (supportOf mass) mass).symm
  have hequiv : ∑ z : {y // y ∈ supportOf mass}, mass z.val =
      ∑ i, mass (yOf mass i) := by
    exact Fintype.sum_equiv (supportOf mass).equivFin
      (fun z => mass z.val) (fun i => mass (yOf mass i))
      (fun z => by simp [yOf])
  linarith

noncomputable def pruned : {T : Tree} → (r : Field T) → Field.IsFlow r → Field.Nonneg r → Tree
  | .leaf, _, _, _ => .leaf
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn =>
      if hr : 0 < Field.root r then
        Tree.node nA hA
          (fun a => (supportOf (fun y => Field.root (r.2 a y))).card)
          (fun a => supportOf_card_pos
            (by simpa [Field.root] using (lt_of_lt_of_eq hr (hf.1 a).symm))
            (fun y => (hn.2 a y).root_nonneg))
          (fun a i =>
            Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) / Field.root r)
          (fun a i => by
            have hmem :=
              ((supportOf (fun y => Field.root (r.2 a y))).equivFin.symm i).2
            have hy : 0 < Field.root
                (r.2 a (((supportOf (fun y => Field.root (r.2 a y))).equivFin.symm i).1)) :=
              (Finset.mem_filter.mp hmem).2
            simpa [yOf] using div_pos hy hr)
          (fun a => by
            have hdiv : ∑ i,
                Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) / Field.root r =
                (∑ i, Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))) /
                  Field.root r := by
              simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
            rw [hdiv, sum_yOf (fun y => Field.root (r.2 a y)) (fun y => (hn.2 a y).root_nonneg)]
            have hflow : ∑ y, Field.root (r.2 a y) = Field.root r := by
              simpa [Field.root] using hf.1 a
            rw [hflow]
            field_simp)
          (fun a i =>
            pruned (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
              (hf.2 a _) (hn.2 a _))
      else
        .leaf

noncomputable def leafEmb : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → Leaf (pruned r hf hn) → Leaf T
  | .leaf, _, _, _, _ => defaultLeaf Tree.leaf
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, ℓ =>
      if hr : 0 < Field.root r then by
        have ℓ' : (a : Fin nA) ×'
            ((i : Fin (supportOf (fun y => Field.root (r.2 a y))).card) ×'
              Leaf (pruned (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
                (hf.2 a _) (hn.2 a _))) := by
          simpa [pruned, hr, Leaf] using ℓ
        rcases ℓ' with ⟨a, i, ℓc⟩
        let y := yOf (fun y => Field.root (r.2 a y)) i
        exact ⟨a, y, leafEmb (r.2 a y) (hf.2 a y) (hn.2 a y) ℓc⟩
      else
        defaultLeaf _

/-- Vanishing inconsistent mass is already a causal coupling. -/
theorem causalMin_le_penalised_of_zero {T : Tree} {Γ : Coupling T} {κ : ℝ}
    (h : Γ.badMass = 0) : causalMin T ≤ penalised κ Γ := by
  unfold penalised
  rw [h, mul_zero, add_zero]
  exact causalMin_le_entropy_of_badMass h

/-- A fully inconsistent coupling pays the whole gap. -/
theorem causalMin_le_penalised_of_one {T : Tree} (Γ : Coupling T)
    (h : Γ.badMass = 1) : causalMin T ≤ penalised gapSup Γ := by
  unfold penalised
  rw [h, mul_one]
  have hgap : causalMin T ≤ ordinaryMin T + gapSup := by
    have := gapOf_le_gapSup T
    unfold gapOf at this
    linarith
  linarith [ordinaryMin_le_entropy Γ, hgap]

#print axioms entropy_ge_envelope
#print axioms gapSup_le_shannonOverhead
#print axioms penalty_shortfall
#print axioms causalMin_le_penalised_of_one

end CausalSpectrum




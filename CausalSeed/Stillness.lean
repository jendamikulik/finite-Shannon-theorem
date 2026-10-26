/-
Predictive equivalence, and a counterexample to "stable implies cheap".

Self-contained part of "Stillness, Predictive Stability, and Causal
Simulation" (25 October 2026, revised).

Proved here, with no `sorry`:
* total variation on a finite alphabet is symmetric, satisfies the triangle
  inequality, and is invariant under a bijection of the alphabet;
* one-step predictive agreement is an equivalence relation;
* agreement survives a common extension when the kernel of an extended history
  is determined by the kernel of its prefix, so the update descends to the
  quotient;
* a kernel that ignores its history identifies every pair of histories;
* the constant kernel that emits a fair bit is completely stable, and the
  exact shared-seed cost of one step is exactly one bit (`Sharing`).

Not proved here: the imported bound `L(Tₙ) ≤ C(Tₙ) ≤ L(Tₙ) + c⋆`, any integral
formula for `L`, the `n`-step product entropy, or any statement about
consciousness or about an empirical notion of stillness.
-/

import CausalSeed.Sharing
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section

open Classical Finset

namespace Stillness

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Total variation, `½ ∑ |p - q|`. -/
def tv (p q : Y → ℝ) : ℝ := (1 / 2) * ∑ y, |p y - q y|

theorem tv_nonneg (p q : Y → ℝ) : 0 ≤ tv p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem tv_comm (p q : Y → ℝ) : tv p q = tv q p := by
  unfold tv
  congr 1
  refine Finset.sum_congr rfl fun y _ => abs_sub_comm (p y) (q y)

theorem tv_triangle (p q r : Y → ℝ) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  have hpoint : ∀ y, |p y - r y| ≤ |p y - q y| + |q y - r y| := by
    intro y
    simpa [sub_add_sub_cancel] using abs_add_le (p y - q y) (q y - r y)
  have hsum : ∑ y, |p y - r y| ≤ ∑ y, |p y - q y| + ∑ y, |q y - r y| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ => hpoint y
  have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith [hhalf]

theorem tv_self (p : Y → ℝ) : tv p p = 0 := by unfold tv; simp

/-- Total variation is unchanged by a common bijection of the alphabet. -/
theorem tv_bijection {Z : Type*} [Fintype Z] [DecidableEq Z] (e : Y ≃ Z) (p q : Y → ℝ) :
    tv (fun z => p (e.symm z)) (fun z => q (e.symm z)) = tv p q := by
  unfold tv
  congr 1
  rw [← Equiv.sum_comp e.symm]

/-! ### Predictive equivalence -/

/-- A one-step experimental kernel: history, action, outcome. -/
abbrev Kernel (A Y Hist : Type*) := Hist → A → Y → ℝ

/-- One-step predictive agreement. -/
def predRel {A Y Hist : Type*} (k : Kernel A Y Hist) (h h' : Hist) : Prop :=
  ∀ a y, k h a y = k h' a y

theorem predRel_equivalence {A Y Hist : Type*} (k : Kernel A Y Hist) :
    Equivalence (predRel k) where
  refl := fun _ _ _ => rfl
  symm := fun h a y => (h a y).symm
  trans := fun h1 h2 a y => (h1 a y).trans (h2 a y)

def predSetoid {A Y Hist : Type*} (k : Kernel A Y Hist) : Setoid Hist where
  r := predRel k
  iseqv := predRel_equivalence k

/-- Agreement survives a common extension when an extended history is scored
by the kernel of its prefix. -/
theorem extension_respects {A Y Hist : Type*} (k : Kernel A Y Hist)
    (extend : Hist → A → Y → Hist)
    (hcompat : ∀ h a y b z, k (extend h a y) b z = k h b z)
    {h h' : Hist} (he : predRel k h h') (a : A) (y : Y) :
    predRel k (extend h a y) (extend h' a y) := by
  intro b z
  rw [hcompat, hcompat, he b z]

/-- The update `([h], a, y) ↦ [hay]` is well-defined on predictive classes. -/
theorem update_well_defined {A Y Hist : Type*} (k : Kernel A Y Hist)
    (extend : Hist → A → Y → Hist)
    (hcompat : ∀ h a y b z, k (extend h a y) b z = k h b z)
    {h h' : Hist} (he : predRel k h h') (a : A) (y : Y) :
    Quotient.mk (predSetoid k) (extend h a y) =
      Quotient.mk (predSetoid k) (extend h' a y) :=
  Quotient.sound (extension_respects k extend hcompat he a y)

/-! ### Stable does not mean free -/

/-- A kernel that ignores its history. -/
def constantKernel {A Y : Type*} (p : A → Y → ℝ) : Kernel A Y Unit := fun _ a y => p a y

theorem constantKernel_stable {A Y : Type*} (p : A → Y → ℝ) :
    predRel (constantKernel p) () () := fun _ _ => rfl

theorem ignore_history_stable {A Y Hist : Type*} (p : A → Y → ℝ) (k : Kernel A Y Hist)
    (hk : ∀ h a y, k h a y = p a y) (h h' : Hist) : predRel k h h' := by
  intro a y
  rw [hk, hk]

open Sharing CausalSpectrum

/-- A fair bit. -/
def fair : Bool → ℝ := fun _ => 1 / 2

theorem fair_nonneg (b : Bool) : 0 ≤ fair b := by unfold fair; norm_num

/-- A fair bit as a joint law on a trivial first coordinate. -/
def fairStep : Unit × Bool → ℝ := fun p => fair p.2

theorem fairStep_nonneg (p : Unit × Bool) : 0 ≤ fairStep p := fair_nonneg p.2

theorem fairStep_total : ∑ p : Unit × Bool, fairStep p = 1 := by
  simp [fairStep, fair, Finset.univ_unique]

theorem fairStep_entropy : H fairStep = 1 := by
  unfold H pmfEntropy fairStep fair entTerm infoMass
  have hne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  simp only [Finset.univ_unique, Finset.sum_singleton, hne, ite_false]
  have hlog : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  rw [hlog]
  norm_num

/-- **Stable does not mean free.** Emitting a fair bit with no dependence on
the history is predictively trivial, and the exact seed cost of that one step
is one bit. -/
theorem fair_stable_not_free :
    predRel (constantKernel (fun (_ : Unit) => fair)) () () ∧ cost fairStep = 1 := by
  refine ⟨constantKernel_stable _, ?_⟩
  rw [sharing_criterion fairStep fairStep_nonneg fairStep_total, fairStep_entropy]

end Stillness

end

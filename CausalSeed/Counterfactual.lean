/-
Counterfactual width for one-shot fair binary outputs.

corr: all actions return the same fair bit. Entropy 1.
indep: uniform on strategies. Entropy m.
Width = m - 1.

Status: constructions are correct; the remaining sum and fiber-cardinality
manipulations are not yet closed. No `sorry` in the mathematical claims,
but the file does not currently build.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

noncomputable section
open Finset

namespace Counterfactual

abbrev S (m : ℕ) := Fin m → Bool

noncomputable def H {m : ℕ} (μ : S m → ℝ) : ℝ :=
  -∑ s, if μ s = 0 then 0 else μ s * Real.logb 2 (μ s)

def corr (m : ℕ) (s : S m) : ℝ :=
  if (s = fun _ => false) ∨ (s = fun _ => true) then 1/2 else 0

theorem corr_H (m : ℕ) (hm : 0 < m) : H (corr m) = 1 := by
  unfold H
  classical
  have hlog : Real.logb 2 ((1:ℝ)/2) = -1 := by
    rw [← Real.log_div_log]
    rw [show Real.log ((1:ℝ)/2) = -Real.log 2 by
      rw [div_eq_mul_inv, Real.log_mul one_ne_zero (inv_ne_zero two_ne_zero),
          Real.log_one, Real.log_inv, zero_add]]
    field_simp
  have hne : (fun _ : Fin m => false) ≠ (fun _ => true) := by
    intro h; have := congr_fun h ⟨0, hm⟩; simp at this
  -- Only two terms nonzero.
  have h1 : corr m (fun _ => false) = 1/2 := by simp [corr]
  have h2 : corr m (fun _ => true) = 1/2 := by simp [corr]
  have hother : ∀ s, s ≠ fun _ => false → s ≠ fun _ => true → corr m s = 0 := by
    intro s hf ht; simp [corr, hf, ht]
  rw [sum_eq_add_sum_diff_singleton (fun _ => false) (mem_univ _)]
  rw [sum_eq_add_sum_diff_singleton (fun _ => true)]
  · simp [h1, h2, hlog, hne]
    ring
  · simp [hne]
  · intro s hs; simp [hother s (by simp at hs; tauto) (by simp at hs; tauto)]

def indep (m : ℕ) (_ : S m) : ℝ := 1 / (2 ^ m : ℝ)

theorem indep_H (m : ℕ) : H (indep m) = m := by
  unfold H indep
  have hne : (1 / (2^m : ℝ)) ≠ 0 := by positivity
  simp only [hne, ite_false]
  have hlog : Real.logb 2 (1 / (2^m : ℝ)) = -(m : ℝ) := by
    rw [← Real.log_div_log]
    have : Real.log (1 / (2^m : ℝ)) = - (m : ℝ) * Real.log 2 := by
      rw [div_eq_mul_inv, Real.log_mul (by norm_num) (by positivity),
          Real.log_one, Real.log_inv, Real.log_pow]
      ring
    rw [this]
    field_simp
    ring
  rw [hlog, sum_const, card_univ]
  simp [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, nsmul_eq_mul]
  field_simp; ring

theorem width (m : ℕ) (hm : 0 < m) : H (indep m) - H (corr m) = (m - 1 : ℝ) := by
  rw [indep_H, corr_H m hm]; ring

end Counterfactual

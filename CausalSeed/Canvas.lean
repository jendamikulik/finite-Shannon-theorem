/-
The picture is not in either half.

Two pure states of two bits can carry the same local statistics and still be
orthogonal. A function can satisfy `F(s) = F(1-s)` and still vanish off the
critical line. A nonnegative function that is strictly higher beside the
origin than at the origin cannot vanish there. None of these is a theorem
about `ξ`, and none of them is a proof of the Riemann hypothesis.

Proved, with no sorry:

* `Φ₊ = (|00⟩ + |11⟩)/√2` and `Φ₋ = (|00⟩ - |11⟩)/√2` are unit and orthogonal;
* each computational-basis marginal, on either factor, is the fair bit `1/2`;
* in the `X` basis, `Φ₊` always agrees and `Φ₋` never does, while each
  single-side outcome is still fair;
* `F(s) = (s - 1/2)² - 1/16` obeys `F(s) = F(1-s)`, vanishes at `1/4` and
  `3/4`, and does not vanish at `1/2`;
* if `0 ≤ M(0)` and `M(0) < M(x)` for every `x ∈ (0, 1/2)`, then `M` has no
  zero on that interval. Symmetry is not used. The rise is stronger than the
  absence of a zero: `(x - 1/4)² + 1/16` never vanishes and still dips.

Not proved: that `|ξ(1/2 + x + it)|²` satisfies the strict inequality; the
Riemann hypothesis; that a dynamics written on one page is an experience.
The inequality is the step the picture does not take.
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

noncomputable section

open Finset

namespace CausalSpectrum
namespace Canvas

def sqrt2inv : ℝ := 1 / Real.sqrt 2

theorem sqrt2inv_sq : sqrt2inv ^ 2 = 1 / 2 := by
  unfold sqrt2inv
  rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

theorem sqrt2inv_pos : 0 < sqrt2inv := by
  unfold sqrt2inv
  exact one_div_pos.mpr (Real.sqrt_pos.mpr (by norm_num))

/-- `|00⟩ + |11⟩`, normalized. Outcomes are a pair of bits. -/
def Φplus (b r : Fin 2) : ℝ :=
  if b = r then sqrt2inv else 0

/-- `|00⟩ - |11⟩`, normalized. -/
def Φminus (b r : Fin 2) : ℝ :=
  if b = r then (if b = 0 then sqrt2inv else -sqrt2inv) else 0

def mass (ψ : Fin 2 → Fin 2 → ℝ) (b : Fin 2) : ℝ :=
  ∑ r, ψ b r ^ 2

theorem two_inv_cubes :
    2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) = (Real.sqrt 2)⁻¹ := by
  have hne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  field_simp [hne]
  exact (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)).symm

theorem plus_left (b : Fin 2) : mass Φplus b = 1 / 2 := by
  fin_cases b <;> simp [mass, Φplus, sqrt2inv_sq]

theorem minus_left (b : Fin 2) : mass Φminus b = 1 / 2 := by
  fin_cases b <;> simp [mass, Φminus, sqrt2inv_sq]

theorem plus_right (r : Fin 2) : (∑ b, Φplus b r ^ 2) = 1 / 2 := by
  fin_cases r <;> simp [Φplus, sqrt2inv_sq]

theorem minus_right (r : Fin 2) : (∑ b, Φminus b r ^ 2) = 1 / 2 := by
  fin_cases r <;> simp [Φminus, sqrt2inv_sq]

theorem same_left (b : Fin 2) : mass Φplus b = mass Φminus b := by
  rw [plus_left, minus_left]

theorem plus_unit : (∑ b, ∑ r, Φplus b r ^ 2) = 1 := by
  simp [Φplus, sqrt2inv_sq]

theorem minus_unit : (∑ b, ∑ r, Φminus b r ^ 2) = 1 := by
  simp [Φminus, sqrt2inv_sq]

theorem orthogonal : (∑ b, ∑ r, Φplus b r * Φminus b r) = 0 := by
  simp [Φplus, Φminus]

theorem wholes_differ : Φplus ≠ Φminus := by
  intro h
  have := congr_fun (congr_fun h 1) 1
  simp [Φplus, Φminus] at this
  linarith [sqrt2inv_pos]

/-- `0` is the plus outcome of `X`, `1` the minus outcome. -/
def xAmp (ε i : Fin 2) : ℝ :=
  if ε = 0 then sqrt2inv else if i = 0 then sqrt2inv else -sqrt2inv

def xJoint (ψ : Fin 2 → Fin 2 → ℝ) (ε₁ ε₂ : Fin 2) : ℝ :=
  ∑ b, ∑ r, xAmp ε₁ b * xAmp ε₂ r * ψ b r

theorem plus_x_agree (ε : Fin 2) : xJoint Φplus ε ε = sqrt2inv := by
  fin_cases ε
  · simp [xJoint, Φplus, xAmp, sqrt2inv]
    exact two_inv_cubes
  · simp [xJoint, Φplus, xAmp, sqrt2inv]
    have hsum :
        (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ +
            (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹
          = 2 * ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹) := by ring
    rw [hsum]
    exact two_inv_cubes

theorem plus_x_disagree (ε₁ ε₂ : Fin 2) (h : ε₁ ≠ ε₂) : xJoint Φplus ε₁ ε₂ = 0 := by
  fin_cases ε₁ <;> fin_cases ε₂ <;> simp_all [xJoint, Φplus, xAmp, sqrt2inv]

theorem minus_x_agree (ε : Fin 2) : xJoint Φminus ε ε = 0 := by
  fin_cases ε <;> simp [xJoint, Φminus, xAmp, sqrt2inv]

theorem minus_x_disagree (ε₁ ε₂ : Fin 2) (h : ε₁ ≠ ε₂) :
    xJoint Φminus ε₁ ε₂ = sqrt2inv := by
  fin_cases ε₁ <;> fin_cases ε₂ <;> simp_all [xJoint, Φminus, xAmp, sqrt2inv] <;>
    exact two_inv_cubes

theorem plus_always_agrees (ε₁ ε₂ : Fin 2) :
    xJoint Φplus ε₁ ε₂ ^ 2 = if ε₁ = ε₂ then 1 / 2 else 0 := by
  by_cases h : ε₁ = ε₂
  · rw [h, plus_x_agree, sqrt2inv_sq, ite_eq_left rfl]
  · rw [plus_x_disagree ε₁ ε₂ h, ite_eq_right h]
    norm_num

theorem minus_never_agrees (ε₁ ε₂ : Fin 2) :
    xJoint Φminus ε₁ ε₂ ^ 2 = if ε₁ = ε₂ then 0 else 1 / 2 := by
  by_cases h : ε₁ = ε₂
  · rw [h, minus_x_agree, ite_eq_left rfl]
    norm_num
  · rw [minus_x_disagree ε₁ ε₂ h, ite_eq_right h, sqrt2inv_sq]

/-- One fair bit on the left, in the basis that sees the picture. -/
theorem plus_x_left (ε : Fin 2) :
    (∑ ε₂, xJoint Φplus ε ε₂ ^ 2) = 1 / 2 := by
  fin_cases ε <;> simp [plus_always_agrees]

theorem minus_x_left (ε : Fin 2) :
    (∑ ε₂, xJoint Φminus ε ε₂ ^ 2) = 1 / 2 := by
  fin_cases ε <;> simp [Fin.sum_univ_two, minus_never_agrees]

/-! Symmetry of a whole does not place each zero. -/

def F (s : ℝ) : ℝ := (s - 1 / 2) ^ 2 - 1 / 16

theorem F_reflect (s : ℝ) : F s = F (1 - s) := by
  unfold F
  ring

theorem F_quarter : F (1 / 4) = 0 := by
  unfold F
  norm_num

theorem F_three_quarters : F (3 / 4) = 0 := by
  unfold F
  norm_num

theorem F_on_the_line : F (1 / 2) = -1 / 16 := by
  unfold F
  norm_num

/-- The zero set is invariant, and neither zero lies on the critical line. -/
theorem mirror_moves_the_zero :
    F (1 / 4) = 0 ∧ F (1 - 1 / 4) = 0 ∧
      (1 / 4 : ℝ) ≠ 1 / 2 ∧ (1 - 1 / 4 : ℝ) ≠ 1 / 2 ∧ (1 / 4 : ℝ) ≠ 1 - 1 / 4 := by
  have h3 : (1 - (1 / 4 : ℝ)) = 3 / 4 := by norm_num
  refine ⟨F_quarter, ?_, ?_, ?_, ?_⟩
  · rw [h3]; exact F_three_quarters
  · norm_num
  · rw [h3]; norm_num
  · norm_num

/-- The missing step. Nonnegativity at the origin and a strict rise beside it. -/
theorem sharpness_blocks_the_side (M : ℝ → ℝ) (h0 : 0 ≤ M 0)
    (hsharp : ∀ x, 0 < x → x < 1 / 2 → M 0 < M x) :
    ∀ x, 0 < x → x < 1 / 2 → M x ≠ 0 := by
  intro x hx hxhalf hzero
  have hlt := hsharp x hx hxhalf
  rw [hzero] at hlt
  exact not_le_of_gt hlt h0

/-- A strict rise forbids a side zero, and a side zero is not the only way the rise can fail. -/
def dip (x : ℝ) : ℝ := (x - 1 / 4) ^ 2 + 1 / 16

theorem dip_pos (x : ℝ) : 0 < dip x := by
  unfold dip
  have hsq : 0 ≤ (x - 1 / 4) ^ 2 := sq_nonneg _
  linarith

theorem dip_not_sharp : dip (1 / 4) < dip 0 := by
  unfold dip
  norm_num

theorem rise_stronger_than_no_zero :
    (∀ x, 0 < x → x < 1 / 2 → dip x ≠ 0) ∧
      ¬ (∀ x, 0 < x → x < 1 / 2 → dip 0 < dip x) := by
  refine ⟨?_, ?_⟩
  · intro x _ _
    exact ne_of_gt (dip_pos x)
  · intro h
    have hlt := h (1 / 4) (by norm_num) (by norm_num)
    exact not_lt_of_gt dip_not_sharp hlt

end Canvas
end CausalSpectrum

end

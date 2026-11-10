/-
The horizontal field of a zero.

A zero of multiplicity `m > 0` at `β + iγ` contributes
`m (σ - β) / ((σ - β)² + (t - γ)²)` to `∂_σ log` of the modulus.
On the horizontal line through the zero this is `m / (σ - β)`.
Approached from the left it goes to `-∞`.

Proved, with no sorry:

* that formula is the `σ`-derivative of `(m / 2) log((σ - β)² + (t - γ)²)`;
* on `t = γ` it reduces to `m / (σ - β)`;
* a mirror pair at `β` and `1 - β` cancels on the critical line, and the
  cancellation does not move either zero onto the line;
* if the field is nonnegative everywhere to the right of `1/2`, off the
  zeros, then no zero has real part greater than `1/2`. Symmetry of the
  zero set then forbids every off-axis zero. A bounded regular term does
  not stop the blow-up.

Not proved: that `∂_σ log|ξ(σ + it)|` is nonnegative to the right of the
critical line; the Riemann hypothesis. The sign is the missing step.
Gravity supplies the language of a potential. It does not supply the law
that would force the sign.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic

noncomputable section

open Classical

namespace CausalSpectrum
namespace Attraction

/-- Horizontal part of the field of one zero. -/
def pole (m β γ σ t : ℝ) : ℝ :=
  m * (σ - β) / ((σ - β) ^ 2 + (t - γ) ^ 2)

theorem hasDerivAt_pole {m β γ σ t : ℝ}
    (hpos : 0 < (σ - β) ^ 2 + (t - γ) ^ 2) :
    HasDerivAt (fun σ => (m / 2) * Real.log ((σ - β) ^ 2 + (t - γ) ^ 2))
      (pole m β γ σ t) σ := by
  have hsub : HasDerivAt (fun σ : ℝ => σ - β) 1 σ :=
    (hasDerivAt_id σ).sub_const β
  have hsq : HasDerivAt (fun σ => (σ - β) ^ 2) (2 * (σ - β)) σ := by
    have hmul := (hsub.mul hsub).congr_deriv
      (by ring : 1 * (σ - β) + (σ - β) * 1 = 2 * (σ - β))
    have hfun : (fun σ => σ - β) * (fun σ => σ - β) = fun σ => (σ - β) ^ 2 := by
      funext y
      simp [Pi.mul_apply]
      ring
    rw [hfun] at hmul
    exact hmul
  have hu : HasDerivAt (fun σ => (σ - β) ^ 2 + (t - γ) ^ 2) (2 * (σ - β)) σ :=
    hsq.add_const ((t - γ) ^ 2)
  have hlog : HasDerivAt Real.log (((σ - β) ^ 2 + (t - γ) ^ 2)⁻¹)
      ((σ - β) ^ 2 + (t - γ) ^ 2) :=
    Real.hasDerivAt_log (ne_of_gt hpos)
  have hcomp := hlog.comp σ hu
  have hmul := hcomp.const_mul (m / 2)
  refine hmul.congr_deriv ?_
  unfold pole
  have hne : (σ - β) ^ 2 + (t - γ) ^ 2 ≠ 0 := ne_of_gt hpos
  field_simp [hne]

theorem horizontal {m β γ σ : ℝ} (h : σ ≠ β) :
    pole m β γ σ γ = m / (σ - β) := by
  unfold pole
  have hden : (σ - β) ^ 2 + (γ - γ) ^ 2 = (σ - β) ^ 2 := by ring
  rw [hden]
  have hne : (σ - β) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr h)
  field_simp [hne]

/-- A mirror pair cancels on the critical line. Neither zero has moved. -/
theorem mirror_cancels (m β γ t : ℝ) :
    pole m β γ (1 / 2) t + pole m (1 - β) γ (1 / 2) t = 0 := by
  unfold pole
  have hsame : (1 / 2 - (1 - β)) ^ 2 + (t - γ) ^ 2 =
      (1 / 2 - β) ^ 2 + (t - γ) ^ 2 := by ring
  rw [hsame]
  field_simp
  ring

/-- Nonnegativity on the right half, plus a bounded regular term, forbids a
zero there. The approach is horizontal, from the left of the zero. -/
theorem sign_forbids_right_zero
    (S : ℝ → ℝ) {β m R : ℝ}
    (hm : 0 < m) (hβ : (1 / 2 : ℝ) < β)
    (hnear : ∀ σ, σ < β → |σ - β| < 1 →
      ∃ r, |r| ≤ |R| ∧ S σ = m / (σ - β) + r)
    (hsign : ∀ σ, (1 / 2 : ℝ) < σ → σ ≠ β → 0 ≤ S σ) :
    False := by
  let B := |R| + 1
  have hB : 0 < B := by
    dsimp [B]
    linarith [abs_nonneg R]
  let ε := min (min ((β - 1 / 2) / 2) (1 / 2)) (m / (2 * B))
  have hε : 0 < ε := by
    refine lt_min (lt_min ?_ (by norm_num)) ?_
    · exact div_pos (by linarith : 0 < β - 1 / 2) (by norm_num)
    · exact div_pos hm (mul_pos (by norm_num) hB)
  let σ := β - ε
  have hσlt : σ < β := by dsimp [σ]; linarith
  have hσgt : (1 / 2 : ℝ) < σ := by
    dsimp [σ]
    have hεle : ε ≤ (β - 1 / 2) / 2 :=
      le_trans (min_le_left _ _) (min_le_left _ _)
    linarith
  have habs : |σ - β| < 1 := by
    have heq : |σ - β| = ε := by
      dsimp [σ]
      rw [show β - ε - β = -ε by ring, abs_neg, abs_of_pos hε]
    rw [heq]
    have hεle : ε ≤ 1 / 2 := le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  obtain ⟨r, hr, hS⟩ := hnear σ hσlt habs
  have hquot : m / (σ - β) = -(m / ε) := by
    dsimp [σ]
    rw [show β - ε - β = -ε by ring]
    field_simp [hε.ne']
  have hle : ε ≤ m / (2 * B) := min_le_right _ _
  have hmul : ε * (2 * B) ≤ m := by
    rwa [le_div_iff₀ (mul_pos (by norm_num) hB)] at hle
  have hbig : 2 * B ≤ m / ε := by
    rw [le_div_iff₀ hε]
    linarith
  have hrle : r ≤ |R| := (le_abs_self r).trans hr
  have hSneg : S σ < 0 := by
    rw [hS, hquot]
    have hlt : |R| < m / ε := by
      have : |R| < 2 * B := by
        dsimp [B]
        linarith [abs_nonneg R]
      exact lt_of_lt_of_le this hbig
    linarith
  exact not_le_of_gt hSneg (hsign σ hσgt (ne_of_lt hσlt))

/-- Symmetry of the zero set passes the ban from the right half to the left. -/
theorem symmetry_clears_both_sides (Z : ℝ → Prop)
    (hsym : ∀ β, Z β ↔ Z (1 - β))
    (hright : ∀ β, (1 / 2 : ℝ) < β → ¬ Z β) :
    ∀ β, β ≠ 1 / 2 → ¬ Z β := by
  intro β hne hZ
  by_cases h : (1 / 2 : ℝ) < β
  · exact hright β h hZ
  · have hlt : β < 1 / 2 := lt_of_le_of_ne (le_of_not_gt h) hne
    have hmirror : (1 / 2 : ℝ) < 1 - β := by linarith
    exact hright (1 - β) hmirror ((hsym β).1 hZ)

/-- The field of a symmetric modulus flips sign across the critical line. -/
theorem reflected_field (S : ℝ → ℝ) (hS : ∀ σ, S σ = -S (1 - σ)) :
    (∀ σ, (1 / 2 : ℝ) < σ → 0 ≤ S σ) ↔
      (∀ σ, σ < 1 / 2 → S σ ≤ 0) := by
  constructor
  · intro h σ hσ
    have hright : (1 / 2 : ℝ) < 1 - σ := by linarith
    have h0 : 0 ≤ S (1 - σ) := h (1 - σ) hright
    rw [hS, show 1 - (1 - σ) = σ by ring] at h0
    linarith
  · intro h σ hσ
    have hleft : 1 - σ < 1 / 2 := by linarith
    have h0 : S (1 - σ) ≤ 0 := h (1 - σ) hleft
    rw [hS, show 1 - (1 - σ) = σ by ring] at h0
    linarith

end Attraction
end CausalSpectrum

end

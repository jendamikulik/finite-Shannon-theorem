/-
Strict exact penalty and quantitative stability.
Written against 36eb2b351303238d59e717c00404d17a127f542a.
Compiled in the lake build of 11 October 2026 (Lean 4.35.0-rc3, mathlib 7d6757bc).
This file is independent of the infinite-seed bridges.
-/
import CausalSeed.Identity

noncomputable section
namespace CausalSpectrum

/-- The objective excess pays at least `(κ - G*)` per unit of bad mass. -/
theorem strict_penalty_margin {T : Tree} (Γ : Coupling T) (κ : ℝ) :
    (κ - gapSup) * Γ.badMass ≤ penalised κ Γ - causalMin T := by
  have h := causalMin_le_penalised Γ
  unfold penalised at h ⊢
  nlinarith

/-- An ε-minimizer above the threshold has at most ε/(κ-G*) bad mass. -/
theorem near_minimizer_badMass_le {T : Tree} (Γ : Coupling T) {κ ε : ℝ}
    (hκ : gapSup < κ)
    (hε : penalised κ Γ ≤ penaltyMin κ T + ε) :
    Γ.badMass ≤ ε / (κ - gapSup) := by
  rw [penaltyMin_eq_causalMin hκ.le T] at hε
  apply (le_div_iff₀ (sub_pos.mpr hκ)).mpr
  have h := strict_penalty_margin Γ κ
  nlinarith

theorem badMass_zero_iff_causal {T : Tree} (Γ : Coupling T) :
    Γ.badMass = 0 ↔ Γ.causal := by
  constructor
  · intro hz α hα
    by_contra hbad
    exact hα (mass_eq_zero_of_bad hz hbad)
  · exact badMass_eq_zero_of_causal

/-- Every attained minimizer at a coefficient STRICTLY above G* is causal. -/
theorem minimizer_above_gap_is_causal {T : Tree} (Γ : Coupling T) {κ : ℝ}
    (hκ : gapSup < κ) (hmin : penalised κ Γ = penaltyMin κ T) :
    Γ.causal := by
  apply (badMass_zero_iff_causal Γ).mp
  apply le_antisymm _ (badMass_nonneg Γ)
  have h := near_minimizer_badMass_le Γ hκ (ε := 0) (by simpa [hmin])
  simpa using h

/-- At κ > G*, minimizers are exactly causal entropy minimizers. -/
theorem minimizer_above_gap_iff {T : Tree} (Γ : Coupling T) {κ : ℝ}
    (hκ : gapSup < κ) :
    penalised κ Γ = penaltyMin κ T ↔
      Γ.causal ∧ Γ.entropy = causalMin T := by
  constructor
  · intro hmin
    have hc := minimizer_above_gap_is_causal Γ hκ hmin
    refine ⟨hc, ?_⟩
    have hz := badMass_eq_zero_of_causal hc
    simpa [penalised, hz, penaltyMin_eq_causalMin hκ.le T] using hmin
  · rintro ⟨hc, he⟩
    simp [penalised, badMass_eq_zero_of_causal hc, he,
      penaltyMin_eq_causalMin hκ.le T]

/-- Any inconsistent coupling is strictly improvable by a causal coupling. -/
theorem incompatible_strictly_improvable {T : Tree} (Γ : Coupling T) {κ : ℝ}
    (hκ : gapSup < κ) (hbad : ¬ Γ.causal) :
    ∃ Δ : Coupling T, Δ.causal ∧ penalised κ Δ < penalised κ Γ := by
  have hz : Γ.badMass ≠ 0 := fun h => hbad ((badMass_zero_iff_causal Γ).mp h)
  have hp : 0 < Γ.badMass := lt_of_le_of_ne (badMass_nonneg Γ) (Ne.symm hz)
  have hm := strict_penalty_margin Γ κ
  have hpos := mul_pos (sub_pos.mpr hκ) hp
  have hroom : 0 < penalised κ Γ - causalMin T := lt_of_lt_of_le hpos hm
  obtain ⟨Δ, hΔ, hent⟩ := exists_causal_entropy_lt (T := T) hroom
  refine ⟨Δ, (badMass_zero_iff_causal Δ).mp hΔ, ?_⟩
  simp only [penalised, hΔ, mul_zero, add_zero] at hent ⊢
  linarith

/-- Equivalent formulation using the defining comparison with all competitors. -/
theorem global_minimizer_above_gap_is_causal {T : Tree} (Γ : Coupling T) {κ : ℝ}
    (hκ : gapSup < κ)
    (hmin : ∀ Δ : Coupling T, penalised κ Γ ≤ penalised κ Δ) : Γ.causal := by
  by_contra hbad
  obtain ⟨Δ, _, hlt⟩ := incompatible_strictly_improvable Γ hκ hbad
  exact (not_lt_of_ge (hmin Δ)) hlt

#print axioms strict_penalty_margin
#print axioms near_minimizer_badMass_le
#print axioms minimizer_above_gap_is_causal
#print axioms minimizer_above_gap_iff
#print axioms incompatible_strictly_improvable
#print axioms global_minimizer_above_gap_is_causal
end CausalSpectrum

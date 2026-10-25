/-
Preservation of event probabilities under an exact deterministic decoding,
and unreachability inside one invariant set.

Proved here, with no `sorry`:
* if `D#μ = P`, then `μ(D⁻¹(B)) = P(B)` for every measurable `B`;
* a positive event stays positive, for every seed with that pushforward;
* two seeds with the same pushforward charge every event equally;
* if `x₀ ∈ A`, `F(A) ⊆ A` and `A ∩ B = ∅`, then `Fⁿ(x₀) ∉ B`;
* exact decoding does not imply that orbit statement, and one missed orbit
  does not set the mass of the missed event to zero.

Not proved here: human invulnerability, a theorem about people, or the claim
that either statement yields the other.
-/
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.MeasurableSpace.Instances

noncomputable section

open MeasureTheory Function Set
open scoped ENNReal

namespace EventFidelity

/-- Exact decoding preserves the prescribed probability of every measurable event.
This is the definition of the pushforward `D#μ`. -/
theorem event_preserved {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {μ : Measure S} {P : Measure Ω} {D : S → Ω}
    (hD : Measurable D) (hexact : Measure.map D μ = P)
    {B : Set Ω} (hB : MeasurableSet B) :
    μ (D ⁻¹' B) = P B := by
  rw [← hexact, Measure.map_apply hD hB]

/-- A positive prescribed event cannot be eliminated by an exact decoder.
The identity does not depend on the cardinality or the entropy of the seed. -/
theorem positive_not_eliminated {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {μ : Measure S} {P : Measure Ω} {D : S → Ω}
    (hD : Measurable D) (hexact : Measure.map D μ = P)
    {B : Set Ω} (hB : MeasurableSet B) (hpos : 0 < P B) :
    0 < μ (D ⁻¹' B) := by
  rw [event_preserved hD hexact hB]
  exact hpos

/-- Replacing the seed does not change event probabilities, once both decodings
are exact for the same law. -/
theorem seed_change_preserves {S₁ S₂ Ω : Type*}
    [MeasurableSpace S₁] [MeasurableSpace S₂] [MeasurableSpace Ω]
    {μ₁ : Measure S₁} {μ₂ : Measure S₂} {P : Measure Ω}
    {D₁ : S₁ → Ω} {D₂ : S₂ → Ω}
    (hD₁ : Measurable D₁) (hD₂ : Measurable D₂)
    (h₁ : Measure.map D₁ μ₁ = P) (h₂ : Measure.map D₂ μ₂ = P)
    {B : Set Ω} (hB : MeasurableSet B) :
    μ₁ (D₁ ⁻¹' B) = μ₂ (D₂ ⁻¹' B) := by
  rw [event_preserved hD₁ h₁ hB, event_preserved hD₂ h₂ hB]

/-- A one-point seed and a fair bit, both decoded to `true`, charge `{true}` equally. -/
theorem dirac_and_fair_agree :
    let μ₁ : Measure Unit := Measure.dirac ()
    let D₁ : Unit → Bool := fun _ => true
    let μ₂ : Measure Bool :=
      (2⁻¹ : ℝ≥0∞) • Measure.dirac false + (2⁻¹ : ℝ≥0∞) • Measure.dirac true
    let D₂ : Bool → Bool := fun _ => true
    let P : Measure Bool := Measure.dirac true
    Measure.map D₁ μ₁ = P ∧ Measure.map D₂ μ₂ = P ∧
      μ₁ (D₁ ⁻¹' {true}) = μ₂ (D₂ ⁻¹' {true}) := by
  intro μ₁ D₁ μ₂ D₂ P
  have h₁ : Measure.map D₁ μ₁ = P := by
    simp [μ₁, D₁, P]
  have huniv : μ₂ Set.univ = 1 := by
    simp only [μ₂, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _)]
    simp [ENNReal.inv_two_add_inv_two]
  have h₂ : Measure.map D₂ μ₂ = P := by
    simp only [D₂, P]
    rw [Measure.map_const, huniv, one_smul]
  have hB : MeasurableSet ({true} : Set Bool) := MeasurableSet.of_discrete
  exact ⟨h₁, h₂, seed_change_preserves measurable_const measurable_const h₁ h₂ hB⟩

/-- An invariant set that misses `B` is never entered by the orbit of `x₀`. -/
theorem unreachable_of_invariant {X : Type*} (F : X → X) {x0 : X} {A B : Set X}
    (hx : x0 ∈ A) (hinv : ∀ x, x ∈ A → F x ∈ A) (hsep : ∀ x, x ∈ A → x ∉ B) :
    ∀ n, F^[n] x0 ∉ B := by
  intro n
  refine hsep _ ?_
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [iterate_succ_apply']
    exact hinv _ ih

/-- Exact decoding of a positive event does not make that event unreachable. -/
theorem exactness_does_not_give_unreachability :
    ∃ (μ P : Measure Bool) (D F : Bool → Bool) (B : Set Bool) (x0 : Bool) (n : ℕ),
      Measurable D ∧ Measure.map D μ = P ∧ MeasurableSet B ∧
        0 < P B ∧ μ (D ⁻¹' B) = P B ∧ F^[n] x0 ∈ B := by
  refine ⟨Measure.dirac true, Measure.dirac true, id, id, {true}, true, 0,
    measurable_id, ?_, MeasurableSet.of_discrete, ?_, ?_, ?_⟩
  · simp
  · rw [Measure.dirac_apply_of_mem (by simp : true ∈ ({true} : Set Bool))]
    exact zero_lt_one
  · exact event_preserved measurable_id (by simp) MeasurableSet.of_discrete
  · simp

/-- Missing `B` along one orbit does not force the prescribed mass of `B` to vanish. -/
theorem missed_orbit_does_not_zero_mass :
    (∀ n, (id : Bool → Bool)^[n] false ∉ ({true} : Set Bool)) ∧
      0 < (Measure.dirac true : Measure Bool) {true} := by
  refine ⟨?_, ?_⟩
  · intro n
    exact unreachable_of_invariant (id : Bool → Bool)
      (by simp : false ∈ ({false} : Set Bool))
      (fun x hx => hx)
      (fun x hx hb => by
        simp only [mem_singleton_iff] at hx hb
        exact absurd (hx.symm.trans hb) Bool.false_ne_true) n
  · rw [Measure.dirac_apply_of_mem (by simp : true ∈ ({true} : Set Bool))]
    exact zero_lt_one

end EventFidelity

end

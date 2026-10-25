/-
Observable identity, exact simulation, dynamical invariance, and representation
invariance.

This module formalizes the note "Observable Identity and Exact Simulation"
(25 October 2026). It reuses the constructions already proved in
`CausalSeed.QuestionStructure` (behavioral quotient, well-defined maps,
rollout equality, hidden-extension transcripts) and in
`CausalSeed.EventFidelity` (pushforward event identity, invariant-orbit
obstruction).

Proved here, with no `sorry`:
* the response profile coincides with the behavioral relation;
* the quotient observation and transitions are well-defined;
* every adaptive policy produces the same transcripts on the quotient;
* a hidden extension produces exactly the same transcripts;
* exact decoding preserves every measurable event probability;
* an invariant region disjoint from a forbidden set is never entered;
* exact decoding does not by itself yield the invariant-region statement;
* if a property factors through the response profile, then it is constant on
  the fibers (the "only if" direction of the identifiability criterion);
* identical profiles with different property values are underdetermination.

The Gaussian fixed-point statement is recorded as a comment. The classical
differentiation-under-the-integral argument is not re-proved (Schwartz-space
Fourier analysis is not imported). The infinite-information remark is not a
finite discrete Shannon-entropy statement and is not formalized.

Not proved here: consciousness transfer, an afterlife, human invulnerability,
or the claim that any of the above statements implies any of the others.
-/

import CausalSeed.QuestionStructure
import CausalSeed.EventFidelity

namespace ObservableIdentity

open QuestionStructure EventFidelity

/-! ### Observable identity -/

/-- The complete response profile of a state under all finite action words. -/
def responseProfile {S Act Y : Type*} (o : S → Y) (F : Act → S → S) (s : S) :
    List Act → Y :=
  fun w => o (run F w s)

/-- Observable equivalence is exactly the behavioral relation. -/
theorem obsEquiv_eq_behav {S Act Y : Type*} (o : S → Y) (F : Act → S → S)
    (s s' : S) :
    responseProfile o F s = responseProfile o F s' ↔ BehavRel o F s s' := by
  constructor
  · intro h w
    exact congrFun h w
  · intro h
    funext w
    exact h w

/-- The quotient observation is well-defined. -/
theorem quotient_observation_well_defined {S Act Y : Type*} (o : S → Y)
    (F : Act → S → S) {s s' : S} (h : BehavRel o F s s') :
    o s = o s' :=
  behav_present h

/-- The quotient transition is well-defined. -/
theorem quotient_transition_well_defined {S Act Y : Type*} (o : S → Y)
    (F : Act → S → S) (a : Act) {s s' : S} (h : BehavRel o F s s') :
    BehavRel o F (F a s) (F a s') :=
  behav_succ h a

/-- Under any adaptive policy the quotient produces the same transcripts. -/
theorem quotient_preserves_transcripts {S Act Y : Type*} (o : S → Y)
    (F : Act → S → S) (π : List Y → Act) (n : ℕ) (hist : List Y) (s : S) :
    rollout (barO o F) (barF o F) π n hist (Quotient.mk _ s) =
      rollout o F π n hist s :=
  rollout_quotient o F π n hist s

/-! ### Hidden extensions -/

/-- An arbitrary hidden extension produces exactly the same transcripts. -/
theorem hidden_extension_same_transcripts {S Act Y E : Type*}
    (o : S → Y) (F : Act → S → S) (G : Act → S → E → E)
    (π : List Y → Act) (n : ℕ) (hist : List Y) (s : S) (e : E) :
    rollout (extO o) (extF F G) π n hist (s, e) =
      rollout o F π n hist s :=
  hidden_extension_transcript o F G π n hist s e

/-! ### Exact simulation preserves the specified law -/

/-- Event preservation under an exact deterministic decoder. -/
theorem event_preservation {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    {μ : Measure S} {P : Measure Ω} {D : S → Ω}
    (hD : Measurable D) (hexact : Measure.map D μ = P)
    {B : Set Ω} (hB : MeasurableSet B) :
    μ (D ⁻¹' B) = P B :=
  event_preserved hD hexact hB

/-- A positive-probability event cannot be removed while preserving the law. -/
theorem positive_event_not_eliminated {S Ω : Type*}
    [MeasurableSpace S] [MeasurableSpace Ω]
    {μ : Measure S} {P : Measure Ω} {D : S → Ω}
    (hD : Measurable D) (hexact : Measure.map D μ = P)
    {B : Set Ω} (hB : MeasurableSet B) (hpos : 0 < P B) :
    0 < μ (D ⁻¹' B) :=
  positive_not_eliminated hD hexact hB hpos

/-! ### Dynamical invariance is an additional condition -/

/-- An invariant region disjoint from a forbidden set is never entered. -/
theorem invariant_region_criterion {X : Type*} (F : X → X) {x0 : X}
    {S B : Set X} (hx : x0 ∈ S) (hinv : ∀ x, x ∈ S → F x ∈ S)
    (hsep : ∀ x, x ∈ S → x ∉ B) :
    ∀ n, F^[n] x0 ∉ B :=
  unreachable_of_invariant F hx hinv hsep

/-- Exact decoding does not by itself yield the invariant-region statement. -/
theorem exactness_does_not_imply_invariance :
    ∃ (μ P : Measure Bool) (D F : Bool → Bool) (B : Set Bool) (x0 : Bool) (n : ℕ),
      Measurable D ∧ Measure.map D μ = P ∧ MeasurableSet B ∧
        0 < P B ∧ μ (D ⁻¹' B) = P B ∧ F^[n] x0 ∈ B :=
  exactness_does_not_give_unreachability

/-! ### Representation invariance -/

/-- The Gaussian \(g(x) = e^{-\pi x^2}\).
The classical statement that it is a fixed point of the Fourier transform is
not re-proved here. -/
noncomputable def gaussian (x : ℝ) : ℝ := Real.exp (- Real.pi * x ^ 2)

/-! ### Underdetermination -/

/-- If a property factors through the response profile, then it is constant on
the fibers. (The "only if" direction of the identifiability criterion.) -/
theorem property_factors_implies_constant {S Act Y V : Type*}
    (o : S → Y) (F : Act → S → S) (P0 : S → V)
    (P̂ : (List Act → Y) → V)
    (hfact : ∀ s, P0 s = P̂ (responseProfile o F s))
    {s s' : S} (heq : responseProfile o F s = responseProfile o F s') :
    P0 s = P0 s' := by
  rw [hfact s, hfact s', heq]

/-- Identical profiles with different property values are underdetermination:
the profiles alone cannot determine the property. -/
theorem underdetermination {S Act Y V : Type*}
    (o : S → Y) (F : Act → S → S) (P0 : S → V) (s s' : S)
    (hsame : responseProfile o F s = responseProfile o F s')
    (hdiff : P0 s ≠ P0 s') :
    ¬ ∃ P̂ : (List Act → Y) → V, ∀ t, P0 t = P̂ (responseProfile o F t) := by
  rintro ⟨P̂, hfact⟩
  exact hdiff (property_factors_implies_constant o F P0 P̂ hfact hsame)

end ObservableIdentity

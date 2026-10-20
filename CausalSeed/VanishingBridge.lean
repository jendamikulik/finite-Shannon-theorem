/-
Finite bridge lemmas for the vanishing-activity research notes.

Source manuscripts (20 October 2026):
* Wholeness as Lossless Causal Compression, Sections 5-6;
* Optimal Entropy Cost of Uniform Causal Approximation, Sections 4-5.

This module is not a complete proof of either manuscript.
It establishes two independent finite interfaces:
(1) quantitative entropy bounds for the last-success statistic;
(2) a single finite coupling controls event errors uniformly over an
    arbitrary family of policies, when its mismatch event is shared.

No additional axioms or unproved propositions are introduced.
Verification command (from repository root):
  lake env lean CausalSeed/VanishingBridge.lean
-/
import CausalSeed.VanishingClose
import CausalSeed.VanishingLastEvent
import Mathlib.Tactic

noncomputable section

namespace Vanishing.LastEvent

/-- Nonnegativity of the full Bernoulli-product entropy. -/
theorem fullEntropy_nonneg (p : List ℝ) (hp : Valid p) :
    0 ≤ fullEntropy p := by
  induction p with
  | nil => simp [fullEntropy]
  | cons a ps ih =>
      have ha : 0 ≤ a ∧ a ≤ 1 := hp a (by simp)
      have ht : Valid ps := by
        intro x hx
        exact hp x (by simp [hx])
      change 0 ≤ h2 a + fullEntropy ps
      exact add_nonneg (Vanishing.h2_nonneg ha.1 ha.2) (ih ht)

/-- The information lost when keeping only the last success is nonnegative. -/
theorem hiddenEntropy_nonneg (p : List ℝ) (hp : Valid p) :
    0 ≤ hiddenEntropy p := by
  induction p with
  | nil => simp [hiddenEntropy, successCases]
  | cons a ps ih =>
      have ha : 0 ≤ a ∧ a ≤ 1 := hp a (by simp)
      have ht : Valid ps := by
        intro x hx
        exact hp x (by simp [hx])
      rw [hiddenEntropy_cons]
      exact add_nonneg
        (mul_nonneg ha.1 (fullEntropy_nonneg ps ht))
        (mul_nonneg (sub_nonneg.mpr ha.2) (ih ht))

/-- An explicit union-bound majorant for the last-success entropy deficit.
The probabilities are listed newest first, as in `lastLaw`. -/
def deficitBound : List ℝ → ℝ
  | [] => 0
  | a :: ps => a * fullEntropy ps + deficitBound ps

/-- The true loss of information is no larger than the explicit majorant.
The key is that `(1-a) * hiddenEntropy ps ≤ hiddenEntropy ps`. -/
theorem hiddenEntropy_le_deficitBound (p : List ℝ) (hp : Valid p) :
    hiddenEntropy p ≤ deficitBound p := by
  induction p with
  | nil => simp [hiddenEntropy, successCases, deficitBound]
  | cons a ps ih =>
      have ha : 0 ≤ a ∧ a ≤ 1 := hp a (by simp)
      have ht : Valid ps := by
        intro x hx
        exact hp x (by simp [hx])
      have hl := ih ht
      have hn := hiddenEntropy_nonneg ps ht
      rw [hiddenEntropy_cons]
      change a * fullEntropy ps + (1 - a) * hiddenEntropy ps ≤
        a * fullEntropy ps + deficitBound ps
      nlinarith [mul_nonneg ha.1 hn]

/-- Finite last-event entropy sandwich, an explicit consequence of the
exact `last_event_identity` already in the repository. -/
theorem last_event_entropy_bounds (p : List ℝ) (hp : Valid p) :
    fullEntropy p - deficitBound p ≤ entropy (lastLaw p) ∧
    entropy (lastLaw p) ≤ fullEntropy p := by
  have hEq := last_event_identity p hp
  have hLo := hiddenEntropy_nonneg p hp
  have hHi := hiddenEntropy_le_deficitBound p hp
  constructor <;> linarith

end Vanishing.LastEvent

namespace Vanishing.Approximation

variable {Ω α : Type*} [Fintype Ω] [DecidableEq Ω] [DecidableEq α]

/-- Probability mass of an output event in a finite weighted source. -/
def eventMass (w : Ω → ℝ) (f : Ω → α) (A : Finset α) : ℝ :=
  ∑ ω, if f ω ∈ A then w ω else 0

/-- Weight of samples on which two decoders disagree. -/
def mismatchMass (w : Ω → ℝ) (f g : Ω → α) : ℝ :=
  ∑ ω, if f ω = g ω then 0 else w ω

/-- One-sided coupling inequality for each observable event. -/
theorem eventMass_diff_le_mismatch (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (f g : Ω → α) (A : Finset α) :
    eventMass w f A - eventMass w g A ≤ mismatchMass w f g := by
  classical
  change (∑ ω, if f ω ∈ A then w ω else 0) -
      (∑ ω, if g ω ∈ A then w ω else 0) ≤
      ∑ ω, if f ω = g ω then 0 else w ω
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro ω _
  by_cases hfg : f ω = g ω
  · simp [hfg]
  · by_cases hf : f ω ∈ A <;> by_cases hg : g ω ∈ A <;>
      simp [hfg, hf, hg] <;> linarith [hw ω]

/-- Coupling inequality in the `sup_A |P(A)-Q(A)|` convention for TV. -/
theorem eventMass_abs_diff_le_mismatch (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (f g : Ω → α) (A : Finset α) :
    |eventMass w f A - eventMass w g A| ≤ mismatchMass w f g := by
  classical
  have hsym : mismatchMass w g f = mismatchMass w f g := by
    unfold mismatchMass
    apply Finset.sum_congr rfl
    intro ω _
    by_cases h : f ω = g ω
    · simp only [ite_eq_left h, ite_eq_left h.symm]
    · simp only [ite_eq_right h, ite_eq_right (Ne.symm h)]
  apply abs_le.mpr
  constructor
  · have h := eventMass_diff_le_mismatch w hw g f A
    rw [hsym] at h
    linarith
  · exact eventMass_diff_le_mismatch w hw f g A

/-- A single bad set, common to *all* policies, uniformly bounds every
observable event error, with no dependence on the number of policies.

The sampling law need not be normalized for the inequality itself.
To obtain the finite-horizon truncation estimate of the manuscript, the
remaining task is to construct this shared bad set from all late nonzero
geometric coordinates, and prove its weight is at most their tail sum.
-/
theorem uniform_policy_event_bound {PolicyIndex : Type*}
    (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (f g : PolicyIndex → Ω → α) (bad : Finset Ω)
    (hgood : ∀ π ω, ω ∉ bad → f π ω = g π ω) :
    ∀ π : PolicyIndex, ∀ A : Finset α,
      |eventMass w (f π) A - eventMass w (g π) A| ≤
        ∑ ω, if ω ∈ bad then w ω else 0 := by
  classical
  intro π A
  have hbad : mismatchMass w (f π) (g π) ≤
      ∑ ω, if ω ∈ bad then w ω else 0 := by
    unfold mismatchMass
    apply Finset.sum_le_sum
    intro ω _
    by_cases hb : ω ∈ bad
    · by_cases heq : f π ω = g π ω <;>
        simp [hb, heq, hw ω]
    · have heq := hgood π ω hb
      simp [hb, heq]
  exact (eventMass_abs_diff_le_mismatch w hw (f π) (g π) A).trans hbad

end Vanishing.Approximation

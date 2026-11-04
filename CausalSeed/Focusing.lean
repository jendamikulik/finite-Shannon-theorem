/-
Hypothetical model of quantum consciousness: focusing and realization in time.

A working hypothesis. Not a proven property of consciousness.

What is formalized, on the classical outcome side:

* a finite set of alternatives;
* a law `q` over them;
* unfocusedness `U q = H q`;
* a point mass has unfocusedness zero;
* an ideal projective measurement of an outcome with positive mass
  yields a point mass on that outcome;
* a step that strictly decreases `U` is one definition of a focusing step;
* the decrease is not automatic: the identity step does not focus;
* a record is a realization of the current law.

The quantum state, the Kraus update, and the claim that conscious
processing is this process are not formalized. They are the hypothesis.

Not proved:

* that a physical subsystem involved in conscious processing has a
  quantum state;
* that the update is a Kraus map of that state;
* that a decrease of `U` is focusing of consciousness;
* that a realization in time is the production of a conscious content;
* anything about the zeros of `ξ`.
-/
import CausalSeed.Sharing

noncomputable section

open Sharing

namespace CausalSpectrum
namespace Focusing

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Unfocusedness of an outcome law. Shannon entropy of the law. -/
def U (q : α → ℝ) : ℝ := H q

/-- Point mass on one alternative. -/
def dirac (i : α) : α → ℝ :=
  fun j => if j = i then 1 else 0

theorem dirac_nonneg (i j : α) : 0 ≤ dirac i j := by
  by_cases h : j = i
  · simp [dirac, h]
  · simp [dirac, h]

theorem dirac_total (i : α) : ∑ j, dirac i j = 1 := by
  classical
  calc
    ∑ j, dirac i j = dirac i i := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        simp [dirac, hj]
      · intro h
        exact absurd (Finset.mem_univ i) h
    _ = 1 := by simp [dirac]

/-- A realized alternative has no residual unfocusedness. -/
theorem dirac_unfocused (i : α) : U (dirac i) = 0 := by
  classical
  unfold U H pmfEntropy
  calc
    ∑ j, entTerm (dirac i j) = entTerm (dirac i i) := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        simp [dirac, hj, entTerm_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    _ = entTerm 1 := by simp [dirac]
    _ = 0 := entTerm_one

/-- Ideal projective measurement of outcome `i`, when that outcome has
positive mass. The posterior is the point mass on `i`. -/
def project (q : α → ℝ) (i : α) (_hpos : 0 < q i) : α → ℝ :=
  dirac i

theorem project_is_dirac (q : α → ℝ) (i : α) (hpos : 0 < q i) :
    project q i hpos = dirac i :=
  rfl

theorem project_unfocused (q : α → ℝ) (i : α) (hpos : 0 < q i) :
    U (project q i hpos) = 0 := by
  rw [project_is_dirac, dirac_unfocused]

/-- A step is focusing when unfocusedness strictly falls.
The fall is part of the definition, not a theorem about every step. -/
def isFocusing (q q' : α → ℝ) : Prop :=
  U q' < U q

/-- The identity step does not focus. -/
theorem identity_not_focusing (q : α → ℝ) : ¬ isFocusing q q := by
  intro h
  exact lt_irrefl (U q) h

/-- A record is an alternative drawn from the current law.
The probability of the record is the mass of that alternative. -/
structure Record (q : α → ℝ) where
  value : α
  prob : ℝ
  law : prob = q value

/-- Realization does not by itself decrease unfocusedness.
The posterior does, when the measurement is projective. -/
theorem realization_is_not_the_posterior
    (q : α → ℝ) (r : Record q) (hpos : 0 < q r.value) :
    U (project q r.value hpos) = 0 :=
  project_unfocused q r.value hpos

/-- Two levels. The law before the record, and the point mass after
an ideal projective measurement of that record. -/
theorem two_levels
    (q : α → ℝ) (i : α) (hpos : 0 < q i) :
    (∃ r : Record q, r.value = i) ∧ U (project q i hpos) = 0 := by
  refine ⟨?_, project_unfocused q i hpos⟩
  exact ⟨{ value := i, prob := q i, law := rfl }, rfl⟩

/-- The hypothesis. A sequence of laws, a record at each step, and a
next law. That conscious processing is this sequence is not a theorem. -/
structure Hypothesis (α : Type) [Fintype α] [DecidableEq α] where
  law : ℕ → α → ℝ
  record : (t : ℕ) → Record (law t)
  nextLaw : (t : ℕ) → α → ℝ
  feedback : ∀ t, nextLaw t = law (t + 1)

/-- A focusing step inside a hypothesis is a step whose unfocusedness falls.
Existence of such a step is not proved. -/
def Hypothesis.focusesAt (h : Hypothesis α) (t : ℕ) : Prop :=
  isFocusing (h.law t) (h.law (t + 1))

end Focusing
end CausalSpectrum

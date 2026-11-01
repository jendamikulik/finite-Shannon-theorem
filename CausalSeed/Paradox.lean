/-
Equality `0 = 1` without logical explosion.

Three separated models, from the note of 1 November 2026.

* In `ZMod 1` one has `(0 : ZMod 1) = 1`. In any unital semiring,
  literal `0 = 1` collapses every element to `0`. In `ℕ`, `0 ≠ 1`,
  and the two classical statements cannot hold together.
* Dunn–Belnap four-valued evidence records positive and negative
  support independently. `{P, ¬P}` does not entail an independent `Q`.
  The value `eq01` is an atomic evidence atom, not Lean's identity
  and not equality of natural numbers.
* A constant realization identifies images and does not identify
  states. For a uniform state, `H(X) = 1`, `H(W X) = 0`, and
  `H(X | W X) = 1`. The original state is not a function of the image.

Not proved:

* a nonclassical calculus of identity and causality;
* that a human will, or consciousness, is any of these models;
* anything about the zeros of `ξ`.
-/
import CausalSeed.ValueGap
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Set.Basic

noncomputable section

open Sharing

namespace CausalSpectrum
namespace Paradox

/-! ### Literal equality in the one-element ring -/

/-- In a unital semiring, `0 = 1` forces every element to `0`. -/
theorem literal_collapse {A : Type*} [Semiring A] (h : (0 : A) = 1) (a : A) : a = 0 := by
  calc
    a = a * 1 := (mul_one a).symm
    _ = a * 0 := by rw [← h]
    _ = 0 := mul_zero a

theorem zmod_one_zero_eq_one : (0 : ZMod 1) = 1 :=
  Subsingleton.elim _ _

theorem zmod_one_collapses (a : ZMod 1) : a = 0 :=
  literal_collapse zmod_one_zero_eq_one a

theorem nat_zero_ne_one : (0 : ℕ) ≠ 1 := by
  decide

/-- The two classical statements about the same type are a contradiction. -/
theorem not_both_classically : ¬ ((0 : ℕ) = 1 ∧ (0 : ℕ) ≠ 1) :=
  fun h => h.2 h.1

/-! ### Four-valued evidence (FDE) -/

/-- Positive and negative support, recorded independently. -/
structure Evidence where
  pos : Bool
  neg : Bool

def negate (p : Evidence) : Evidence :=
  ⟨p.neg, p.pos⟩

def conj (p q : Evidence) : Evidence :=
  ⟨p.pos && q.pos, p.neg || q.neg⟩

def disj (p q : Evidence) : Evidence :=
  ⟨p.pos || q.pos, p.neg && q.neg⟩

/-- Designated: the positive bit is on. `Des = {(1,0), (1,1)}`. -/
def holds (p : Evidence) : Prop :=
  p.pos = true

theorem holds_iff (p : Evidence) :
    holds p ↔ p = ⟨true, false⟩ ∨ p = ⟨true, true⟩ := by
  rcases p with ⟨b, c⟩
  cases b <;> cases c <;> simp [holds]

/-- The atomic reading of "zero equals one". Not `Eq` on `ℕ`. -/
def eq01 : Evidence :=
  ⟨true, true⟩

/-- An independent atom with no support either way. -/
def arbitrary : Evidence :=
  ⟨false, false⟩

theorem both_supported : holds eq01 ∧ holds (negate eq01) :=
  ⟨rfl, rfl⟩

theorem not_everything_follows : ¬ holds arbitrary := by
  intro h
  cases h

inductive Atom
  | P
  | Q

inductive Formula
  | atom : Atom → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula

def eval (v : Atom → Evidence) : Formula → Evidence
  | .atom a => v a
  | .neg φ => negate (eval v φ)
  | .conj φ ψ => conj (eval v φ) (eval v ψ)
  | .disj φ ψ => disj (eval v φ) (eval v ψ)

/-- `Γ ⊨_FDE φ`: every valuation that designates all of `Γ` designates `φ`. -/
def Entails (Γ : Set Formula) (φ : Formula) : Prop :=
  ∀ v, (∀ ψ ∈ Γ, holds (eval v ψ)) → holds (eval v φ)

/-- The counterexample of the note: `P` is glutty, `Q` has no support. -/
def counter : Atom → Evidence
  | .P => eq01
  | .Q => arbitrary

theorem counter_designates_the_contradiction :
    holds (eval counter (Formula.atom Atom.P)) ∧
      holds (eval counter (Formula.neg (Formula.atom Atom.P))) ∧
      ¬ holds (eval counter (Formula.atom Atom.Q)) := by
  refine ⟨rfl, rfl, ?_⟩
  intro h
  cases h

/-- `{P, ¬P}` does not force an independent atom. -/
theorem nonexplosion :
    ¬ Entails {Formula.atom Atom.P, Formula.neg (Formula.atom Atom.P)}
        (Formula.atom Atom.Q) := by
  intro h
  have hQ :=
    h counter fun ψ hψ => by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hψ
      rcases hψ with rfl | rfl
      · exact rfl
      · exact rfl
  exact counter_designates_the_contradiction.2.2 hQ

/-- Conflicting evidence about the atom does not rewrite `ℕ`. -/
theorem evidence_does_not_rewrite_nat :
    holds eq01 ∧ holds (negate eq01) ∧ (0 : ℕ) ≠ 1 :=
  ⟨both_supported.1, both_supported.2, nat_zero_ne_one⟩

/-- The semantics is not empty: a conjunction still yields its conjunct. -/
theorem conj_entails_left (φ ψ : Formula) :
    Entails {Formula.conj φ ψ} φ := by
  intro v hv
  have h := hv (Formula.conj φ ψ) rfl
  simp only [eval, conj, holds, Bool.and_eq_true] at h
  simpa [holds] using h.1

/-! ### Two levels: states and the realized image -/

/-- Uniform state on `{false, true}`. -/
def state : Bool → ℝ :=
  bernoulli (1 / 2)

/-- Constant realization. One image, two states. -/
def realize : Bool → Unit :=
  fun _ => ()

theorem states_distinct : (false : Bool) ≠ true :=
  Bool.false_ne_true

theorem images_equal : realize false = realize true :=
  rfl

theorem two_levels : (false : Bool) ≠ true ∧ realize false = realize true :=
  ⟨states_distinct, images_equal⟩

/-- Law of `(realize X, X)`. The first coordinate is the image. -/
def joint : Unit × Bool → ℝ
  | (_, b) => state b

theorem marginal_joint : marginal joint = fun _ => 1 := by
  funext u
  cases u
  simp only [marginal, joint]
  simpa [state] using bernoulli_total (1 / 2)

theorem state_entropy : H state = 1 := by
  rw [state, bernoulli_entropy (by norm_num) (by norm_num), ValueGap.binEntropy_half]

theorem image_entropy : H (marginal joint) = 0 := by
  rw [marginal_joint]
  unfold H pmfEntropy
  simp [Finset.univ_unique, entTerm_one]

theorem joint_nonneg (p : Unit × Bool) : 0 ≤ joint p := by
  cases p with
  | mk u b =>
    cases u
    simpa [joint, state] using bernoulli_nonneg (by norm_num) (by norm_num) b

theorem joint_total : ∑ p : Unit × Bool, joint p = 1 := by
  have hpair : (Finset.univ : Finset (Unit × Bool)) = {((), false), ((), true)} := by
    ext ⟨u, b⟩
    cases u
    cases b <;> simp
  rw [hpair, Finset.sum_pair (by decide : (((), false) : Unit × Bool) ≠ ((), true))]
  simp [joint, state, bernoulli]

theorem joint_entropy : H joint = 1 := by
  unfold H pmfEntropy
  have hpair : (Finset.univ : Finset (Unit × Bool)) = {((), false), ((), true)} := by
    ext ⟨u, b⟩
    cases u
    cases b <;> simp
  rw [hpair, Finset.sum_pair (by decide : (((), false) : Unit × Bool) ≠ ((), true))]
  have hbin : entTerm (joint ((), false)) + entTerm (joint ((), true)) = binEntropy (1 / 2) := by
    simp [joint, state, bernoulli, binEntropy, add_comm]
  rw [hbin, ValueGap.binEntropy_half]

/-- One bit remains after seeing the image: `H(X | W X) = 1`. -/
theorem hidden_given_image : condEntropy joint = 1 := by
  have hchain := chain_rule joint_nonneg joint_total
  linarith [joint_entropy, image_entropy]

theorem constant_map_hides_the_bit :
    H state = 1 ∧ H (marginal joint) = 0 ∧ condEntropy joint = 1 :=
  ⟨state_entropy, image_entropy, hidden_given_image⟩

/-- The image does not determine the state. Not a lossless compression. -/
theorem not_lossless : ¬ FunctionallyDependent joint := by
  intro ⟨g, hg⟩
  have hpos : ∀ b : Bool, joint ((), b) = 1 / 2 := by
    intro b
    cases b
    · simp [joint, state, bernoulli]
      norm_num
    · simp [joint, state, bernoulli]
  cases hb : g () with
  | false =>
      have := hg () true (by simp [hb])
      rw [hpos] at this
      norm_num at this
  | true =>
      have := hg () false (by simp [hb])
      rw [hpos] at this
      norm_num at this

end Paradox
end CausalSpectrum

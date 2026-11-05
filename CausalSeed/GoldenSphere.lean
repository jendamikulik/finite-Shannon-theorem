/-
The golden sphere: a definition of admissible next states.

A wish opens a set of actions. An action changes the state. Each agent
affected by the change has a consent boundary. A set of states satisfies
the chosen conditions of care.

The sphere offers a next state only when three things hold together:
the action is opened by the wish, the action lies in every consent
boundary, and the resulting state lies in the care set.

If the offered set is nonempty, a choice from it keeps the trajectory
inside the care set. If it is empty, the sphere is silent. The definition
contains no clause that replaces a missing consent by another agent's
sacrifice.

Not proved:

* that a wish exists;
* that the consent boundaries are the right ones;
* that the care set is nonempty;
* that the sphere speaks.
-/

import Mathlib.Data.Set.Basic

namespace CausalSpectrum
namespace GoldenSphere

/-- A sphere. The data are a wish-opening, a transition, consent
boundaries, and a care set. -/
structure Sphere (X : Type*) (Ω : Type*) (W : Type*) (N : Type*) where
  I : W → X → Set Ω
  F : X → Ω → X
  C : N → X → Set Ω
  K : Set X

variable {X Ω W N : Type*}

/-- Actions opened by the wish and accepted by every consent boundary. -/
def admissible (S : Sphere X Ω W N) (w : W) (x : X) : Set Ω :=
  { a | a ∈ S.I w x ∧ ∀ i, a ∈ S.C i x }

/-- Next states offered by the sphere: images of admissible actions that
land in the care set. -/
def G (S : Sphere X Ω W N) (w : W) (x : X) : Set X :=
  { y | ∃ a, a ∈ admissible S w x ∧ y = S.F x a ∧ y ∈ S.K }

/-- An offered next state lies in the care set. -/
theorem G_subset_K (S : Sphere X Ω W N) (w : W) (x : X) :
    G S w x ⊆ S.K :=
  fun _ ⟨_, _, hy, hk⟩ => hy ▸ hk

/-- A trajectory that always chooses from the offered set, starting in
the care set, remains in the care set. -/
theorem stays_in_K (S : Sphere X Ω W N) (w : ℕ → W) (x : ℕ → X)
    (h0 : x 0 ∈ S.K)
    (hstep : ∀ t, x (t + 1) ∈ G S (w t) (x t)) :
    ∀ t, x t ∈ S.K := by
  intro t
  induction t with
  | zero => exact h0
  | succ t ih =>
    exact G_subset_K S (w t) (x t) (hstep t)

/-- If the offered set is empty, no next state is available. -/
theorem silent (S : Sphere X Ω W N) (w : W) (x : X) (h : G S w x = ∅) :
    ∀ y, y ∉ G S w x := by
  intro y hy
  rw [h] at hy
  exact hy

/-- An action outside some consent boundary is not admissible. -/
theorem outside_consent_not_admissible (S : Sphere X Ω W N) (w : W) (x : X)
    (i : N) (a : Ω) (ha : a ∉ S.C i x) :
    a ∉ admissible S w x := by
  intro h
  exact ha (h.2 i)

/-- The definition of `G` requires every consent boundary. There is no
alternative clause that drops one. -/
theorem G_requires_all_consent (S : Sphere X Ω W N) (w : W) (x : X)
    (a : Ω) (i : N) (ha : a ∉ S.C i x) :
    a ∉ admissible S w x :=
  outside_consent_not_admissible S w x i a ha

end GoldenSphere
end CausalSpectrum

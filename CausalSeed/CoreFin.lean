/-
The core, as a computation on finite sets.

`Core` proves that the predecessor iteration stabilizes. The sets there
are arbitrary, so the proof is not a program. Here the state, action,
and circumstance spaces are finite, protection is a `Bool`, and the
available actions are a `Finset`. The predecessor is then a filter, and
the same card argument shows that the iterates stabilize.

What is proved:

* the filter agrees with `Core.pred` on the corresponding model;
* the iterates decrease and, on a finite state space, stabilize;
* the stable set is a fixed point and contains every self-safe set.

Not proved:

* that the stable set is nonempty;
* that a participant will choose an action from it.
-/
import CausalSeed.Core
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic

namespace CausalSpectrum
namespace CoreFin

open Classical

variable {X A W : Type*} [Fintype X] [DecidableEq X]
    [Fintype A] [DecidableEq A] [Fintype W]

/-- Decidable data for one step. -/
structure Data (X A W : Type*) [Fintype X] [Fintype A] [Fintype W] where
  protected_ : X → Bool
  act : X → Finset A
  step : X → A → W → X

variable (D : Data X A W)

/-- The set-theoretic model with one participant. Protected means floor `0`. -/
def toModel : NobodyLeft.Model Unit X A W where
  participants := ⟨()⟩
  act := fun x => ↑(D.act x)
  step := D.step
  floor := fun _ x => if D.protected_ x then 0 else -1

/-- The predecessor, as a filter. -/
def pred (S : Finset X) : Finset X :=
  Finset.univ.filter fun x =>
    D.protected_ x = true ∧ ∃ a ∈ D.act x, ∀ w, D.step x a w ∈ S

theorem mem_pred {S : Finset X} {x : X} :
    x ∈ pred D S ↔
      D.protected_ x = true ∧ ∃ a ∈ D.act x, ∀ w, D.step x a w ∈ S := by
  classical
  simp [pred]

theorem pred_agrees (S : Finset X) :
    (pred D S : Set X) = Core.pred (toModel D) (S : Set X) := by
  ext x
  constructor
  · intro hx
    rcases (mem_pred (D := D) (S := S) (x := x)).1 hx with ⟨hp, hex⟩
    rcases hex with ⟨a, ha, hw⟩
    refine ⟨?_, ⟨a, ?_, hw⟩⟩
    · intro i
      cases i
      simp [toModel, hp]
    · simpa [toModel] using ha
  · intro hx
    rcases hx with ⟨hprot, hex⟩
    rcases hex with ⟨a, ha, hw⟩
    have hp : D.protected_ x = true := by
      have h0 : 0 ≤ (if D.protected_ x then (0 : ℝ) else -1) := by
        simpa [Core.pred, NobodyLeft.protectedSet, toModel] using hprot
      by_contra h
      simp [h] at h0
      exact absurd h0 (by norm_num)
    apply (mem_pred (D := D) (S := S) (x := x)).2
    exact ⟨hp, ⟨a, by simpa [toModel] using ha, hw⟩⟩

/-- Iteration from the protected states. -/
def V : ℕ → Finset X
  | 0 => Finset.univ.filter fun x => D.protected_ x = true
  | n + 1 => pred D (V n)

theorem V_zero : V D 0 = Finset.univ.filter fun x => D.protected_ x = true := rfl

theorem V_succ (n : ℕ) : V D (n + 1) = pred D (V D n) := rfl

theorem pred_subset_protected (S : Finset X) :
    pred D S ⊆ Finset.univ.filter fun x => D.protected_ x = true := by
  intro x hx
  rcases (mem_pred (D := D) (S := S) (x := x)).1 hx with ⟨hp, -⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩

theorem pred_mono {S T : Finset X} (h : S ⊆ T) : pred D S ⊆ pred D T := by
  intro x hx
  rcases (mem_pred (D := D) (S := S) (x := x)).1 hx with ⟨hp, hex⟩
  rcases hex with ⟨a, ha, hw⟩
  exact (mem_pred (D := D) (S := T) (x := x)).2 ⟨hp, ⟨a, ha, fun w => h (hw w)⟩⟩

theorem V_anti (n : ℕ) : V D (n + 1) ⊆ V D n := by
  induction n with
  | zero =>
      intro x hx
      have hx' : x ∈ pred D (V D 0) := by simpa [V_succ] using hx
      rcases (mem_pred (D := D)).1 hx' with ⟨hp, -⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
  | succ n ih =>
      rw [V_succ, V_succ]
      exact pred_mono D ih

theorem V_le {m n : ℕ} (h : m ≤ n) : V D n ⊆ V D m := by
  induction n, h using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n _ ih => exact (V_anti D n).trans ih

/-- A nonincreasing sequence of naturals has two consecutive equals. -/
theorem exists_card_fix {c : ℕ → ℕ} (mono : ∀ n, c (n + 1) ≤ c n) :
    ∃ N, c (N + 1) = c N := by
  classical
  by_contra h
  push_neg at h
  have strict : ∀ n, c (n + 1) < c n := fun n => lt_of_le_of_ne (mono n) (h n)
  have bound : ∀ k, c k ≤ c 0 - k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have ih' : c k ≤ c 0 - k := ih
        have hlt : c (k + 1) < c k := strict k
        omega
  have h0 : c (c 0) ≤ 0 := by simpa using bound (c 0)
  have h1 : c (c 0 + 1) < c (c 0) := strict (c 0)
  omega

theorem V_stabilizes : ∃ N, ∀ n ≥ N, V D n = V D N := by
  classical
  let c : ℕ → ℕ := fun n => (V D n).card
  have mono : ∀ n, c (n + 1) ≤ c n := fun n => Finset.card_le_card (V_anti D n)
  obtain ⟨N, hcard⟩ := exists_card_fix mono
  have hsub : V D (N + 1) ⊆ V D N := V_anti D N
  have heq : V D (N + 1) = V D N :=
    Finset.eq_of_subset_of_card_le hsub (by simpa [c] using hcard.ge)
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk : N + k ≥ N := Nat.le_add_right _ _
      rw [← Nat.add_assoc, V_succ, ih hk, ← V_succ, heq]

/-- A set that the filter can hold. -/
def SelfSafe (S : Finset X) : Prop :=
  (S ⊆ Finset.univ.filter fun x => D.protected_ x = true) ∧ S ⊆ pred D S

theorem stable_fixed (N : ℕ) (hN : ∀ n ≥ N, V D n = V D N) :
    pred D (V D N) = V D N := by
  have := hN (N + 1) (Nat.le_succ N)
  simpa [V_succ] using this

theorem stable_selfSafe (N : ℕ) (hN : ∀ n ≥ N, V D n = V D N) :
    SelfSafe D (V D N) := by
  unfold SelfSafe
  refine And.intro ?_ ?_
  · intro x hx
    have hx0 : x ∈ V D 0 := V_le D (Nat.zero_le N) hx
    simpa [V_zero] using hx0
  · intro x hx
    rw [stable_fixed D N hN]
    exact hx

/-- The computed stable set contains every self-safe set. -/
theorem stable_greatest (N : ℕ) (hN : ∀ n ≥ N, V D n = V D N)
    {S : Finset X} (hS : SelfSafe D S) : S ⊆ V D N := by
  unfold SelfSafe at hS
  have hold : ∀ n, S ⊆ V D n := by
    intro n
    induction n with
    | zero =>
        intro x hx
        simpa [V_zero] using hS.1 hx
    | succ n ih =>
        intro x hx
        rcases (mem_pred (D := D)).1 (hS.2 hx) with ⟨hp, hex⟩
        rcases hex with ⟨a, ha, hw⟩
        exact (mem_pred (D := D)).2 ⟨hp, ⟨a, ha, fun w => ih (hw w)⟩⟩
  exact hold N

end CoreFin
end CausalSpectrum

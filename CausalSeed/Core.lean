/-
The greatest safe core, by iteration.

Formalization of the operator and fixed point from
"Společná pravidla a bezpečná volba".

Proved, with no sorry:

* the predecessor `P` is monotone and lands in the protected set;
* a set contained in its own predecessor can be held by an action
  chosen before the circumstance;
* starting from the protected set, the iterates decrease;
* on a finite state space the sequence stabilizes;
* the stable set is a fixed point of `P` and the greatest self-safe set.

Not proved:

* that the core is nonempty for an arbitrary system;
* that a participant will choose an action from it;
* that the core prices help or constructs a seed.

The core is what the definition keeps. It is not a vote.
-/
import CausalSeed.NobodyLeft
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Basic

noncomputable section

open Classical

namespace CausalSpectrum
namespace Core

variable {I X A W : Type*}

open NobodyLeft

/-- Predecessor. A state is kept only if it is already protected and some
action, chosen before `w`, lands back in `D` for every circumstance. -/
def pred (M : NobodyLeft.Model I X A W) (D : Set X) : Set X :=
  {x | x ∈ protectedSet M ∧ ∃ a ∈ M.act x, ∀ w, M.step x a w ∈ D}

theorem pred_subset_protected (M : NobodyLeft.Model I X A W) (D : Set X) :
    pred M D ⊆ protectedSet M :=
  fun _ hx => hx.1

theorem pred_mono {M : NobodyLeft.Model I X A W} {D E : Set X} (h : D ⊆ E) :
    pred M D ⊆ pred M E := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  obtain ⟨a, ha, hw⟩ := hx.2
  exact ⟨a, ha, fun w => h (hw w)⟩

/-- A set that can be held. Every state in it has an action, fixed before
the circumstance, whose every successor stays in it. -/
def SelfSafe (M : NobodyLeft.Model I X A W) (D : Set X) : Prop :=
  D ⊆ protectedSet M ∧ D ⊆ pred M D

theorem selfSafe_iff {M : NobodyLeft.Model I X A W} {D : Set X} :
    SelfSafe M D ↔
      D ⊆ protectedSet M ∧
        ∀ x ∈ D, ∃ a ∈ M.act x, ∀ w, M.step x a w ∈ D := by
  constructor
  · rintro ⟨hsub, hpred⟩
    refine ⟨hsub, ?_⟩
    intro x hx
    obtain ⟨_, a, ha, hw⟩ := hpred hx
    exact ⟨a, ha, hw⟩
  · rintro ⟨hsub, hact⟩
    refine ⟨hsub, ?_⟩
    intro x hx
    exact ⟨hsub hx, hact x hx⟩

/-- Iteration from the protected set. `V 0` is the protected set. -/
def V (M : NobodyLeft.Model I X A W) : ℕ → Set X
  | 0 => protectedSet M
  | n + 1 => pred M (V M n)

theorem V_zero (M : NobodyLeft.Model I X A W) : V M 0 = protectedSet M := rfl

theorem V_succ (M : NobodyLeft.Model I X A W) (n : ℕ) :
    V M (n + 1) = pred M (V M n) := rfl

theorem V_anti (M : NobodyLeft.Model I X A W) (n : ℕ) : V M (n + 1) ⊆ V M n := by
  induction n with
  | zero =>
      intro x hx
      exact hx.1
  | succ n ih =>
      exact pred_mono ih

theorem V_le (M : NobodyLeft.Model I X A W) {m n : ℕ} (h : m ≤ n) :
    V M n ⊆ V M m := by
  induction n, h using Nat.le_induction with
  | base => exact Set.Subset.refl _
  | succ n _ ih => exact (V_anti M n).trans ih

/-- The stable core: states that survive every iterate. -/
def core (M : NobodyLeft.Model I X A W) : Set X :=
  Set.iInter (V M)

theorem core_subset_V (M : NobodyLeft.Model I X A W) (n : ℕ) :
    core M ⊆ V M n :=
  Set.iInter_subset _ n

theorem core_subset_protected (M : NobodyLeft.Model I X A W) :
    core M ⊆ protectedSet M := by
  simpa [V_zero] using core_subset_V M 0

/-- A self-safe set sits inside every iterate, hence inside the core. -/
theorem selfSafe_subset_V {M : NobodyLeft.Model I X A W} {D : Set X}
    (hD : SelfSafe M D) (n : ℕ) : D ⊆ V M n := by
  induction n with
  | zero =>
      simpa [V_zero] using hD.1
  | succ n ih =>
      intro x hx
      exact pred_mono ih (hD.2 hx)

theorem selfSafe_subset_core {M : NobodyLeft.Model I X A W} {D : Set X}
    (hD : SelfSafe M D) : D ⊆ core M :=
  Set.subset_iInter (selfSafe_subset_V hD)

/-- Once two consecutive iterates agree, all later ones agree. -/
theorem V_stable_of_eq {M : NobodyLeft.Model I X A W} {n : ℕ}
    (h : V M (n + 1) = V M n) (k : ℕ) : V M (n + k) = V M n := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [← Nat.add_assoc, V_succ, ih, ← V_succ, h]

theorem V_eq_of_ge {M : NobodyLeft.Model I X A W} {N n : ℕ}
    (h : V M (N + 1) = V M N) (hn : N ≤ n) : V M n = V M N := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact V_stable_of_eq h k

/-- A nonincreasing sequence of naturals has two consecutive equals within its start value. -/
theorem exists_card_fix {c : ℕ → ℕ} (mono : ∀ n, c (n + 1) ≤ c n) :
    ∃ N, N ≤ c 0 ∧ c (N + 1) = c N := by
  classical
  by_contra h
  push_neg at h
  have strict : ∀ N, N ≤ c 0 → c (N + 1) < c N := by
    intro N hN
    exact lt_of_le_of_ne (mono N) (h N hN)
  have bound : ∀ k, k ≤ c 0 → c k ≤ c 0 - k := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
        have hk' : k ≤ c 0 := Nat.le_of_succ_le hk
        have ih' : c k ≤ c 0 - k := ih hk'
        have hlt : c (k + 1) < c k := strict k hk'
        omega
  have h0 : c (c 0) ≤ 0 := by simpa using bound (c 0) le_rfl
  have h1 : c (c 0 + 1) < c (c 0) := strict (c 0) le_rfl
  omega

/-- On a finite state space the decreasing sequence stabilizes. -/
theorem V_stabilizes [Fintype X] (M : NobodyLeft.Model I X A W) :
    ∃ N, ∀ n ≥ N, V M n = V M N := by
  classical
  let c : ℕ → ℕ := fun n => (V M n).toFinset.card
  have mono : ∀ n, c (n + 1) ≤ c n := by
    intro n
    exact Finset.card_le_card (Set.toFinset_mono (V_anti M n))
  obtain ⟨N, _, hcard⟩ := exists_card_fix mono
  have hsub : V M (N + 1) ⊆ V M N := V_anti M N
  have heqFin : (V M (N + 1)).toFinset = (V M N).toFinset := by
    apply Finset.eq_of_subset_of_card_le
    · exact Set.toFinset_mono hsub
    · simpa [c] using hcard.ge
  have hset : V M (N + 1) = V M N := Set.toFinset_inj.mp heqFin
  exact ⟨N, fun n hn => V_eq_of_ge hset hn⟩

/-- After stabilization the core equals the stable iterate, and is a fixed point. -/
theorem core_eq_stable [Fintype X] (M : NobodyLeft.Model I X A W) :
    ∃ N, core M = V M N ∧ V M (N + 1) = V M N := by
  obtain ⟨N, hN⟩ := V_stabilizes M
  refine ⟨N, ?_, ?_⟩
  · ext x
    constructor
    · exact fun hx => core_subset_V M N hx
    · intro hx
      rw [core, Set.mem_iInter]
      intro i
      rcases le_total N i with hle | hle
      · simpa [hN i hle] using hx
      · exact V_le M hle hx
  · simpa [V_succ] using hN (N + 1) (Nat.le_succ N)

theorem core_fixed [Fintype X] (M : NobodyLeft.Model I X A W) :
    pred M (core M) = core M := by
  obtain ⟨N, hcore, hfix⟩ := core_eq_stable M
  rw [hcore]
  simpa [V_succ] using hfix

theorem core_selfSafe [Fintype X] (M : NobodyLeft.Model I X A W) :
    SelfSafe M (core M) :=
  ⟨core_subset_protected M, by
    intro x hx
    simpa [core_fixed M] using hx⟩

/-- Maximality: the core contains every self-safe set. -/
theorem core_greatest [Fintype X] (M : NobodyLeft.Model I X A W) {D : Set X}
    (hD : SelfSafe M D) : D ⊆ core M :=
  selfSafe_subset_core hD

end Core
end CausalSpectrum

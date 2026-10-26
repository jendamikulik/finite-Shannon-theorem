/-
Safety on a finite controlled tree, separated from simulation cost.

Formalization of the safety recursion discussed with the causal-seed programme.

Proved here, with no `sorry`:
* the backward recursion for the least probability `V(h)` of visiting a
  forbidden set `B` before the horizon ends;
* the minimum is attained, because the action set is finite and nonempty;
* for a nonterminal history outside `B`,
  `V(h) = 0 ↔ ∃ a ∀ y, p(y | h, a) > 0 → V(hay) = 0`;
* `V = 0` if and only if some policy has hit probability zero;
* every policy has hit probability at least `V`;
* the hit probability of a fixed policy is a function of that policy and the
  kernels, so an exact simulator, which reproduces those kernels, reproduces it.

Not proved here: a change in the optimal seed cost when exactness is required
only on the safe policies. That is the research question, not a theorem.
`V(∅) = 0` decides preventability. `C(T)` decides the cost of simulating the
environment. The recursion itself is the standard dynamic-programming identity.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

noncomputable section

open Classical Finset

namespace Safety

/-- A finite controlled tree. Kernels are nonnegative and sum to one, so a
transition may be absent. `bad` means the current history is forbidden. -/
inductive Tree : Type
  | leaf (bad : Bool)
  | node
      (bad : Bool)
      (nA : ℕ)
      (hA : 0 < nA)
      (nY : Fin nA → ℕ)
      (hY : ∀ a, 0 < nY a)
      (K : (a : Fin nA) → Fin (nY a) → ℝ)
      (Knn : ∀ a y, 0 ≤ K a y)
      (Ksum : ∀ a, ∑ y, K a y = 1)
      (child : (a : Fin nA) → Fin (nY a) → Tree)

def isBad : Tree → Bool
  | .leaf b => b
  | .node b _ _ _ _ _ _ _ _ => b

def isLeaf : Tree → Bool
  | .leaf _ => true
  | .node _ _ _ _ _ _ _ _ _ => false

/-- Minimum of a nonempty finite family of reals. -/
def minAction {nA : ℕ} (hA : 0 < nA) (f : Fin nA → ℝ) : ℝ :=
  let s : Finset ℝ := (univ : Finset (Fin nA)).image f
  s.min' (Finset.Nonempty.image ⟨⟨0, hA⟩, Finset.mem_univ _⟩ f)

theorem minAction_le {nA : ℕ} (hA : 0 < nA) (f : Fin nA → ℝ) (a : Fin nA) :
    minAction hA f ≤ f a := by
  unfold minAction
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem f (Finset.mem_univ a))

theorem exists_minAction {nA : ℕ} (hA : 0 < nA) (f : Fin nA → ℝ) :
    ∃ a, minAction hA f = f a := by
  have hmem : minAction hA f ∈ (univ : Finset (Fin nA)).image f := by
    simpa [minAction] using
      Finset.min'_mem ((univ : Finset (Fin nA)).image f) _
  obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hmem
  exact ⟨a, ha.symm⟩

theorem minAction_nonneg {nA : ℕ} (hA : 0 < nA) {f : Fin nA → ℝ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ minAction hA f := by
  obtain ⟨a, ha⟩ := exists_minAction hA f
  rw [ha]
  exact hf a

theorem minAction_eq_zero_iff {nA : ℕ} (hA : 0 < nA) {f : Fin nA → ℝ}
    (hf : ∀ a, 0 ≤ f a) : minAction hA f = 0 ↔ ∃ a, f a = 0 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := exists_minAction hA f
    exact ⟨a, ha.symm.trans h⟩
  · rintro ⟨a, ha⟩
    have hle : minAction hA f ≤ 0 := by simpa [ha] using minAction_le hA f a
    exact le_antisymm hle (minAction_nonneg hA hf)

/-- Least probability of visiting `B` from this history. -/
def V : Tree → ℝ
  | .leaf bad => if bad then 1 else 0
  | .node bad nA hA nY _ K _ _ child =>
      if bad then 1 else
        minAction hA (fun a => ∑ y, K a y * V (child a y))

theorem V_leaf_bad : V (.leaf true) = 1 := by simp [V]

theorem V_leaf_safe : V (.leaf false) = 0 := by simp [V]

theorem V_nonneg : ∀ T, 0 ≤ V T := by
  intro T
  induction T with
  | leaf bad =>
      cases bad <;> simp [V]
  | node bad nA hA nY hY K Knn Ksum child ih =>
      cases bad
      · simp only [V, Bool.false_eq_true, ite_false]
        refine minAction_nonneg hA ?_
        intro a
        exact Finset.sum_nonneg fun y _ =>
          mul_nonneg (Knn a y) (ih a y)
      · simp [V]

theorem expected_nonneg {nA : ℕ} {nY : Fin nA → ℕ}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    (Knn : ∀ a y, 0 ≤ K a y)
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (a : Fin nA) (hV : ∀ a y, 0 ≤ V (child a y)) :
    0 ≤ ∑ y, K a y * V (child a y) :=
  Finset.sum_nonneg fun y _ => mul_nonneg (Knn a y) (hV a y)

theorem expected_eq_zero_iff {nA : ℕ} {nY : Fin nA → ℕ}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    (Knn : ∀ a y, 0 ≤ K a y)
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (a : Fin nA) (hV : ∀ y, 0 ≤ V (child a y)) :
    (∑ y, K a y * V (child a y)) = 0 ↔
      ∀ y, 0 < K a y → V (child a y) = 0 := by
  constructor
  · intro hsum y hy
    have hnn : ∀ y ∈ univ, 0 ≤ K a y * V (child a y) :=
      fun y _ => mul_nonneg (Knn a y) (hV y)
    have hterm : K a y * V (child a y) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum y (Finset.mem_univ y)
    rcases mul_eq_zero.mp hterm with hK | hVy
    · exact absurd hK (ne_of_gt hy)
    · exact hVy
  · intro h
    refine Finset.sum_eq_zero fun y _ => ?_
    by_cases hy : 0 < K a y
    · rw [h y hy, mul_zero]
    · have : K a y = 0 := le_antisymm (not_lt.mp hy) (Knn a y)
      rw [this, zero_mul]

/-- **Safety criterion.** Outside `B`, and away from the terminal layer,
`V` vanishes exactly when one action stays in the zero-`V` set on its
whole positive support. -/
theorem V_zero_iff
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Knn : ∀ a y, 0 ≤ K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree} :
    V (.node false nA hA nY hY K Knn Ksum child) = 0 ↔
      ∃ a, ∀ y, 0 < K a y → V (child a y) = 0 := by
  have hV : ∀ a y, 0 ≤ V (child a y) := fun a y => V_nonneg _
  simp only [V, Bool.false_eq_true, ite_false]
  rw [minAction_eq_zero_iff hA]
  · constructor
    · rintro ⟨a, ha⟩
      exact ⟨a, (expected_eq_zero_iff Knn a (fun y => hV a y)).mp ha⟩
    · rintro ⟨a, ha⟩
      exact ⟨a, (expected_eq_zero_iff Knn a (fun y => hV a y)).mpr ha⟩
  · intro a
    exact expected_nonneg Knn a hV

/-- The minimizing action is attained. -/
theorem V_attained
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Knn : ∀ a y, 0 ≤ K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree} :
    ∃ a, V (.node false nA hA nY hY K Knn Ksum child) =
      ∑ y, K a y * V (child a y) := by
  simpa [V] using exists_minAction hA (fun a => ∑ y, K a y * V (child a y))

/-! ### Policies and hit probability -/

def Policy : Tree → Type
  | .leaf _ => PUnit
  | .node _ nA _ nY _ _ _ _ child =>
      Fin nA × ((a : Fin nA) → (y : Fin (nY a)) → Policy (child a y))

def defaultPolicy : (T : Tree) → Policy T
  | .leaf _ => ()
  | .node _ nA hA nY _ _ _ _ child =>
      (⟨0, hA⟩, fun a y => defaultPolicy (child a y))

/-- Hit probability of one fixed policy. -/
def hit : {T : Tree} → Policy T → ℝ
  | .leaf bad, _ => if bad then 1 else 0
  | .node true _ _ _ _ _ _ _ _, _ => 1
  | .node false _ _ _ _ K _ _ _, ⟨a, cont⟩ =>
      ∑ y, K a y * hit (cont a y)

theorem hit_nonneg : ∀ {T} (π : Policy T), 0 ≤ hit π := by
  intro T
  induction T with
  | leaf bad =>
      intro _
      cases bad <;> simp [hit]
  | node bad nA hA nY hY K Knn Ksum child ih =>
      intro π
      cases bad
      · rcases π with ⟨a, cont⟩
        simp only [hit]
        exact Finset.sum_nonneg fun y _ => mul_nonneg (Knn a y) (ih a y (cont a y))
      · simp [hit]

theorem hit_ge_V : ∀ {T} (π : Policy T), V T ≤ hit π := by
  intro T
  induction T with
  | leaf bad =>
      intro _
      cases bad <;> simp [V, hit]
  | node bad nA hA nY hY K Knn Ksum child ih =>
      intro π
      cases bad
      · rcases π with ⟨a, cont⟩
        simp only [V, hit, Bool.false_eq_true, ite_false]
        refine le_trans (minAction_le hA _ a) ?_
        refine Finset.sum_le_sum fun y _ => ?_
        exact mul_le_mul_of_nonneg_left (ih a y (cont a y)) (Knn a y)
      · simp [V, hit]

/-- A policy that stays out of `B` whenever `V` says that is possible. -/
noncomputable def safePolicy : (T : Tree) → V T = 0 → Policy T
  | .leaf false, _ => ()
  | .leaf true, h => False.elim (by simpa [V] using h)
  | .node true _ _ _ _ _ _ _ _, h => False.elim (by simpa [V] using h)
  | .node false nA hA nY hY K Knn Ksum child, h =>
      let hex := (V_zero_iff (nA := nA) (hA := hA) (nY := nY) (hY := hY)
        (K := K) (Knn := Knn) (Ksum := Ksum) (child := child)).mp h
      let a := Classical.choose hex
      (a, fun b =>
        if hba : b = a then
          hba.symm.rec
            (motive := fun c _ => (y : Fin (nY c)) → Policy (child c y))
            (fun y => if hy : V (child a y) = 0 then safePolicy (child a y) hy
              else defaultPolicy (child a y))
        else fun y => defaultPolicy (child b y))

theorem hit_safePolicy : ∀ {T} (h : V T = 0), hit (safePolicy T h) = 0 := by
  intro T
  induction T with
  | leaf bad =>
      intro h
      cases bad
      · simp [hit]
      · simp [V] at h
  | node bad nA hA nY hY K Knn Ksum child ih =>
      intro h
      cases bad
      · have hex := (V_zero_iff (nA := nA) (hA := hA) (nY := nY) (hY := hY)
          (K := K) (Knn := Knn) (Ksum := Ksum) (child := child)).mp h
        let a := Classical.choose hex
        have ha : ∀ y, 0 < K a y → V (child a y) = 0 := Classical.choose_spec hex
        have hform : safePolicy (.node false nA hA nY hY K Knn Ksum child) h =
            (a, fun b =>
              if hba : b = a then
                hba.symm.rec
                  (motive := fun c _ => (y : Fin (nY c)) → Policy (child c y))
                  (fun y => if hy : V (child a y) = 0 then safePolicy (child a y) hy
                    else defaultPolicy (child a y))
              else fun y => defaultPolicy (child b y)) := by
          rfl
        rw [hform, hit]
        refine Finset.sum_eq_zero fun y _ => ?_
        have hcont : hit
            ((if hba : a = a then
                hba.symm.rec
                  (motive := fun c _ => (y : Fin (nY c)) → Policy (child c y))
                  (fun y => if hy : V (child a y) = 0 then safePolicy (child a y) hy
                    else defaultPolicy (child a y))
              else fun y => defaultPolicy (child a y)) y) =
            hit (if hy : V (child a y) = 0 then safePolicy (child a y) hy
              else defaultPolicy (child a y)) := by
          simp
        rw [hcont]
        by_cases hy : V (child a y) = 0
        · simp [hy, ih a y hy]
        · have hK : K a y = 0 := by
            by_contra hne
            exact hy (ha y (lt_of_le_of_ne (Knn a y) (Ne.symm hne)))
          rw [hK, zero_mul]
      · simp [V] at h

/-- Preventability is exactly the existence of a policy that never hits `B`. -/
theorem preventable_iff {T : Tree} :
    V T = 0 ↔ ∃ π : Policy T, hit π = 0 := by
  constructor
  · intro h
    exact ⟨safePolicy T h, hit_safePolicy h⟩
  · rintro ⟨π, hπ⟩
    have hle : V T ≤ hit π := hit_ge_V π
    have hnn : 0 ≤ V T := V_nonneg T
    linarith

/-- Hitting `B` is determined by the policy and the kernels. An exact simulator
reproduces those kernels along every policy, so it reproduces the hit
probability. Preventability (`V = 0`) and simulation cost are separate
questions: the first is decided here, the second is `C(T)` and is not
re-proved. Restricting exactness to the safe policies is not given a cost
identity in this module. -/
theorem hit_depends_on_kernel
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Knn : ∀ a y, 0 ≤ K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (π : Policy (.node false nA hA nY hY K Knn Ksum child)) :
    hit π = ∑ y, K π.1 y * hit (π.2 π.1 y) := by
  rcases π with ⟨a, cont⟩
  rfl

end Safety

end

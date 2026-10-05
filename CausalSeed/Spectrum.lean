/- Kernel certificate through the refined cutoff. No Shannon, Rényi, or Wasserstein claim. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Order.Bounds.Basic
import Mathlib.Tactic
noncomputable section
open Classical
namespace CausalSpectrum
/-
Finite full-history tree.
Every finite alphabet is represented by a `Fin n`; the arities `nA` and `nY a`
may vary from node to node and from action to action.  This is only a
relabeling of arbitrary finite nonempty alphabets.
Kernels are arbitrary positive real numbers, not rationals/dyadics.
-/
inductive Tree : Type
  | leaf : Tree
  | node
      (nA : ℕ)
      (hA : 0 < nA)
      (nY : Fin nA → ℕ)
      (hY : ∀ a, 0 < nY a)
      (K : (a : Fin nA) → Fin (nY a) → ℝ)
      (Kpos : ∀ a y, 0 < K a y)
      (Ksum : ∀ a, ∑ y, K a y = 1)
      (child : (a : Fin nA) → Fin (nY a) → Tree) : Tree
/-- A real field on all vertices of a full-history tree. -/
@[reducible] def Field : Tree → Type
  | .leaf => ℝ
  | .node nA _ nY _ _ _ _ child =>
      ℝ × ((a : Fin nA) → (y : Fin (nY a)) → Field (child a y))
namespace Field
/-- Value at the root of a field. -/
def root : {T : Tree} → Field T → ℝ
  | .leaf, r => r
  | .node _ _ _ _ _ _ _ _, r => r.1
@[simp] theorem root_leaf (r : Field Tree.leaf) : root r = r := rfl
/-- Flow conservation, separately for each action. -/
def IsFlow : {T : Tree} → Field T → Prop
  | .leaf, _ => True
  | .node _ _ _ _ _ _ _ _, r =>
      (∀ a, (∑ y, root (r.2 a y)) = r.1) ∧
      (∀ a y, IsFlow (r.2 a y))
/-- Nonnegativity at every vertex. -/
def Nonneg : {T : Tree} → Field T → Prop
  | .leaf, r => 0 ≤ r
  | .node _ _ _ _ _ _ _ _, r =>
      0 ≤ r.1 ∧ ∀ a y, Nonneg (r.2 a y)
/-- Pointwise order of fields. -/
def LE : {T : Tree} → Field T → Field T → Prop
  | .leaf, r, s => r ≤ s
  | .node _ _ _ _ _ _ _ _, r, s =>
      r.1 ≤ s.1 ∧ ∀ a y, LE (r.2 a y) (s.2 a y)
theorem Nonneg.root_nonneg {T : Tree} {r : Field T} (h : Nonneg r) :
    0 ≤ root r := by
  cases T with
  | leaf =>
      exact h
  | node =>
      exact h.1
theorem Nonneg.child
    {nA : ℕ} {hA : 0 < nA}
    {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {r : Field (.node nA hA nY hY K Kpos Ksum child)}
    (h : Nonneg r) (a : Fin nA) (y : Fin (nY a)) :
    Nonneg (r.2 a y) :=
  h.2 a y
/-- The probability cylinder field with prescribed root mass `q`. -/
def probability : (T : Tree) → ℝ → Field T
  | .leaf, q => q
  | .node _ _ _ _ K _ _ child, q =>
      (q, fun a y => probability (child a y) (q * K a y))
@[simp] theorem root_probability (T : Tree) (q : ℝ) :
    root (probability T q) = q := by
  cases T <;> rfl
theorem probability_isFlow (T : Tree) (q : ℝ) :
    IsFlow (probability T q) := by
  induction T generalizing q with
  | leaf =>
      trivial
  | node nA hA nY hY K Kpos Ksum child ih =>
      constructor
      · intro a
        simp only [probability, root_probability]
        rw [← Finset.mul_sum, Ksum a, mul_one]
      · intro a y
        exact ih a y (q * K a y)
theorem probability_nonneg (T : Tree) {q : ℝ} (hq : 0 ≤ q) :
    Nonneg (probability T q) := by
  induction T generalizing q with
  | leaf =>
      simpa [Nonneg, probability]
  | node nA hA nY hY K Kpos Ksum child ih =>
      constructor
      · exact hq
      · intro a y
        exact ih a y (mul_nonneg hq (le_of_lt (Kpos a y)))
/-- The original cylinder-probability flow. -/
def p (T : Tree) : Field T := probability T 1
theorem p_isFlow (T : Tree) : IsFlow (p T) :=
  probability_isFlow T 1
theorem p_nonneg (T : Tree) : Nonneg (p T) :=
  probability_nonneg T zero_le_one
@[simp] theorem root_p (T : Tree) : root (p T) = 1 :=
  root_probability T 1
end Field
/-!
## Policies, response strategies, terminal histories
-/
/--
A deterministic adaptive policy.
At a node it chooses one current action, but its continuation is total:
it is specified on every child history, including histories not reached
under its own current choice.
-/
def Policy : Tree → Type
  | .leaf => PUnit
  | .node nA _ nY _ _ _ _ child =>
      Fin nA × ((a : Fin nA) → (y : Fin (nY a)) → Policy (child a y))
/--
A deterministic total response strategy.
At every history it chooses one output separately for every action, and
is also specified recursively on all histories it may never visit.
-/
def Strategy : Tree → Type
  | .leaf => PUnit
  | .node nA _ nY _ _ _ _ child =>
      ((a : Fin nA) → Fin (nY a)) ×
      ((a : Fin nA) → (y : Fin (nY a)) → Strategy (child a y))
/-- Full-tree terminal histories. -/
def Leaf : Tree → Type
  | .leaf => PUnit
  | .node nA _ nY _ _ _ _ child =>
      (a : Fin nA) ×' ((y : Fin (nY a)) ×' Leaf (child a y))
/-- Probability of a terminal history. -/
def leafMass : {T : Tree} → Leaf T → ℝ
  | .leaf, _ => 1
  | .node _ _ _ _ K _ _ _, ⟨a, y, ℓ⟩ =>
      K a y * leafMass ℓ
/-- Compatibility of a terminal history with a policy. -/
def CompatiblePolicy : {T : Tree} → Leaf T → Policy T → Prop
  | .leaf, _, _ => True
  | .node _ _ _ _ _ _ _ _, ⟨a, y, ℓ⟩, π =>
      a = π.1 ∧ CompatiblePolicy ℓ (π.2 a y)
/-- Compatibility of a terminal history with a response strategy. -/
def CompatibleStrategy : {T : Tree} → Leaf T → Strategy T → Prop
  | .leaf, _, _ => True
  | .node _ _ _ _ _ _ _ _, ⟨a, y, ℓ⟩, d =>
      y = d.1 a ∧ CompatibleStrategy ℓ (d.2 a y)
/-- The unique transcript obtained by running deterministic `π` against deterministic `d`. -/
def run : {T : Tree} → Strategy T → Policy T → Leaf T
  | .leaf, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ _, d, π =>
      let a := π.1
      let y := d.1 a
      ⟨a, y, run (d.2 a y) (π.2 a y)⟩
theorem run_compatible_policy :
    ∀ {T : Tree} (d : Strategy T) (π : Policy T),
      CompatiblePolicy (run d π) π := by
  intro T
  induction T with
  | leaf =>
      intro d π
      trivial
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro d π
      constructor
      · rfl
      · exact ih π.1 (d.1 π.1) (d.2 π.1 (d.1 π.1))
          (π.2 π.1 (d.1 π.1))
theorem run_compatible_strategy :
    ∀ {T : Tree} (d : Strategy T) (π : Policy T),
      CompatibleStrategy (run d π) d := by
  intro T
  induction T with
  | leaf =>
      intro d π
      trivial
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro d π
      constructor
      · rfl
      · exact ih π.1 (d.1 π.1) (d.2 π.1 (d.1 π.1))
          (π.2 π.1 (d.1 π.1))
/--
For every pair `(d,π)` there is exactly one compatible terminal history.
This is the combinatorial bridge needed to turn a strategy mixture into
one causal seed valid for every policy.
-/
theorem compatible_leaf_unique :
    ∀ {T : Tree} (d : Strategy T) (π : Policy T) (ℓ : Leaf T),
      CompatibleStrategy ℓ d →
      CompatiblePolicy ℓ π →
      ℓ = run d π := by
  intro T
  induction T with
  | leaf =>
      intro d π ℓ hd hπ
      cases ℓ
      rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro d π ℓ hd hπ
      rcases ℓ with ⟨a, y, ℓ⟩
      rcases hd with ⟨hy, hd⟩
      rcases hπ with ⟨ha, hπ⟩
      subst a
      subst y
      change
        (⟨π.1, d.1 π.1, ℓ⟩ :
          Leaf (.node nA hA nY hY K Kpos Ksum child))
        =
        ⟨π.1, d.1 π.1,
          run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))⟩
      congr
      exact ih π.1 (d.1 π.1) (d.2 π.1 (d.1 π.1))
        (π.2 π.1 (d.1 π.1)) ℓ hd hπ
/-!
## Finite extrema with explicit witnesses
-/
private theorem fin_exists_min {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ i : Fin n, ∀ j : Fin n, f i ≤ f j := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin n)) f hne
  exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩

private theorem fin_exists_max {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) :
    ∃ i : Fin n, ∀ j : Fin n, f j ≤ f i := by
  have hne : (Finset.univ : Finset (Fin n)).Nonempty := ⟨⟨0, hn⟩, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) f hne
  exact ⟨i, fun j => hi j (Finset.mem_univ _)⟩

private noncomputable def finArgmin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : Fin n :=
  Classical.choose (fin_exists_min hn f)

private theorem finArgmin_spec {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (i : Fin n) :
    f (finArgmin hn f) ≤ f i :=
  Classical.choose_spec (fin_exists_min hn f) i

private noncomputable def finArgmax {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : Fin n :=
  Classical.choose (fin_exists_max hn f)

private theorem finArgmax_spec {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (i : Fin n) :
    f i ≤ f (finArgmax hn f) :=
  Classical.choose_spec (fin_exists_max hn f) i
private noncomputable def finMin {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : ℝ :=
  f (finArgmin hn f)
private noncomputable def finMax {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) : ℝ :=
  f (finArgmax hn f)
private theorem finMin_le {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (i : Fin n) :
    finMin hn f ≤ f i :=
  finArgmin_spec hn f i
private theorem le_finMax {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ) (i : Fin n) :
    f i ≤ finMax hn f :=
  finArgmax_spec hn f i
private theorem finMin_mono {n : ℕ} (hn : 0 < n)
    {f g : Fin n → ℝ} (h : ∀ i, f i ≤ g i) :
    finMin hn f ≤ finMin hn g := by
  calc
    finMin hn f ≤ f (finArgmin hn g) := finMin_le hn f _
    _ ≤ g (finArgmin hn g) := h _
    _ = finMin hn g := rfl
private theorem finMax_mono {n : ℕ} (hn : 0 < n)
    {f g : Fin n → ℝ} (h : ∀ i, f i ≤ g i) :
    finMax hn f ≤ finMax hn g := by
  calc
    finMax hn f = f (finArgmax hn f) := rfl
    _ ≤ g (finArgmax hn f) := h _
    _ ≤ finMax hn g := le_finMax hn g _
private theorem finMax_le_of_forall {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) {c : ℝ} (h : ∀ i, f i ≤ c) :
    finMax hn f ≤ c := by
  exact h (finArgmax hn f)
private theorem finMin_pos_of_forall {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (h : ∀ i, 0 < f i) :
    0 < finMin hn f := by
  exact h (finArgmin hn f)
private theorem finMax_pos_of_exists {n : ℕ} (hn : 0 < n)
    (f : Fin n → ℝ) (h : ∃ i, 0 < f i) :
    0 < finMax hn f := by
  rcases h with ⟨i, hi⟩
  exact lt_of_lt_of_le hi (le_finMax hn f i)
/-!
## Bottleneck recursion and exact tree minimax identity
-/
/-- Bellman bottleneck `B_r`. -/
def bottleneck : {T : Tree} → Field T → ℝ
  | .leaf, r => r
  | .node nA hA nY hY _ _ _ _, r =>
      finMin hA (fun a =>
        finMax (hY a) (fun y => bottleneck (r.2 a y)))
/--
For a fixed response strategy, minimum residual over all compatible
terminal histories (all possible action choices).
-/
def strategyFloor : {T : Tree} → Field T → Strategy T → ℝ
  | .leaf, r, _ => r
  | .node _ hA _ _ _ _ _ _, r, d =>
      finMin hA (fun a =>
        strategyFloor (r.2 a (d.1 a)) (d.2 a (d.1 a)))
/--
For a fixed policy, maximum residual over all terminal histories reachable
under that policy (all possible outputs).
-/
def policyCeil : {T : Tree} → Field T → Policy T → ℝ
  | .leaf, r, _ => r
  | .node _ _ _ hY _ _ _ _, r, π =>
      finMax (hY π.1) (fun y =>
        policyCeil (r.2 π.1 y) (π.2 π.1 y))
theorem strategyFloor_le_bottleneck :
    ∀ {T : Tree} (r : Field T) (d : Strategy T),
      strategyFloor r d ≤ bottleneck r := by
  intro T
  induction T with
  | leaf =>
      intro r d
      exact le_rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro r d
      dsimp [strategyFloor, bottleneck]
      apply finMin_mono hA
      intro a
      calc
        strategyFloor (r.2 a (d.1 a)) (d.2 a (d.1 a))
            ≤ bottleneck (r.2 a (d.1 a)) :=
          ih a (d.1 a) (r.2 a (d.1 a)) (d.2 a (d.1 a))
        _ ≤ finMax (hY a) (fun y => bottleneck (r.2 a y)) :=
          le_finMax (hY a) (fun y => bottleneck (r.2 a y)) (d.1 a)
theorem bottleneck_le_policyCeil :
    ∀ {T : Tree} (r : Field T) (π : Policy T),
      bottleneck r ≤ policyCeil r π := by
  intro T
  induction T with
  | leaf =>
      intro r π
      exact le_rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro r π
      dsimp [bottleneck, policyCeil]
      calc
        finMin hA (fun a =>
            finMax (hY a) (fun y => bottleneck (r.2 a y)))
          ≤ finMax (hY π.1) (fun y => bottleneck (r.2 π.1 y)) :=
            finMin_le hA _ π.1
        _ ≤ finMax (hY π.1) (fun y =>
            policyCeil (r.2 π.1 y) (π.2 π.1 y)) := by
              apply finMax_mono (hY π.1)
              intro y
              exact ih π.1 y (r.2 π.1 y) (π.2 π.1 y)
/--
A maximizing response strategy: for every current action, choose a child
with maximal child bottleneck; continue recursively everywhere.
-/
def maximizingStrategy : {T : Tree} → Field T → Strategy T
  | .leaf, _ => PUnit.unit
  | .node _ _ _ hY _ _ _ _, r =>
      let out := fun a =>
        finArgmax (hY a) (fun y => bottleneck (r.2 a y))
      (out, fun a y => maximizingStrategy (r.2 a y))
/--
A minimizing policy: choose a current action minimizing the maximum
child bottleneck; continue recursively everywhere.
-/
def minimizingPolicy : {T : Tree} → Field T → Policy T
  | .leaf, _ => PUnit.unit
  | .node _ hA _ hY _ _ _ _, r =>
      let a0 := finArgmin hA (fun a =>
        finMax (hY a) (fun y => bottleneck (r.2 a y)))
      (a0, fun a y => minimizingPolicy (r.2 a y))
theorem maximizingStrategy_attains :
    ∀ {T : Tree} (r : Field T),
      strategyFloor r (maximizingStrategy r) = bottleneck r := by
  intro T
  induction T with
  | leaf =>
      intro r
      rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro r
      dsimp [maximizingStrategy, strategyFloor, bottleneck]
      apply congrArg (fun f : Fin nA → ℝ => finMin hA f)
      funext a
      rw [ih a (finArgmax (hY a) (fun y => bottleneck (r.2 a y)))
          (r.2 a (finArgmax (hY a) (fun y => bottleneck (r.2 a y))))]
      rfl
theorem minimizingPolicy_attains :
    ∀ {T : Tree} (r : Field T),
      policyCeil r (minimizingPolicy r) = bottleneck r := by
  intro T
  induction T with
  | leaf =>
      intro r
      rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro r
      dsimp [minimizingPolicy, policyCeil, bottleneck]
      let a0 := finArgmin hA (fun a =>
        finMax (hY a) (fun y => bottleneck (r.2 a y)))
      change
        finMax (hY a0) (fun y =>
          policyCeil (r.2 a0 y) (minimizingPolicy (r.2 a0 y)))
        =
        finMin hA (fun a =>
          finMax (hY a) (fun y => bottleneck (r.2 a y)))
      have hchild :
          finMax (hY a0) (fun y =>
            policyCeil (r.2 a0 y) (minimizingPolicy (r.2 a0 y)))
          =
          finMax (hY a0) (fun y => bottleneck (r.2 a0 y)) := by
        apply congrArg (fun f : Fin (nY a0) → ℝ => finMax (hY a0) f)
        funext y
        exact ih a0 y (r.2 a0 y)
      rw [hchild]
      rfl
/--
Exact strategy side:
`B_r(root)` is the greatest value attained by
`d ↦ min_{compatible leaves} r(leaf)`.
-/
theorem bottleneck_isGreatest_strategyFloor {T : Tree} (r : Field T) :
    IsGreatest (Set.range (strategyFloor r)) (bottleneck r) := by
  constructor
  · refine ⟨maximizingStrategy r, ?_⟩
    exact maximizingStrategy_attains r
  · intro x hx
    rcases hx with ⟨d, rfl⟩
    exact strategyFloor_le_bottleneck r d
/--
Exact policy side:
`B_r(root)` is the least value attained by
`π ↦ max_{π-reachable leaves} r(leaf)`.
-/
theorem bottleneck_isLeast_policyCeil {T : Tree} (r : Field T) :
    IsLeast (Set.range (policyCeil r)) (bottleneck r) := by
  constructor
  · refine ⟨minimizingPolicy r, ?_⟩
    exact minimizingPolicy_attains r
  · intro x hx
    rcases hx with ⟨π, rfl⟩
    exact bottleneck_le_policyCeil r π
/--
This pair of `IsGreatest`/`IsLeast` statements is the formal exact minimax
identity
  max_d min_{ℓ∈L(d)} r(ℓ)
    = B_r(root)
    = min_π max_{ℓ∈L_π} r(ℓ).
-/
theorem exact_tree_minimax {T : Tree} (r : Field T) :
    IsGreatest (Set.range (strategyFloor r)) (bottleneck r) ∧
    IsLeast (Set.range (policyCeil r)) (bottleneck r) :=
  ⟨bottleneck_isGreatest_strategyFloor r,
   bottleneck_isLeast_policyCeil r⟩
/-!
## Positivity of the bottleneck
-/
private theorem child_root_le_root
    {nA : ℕ} {hA : 0 < nA}
    {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {r : Field (.node nA hA nY hY K Kpos Ksum child)}
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (a : Fin nA) (y : Fin (nY a)) :
    Field.root (r.2 a y) ≤ Field.root r := by
  have hs :
      Field.root (r.2 a y) ≤ ∑ z : Fin (nY a), Field.root (r.2 a z) := by
    refine Finset.single_le_sum (f := fun z => Field.root (r.2 a z)) ?_ (Finset.mem_univ y)
    intro z _
    exact (hn.2 a z).root_nonneg
  rw [hf.1 a] at hs
  exact hs
theorem bottleneck_le_root :
    ∀ {T : Tree} {r : Field T},
      Field.IsFlow r → Field.Nonneg r →
      bottleneck r ≤ Field.root r := by
  intro T
  induction T with
  | leaf =>
      intro r hf hn
      exact le_rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro r hf hn
      let a0 : Fin nA := ⟨0, hA⟩
      calc
        bottleneck r
            ≤ finMax (hY a0) (fun y => bottleneck (r.2 a0 y)) := by
              exact finMin_le hA _ a0
        _ ≤ Field.root r := by
              apply finMax_le_of_forall (hY a0)
              intro y
              calc
                bottleneck (r.2 a0 y)
                    ≤ Field.root (r.2 a0 y) :=
                      ih a0 y (r := r.2 a0 y) (hf.2 a0 y) (hn.2 a0 y)
                _ ≤ Field.root r :=
                      child_root_le_root hf hn a0 y
theorem bottleneck_pos :
    ∀ {T : Tree} {r : Field T},
      Field.IsFlow r → Field.Nonneg r →
      0 < Field.root r →
      0 < bottleneck r := by
  intro T
  induction T with
  | leaf =>
      intro r hf hn hr
      exact hr
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro r hf hn hr
      apply finMin_pos_of_forall hA
      intro a
      apply finMax_pos_of_exists (hY a)
      have hex : ∃ y : Fin (nY a), 0 < Field.root (r.2 a y) := by
        by_contra h
        simp only [not_exists, not_lt] at h
        have hz : ∀ y : Fin (nY a), Field.root (r.2 a y) = 0 := by
          intro y
          exact le_antisymm (h y) ((hn.2 a y).root_nonneg)
        have hsum0 : (∑ y, Field.root (r.2 a y)) = 0 := by
          simp [hz]
        rw [hf.1 a] at hsum0
        simp only [Field.root] at hr
        linarith
      rcases hex with ⟨y, hy⟩
      refine ⟨y, ?_⟩
      exact ih a y (r := r.2 a y) (hf.2 a y) (hn.2 a y) hy
/-- Required positivity consequence for a residual flow. -/
theorem positive_root_implies_positive_bottleneck
    {T : Tree} {r : Field T}
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (hr : 0 < Field.root r) :
    0 < bottleneck r :=
  bottleneck_pos hf hn hr
/-!
## Leaf count
Used later as the well-founded measure for greedy extraction.
-/
def terminalCount : Tree → ℕ
  | .leaf => 1
  | .node _ _ _ _ _ _ _ child =>
      ∑ a, ∑ y, terminalCount (child a y)
theorem terminalCount_pos : ∀ T : Tree, 0 < terminalCount T := by
  intro T
  induction T with
  | leaf =>
      simp [terminalCount]
  | node nA hA nY hY K Kpos Ksum child ih =>
      have ha : ∃ a : Fin nA, True := ⟨⟨0, hA⟩, trivial⟩
      rcases ha with ⟨a, -⟩
      have hy : ∃ y : Fin (nY a), True := ⟨⟨0, hY a⟩, trivial⟩
      rcases hy with ⟨y, -⟩
      have hpos : 0 < terminalCount (child a y) := ih a y
      have h1 :
          terminalCount (child a y)
            ≤ ∑ z : Fin (nY a), terminalCount (child a z) := by
        refine Finset.single_le_sum
          (f := fun z : Fin (nY a) => terminalCount (child a z)) ?_ (Finset.mem_univ y)
        intro _ _
        exact Nat.zero_le _
      have h2 :
          (∑ z : Fin (nY a), terminalCount (child a z))
            ≤ ∑ b : Fin nA, ∑ z : Fin (nY b), terminalCount (child b z) := by
        refine Finset.single_le_sum
          (f := fun b : Fin nA => ∑ z : Fin (nY b), terminalCount (child b z)) ?_
          (Finset.mem_univ a)
        intro _ _
        exact Nat.zero_le _
      exact lt_of_lt_of_le hpos (le_trans h1 h2)

/-! Semantic bridge from recursive extrema to actual terminal histories. -/
def leafValue : {T : Tree} → Field T → Leaf T → ℝ
  | .leaf, r, _ => r
  | .node _ _ _ _ _ _ _ _, r, ⟨a, y, ℓ⟩ =>
      leafValue (r.2 a y) ℓ

theorem strategyFloor_le_leaf : ∀ {T : Tree} (r : Field T)
    (d : Strategy T) (ℓ : Leaf T), CompatibleStrategy ℓ d →
    strategyFloor r d ≤ leafValue r ℓ := by
  intro T
  induction T with
  | leaf => intro r d ℓ h; exact le_rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r d ℓ h
    rcases ℓ with ⟨a, y, ℓ⟩
    rcases h with ⟨hy, hℓ⟩
    subst y
    exact le_trans (finMin_le hA _ a)
      (ih a (d.1 a) (r.2 a (d.1 a)) (d.2 a (d.1 a)) ℓ hℓ)

theorem strategyFloor_attained_leaf : ∀ {T : Tree} (r : Field T)
    (d : Strategy T), ∃ ℓ : Leaf T,
    CompatibleStrategy ℓ d ∧ leafValue r ℓ = strategyFloor r d := by
  intro T
  induction T with
  | leaf => intro r d; exact ⟨PUnit.unit, trivial, rfl⟩
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r d
    let a := finArgmin hA (fun a =>
      strategyFloor (r.2 a (d.1 a)) (d.2 a (d.1 a)))
    obtain ⟨ℓ, hc, he⟩ := ih a (d.1 a)
      (r.2 a (d.1 a)) (d.2 a (d.1 a))
    refine ⟨⟨a, d.1 a, ℓ⟩, ⟨rfl, hc⟩, ?_⟩
    exact he

theorem leaf_le_policyCeil : ∀ {T : Tree} (r : Field T)
    (π : Policy T) (ℓ : Leaf T), CompatiblePolicy ℓ π →
    leafValue r ℓ ≤ policyCeil r π := by
  intro T
  induction T with
  | leaf => intro r π ℓ h; exact le_rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r π ℓ h
    rcases ℓ with ⟨a, y, ℓ⟩
    rcases h with ⟨ha, hℓ⟩
    subst a
    exact le_trans (ih π.1 y (r.2 π.1 y) (π.2 π.1 y) ℓ hℓ)
      (le_finMax (hY π.1) (fun y => policyCeil (r.2 π.1 y) (π.2 π.1 y)) y)

theorem policyCeil_attained_leaf : ∀ {T : Tree} (r : Field T)
    (π : Policy T), ∃ ℓ : Leaf T,
    CompatiblePolicy ℓ π ∧ leafValue r ℓ = policyCeil r π := by
  intro T
  induction T with
  | leaf => intro r π; exact ⟨PUnit.unit, trivial, rfl⟩
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r π
    let y := finArgmax (hY π.1) (fun y =>
      policyCeil (r.2 π.1 y) (π.2 π.1 y))
    obtain ⟨ℓ, hc, he⟩ := ih π.1 y (r.2 π.1 y) (π.2 π.1 y)
    exact ⟨⟨π.1, y, ℓ⟩, ⟨rfl, hc⟩, he⟩

theorem strategyFloor_isLeast_leaves {T : Tree} (r : Field T)
    (d : Strategy T) :
    IsLeast {x : ℝ | ∃ ℓ : Leaf T,
      CompatibleStrategy ℓ d ∧ leafValue r ℓ = x}
      (strategyFloor r d) := by
  constructor
  · exact strategyFloor_attained_leaf r d
  · rintro x ⟨ℓ, hc, rfl⟩
    exact strategyFloor_le_leaf r d ℓ hc

theorem policyCeil_isGreatest_leaves {T : Tree} (r : Field T)
    (π : Policy T) :
    IsGreatest {x : ℝ | ∃ ℓ : Leaf T,
      CompatiblePolicy ℓ π ∧ leafValue r ℓ = x}
      (policyCeil r π) := by
  constructor
  · exact policyCeil_attained_leaf r π
  · rintro x ⟨ℓ, hc, rfl⟩
    exact leaf_le_policyCeil r π ℓ hc

theorem leafValue_nonneg : ∀ {T : Tree} (r : Field T),
    Field.Nonneg r → ∀ ℓ : Leaf T, 0 ≤ leafValue r ℓ := by
  intro T
  induction T with
  | leaf => intro r hn ℓ; exact hn
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r hn ℓ
    rcases ℓ with ⟨a, y, ℓ⟩
    exact ih a y (r.2 a y) (hn.2 a y) ℓ

/-! Subtract a strategy atom on all compatible vertices. -/
def extract : {T : Tree} → Field T → Strategy T → ℝ → Field T
  | .leaf, r, _, w => r - w
  | .node _ _ _ _ _ _ _ _, r, d, w =>
    (r.1 - w, fun a y =>
      if y = d.1 a then extract (r.2 a y) (d.2 a y) w else r.2 a y)

@[simp] theorem root_extract {T : Tree} (r : Field T)
    (d : Strategy T) (w : ℝ) :
    Field.root (extract r d w) = Field.root r - w := by
  cases T <;> rfl

theorem extract_isFlow : ∀ {T : Tree} (r : Field T)
    (d : Strategy T) (w : ℝ), Field.IsFlow r →
    Field.IsFlow (extract r d w) := by
  intro T
  induction T with
  | leaf => intro r d w hf; trivial
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r d w hf
    constructor
    · intro a
      change (∑ y, Field.root
        (if y = d.1 a then extract (r.2 a y) (d.2 a y) w
         else r.2 a y)) = r.1 - w
      have he : ∀ y : Fin (nY a),
          Field.root (if y = d.1 a then extract (r.2 a y) (d.2 a y) w
            else r.2 a y) =
          Field.root (r.2 a y) - (if y = d.1 a then w else 0) := by
        intro y
        by_cases hy : y = d.1 a <;> simp [hy]
      simp_rw [he]
      rw [Finset.sum_sub_distrib, hf.1 a]
      simp
    · intro a y
      change Field.IsFlow
        (if y = d.1 a then extract (r.2 a y) (d.2 a y) w else r.2 a y)
      split_ifs
      · exact ih a y (r.2 a y) (d.2 a y) w (hf.2 a y)
      · exact hf.2 a y

theorem extract_nonneg : ∀ {T : Tree} (r : Field T)
    (d : Strategy T) (w : ℝ), Field.IsFlow r → Field.Nonneg r →
    w ≤ strategyFloor r d → Field.Nonneg (extract r d w) := by
  intro T
  induction T with
  | leaf => intro r d w hf hn hw; exact sub_nonneg.mpr hw
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r d w hf hn hw
    constructor
    · exact sub_nonneg.mpr (le_trans hw
        (le_trans (strategyFloor_le_bottleneck r d) (bottleneck_le_root hf hn)))
    · intro a y
      change Field.Nonneg
        (if y = d.1 a then extract (r.2 a y) (d.2 a y) w else r.2 a y)
      split_ifs with hy
      · subst y
        exact ih a (d.1 a) (r.2 a (d.1 a)) (d.2 a (d.1 a)) w
          (hf.2 a (d.1 a)) (hn.2 a (d.1 a))
          (le_trans hw (finMin_le hA _ a))
      · exact hn.2 a y

theorem leafValue_extract : ∀ {T : Tree} (r : Field T)
    (d : Strategy T) (w : ℝ) (ℓ : Leaf T),
    leafValue (extract r d w) ℓ =
      leafValue r ℓ - (if CompatibleStrategy ℓ d then w else 0) := by
  classical
  intro T
  induction T with
  | leaf => intro r d w ℓ; simp [extract, leafValue, CompatibleStrategy]
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r d w ℓ
    rcases ℓ with ⟨a, y, ℓ⟩
    by_cases hy : y = d.1 a
    · simpa [extract, leafValue, CompatibleStrategy, hy] using
        ih a y (r.2 a y) (d.2 a y) w ℓ
    · simp [extract, leafValue, CompatibleStrategy, hy]

/-- The exact one-step extraction certificate, with a leaf killed by this step. -/
theorem greedy_step {T : Tree} (r : Field T)
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (hr : 0 < Field.root r) :
    let w := bottleneck r
    let d := maximizingStrategy r
    let r' := extract r d w
    0 < w ∧ Field.IsFlow r' ∧ Field.Nonneg r' ∧
    Field.root r' = Field.root r - w ∧
    ∃ ℓ : Leaf T, CompatibleStrategy ℓ d ∧
      leafValue r ℓ = w ∧ 0 < leafValue r ℓ ∧ leafValue r' ℓ = 0 := by
  classical
  dsimp only
  have hw := bottleneck_pos hf hn hr
  obtain ⟨ℓ, hc, he⟩ := strategyFloor_attained_leaf r (maximizingStrategy r)
  rw [maximizingStrategy_attains] at he
  refine ⟨hw, extract_isFlow _ _ _ hf,
    extract_nonneg _ _ _ hf hn (le_of_eq (maximizingStrategy_attains r).symm),
    root_extract _ _ _, ℓ, hc, he, ?_, ?_⟩
  · rwa [he]
  · rw [leafValue_extract, if_pos hc, he, sub_self]

noncomputable instance leafFintype : (T : Tree) → Fintype (Leaf T)
  | .leaf => by
      unfold Leaf
      exact Fintype.ofSubsingleton PUnit.unit
  | .node nA hA nY hY K Kpos Ksum child => by
      letI : ∀ a y, Fintype (Leaf (child a y)) := fun a y => leafFintype (child a y)
      unfold Leaf
      infer_instance

noncomputable def positiveLeaves {T : Tree} (r : Field T) : Finset (Leaf T) := by
  classical
  exact Finset.univ.filter (fun ℓ => 0 < leafValue r ℓ)

noncomputable def positiveLeafCount {T : Tree} (r : Field T) : ℕ :=
  (positiveLeaves r).card

theorem greedy_count_decreases {T : Tree} (r : Field T)
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (hr : 0 < Field.root r) :
    positiveLeafCount (extract r (maximizingStrategy r) (bottleneck r)) <
      positiveLeafCount r := by
  classical
  obtain ⟨hw, hflow, hnonneg, hroot, ℓ, hc, he, hp, hz⟩ := greedy_step r hf hn hr
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro k hk
    simp only [positiveLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    rw [leafValue_extract] at hk
    split_ifs at hk
    · linarith
    · simpa using hk
  · intro heq
    have hmem : ℓ ∈ positiveLeaves r := by
      simpa [positiveLeaves] using hp
    rw [← heq] at hmem
    have : 0 < leafValue (extract r (maximizingStrategy r) (bottleneck r)) ℓ := by
      simpa [positiveLeaves] using hmem
    linarith

theorem leafValue_le_root : ∀ {T : Tree} (r : Field T),
    Field.IsFlow r → Field.Nonneg r → ∀ ℓ : Leaf T,
    leafValue r ℓ ≤ Field.root r := by
  intro T
  induction T with
  | leaf => intro r hf hn ℓ; exact le_rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r hf hn ℓ
    rcases ℓ with ⟨a, y, ℓ⟩
    exact le_trans (ih a y (r.2 a y) (hf.2 a y) (hn.2 a y) ℓ)
      (child_root_le_root hf hn a y)

/-- Atom indices remain distinct even if their response strategies coincide. -/
abbrev Atom (T : Tree) := ℝ × Strategy T

def totalWeight {T : Tree} (atoms : List (Atom T)) : ℝ :=
  (atoms.map Prod.fst).sum

noncomputable def representedLeaf {T : Tree} (atoms : List (Atom T))
    (ℓ : Leaf T) : ℝ := by
  classical
  exact (atoms.map (fun a => if CompatibleStrategy ℓ a.2 then a.1 else 0)).sum

/-- A finite positive strategy decomposition of a nonnegative flow. -/
theorem finite_flow_decomposition {T : Tree} (r : Field T)
    (hf : Field.IsFlow r) (hn : Field.Nonneg r) :
    ∃ atoms : List (Atom T),
      (∀ a ∈ atoms, 0 < a.1) ∧
      atoms.length ≤ positiveLeafCount r ∧
      totalWeight atoms = Field.root r ∧
      ∀ ℓ : Leaf T, representedLeaf atoms ℓ = leafValue r ℓ := by
  classical
  have aux : ∀ n : ℕ, ∀ r : Field T,
      positiveLeafCount r = n → Field.IsFlow r → Field.Nonneg r →
      ∃ atoms : List (Atom T),
        (∀ a ∈ atoms, 0 < a.1) ∧
        atoms.length ≤ positiveLeafCount r ∧
        totalWeight atoms = Field.root r ∧
        ∀ ℓ : Leaf T, representedLeaf atoms ℓ = leafValue r ℓ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r hcount hf hn
      by_cases hr : 0 < Field.root r
      · let w := bottleneck r
        let d := maximizingStrategy r
        let r' := extract r d w
        have step := greedy_step r hf hn hr
        obtain ⟨hw, hflow, hnonneg, hroot, hkilled⟩ := step
        have hlt : positiveLeafCount r' < n := by
          simpa [r', d, w, hcount] using greedy_count_decreases r hf hn hr
        obtain ⟨atoms, hpos, hlen, hsum, hrep⟩ :=
          ih (positiveLeafCount r') hlt r' rfl hflow hnonneg
        refine ⟨(w, d) :: atoms, ?_, ?_, ?_, ?_⟩
        · intro a ha
          simp only [List.mem_cons] at ha
          rcases ha with rfl | ha
          · exact hw
          · exact hpos a ha
        · simp only [List.length_cons]
          have : positiveLeafCount r' < positiveLeafCount r := by omega
          omega
        · change w + totalWeight atoms = Field.root r
          rw [hsum]
          change w + Field.root (extract r d w) = Field.root r
          rw [root_extract]
          ring
        · intro ℓ
          change (if CompatibleStrategy ℓ d then w else 0) +
            representedLeaf atoms ℓ = leafValue r ℓ
          rw [hrep]
          change (if CompatibleStrategy ℓ d then w else 0) +
            leafValue (extract r d w) ℓ = leafValue r ℓ
          rw [leafValue_extract]
          ring
      · have hz : Field.root r = 0 :=
          le_antisymm (le_of_not_gt hr) hn.root_nonneg
        refine ⟨[], ?_, ?_, ?_, ?_⟩
        · simp
        · simp
        · simpa [totalWeight] using hz.symm
        · intro ℓ
          have hl : leafValue r ℓ = 0 :=
            le_antisymm (by simpa [hz] using leafValue_le_root r hf hn ℓ)
              (leafValue_nonneg r hn ℓ)
          simp [representedLeaf, hl]
  exact aux (positiveLeafCount r) r rfl hf hn

theorem leafValue_probability : ∀ (T : Tree) (q : ℝ) (ℓ : Leaf T),
    leafValue (Field.probability T q) ℓ = q * leafMass ℓ := by
  intro T
  induction T with
  | leaf => intro q ℓ; simp [Field.probability, leafValue, leafMass]
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro q ℓ
    rcases ℓ with ⟨a, y, ℓ⟩
    change leafValue (Field.probability (child a y) (q * K a y)) ℓ =
      q * (K a y * leafMass ℓ)
    rw [ih a y]
    ring

/-- Concrete seed semantics: choose a LIST INDEX with its positive atom weight,
then run that index's strategy. Equal strategies need not be merged. -/
noncomputable def transcriptWeight {T : Tree} (atoms : List (Atom T))
    (π : Policy T) (ℓ : Leaf T) : ℝ := by
  classical
  exact (atoms.map (fun a => if run a.2 π = ℓ then a.1 else 0)).sum

theorem run_eq_iff {T : Tree} (d : Strategy T) (π : Policy T) (ℓ : Leaf T) :
    run d π = ℓ ↔ CompatibleStrategy ℓ d ∧ CompatiblePolicy ℓ π := by
  constructor
  · rintro rfl
    exact ⟨run_compatible_strategy d π, run_compatible_policy d π⟩
  · rintro ⟨hd, hp⟩
    exact (compatible_leaf_unique d π ℓ hd hp).symm

theorem transcriptWeight_eq {T : Tree} (atoms : List (Atom T))
    (π : Policy T) (ℓ : Leaf T) :
    transcriptWeight atoms π ℓ =
      if CompatiblePolicy ℓ π then representedLeaf atoms ℓ else 0 := by
  classical
  by_cases hp : CompatiblePolicy ℓ π
  · simp only [transcriptWeight, representedLeaf, if_pos hp]
    have he : (fun a : Atom T => if run a.2 π = ℓ then a.1 else 0) =
        (fun a : Atom T => if CompatibleStrategy ℓ a.2 then a.1 else 0) := by
      funext a
      simp [run_eq_iff, hp]
    rw [he]
  · simp [transcriptWeight, run_eq_iff, hp]

/-- Exact finite causal realization, simultaneously for EVERY deterministic policy.
This theorem is a realization theorem ONLY; it contains no entropy bound. -/
theorem exact_finite_seed (T : Tree) :
    ∃ atoms : List (Atom T),
      (∀ a ∈ atoms, 0 < a.1) ∧
      atoms.length ≤ Fintype.card (Leaf T) ∧
      totalWeight atoms = 1 ∧
      ∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ =
          if CompatiblePolicy ℓ π then leafMass ℓ else 0 := by
  classical
  obtain ⟨atoms, hpos, hlen, hsum, hrep⟩ :=
    finite_flow_decomposition (Field.p T) (Field.p_isFlow T) (Field.p_nonneg T)
  refine ⟨atoms, hpos, ?_, ?_, ?_⟩
  · exact le_trans hlen (Finset.card_le_univ _)
  · simpa using hsum
  · intro π ℓ
    rw [transcriptWeight_eq, hrep]
    have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
      simpa [Field.p] using leafValue_probability T 1 ℓ
    rw [hp]

#print axioms exact_tree_minimax
#print axioms strategyFloor_isLeast_leaves
#print axioms policyCeil_isGreatest_leaves
#print axioms greedy_step
#print axioms greedy_count_decreases
#print axioms finite_flow_decomposition
#print axioms exact_finite_seed


/-! Greedy history: unlike an arbitrary decomposition this retains every
    optimal extraction, and therefore supports a cutoff argument. -/
inductive GreedyTrace {T : Tree} : Field T → List (Atom T) → Prop
  | done (r : Field T) (hz : Field.root r = 0) : GreedyTrace r []
  | step (r : Field T) (tail : List (Atom T))
      (hr : 0 < Field.root r)
      (next : GreedyTrace
        (extract r (maximizingStrategy r) (bottleneck r)) tail) :
      GreedyTrace r ((bottleneck r, maximizingStrategy r) :: tail)

theorem greedyTrace_exists {T : Tree} (r : Field T)
    (hf : Field.IsFlow r) (hn : Field.Nonneg r) :
    ∃ atoms, GreedyTrace r atoms := by
  have aux : ∀ n : ℕ, ∀ r : Field T, positiveLeafCount r = n →
      Field.IsFlow r → Field.Nonneg r → ∃ atoms, GreedyTrace r atoms := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro r hc hf hn
      by_cases hr : 0 < Field.root r
      · obtain ⟨hw, hf', hn', hroot, hk⟩ := greedy_step r hf hn hr
        have hlt : positiveLeafCount
            (extract r (maximizingStrategy r) (bottleneck r)) < n := by
          simpa [hc] using greedy_count_decreases r hf hn hr
        obtain ⟨atoms, ht⟩ := ih _ hlt _ rfl hf' hn'
        exact ⟨_, GreedyTrace.step r atoms hr ht⟩
      · exact ⟨[], GreedyTrace.done r
          (le_antisymm (le_of_not_gt hr) hn.root_nonneg)⟩
  exact aux _ r rfl hf hn

theorem bottleneck_mono : ∀ {T : Tree} (r s : Field T),
    Field.LE r s → bottleneck r ≤ bottleneck s := by
  intro T
  induction T with
  | leaf => intro r s h; exact h
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r s h
    apply finMin_mono hA
    intro a
    apply finMax_mono (hY a)
    intro y
    exact ih a y (r.2 a y) (s.2 a y) (h.2 a y)

theorem extract_le : ∀ {T : Tree} (r : Field T) (d : Strategy T)
    (w : ℝ), 0 ≤ w → Field.LE (extract r d w) r := by
  intro T
  induction T with
  | leaf => intro r d w hw; exact sub_le_self r hw
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r d w hw
    constructor
    · exact sub_le_self r.1 hw
    · intro a y
      change Field.LE
        (if y = d.1 a then extract (r.2 a y) (d.2 a y) w else r.2 a y)
        (r.2 a y)
      split_ifs
      · exact ih a y (r.2 a y) (d.2 a y) w hw
      · have reflField : ∀ {U : Tree} (s : Field U), Field.LE s s := by
          intro U
          induction U with
          | leaf => intro s; exact le_rfl
          | node m hm ny hy k kp ks ch hi =>
            intro s
            exact ⟨le_rfl, fun b z => hi b z (s.2 b z)⟩
        exact reflField _

theorem greedyTrace_properties {T : Tree} {r : Field T}
    {atoms : List (Atom T)} (ht : GreedyTrace r atoms)
    (hf : Field.IsFlow r) (hn : Field.Nonneg r) :
    (∀ a ∈ atoms, 0 < a.1 ∧ a.1 ≤ bottleneck r) ∧
    atoms.length ≤ positiveLeafCount r ∧
    totalWeight atoms = Field.root r ∧
    ∀ ℓ, representedLeaf atoms ℓ = leafValue r ℓ := by
  classical
  induction ht with
  | done r hz =>
    refine ⟨by simp, by simp, ?_, ?_⟩
    · simpa [totalWeight] using hz.symm
    · intro ℓ
      have hl : leafValue r ℓ = 0 :=
        le_antisymm (by simpa [hz] using leafValue_le_root r hf hn ℓ)
          (leafValue_nonneg r hn ℓ)
      simp [representedLeaf, hl]
  | step r tail hr ht ih =>
    obtain ⟨hw, hf', hn', hroot, hk⟩ := greedy_step r hf hn hr
    obtain ⟨ha, hlen, hsum, hrep⟩ := ih hf' hn'
    have hb : bottleneck (extract r (maximizingStrategy r) (bottleneck r)) ≤
        bottleneck r := bottleneck_mono _ _ (extract_le _ _ _ hw.le)
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro a ha'
      simp only [List.mem_cons] at ha'
      rcases ha' with rfl | ha'
      · exact ⟨hw, le_rfl⟩
      · exact ⟨(ha a ha').1, le_trans (ha a ha').2 hb⟩
    · have hlt := greedy_count_decreases r hf hn hr
      simp only [List.length_cons]
      omega
    · change bottleneck r + totalWeight tail = Field.root r
      rw [hsum, root_extract]
      ring
    · intro ℓ
      change (if CompatibleStrategy ℓ (maximizingStrategy r) then bottleneck r else 0)
        + representedLeaf tail ℓ = leafValue r ℓ
      rw [hrep, leafValue_extract]
      ring

noncomputable def smallWeight {T : Tree} (atoms : List (Atom T)) (δ : ℝ) : ℝ := by
  classical
  exact (atoms.map (fun a => if a.1 ≤ δ then a.1 else 0)).sum

/-- Residual relation after removing atoms each larger than the cutoff. -/
def CutHistory {T : Tree} (δ : ℝ) (p r : Field T) : Prop :=
  ∀ ℓ : Leaf T, leafValue r ℓ ≤ leafValue p ℓ ∧
    (leafValue r ℓ = leafValue p ℓ ∨ leafValue r ℓ ≤ leafValue p ℓ - δ)

theorem cutHistory_self {T : Tree} (δ : ℝ) (p : Field T) : CutHistory δ p p :=
  fun _ => ⟨le_rfl, Or.inl rfl⟩

theorem cutHistory_extract {T : Tree} (δ : ℝ) (p r : Field T)
    (d : Strategy T) (w : ℝ) (hδ : 0 ≤ δ) (hw : δ < w)
    (hh : CutHistory δ p r) : CutHistory δ p (extract r d w) := by
  classical
  intro ℓ
  rw [leafValue_extract]
  by_cases hc : CompatibleStrategy ℓ d
  · simp only [if_pos hc]
    have hle := (hh ℓ).1
    constructor
    · linarith
    · right; linarith
  · simpa [hc] using hh ℓ

/-- Every cutoff has a residual flow of exactly the mass of the small atoms;
    its bottleneck is at most the cutoff and it remembers the removed atoms. -/
theorem greedy_cutoff {T : Tree} {r : Field T} {atoms : List (Atom T)}
    (ht : GreedyTrace r atoms) (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (δ : ℝ) (hδ : 0 ≤ δ) (p : Field T) (hh : CutHistory δ p r) :
    ∃ s : Field T, Field.IsFlow s ∧ Field.Nonneg s ∧
      Field.root s = smallWeight atoms δ ∧ bottleneck s ≤ δ ∧ CutHistory δ p s := by
  classical
  induction ht with
  | done r hz =>
    refine ⟨r, hf, hn, ?_, ?_, hh⟩
    · simpa [smallWeight] using hz
    · exact le_trans (bottleneck_le_root hf hn) (by simpa [hz] using hδ)
  | step r tail hr ht ih =>
    obtain ⟨hw, hf', hn', hroot, hk⟩ := greedy_step r hf hn hr
    by_cases hsmall : bottleneck r ≤ δ
    · have hp := greedyTrace_properties (GreedyTrace.step r tail hr ht) hf hn
      have he : smallWeight ((bottleneck r, maximizingStrategy r) :: tail) δ =
          totalWeight ((bottleneck r, maximizingStrategy r) :: tail) := by
        unfold smallWeight totalWeight
        congr 1
        apply List.map_congr_left
        intro a ha
        exact if_pos (le_trans (hp.1 a ha).2 hsmall)
      exact ⟨r, hf, hn, (he.trans hp.2.2.1).symm, hsmall, hh⟩
    · have hlarge : δ < bottleneck r := lt_of_not_ge hsmall
      obtain ⟨s, hsflow, hsnonneg, hsroot, hsbot, hshist⟩ :=
        ih hf' hn' (cutHistory_extract δ p r (maximizingStrategy r)
          (bottleneck r) hδ hlarge hh)
      refine ⟨s, hsflow, hsnonneg, ?_, hsbot, hshist⟩
      simpa [smallWeight, hsmall] using hsroot

/-- Sum over the terminal histories compatible with one policy. -/
def policySum : {T : Tree} → (Leaf T → ℝ) → Policy T → ℝ
  | .leaf, f, _ => f PUnit.unit
  | .node _ _ _ _ _ _ _ _, f, π =>
      ∑ y, policySum (fun ℓ => f ⟨π.1, y, ℓ⟩) (π.2 π.1 y)

theorem policySum_mono : ∀ {T : Tree} (f g : Leaf T → ℝ) (π : Policy T),
    (∀ ℓ, CompatiblePolicy ℓ π → f ℓ ≤ g ℓ) → policySum f π ≤ policySum g π := by
  intro T
  induction T with
  | leaf => intro f g π h; exact h PUnit.unit trivial
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro f g π h
    apply Finset.sum_le_sum
    intro y hy
    apply ih π.1 y
    intro ℓ hℓ
    exact h ⟨π.1, y, ℓ⟩ ⟨rfl, hℓ⟩

theorem policySum_flow : ∀ {T : Tree} (r : Field T) (π : Policy T),
    Field.IsFlow r → policySum (leafValue r) π = Field.root r := by
  intro T
  induction T with
  | leaf => intro r π hf; rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro r π hf
    change (∑ y, policySum (leafValue (r.2 π.1 y)) (π.2 π.1 y)) = r.1
    have he : ∀ y, policySum (leafValue (r.2 π.1 y)) (π.2 π.1 y) =
        Field.root (r.2 π.1 y) := fun y => ih π.1 y _ _ (hf.2 π.1 y)
    simp_rw [he]
    exact hf.1 π.1

noncomputable def aDelta (δ p : ℝ) : ℝ :=
  if p ≤ δ then p else min δ (p - δ)

noncomputable def psi (u : ℝ) : ℝ :=
  if u ≤ 1 / 2 then u else if u < 1 then 1 / 2 else 1

theorem psi_mono : Monotone psi := by
  intro u v huv
  unfold psi
  split_ifs <;> linarith

theorem aDelta_le_majorant (δ p : ℝ) (hδ : 0 ≤ δ) (hp : 0 < p) :
    aDelta δ p ≤ p * psi (δ / p) := by
  unfold aDelta psi
  by_cases hpd : p ≤ δ
  · rw [if_pos hpd]
    have hu : 1 ≤ δ / p := (le_div_iff₀ hp).mpr (by simpa using hpd)
    rw [if_neg (by linarith), if_neg (by linarith)]
    simp
  · rw [if_neg hpd]
    by_cases hh : δ / p ≤ 1 / 2
    · rw [if_pos hh]
      have he : p * (δ / p) = δ := by field_simp
      rw [he]
      exact min_le_left _ _
    · rw [if_neg hh]
      have hu : δ / p < 1 := (div_lt_iff₀ hp).mpr (by linarith)
      rw [if_pos hu]
      have hd : p / 2 < δ := by
        have := (lt_div_iff₀ hp).mp (lt_of_not_ge hh)
        linarith
      exact le_trans (min_le_right _ _) (by linarith)

theorem leafMass_pos : ∀ {T : Tree} (ℓ : Leaf T), 0 < leafMass ℓ := by
  intro T
  induction T with
  | leaf => intro ℓ; exact zero_lt_one
  | node nA hA nY hY K Kpos Ksum child ih =>
    rintro ⟨a, y, ℓ⟩
    exact mul_pos (Kpos a y) (ih a y ℓ)

/-- The strengthened finite cutoff bound, still before any logarithms or measures. -/
theorem greedy_advanced_bound {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ π : Policy T, smallWeight atoms δ ≤
      policySum (fun ℓ => aDelta δ (leafMass ℓ)) π := by
  obtain ⟨s, hf, hn, hroot, hb, hh⟩ :=
    greedy_cutoff ht (Field.p_isFlow T) (Field.p_nonneg T) δ hδ
      (Field.p T) (cutHistory_self δ (Field.p T))
  let π := minimizingPolicy s
  refine ⟨π, ?_⟩
  rw [← hroot, ← policySum_flow s π hf]
  apply policySum_mono
  intro ℓ hc
  have hsmall : leafValue s ℓ ≤ δ := by
    have hl := leaf_le_policyCeil s π ℓ hc
    have he : policyCeil s π = bottleneck s := minimizingPolicy_attains s
    rw [he] at hl
    exact le_trans hl hb
  have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
    simpa [Field.p] using leafValue_probability T 1 ℓ
  obtain ⟨hle, heq | hremoved⟩ := hh ℓ
  · rw [hp] at hle heq
    by_cases hpd : leafMass ℓ ≤ δ
    · simpa [aDelta, hpd] using hle
    · exfalso; linarith
  · rw [hp] at hle hremoved
    by_cases hpd : leafMass ℓ ≤ δ
    · simpa [aDelta, hpd] using hle
    · exact (by
        rw [aDelta, if_neg hpd]
        exact le_min hsmall hremoved)

theorem greedy_refined_bound {T : Tree} {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) (δ : ℝ) (hδ : 0 ≤ δ) :
    ∃ π : Policy T, smallWeight atoms δ ≤
      policySum (fun ℓ => leafMass ℓ * psi (δ / leafMass ℓ)) π := by
  obtain ⟨π, hπ⟩ := greedy_advanced_bound ht δ hδ
  refine ⟨π, le_trans hπ ?_⟩
  apply policySum_mono
  intro ℓ hc
  exact aDelta_le_majorant δ (leafMass ℓ) hδ (leafMass_pos ℓ)

/-- One and the same exact seed satisfies the refined bound at EVERY cutoff.
    This is stronger than choosing a different seed at each cutoff. -/
theorem exact_seed_with_refined_cutoffs (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧
      (∀ a ∈ atoms, 0 < a.1) ∧
      atoms.length ≤ Fintype.card (Leaf T) ∧
      totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T), transcriptWeight atoms π ℓ =
        if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      (∀ δ : ℝ, 0 ≤ δ → ∃ π : Policy T, smallWeight atoms δ ≤
        policySum (fun ℓ => leafMass ℓ * psi (δ / leafMass ℓ)) π) := by
  classical
  obtain ⟨atoms, ht⟩ := greedyTrace_exists (Field.p T)
    (Field.p_isFlow T) (Field.p_nonneg T)
  obtain ⟨hpos, hlen, hsum, hrep⟩ := greedyTrace_properties ht
    (Field.p_isFlow T) (Field.p_nonneg T)
  refine ⟨atoms, ht, (fun a ha => (hpos a ha).1),
    le_trans hlen (Finset.card_le_univ _), ?_, ?_, ?_⟩
  · simpa using hsum
  · intro π ℓ
    rw [transcriptWeight_eq, hrep]
    have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
      simpa [Field.p] using leafValue_probability T 1 ℓ
    rw [hp]
  · intro δ hδ
    exact greedy_refined_bound ht δ hδ

/-! These are the new kernel-audit entry points. Running this file is required
before claiming certification. The probability-measure envelope construction,
stochastic sandwich, Shannon/Renyi inequalities and Wasserstein identity are
NOT proved in this file. No theorem below assumes them as hypotheses. -/
#print axioms greedyTrace_exists
#print axioms greedyTrace_properties
#print axioms greedy_cutoff
#print axioms aDelta_le_majorant
#print axioms greedy_advanced_bound
#print axioms greedy_refined_bound
#print axioms exact_seed_with_refined_cutoffs

end CausalSpectrum

/-
Zero probabilities, part 2: finite controlled trees whose kernels may vanish.

A `ZTree` is a shape (all actions, outputs and histories, nothing pruned)
together with a kernel field `K(y|h,a) ≥ 0`, `∑_y K = 1`.  Policies, total
response strategies and transcripts depend only on the shape.  A strictly
positive kernel field produces an ordinary `Tree` (`toTree`), whose policy,
strategy and leaf types are identified with the shape's by explicit
equivalences commuting with `run`, compatibility and leaf masses.  Every
`Tree` embeds (`ZTree.ofTree`) and `toTree ∘ ofTree = id`.
-/
import CausalSeed.ZeroGame

noncomputable section
open Classical Finset Filter
open scoped Topology
namespace CausalSpectrum.Zero

inductive Shape : Type
  | leaf : Shape
  | node (nA : ℕ) (hA : 0 < nA) (nY : Fin nA → ℕ) (hY : ∀ a, 0 < nY a)
      (child : (a : Fin nA) → Fin (nY a) → Shape) : Shape

namespace Shape

def Pol : Shape → Type
  | .leaf => PUnit
  | .node nA _ nY _ child => Fin nA × ((a : Fin nA) → (y : Fin (nY a)) → Pol (child a y))

def Str : Shape → Type
  | .leaf => PUnit
  | .node nA _ nY _ child =>
      ((a : Fin nA) → Fin (nY a)) × ((a : Fin nA) → (y : Fin (nY a)) → Str (child a y))

def Lf : Shape → Type
  | .leaf => PUnit
  | .node nA _ nY _ child => (a : Fin nA) ×' ((y : Fin (nY a)) ×' Lf (child a y))

def run : {S : Shape} → Str S → Pol S → Lf S
  | .leaf, _, _ => PUnit.unit
  | .node _ _ _ _ _, d, π => ⟨π.1, d.1 π.1, run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))⟩

def compat : {S : Shape} → Lf S → Pol S → Prop
  | .leaf, _, _ => True
  | .node _ _ _ _ _, ⟨a, y, ℓ⟩, π => a = π.1 ∧ compat ℓ (π.2 a y)

theorem run_compat : ∀ {S : Shape} (d : Str S) (π : Pol S), compat (run d π) π := by
  intro S
  induction S with
  | leaf => intro d π; trivial
  | node nA hA nY hY child ih => intro d π; exact ⟨rfl, ih _ _ _ _⟩

instance polFintype : (S : Shape) → Fintype (Pol S)
  | .leaf => by unfold Pol; infer_instance
  | .node nA hA nY hY child => by
      letI := fun a y => polFintype (child a y); unfold Pol; infer_instance

instance strFintype : (S : Shape) → Fintype (Str S)
  | .leaf => by unfold Str; infer_instance
  | .node nA hA nY hY child => by
      letI := fun a y => strFintype (child a y); unfold Str; infer_instance

instance lfFintype : (S : Shape) → Fintype (Lf S)
  | .leaf => by unfold Lf; infer_instance
  | .node nA hA nY hY child => by
      letI := fun a y => lfFintype (child a y); unfold Lf; infer_instance

def defaultPol : (S : Shape) → Pol S
  | .leaf => PUnit.unit
  | .node _ hA _ _ child => (⟨0, hA⟩, fun a y => defaultPol (child a y))

instance (S : Shape) : Nonempty (Pol S) := ⟨defaultPol S⟩

/-- Kernel fields on a shape. -/
def KField : Shape → Type
  | .leaf => PUnit
  | .node nA _ nY _ child =>
      ((a : Fin nA) → Fin (nY a) → ℝ) × ((a : Fin nA) → (y : Fin (nY a)) → KField (child a y))

/-- Nonnegative kernels summing to one (zeros allowed). -/
def Valid : (S : Shape) → KField S → Prop
  | .leaf, _ => True
  | .node _ _ _ _ child, k =>
      (∀ a y, 0 ≤ k.1 a y) ∧ (∀ a, ∑ y, k.1 a y = 1) ∧ ∀ a y, Valid (child a y) (k.2 a y)

/-- Strictly positive kernels summing to one. -/
def PosValid : (S : Shape) → KField S → Prop
  | .leaf, _ => True
  | .node _ _ _ _ child, k =>
      (∀ a y, 0 < k.1 a y) ∧ (∀ a, ∑ y, k.1 a y = 1) ∧ ∀ a y, PosValid (child a y) (k.2 a y)

/-- Probability of a transcript (the product of the kernels along it; may be `0`). -/
def mass : {S : Shape} → KField S → Lf S → ℝ
  | .leaf, _, _ => 1
  | .node _ _ _ _ _, k, ⟨a, y, ℓ⟩ => k.1 a y * mass (k.2 a y) ℓ

theorem mass_nonneg : ∀ {S : Shape} {k : KField S}, Valid S k → ∀ ℓ, 0 ≤ mass k ℓ := by
  intro S
  induction S with
  | leaf => intro k _ ℓ; exact zero_le_one
  | node nA hA nY hY child ih =>
      intro k hk ℓ
      obtain ⟨a, y, ℓ⟩ := ℓ
      exact mul_nonneg (hk.1 a y) (ih a y (hk.2.2 a y) ℓ)

/-- The ordinary positive tree carried by a positive kernel field. -/
def toTree : (S : Shape) → (k : KField S) → PosValid S k → Tree
  | .leaf, _, _ => Tree.leaf
  | .node nA hA nY hY child, k, h =>
      Tree.node nA hA nY hY k.1 h.1 h.2.1 fun a y => toTree (child a y) (k.2 a y) (h.2.2 a y)

def polE : (S : Shape) → (k : KField S) → (h : PosValid S k) → Pol S ≃ Policy (toTree S k h)
  | .leaf, _, _ => Equiv.refl _
  | .node nA hA nY hY child, k, h =>
      Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun a => Equiv.piCongrRight fun y =>
        polE (child a y) (k.2 a y) (h.2.2 a y))

def strE : (S : Shape) → (k : KField S) → (h : PosValid S k) → Str S ≃ Strategy (toTree S k h)
  | .leaf, _, _ => Equiv.refl _
  | .node nA hA nY hY child, k, h =>
      Equiv.prodCongr (Equiv.refl _) (Equiv.piCongrRight fun a => Equiv.piCongrRight fun y =>
        strE (child a y) (k.2 a y) (h.2.2 a y))

def lfE : (S : Shape) → (k : KField S) → (h : PosValid S k) → Lf S ≃ Leaf (toTree S k h)
  | .leaf, _, _ => Equiv.refl _
  | .node nA hA nY hY child, k, h =>
      Equiv.psigmaCongrRight fun a => Equiv.psigmaCongrRight fun y =>
        lfE (child a y) (k.2 a y) (h.2.2 a y)

theorem run_E : ∀ (S : Shape) (k : KField S) (h : PosValid S k) (d : Str S) (π : Pol S),
    CausalSpectrum.run (strE S k h d) (polE S k h π) = lfE S k h (run d π) := by
  intro S
  induction S with
  | leaf => intro k h d π; rfl
  | node nA hA nY hY child ih =>
      intro k h d π
      show (⟨π.1, d.1 π.1, CausalSpectrum.run
          (strE (child π.1 (d.1 π.1)) (k.2 π.1 (d.1 π.1)) (h.2.2 _ _) (d.2 π.1 (d.1 π.1)))
          (polE (child π.1 (d.1 π.1)) (k.2 π.1 (d.1 π.1)) (h.2.2 _ _) (π.2 π.1 (d.1 π.1)))⟩ :
          Leaf (toTree _ k h)) =
        ⟨π.1, d.1 π.1, lfE (child π.1 (d.1 π.1)) (k.2 π.1 (d.1 π.1)) (h.2.2 _ _)
          (run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1)))⟩
      rw [ih]

theorem compat_E : ∀ (S : Shape) (k : KField S) (h : PosValid S k) (ℓ : Lf S) (π : Pol S),
    CompatiblePolicy (lfE S k h ℓ) (polE S k h π) ↔ compat ℓ π := by
  intro S
  induction S with
  | leaf => intro k h ℓ π; exact Iff.rfl
  | node nA hA nY hY child ih =>
      intro k h ℓ π
      obtain ⟨a, y, ℓ⟩ := ℓ
      obtain ⟨b, πs⟩ := π
      show a = b ∧ CompatiblePolicy (lfE (child a y) (k.2 a y) (h.2.2 a y) ℓ)
          (polE (child a y) (k.2 a y) (h.2.2 a y) (πs a y)) ↔ a = b ∧ compat ℓ (πs a y)
      rw [ih]

theorem mass_E : ∀ (S : Shape) (k : KField S) (h : PosValid S k) (ℓ : Lf S),
    leafMass (lfE S k h ℓ) = mass k ℓ := by
  intro S
  induction S with
  | leaf => intro k h ℓ; rfl
  | node nA hA nY hY child ih =>
      intro k h ℓ
      obtain ⟨a, y, ℓ⟩ := ℓ
      show k.1 a y * leafMass _ = k.1 a y * mass (k.2 a y) ℓ
      rw [ih]

/-! ### Mixing with the uniform kernel -/

def mix (ε : ℝ) : {S : Shape} → KField S → KField S
  | .leaf, k => k
  | .node _ _ nY _ _, k => (fun a y => (1 - ε) * k.1 a y + ε / nY a, fun a y => mix ε (k.2 a y))

theorem mix_posValid {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) :
    ∀ {S : Shape} {k : KField S}, Valid S k → PosValid S (mix ε k) := by
  intro S
  induction S with
  | leaf => intro k _; trivial
  | node nA hA nY hY child ih =>
      intro k hk
      refine ⟨fun a y => ?_, fun a => ?_, fun a y => ih a y (hk.2.2 a y)⟩
      · have := hk.1 a y
        have : (0:ℝ) < nY a := by exact_mod_cast hY a
        show 0 < (1 - ε) * k.1 a y + ε / nY a
        have : 0 ≤ (1 - ε) * k.1 a y := mul_nonneg (by linarith) (hk.1 a y)
        positivity
      · show ∑ y, ((1 - ε) * k.1 a y + ε / nY a) = 1
        have hn : (nY a : ℝ) ≠ 0 := by exact_mod_cast (hY a).ne'
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, hk.2.1 a, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp; ring

theorem mass_mix_continuous : ∀ {S : Shape} (k : KField S) (ℓ : Lf S),
    Continuous (fun ε : ℝ => mass (mix ε k) ℓ) := by
  intro S
  induction S with
  | leaf => intro k ℓ; exact continuous_const
  | node nA hA nY hY child ih =>
      intro k ℓ
      obtain ⟨a, y, ℓ⟩ := ℓ
      show Continuous fun ε : ℝ => ((1 - ε) * k.1 a y + ε / nY a) * mass (mix ε (k.2 a y)) ℓ
      exact (((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.div_const _)).mul (ih a y _ ℓ)

theorem mass_mix_zero : ∀ {S : Shape} (k : KField S) (ℓ : Lf S), mass (mix 0 k) ℓ = mass k ℓ := by
  intro S
  induction S with
  | leaf => intro k ℓ; rfl
  | node nA hA nY hY child ih =>
      intro k ℓ
      obtain ⟨a, y, ℓ⟩ := ℓ
      show ((1 - 0) * k.1 a y + 0 / nY a) * mass (mix 0 (k.2 a y)) ℓ = k.1 a y * mass (k.2 a y) ℓ
      rw [ih]; ring

theorem posValid_valid : ∀ {S : Shape} {k : KField S}, PosValid S k → Valid S k := by
  intro S
  induction S with
  | leaf => intro k _; trivial
  | node nA hA nY hY child ih =>
      intro k h
      exact ⟨fun a y => (h.1 a y).le, h.2.1, fun a y => ih a y (h.2.2 a y)⟩

/-! ### Positive trees embed -/

def shapeOf : Tree → Shape
  | .leaf => .leaf
  | .node nA hA nY hY _ _ _ child => .node nA hA nY hY fun a y => shapeOf (child a y)

def kernelOf : (T : Tree) → KField (shapeOf T)
  | .leaf => PUnit.unit
  | .node _ _ _ _ K _ _ child => (K, fun a y => kernelOf (child a y))

theorem kernelOf_posValid : ∀ T : Tree, PosValid (shapeOf T) (kernelOf T) := by
  intro T
  induction T with
  | leaf => trivial
  | node nA hA nY hY K Kpos Ksum child ih => exact ⟨Kpos, Ksum, ih⟩

theorem toTree_ofTree : ∀ T : Tree, toTree (shapeOf T) (kernelOf T) (kernelOf_posValid T) = T := by
  intro T
  induction T with
  | leaf => rfl
  | node nA hA nY hY K Kpos Ksum child ih =>
      show Tree.node nA hA nY hY K _ _ _ = _
      congr 1
      funext a y
      exact ih a y

end Shape

open Shape

/-- A finite controlled tree whose kernels may vanish; no branch is removed. -/
structure ZTree where
  shape : Shape
  K : KField shape
  valid : Valid shape K

namespace ZTree
variable (Z : ZTree)

abbrev Pol := Shape.Pol Z.shape
abbrev Str := Shape.Str Z.shape
abbrev Lf := Shape.Lf Z.shape
/-- `P_{K,π}(ℓ)` (for `ℓ` compatible with `π`). -/
def P : Z.Lf → ℝ := mass Z.K

/-- `F_K(t) = min_π ∑_{ℓ ∼ π, P(ℓ) ≥ 2^{-t}} P(ℓ)`. -/
def F (t : ℝ) : ℝ := Fenv (P := Z.Pol) Shape.compat Z.P t
/-- `L(K) = ∫_0^∞ (1 - F_K(t)) dt`, in bits. -/
def L : ℝ := Lenv (P := Z.Pol) Shape.compat Z.P

/-- The embedding of the ordinary positive trees. -/
def ofTree (T : Tree) : ZTree :=
  ⟨shapeOf T, kernelOf T, posValid_valid (kernelOf_posValid T)⟩

end ZTree

/-! ### The envelope mean of a positive tree is `L` -/

instance (T : Tree) : Nonempty (Policy T) := ⟨defaultPolicy T⟩

theorem dyadic_le_iff {w t : ℝ} (hw : 0 < w) : (2:ℝ) ^ (-t) ≤ w ↔ infoMass w ≤ t := by
  rw [← not_lt, weight_lt_dyadic_iff hw, not_lt]

/-- For an ordinary tree, the game envelope is `Fstar`, hence `Lenv = envelopeMean`. -/
theorem Lenv_tree (T : Tree) :
    Lenv (P := Policy T) (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf T => leafMass ℓ) =
      envelopeMean T := by
  rw [← integral_one_sub_Fstar]
  unfold Lenv
  congr 1; funext t; congr 1
  have hS : ∀ π, Sp (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf T => leafMass ℓ) π t =
      policyCDF T π t := by
    intro π
    rw [policyCDF, policySum_eq_finset]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    have := dyadic_le_iff (t := t) (leafMass_pos ℓ)
    by_cases hc : CompatiblePolicy ℓ π <;> by_cases hl : infoMass (leafMass ℓ) ≤ t <;>
      simp [hc, hl, this]
  unfold Fenv
  apply le_antisymm
  · unfold Fstar; rw [← hS]; exact Finset.inf'_le _ (Finset.mem_univ _)
  · exact Finset.le_inf' _ _ fun π _ => (hS π) ▸ Fstar_le T t π

/-- For a positive kernel field, `L` of the shape game equals `envelopeMean (toTree …)`. -/
theorem Lenv_shape_eq (S : Shape) (k : KField S) (h : PosValid S k) :
    Lenv (P := Pol S) compat (mass k) = envelopeMean (toTree S k h) := by
  rw [← Lenv_tree, Lenv_transport (polE S k h) (lfE S k h) (compat_E S k h)]
  congr 1; funext ℓ; exact (mass_E S k h ℓ).symm

/-- **Agreement in the positive case.** `L(ofTree T) = envelopeMean T` (bits). -/
theorem ZTree.L_ofTree (T : Tree) : (ZTree.ofTree T).L = envelopeMean T := by
  have := Lenv_shape_eq (shapeOf T) (kernelOf T) (kernelOf_posValid T)
  rw [toTree_ofTree] at this
  exact this

end CausalSpectrum.Zero

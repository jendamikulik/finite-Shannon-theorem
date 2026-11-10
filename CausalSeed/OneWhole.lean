/-
One whole for every playback.

A finite tree carries, at each full history and each action, a prescribed
answer kernel. Draw those cells independently. The table is one finite seed.
Reading the cell of the history actually reached is a deterministic decoder,
and the decoder does not depend on which playback is running.

Proved, with no sorry:

* two playbacks that meet at the same history and choose the same action
  read the same cell of a fixed table;
* for every playback, the law of the transcript is the prescribed product
  of the kernels along the path actually taken;
* the table is assembled from the tree alone;
* two different wholes can share every single-groove law. One repeats the
  tone whenever the needle is set beside it. The other never does.

Not proved: that this table is the cheapest seed; that it is a physical
singularity; that knowing the law of each playback determines the whole.
The information clock is not this relation, and nothing here is spacetime.
-/

import CausalSeed.Penalty
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Prod

noncomputable section

open Classical Finset

namespace CausalSpectrum
namespace OneWhole

/-! ### Sums of independent cells -/

lemma sum_prod_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) :
    (∑ g : ∀ i, α i, ∏ i, f i (g i)) = ∏ i, ∑ a : α i, f i a := by
  simpa [Fintype.piFinset_univ] using
    (Finset.prod_univ_sum (fun i => (Finset.univ : Finset (α i))) f).symm

lemma ite_and_mul {p q : Prop} [Decidable p] [Decidable q] (x y : ℝ) :
    (if p ∧ q then x * y else 0) = (if p then x else 0) * (if q then y else 0) := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

lemma prod_erase_subtype {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (u : ι → ℝ) :
    (∏ j : {j // j ≠ i₀}, u j) = ∏ j ∈ Finset.univ.erase i₀, u j := by
  symm
  refine Finset.prod_subtype (Finset.univ.erase i₀) ?_ u
  intro j
  simp

/-- Fix a predicate on one coordinate. The other coordinates sum apart. -/
lemma sum_prod_pi_pred {ι : Type*} [Fintype ι] [DecidableEq ι] {α : ι → Type*}
    [∀ i, Fintype (α i)] (f : ∀ i, α i → ℝ) (i₀ : ι) (R : α i₀ → Prop)
    [DecidablePred R] :
    (∑ g : ∀ i, α i, if R (g i₀) then ∏ i, f i (g i) else 0) =
      (∑ b : α i₀, if R b then f i₀ b else 0) *
        ∏ i ∈ Finset.univ.erase i₀, ∑ a : α i, f i a := by
  let e := Equiv.piSplitAt i₀ α
  have htransport :
      (∑ g : ∀ i, α i, if R (g i₀) then ∏ i, f i (g i) else 0) =
        ∑ p : α i₀ × (∀ j : {j // j ≠ i₀}, α j),
          (if R ((e.symm p) i₀) then ∏ i, f i ((e.symm p) i) else 0) := by
    symm
    exact Fintype.sum_equiv e.symm
      (fun p => if R ((e.symm p) i₀) then ∏ i, f i ((e.symm p) i) else 0)
      (fun g => if R (g i₀) then ∏ i, f i (g i) else 0)
      (fun _ => rfl)
  rw [htransport]
  have hpt :
      ∀ p : α i₀ × (∀ j : {j // j ≠ i₀}, α j),
        (if R ((e.symm p) i₀) then ∏ i, f i ((e.symm p) i) else 0) =
          (if R p.1 then f i₀ p.1 else 0) *
            ∏ j : {j // j ≠ i₀}, f j (p.2 j) := by
    intro p
    have hi : (e.symm p) i₀ = p.1 := by
      simp [e, Equiv.piSplitAt_symm_apply]
    by_cases hR : R p.1
    · simp only [hi, hR, ite_true]
      rw [← Finset.mul_prod_erase (Finset.univ : Finset ι)
        (fun i => f i ((e.symm p) i)) (Finset.mem_univ i₀)]
      rw [hi]
      refine congrArg (fun t => f i₀ p.1 * t) ?_
      rw [← prod_erase_subtype i₀ (fun x => f x ((e.symm p) x))]
      refine congrArg (fun u : {j // j ≠ i₀} → ℝ => ∏ j, u j) ?_
      funext j
      have hne : (j : ι) ≠ i₀ := j.2
      simp [e, Equiv.piSplitAt_symm_apply, hne]
    · have hnot : ¬ R ((e.symm p) i₀) := by simpa [hi] using hR
      simp [hnot, hR]
  simp_rw [hpt]
  rw [Fintype.sum_prod_type]
  have hfactor :
      (∑ b : α i₀, ∑ rest : ∀ j : {j // j ≠ i₀}, α j,
          (if R b then f i₀ b else 0) *
            ∏ j : {j // j ≠ i₀}, f j (rest j)) =
        (∑ b : α i₀, if R b then f i₀ b else 0) *
          ∑ rest : ∀ j : {j // j ≠ i₀}, α j,
            ∏ j : {j // j ≠ i₀}, f j (rest j) := by
    simp_rw [← Finset.mul_sum]
    rw [Finset.sum_mul]
  rw [hfactor]
  have hrest :
      (∑ rest : ∀ j : {j // j ≠ i₀}, α (j : ι),
          ∏ j : {j // j ≠ i₀}, f (j : ι) (rest j)) =
        ∏ j : {j // j ≠ i₀}, ∑ a : α (j : ι), f (j : ι) a :=
    sum_prod_pi (fun (j : {j // j ≠ i₀}) (a : α (j : ι)) => f (j : ι) a)
  have herase :
      (∏ j : {j // j ≠ i₀}, ∑ a : α (j : ι), f (j : ι) a) =
        ∏ i ∈ Finset.univ.erase i₀, ∑ a, f i a :=
    prod_erase_subtype i₀ (fun i => ∑ a, f i a)
  rw [hrest, herase]

/-! ### The table does not ask which playback will run -/

def tableMass : {T : Tree} → Strategy T → ℝ
  | .leaf, _ => 1
  | .node _ _ _ _ K _ _ _, d =>
      (∏ a, K a (d.1 a)) * (∏ a, ∏ y, tableMass (d.2 a y))

theorem tableMass_nonneg : ∀ {T : Tree} (d : Strategy T), 0 ≤ tableMass d
  | .leaf, _ => by simp [tableMass]
  | .node _ _ _ _ K Kpos _ _, d => by
      unfold tableMass
      refine mul_nonneg (Finset.prod_nonneg fun a _ => (Kpos a (d.1 a)).le)
        (Finset.prod_nonneg fun a _ =>
          Finset.prod_nonneg fun y _ => tableMass_nonneg (d.2 a y))

theorem tableMass_total : ∀ T : Tree, ∑ d : Strategy T, tableMass d = 1
  | .leaf => by
      change (∑ _ : PUnit, (1 : ℝ)) = 1
      simp
  | .node nA hA nY hY K Kpos Ksum child => by
      have hchild : ∀ a y, ∑ s : Strategy (child a y), tableMass s = 1 :=
        fun a y => tableMass_total (child a y)
      unfold tableMass
      let e : Strategy (.node nA hA nY hY K Kpos Ksum child) ≃
          ((a : Fin nA) → Fin (nY a)) ×
            ((a : Fin nA) → (y : Fin (nY a)) → Strategy (child a y)) :=
        Equiv.refl _
      rw [Fintype.sum_equiv e
        (fun d => (∏ a, K a (d.1 a)) * (∏ a, ∏ y, tableMass (d.2 a y)))
        (fun p => (∏ a, K a (p.1 a)) * (∏ a, ∏ y, tableMass (p.2 a y)))
        (fun _ => rfl)]
      refine Eq.trans (Fintype.sum_prod_type'
        (fun (ans : (a : Fin nA) → Fin (nY a))
            (cont : (a : Fin nA) → (y : Fin (nY a)) → Strategy (child a y)) =>
          (∏ a, K a (ans a)) * (∏ a, ∏ y, tableMass (cont a y)))) ?_
      rw [← Fintype.sum_mul_sum]
      have hans :
          (∑ ans : (a : Fin nA) → Fin (nY a), ∏ a, K a (ans a)) = 1 := by
        rw [sum_prod_pi (fun a yy => K a yy)]
        simp_rw [Ksum]
        exact Finset.prod_eq_one (fun _ _ => rfl)
      have hcont :
          (∑ cont : (a : Fin nA) → (y : Fin (nY a)) → Strategy (child a y),
              ∏ a, ∏ y, tableMass (cont a y)) = 1 := by
        rw [sum_prod_pi (fun a (g : (y : Fin (nY a)) → Strategy (child a y)) =>
          ∏ y, tableMass (g y))]
        refine Finset.prod_eq_one fun a _ => ?_
        rw [sum_prod_pi (fun y (s : Strategy (child a y)) => tableMass s)]
        rw [Finset.prod_congr rfl (fun y _ => hchild a y)]
        simp
      rw [hans, hcont]
      simp

theorem cell_heq {nA : ℕ} {nY : Fin nA → ℕ} {a b : Fin nA}
    (h : a = b) (ans : (c : Fin nA) → Fin (nY c)) : HEq (ans a) (ans b) := by
  subst h
  rfl

/-- Same history, same action, same cell. The playback that was not taken
does not get a different answer out of the same table. -/
theorem same_next
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (d : Strategy (.node nA hA nY hY K Kpos Ksum child))
    (π ρ : Policy (.node nA hA nY hY K Kpos Ksum child))
    (hact : π.1 = ρ.1) :
    HEq (d.1 π.1) (d.1 ρ.1) :=
  cell_heq hact d.1

/-- For every playback, the table reproduces the prescribed law.
An unread cell is still drawn from its own kernel: choosing the address
from what has already been read does not change that cell. -/
theorem playback_law : ∀ (T : Tree) (π : Policy T) (ℓ : Leaf T),
    (∑ d : Strategy T, if run d π = ℓ then tableMass d else 0) =
      if CompatiblePolicy ℓ π then leafMass ℓ else 0
  | .leaf, π, ℓ => by
      cases ℓ
      cases π
      let : Unique (Strategy Tree.leaf) := by
        unfold Strategy
        infer_instance
      simp [run, tableMass, leafMass, CompatiblePolicy]
      exact ite_eq_left rfl
  | .node nA hA nY hY K Kpos Ksum child, π, ℓ => by
      have ih := fun a y π ℓ => playback_law (child a y) π ℓ
      by_cases hcompat : CompatiblePolicy ℓ π
      · have hcompat0 := hcompat
        rcases ℓ with ⟨a, y, rest⟩
        rcases hcompat with ⟨ha, hcrest⟩
        subst ha
        have run_form (d : Strategy (.node nA hA nY hY K Kpos Ksum child)) :
            run d π =
              ⟨π.1, d.1 π.1, run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))⟩ :=
          rfl
        have hrun : ∀ d : Strategy (.node nA hA nY hY K Kpos Ksum child),
            (run d π = ⟨π.1, y, rest⟩) ↔
              d.1 π.1 = y ∧ run (d.2 π.1 y) (π.2 π.1 y) = rest := by
          intro d
          constructor
          · intro h
            rw [run_form] at h
            obtain ⟨_, hpair⟩ := (PSigma.mk.inj_iff).mp h
            obtain ⟨hy, hrest⟩ := (PSigma.mk.inj_iff).mp (eq_of_heq hpair)
            have hy' : y = d.1 π.1 := hy.symm
            subst hy'
            exact ⟨rfl, eq_of_heq hrest⟩
          · rintro ⟨rfl, hrest⟩
            rw [run_form]
            exact congrArg
              (fun t : Leaf (child π.1 (d.1 π.1)) =>
                (⟨π.1, d.1 π.1, t⟩ : Leaf (.node nA hA nY hY K Kpos Ksum child)))
              hrest
        have hsummand :
            ∀ d : Strategy (.node nA hA nY hY K Kpos Ksum child),
              (if run d π = ⟨π.1, y, rest⟩ then tableMass d else 0) =
                (if d.1 π.1 = y ∧ run (d.2 π.1 y) (π.2 π.1 y) = rest then
                  (∏ b, K b (d.1 b)) * (∏ b, ∏ z, tableMass (d.2 b z)) else 0) := by
          intro d
          exact ite_congr (propext (hrun d)) (fun _ => rfl) (fun _ => rfl)
        simp_rw [hsummand]
        let eStrat : Strategy (.node nA hA nY hY K Kpos Ksum child) ≃
            ((b : Fin nA) → Fin (nY b)) ×
              ((b : Fin nA) → (z : Fin (nY b)) → Strategy (child b z)) :=
          Equiv.refl _
        rw [Fintype.sum_equiv eStrat
          (fun d => if d.1 π.1 = y ∧ run (d.2 π.1 y) (π.2 π.1 y) = rest then
              (∏ b, K b (d.1 b)) * (∏ b, ∏ z, tableMass (d.2 b z)) else 0)
          (fun p => if p.1 π.1 = y ∧ run (p.2 π.1 y) (π.2 π.1 y) = rest then
              (∏ b, K b (p.1 b)) * (∏ b, ∏ z, tableMass (p.2 b z)) else 0)
          (fun _ => rfl)]
        rw [Fintype.sum_prod_type]
        simp_rw [ite_and_mul]
        rw [← Fintype.sum_mul_sum]
        have hans :
            (∑ ans : (b : Fin nA) → Fin (nY b),
                if ans π.1 = y then ∏ b, K b (ans b) else 0) = K π.1 y := by
          rw [sum_prod_pi_pred (fun b yy => K b yy) π.1 (fun yy => yy = y)]
          have hother : (∏ i ∈ Finset.univ.erase π.1, ∑ yy, K i yy) = 1 := by
            exact Finset.prod_eq_one fun _ _ => Ksum _
          rw [hother, mul_one]
          simp
        have htail :
            (∑ cont : (b : Fin nA) → (z : Fin (nY b)) → Strategy (child b z),
                if run (cont π.1 y) (π.2 π.1 y) = rest
                  then ∏ b, ∏ z, tableMass (cont b z) else 0) =
              if CompatiblePolicy rest (π.2 π.1 y) then leafMass rest else 0 := by
          rw [sum_prod_pi_pred
            (fun b (g : (z : Fin (nY b)) → Strategy (child b z)) => ∏ z, tableMass (g z))
            π.1 (fun g => run (g y) (π.2 π.1 y) = rest)]
          have hother :
              (∏ b ∈ Finset.univ.erase π.1,
                  ∑ g : (z : Fin (nY b)) → Strategy (child b z), ∏ z, tableMass (g z)) = 1 := by
            refine Finset.prod_eq_one fun b _ => ?_
            rw [sum_prod_pi (fun z s => tableMass s)]
            rw [Finset.prod_congr rfl (fun z _ => tableMass_total (child b z))]
            simp
          rw [hother, mul_one]
          rw [sum_prod_pi_pred (fun z s => tableMass s) y
            (fun s => run s (π.2 π.1 y) = rest)]
          have hother2 :
              (∏ z ∈ Finset.univ.erase y, ∑ s : Strategy (child π.1 z), tableMass s) = 1 := by
            exact Finset.prod_eq_one fun z _ => tableMass_total (child π.1 z)
          rw [hother2, mul_one]
          exact ih π.1 y (π.2 π.1 y) rest
        rw [hans, htail, ite_eq_left hcrest, ite_eq_left hcompat0]
        simp [leafMass]
      · rw [ite_eq_right hcompat]
        refine Finset.sum_eq_zero fun d _ => ?_
        have hne : run d π ≠ ℓ := by
          intro h
          exact hcompat (h ▸ run_compatible_policy d π)
        exact ite_eq_right hne

/-! ### The law of each groove does not determine the record -/

/-- The record that repeats. Mass `1/2` on each shared tone. -/
def Copy (p : Fin 2 × Fin 2) : ℝ :=
  if p.1 = p.2 then 1 / 2 else 0

/-- The record that never repeats. -/
def Flip (p : Fin 2 × Fin 2) : ℝ :=
  if p.1 ≠ p.2 then 1 / 2 else 0

theorem copy_left (b : Fin 2) : ∑ r : Fin 2, Copy (b, r) = 1 / 2 := by
  fin_cases b <;> simp [Copy]

theorem flip_left (b : Fin 2) : ∑ r : Fin 2, Flip (b, r) = 1 / 2 := by
  fin_cases b <;> simp [Flip, Fin.sum_univ_two]

theorem copy_right (r : Fin 2) : ∑ b : Fin 2, Copy (b, r) = 1 / 2 := by
  fin_cases r <;> simp [Copy]

theorem flip_right (r : Fin 2) : ∑ b : Fin 2, Flip (b, r) = 1 / 2 := by
  fin_cases r <;> simp [Flip, Fin.sum_univ_two]

theorem copy_total : ∑ p : Fin 2 × Fin 2, Copy p = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [copy_left]
  rw [Fin.sum_univ_two]
  norm_num

theorem flip_total : ∑ p : Fin 2 × Fin 2, Flip p = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [flip_left]
  rw [Fin.sum_univ_two]
  norm_num

/-- On the first record the tone beside the needle is the same one. -/
theorem copy_repeats (b r : Fin 2) (h : Copy (b, r) ≠ 0) : r = b := by
  by_contra hne
  exact h (by simp [Copy, Ne.symm hne])

/-- On the second record it never is. -/
theorem flip_never (b r : Fin 2) (h : Flip (b, r) ≠ 0) : r ≠ b := by
  intro heq
  simp [Flip, heq] at h

theorem marginals_agree (b : Fin 2) :
    (∑ r, Copy (b, r)) = ∑ r, Flip (b, r) := by
  rw [copy_left, flip_left]

theorem records_differ : Copy ≠ Flip := by
  intro h
  have := congrFun h (0, 0)
  simp [Copy, Flip] at this

end OneWhole
end CausalSpectrum

end

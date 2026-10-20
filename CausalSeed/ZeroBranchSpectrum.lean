/-
The spectrum is preserved by positive-support reduction.

The horizon-`n` unrolling `T.Zt n` of a nonnegative history-dependent tree keeps every branch,
including the zero-probability ones. Its lower envelope `F*` and envelope mean `L` coincide with
those of the positive tree `trunc T⁺ n []`.
-/
import CausalSeed.ZeroBranchSeed
import CausalSeed.ZeroKernel

noncomputable section
open Classical Finset

namespace CausalSpectrum.ZeroBranch
open Zero Zero.Shape

namespace NNTree
variable (T : NNTree)

/-! ### The unrolled finite trees with all branches -/

def shapeN : ℕ → List (ℕ × ℕ) → Shape
  | 0, _ => .leaf
  | n + 1, q => .node (T.nA q) (T.hA q) (T.nY q) (T.hY q) fun a y => shapeN n (q ++ [(a.val, y.val)])

def kfN : (n : ℕ) → (q : List (ℕ × ℕ)) → KField (T.shapeN n q)
  | 0, _ => PUnit.unit
  | n + 1, q => (T.kern q, fun a y => kfN n (q ++ [(a.val, y.val)]))

theorem validN : ∀ n q, Valid (T.shapeN n q) (T.kfN n q)
  | 0, _ => trivial
  | n + 1, q => ⟨T.knn q, T.ksum q, fun a y => validN n _⟩

/-- The horizon-`n` tree `T_n`, every zero-probability branch retained. -/
def Zt (n : ℕ) : ZTree := ⟨T.shapeN n [], T.kfN n [], T.validN n []⟩

/-! ### Policy maps between `T_n` and `T⁺_n` -/

theorem liftStep (p : List (ℕ × ℕ)) (a : Fin (T.nA (T.lift p))) (i : Fin (T.supp (T.lift p) a).card) :
    T.lift p ++ [(a.val, (T.emb (T.lift p) a i).1.val)] = T.lift (p ++ [(a.val, i.val)]) := by
  rw [lift_snoc]
  simp only [step, List.cons.injEq, and_true, List.append_cancel_left_eq, Prod.mk.injEq, true_and]
  rw [T.stepY_lt a.isLt i.isLt]

theorem liftStep' (p : List (ℕ × ℕ)) (a : Fin (T.nA (T.lift p))) (y : Fin (T.nY (T.lift p) a))
    (hy : y ∈ T.supp (T.lift p) a) :
    T.lift (p ++ [(a.val, ((T.emb (T.lift p) a).symm ⟨y, hy⟩).val)]) =
      T.lift p ++ [(a.val, y.val)] := by
  rw [← T.liftStep, OrderIso.apply_symm_apply]

def castP {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (π : Pol (T.shapeN n q)) :
    Pol (T.shapeN n q') := e ▸ π

theorem Phi_cast {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (π : Pol (T.shapeN n q)) (c t : ℝ) :
    Phi (T.kfN n q') (T.castP e π) c t = Phi (T.kfN n q) π c t := by
  subst e; rfl

def restrictN : (n : ℕ) → (p : List (ℕ × ℕ)) → Pol (T.shapeN n (T.lift p)) →
    Pol (shapeOf (trunc T.plus n p))
  | 0, _, _ => PUnit.unit
  | n + 1, p, π => (π.1, fun a i =>
      restrictN n (p ++ [(a.val, i.val)]) (T.castP (T.liftStep p a i) (π.2 a (T.emb (T.lift p) a i).1)))

def extendN : (n : ℕ) → (p : List (ℕ × ℕ)) → Pol (shapeOf (trunc T.plus n p)) →
    Pol (T.shapeN n (T.lift p))
  | 0, _, _ => PUnit.unit
  | n + 1, p, π => (π.1, fun a y =>
      if hy : y ∈ T.supp (T.lift p) a then
        T.castP (T.liftStep' p a y hy) (extendN n (p ++ [(a.val, ((T.emb (T.lift p) a).symm ⟨y, hy⟩).val)])
          (π.2 a ((T.emb (T.lift p) a).symm ⟨y, hy⟩)))
      else defaultPol _)

theorem sum_emb_of (h : List (ℕ × ℕ)) (a : Fin (T.nA h)) (f : Fin (T.nY h a) → ℝ)
    (hf : ∀ y, T.kern h a y = 0 → f y = 0) :
    ∑ y, f y = ∑ i, f (T.emb h a i).1 := by
  rw [← sum_filter_add_sum_filter_not univ (fun y => 0 < T.kern h a y)]
  have h0 : ∑ y ∈ univ.filter (fun y => ¬ 0 < T.kern h a y), f y = 0 :=
    sum_eq_zero fun y hy => by
      simp only [mem_filter, mem_univ, true_and, not_lt] at hy
      exact hf y (le_antisymm hy (T.knn _ _ _))
  rw [h0, add_zero, ← Finset.sum_coe_sort (univ.filter fun y => 0 < T.kern h a y)]
  exact (Equiv.sum_comp (T.emb h a).toEquiv (fun y : T.supp h a => f y.1)).symm

theorem Phi_restrictN : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (π : Pol (T.shapeN n (T.lift p))) (c t : ℝ),
    0 ≤ c → Phi (T.kfN n (T.lift p)) π c t =
      Phi (kernelOf (trunc T.plus n p)) (T.restrictN n p π) c t
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, π, c, t, hc => by
      refine (Phi_node (T.kfN (n + 1) (T.lift p)) π c t).trans (Eq.trans ?_
        (Phi_node (kernelOf (trunc T.plus (n + 1) p)) (T.restrictN (n + 1) p π) c t).symm)
      show ∑ y, Phi (T.kfN n (T.lift p ++ [(π.1.val, y.val)])) (π.2 π.1 y)
          (c * T.kern (T.lift p) π.1 y) t =
        ∑ i, Phi (kernelOf (trunc T.plus n (p ++ [(π.1.val, i.val)])))
          (T.restrictN n (p ++ [(π.1.val, i.val)])
            (T.castP (T.liftStep p π.1 i) (π.2 π.1 (T.emb (T.lift p) π.1 i).1)))
          (c * T.kern (T.lift p) π.1 (T.emb (T.lift p) π.1 i).1) t
      rw [T.sum_emb_of _ π.1 _ (fun y hy => by rw [hy, mul_zero, Phi_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Phi_restrictN n _ _ _ t (mul_nonneg hc (T.knn _ _ _)), T.Phi_cast]

theorem Phi_extendN : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (π : Pol (shapeOf (trunc T.plus n p))) (c t : ℝ),
    0 ≤ c → Phi (kernelOf (trunc T.plus n p)) π c t =
      Phi (T.kfN n (T.lift p)) (T.extendN n p π) c t
  | 0, _, _, _, _, _ => rfl
  | n + 1, p, π, c, t, hc => by
      refine (Phi_node (kernelOf (trunc T.plus (n + 1) p)) π c t).trans (Eq.trans ?_
        (Phi_node (T.kfN (n + 1) (T.lift p)) (T.extendN (n + 1) p π) c t).symm)
      show ∑ i, Phi (kernelOf (trunc T.plus n (p ++ [(π.1.val, i.val)]))) (π.2 π.1 i)
          (c * T.kern (T.lift p) π.1 (T.emb (T.lift p) π.1 i).1) t =
        ∑ y, Phi (T.kfN n (T.lift p ++ [(π.1.val, y.val)])) ((T.extendN (n + 1) p π).2 π.1 y)
          (c * T.kern (T.lift p) π.1 y) t
      rw [T.sum_emb_of _ π.1 _ (fun y hy => by rw [hy, mul_zero, Phi_zero])]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hi : (T.emb (T.lift p) π.1 i).1 ∈ T.supp (T.lift p) π.1 := (T.emb (T.lift p) π.1 i).2
      show _ = Phi _ (if h : (T.emb (T.lift p) π.1 i).1 ∈ T.supp (T.lift p) π.1 then
        T.castP (T.liftStep' p π.1 _ h) (T.extendN n (p ++ [(π.1.val,
          ((T.emb (T.lift p) π.1).symm ⟨_, h⟩).val)])
          (π.2 π.1 ((T.emb (T.lift p) π.1).symm ⟨_, h⟩))) else defaultPol _) _ t
      rw [dif_pos hi, T.Phi_cast]
      have key : ∀ j (_ : j = i), Phi (kernelOf (trunc T.plus n (p ++ [(π.1.val, i.val)])))
          (π.2 π.1 i) (c * T.kern (T.lift p) π.1 (T.emb (T.lift p) π.1 i).1) t =
          Phi (T.kfN n (T.lift (p ++ [(π.1.val, j.val)]))) (T.extendN n (p ++ [(π.1.val, j.val)])
            (π.2 π.1 j)) (c * T.kern (T.lift p) π.1 (T.emb (T.lift p) π.1 i).1) t := by
        rintro j rfl
        exact Phi_extendN n _ _ _ t (mul_nonneg hc (T.knn _ _ _))
      exact key _ (by simp only [Subtype.coe_eta]; exact (T.emb (T.lift p) π.1).symm_apply_apply i)

/-! ### Equality of envelopes -/

theorem F_Zt_ofTree (n : ℕ) (t : ℝ) : (T.Zt n).F t = (ZTree.ofTree (trunc T.plus n [])).F t := by
  unfold ZTree.F Fenv ZTree.P
  apply le_antisymm
  · refine Finset.le_inf' _ _ fun πr _ => ?_
    refine (Finset.inf'_le _ (Finset.mem_univ (T.extendN n [] πr))).trans_eq ?_
    show Sp compat (mass (T.kfN n [])) (T.extendN n [] πr) t =
      Sp compat (mass (kernelOf (trunc T.plus n []))) πr t
    exact (NNKernel.Sp_eq_Phi (T.kfN n []) (T.extendN n [] πr) t).trans ((T.Phi_extendN n [] πr 1 t
      zero_le_one).symm.trans (NNKernel.Sp_eq_Phi (kernelOf (trunc T.plus n [])) πr t).symm)
  · refine Finset.le_inf' _ _ fun π _ => ?_
    refine (Finset.inf'_le _ (Finset.mem_univ (T.restrictN n [] π))).trans_eq ?_
    show Sp compat (mass (kernelOf (trunc T.plus n []))) (T.restrictN n [] π) t =
      Sp compat (mass (T.kfN n [])) π t
    exact (NNKernel.Sp_eq_Phi (kernelOf (trunc T.plus n [])) (T.restrictN n [] π) t).trans
      ((T.Phi_restrictN n [] π 1 t zero_le_one).symm.trans (NNKernel.Sp_eq_Phi (T.kfN n []) π t).symm)

end NNTree

/-- For an ordinary tree the game envelope is `F*`. -/
theorem Fenv_tree (T : Tree) (t : ℝ) :
    Fenv (P := Policy T) (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf T => leafMass ℓ) t =
      Fstar T t := by
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

theorem Fenv_shape_eq (S : Shape) (k : KField S) (h : PosValid S k) (t : ℝ) :
    Fenv (P := Pol S) compat (mass k) t = Fstar (toTree S k h) t := by
  rw [← Fenv_tree, Fenv_transport (polE S k h) (lfE S k h) (compat_E S k h)]
  congr 1; funext ℓ; exact (mass_E S k h ℓ).symm

theorem ZTree.F_ofTree (T : Tree) (t : ℝ) : (ZTree.ofTree T).F t = Fstar T t := by
  have := Fenv_shape_eq (shapeOf T) (kernelOf T) (kernelOf_posValid T) t
  rw [toTree_ofTree] at this
  exact this

namespace NNTree
variable (T : NNTree)

/-- **Spectrum equality, envelope form:** `F*_{T_n}(t) = F*_{T⁺_n}(t)`. -/
theorem F_Zt (n : ℕ) (t : ℝ) : (T.Zt n).F t = Fstar (trunc T.plus n []) t := by
  rw [F_Zt_ofTree, ZTree.F_ofTree]

/-- **Spectrum equality, mean form:** `L(T_n) = L(T⁺_n)` (bits). -/
theorem L_Zt (n : ℕ) : (T.Zt n).L = envelopeMean (trunc T.plus n []) := by
  rw [← ZTree.L_ofTree]
  unfold ZTree.L Lenv
  congr 1
  funext t
  exact congrArg (1 - ·) (T.F_Zt_ofTree n t)

end NNTree
end CausalSpectrum.ZeroBranch

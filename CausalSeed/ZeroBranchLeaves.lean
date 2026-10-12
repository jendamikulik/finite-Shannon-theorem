/-
Transcripts of the trees with zero branches and of their positive reductions.

Policies of `T_n` restrict to policies of `T⁺_n` and policies of `T⁺_n` extend to `T_n`;
transcripts of `T⁺_n` lift injectively to transcripts of `T_n` with the same mass and
compatibility, and every compatible transcript of positive mass is such a lift.
-/
import CausalSeed.ZeroBranchSpectrum

noncomputable section
open Classical Finset

namespace CausalSpectrum.ZeroBranch
open Zero Zero.Shape

namespace NNTree
variable (T : NNTree)

def castL {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (ℓ : Lf (T.shapeN n q)) :
    Lf (T.shapeN n q') := e ▸ ℓ

theorem castL_castL {n : ℕ} {q1 q2 q3 : List (ℕ × ℕ)} (e1 : q1 = q2) (e2 : q2 = q3)
    (ℓ : Lf (T.shapeN n q1)) : T.castL e2 (T.castL e1 ℓ) = T.castL (e1.trans e2) ℓ := by
  subst e1; subst e2; rfl

theorem castL_self {n : ℕ} {q : List (ℕ × ℕ)} (e : q = q) (ℓ : Lf (T.shapeN n q)) :
    T.castL e ℓ = ℓ := rfl

theorem castL_injective {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') :
    Function.Injective (T.castL (n := n) e) := by
  subst e; exact fun _ _ h => h

theorem mass_castL {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (ℓ : Lf (T.shapeN n q)) :
    mass (T.kfN n q') (T.castL e ℓ) = mass (T.kfN n q) ℓ := by
  subst e; rfl

theorem compat_cast {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (ℓ : Lf (T.shapeN n q))
    (π : Pol (T.shapeN n q)) : compat (T.castL e ℓ) (T.castP e π) ↔ compat ℓ π := by
  subst e; rfl

theorem castP_cancel {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (π : Pol (T.shapeN n q)) :
    T.castP e.symm (T.castP e π) = π := by
  subst e; rfl

theorem castP_symm {n : ℕ} {q q' : List (ℕ × ℕ)} (e : q = q') (π : Pol (T.shapeN n q')) :
    T.castP e (T.castP e.symm π) = π := by
  subst e; rfl

/-! ### Policy and transcript maps -/

def restrictP : (n : ℕ) → (p : List (ℕ × ℕ)) → Pol (T.shapeN n (T.lift p)) →
    Policy (trunc T.plus n p)
  | 0, _, _ => PUnit.unit
  | n + 1, p, π => (π.1, fun a i =>
      restrictP n (p ++ [(a.val, i.val)]) (T.castP (T.liftStep p a i) (π.2 a (T.emb (T.lift p) a i).1)))

def extendP : (n : ℕ) → (p : List (ℕ × ℕ)) → Policy (trunc T.plus n p) →
    Pol (T.shapeN n (T.lift p))
  | 0, _, _ => PUnit.unit
  | n + 1, p, π => (π.1, fun a y =>
      if hy : y ∈ T.supp (T.lift p) a then
        T.castP (T.liftStep' p a y hy) (extendP n (p ++ [(a.val, ((T.emb (T.lift p) a).symm ⟨y, hy⟩).val)])
          (π.2 a ((T.emb (T.lift p) a).symm ⟨y, hy⟩)))
      else defaultPol _)

def liftL : (n : ℕ) → (p : List (ℕ × ℕ)) → Leaf (trunc T.plus n p) → Lf (T.shapeN n (T.lift p))
  | 0, _, _ => PUnit.unit
  | n + 1, p, ⟨a, i, ℓ⟩ =>
      ⟨a, (T.emb (T.lift p) a i).1, T.castL (T.liftStep p a i).symm (liftL n (p ++ [(a.val, i.val)]) ℓ)⟩

theorem mass_liftL : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (ℓ : Leaf (trunc T.plus n p)),
    mass (T.kfN n (T.lift p)) (T.liftL n p ℓ) = leafMass ℓ
  | 0, _, _ => rfl
  | n + 1, p, ⟨a, i, ℓ⟩ => by
      show T.kern (T.lift p) a (T.emb (T.lift p) a i).1 * mass _ (T.castL _ _) =
        T.kern (T.lift p) a (T.emb (T.lift p) a i).1 * leafMass ℓ
      have := (T.mass_castL (T.liftStep p a i).symm (T.liftL n _ ℓ)).trans (mass_liftL n _ ℓ)
      exact congrArg (T.kern (T.lift p) a (T.emb (T.lift p) a i).1 * ·) this

theorem sigma_eq {n : ℕ} {q : List (ℕ × ℕ)} (a : Fin (T.nA q)) {y y' : Fin (T.nY q a)} (h : y' = y)
    (x : Lf (T.shapeN n (q ++ [(a.val, y'.val)]))) (z : Lf (T.shapeN n (q ++ [(a.val, y.val)])))
    (hx : T.castL (by rw [h]) x = z) :
    (⟨a, y', x⟩ : Lf (T.shapeN (n + 1) q)) = ⟨a, y, z⟩ := by
  subst h; rw [← hx]; rfl

theorem liftL_injective : ∀ (n : ℕ) (p : List (ℕ × ℕ)), Function.Injective (T.liftL n p)
  | 0, _, _, _, _ => rfl
  | n + 1, p, ⟨a, i, ℓ⟩, ⟨a', i', ℓ'⟩, h => by
      simp only [liftL] at h
      obtain ⟨rfl, h⟩ := PSigma.mk.inj_iff.1 h
      have h := eq_of_heq h
      obtain ⟨hy, h⟩ := PSigma.mk.inj_iff.1 h
      have hi : i = i' := (T.emb (T.lift p) a).injective (Subtype.ext hy)
      subst hi
      have h := T.castL_injective _ (eq_of_heq h)
      rw [liftL_injective n _ h]

theorem compat_liftL_extendP : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (ℓ : Leaf (trunc T.plus n p))
    (π : Policy (trunc T.plus n p)), CompatiblePolicy ℓ π → compat (T.liftL n p ℓ) (T.extendP n p π)
  | 0, _, _, _, _ => trivial
  | n + 1, p, ⟨a, i, ℓ⟩, π, ⟨ha, hc⟩ => by
      refine ⟨ha, ?_⟩
      have hi : (T.emb (T.lift p) a i).1 ∈ T.supp (T.lift p) a := (T.emb (T.lift p) a i).2
      show compat (T.castL _ (T.liftL n _ ℓ)) (if h : (T.emb (T.lift p) a i).1 ∈ T.supp (T.lift p) a then
        T.castP (T.liftStep' p a _ h) (T.extendP n (p ++ [(a.val,
          ((T.emb (T.lift p) a).symm ⟨_, h⟩).val)])
          (π.2 a ((T.emb (T.lift p) a).symm ⟨_, h⟩))) else defaultPol _)
      rw [dif_pos hi]
      have key : ∀ j (_ : j = i) (e : T.lift (p ++ [(a.val, j.val)]) =
          T.lift p ++ [(a.val, (T.emb (T.lift p) a i).1.val)]),
          compat (T.castL (T.liftStep p a i).symm (T.liftL n (p ++ [(a.val, i.val)]) ℓ))
            (T.castP e (T.extendP n (p ++ [(a.val, j.val)]) (π.2 a j))) := by
        rintro j rfl e
        exact (T.compat_cast _ _ _).2 (compat_liftL_extendP n _ ℓ _ hc)
      exact key _ (by simp only [Subtype.coe_eta]; exact (T.emb (T.lift p) a).symm_apply_apply i) _

theorem compat_liftL_restrictP : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (ℓ : Leaf (trunc T.plus n p))
    (π : Pol (T.shapeN n (T.lift p))),
    CompatiblePolicy ℓ (T.restrictP n p π) → compat (T.liftL n p ℓ) π
  | 0, _, _, _, _ => trivial
  | n + 1, p, ⟨a, i, ℓ⟩, π, ⟨ha, hc⟩ => by
      refine ⟨ha, ?_⟩
      have := compat_liftL_restrictP n _ ℓ _ hc
      show compat (T.castL (T.liftStep p a i).symm _) (π.2 a (T.emb (T.lift p) a i).1)
      rw [← T.castP_symm (T.liftStep p a i).symm (π.2 a (T.emb (T.lift p) a i).1), T.compat_cast]
      exact this

theorem supp_of_mass {n : ℕ} {q : List (ℕ × ℕ)} {a : Fin (T.nA q)} {y : Fin (T.nY q a)}
    {ℓ : Lf (T.shapeN n (q ++ [(a.val, y.val)]))}
    (hm : mass (T.kfN (n + 1) q) (⟨a, y, ℓ⟩ : Lf (T.shapeN (n + 1) q)) ≠ 0) :
    y ∈ T.supp q a ∧ mass (T.kfN n (q ++ [(a.val, y.val)])) ℓ ≠ 0 := by
  change T.kern q a y * mass _ ℓ ≠ 0 at hm
  refine ⟨?_, right_ne_zero_of_mul hm⟩
  simp only [supp, mem_filter, mem_univ, true_and]
  exact lt_of_le_of_ne (T.knn _ _ _) (Ne.symm (left_ne_zero_of_mul hm))

/-- Every transcript of positive mass compatible with an extended policy is a lifted transcript. -/
theorem surj_extendP : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (ℓ : Lf (T.shapeN n (T.lift p)))
    (π : Policy (trunc T.plus n p)), compat ℓ (T.extendP n p π) →
    mass (T.kfN n (T.lift p)) ℓ ≠ 0 → ∃ ℓp, CompatiblePolicy ℓp π ∧ T.liftL n p ℓp = ℓ
  | 0, _, ℓ, _, _, _ => ⟨PUnit.unit, trivial, rfl⟩
  | n + 1, p, ⟨a, y, ℓ⟩, π, ⟨ha, hc⟩, hm => by
      obtain ⟨hy, hm'⟩ := T.supp_of_mass hm
      set i := (T.emb (T.lift p) a).symm ⟨y, hy⟩
      have hc' : compat ℓ ((T.extendP (n + 1) p π).2 a y) := hc
      have hext : (T.extendP (n + 1) p π).2 a y =
          T.castP (T.liftStep' p a y hy) (T.extendP n (p ++ [(a.val, i.val)]) (π.2 a i)) := by
        show (if h : y ∈ T.supp (T.lift p) a then _ else _) = _
        rw [dif_pos hy]
      rw [hext] at hc'
      set ℓ'' := T.castL (T.liftStep' p a y hy).symm ℓ
      have hc'' : compat ℓ'' (T.extendP n (p ++ [(a.val, i.val)]) (π.2 a i)) := by
        have := (T.compat_cast (T.liftStep' p a y hy).symm ℓ
          (T.castP (T.liftStep' p a y hy) (T.extendP n (p ++ [(a.val, i.val)]) (π.2 a i)))).2 hc'
        rwa [T.castP_cancel] at this
      have hm'' : mass (T.kfN n (T.lift (p ++ [(a.val, i.val)]))) ℓ'' ≠ 0 := by
        rw [mass_castL]; exact hm'
      obtain ⟨ℓp, hcp, hlp⟩ := surj_extendP n _ ℓ'' _ hc'' hm''
      refine ⟨⟨a, i, ℓp⟩, ⟨ha, hcp⟩, ?_⟩
      show (⟨a, (T.emb (T.lift p) a i).1, T.castL (T.liftStep p a i).symm (T.liftL n _ ℓp)⟩ :
        Lf (T.shapeN (n + 1) (T.lift p))) = ⟨a, y, ℓ⟩
      refine T.sigma_eq a (by simp [i]) _ _ ?_
      rw [hlp, T.castL_castL, T.castL_castL]
      rfl

theorem surj_restrictP : ∀ (n : ℕ) (p : List (ℕ × ℕ)) (ℓ : Lf (T.shapeN n (T.lift p)))
    (π : Pol (T.shapeN n (T.lift p))), compat ℓ π →
    mass (T.kfN n (T.lift p)) ℓ ≠ 0 → ∃ ℓp, CompatiblePolicy ℓp (T.restrictP n p π) ∧ T.liftL n p ℓp = ℓ
  | 0, _, ℓ, _, _, _ => ⟨PUnit.unit, trivial, rfl⟩
  | n + 1, p, ⟨a, y, ℓ⟩, π, ⟨ha, hc⟩, hm => by
      obtain ⟨hy, hm'⟩ := T.supp_of_mass hm
      set i := (T.emb (T.lift p) a).symm ⟨y, hy⟩
      set ℓ'' := T.castL (T.liftStep' p a y hy).symm ℓ
      have hm'' : mass (T.kfN n (T.lift (p ++ [(a.val, i.val)]))) ℓ'' ≠ 0 := by
        rw [mass_castL]; exact hm'
      have key : ∀ y' (_ : y' = y) (e : T.lift p ++ [(a.val, y'.val)] = T.lift (p ++ [(a.val, i.val)])),
          compat ℓ'' (T.castP e (π.2 a y')) := by
        rintro y' rfl e
        have := (T.compat_cast e.symm.symm ℓ (π.2 a y')).2 hc
        exact this
      have hc'' := key (T.emb (T.lift p) a i).1 (by simp [i]) (T.liftStep p a i)
      obtain ⟨ℓp, hcp, hlp⟩ := surj_restrictP n _ ℓ'' _ hc'' hm''
      refine ⟨⟨a, i, ℓp⟩, ⟨ha, hcp⟩, ?_⟩
      show (⟨a, (T.emb (T.lift p) a i).1, T.castL (T.liftStep p a i).symm (T.liftL n _ ℓp)⟩ :
        Lf (T.shapeN (n + 1) (T.lift p))) = ⟨a, y, ℓ⟩
      refine T.sigma_eq a (by simp [i]) _ _ ?_
      rw [hlp, T.castL_castL, T.castL_castL]
      rfl

end NNTree
end CausalSpectrum.ZeroBranch

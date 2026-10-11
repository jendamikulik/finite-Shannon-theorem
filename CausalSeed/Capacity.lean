/-
Path mass, limiting strategies, and cylinder mass on a locally finite tree.

`diagMass = atomQ` is proved in `Atomic.lean`. Here each finite greedy strategy
is extended to the infinite tree, and a subsequence of those codes converges
at every node (`capStrat`). Along any raw history `h`, the total weight of the
limiting strategies that reproduce `h` is at most the kernel mass of `h`
(`cylMass_le_path`). The root cylinder has mass `atomQ`. The difference
`resMass h = pathMass h - cylMass h` is nonnegative and is conserved by every
action (`resMass_split`).

`resCyl h` is the product of one-step ratios along `h`. Where the residual at
`h` is positive, the ratio of a step `p` is `resMass (h ++ [p]) / resMass h`.
Where that residual vanishes, the ratio is the original kernel (`kernRaw`),
so every action stays a probability kernel (`resRatioStep_sum`). The weighted
identity `resMass h = resMass [] * resCyl h` (`resMass_eq_root_mul`) does not
use the value of a ratio at a history of residual zero, and
`cylMass h + resMass [] * resCyl h = pathMass h` (`exact_split`) is unchanged.
`resCyl` is the cylinder function of that kernel product. The atomic measure
`atomMeasure` is the sum of weighted Diracs of the limiting strategies.
Its total mass and its cylinder masses are proved in
`CausalSeed/MeasureCompletion.lean`, which also builds the residual
product and the exact mixture. Ordinary and causal atomic capacity, and
the projective entropy identity for ranked seeds, are in
`AtomicCapacity.lean` and `EntropyLimit.lean`.

Not proved here: the information-spectrum limit of `atomQ`, the comparison
of that entropy with `L_∞`, and any identification of `G_*`. No publication
priority is claimed. Ordinary infinite-family concentration is prior work
and is not reproved.
-/
import CausalSeed.Atomic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.List
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Bases
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order
import Mathlib.Data.EReal.Basic
import CausalSeed.Penalty
import Mathlib.MeasureTheory.Measure.Sum
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.Data.ENNReal.Basic


noncomputable section
open Classical
open MeasureTheory
open Finset
namespace CausalSpectrum

set_option backward.isDefEq.respectTransparency false

noncomputable def pm (ι : ITree) (pref : List (ℕ × ℕ)) : List (ℕ × ℕ) → ℝ
  | [] => 1
  | p :: t =>
      if ha : p.1 < ι.nA pref then
        let a : Fin (ι.nA pref) := ⟨p.1, ha⟩
        if hy : p.2 < ι.nY pref a then
          ι.kern pref a ⟨p.2, hy⟩ * pm ι (pref ++ [p]) t
        else 0
      else 0

noncomputable def pathMass (ι : ITree) (h : List (ℕ × ℕ)) : ℝ :=
  pm ι [] h

theorem pm_nil (ι : ITree) (pref : List (ℕ × ℕ)) : pm ι pref [] = 1 := rfl

theorem pm_cons_act {ι : ITree} {pref : List (ℕ × ℕ)} {p : ℕ × ℕ} {t : List (ℕ × ℕ)}
    (ha : ¬ p.1 < ι.nA pref) : pm ι pref (p :: t) = 0 := by
  simp [pm, ha]

theorem pm_cons_out {ι : ITree} {pref : List (ℕ × ℕ)} {p : ℕ × ℕ} {t : List (ℕ × ℕ)}
    (ha : p.1 < ι.nA pref) (hy : ¬ p.2 < ι.nY pref ⟨p.1, ha⟩) :
    pm ι pref (p :: t) = 0 := by
  simp [pm, ha, hy]

theorem pm_cons_ok {ι : ITree} {pref : List (ℕ × ℕ)} {p : ℕ × ℕ} {t : List (ℕ × ℕ)}
    (ha : p.1 < ι.nA pref) (hy : p.2 < ι.nY pref ⟨p.1, ha⟩) :
    pm ι pref (p :: t) =
      ι.kern pref ⟨p.1, ha⟩ ⟨p.2, hy⟩ * pm ι (pref ++ [p]) t := by
  simp [pm, ha, hy]

theorem pm_nonneg (ι : ITree) (pref : List (ℕ × ℕ)) : ∀ t, 0 ≤ pm ι pref t := by
  intro t
  induction t generalizing pref with
  | nil => simp [pm]
  | cons p t ih =>
      by_cases ha : p.1 < ι.nA pref
      · by_cases hy : p.2 < ι.nY pref ⟨p.1, ha⟩
        · rw [pm_cons_ok ha hy]
          exact mul_nonneg (ι.kpos _ _ _).le (ih _)
        · rw [pm_cons_out ha hy]
      · rw [pm_cons_act ha]

theorem pm_single (ι : ITree) (pref : List (ℕ × ℕ))
    (a : Fin (ι.nA pref)) (y : Fin (ι.nY pref a)) :
    pm ι pref [(a.val, y.val)] = ι.kern pref a y := by
  have hy : y.val < ι.nY pref ⟨a.val, a.isLt⟩ := by
    rw [show (⟨a.val, a.isLt⟩ : Fin (ι.nA pref)) = a from Fin.ext rfl]
    exact y.isLt
  rw [pm_cons_ok (p := (a.val, y.val)) (t := []) a.isLt hy, pm_nil, mul_one]

noncomputable def kernRaw (ι : ITree) (h : List (ℕ × ℕ)) (av yv : ℕ) : ℝ :=
  if ha : av < ι.nA h then
    if hy : yv < ι.nY h ⟨av, ha⟩ then ι.kern h ⟨av, ha⟩ ⟨yv, hy⟩ else 0
  else 0

theorem kernRaw_nonneg (ι : ITree) (h : List (ℕ × ℕ)) (av yv : ℕ) :
    0 ≤ kernRaw ι h av yv := by
  unfold kernRaw
  split_ifs with ha hy
  · exact (ι.kpos h ⟨av, ha⟩ ⟨yv, hy⟩).le
  · exact le_rfl
  · exact le_rfl

theorem kernRaw_fin (ι : ITree) (h : List (ℕ × ℕ))
    (a : Fin (ι.nA h)) (y : Fin (ι.nY h a)) :
    kernRaw ι h a.val y.val = ι.kern h a y := by
  have hy : y.val < ι.nY h ⟨a.val, a.isLt⟩ := by
    rw [show (⟨a.val, a.isLt⟩ : Fin (ι.nA h)) = a from Fin.ext rfl]
    exact y.isLt
  simp [kernRaw, a.isLt, hy, show (⟨a.val, a.isLt⟩ : Fin (ι.nA h)) = a from Fin.ext rfl,
    show (⟨y.val, hy⟩ : Fin (ι.nY h ⟨a.val, a.isLt⟩)) = y from Fin.ext (by simp)]

theorem pm_append_one (ι : ITree) (pref : List (ℕ × ℕ)) :
    ∀ (h : List (ℕ × ℕ)) (av yv : ℕ),
      pm ι pref (h ++ [(av, yv)]) = pm ι pref h * kernRaw ι (pref ++ h) av yv := by
  intro h
  induction h generalizing pref with
  | nil =>
      intro av yv
      rw [List.nil_append, pm_nil, one_mul, List.append_nil]
      by_cases ha : av < ι.nA pref
      · by_cases hy : yv < ι.nY pref ⟨av, ha⟩
        · rw [pm_single ι pref ⟨av, ha⟩ ⟨yv, hy⟩]
          simp [kernRaw, ha, hy]
        · rw [pm_cons_out (p := (av, yv)) (t := []) ha hy]
          simp [kernRaw, ha, hy]
      · rw [pm_cons_act (p := (av, yv)) (t := []) ha]
        simp [kernRaw, ha]
  | cons p t ih =>
      intro av yv
      simp only [List.cons_append]
      by_cases hact : p.1 < ι.nA pref
      · by_cases hout : p.2 < ι.nY pref ⟨p.1, hact⟩
        · have hhist : (pref ++ [p]) ++ t = pref ++ (p :: t) := by
            simp [List.append_assoc]
          rw [pm_cons_ok (t := t ++ [(av, yv)]) hact hout,
            pm_cons_ok (t := t) hact hout, ih (pref ++ [p]) av yv]
          have hkern : kernRaw ι ((pref ++ [p]) ++ t) av yv =
              kernRaw ι (pref ++ (p :: t)) av yv := by
            rw [hhist]
          rw [hkern]
          ring
        · rw [pm_cons_out (t := t ++ [(av, yv)]) hact hout,
            pm_cons_out (t := t) hact hout, zero_mul]
      · rw [pm_cons_act (t := t ++ [(av, yv)]) hact,
          pm_cons_act (t := t) hact, zero_mul]

theorem pathMass_append_one (ι : ITree) (h : List (ℕ × ℕ))
    (a : Fin (ι.nA h)) (y : Fin (ι.nY h a)) :
    pathMass ι (h ++ [(a.val, y.val)]) = pathMass ι h * ι.kern h a y := by
  rw [pathMass, pathMass, pm_append_one ι [] h a.val y.val, kernRaw_fin]
  simp

theorem pathMass_sum_child (ι : ITree) (h : List (ℕ × ℕ)) (a : Fin (ι.nA h)) :
    ∑ y : Fin (ι.nY h a), pathMass ι (h ++ [(a.val, y.val)]) = pathMass ι h := by
  simp_rw [pathMass_append_one ι h a, ← mul_sum, ι.ksum h a, mul_one]

theorem pathMass_nonneg (ι : ITree) (h : List (ℕ × ℕ)) : 0 ≤ pathMass ι h :=
  pm_nonneg ι [] h

def truncPath (ι : ITree) : ∀ (n : ℕ) (pref : List (ℕ × ℕ)),
    Leaf (trunc ι n pref) → List (ℕ × ℕ)
  | 0, _, _ => []
  | n + 1, pref, ℓ =>
      (ℓ.fst.val, ℓ.snd.fst.val) ::
        truncPath ι n (pref ++ [(ℓ.fst.val, ℓ.snd.fst.val)]) ℓ.snd.snd

theorem leafPath_mass (ι : ITree) :
    ∀ (n : ℕ) (pref : List (ℕ × ℕ)) (ℓ : Leaf (trunc ι n pref)),
      pm ι pref (truncPath ι n pref ℓ) = leafMass ℓ := by
  intro n
  induction n with
  | zero =>
      intro pref ℓ
      cases ℓ
      simp [trunc, truncPath, leafMass, pm]
  | succ n ih =>
      intro pref ℓ
      have ha : ℓ.fst.val < ι.nA pref := ℓ.fst.isLt
      have hy : ℓ.snd.fst.val < ι.nY pref ⟨ℓ.fst.val, ha⟩ := by
        rw [show (⟨ℓ.fst.val, ha⟩ : Fin (ι.nA pref)) = ℓ.fst from Fin.ext rfl]
        exact ℓ.snd.fst.isLt
      rw [truncPath, pm_cons_ok (p := (ℓ.fst.val, ℓ.snd.fst.val)) ha hy]
      have hchild := ih (pref ++ [(ℓ.fst.val, ℓ.snd.fst.val)]) ℓ.snd.snd
      have ha' : (⟨ℓ.fst.val, ha⟩ : Fin (ι.nA pref)) = ℓ.fst := Fin.ext rfl
      have hy' : (⟨ℓ.snd.fst.val, hy⟩ : Fin (ι.nY pref ⟨ℓ.fst.val, ha⟩)) = ℓ.snd.fst := by
        apply Fin.ext
        simp [ha']
      simp only [ha', hy'] at hchild ⊢
      have hmass : leafMass ℓ = ι.kern pref ℓ.fst ℓ.snd.fst * leafMass ℓ.snd.snd := by
        simp only [trunc] at ℓ
        rfl
      rw [hmass, hchild]

theorem pathMass_leaf (ι : ITree) (n : ℕ) (ℓ : Leaf (trunc ι n [])) :
    pathMass ι (truncPath ι n [] ℓ) = leafMass ℓ := by
  simpa [pathMass] using leafPath_mass ι n [] ℓ

def zeroStrategy : (T : Tree) → Strategy T
  | .leaf => PUnit.unit
  | .node _ _ _ hY _ _ _ child =>
      (fun a => ⟨0, hY a⟩, fun a y => zeroStrategy (child a y))

/-- The raw history read off a terminal leaf. -/
def leafPath : {T : Tree} → Leaf T → List (ℕ × ℕ)
  | .leaf, _ => []
  | .node _ _ _ _ _ _ _ _, ℓ =>
      (ℓ.1.val, ℓ.2.1.val) :: leafPath ℓ.2.2

/-- The strategy's own outputs reproduce this raw history. -/
def stratAgrees : {T : Tree} → Strategy T → List (ℕ × ℕ) → Prop
  | .leaf, _, todo => todo = []
  | .node _ _ _ _ _ _ _ _, _, [] => True
  | .node _ _ _ _ _ _ _ _, s, p :: t =>
      ∃ a : Fin _, a.val = p.1 ∧ (s.1 a).val = p.2 ∧ stratAgrees (s.2 a (s.1 a)) t

noncomputable instance {T : Tree} (s : Strategy T) (todo : List (ℕ × ℕ)) :
    Decidable (stratAgrees s todo) :=
  Classical.propDecidable _

/-- Policy that plays the actions of `todo` for as long as the outputs match it. -/
def followPol : {T : Tree} → List (ℕ × ℕ) → Policy T
  | .leaf, _ => PUnit.unit
  | .node _ hA _ _ _ _ _ child, [] =>
      ⟨⟨0, hA⟩, fun a y => followPol (T := child a y) []⟩
  | .node nA hA _ _ _ _ _ child, p :: t =>
      if ha : p.1 < nA then
        ⟨⟨p.1, ha⟩, fun a y =>
          if a.val = p.1 ∧ y.val = p.2 then followPol (T := child a y) t
          else followPol (T := child a y) []⟩
      else
        ⟨⟨0, hA⟩, fun a y => followPol (T := child a y) []⟩

theorem agrees_prefix :
    ∀ {T : Tree} (s : Strategy T) (todo : List (ℕ × ℕ)),
      stratAgrees s todo → List.IsPrefix todo (leafPath (run s (followPol todo))) := by
  intro T
  induction T with
  | leaf =>
      intro s todo h
      have htodo : todo = [] := by simpa [stratAgrees] using h
      subst htodo
      simp [leafPath, run, List.nil_prefix]
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro s todo h
      cases todo with
      | nil =>
          simp [List.nil_prefix]
      | cons p t =>
          simp only [stratAgrees] at h
          rcases h with ⟨a, ha, hy, ht⟩
          have hlt : p.1 < nA := by simpa [ha] using a.isLt
          have haFin : (⟨p.1, hlt⟩ : Fin nA) = a := Fin.ext (by simpa using ha.symm)
          subst haFin
          simp only [Strategy] at s ⊢
          rcases s with ⟨out, cont⟩
          have hty :
              (Policy (Tree.node nA hA nY hY K Kpos Ksum child)) =
                (Fin nA × ((a : Fin nA) → (y : Fin (nY a)) → Policy (child a y))) := rfl
          let πpair : Fin nA × ((a : Fin nA) → (y : Fin (nY a)) → Policy (child a y)) :=
            ⟨⟨p.1, hlt⟩, fun b y =>
              if b.val = p.1 ∧ y.val = p.2 then followPol (T := child b y) t
              else followPol (T := child b y) []⟩
          have hπ : followPol (p :: t) = cast hty.symm πpair := by
            simp [followPol, hlt, πpair, hty]
          have hchild : stratAgrees (cont ⟨p.1, hlt⟩ (out ⟨p.1, hlt⟩)) t := ht
          have hih := ih ⟨p.1, hlt⟩ (out ⟨p.1, hlt⟩)
            (cont ⟨p.1, hlt⟩ (out ⟨p.1, hlt⟩)) t hchild
          rw [hπ]
          simp only [run, leafPath, cast_eq]
          have hy' : (out ⟨p.1, hlt⟩).val = p.2 := by simpa using hy
          simp only [πpair, hy', ite_true]
          rcases hih with ⟨u, hu⟩
          refine ⟨u, ?_⟩
          simp [List.cons_append, hu]

/-- Leaves whose raw path extends `todo` and which follow `followPol todo`. -/
noncomputable def prefixLeaves {T : Tree} (todo : List (ℕ × ℕ)) : Finset (Leaf T) :=
  Finset.univ.filter fun ℓ =>
    List.IsPrefix todo (leafPath ℓ) ∧ CompatiblePolicy ℓ (followPol todo)

theorem prefix_mass (ι : ITree) :
    ∀ n pref todo,
      todo.length ≤ n →
        ∑ ℓ ∈ prefixLeaves (T := trunc ι n pref) todo, leafMass ℓ = pm ι pref todo := by
  classical
  intro n
  induction n with
  | zero =>
      intro pref todo hn
      have htodo : todo = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hn)
      subst htodo
      have hone : (Finset.univ : Finset (Leaf Tree.leaf)) = {PUnit.unit} := by
        ext x
        cases x
        simp
      simp [trunc, prefixLeaves, leafPath, followPol, CompatiblePolicy, leafMass, pm, hone]
  | succ n ih =>
      intro pref todo hn
      cases todo with
      | nil =>
          have hset : prefixLeaves (T := trunc ι (n + 1) pref) [] =
              Finset.univ.filter fun ℓ : Leaf (trunc ι (n + 1) pref) =>
                CompatiblePolicy ℓ (followPol []) := by
            ext ℓ
            simp [prefixLeaves, List.nil_prefix]
          rw [hset, compatible_mass, pm_nil]
      | cons p t =>
          by_cases hlt : p.1 < ι.nA pref
          · by_cases hy : p.2 < ι.nY pref ⟨p.1, hlt⟩
            · have hlen : t.length ≤ n := by
                simpa using hn
              let a0 : Fin (ι.nA pref) := ⟨p.1, hlt⟩
              let y0 : Fin (ι.nY pref a0) := ⟨p.2, hy⟩
              have hchild := ih (pref ++ [(a0.val, y0.val)]) t hlen
              have hkern := pm_cons_ok (ι := ι) (pref := pref) (p := p) (t := t) hlt hy
              have hty :
                  (Policy (Tree.node (ι.nA pref) (ι.hA pref) (ι.nY pref) (ι.hY pref)
                      (ι.kern pref) (ι.kpos pref) (ι.ksum pref)
                      (fun a y => trunc ι n (pref ++ [(a.val, y.val)])))) =
                    (Fin (ι.nA pref) × ((a : Fin (ι.nA pref)) → (y : Fin (ι.nY pref a)) →
                      Policy (trunc ι n (pref ++ [(a.val, y.val)])))) := rfl
              let πpair : Fin (ι.nA pref) × ((a : Fin (ι.nA pref)) →
                  (y : Fin (ι.nY pref a)) → Policy (trunc ι n (pref ++ [(a.val, y.val)]))) :=
                ⟨a0, fun b y =>
                  if b.val = p.1 ∧ y.val = p.2 then followPol t else followPol []⟩
              have hπ : followPol (p :: t) = cast hty.symm πpair := by
                simp [followPol, hlt, πpair, a0]
              have hsplit :
                  ∑ ℓ ∈ prefixLeaves (T := trunc ι (n + 1) pref) (p :: t), leafMass ℓ =
                    ∑ a : Fin (ι.nA pref), ∑ y : Fin (ι.nY pref a),
                      ∑ ℓc : Leaf (trunc ι n (pref ++ [(a.val, y.val)])),
                        if a = a0 ∧ y.val = p.2 ∧
                            List.IsPrefix t (leafPath ℓc) ∧
                            CompatiblePolicy ℓc (followPol t)
                          then ι.kern pref a y * leafMass ℓc else 0 := by
                classical
                rw [trunc_succ ι pref n, prefixLeaves, sum_filter]
                simp only [Leaf, prefixLeaves, hπ, leafPath, CompatiblePolicy]
                rw [leafSum_psigma]
                refine Finset.sum_congr rfl ?_
                intro a _
                rw [leafSum_psigma]
                refine Finset.sum_congr rfl ?_
                intro y _
                refine Finset.sum_congr rfl ?_
                intro ℓc _
                by_cases ha : a = a0
                · subst ha
                  by_cases hyv : y.val = p.2
                  · have hyFin : y = y0 := Fin.ext (by simpa [y0] using hyv)
                    subst hyFin
                    simp [a0, y0, πpair, List.cons_prefix_cons, hyv, leafMass]
                  · simp [hyv, πpair, a0, leafMass, List.cons_prefix_cons]
                    intro h _ _
                    exfalso
                    exact hyv (congrArg Prod.snd h).symm
                · simp [ha, πpair, a0, leafMass, List.cons_prefix_cons]
              have honly :
                  (∑ a : Fin (ι.nA pref), ∑ y : Fin (ι.nY pref a),
                      ∑ ℓc : Leaf (trunc ι n (pref ++ [(a.val, y.val)])),
                        if a = a0 ∧ y.val = p.2 ∧
                            List.IsPrefix t (leafPath ℓc) ∧
                            CompatiblePolicy ℓc (followPol t)
                          then ι.kern pref a y * leafMass ℓc else 0) =
                    ι.kern pref a0 y0 *
                      ∑ ℓc ∈ prefixLeaves (T := trunc ι n (pref ++ [(a0.val, y0.val)])) t,
                        leafMass ℓc := by
                classical
                have hform : ∀ a : Fin (ι.nA pref),
                    (∑ y : Fin (ι.nY pref a), ∑ ℓc : Leaf (trunc ι n (pref ++ [(a.val, y.val)])),
                        if a = a0 ∧ y.val = p.2 ∧
                            List.IsPrefix t (leafPath ℓc) ∧
                            CompatiblePolicy ℓc (followPol t)
                          then ι.kern pref a y * leafMass ℓc else 0) =
                    if a = a0 then
                      ∑ ℓc ∈ prefixLeaves (T := trunc ι n (pref ++ [(a0.val, y0.val)])) t,
                        ι.kern pref a0 y0 * leafMass ℓc
                    else 0 := by
                  intro a
                  by_cases ha : a = a0
                  · subst ha
                    simp only [if_true, true_and]
                    let f : Fin (ι.nY pref a0) → ℝ := fun y =>
                      ∑ ℓc : Leaf (trunc ι n (pref ++ [(a0.val, y.val)])),
                        if y.val = p.2 ∧ List.IsPrefix t (leafPath ℓc) ∧
                            CompatiblePolicy ℓc (followPol t)
                          then ι.kern pref a0 y * leafMass ℓc else 0
                    have hsingle := Finset.sum_eq_single (s := (Finset.univ : Finset (Fin (ι.nY pref a0))))
                      (a := y0) (f := f) ?_ ?_
                    · simpa [f, y0, prefixLeaves, sum_filter, mul_ite] using hsingle
                    · intro y _ hyne
                      have : y.val ≠ p.2 := by
                        intro h
                        exact hyne (Fin.ext (by simpa [y0] using h))
                      simp [f, this]
                    · intro h
                      exact absurd (Finset.mem_univ y0) h
                  · simp [ha]
                simp_rw [hform]
                rw [Finset.sum_ite_eq' (s := Finset.univ) (a := a0), if_pos (Finset.mem_univ _)]
                rw [Finset.mul_sum]
              rw [hsplit, honly, hchild]
              simp [a0, y0, hkern]
            · rw [pm_cons_out hlt hy]
              apply (Finset.sum_eq_zero_iff_of_nonneg (s := prefixLeaves (p :: t))
                (f := fun ℓ : Leaf (trunc ι (n + 1) pref) => leafMass ℓ)
                (fun ℓ _ => (leafMass_pos ℓ).le)).mpr
              intro ℓ hℓ
              simp only [prefixLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
              exfalso
              have htree := trunc_succ ι pref n
              revert ℓ hℓ
              rw [htree]
              intro ℓ hℓ
              rcases ℓ with ⟨a, y, ℓc⟩
              rcases hℓ with ⟨hpre, -⟩
              have hp := (List.cons_prefix_cons.mp (by simpa [leafPath] using hpre)).1
              have hyv : y.val = p.2 := (congrArg Prod.snd hp).symm
              have hav : a.val = p.1 := (congrArg Prod.fst hp).symm
              have haFin : a = ⟨p.1, hlt⟩ := Fin.ext hav
              exact hy (hyv ▸ (haFin ▸ y.isLt))
          · rw [pm_cons_act hlt]
            apply (Finset.sum_eq_zero_iff_of_nonneg (s := prefixLeaves (p :: t))
              (f := fun ℓ : Leaf (trunc ι (n + 1) pref) => leafMass ℓ)
              (fun ℓ _ => (leafMass_pos ℓ).le)).mpr
            intro ℓ hℓ
            simp only [prefixLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ
            exfalso
            have htree := trunc_succ ι pref n
            revert ℓ hℓ
            rw [htree]
            intro ℓ hℓ
            rcases ℓ with ⟨a, y, ℓc⟩
            rcases hℓ with ⟨hpre, -⟩
            have hp := (List.cons_prefix_cons.mp (by simpa [leafPath] using hpre)).1
            have hav : a.val = p.1 := (congrArg Prod.fst hp).symm
            exact hlt (hav ▸ a.isLt)

noncomputable def hitSum {T : Tree} (atoms : List (Atom T)) (todo : List (ℕ × ℕ)) : ℝ :=
  (atoms.map fun a => if stratAgrees a.2 todo then a.1 else 0).sum

theorem hitSum_eq_total {T : Tree} (atoms : List (Atom T)) (todo : List (ℕ × ℕ)) :
    hitSum atoms todo = totalWeight (atoms.filter fun a => stratAgrees a.2 todo) := by
  classical
  induction atoms with
  | nil => simp [hitSum, totalWeight]
  | cons a tail ih =>
      have hhead : hitSum (a :: tail) todo =
          (if stratAgrees a.2 todo then a.1 else 0) + hitSum tail todo := by
        simp [hitSum]
      rw [hhead, ih]
      by_cases h : stratAgrees a.2 todo
      · simp [totalWeight, h]
      · simp [totalWeight, h]

theorem transcript_filter_le {T : Tree} (atoms : List (Atom T))
    (p : Atom T → Prop) [DecidablePred p] (π : Policy T) (ℓ : Leaf T)
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) :
    transcriptWeight (atoms.filter p) π ℓ ≤ transcriptWeight atoms π ℓ := by
  classical
  induction atoms with
  | nil => simp [transcriptWeight]
  | cons a tail ih =>
      have htail : ∀ b ∈ tail, 0 ≤ b.1 := fun b hb => hnn b (by simp [hb])
      by_cases hp : p a
      · simp only [List.filter_cons, hp, decide_eq_true_eq, if_true, transcriptWeight,
          List.map_cons, List.sum_cons]
        have hih := ih htail
        simp only [transcriptWeight] at hih
        linarith
      · have hhead : 0 ≤ (if run a.2 π = ℓ then a.1 else 0) := by
          split_ifs with hr
          · exact hnn a (by simp)
          · simp
        simp only [List.filter_cons, hp, decide_eq_true_eq, ite_false, transcriptWeight,
          List.map_cons, List.sum_cons]
        have hih := ih htail
        simp only [transcriptWeight] at hih
        linarith [hhead, hih]

theorem agrees_mem_prefix {T : Tree} (s : Strategy T) (todo : List (ℕ × ℕ))
    (h : stratAgrees s todo) :
    run s (followPol todo) ∈ prefixLeaves todo := by
  classical
  refine Finset.mem_filter.mpr ?_
  exact ⟨Finset.mem_univ _, ⟨agrees_prefix s todo h, run_compatible_policy s (followPol todo)⟩⟩

theorem good_misses_outside {T : Tree} (atoms : List (Atom T)) (todo : List (ℕ × ℕ))
    (ℓ : Leaf T) (hℓ : ℓ ∉ prefixLeaves todo) :
    transcriptWeight (atoms.filter fun a => stratAgrees a.2 todo) (followPol todo) ℓ = 0 := by
  classical
  refine transcript_zero_of_not_hit _ (followPol todo) ℓ ?_
  intro hmem
  simp only [List.mem_toFinset, List.mem_map] at hmem
  rcases hmem with ⟨a, ha, heq⟩
  have hagree : stratAgrees a.2 todo := by
    simpa using (List.mem_filter.mp ha).2
  exact hℓ (by simpa [heq] using agrees_mem_prefix a.2 todo hagree)

theorem hit_le_prefix {T : Tree} (atoms : List (Atom T)) (todo : List (ℕ × ℕ))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1)
    (hle : ∀ ℓ, transcriptWeight atoms (followPol todo) ℓ ≤ leafMass ℓ) :
    hitSum atoms todo ≤ ∑ ℓ ∈ prefixLeaves (T := T) todo, leafMass ℓ := by
  classical
  let good := atoms.filter fun a => stratAgrees a.2 todo
  have htot : hitSum atoms todo = totalWeight good := hitSum_eq_total atoms todo
  have hsplit : totalWeight good = ∑ ℓ : Leaf T, transcriptWeight good (followPol todo) ℓ :=
    total_eq_transcript good (followPol todo)
  have houtside : ∑ ℓ : Leaf T, transcriptWeight good (followPol todo) ℓ =
      ∑ ℓ ∈ prefixLeaves (T := T) todo, transcriptWeight good (followPol todo) ℓ :=
    (Finset.sum_subset (Finset.subset_univ _)
      (fun ℓ _ hℓ => good_misses_outside atoms todo ℓ hℓ)).symm
  have hle' : ∑ ℓ ∈ prefixLeaves (T := T) todo, transcriptWeight good (followPol todo) ℓ ≤
      ∑ ℓ ∈ prefixLeaves (T := T) todo, leafMass ℓ := by
    refine Finset.sum_le_sum ?_
    intro ℓ _
    exact le_trans (transcript_filter_le atoms (fun a => stratAgrees a.2 todo)
      (followPol todo) ℓ hnn) (hle ℓ)
  linarith

theorem greedy_take_nonneg (T : Tree) (M : ℕ) :
    ∀ a ∈ (greedyList T).take M, 0 ≤ a.1 := by
  intro a ha
  exact greedy_mem_nonneg T (List.mem_of_mem_take ha)

theorem greedy_cylinder (ι : ITree) (n : ℕ) (todo : List (ℕ × ℕ))
    (hn : todo.length ≤ n) (M : ℕ) :
    hitSum ((greedyList (trunc ι n [])).take M) todo ≤ pathMass ι todo := by
  classical
  have hhit := hit_le_prefix ((greedyList (trunc ι n [])).take M) todo
    (greedy_take_nonneg _ M)
    (fun ℓ => transcript_take_le (trunc ι n []) (followPol todo) M ℓ)
  have hmass := prefix_mass ι n [] todo hn
  simpa [pathMass] using le_trans hhit (le_of_eq hmass)

/-! ## Strategies on the infinite tree -/

abbrev NodeIdx (ι : ITree) := Σ h : List (ℕ × ℕ), Fin (ι.nA h)

abbrev IStrategy (ι : ITree) := ∀ p : NodeIdx ι, Fin (ι.nY p.1 p.2)

def restrict (ι : ITree) : ∀ (n : ℕ) (pref : List (ℕ × ℕ)),
    IStrategy ι → Strategy (trunc ι n pref)
  | 0, _, _ => PUnit.unit
  | n + 1, pref, s =>
      (fun a => s ⟨pref, a⟩,
        fun a y => restrict ι n (pref ++ [(a.val, y.val)]) s)

/-- Output value prescribed by a depth-`n` strategy at a raw continuation. -/
def readVal (ι : ITree) : ∀ (n : ℕ) (base : List (ℕ × ℕ)),
    Strategy (trunc ι n base) → List (ℕ × ℕ) → ℕ → ℕ
  | 0, _, _, _, _ => 0
  | n + 1, base, s, [], av =>
      if ha : av < ι.nA base then (s.1 ⟨av, ha⟩).val else 0
  | n + 1, base, s, p :: rest, av =>
      if ha : p.1 < ι.nA base then
        if hy : p.2 < ι.nY base ⟨p.1, ha⟩ then
          readVal ι n (base ++ [(p.1, p.2)]) (s.2 ⟨p.1, ha⟩ ⟨p.2, hy⟩) rest av
        else 0
      else 0

noncomputable def extendAbs (ι : ITree) (n : ℕ) (pref : List (ℕ × ℕ))
    (s : Strategy (trunc ι n pref)) : IStrategy ι :=
  fun p =>
    let rest := p.1.drop pref.length
    let v := readVal ι n pref s rest p.2.val
    if hv : p.1.take pref.length = pref ∧ v < ι.nY p.1 p.2 then ⟨v, hv.2⟩
    else ⟨0, ι.hY p.1 p.2⟩

noncomputable def extend (ι : ITree) (n : ℕ) (s : Strategy (trunc ι n [])) : IStrategy ι :=
  extendAbs ι n [] s

def iAgree (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ)) : Prop :=
  stratAgrees (restrict ι h.length [] s) h

noncomputable def greedyStrat (ι : ITree) (n i : ℕ) : Strategy (trunc ι n []) :=
  if h : i < (greedyList (trunc ι n [])).length then
    ((greedyList (trunc ι n []))[i]).2
  else
    zeroStrategy _

noncomputable def greedyCode (ι : ITree) (n i : ℕ) : IStrategy ι :=
  extend ι n (greedyStrat ι n i)

theorem readVal_nil (ι : ITree) (n : ℕ) (base : List (ℕ × ℕ))
    (s : Strategy (trunc ι (n + 1) base)) (a : Fin (ι.nA base)) :
    readVal ι (n + 1) base s [] a.val = (s.1 a).val := by
  simp [readVal, a.isLt, Fin.ext_iff]

theorem extend_root (ι : ITree) (n : ℕ) (s : Strategy (trunc ι (n + 1) []))
    (a : Fin (ι.nA [])) :
    extend ι (n + 1) s ⟨[], a⟩ = s.1 a := by
  have hv : readVal ι (n + 1) [] s [] a.val = (s.1 a).val := readVal_nil ι n [] s a
  have hlt : readVal ι (n + 1) [] s [] a.val < ι.nY [] a := by
    rw [hv]
    exact (s.1 a).isLt
  simp [extend, extendAbs, hv, hlt, List.take_nil, List.drop_nil, Fin.ext_iff]

theorem readVal_step (ι : ITree) (n : ℕ) (base : List (ℕ × ℕ))
    (s : Strategy (trunc ι (n + 1) base)) (p : ℕ × ℕ) (rest : List (ℕ × ℕ)) (av : ℕ)
    (ha : p.1 < ι.nA base) (hy : p.2 < ι.nY base ⟨p.1, ha⟩) :
    readVal ι (n + 1) base s (p :: rest) av =
      readVal ι n (base ++ [(p.1, p.2)]) (s.2 ⟨p.1, ha⟩ ⟨p.2, hy⟩) rest av := by
  simp [readVal, ha, hy]

theorem extendAbs_here (ι : ITree) (n : ℕ) (pref : List (ℕ × ℕ))
    (s : Strategy (trunc ι (n + 1) pref)) (a : Fin (ι.nA pref)) :
    extendAbs ι (n + 1) pref s ⟨pref, a⟩ = s.1 a := by
  have hv : readVal ι (n + 1) pref s [] a.val = (s.1 a).val := readVal_nil ι n pref s a
  have hlt : readVal ι (n + 1) pref s [] a.val < ι.nY pref a := by
    rw [hv]
    exact (s.1 a).isLt
  simp [extendAbs, List.drop_length, List.take_length, hv, hlt, Fin.ext_iff]

theorem extendAbs_under (ι : ITree) (n : ℕ) (pref : List (ℕ × ℕ))
    (s : Strategy (trunc ι (n + 1) pref)) (a : Fin (ι.nA pref)) (y : Fin (ι.nY pref a))
    (rest : List (ℕ × ℕ))
    (b : Fin (ι.nA (pref ++ [(a.val, y.val)] ++ rest))) :
    extendAbs ι (n + 1) pref s ⟨pref ++ [(a.val, y.val)] ++ rest, b⟩ =
      extendAbs ι n (pref ++ [(a.val, y.val)]) (s.2 a y)
        ⟨pref ++ [(a.val, y.val)] ++ rest, b⟩ := by
  classical
  rcases a with ⟨av, hav⟩
  rcases y with ⟨yv, hyv⟩
  have hread :
      readVal ι (n + 1) pref s ((av, yv) :: rest) b.val =
        readVal ι n (pref ++ [(av, yv)]) (s.2 ⟨av, hav⟩ ⟨yv, hyv⟩) rest b.val := by
    simp [readVal, hav, hyv]
  have hassoc : pref ++ [(av, yv)] ++ rest = pref ++ ([(av, yv)] ++ rest) := by
    simp [List.append_assoc]
  have htake1 :
      (pref ++ [(av, yv)] ++ rest).take (pref ++ [(av, yv)]).length = pref ++ [(av, yv)] :=
    List.take_append_length (l₁ := pref ++ [(av, yv)]) (l₂ := rest)
  have hdrop1 :
      (pref ++ [(av, yv)] ++ rest).drop (pref ++ [(av, yv)]).length = rest :=
    List.drop_append_length (l₁ := pref ++ [(av, yv)]) (l₂ := rest)
  have htake0 : (pref ++ [(av, yv)] ++ rest).take pref.length = pref := by
    rw [hassoc]
    exact List.take_append_length (l₁ := pref) (l₂ := [(av, yv)] ++ rest)
  have hdrop0 : (pref ++ [(av, yv)] ++ rest).drop pref.length = (av, yv) :: rest := by
    rw [hassoc]
    simpa [List.singleton_append] using
      (List.drop_append_length (l₁ := pref) (l₂ := [(av, yv)] ++ rest))
  apply Fin.ext
  simp only [extendAbs, htake0, htake1, hdrop0, hdrop1, hread, Fin.val_mk]

/-! ## Agreement along a raw history

`agreesFrom s pref todo` says that `s`, read on top of `pref`, reproduces every
output recorded in `todo`. It depends only on the finitely many nodes along
that history, so it is continuous for the product of discrete output spaces.
-/

def agreesFrom (ι : ITree) (s : IStrategy ι) :
    List (ℕ × ℕ) → List (ℕ × ℕ) → Prop
  | _, [] => True
  | pref, p :: t =>
      ∃ a : Fin (ι.nA pref), a.val = p.1 ∧ (s ⟨pref, a⟩).val = p.2 ∧
        agreesFrom ι s (pref ++ [p]) t

noncomputable instance (ι : ITree) (s : IStrategy ι) (pref todo : List (ℕ × ℕ)) :
    Decidable (agreesFrom ι s pref todo) :=
  Classical.propDecidable _

theorem agreesFrom_nil (ι : ITree) (s : IStrategy ι) (pref : List (ℕ × ℕ)) :
    agreesFrom ι s pref [] := by
  simp [agreesFrom]

theorem agreesFrom_cons (ι : ITree) (s : IStrategy ι) (pref : List (ℕ × ℕ))
    (p : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    agreesFrom ι s pref (p :: t) ↔
      (∃ a : Fin (ι.nA pref), a.val = p.1 ∧ (s ⟨pref, a⟩).val = p.2) ∧
        agreesFrom ι s (pref ++ [p]) t := by
  simp only [agreesFrom]
  constructor
  · rintro ⟨a, ha, hv, ht⟩
    exact ⟨⟨a, ha, hv⟩, ht⟩
  · rintro ⟨⟨a, ha, hv⟩, ht⟩
    exact ⟨a, ha, hv, ht⟩

theorem agreesFrom_congr {ι : ITree} {s t : IStrategy ι} {pref todo : List (ℕ × ℕ)}
    (h : ∀ q : NodeIdx ι, List.IsPrefix pref q.1 → s q = t q) :
    agreesFrom ι s pref todo ↔ agreesFrom ι t pref todo := by
  induction todo generalizing pref with
  | nil => simp [agreesFrom]
  | cons p tl ih =>
      simp only [agreesFrom]
      constructor
      · rintro ⟨a, ha, hv, htail⟩
        have hs : s ⟨pref, a⟩ = t ⟨pref, a⟩ :=
          h ⟨pref, a⟩ ⟨[], List.append_nil _⟩
        refine ⟨a, ha, by simpa [hs] using hv, ?_⟩
        refine (ih (pref := pref ++ [p]) ?_).1 htail
        intro q hq
        rcases hq with ⟨rest, hrest⟩
        exact h q ⟨[p] ++ rest, by
          simpa [List.singleton_append, List.append_assoc] using hrest⟩
      · rintro ⟨a, ha, hv, htail⟩
        have hs : s ⟨pref, a⟩ = t ⟨pref, a⟩ :=
          h ⟨pref, a⟩ ⟨[], List.append_nil _⟩
        refine ⟨a, ha, by simpa [hs] using hv, ?_⟩
        refine (ih (pref := pref ++ [p]) ?_).2 htail
        intro q hq
        rcases hq with ⟨rest, hrest⟩
        exact h q ⟨[p] ++ rest, by
          simpa [List.singleton_append, List.append_assoc] using hrest⟩

theorem extendAbs_agreesFrom (ι : ITree) (n : ℕ) (pref todo : List (ℕ × ℕ))
    (s : Strategy (trunc ι n pref)) (hn : todo.length ≤ n) :
    agreesFrom ι (extendAbs ι n pref s) pref todo ↔ stratAgrees s todo := by
  classical
  induction n generalizing pref todo with
  | zero =>
      have htodo : todo = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hn)
      subst htodo
      simp [agreesFrom, trunc, stratAgrees]
  | succ n ih =>
      cases todo with
      | nil =>
          simp [agreesFrom, trunc, stratAgrees]
      | cons p tl =>
          have hlen : tl.length ≤ n := by simpa using hn
          rw [agreesFrom_cons]
          constructor
          · rintro ⟨⟨a, ha, hv⟩, htail⟩
            have hhere := extendAbs_here ι n pref s a
            have hout : (s.1 a).val = p.2 := by simpa [hhere] using hv
            have hstep : (a.val, (s.1 a).val) = p := Prod.ext ha hout
            have hpt :
                agreesFrom ι (extendAbs ι (n + 1) pref s) (pref ++ [p]) tl ↔
                  agreesFrom ι
                    (extendAbs ι n (pref ++ [(a.val, (s.1 a).val)]) (s.2 a (s.1 a)))
                    (pref ++ [p]) tl := by
              apply agreesFrom_congr
              intro q hq
              rcases q with ⟨hist, b⟩
              rcases hq with ⟨rest, hrest⟩
              have hhist : hist = pref ++ [(a.val, (s.1 a).val)] ++ rest := by
                simpa [hstep, List.append_assoc] using hrest.symm
              subst hhist
              let hb : Fin (ι.nA (pref ++ [(a.val, (s.1 a).val)] ++ rest)) :=
                ⟨b.val, b.isLt⟩
              have hbEq : b = hb := Fin.ext rfl
              rw [hbEq]
              exact extendAbs_under ι n pref s a (s.1 a) rest hb
            have hchild := ih (pref ++ [(a.val, (s.1 a).val)]) tl (s.2 a (s.1 a)) hlen
            simp only [hstep] at hchild
            exact ⟨a, ha, hout, hchild.mp (hpt.mp htail)⟩
          · rintro ⟨a, ha, hout, hchild⟩
            have hstep : (a.val, (s.1 a).val) = p := Prod.ext ha hout
            have hpt :
                agreesFrom ι (extendAbs ι (n + 1) pref s) (pref ++ [p]) tl ↔
                  agreesFrom ι
                    (extendAbs ι n (pref ++ [(a.val, (s.1 a).val)]) (s.2 a (s.1 a)))
                    (pref ++ [p]) tl := by
              apply agreesFrom_congr
              intro q hq
              rcases q with ⟨hist, b⟩
              rcases hq with ⟨rest, hrest⟩
              have hhist : hist = pref ++ [(a.val, (s.1 a).val)] ++ rest := by
                simpa [hstep, List.append_assoc] using hrest.symm
              subst hhist
              let hb : Fin (ι.nA (pref ++ [(a.val, (s.1 a).val)] ++ rest)) :=
                ⟨b.val, b.isLt⟩
              have hbEq : b = hb := Fin.ext rfl
              rw [hbEq]
              exact extendAbs_under ι n pref s a (s.1 a) rest hb
            have hih := ih (pref ++ [(a.val, (s.1 a).val)]) tl (s.2 a (s.1 a)) hlen
            simp only [hstep] at hih
            refine ⟨⟨a, ha, ?_⟩, hpt.mpr (hih.mpr hchild)⟩
            have hhere := extendAbs_here ι n pref s a
            simpa [hhere] using hout

/-- Outputs of the restricted strategy are the infinite strategy's outputs. -/
theorem restrict_agreesFrom (ι : ITree) (n : ℕ) (pref todo : List (ℕ × ℕ))
    (s : IStrategy ι) (hn : todo.length ≤ n) :
    stratAgrees (restrict ι n pref s) todo ↔ agreesFrom ι s pref todo := by
  classical
  induction n generalizing pref todo s with
  | zero =>
      have htodo : todo = [] :=
        List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero hn)
      subst htodo
      simp [restrict, trunc, stratAgrees, agreesFrom]
  | succ n ih =>
      cases todo with
      | nil =>
          simp [restrict, trunc, stratAgrees, agreesFrom]
      | cons p tl =>
          have hlen : tl.length ≤ n := by simpa using hn
          rw [agreesFrom_cons]
          simp only [restrict, trunc, stratAgrees]
          constructor
          · rintro ⟨a, ha, hv, hchild⟩
            refine ⟨⟨a, ha, hv⟩, ?_⟩
            have hstep : (a.val, (s ⟨pref, a⟩).val) = p := Prod.ext ha hv
            have hih := ih (pref ++ [(a.val, (s ⟨pref, a⟩).val)]) tl s hlen
            simp only [hstep] at hih
            exact hih.mp hchild
          · rintro ⟨⟨a, ha, hv⟩, htail⟩
            have hstep : (a.val, (s ⟨pref, a⟩).val) = p := Prod.ext ha hv
            refine ⟨a, ha, hv, ?_⟩
            have hih := ih (pref ++ [(a.val, (s ⟨pref, a⟩).val)]) tl s hlen
            simp only [hstep] at hih
            exact hih.mpr htail

theorem stratAgrees_iff_compat :
    ∀ {T : Tree} (d : Strategy T) (ℓ : Leaf T),
      stratAgrees d (leafPath ℓ) ↔ CompatibleStrategy ℓ d := by
  classical
  intro T
  induction T with
  | leaf =>
      intro d ℓ
      cases ℓ
      simp [stratAgrees, leafPath, CompatibleStrategy]
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro d ℓ
      rcases ℓ with ⟨a, y, ℓc⟩
      simp only [Strategy] at d
      rcases d with ⟨out, cont⟩
      simp only [leafPath, stratAgrees, CompatibleStrategy]
      constructor
      · rintro ⟨a0, ha0, hv, ht⟩
        have haEq : a0 = a := Fin.ext ha0
        rw [haEq] at hv ht
        have hy : out a = y := Fin.ext hv
        rw [hy] at ht
        exact ⟨hy.symm, (ih a y (cont a y) ℓc).1 ht⟩
      · rintro ⟨rfl, hc⟩
        exact ⟨a, rfl, rfl, (ih a (out a) (cont a (out a)) ℓc).2 hc⟩

theorem truncPath_length (ι : ITree) :
    ∀ (n : ℕ) (pref : List (ℕ × ℕ)) (ℓ : Leaf (trunc ι n pref)),
      (truncPath ι n pref ℓ).length = n := by
  intro n
  induction n with
  | zero =>
      intro pref ℓ
      cases ℓ
      simp [trunc, truncPath]
  | succ n ih =>
      intro pref ℓ
      simp only [trunc] at ℓ
      rcases ℓ with ⟨a, y, ℓc⟩
      simp [truncPath, ih]

theorem leafPath_eq_truncPath (ι : ITree) :
    ∀ (n : ℕ) (pref : List (ℕ × ℕ)) (ℓ : Leaf (trunc ι n pref)),
      leafPath ℓ = truncPath ι n pref ℓ := by
  intro n
  induction n with
  | zero =>
      intro pref ℓ
      cases ℓ
      simp [trunc, leafPath, truncPath]
  | succ n ih =>
      intro pref ℓ
      simp only [trunc] at ℓ
      rcases ℓ with ⟨a, y, ℓc⟩
      simp [leafPath, truncPath, ih]

theorem iAgree_iff (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ)) :
    iAgree ι s h ↔ agreesFrom ι s [] h := by
  exact restrict_agreesFrom ι h.length [] h s le_rfl

/-! ## Limit strategies

The greedy weights along `diagIndex` already converge. The codes of those
finite strategies live in a countable product of finite discrete output
spaces, so a further subsequence converges at every node. The limit is a
countable family of strategies on the infinite tree, not merely a family
of weights.
-/

open Filter
open scoped Topology

instance (ι : ITree) : Countable (NodeIdx ι) := inferInstance

instance (ι : ITree) : CompactSpace (IStrategy ι) := Pi.compactSpace

instance (ι : ITree) : FirstCountableTopology (IStrategy ι) := inferInstance

instance (ι : ITree) : CompactSpace (ℕ → IStrategy ι) := Pi.compactSpace

instance (ι : ITree) : FirstCountableTopology (ℕ → IStrategy ι) := inferInstance

structure CapPack (ι : ITree) where
  strat : ℕ → IStrategy ι
  index : ℕ → ℕ
  mono : StrictMono index
  tend : Tendsto (fun n => fun i => greedyCode ι (diagIndex ι (index n)) i) atTop (𝓝 strat)

noncomputable def capPack (ι : ITree) : CapPack ι :=
  Classical.choice <| by
    obtain ⟨a, φ, hφ, htend⟩ :=
      CompactSpace.tendsto_subseq
        (fun n : ℕ => fun i : ℕ => greedyCode ι (diagIndex ι n) i)
    exact ⟨⟨a, φ, hφ, htend⟩⟩

noncomputable def capStrat (ι : ITree) (i : ℕ) : IStrategy ι :=
  (capPack ι).strat i

noncomputable def capIndex (ι : ITree) (n : ℕ) : ℕ :=
  diagIndex ι ((capPack ι).index n)

theorem capIndex_mono (ι : ITree) : StrictMono (capIndex ι) := by
  intro a b hab
  unfold capIndex diagIndex
  exact (diagPack ι).mono ((capPack ι).mono hab)

theorem cap_coord_tendsto (ι : ITree) (i : ℕ) (p : NodeIdx ι) :
    Tendsto (fun n => greedyCode ι (capIndex ι n) i p) atTop (𝓝 (capStrat ι i p)) := by
  have h := (capPack ι).tend
  rw [tendsto_pi_nhds] at h
  have hi := h i
  rw [tendsto_pi_nhds] at hi
  simpa [capIndex, capStrat] using hi p

theorem cap_coord_eventually (ι : ITree) (i : ℕ) (p : NodeIdx ι) :
    ∀ᶠ n in atTop, greedyCode ι (capIndex ι n) i p = capStrat ι i p := by
  have h := cap_coord_tendsto ι i p
  rw [nhds_discrete] at h
  exact (tendsto_pure.mp h)

theorem cap_weight_tendsto (ι : ITree) (i : ℕ) :
    Tendsto (fun n => gWeight ι (capIndex ι n) i) atTop (𝓝 (diagWeight ι i)) := by
  unfold capIndex
  have h := (diag_coord_tendsto ι i).comp (capPack ι).mono.tendsto_atTop
  have heq :
      ((fun n => gWeight ι (diagIndex ι n) i) ∘ (capPack ι).index) =
        fun n => gWeight ι (diagIndex ι ((capPack ι).index n)) i := by
    funext n
    rfl
  exact heq ▸ h

theorem diagWeight_nonneg (ι : ITree) (i : ℕ) : 0 ≤ diagWeight ι i :=
  ((diagPack ι).mem i).1

theorem diagWeight_le_one (ι : ITree) (i : ℕ) : diagWeight ι i ≤ 1 :=
  ((diagPack ι).mem i).2

theorem diagPartial_mono (ι : ITree) : Monotone (diagPartial ι) := by
  intro M N hMN
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hMN) ?_
  intro i _ _
  exact diagWeight_nonneg ι i

theorem diagWeight_tsum (ι : ITree) : ∑' i, diagWeight ι i = diagMass ι := by
  have hs : Summable (diagWeight ι) :=
    summable_of_sum_range_le (diagWeight_nonneg ι) fun M => diagPartial_le_atomQ ι M
  have hsum : Tendsto (fun M => diagPartial ι M) atTop (𝓝 (∑' i, diagWeight ι i)) := by
    simpa [diagPartial] using hs.hasSum.tendsto_sum_nat
  have hsup : Tendsto (diagPartial ι) atTop (𝓝 (diagMass ι)) := by
    rw [diagMass, sSup_range]
    exact tendsto_atTop_ciSup (diagPartial_mono ι) (diagPartial_bdd ι)
  exact tendsto_nhds_unique hsup hsum |>.symm

theorem diagMass_eq_tsum_atomQ (ι : ITree) : ∑' i, diagWeight ι i = atomQ ι := by
  rw [diagWeight_tsum, diagMass_eq_atomQ]

noncomputable def indAgree (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ)) : ℝ :=
  if iAgree ι s h then 1 else 0

theorem indAgree_nonneg (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ)) :
    0 ≤ indAgree ι s h := by
  by_cases hi : iAgree ι s h <;> simp [indAgree, hi]

theorem indAgree_le_one (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ)) :
    indAgree ι s h ≤ 1 := by
  by_cases hi : iAgree ι s h <;> simp [indAgree, hi]

theorem iAgree_nil (ι : ITree) (s : IStrategy ι) : iAgree ι s [] := by
  simp [iAgree, stratAgrees, restrict, trunc]

theorem indAgree_nil (ι : ITree) (s : IStrategy ι) : indAgree ι s [] = 1 := by
  simp [indAgree, iAgree_nil]

theorem iAgree_greedyCode (ι : ITree) (n i : ℕ) (h : List (ℕ × ℕ)) (hn : h.length ≤ n) :
    iAgree ι (greedyCode ι n i) h ↔ stratAgrees (greedyStrat ι n i) h := by
  rw [iAgree_iff, greedyCode, extend]
  exact (extendAbs_agreesFrom ι n [] h (greedyStrat ι n i) hn)

theorem eventually_agreesFrom (ι : ITree) {s : ℕ → IStrategy ι} {t : IStrategy ι}
    (hcoord : ∀ p, ∀ᶠ n in atTop, s n p = t p)
    (pref todo : List (ℕ × ℕ)) :
    ∀ᶠ n in atTop, agreesFrom ι (s n) pref todo ↔ agreesFrom ι t pref todo := by
  classical
  induction todo generalizing pref with
  | nil =>
      exact Eventually.of_forall fun _ => by simp [agreesFrom]
  | cons p tl ih =>
      by_cases hact : p.1 < ι.nA pref
      · let a : Fin (ι.nA pref) := ⟨p.1, hact⟩
        refine ((hcoord ⟨pref, a⟩).and (ih (pref ++ [p]))).mono ?_
        intro n ⟨hn, ht⟩
        rw [agreesFrom_cons, agreesFrom_cons]
        constructor
        · rintro ⟨⟨a', ha', hv⟩, htl⟩
          have haEq : a' = a := Fin.ext (by simp [a, ha'])
          subst haEq
          exact ⟨⟨a, ha', by simpa [hn] using hv⟩, ht.mp htl⟩
        · rintro ⟨⟨a', ha', hv⟩, htl⟩
          have haEq : a' = a := Fin.ext (by simp [a, ha'])
          subst haEq
          exact ⟨⟨a, ha', by simpa [hn] using hv⟩, ht.mpr htl⟩
      · refine Eventually.of_forall ?_
        intro n
        rw [agreesFrom_cons, agreesFrom_cons]
        constructor
        · rintro ⟨⟨a', ha', _⟩, _⟩
          exact False.elim (hact (ha' ▸ a'.isLt))
        · rintro ⟨⟨a', ha', _⟩, _⟩
          exact False.elim (hact (ha' ▸ a'.isLt))

theorem cap_iAgree_eventually (ι : ITree) (i : ℕ) (h : List (ℕ × ℕ)) :
    ∀ᶠ n in atTop,
      iAgree ι (greedyCode ι (capIndex ι n) i) h ↔ iAgree ι (capStrat ι i) h := by
  have hcoord : ∀ p, ∀ᶠ n in atTop, greedyCode ι (capIndex ι n) i p = capStrat ι i p :=
    fun p => cap_coord_eventually ι i p
  have hfrom := eventually_agreesFrom ι hcoord [] h
  refine hfrom.mono ?_
  intro n hn
  simp only [iAgree_iff] at hn ⊢
  exact hn

theorem hitSum_cons {T : Tree} (a : Atom T) (tail : List (Atom T)) (todo : List (ℕ × ℕ)) :
    hitSum (a :: tail) todo =
      (if stratAgrees a.2 todo then a.1 else 0) + hitSum tail todo := by
  simp [hitSum]

theorem hitSum_eq_range {T : Tree} (atoms : List (Atom T)) (todo : List (ℕ × ℕ)) :
    hitSum atoms todo =
      ∑ i ∈ range atoms.length,
        if hi : i < atoms.length then
          if stratAgrees (atoms[i]'hi).2 todo then (atoms[i]'hi).1 else 0
        else 0 := by
  classical
  induction atoms with
  | nil => simp [hitSum]
  | cons a tail ih =>
      classical
      let f : ℕ → ℝ := fun i =>
        if hi : i < (a :: tail).length then
          if stratAgrees ((a :: tail)[i]'hi).2 todo then ((a :: tail)[i]'hi).1 else 0
        else 0
      rw [hitSum_cons, ih]
      have hlen : (a :: tail).length = tail.length + 1 := by simp
      have hrange : range (a :: tail).length = range (tail.length + 1) := by
        simp [hlen]
      have hsplit := Finset.sum_range_succ' (n := tail.length) f
      rw [hrange, hsplit]
      have h0 : f 0 = (if stratAgrees a.2 todo then a.1 else 0) := by
        have hlt : 0 < (a :: tail).length := by simp
        simp [f, hlt, List.getElem_cons_zero]
      have hshift : ∀ i ∈ range tail.length, f (i + 1) =
          (if hi : i < tail.length then
            if stratAgrees (tail[i]'hi).2 todo then (tail[i]'hi).1 else 0
            else 0) := by
        intro i hi
        have hlt : i < tail.length := Finset.mem_range.mp hi
        have hlt' : i + 1 < (a :: tail).length := by
          simpa [List.length_cons] using Nat.succ_lt_succ hlt
        simp [f, hlt, hlt', List.getElem_cons_succ]
      rw [h0, add_comm]
      exact congrArg (fun z => z + (if stratAgrees a.2 todo then a.1 else 0))
        (Finset.sum_congr rfl hshift).symm

theorem atomWeight_lt {T : Tree} (atoms : List (Atom T)) {i : ℕ} (hi : i < atoms.length) :
    atomWeight atoms i = (atoms[i]).1 := by
  simp [atomWeight, hi]

theorem atomWeight_ge {T : Tree} (atoms : List (Atom T)) {i : ℕ} (hi : atoms.length ≤ i) :
    atomWeight atoms i = 0 := by
  have hnot : ¬ i < atoms.length := not_lt.mpr hi
  simp [atomWeight, hnot]

theorem greedyStrat_lt (ι : ITree) (n : ℕ) {i : ℕ}
    (hi : i < (greedyList (trunc ι n [])).length) :
    greedyStrat ι n i = ((greedyList (trunc ι n []))[i]).2 := by
  simp [greedyStrat, hi]

theorem gWeight_eq (ι : ITree) (n i : ℕ) :
    gWeight ι n i = atomWeight (greedyList (trunc ι n [])) i := by
  simpa [gWeight] using (greedy_wAt (trunc ι n []) i).symm

theorem greedy_term (ι : ITree) (n : ℕ) (todo : List (ℕ × ℕ)) (hn : todo.length ≤ n) (i : ℕ) :
    gWeight ι n i * indAgree ι (greedyCode ι n i) todo =
      if hi : i < (greedyList (trunc ι n [])).length then
        if stratAgrees ((greedyList (trunc ι n []))[i]'hi).2 todo then
          ((greedyList (trunc ι n []))[i]'hi).1
        else 0
      else 0 := by
  classical
  rw [gWeight_eq]
  by_cases hi : i < (greedyList (trunc ι n [])).length
  · rw [atomWeight_lt _ hi, dif_pos hi]
    have hstrat : greedyStrat ι n i = ((greedyList (trunc ι n []))[i]'hi).2 :=
      greedyStrat_lt ι n hi
    by_cases hs : stratAgrees ((greedyList (trunc ι n []))[i]'hi).2 todo
    · have hagree : iAgree ι (greedyCode ι n i) todo :=
        (iAgree_greedyCode ι n i todo hn).mpr (by simpa [hstrat] using hs)
      simp [indAgree, hs, hagree, mul_one]
    · have hnot : ¬ iAgree ι (greedyCode ι n i) todo := by
        intro h
        exact hs (by simpa [hstrat] using (iAgree_greedyCode ι n i todo hn).mp h)
      simp [indAgree, hs, hnot, mul_zero]
  · rw [atomWeight_ge _ (not_lt.mp hi), dif_neg hi, zero_mul]

theorem greedy_hit_eq (ι : ITree) (n : ℕ) (todo : List (ℕ × ℕ))
    (hn : todo.length ≤ n) (M : ℕ) :
    ∑ i ∈ range M, gWeight ι n i * indAgree ι (greedyCode ι n i) todo =
      hitSum ((greedyList (trunc ι n [])).take M) todo := by
  classical
  let atoms : List (Atom (trunc ι n [])) := greedyList (trunc ι n [])
  have hterm : ∀ i ∈ range M,
      gWeight ι n i * indAgree ι (greedyCode ι n i) todo =
        if hi : i < atoms.length then
          if stratAgrees (atoms[i]'hi).2 todo then (atoms[i]'hi).1 else 0
        else 0 := by
    intro i _
    simpa [atoms] using greedy_term ι n todo hn i
  rw [Finset.sum_congr rfl hterm]
  by_cases hM : M ≤ atoms.length
  · have hlen : (atoms.take M).length = M := List.length_take_of_le hM
    let takeD : ℕ → ℝ := fun i =>
      if hi : i < (atoms.take M).length then
        if stratAgrees ((atoms.take M)[i]'hi).2 todo then ((atoms.take M)[i]'hi).1 else 0
      else 0
    have hhit : hitSum (atoms.take M) todo = ∑ i ∈ range (atoms.take M).length, takeD i := by
      simpa [takeD] using hitSum_eq_range (atoms.take M) todo
    have hrange : range (atoms.take M).length = range M := by simp [hlen]
    rw [hhit, hrange]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hiM : i < M := Finset.mem_range.mp hi
    have hlt : i < atoms.length := hiM.trans_le hM
    have htakei : i < (atoms.take M).length := by simpa [hlen] using hiM
    have hget := List.getElem_take (xs := atoms) (j := M) (i := i) (h := htakei)
    have hbody : takeD i =
        (if stratAgrees ((atoms.take M)[i]'htakei).2 todo then
          ((atoms.take M)[i]'htakei).1 else 0) := by
      unfold takeD
      rw [dif_pos htakei]
    rw [hbody, hget, dif_pos hlt]
  · have hlen : atoms.length ≤ M := le_of_not_ge hM
    have htake : atoms.take M = atoms := List.take_of_length_le hlen
    rw [htake, hitSum_eq_range atoms todo]
    have hsub : range atoms.length ⊆ range M := Finset.range_mono hlen
    rw [← Finset.sum_subset hsub]
    intro i _ hnot
    simp [not_lt.mpr (by simpa [Finset.mem_range] using hnot)]

theorem greedy_ind_le (ι : ITree) (n : ℕ) (todo : List (ℕ × ℕ))
    (hn : todo.length ≤ n) (M : ℕ) :
    ∑ i ∈ range M, gWeight ι n i * indAgree ι (greedyCode ι n i) todo ≤ pathMass ι todo := by
  rw [greedy_hit_eq ι n todo hn M]
  exact greedy_cylinder ι n todo hn M

theorem capIndex_eventually_ge (ι : ITree) (N : ℕ) :
    ∀ᶠ n in atTop, N ≤ capIndex ι n :=
  (capIndex_mono ι).tendsto_atTop.eventually (eventually_ge_atTop N)

theorem indAgree_cap_eventually (ι : ITree) (i : ℕ) (h : List (ℕ × ℕ)) :
    ∀ᶠ n in atTop, indAgree ι (greedyCode ι (capIndex ι n) i) h =
      indAgree ι (capStrat ι i) h := by
  refine (cap_iAgree_eventually ι i h).mono ?_
  intro n hn
  by_cases hc : iAgree ι (greedyCode ι (capIndex ι n) i) h
  · have ht : iAgree ι (capStrat ι i) h := hn.mp hc
    simp [indAgree, hc, ht]
  · have ht : ¬ iAgree ι (capStrat ι i) h := fun hcap => hc (hn.mpr hcap)
    simp [indAgree, hc, ht]

theorem cap_partial_tendsto (ι : ITree) (h : List (ℕ × ℕ)) (M : ℕ) :
    Tendsto (fun n => ∑ i ∈ range M, gWeight ι (capIndex ι n) i *
        indAgree ι (greedyCode ι (capIndex ι n) i) h) atTop
      (𝓝 (∑ i ∈ range M, diagWeight ι i * indAgree ι (capStrat ι i) h)) := by
  refine tendsto_finsetSum (f := fun i n =>
      gWeight ι (capIndex ι n) i * indAgree ι (greedyCode ι (capIndex ι n) i) h)
      (a := fun i => diagWeight ι i * indAgree ι (capStrat ι i) h) (range M) ?_
  intro i _
  have hw := cap_weight_tendsto ι i
  have hind := indAgree_cap_eventually ι i h
  have hconst : Tendsto (fun n => gWeight ι (capIndex ι n) i * indAgree ι (capStrat ι i) h)
      atTop (𝓝 (diagWeight ι i * indAgree ι (capStrat ι i) h)) :=
    hw.mul tendsto_const_nhds
  exact hconst.congr' <| hind.mono fun n hn => by simp [hn]

theorem cyl_partial_le (ι : ITree) (h : List (ℕ × ℕ)) (M : ℕ) :
    ∑ i ∈ range M, diagWeight ι i * indAgree ι (capStrat ι i) h ≤ pathMass ι h := by
  refine le_of_tendsto (cap_partial_tendsto ι h M) ?_
  refine (capIndex_eventually_ge ι h.length).mono ?_
  intro n hn
  simpa using greedy_ind_le ι (capIndex ι n) h hn M

/-! ## Cylinder mass of the limit strategies

`cylMass h` is the total weight of those limiting strategies that reproduce
the raw history `h`. It is at most the kernel mass of `h`. At the root every
strategy agrees, so the cylinder mass is `atomQ`.
-/

noncomputable def cylMass (ι : ITree) (h : List (ℕ × ℕ)) : ℝ :=
  ∑' i, diagWeight ι i * indAgree ι (capStrat ι i) h

theorem cyl_term_nonneg (ι : ITree) (h : List (ℕ × ℕ)) (i : ℕ) :
    0 ≤ diagWeight ι i * indAgree ι (capStrat ι i) h :=
  mul_nonneg (diagWeight_nonneg ι i) (indAgree_nonneg ι (capStrat ι i) h)

theorem cyl_summable (ι : ITree) (h : List (ℕ × ℕ)) :
    Summable fun i => diagWeight ι i * indAgree ι (capStrat ι i) h :=
  summable_of_sum_range_le (cyl_term_nonneg ι h) fun M => cyl_partial_le ι h M

theorem cylMass_tendsto (ι : ITree) (h : List (ℕ × ℕ)) :
    Tendsto (fun M => ∑ i ∈ range M, diagWeight ι i * indAgree ι (capStrat ι i) h)
      atTop (𝓝 (cylMass ι h)) := by
  simpa [cylMass] using (cyl_summable ι h).hasSum.tendsto_sum_nat

theorem cylMass_le_path (ι : ITree) (h : List (ℕ × ℕ)) :
    cylMass ι h ≤ pathMass ι h :=
  le_of_tendsto' (cylMass_tendsto ι h) fun M => cyl_partial_le ι h M

theorem cylMass_nil (ι : ITree) : cylMass ι [] = ∑' i, diagWeight ι i := by
  simp [cylMass, indAgree_nil, mul_one]

theorem cylMass_root (ι : ITree) : cylMass ι [] = atomQ ι := by
  rw [cylMass_nil, diagMass_eq_tsum_atomQ]

theorem pathMass_nil (ι : ITree) : pathMass ι [] = 1 := by
  simp [pathMass, pm]

theorem agreesFrom_concat (ι : ITree) (s : IStrategy ι) :
    ∀ pref todo p,
      agreesFrom ι s pref (todo ++ [p]) ↔
        agreesFrom ι s pref todo ∧ agreesFrom ι s (pref ++ todo) [p] := by
  intro pref todo
  induction todo generalizing pref with
  | nil =>
      intro p
      rw [List.nil_append, List.append_nil]
      simp [agreesFrom]
  | cons q t ih =>
      intro p
      rw [List.cons_append, agreesFrom_cons, agreesFrom_cons, ih]
      have hassoc : pref ++ (q :: t) = (pref ++ [q]) ++ t := by
        simp [List.append_assoc]
      rw [← and_assoc, hassoc]

theorem iAgree_concat (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    iAgree ι s (h ++ [p]) ↔ iAgree ι s h ∧ agreesFrom ι s h [p] := by
  rw [iAgree_iff, iAgree_iff, agreesFrom_concat]
  simp

theorem agreesFrom_singleton (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ))
    (a : Fin (ι.nA h)) (y : Fin (ι.nY h a)) :
    agreesFrom ι s h [(a.val, y.val)] ↔ s ⟨h, a⟩ = y := by
  simp only [agreesFrom]
  constructor
  · rintro ⟨a', ha, hv, _⟩
    have ha' : a' = a := Fin.ext ha
    subst ha'
    exact Fin.ext hv
  · intro heq
    exact ⟨a, rfl, congrArg Fin.val heq, trivial⟩

theorem indAgree_split (ι : ITree) (s : IStrategy ι) (h : List (ℕ × ℕ))
    (a : Fin (ι.nA h)) :
    indAgree ι s h =
      ∑ y : Fin (ι.nY h a), indAgree ι s (h ++ [(a.val, y.val)]) := by
  classical
  by_cases hh : iAgree ι s h
  · let y0 : Fin (ι.nY h a) := s ⟨h, a⟩
    have hyes : iAgree ι s (h ++ [(a.val, y0.val)]) :=
      (iAgree_concat ι s h (a.val, y0.val)).mpr
        ⟨hh, (agreesFrom_singleton ι s h a y0).mpr rfl⟩
    have hone : indAgree ι s (h ++ [(a.val, y0.val)]) = 1 := by
      simp [indAgree, hyes]
    have hrest : ∀ y ∈ (Finset.univ : Finset (Fin (ι.nY h a))), y ≠ y0 →
        indAgree ι s (h ++ [(a.val, y.val)]) = 0 := by
      intro y _ hy
      have hnot : ¬ iAgree ι s (h ++ [(a.val, y.val)]) := by
        intro hagree
        rcases (iAgree_concat ι s h (a.val, y.val)).mp hagree with ⟨_, hstep⟩
        exact hy ((agreesFrom_singleton ι s h a y).mp hstep).symm
      simp [indAgree, hnot]
    rw [show indAgree ι s h = 1 by simp [indAgree, hh]]
    rw [Finset.sum_eq_single y0 hrest (by simp)]
    exact hone.symm
  · have hno : ∀ y : Fin (ι.nY h a), indAgree ι s (h ++ [(a.val, y.val)]) = 0 := by
      intro y
      have hnot : ¬ iAgree ι s (h ++ [(a.val, y.val)]) := by
        intro hagree
        exact hh ((iAgree_concat ι s h (a.val, y.val)).mp hagree).1
      simp [indAgree, hnot]
    rw [show indAgree ι s h = 0 by simp [indAgree, hh]]
    exact (Finset.sum_eq_zero fun y _ => hno y).symm

theorem cylMass_split (ι : ITree) (h : List (ℕ × ℕ)) (a : Fin (ι.nA h)) :
    cylMass ι h =
      ∑ y : Fin (ι.nY h a), cylMass ι (h ++ [(a.val, y.val)]) := by
  have hterm : ∀ i, diagWeight ι i * indAgree ι (capStrat ι i) h =
      ∑ y : Fin (ι.nY h a),
        diagWeight ι i * indAgree ι (capStrat ι i) (h ++ [(a.val, y.val)]) := by
    intro i
    rw [indAgree_split ι (capStrat ι i) h a, Finset.mul_sum]
  have hinter : ∀ y : Fin (ι.nY h a),
      Summable fun i =>
        diagWeight ι i * indAgree ι (capStrat ι i) (h ++ [(a.val, y.val)]) :=
    fun y => cyl_summable ι _
  calc
    cylMass ι h = ∑' i, diagWeight ι i * indAgree ι (capStrat ι i) h := rfl
    _ = ∑' i, ∑ y : Fin (ι.nY h a),
          diagWeight ι i * indAgree ι (capStrat ι i) (h ++ [(a.val, y.val)]) := by
      exact tsum_congr hterm
    _ = ∑ y : Fin (ι.nY h a), ∑' i,
          diagWeight ι i * indAgree ι (capStrat ι i) (h ++ [(a.val, y.val)]) :=
      Summable.tsum_finsetSum (fun y _ => hinter y)
    _ = ∑ y : Fin (ι.nY h a), cylMass ι (h ++ [(a.val, y.val)]) := by
      simp [cylMass]

/-- Residual cylinder mass `p(h) - ν(E_h)`. Nonnegative, and conserved by every action. -/
noncomputable def resMass (ι : ITree) (h : List (ℕ × ℕ)) : ℝ :=
  pathMass ι h - cylMass ι h

theorem resMass_nonneg (ι : ITree) (h : List (ℕ × ℕ)) : 0 ≤ resMass ι h :=
  sub_nonneg.mpr (cylMass_le_path ι h)

theorem resMass_root (ι : ITree) : resMass ι [] = 1 - atomQ ι := by
  simp [resMass, pathMass_nil, cylMass_root]

theorem resMass_split (ι : ITree) (h : List (ℕ × ℕ)) (a : Fin (ι.nA h)) :
    ∑ y : Fin (ι.nY h a), resMass ι (h ++ [(a.val, y.val)]) = resMass ι h := by
  simp only [resMass]
  rw [Finset.sum_sub_distrib, pathMass_sum_child, cylMass_split]

/-! ## Residual ratios and cylinder exactness

`resRatioStep h p` is a one-step probability ratio. Where `resMass h` is
positive it is the residual child over the residual parent. Where `resMass h`
vanishes it is the original kernel at `h`, which is already normalised, rather
than the zero function. Every action therefore satisfies

```
∑ y, resRatioStep h (a, y) = 1.
```

`resCyl h` is the product of those ratios along `h`, with value `1` at the
root. A ratio at a history of residual zero is multiplied, in
`resMass_eq_root_mul`, by a factor that is already zero, so

```
resMass h = resMass [] * resCyl h
```

holds for every history either way, and so does

```
cylMass h + resMass [] * resCyl h = pathMass h.
```

This is an identity of real cylinder functions. It is not a measure on the
strategy space, and it is not the equality of ordinary and causal atomic
capacities.
-/

/-- The history before its last step. -/
def initHist (h : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  h.reverse.tail.reverse

theorem initHist_append (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    initHist (h ++ [p]) = h := by
  simp [initHist, List.reverse_append, List.tail_cons]

/-- One-step ratio. The original kernel replaces the residual ratio wherever
the residual vanishes, so the ratio of every action remains a probability. -/
noncomputable def resRatioStep (ι : ITree) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) : ℝ :=
  if resMass ι h = 0 then kernRaw ι h p.1 p.2
  else resMass ι (h ++ [p]) / resMass ι h

/-- Product of residual ratios, computed on the reversed history. -/
noncomputable def resCylRev (ι : ITree) : List (ℕ × ℕ) → ℝ
  | [] => 1
  | p :: t => resRatioStep ι t.reverse p * resCylRev ι t

/-- Product of residual ratios along a history. `resCyl [] = 1`. -/
noncomputable def resCyl (ι : ITree) (h : List (ℕ × ℕ)) : ℝ :=
  resCylRev ι h.reverse

theorem resCyl_nil (ι : ITree) : resCyl ι [] = 1 := by
  simp [resCyl, resCylRev]

theorem resCyl_append (ι : ITree) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    resCyl ι (h ++ [p]) = resRatioStep ι h p * resCyl ι h := by
  simp [resCyl, resCylRev, List.reverse_append]

theorem resRatioStep_of_zero {ι : ITree} {h : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (hz : resMass ι h = 0) :
    resRatioStep ι h p = kernRaw ι h p.1 p.2 := by
  simp [resRatioStep, hz]

theorem resRatioStep_of_pos {ι : ITree} {h : List (ℕ × ℕ)} {p : ℕ × ℕ}
    (hz : resMass ι h ≠ 0) :
    resRatioStep ι h p = resMass ι (h ++ [p]) / resMass ι h := by
  simp [resRatioStep, hz]

theorem resRatioStep_nonneg (ι : ITree) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    0 ≤ resRatioStep ι h p := by
  by_cases hz : resMass ι h = 0
  · rw [resRatioStep_of_zero hz]
    exact kernRaw_nonneg ι h p.1 p.2
  · rw [resRatioStep_of_pos hz]
    exact div_nonneg (resMass_nonneg ι _) (resMass_nonneg ι h)

/-- Every action has residual ratios that sum to one. On a positive residual
this is conservation of `resMass`. On a zero residual it is `ksum` of the
original kernel. -/
theorem resRatioStep_sum (ι : ITree) (h : List (ℕ × ℕ)) (a : Fin (ι.nA h)) :
    ∑ y : Fin (ι.nY h a), resRatioStep ι h (a.val, y.val) = 1 := by
  by_cases hz : resMass ι h = 0
  · have hkern : ∀ y : Fin (ι.nY h a),
        resRatioStep ι h (a.val, y.val) = ι.kern h a y := by
      intro y
      rw [resRatioStep_of_zero hz, kernRaw_fin]
    simp_rw [hkern]
    exact ι.ksum h a
  · have hstep : ∀ y : Fin (ι.nY h a),
        resRatioStep ι h (a.val, y.val) =
          resMass ι (h ++ [(a.val, y.val)]) / resMass ι h :=
      fun y => resRatioStep_of_pos hz
    simp_rw [hstep, ← Finset.sum_div, resMass_split ι h a]
    exact div_self hz

theorem resCyl_nonneg (ι : ITree) : ∀ h, 0 ≤ resCyl ι h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => rw [resCyl_nil]; norm_num
  | append_singleton t q ih =>
      rw [resCyl_append]
      exact mul_nonneg (resRatioStep_nonneg ι t q) ih

/-- A residual child is at most its parent, by conservation over the valid
outputs of any action. Invalid steps have residual zero. -/
theorem resMass_child_le (ι : ITree) (h : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    resMass ι (h ++ [p]) ≤ resMass ι h := by
  by_cases ha : p.1 < ι.nA h
  · let a : Fin (ι.nA h) := ⟨p.1, ha⟩
    by_cases hy : p.2 < ι.nY h a
    · let y : Fin (ι.nY h a) := ⟨p.2, hy⟩
      have hmem : resMass ι (h ++ [p]) =
          resMass ι (h ++ [(a.val, y.val)]) := rfl
      have hsum := resMass_split ι h a
      have hle : resMass ι (h ++ [(a.val, y.val)]) ≤
          ∑ z : Fin (ι.nY h a), resMass ι (h ++ [(a.val, z.val)]) :=
        Finset.single_le_sum (fun z _ => resMass_nonneg ι (h ++ [(a.val, z.val)]))
          (Finset.mem_univ y)
      rw [hmem]
      exact le_trans hle (le_of_eq hsum)
    · have : resMass ι (h ++ [p]) = 0 := by
        have hpm : pathMass ι (h ++ [p]) = 0 := by
          rw [pathMass, pm_append_one ι [] h p.1 p.2]
          unfold kernRaw
          split_ifs with h1 h2
          · exact absurd h2 hy
          · exact mul_zero _
          · exact mul_zero _
        have hcyl : cylMass ι (h ++ [p]) = 0 := by
          have hle := cylMass_le_path ι (h ++ [p])
          exact le_antisymm (le_trans hle (le_of_eq hpm)) (by
            have : 0 ≤ cylMass ι (h ++ [p]) := by
              have hsum := cyl_summable ι (h ++ [p])
              exact tsum_nonneg (cyl_term_nonneg ι (h ++ [p]))
            exact this)
        simp [resMass, hpm, hcyl]
      rw [this]
      exact resMass_nonneg ι h
  · have : resMass ι (h ++ [p]) = 0 := by
      have hpm : pathMass ι (h ++ [p]) = 0 := by
        rw [pathMass, pm_append_one ι [] h p.1 p.2]
        unfold kernRaw
        rw [List.nil_append]
        simp [ha]
      have hcyl : cylMass ι (h ++ [p]) = 0 := by
        have hle := cylMass_le_path ι (h ++ [p])
        exact le_antisymm (le_trans hle (le_of_eq hpm))
          (tsum_nonneg (cyl_term_nonneg ι (h ++ [p])))
      simp [resMass, hpm, hcyl]
    rw [this]
    exact resMass_nonneg ι h

theorem resMass_eq_root_mul (ι : ITree) :
    ∀ h, resMass ι h = resMass ι [] * resCyl ι h := by
  intro h
  induction h using List.reverseRecOn with
  | nil => rw [resCyl_nil]; norm_num
  | append_singleton t q ih =>
      rw [resCyl_append]
      by_cases hz : resMass ι t = 0
      · have hzero : resMass ι (t ++ [q]) = 0 :=
          le_antisymm (le_trans (resMass_child_le ι t q) (le_of_eq hz))
            (resMass_nonneg ι _)
        -- The parent product is already zero, so the fallback ratio is irrelevant.
        rw [mul_left_comm (resMass ι []) (resRatioStep ι t q) (resCyl ι t),
            ← ih, hz, mul_zero]
        exact hzero
      · have hstep : resRatioStep ι t q = resMass ι (t ++ [q]) / resMass ι t :=
          resRatioStep_of_pos hz
        rw [hstep]
        have hrewrite : resMass ι [] * (resMass ι (t ++ [q]) / resMass ι t * resCyl ι t) =
            resMass ι (t ++ [q]) * (resMass ι [] * resCyl ι t) / resMass ι t := by
          rw [div_mul_eq_mul_div, mul_div_assoc,
            mul_left_comm (resMass ι []) (resMass ι (t ++ [q])),
            (mul_div_assoc (resMass ι []) (resCyl ι t) (resMass ι t)).symm,
            (mul_div_assoc (resMass ι (t ++ [q]))
              (resMass ι [] * resCyl ι t) (resMass ι t)).symm]
        rw [hrewrite, ← ih]
        exact (mul_div_cancel_right₀ _ hz).symm

theorem exact_split (ι : ITree) (h : List (ℕ × ℕ)) :
    cylMass ι h + resMass ι [] * resCyl ι h = pathMass ι h := by
  rw [← resMass_eq_root_mul ι h]
  simp [resMass]

#print axioms resRatioStep_sum
#print axioms resMass_child_le
#print axioms resMass_eq_root_mul
#print axioms exact_split
#print axioms cap_coord_tendsto
#print axioms cyl_partial_le
#print axioms cylMass_le_path
#print axioms cylMass_root
#print axioms cylMass_split
#print axioms resMass_split



/-! ## Atomic measure from the diagonal limit

`atomMeasure` is the countable sum of weighted Diracs of `capStrat`.
`Completion.atomMeasure_univ` and `Completion.atomMeasure_cylinder`, in
`MeasureCompletion.lean`, identify its total mass with `atomQ` and its
cylinder masses with `cylMass`.
-/

noncomputable def atomMeasure (ι : ITree) : Measure (IStrategy ι) :=
  Measure.sum fun i => ENNReal.ofReal (diagWeight ι i) • Measure.dirac (capStrat ι i)

end CausalSpectrum
end

/-
Residual flow of a coupling. The realizable atoms are extracted from the
probability field. What remains is a nonnegative flow whose root is the
inconsistent mass and whose leaves are the inconsistent marginals.

The pruned tree and the leaf transport are in `CausalSeed/Transport.lean`.
The inequality `causalMin T ≤ H(Γ) + gapSup · Γ(B)` is
`causalMin_le_penalised` in `CausalSeed/Identity.lean`.
-/
import CausalSeed.Penalty

noncomputable section
open Classical
namespace CausalSpectrum

def defaultStrategy : (T : Tree) → Strategy T
  | .leaf => PUnit.unit
  | .node _ _ _ hY _ _ _ child =>
      (fun a => ⟨0, hY a⟩, fun a y => defaultStrategy (child a y))

/-- A policy that follows one terminal history and is arbitrary off that path. -/
def policyOfLeaf : {T : Tree} → Leaf T → Policy T
  | .leaf, _ => PUnit.unit
  | .node _ _ nY _ _ _ _ child, ⟨a, y, ℓ⟩ =>
      (a, fun b z =>
        dite (a = b)
          (fun hb =>
            (Eq.rec
              (motive := fun (b : Fin _) (_ : a = b) =>
                (z : Fin (nY b)) → Policy (child b z))
              (fun z =>
                dite (y = z)
                  (fun hz =>
                    Eq.rec
                      (motive := fun (z : Fin (nY a)) (_ : y = z) => Policy (child a z))
                      (policyOfLeaf ℓ) hz)
                  (fun _ => defaultPolicy (child a z)))
              hb) z)
          (fun _ => defaultPolicy (child b z)))

theorem policyOfLeaf_compatible : ∀ {T : Tree} (ℓ : Leaf T),
    CompatiblePolicy ℓ (policyOfLeaf ℓ)
  | .leaf, ℓ => by
      cases ℓ
      trivial
  | .node nA hA nY hY K Kpos Ksum child, ⟨a, y, ℓ⟩ => by
      refine ⟨rfl, ?_⟩
      simpa [policyOfLeaf] using policyOfLeaf_compatible ℓ

/-! Subtract a list of strategy atoms. -/

def extractList {T : Tree} : Field T → List (Atom T) → Field T
  | r, [] => r
  | r, a :: tail => extractList (extract r a.2 a.1) tail

theorem representedLeaf_nil {T : Tree} (ℓ : Leaf T) :
    representedLeaf ([] : List (Atom T)) ℓ = 0 := by
  simp [representedLeaf]

theorem representedLeaf_cons {T : Tree} (a : Atom T) (tail : List (Atom T)) (ℓ : Leaf T) :
    representedLeaf (a :: tail) ℓ =
      (if CompatibleStrategy ℓ a.2 then a.1 else 0) + representedLeaf tail ℓ := by
  classical
  simp [representedLeaf, List.map_cons, List.sum_cons]

theorem root_extractList {T : Tree} (r : Field T) (atoms : List (Atom T)) :
    Field.root (extractList r atoms) = Field.root r - totalWeight atoms := by
  induction atoms generalizing r with
  | nil => simp [extractList, totalWeight]
  | cons a tail ih =>
      rw [extractList, ih, root_extract]
      simp [totalWeight, List.map_cons, List.sum_cons]
      ring

theorem leafValue_extractList {T : Tree} (r : Field T) (atoms : List (Atom T))
    (ℓ : Leaf T) :
    leafValue (extractList r atoms) ℓ =
      leafValue r ℓ - representedLeaf atoms ℓ := by
  classical
  induction atoms generalizing r with
  | nil => simp [extractList, representedLeaf]
  | cons a tail ih =>
      rw [extractList, ih, leafValue_extract, representedLeaf_cons]
      ring

theorem extractList_isFlow {T : Tree} (r : Field T) (atoms : List (Atom T))
    (hf : Field.IsFlow r) : Field.IsFlow (extractList r atoms) := by
  induction atoms generalizing r with
  | nil => simpa [extractList] using hf
  | cons a tail ih =>
      exact ih (extract r a.2 a.1) (extract_isFlow r a.2 a.1 hf)

theorem le_strategyFloor_of_compatible {T : Tree} (r : Field T) (d : Strategy T)
    {w : ℝ} (h : ∀ ℓ : Leaf T, CompatibleStrategy ℓ d → w ≤ leafValue r ℓ) :
    w ≤ strategyFloor r d := by
  obtain ⟨ℓ, hc, he⟩ := strategyFloor_attained_leaf r d
  rw [← he]
  exact h ℓ hc

private theorem representedLeaf_nonneg {T : Tree} (atoms : List (Atom T))
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1) (ℓ : Leaf T) : 0 ≤ representedLeaf atoms ℓ := by
  induction atoms with
  | nil => simp [representedLeaf]
  | cons a tail ih =>
      rw [representedLeaf_cons]
      refine add_nonneg ?_ (ih fun b hb => hnn b (List.mem_cons_of_mem a hb))
      split_ifs
      · exact hnn a (by simp)
      · exact le_rfl

theorem extractList_nonneg {T : Tree} (r : Field T) (atoms : List (Atom T))
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    (hnn : ∀ a ∈ atoms, 0 ≤ a.1)
    (hdom : ∀ ℓ : Leaf T, representedLeaf atoms ℓ ≤ leafValue r ℓ) :
    Field.Nonneg (extractList r atoms) := by
  induction atoms generalizing r with
  | nil => simpa [extractList] using hn
  | cons a tail ih =>
      have hfloor : a.1 ≤ strategyFloor r a.2 := by
        refine le_strategyFloor_of_compatible r a.2 ?_
        intro ℓ hc
        have hrep := hdom ℓ
        rw [representedLeaf_cons, ite_eq_left hc] at hrep
        have htail := representedLeaf_nonneg tail (fun b hb => hnn b (by simp [hb])) ℓ
        linarith
      have hnext : Field.Nonneg (extract r a.2 a.1) :=
        extract_nonneg r a.2 a.1 hf hn hfloor
      have hdom' : ∀ ℓ, representedLeaf tail ℓ ≤ leafValue (extract r a.2 a.1) ℓ := by
        intro ℓ
        rw [leafValue_extract]
        have hrep := hdom ℓ
        rw [representedLeaf_cons] at hrep
        by_cases hc : CompatibleStrategy ℓ a.2
        · rw [ite_eq_left hc] at hrep ⊢
          linarith
        · rw [ite_eq_right hc] at hrep ⊢
          linarith
      exact ih (extract r a.2 a.1) (extract_isFlow r a.2 a.1 hf) hnext
        (fun b hb => hnn b (by simp [hb])) hdom'

/-! Realizable atoms of one coupling. -/

noncomputable def goodList {T : Tree} (Γ : Coupling T) : List (Assignment T) :=
  (Finset.univ.filter fun α : Assignment T => realizable α ∧ 0 < Γ.mass α).toList

noncomputable def chosenOf {T : Tree} (α : Assignment T) : Strategy T :=
  if h : realizable α then chosenStrategy α h else defaultStrategy T

noncomputable def goodAtoms {T : Tree} (Γ : Coupling T) : List (Atom T) :=
  (goodList Γ).map fun α => (Γ.mass α, chosenOf α)

theorem goodList_mem {T : Tree} {Γ : Coupling T} {α : Assignment T} :
    α ∈ goodList Γ ↔ realizable α ∧ 0 < Γ.mass α := by
  simp [goodList, Finset.mem_toList, Finset.mem_filter]

theorem chosenOf_realizes {T : Tree} {α : Assignment T} (h : realizable α) :
    realizes (chosenOf α) = α := by
  simp [chosenOf, h, realizes_chosen]

theorem goodAtoms_pos {T : Tree} (Γ : Coupling T) :
    ∀ a ∈ goodAtoms Γ, 0 < a.1 := by
  intro a ha
  simp only [goodAtoms, List.mem_map] at ha
  rcases ha with ⟨α, hα, rfl⟩
  exact (goodList_mem.mp hα).2

theorem list_sum_finset {α : Type} [DecidableEq α] (s : Finset α) (f : α → ℝ) :
    (s.toList.map f).sum = ∑ x ∈ s, f x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      have hperm : List.Perm ((insert a s).toList.map f) ((a :: s.toList).map f) :=
        List.Perm.map _ (Finset.toList_insert ha)
      rw [List.Perm.sum_eq hperm, List.map_cons, List.sum_cons, ih]

theorem totalWeight_good {T : Tree} (Γ : Coupling T) :
    totalWeight (goodAtoms Γ) = 1 - Γ.badMass := by
  classical
  have hlist : totalWeight (goodAtoms Γ) =
      ∑ α ∈ Finset.univ.filter fun α : Assignment T => realizable α ∧ 0 < Γ.mass α,
        Γ.mass α := by
    simp only [totalWeight, goodAtoms, goodList, List.map_map]
    exact list_sum_finset _ _
  rw [hlist, Finset.sum_filter]
  have hsame : ∑ α : Assignment T, (if realizable α ∧ 0 < Γ.mass α then Γ.mass α else 0) =
      ∑ α : Assignment T, (if realizable α then Γ.mass α else 0) := by
    refine Finset.sum_congr rfl fun α _ => ?_
    by_cases hr : realizable α
    · by_cases hp : 0 < Γ.mass α
      · simp [hr, hp]
      · have hz : Γ.mass α = 0 := le_antisymm (le_of_not_gt hp) (Γ.nonneg α)
        simp [hr, hp, hz]
    · simp [hr]
  rw [hsame]
  exact goodMass_eq Γ

theorem transcript_good {T : Tree} (Γ : Coupling T) (π : Policy T) (ℓ : Leaf T) :
    transcriptWeight (goodAtoms Γ) π ℓ =
      ∑ α : Assignment T, if realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0 := by
  classical
  have hlist : transcriptWeight (goodAtoms Γ) π ℓ =
      ∑ α ∈ Finset.univ.filter fun α : Assignment T => realizable α ∧ 0 < Γ.mass α,
        if run (chosenOf α) π = ℓ then Γ.mass α else 0 := by
    simp only [transcriptWeight, goodAtoms, goodList, List.map_map]
    exact list_sum_finset _ _
  rw [hlist, Finset.sum_filter]
  refine Finset.sum_congr rfl fun α _ => ?_
  by_cases hr : realizable α
  · by_cases hp : 0 < Γ.mass α
    · simp only [hr, hp, true_and, ite_true]
      have hrun : run (chosenOf α) π = (α π).1 := by
        have hpair := congrArg Subtype.val (congrFun (chosenOf_realizes hr) π)
        simpa [realizes] using hpair
      by_cases hℓ : (α π).1 = ℓ
      · simp [hrun, hℓ]
      · simp [hrun, hℓ]
    · have hz : Γ.mass α = 0 := le_antisymm (le_of_not_gt hp) (Γ.nonneg α)
      simp [hr, hp, hz]
  · simp [hr]

theorem represented_good {T : Tree} (Γ : Coupling T) (ℓ : Leaf T) :
    representedLeaf (goodAtoms Γ) ℓ =
      ∑ α : Assignment T,
        if realizable α ∧ (α (policyOfLeaf ℓ)).1 = ℓ then Γ.mass α else 0 := by
  have hc := policyOfLeaf_compatible ℓ
  have htr := transcript_good Γ (policyOfLeaf ℓ) ℓ
  rw [transcriptWeight_eq, if_pos hc] at htr
  exact htr

theorem represented_good_le {T : Tree} (Γ : Coupling T) (ℓ : Leaf T) :
    representedLeaf (goodAtoms Γ) ℓ ≤ leafMass ℓ := by
  rw [represented_good]
  let π := policyOfLeaf ℓ
  have hc := policyOfLeaf_compatible ℓ
  have hm := Γ.marginal π ℓ hc
  have hle : ∑ α : Assignment T,
      (if realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) ≤
      ∑ α : Assignment T, (if (α π).1 = ℓ then Γ.mass α else 0) := by
    refine Finset.sum_le_sum fun α _ => ?_
    by_cases h : realizable α ∧ (α π).1 = ℓ
    · simp [h]
    · simp only [h, ite_false]
      split_ifs
      · exact Γ.nonneg α
      · exact le_rfl
  exact le_trans hle (le_of_eq hm)

noncomputable def residualField {T : Tree} (Γ : Coupling T) : Field T :=
  extractList (Field.p T) (goodAtoms Γ)

theorem residual_isFlow {T : Tree} (Γ : Coupling T) :
    Field.IsFlow (residualField Γ) :=
  extractList_isFlow (Field.p T) (goodAtoms Γ) (Field.p_isFlow T)

theorem residual_nonneg {T : Tree} (Γ : Coupling T) :
    Field.Nonneg (residualField Γ) := by
  refine extractList_nonneg (Field.p T) (goodAtoms Γ) (Field.p_isFlow T) (Field.p_nonneg T)
    (fun a ha => (goodAtoms_pos Γ a ha).le) ?_
  intro ℓ
  rw [show leafValue (Field.p T) ℓ = leafMass ℓ by
    simpa [Field.p] using leafValue_probability T 1 ℓ]
  exact represented_good_le Γ ℓ

theorem residual_root {T : Tree} (Γ : Coupling T) :
    Field.root (residualField Γ) = Γ.badMass := by
  rw [residualField, root_extractList, Field.root_p, totalWeight_good]
  ring

theorem residual_leaf {T : Tree} (Γ : Coupling T) (ℓ : Leaf T) :
    leafValue (residualField Γ) ℓ =
      leafMass ℓ - representedLeaf (goodAtoms Γ) ℓ := by
  have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
    simpa [Field.p] using leafValue_probability T 1 ℓ
  rw [residualField, leafValue_extractList, hp]

theorem residual_eq_bad {T : Tree} (Γ : Coupling T) (π : Policy T) (ℓ : Leaf T)
    (hc : CompatiblePolicy ℓ π) :
    leafValue (residualField Γ) ℓ =
      ∑ α : Assignment T, if ¬ realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0 := by
  classical
  rw [residual_leaf]
  have hfull := Γ.marginal π ℓ hc
  have hgood := transcript_good Γ π ℓ
  rw [transcriptWeight_eq, if_pos hc] at hgood
  have hsplit : ∀ α,
      (if (α π).1 = ℓ then Γ.mass α else 0) =
        (if realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) +
          (if ¬ realizable α ∧ (α π).1 = ℓ then Γ.mass α else 0) := by
    intro α
    by_cases hℓ : (α π).1 = ℓ
    · by_cases hr : realizable α
      · simp [hℓ, hr]
      · simp [hℓ, hr]
    · simp [hℓ]
  have hsum := Finset.sum_congr rfl fun α (_ : α ∈ Finset.univ) => hsplit α
  rw [Finset.sum_add_distrib] at hsum
  linarith [hfull, hgood, hsum]

/-! Prune zero branches. `flowTree` is the same construction as `pruned`. -/

noncomputable def flowTree : {T : Tree} → (r : Field T) → Field.IsFlow r → Field.Nonneg r → Tree
  | .leaf, _, _, _ => .leaf
  | .node nA hA nY _ K _ _ child, r, hf, hn =>
      if hr : 0 < Field.root r then
        Tree.node nA hA
          (fun a => (supportOf (fun y => Field.root (r.2 a y))).card)
          (fun a => supportOf_card_pos
            (by simpa [Field.root] using (lt_of_lt_of_eq hr (hf.1 a).symm))
            (fun y => (hn.2 a y).root_nonneg))
          (fun a i =>
            Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) / Field.root r)
          (fun a i => by
            have hmem :=
              ((supportOf (fun y => Field.root (r.2 a y))).equivFin.symm i).2
            have hy : 0 < Field.root
                (r.2 a (((supportOf (fun y => Field.root (r.2 a y))).equivFin.symm i).1)) :=
              (Finset.mem_filter.mp hmem).2
            simpa [yOf] using div_pos hy hr)
          (fun a => by
            have hdiv : ∑ i,
                Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) / Field.root r =
                (∑ i, Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))) /
                  Field.root r := by
              simp_rw [div_eq_mul_inv, ← Finset.sum_mul]
            rw [hdiv, sum_yOf (fun y => Field.root (r.2 a y)) (fun y => (hn.2 a y).root_nonneg)]
            have hflow : ∑ y, Field.root (r.2 a y) = Field.root r := by
              simpa [Field.root] using hf.1 a
            rw [hflow]
            field_simp)
          (fun a i =>
            flowTree (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
              (hf.2 a _) (hn.2 a _))
      else
        .leaf

theorem flowLeafMass_cast
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {r : Field (Tree.node nA hA nY hY K Kpos Ksum child)}
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    {a : Fin nA} {y1 y2 : Fin (nY a)} (h : y1 = y2)
    (ℓ : Leaf (flowTree (r.2 a y2) (hf.2 a y2) (hn.2 a y2))) :
    leafMass (Eq.rec (motive := fun z _ =>
        Leaf (flowTree (r.2 a z) (hf.2 a z) (hn.2 a z))) ℓ h.symm) =
      leafMass ℓ := by
  subst h
  rfl

/-- A positive original leaf, read as a leaf of the pruned tree, together with
the identity `leafMass · root = leaf value`. -/
noncomputable def leafPack : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → (hr : 0 < Field.root r) → (ℓ : Leaf T) →
    (hp : 0 < leafValue r ℓ) →
    { idx : Leaf (flowTree r hf hn) // leafMass idx * Field.root r = leafValue r ℓ }
  | .leaf, r, _, _, _, ℓ, hp => by
      cases ℓ
      refine ⟨PUnit.unit, ?_⟩
      show (1 : ℝ) * r = r
      ring
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨a, y, ℓ⟩, hp => by
      have hchild : 0 < leafValue (r.2 a y) ℓ := by simpa [leafValue] using hp
      have hroot : 0 < Field.root (r.2 a y) :=
        lt_of_lt_of_le hchild (leafValue_le_root _ (hf.2 a y) (hn.2 a y) ℓ)
      have hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) := by
        simp [supportOf, hroot]
      let i := indexOf (fun z => Field.root (r.2 a z)) hy
      have hyOf : yOf (fun z => Field.root (r.2 a z)) i = y := yOf_indexOf _ hy
      have childPack := leafPack (r.2 a y) (hf.2 a y) (hn.2 a y) hroot ℓ hchild
      let ℓc :=
        Eq.rec (motive := fun z _ =>
            Leaf (flowTree (r.2 a z) (hf.2 a z) (hn.2 a z)))
          childPack.1 hyOf.symm
      have hL : leafMass ℓc = leafMass childPack.1 :=
        flowLeafMass_cast hf hn hyOf childPack.1
      have hR : Field.root (r.2 a (yOf (fun z => Field.root (r.2 a z)) i)) =
          Field.root (r.2 a y) := congrArg (fun z => Field.root (r.2 a z)) hyOf
      dsimp only [flowTree]
      rw [dite_eq_left hr]
      refine ⟨⟨a, i, ℓc⟩, ?_⟩
      simp only [leafMass, leafValue]
      calc
        (Field.root (r.2 a (yOf (fun z => Field.root (r.2 a z)) i)) / Field.root r) *
              leafMass ℓc * Field.root r
            = leafMass ℓc * Field.root (r.2 a (yOf (fun z => Field.root (r.2 a z)) i)) := by
              field_simp [ne_of_gt hr, ne_of_gt (lt_of_lt_of_eq hroot hR.symm)]
        _ = leafMass childPack.1 * Field.root (r.2 a y) := by rw [hL, hR]
        _ = leafValue (r.2 a y) ℓ := childPack.2
        _ = leafValue r ⟨a, y, ℓ⟩ := by simp [leafValue]

noncomputable def leafPre {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r) (ℓ : Leaf T)
    (hp : 0 < leafValue r ℓ) : Leaf (flowTree r hf hn) :=
  (leafPack r hf hn hr ℓ hp).1

theorem leafPre_scale {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r) (ℓ : Leaf T)
    (hp : 0 < leafValue r ℓ) :
    leafMass (leafPre r hf hn hr ℓ hp) * Field.root r = leafValue r ℓ :=
  (leafPack r hf hn hr ℓ hp).2

/-- Pruned leaf, read back on the original tree. -/
noncomputable def flowLeaf : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → Leaf (flowTree r hf hn) → Leaf T
  | .leaf, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ _, r, hf, hn, ℓ => by
      by_cases hr : 0 < Field.root r
      · dsimp only [flowTree] at ℓ
        rw [dite_eq_left hr] at ℓ
        rcases ℓ with ⟨a, i, ℓc⟩
        exact ⟨a, yOf (fun z => Field.root (r.2 a z)) i,
          flowLeaf (r.2 a (yOf (fun z => Field.root (r.2 a z)) i))
            (hf.2 a _) (hn.2 a _) ℓc⟩
      · exact defaultLeaf _

noncomputable def strategyEmb : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → Strategy (flowTree r hf hn) → Strategy T
  | .leaf, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ child, r, hf, hn, d => by
      by_cases hr : 0 < Field.root r
      · dsimp only [flowTree] at d
        rw [dite_eq_left hr] at d
        rcases d with ⟨out, cont⟩
        refine ⟨fun a => yOf (fun z => Field.root (r.2 a z)) (out a), fun a y => ?_⟩
        by_cases hy : y ∈ supportOf (fun z => Field.root (r.2 a z))
        · let i := indexOf (fun z => Field.root (r.2 a z)) hy
          have hyOf : yOf (fun z => Field.root (r.2 a z)) i = y := yOf_indexOf _ hy
          exact hyOf ▸ strategyEmb (r.2 a (yOf (fun z => Field.root (r.2 a z)) i))
            (hf.2 a _) (hn.2 a _) (cont a i)
        · exact defaultStrategy (child a y)
      · exact defaultStrategy _

noncomputable def policyEmb : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → Policy (flowTree r hf hn) → Policy T
  | .leaf, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ child, r, hf, hn, π => by
      by_cases hr : 0 < Field.root r
      · dsimp only [flowTree] at π
        rw [dite_eq_left hr] at π
        rcases π with ⟨a0, cont⟩
        refine ⟨a0, fun a y => ?_⟩
        by_cases hy : y ∈ supportOf (fun z => Field.root (r.2 a z))
        · let i := indexOf (fun z => Field.root (r.2 a z)) hy
          have hyOf : yOf (fun z => Field.root (r.2 a z)) i = y := yOf_indexOf _ hy
          exact hyOf ▸ policyEmb (r.2 a (yOf (fun z => Field.root (r.2 a z)) i))
            (hf.2 a _) (hn.2 a _) (cont a i)
        · exact defaultPolicy (child a y)
      · exact defaultPolicy _

theorem yOf_inj {n : ℕ} (mass : Fin n → ℝ) {i j : Fin (supportOf mass).card}
    (h : yOf mass i = yOf mass j) : i = j := by
  apply (supportOf mass).equivFin.symm.injective
  exact Subtype.ext h

end CausalSpectrum

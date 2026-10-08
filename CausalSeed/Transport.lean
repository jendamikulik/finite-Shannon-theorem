import CausalSeed.Close

noncomputable section
open Classical
namespace CausalSpectrum

theorem yOf_mem {n : ℕ} (mass : Fin n → ℝ) (i : Fin (supportOf mass).card) :
    yOf mass i ∈ supportOf mass :=
  ((supportOf mass).equivFin.symm i).2

theorem yOf_pos {n : ℕ} (mass : Fin n → ℝ) (i : Fin (supportOf mass).card) :
    0 < mass (yOf mass i) :=
  (Finset.mem_filter.mp (yOf_mem mass i)).2

noncomputable def prunedTree : {T : Tree} → (r : Field T) → Field.IsFlow r →
    Field.Nonneg r → (hr : 0 < Field.root r) → Tree
  | .leaf, _, _, _, _ => .leaf
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr =>
      Tree.node nA hA
        (fun a => (supportOf (fun y => Field.root (r.2 a y))).card)
        (fun a => supportOf_card_pos
          (by simpa [Field.root] using (lt_of_lt_of_eq hr (hf.1 a).symm))
          (fun y => (hn.2 a y).root_nonneg))
        (fun a i =>
          Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) / Field.root r)
        (fun a i => div_pos (yOf_pos (fun y => Field.root (r.2 a y)) i) hr)
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
          prunedTree (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
            (hf.2 a _) (hn.2 a _) (yOf_pos (fun y => Field.root (r.2 a y)) i))

noncomputable def leafOut : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → (hr : 0 < Field.root r) → Leaf (prunedTree r hf hn hr) → Leaf T
  | .leaf, _, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ _, r, hf, hn, hr, ⟨a, i, ℓc⟩ =>
      ⟨a, yOf (fun y => Field.root (r.2 a y)) i,
        leafOut (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
          (hf.2 a _) (hn.2 a _) (yOf_pos _ i) ℓc⟩

noncomputable def leafIn : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → (hr : 0 < Field.root r) → (ℓ : Leaf T) →
    (hp : 0 < leafValue r ℓ) → Leaf (prunedTree r hf hn hr)
  | .leaf, _, _, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ _, r, hf, hn, hr, ⟨a, y, ℓ⟩, hp =>
      let hchild : 0 < leafValue (r.2 a y) ℓ := by simpa [leafValue] using hp
      let hrooty : 0 < Field.root (r.2 a y) :=
        lt_of_lt_of_le hchild (leafValue_le_root _ (hf.2 a y) (hn.2 a y) ℓ)
      let hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) := by simp [supportOf, hrooty]
      let i := indexOf (fun z => Field.root (r.2 a z)) hy
      let hyOf : yOf (fun z => Field.root (r.2 a z)) i = y := yOf_indexOf _ hy
      let ℓc := leafIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild
      ⟨a, i,
        Eq.rec (motive := fun z h =>
          Leaf (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ hrooty)))
          ℓc hyOf.symm⟩

theorem leafOut_pos : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r)
    (ℓ : Leaf (prunedTree r hf hn hr)),
    0 < leafValue r (leafOut r hf hn hr ℓ)
  | .leaf, r, _, _, hr, ℓ => by
      cases ℓ
      simpa [leafOut, leafValue] using hr
  | .node _ _ _ _ _ _ _ _, r, hf, hn, hr, ⟨a, i, ℓc⟩ => by
      have ih := leafOut_pos
        (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
        (hf.2 a _) (hn.2 a _) (yOf_pos (fun y => Field.root (r.2 a y)) i) ℓc
      simpa [leafOut, leafValue] using ih

theorem leafOut_scale : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r)
    (ℓ : Leaf (prunedTree r hf hn hr)),
    leafMass ℓ * Field.root r = leafValue r (leafOut r hf hn hr ℓ)
  | .leaf, r, _, _, hr, ℓ => by
      cases ℓ
      show (1 : ℝ) * r = r
      ring
  | .node _ _ _ _ _ _ _ _, r, hf, hn, hr, ⟨a, i, ℓc⟩ => by
      have ih := leafOut_scale
        (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
        (hf.2 a _) (hn.2 a _) (yOf_pos (fun y => Field.root (r.2 a y)) i) ℓc
      simp only [prunedTree, leafMass, leafOut, leafValue]
      calc
        (Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) / Field.root r) *
              leafMass ℓc * Field.root r
            = leafMass ℓc * Field.root (r.2 a (yOf (fun y => Field.root (r.2 a y)) i)) := by
              field_simp [ne_of_gt hr, ne_of_gt (yOf_pos (fun y => Field.root (r.2 a y)) i)]
        _ = leafValue (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
              (leafOut _ _ _ _ ℓc) := ih

private theorem leafOut_eqRec
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {r : Field (Tree.node nA hA nY hY K Kpos Ksum child)}
    (hf : Field.IsFlow r) (hn : Field.Nonneg r)
    {a : Fin nA} {y1 y2 : Fin (nY a)} (h : y1 = y2)
    (hr1 : 0 < Field.root (r.2 a y1))
    (ℓ : Leaf (prunedTree (r.2 a y1) (hf.2 a y1) (hn.2 a y1) hr1)) :
    leafOut (r.2 a y2) (hf.2 a y2) (hn.2 a y2) (h ▸ hr1)
        (Eq.rec (motive := fun z h' =>
          Leaf (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h' ▸ hr1))) ℓ h)
      = h ▸ leafOut (r.2 a y1) (hf.2 a y1) (hn.2 a y1) hr1 ℓ := by
  subst h
  rfl

private theorem leaf_triple_cast
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {a : Fin nA} {y1 y2 : Fin (nY a)} (h : y1 = y2)
    (ℓ : Leaf (child a y2)) :
    (⟨a, y1, h.symm ▸ ℓ⟩ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child))
      = ⟨a, y2, ℓ⟩ := by
  subst h
  rfl

theorem leafOut_leafIn : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r) (ℓ : Leaf T)
    (hp : 0 < leafValue r ℓ),
    leafOut r hf hn hr (leafIn r hf hn hr ℓ hp) = ℓ
  | .leaf, r, hf, hn, hr, ℓ, hp => by
      cases ℓ
      rfl
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨a, y, ℓ⟩, hp => by
      dsimp only [leafIn, leafOut]
      have hchild : 0 < leafValue (r.2 a y) ℓ := hp
      have hrooty : 0 < Field.root (r.2 a y) :=
        lt_of_lt_of_le hchild (leafValue_le_root _ (hf.2 a y) (hn.2 a y) ℓ)
      have hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) := by simp [supportOf, hrooty]
      have hyOf := yOf_indexOf (fun z => Field.root (r.2 a z)) hy
      have ih := leafOut_leafIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild
      have hrec := leafOut_eqRec hf hn hyOf.symm hrooty
        (leafIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild)
      rw [ih] at hrec
      rw [hrec]
      exact leaf_triple_cast (hA := hA) (hY := hY) (K := K) (Kpos := Kpos) (Ksum := Ksum) hyOf ℓ

theorem indexOf_yOf {n : ℕ} (mass : Fin n → ℝ) (i : Fin (supportOf mass).card) :
    indexOf mass (yOf_mem mass i) = i := by
  apply (supportOf mass).equivFin.symm.injective
  apply Subtype.ext
  simpa [yOf, indexOf] using (yOf_indexOf mass (yOf_mem mass i)).symm

noncomputable def polIn : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → (hr : 0 < Field.root r) →
    Policy T → Policy (prunedTree r hf hn hr)
  | .leaf, _, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ _, r, hf, hn, hr, ⟨a0, cont⟩ =>
      ⟨a0, fun a i =>
        polIn (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
          (hf.2 a _) (hn.2 a _) (yOf_pos (fun y => Field.root (r.2 a y)) i)
          (cont a (yOf (fun y => Field.root (r.2 a y)) i))⟩

noncomputable def polOut : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → (hr : 0 < Field.root r) →
    Policy (prunedTree r hf hn hr) → Policy T
  | .leaf, _, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ child, r, hf, hn, hr, ⟨a0, cont⟩ =>
      ⟨a0, fun a y =>
        if hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) then
          let i := indexOf (fun z => Field.root (r.2 a z)) hy
          Eq.rec (motive := fun z _ => Policy (child a z))
            (polOut (r.2 a (yOf (fun z => Field.root (r.2 a z)) i))
              (hf.2 a _) (hn.2 a _) (yOf_pos _ i) (cont a i))
            (yOf_indexOf _ hy)
        else
          defaultPolicy (child a y)⟩

noncomputable def stratOut : {T : Tree} → (r : Field T) → (hf : Field.IsFlow r) →
    (hn : Field.Nonneg r) → (hr : 0 < Field.root r) →
    Strategy (prunedTree r hf hn hr) → Strategy T
  | .leaf, _, _, _, _, _ => PUnit.unit
  | .node _ _ _ _ _ _ _ child, r, hf, hn, hr, ⟨out, cont⟩ =>
      ⟨fun a => yOf (fun y => Field.root (r.2 a y)) (out a),
        fun a y =>
          if hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) then
            let i := indexOf (fun z => Field.root (r.2 a z)) hy
            Eq.rec (motive := fun z _ => Strategy (child a z))
              (stratOut (r.2 a (yOf (fun z => Field.root (r.2 a z)) i))
                (hf.2 a _) (hn.2 a _) (yOf_pos _ i) (cont a i))
              (yOf_indexOf _ hy)
          else
            defaultStrategy (child a y)⟩

theorem run_stratOut : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r)
    (d : Strategy (prunedTree r hf hn hr)) (π : Policy T),
    run (stratOut r hf hn hr d) π =
      leafOut r hf hn hr (run d (polIn r hf hn hr π))
  | .leaf, _, _, _, _, d, π => by
      cases d
      cases π
      rfl
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨out, cont⟩, ⟨a0, πc⟩ => by
      let mass : (a : Fin nA) → Fin (nY a) → ℝ := fun a y => Field.root (r.2 a y)
      have hy : yOf (mass a0) (out a0) ∈ supportOf (mass a0) := yOf_mem _ _
      have hi : indexOf (mass a0) hy = out a0 :=
        yOf_inj (mass a0) (yOf_indexOf (mass a0) hy)
      have ih := run_stratOut
        (r.2 a0 (yOf (mass a0) (out a0))) (hf.2 a0 _) (hn.2 a0 _)
        (yOf_pos (mass a0) (out a0)) (cont a0 (out a0))
        (πc a0 (yOf (mass a0) (out a0)))
      dsimp only [stratOut, polIn, run, leafOut, prunedTree]
      rw [dite_eq_left hy]
      have hrun (i : Fin (supportOf (mass a0)).card) (h : i = out a0)
          (heq : yOf (mass a0) i = yOf (mass a0) (out a0)) :
          run (Eq.rec (motive := fun z _ => Strategy (child a0 z))
              (stratOut (r.2 a0 (yOf (mass a0) i)) (hf.2 a0 _) (hn.2 a0 _)
                (yOf_pos (mass a0) i) (cont a0 i)) heq)
            (πc a0 (yOf (mass a0) (out a0))) =
            leafOut (r.2 a0 (yOf (mass a0) (out a0))) (hf.2 a0 _) (hn.2 a0 _)
              (yOf_pos (mass a0) (out a0))
              (run (cont a0 (out a0))
                (polIn (r.2 a0 (yOf (mass a0) (out a0))) (hf.2 a0 _) (hn.2 a0 _)
                  (yOf_pos (mass a0) (out a0)) (πc a0 (yOf (mass a0) (out a0))))) := by
        subst h
        exact ih
      have hinner := hrun (indexOf (mass a0) hy) hi (yOf_indexOf (mass a0) hy)
      rw [hinner]

theorem leafIn_leafOut : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r)
    (ℓ : Leaf (prunedTree r hf hn hr)),
    leafIn r hf hn hr (leafOut r hf hn hr ℓ) (leafOut_pos r hf hn hr ℓ) = ℓ
  | .leaf, _, _, _, _, ℓ => by
      cases ℓ
      rfl
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨a, i, ℓc⟩ => by
      let mass : Fin (nY a) → ℝ := fun y => Field.root (r.2 a y)
      have ih := leafIn_leafOut (r.2 a (yOf mass i)) (hf.2 a _) (hn.2 a _)
        (yOf_pos mass i) ℓc
      dsimp only [leafOut, leafIn]
      have hy : yOf mass i ∈ supportOf mass := yOf_mem mass i
      have hi : indexOf mass hy = i := indexOf_yOf mass i
      have hrun (j : Fin (supportOf mass).card) (hj : j = i)
          (heq : yOf mass i = yOf mass j) :
          (⟨a, j, Eq.rec (motive := fun z h =>
              Leaf (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ yOf_pos mass i)))
              (leafIn (r.2 a (yOf mass i)) (hf.2 a _) (hn.2 a _) (yOf_pos mass i)
                (leafOut (r.2 a (yOf mass i)) (hf.2 a _) (hn.2 a _) (yOf_pos mass i) ℓc)
                (leafOut_pos (r.2 a (yOf mass i)) (hf.2 a _) (hn.2 a _) (yOf_pos mass i) ℓc))
              heq⟩ : Leaf (prunedTree r hf hn hr)) = ⟨a, i, ℓc⟩ := by
        subst hj
        simpa [ih]
      exact hrun (indexOf mass hy) hi (yOf_indexOf mass hy).symm

theorem leafIn_polIn : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r) (ℓ : Leaf T)
    (hp : 0 < leafValue r ℓ) (π : Policy T),
    CompatiblePolicy ℓ π →
    CompatiblePolicy (leafIn r hf hn hr ℓ hp) (polIn r hf hn hr π)
  | .leaf, _, _, _, _, _, _, _, _ => trivial
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨a, y, ℓ⟩, hp, ⟨a0, cont⟩, hc => by
      rcases hc with ⟨rfl, hc⟩
      have hchild : 0 < leafValue (r.2 a y) ℓ := hp
      have hrooty : 0 < Field.root (r.2 a y) :=
        lt_of_lt_of_le hchild (leafValue_le_root _ (hf.2 a y) (hn.2 a y) ℓ)
      have hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) := by simp [supportOf, hrooty]
      have hyOf := yOf_indexOf (fun z => Field.root (r.2 a z)) hy
      have ih := leafIn_polIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild (cont a y) hc
      dsimp only [leafIn, polIn, CompatiblePolicy]
      refine ⟨rfl, ?_⟩
      have hrun (j : Fin (supportOf (fun z => Field.root (r.2 a z))).card)
          (hj : yOf (fun z => Field.root (r.2 a z)) j = y)
          (heq : y = yOf (fun z => Field.root (r.2 a z)) j) :
          CompatiblePolicy
            (Eq.rec (motive := fun z h =>
              Leaf (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ hrooty)))
              (leafIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild) heq)
            (polIn (r.2 a (yOf (fun z => Field.root (r.2 a z)) j))
              (hf.2 a _) (hn.2 a _) (yOf_pos _ j) (cont a (yOf (fun z => Field.root (r.2 a z)) j))) := by
        subst hj
        simpa [ih]
      exact hrun (indexOf (fun z => Field.root (r.2 a z)) hy) hyOf hyOf.symm

theorem leafIn_polOut : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r) (ℓ : Leaf T)
    (hp : 0 < leafValue r ℓ) (πS : Policy (prunedTree r hf hn hr)),
    CompatiblePolicy ℓ (polOut r hf hn hr πS) →
    CompatiblePolicy (leafIn r hf hn hr ℓ hp) πS
  | .leaf, _, _, _, _, _, _, _, _ => trivial
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨a, y, ℓ⟩, hp, ⟨a0, cont⟩, hc => by
      have hchild : 0 < leafValue (r.2 a y) ℓ := hp
      have hrooty : 0 < Field.root (r.2 a y) :=
        lt_of_lt_of_le hchild (leafValue_le_root _ (hf.2 a y) (hn.2 a y) ℓ)
      have hy : y ∈ supportOf (fun z => Field.root (r.2 a z)) := by simp [supportOf, hrooty]
      dsimp only [polOut, CompatiblePolicy] at hc
      rcases hc with ⟨rfl, hc⟩
      rw [dite_eq_left hy] at hc
      have hyOf := yOf_indexOf (fun z => Field.root (r.2 a z)) hy
      let j := indexOf (fun z => Field.root (r.2 a z)) hy
      have hc' : CompatiblePolicy ℓ
          (polOut (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty
            (Eq.rec (motive := fun z h =>
              Policy (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ yOf_pos _ j)))
              (cont a j) hyOf)) := by
        have hrun (k : Fin (supportOf (fun z => Field.root (r.2 a z))).card)
            (hk : yOf (fun z => Field.root (r.2 a z)) k = y)
            (heq : yOf (fun z => Field.root (r.2 a z)) k = y) :
            CompatiblePolicy ℓ
              (Eq.rec (motive := fun z _ => Policy (child a z))
                (polOut (r.2 a (yOf (fun z => Field.root (r.2 a z)) k))
                  (hf.2 a _) (hn.2 a _) (yOf_pos _ k) (cont a k)) heq) =
            CompatiblePolicy ℓ
              (polOut (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty
                (Eq.rec (motive := fun z h =>
                  Policy (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ yOf_pos _ k)))
                  (cont a k) hk)) := by
          subst hk
          rfl
        exact (hrun j hyOf hyOf).mp hc
      have ih := leafIn_polOut (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild _ hc'
      dsimp only [leafIn, CompatiblePolicy]
      refine ⟨rfl, ?_⟩
      have hback (k : Fin (supportOf (fun z => Field.root (r.2 a z))).card)
          (hk : yOf (fun z => Field.root (r.2 a z)) k = y)
          (heq : y = yOf (fun z => Field.root (r.2 a z)) k)
          (hπ : CompatiblePolicy (leafIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild)
            (Eq.rec (motive := fun z h =>
              Policy (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ yOf_pos _ k)))
              (cont a k) hk)) :
          CompatiblePolicy
            (Eq.rec (motive := fun z h =>
              Leaf (prunedTree (r.2 a z) (hf.2 a z) (hn.2 a z) (h ▸ hrooty)))
              (leafIn (r.2 a y) (hf.2 a y) (hn.2 a y) hrooty ℓ hchild) heq)
            (cont a k) := by
        subst hk
        exact hπ
      exact hback j hyOf hyOf.symm ih

theorem leafOut_polOut : ∀ {T : Tree} (r : Field T) (hf : Field.IsFlow r)
    (hn : Field.Nonneg r) (hr : 0 < Field.root r)
    (ℓS : Leaf (prunedTree r hf hn hr)) (πS : Policy (prunedTree r hf hn hr)),
    CompatiblePolicy ℓS πS →
    CompatiblePolicy (leafOut r hf hn hr ℓS) (polOut r hf hn hr πS)
  | .leaf, _, _, _, _, ℓS, πS, _ => by
      cases ℓS
      cases πS
      trivial
  | .node nA hA nY hY K Kpos Ksum child, r, hf, hn, hr, ⟨a, i, ℓc⟩, ⟨a0, cont⟩, hc => by
      rcases hc with ⟨rfl, hc⟩
      have ih := leafOut_polOut
        (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
        (hf.2 a _) (hn.2 a _) (yOf_pos (fun y => Field.root (r.2 a y)) i)
        ℓc (cont a i) hc
      dsimp only [leafOut, polOut, CompatiblePolicy]
      refine ⟨rfl, ?_⟩
      have hy : yOf (fun y => Field.root (r.2 a y)) i ∈
          supportOf (fun y => Field.root (r.2 a y)) := yOf_mem _ i
      rw [dite_eq_left hy]
      have hi : indexOf (fun y => Field.root (r.2 a y)) hy = i := indexOf_yOf _ i
      have hrun (j : Fin (supportOf (fun y => Field.root (r.2 a y))).card) (hj : j = i)
          (heq : yOf (fun y => Field.root (r.2 a y)) j = yOf (fun y => Field.root (r.2 a y)) i) :
          CompatiblePolicy
            (leafOut (r.2 a (yOf (fun y => Field.root (r.2 a y)) i))
              (hf.2 a _) (hn.2 a _) (yOf_pos _ i) ℓc)
            (Eq.rec (motive := fun z _ => Policy (child a z))
              (polOut (r.2 a (yOf (fun y => Field.root (r.2 a y)) j))
                (hf.2 a _) (hn.2 a _) (yOf_pos _ j) (cont a j)) heq) := by
        subst hj
        exact ih
      exact hrun (indexOf (fun y => Field.root (r.2 a y)) hy) hi (yOf_indexOf _ hy)

end CausalSpectrum








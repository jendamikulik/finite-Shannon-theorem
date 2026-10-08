/-
Structural characterization of policy-indexed decoders.

`bad_mem_defect` is the upper bound: every unrealizable seed index of an
`ε`-accurate family lies in the subset-sum defect. This file adds the matching
depth-two attainment and the two corollaries. It does not use the Shannon bound.
-/
import CausalSeed.Probe
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

noncomputable section
open Classical
namespace CausalSpectrum

def treeDepth : Tree → ℕ
  | .leaf => 0
  | .node nA _ nY _ _ _ _ child =>
      1 + Finset.sup Finset.univ fun a =>
        Finset.sup (Finset.univ : Finset (Fin (nY a))) fun y => treeDepth (child a y)

theorem treeDepth_leaf : treeDepth Tree.leaf = 0 := rfl

def choiceNode : Tree :=
  .node 2 (by decide) (fun _ => 1) (fun _ => Nat.one_pos)
    (fun _ _ => 1) (fun _ _ => zero_lt_one)
    (fun _ => by simp [Fin.sum_univ_one])
    (fun _ _ => .leaf)

theorem choiceNode_depth : treeDepth choiceNode = 1 := by
  simp [choiceNode, treeDepth, Fin.sum_univ_one]

def pairChild (y : Fin 2) : Tree :=
  if y = 0 then choiceNode else .leaf

def pairK {n : ℕ} (q : Fin n → ℝ) (j : Fin n) (y : Fin 2) : ℝ :=
  if y = 0 then q j else 1 - q j

theorem pairK_pos {n : ℕ} {q : Fin n → ℝ} (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (j : Fin n) (y : Fin 2) : 0 < pairK q j y := by
  unfold pairK
  by_cases hy : y = 0
  · simp [hy, hq0]
  · have hy1 : y = 1 := by
      fin_cases y <;> simp_all
    simp [hy, hy1, sub_pos, hq1]

theorem pairK_sum {n : ℕ} (q : Fin n → ℝ) (j : Fin n) :
    ∑ y : Fin 2, pairK q j y = 1 := by
  simp [pairK, Fin.sum_univ_two]

def pairTree {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) : Tree :=
  .node n hn (fun _ => 2) (fun _ => Nat.two_pos)
    (pairK q) (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y)

theorem pairTree_depth {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) :
    treeDepth (pairTree hn q hq0 hq1) ≤ 2 := by
  have hchild : ∀ y : Fin 2, treeDepth (pairChild y) ≤ 1 := by
    intro y
    fin_cases y
    · simp [pairChild, choiceNode, treeDepth, Fin.sum_univ_one]
    · simp [pairChild, treeDepth]
  simp only [pairTree, treeDepth]
  have hsup : Finset.sup Finset.univ (fun a : Fin n =>
      Finset.sup (Finset.univ : Finset (Fin 2)) fun y => treeDepth (pairChild y)) ≤ 1 := by
    refine Finset.sup_le fun a _ => ?_
    refine Finset.sup_le fun y _ => hchild y
  exact Nat.add_le_add_left hsup 1

def goLeaf (later : Fin 2) : Leaf choiceNode :=
  ⟨later, ⟨0, Nat.one_pos⟩, PUnit.unit⟩

def rootAct {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (π : Policy (pairTree hn q hq0 hq1)) : Fin n :=
  π.1

def laterAct {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (π : Policy (pairTree hn q hq0 hq1)) : Fin 2 :=
  (π.2 (rootAct hn q hq0 hq1 π) 0).1

def yesLeaf {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (j : Fin n) (later : Fin 2) : Leaf (pairTree hn q hq0 hq1) :=
  pack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q) (pairK_pos hq0 hq1)
    (pairK_sum q) (fun _ y => pairChild y) j 0 (goLeaf later)

def noLeaf {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (j : Fin n) : Leaf (pairTree hn q hq0 hq1) :=
  pack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q) (pairK_pos hq0 hq1)
    (pairK_sum q) (fun _ y => pairChild y) j 1 PUnit.unit

theorem yes_compatible {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (π : Policy (pairTree hn q hq0 hq1)) :
    CompatiblePolicy (yesLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) (laterAct hn q hq0 hq1 π)) π := by
  unfold pairTree at *
  dsimp [yesLeaf, pack, CompatiblePolicy, goLeaf, laterAct, rootAct]
  constructor
  · rfl
  · constructor
    · rfl
    · trivial

theorem no_compatible {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (π : Policy (pairTree hn q hq0 hq1)) :
    CompatiblePolicy (noLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π)) π := by
  unfold pairTree at *
  dsimp [noLeaf, pack, CompatiblePolicy, rootAct]
  constructor
  · rfl
  · trivial

theorem hitMass_pair {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (π : Policy (pairTree hn q hq0 hq1)) (S : Leaf (pairTree hn q hq0 hq1) → Prop) :
    hitMass S π =
      (if S (yesLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) (laterAct hn q hq0 hq1 π)) then
        q (rootAct hn q hq0 hq1 π) else 0) +
      (if S (noLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π)) then
        1 - q (rootAct hn q hq0 hq1 π) else 0) := by
  unfold pairTree hitMass rootAct laterAct yesLeaf noLeaf pack goLeaf pairChild choiceNode at *
  simp [policySum, leafMass, pairK, Fin.sum_univ_two, Fin.sum_univ_one, rootAct]
  rfl

def sideSet {m n : ℕ} (A B : Fin n → Finset (Fin m)) (later : Fin 2) (j : Fin n) :
    Finset (Fin m) :=
  if later = 0 then A j else B j

def attainDecoder {m n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (A B : Fin n → Finset (Fin m)) :
    Decoder (m := m) (pairTree hn q hq0 hq1) :=
  fun π i =>
    if i ∈ sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π) then
      ⟨yesLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) (laterAct hn q hq0 hq1 π),
        yes_compatible hn q hq0 hq1 π⟩
    else
      ⟨noLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π), no_compatible hn q hq0 hq1 π⟩

theorem dec_eq_side {m n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (A B : Fin n → Finset (Fin m)) (π : Policy (pairTree hn q hq0 hq1)) (i : Fin m) :
    (attainDecoder hn q hq0 hq1 A B π i).1 =
      if i ∈ sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π) then
        yesLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) (laterAct hn q hq0 hq1 π)
      else
        noLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) := by
  by_cases hi : i ∈ sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π)
  · simp [attainDecoder, hi]
  · simp [attainDecoder, hi]

theorem seedMass_ite {m : ℕ} (w : Fin m → ℝ) (p : Fin m → Prop) :
    seedMass w p = ∑ i, if p i then w i else 0 := by
  simp [seedMass, Finset.sum_filter]

theorem half_side {a b ε : ℝ} (h : |a - b| ≤ 2 * ε) (later : Fin 2) :
    |(if later = 0 then a else b) - (a + b) / 2| ≤ ε := by
  by_cases h0 : later = 0
  · simpa [h0] using (half_gap_le h).1
  · have h1 : later = 1 := by fin_cases later <;> simp_all
    simpa [h0, h1] using (half_gap_le h).2

theorem ite_mem_sum {m : ℕ} (w : Fin m → ℝ) (s : Finset (Fin m)) :
    ∑ i, (if i ∈ s then w i else 0) = subsetSum w s := by
  simp [subsetSum, Finset.sum_ite, Finset.sum_filter]

theorem seed_by_side {m n : ℕ} (w : Fin m → ℝ) (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (A B : Fin n → Finset (Fin m)) (π : Policy (pairTree hn q hq0 hq1))
    (S : Leaf (pairTree hn q hq0 hq1) → Prop) :
    seedMass w (fun i => S (attainDecoder hn q hq0 hq1 A B π i).1) =
      (if S (yesLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) (laterAct hn q hq0 hq1 π)) then
        subsetSum w (sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π)) else 0) +
      (if S (noLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π)) then
        subsetSum w (Finset.univ \ sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π))
        else 0) := by
  let side := sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π)
  let yes := yesLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π) (laterAct hn q hq0 hq1 π)
  let no := noLeaf hn q hq0 hq1 (rootAct hn q hq0 hq1 π)
  rw [seedMass_ite]
  have hpt : ∀ i, (if S (attainDecoder hn q hq0 hq1 A B π i).1 then w i else 0) =
      (if i ∈ side ∧ S yes then w i else 0) + (if i ∉ side ∧ S no then w i else 0) := by
    intro i
    rw [dec_eq_side]
    by_cases hi : i ∈ side
    · simp [hi, side, yes]
    · simp [hi, side, no]
  simp_rw [hpt, Finset.sum_add_distrib]
  have hyes : ∑ i, (if i ∈ side ∧ S yes then w i else 0) =
      if S yes then subsetSum w side else 0 := by
    by_cases hs : S yes
    · simp [hs, subsetSum]
    · simp [hs]
  have hno : ∑ i, (if i ∉ side ∧ S no then w i else 0) =
      if S no then subsetSum w (Finset.univ \ side) else 0 := by
    by_cases hs : S no
    · simp only [hs, ite_true, subsetSum]
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext i
        simp
      · intro i _
        rfl
    · simp [hs]
  simp [hyes, hno, side, yes, no]

theorem attain_accurate {m n : ℕ} (w : Fin m → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hsum : ∑ i, w i = 1) (hn : 0 < n) (A B : Fin n → Finset (Fin m))
    (hgap : ∀ j, |subsetSum w (A j) - subsetSum w (B j)| ≤ 2 * ε)
    (q : Fin n → ℝ) (hq : ∀ j, q j = (subsetSum w (A j) + subsetSum w (B j)) / 2)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) :
    Accurate w ε (attainDecoder hn q hq0 hq1 A B) := by
  intro π S
  have hseed := seed_by_side w hn q hq0 hq1 A B π S
  have hhit := hitMass_pair hn q hq0 hq1 π S
  let j := rootAct hn q hq0 hq1 π
  let b := laterAct hn q hq0 hq1 π
  by_cases hy : S (yesLeaf hn q hq0 hq1 j b)
  · by_cases hnS : S (noLeaf hn q hq0 hq1 j)
    · have hcompl : subsetSum w (sideSet A B b j) +
          subsetSum w (Finset.univ \ sideSet A B b j) = 1 := by
        have hsplit := Finset.sum_add_sum_compl (sideSet A B b j) w
        simpa [subsetSum, hsum] using hsplit
      simp [hseed, hhit, hy, hnS, j, b, hq, hcompl]
      ring_nf
      simpa using hε
    · simp [hseed, hhit, hy, hnS, j, b]
      have hmove : subsetSum w (sideSet A B b j) =
          if b = 0 then subsetSum w (A j) else subsetSum w (B j) := by
        by_cases hb : b = 0 <;> simp [sideSet, hb]
      rw [hq, hmove]
      exact half_side (hgap j) b
  · by_cases hnS : S (noLeaf hn q hq0 hq1 j)
    · have hcompl : subsetSum w (Finset.univ \ sideSet A B b j) =
          1 - subsetSum w (sideSet A B b j) := by
        have hsplit := Finset.sum_add_sum_compl (sideSet A B b j) w
        have : subsetSum w (sideSet A B b j) +
            subsetSum w (Finset.univ \ sideSet A B b j) = 1 := by
          simpa [subsetSum, hsum] using hsplit
        linarith
      simp [hseed, hhit, hy, hnS, j, b, hcompl]
      have hmove : subsetSum w (sideSet A B b j) =
          if b = 0 then subsetSum w (A j) else subsetSum w (B j) := by
        by_cases hb : b = 0 <;> simp [sideSet, hb]
      rw [hq, hmove]
      simpa [abs_sub_comm] using half_side (hgap j) b
    · simp [hseed, hhit, hy, hnS, j, b, abs_zero]
      exact hε

def polAt {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (j : Fin n) (later : Fin 2) : Policy (pairTree hn q hq0 hq1) :=
  (j, fun _ y =>
    if h : y = 0 then
      h ▸ (⟨later, fun _ _ => PUnit.unit⟩ : Policy choiceNode)
    else
      (show y = 1 by fin_cases y <;> simp_all) ▸ (PUnit.unit : Policy Tree.leaf))

theorem pol_root {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) (j : Fin n) (later : Fin 2) :
    rootAct hn q hq0 hq1 (polAt hn q hq0 hq1 j later) = j := rfl

theorem pol_later {n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1) (j : Fin n) (later : Fin 2) :
    laterAct hn q hq0 hq1 (polAt hn q hq0 hq1 j later) = later := by
  simp [laterAct, polAt, rootAct, pairChild]

theorem sym_bad {m n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (A B : Fin n → Finset (Fin m)) (j : Fin n) (i : Fin m)
    (hi : i ∈ seedSym (A j) (B j)) :
    ¬ seedRealizable (oneAssign (attainDecoder hn q hq0 hq1 A B) i) := by
  intro ⟨d, hd⟩
  rw [mem_seedSym] at hi
  let π0 := polAt hn q hq0 hq1 j 0
  let π1 := polAt hn q hq0 hq1 j 1
  have hrun0 : run d π0 = (oneAssign (attainDecoder hn q hq0 hq1 A B) i π0).1 :=
    congrArg Subtype.val (congrFun hd π0)
  have hrun1 : run d π1 = (oneAssign (attainDecoder hn q hq0 hq1 A B) i π1).1 :=
    congrArg Subtype.val (congrFun hd π1)
  have hyes : (oneAssign (attainDecoder hn q hq0 hq1 A B) i π0).1 =
      yesLeaf hn q hq0 hq1 j 0 ∨
      (oneAssign (attainDecoder hn q hq0 hq1 A B) i π1).1 =
      yesLeaf hn q hq0 hq1 j 1 := by
    rcases hi with ⟨hA, hB⟩ | ⟨hB, hA⟩
    · exact Or.inl (by
        simp [oneAssign, dec_eq_side, π0, sideSet, pol_later, pol_root, hA])
    · exact Or.inr (by
        simp [oneAssign, dec_eq_side, π1, sideSet, pol_later, pol_root, hB])
  have hout0 : (unpack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q)
      (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y) (run d π0)).2.1 =
      d.1 j := by
    erw [run_pack]
    simp [unpack_pack]
    exact congrArg d.1 (pol_root hn q hq0 hq1 j 0)
  have hout1 : (unpack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q)
      (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y) (run d π1)).2.1 =
      d.1 j := by
    erw [run_pack]
    simp [unpack_pack]
    exact congrArg d.1 (pol_root hn q hq0 hq1 j 1)
  rcases hi with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · have hy : (oneAssign (attainDecoder hn q hq0 hq1 A B) i π0).1 = yesLeaf hn q hq0 hq1 j 0 := by
      simp [oneAssign, dec_eq_side, π0, sideSet, pol_later, pol_root, hA]
    have hnoleaf : (oneAssign (attainDecoder hn q hq0 hq1 A B) i π1).1 =
        noLeaf hn q hq0 hq1 j := by
      simp [oneAssign, dec_eq_side, π1, sideSet, pol_later, pol_root, hB]
    have hz : (unpack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q)
        (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y) (yesLeaf hn q hq0 hq1 j 0)).2.1 = 0 := by
      unfold yesLeaf
      erw [unpack_pack]
    have ho : (unpack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q)
        (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y) (noLeaf hn q hq0 hq1 j)).2.1 = 1 := by
      unfold noLeaf
      erw [unpack_pack]
    have h0 : d.1 j = 0 := by
      erw [← hout0, hrun0, hy, hz]
    have h1 : d.1 j = 1 := by
      erw [← hout1, hrun1, hnoleaf, ho]
    exact Fin.zero_ne_one (h0.symm.trans h1)
  · have hy : (oneAssign (attainDecoder hn q hq0 hq1 A B) i π1).1 = yesLeaf hn q hq0 hq1 j 1 := by
      simp [oneAssign, dec_eq_side, π1, sideSet, pol_later, pol_root, hB]
    have hnoleaf : (oneAssign (attainDecoder hn q hq0 hq1 A B) i π0).1 =
        noLeaf hn q hq0 hq1 j := by
      simp [oneAssign, dec_eq_side, π0, sideSet, pol_later, pol_root, hA]
    have hz : (unpack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q)
        (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y) (yesLeaf hn q hq0 hq1 j 1)).2.1 = 0 := by
      unfold yesLeaf
      erw [unpack_pack]
    have ho : (unpack n hn (fun _ => 2) (fun _ => Nat.two_pos) (pairK q)
        (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y) (noLeaf hn q hq0 hq1 j)).2.1 = 1 := by
      unfold noLeaf
      erw [unpack_pack]
    have h0 : d.1 j = 0 := by
      erw [← hout1, hrun1, hy, hz]
    have h1 : d.1 j = 1 := by
      erw [← hout0, hrun0, hnoleaf, ho]
    exact Fin.zero_ne_one (h0.symm.trans h1)

def goodStrat {m n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (A : Fin n → Finset (Fin m)) (i : Fin m) : Strategy (pairTree hn q hq0 hq1) :=
  (fun j => if i ∈ A j then 0 else 1, fun _ y =>
    if h : y = 0 then
      h ▸ (⟨fun _ => (⟨0, Nat.one_pos⟩ : Fin 1), fun _ _ => PUnit.unit⟩ : Strategy choiceNode)
    else
      (show y = 1 by fin_cases y <;> simp_all) ▸ (PUnit.unit : Strategy Tree.leaf))

theorem sym_good {m n : ℕ} (hn : 0 < n) (q : Fin n → ℝ)
    (hq0 : ∀ j, 0 < q j) (hq1 : ∀ j, q j < 1)
    (A B : Fin n → Finset (Fin m)) (i : Fin m)
    (hagree : ∀ j, i ∈ A j ↔ i ∈ B j) :
    seedRealizable (oneAssign (attainDecoder hn q hq0 hq1 A B) i) := by
  refine ⟨goodStrat hn q hq0 hq1 A i, ?_⟩
  funext π
  apply Subtype.ext
  dsimp only [seedRealizes]
  by_cases hi : i ∈ A (rootAct hn q hq0 hq1 π)
  · have hside : i ∈ sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π) := by
      by_cases hb : laterAct hn q hq0 hq1 π = 0
      · simp [sideSet, hb, hi]
      · have hB : i ∈ B (rootAct hn q hq0 hq1 π) := (hagree _).mp hi
        simp [sideSet, hb, hB]
    have hi' : i ∈ A π.1 := by simpa [rootAct] using hi
    erw [run_pack]
    unfold goodStrat
    dsimp
    rw [if_pos hi']
    erw [oneAssign, dec_eq_side]
    rw [if_pos hside]
    erw [run]
    simp [run, choiceNode, goLeaf, yesLeaf, pack, rootAct, laterAct]
    rfl
  · have hside : i ∉ sideSet A B (laterAct hn q hq0 hq1 π) (rootAct hn q hq0 hq1 π) := by
      by_cases hb : laterAct hn q hq0 hq1 π = 0
      · simp [sideSet, hb, hi]
      · have hB : i ∉ B (rootAct hn q hq0 hq1 π) := by
          intro h
          exact hi ((hagree _).mpr h)
        simp [sideSet, hb, hB]
    have hi' : i ∉ A π.1 := by simpa [rootAct] using hi
    erw [run_pack]
    unfold goodStrat
    dsimp
    rw [if_neg hi']
    erw [oneAssign, dec_eq_side]
    rw [if_neg hside]
    erw [run]
    simp [run, noLeaf, pack, rootAct]
    rfl

def leafDecoder {m : ℕ} : Decoder (m := m) Tree.leaf :=
  fun _ _ => ⟨PUnit.unit, trivial⟩

theorem leaf_accurate {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) (hε : 0 ≤ ε) (hsum : ∑ i, w i = 1) :
    Accurate w ε (leafDecoder (m := m)) := by
  intro π S
  cases π
  by_cases hS : S PUnit.unit
  · simp [Accurate, hitMass, policySum, seedMass, leafDecoder, leafMass, hS, hsum, abs_zero]
    exact hε
  · simp [hitMass, policySum, seedMass, leafDecoder, hS, abs_zero]
    exact hε

theorem exists_pair {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) {i : Fin m} (h : inDefect w ε i) :
    ∃ p : Finset (Fin m) × Finset (Fin m),
      p.1 ≠ p.2 ∧ |subsetSum w p.1 - subsetSum w p.2| ≤ 2 * ε ∧ i ∈ seedSym p.1 p.2 := by
  rcases h with ⟨A, B, hne, hg, hi⟩
  exact ⟨(A, B), hne, hg, hi⟩

def pairOf {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) {i : Fin m} (h : inDefect w ε i) :
    Finset (Fin m) × Finset (Fin m) :=
  Classical.choose (exists_pair w ε h)

theorem pairOf_spec {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) {i : Fin m} (h : inDefect w ε i) :
    (pairOf w ε h).1 ≠ (pairOf w ε h).2 ∧
      |subsetSum w (pairOf w ε h).1 - subsetSum w (pairOf w ε h).2| ≤ 2 * ε ∧
      i ∈ seedSym (pairOf w ε h).1 (pairOf w ε h).2 := by
  simpa [pairOf] using Classical.choose_spec (exists_pair w ε h)

/-- The incompatible indices of an `ε`-accurate family are exactly the arithmetic defect,
and one controlled tree of depth at most two attains the equality. -/
theorem profile_attainment {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    ∃ (T : Tree) (f : Decoder (m := m) T),
      Accurate w ε f ∧ treeDepth T ≤ 2 ∧
        ∀ i, ¬ seedRealizable (oneAssign f i) ↔ inDefect w ε i := by
  by_cases hE : ∀ i, ¬ inDefect w ε i
  · refine ⟨Tree.leaf, leafDecoder, leaf_accurate w ε hε hsum, ?_, ?_⟩
    · simp [treeDepth]
    · intro i
      constructor
      · intro hbad
        exact False.elim
          (hE i (bad_mem_defect w ε leafDecoder (leaf_accurate w ε hε hsum) i hbad))
      · intro hi
        exact (hE i hi).elim
  · push Not at hE
    obtain ⟨i0, hi0⟩ := hE
    let D := defectFinset w ε
    have hD : D.Nonempty := by
      refine ⟨i0, ?_⟩
      simpa [D, defectFinset, Finset.mem_filter] using hi0
    have hn : 0 < D.card := hD.card_pos
    let e : {x // x ∈ D} ≃ Fin D.card := D.equivFin
    let idx : Fin D.card → Fin m := fun k => (e.symm k).1
    have hidx : ∀ k, inDefect w ε (idx k) := by
      intro k
      have hk : idx k ∈ D := (e.symm k).2
      simpa [D, defectFinset, Finset.mem_filter] using hk
    let A : Fin D.card → Finset (Fin m) := fun k => (pairOf w ε (hidx k)).1
    let B : Fin D.card → Finset (Fin m) := fun k => (pairOf w ε (hidx k)).2
    have hne : ∀ k, A k ≠ B k := fun k => (pairOf_spec w ε (hidx k)).1
    have hgap : ∀ k, |subsetSum w (A k) - subsetSum w (B k)| ≤ 2 * ε :=
      fun k => (pairOf_spec w ε (hidx k)).2.1
    have hmem : ∀ k, idx k ∈ seedSym (A k) (B k) :=
      fun k => (pairOf_spec w ε (hidx k)).2.2
    let q : Fin D.card → ℝ := fun k => (subsetSum w (A k) + subsetSum w (B k)) / 2
    have hq0 : ∀ k, 0 < q k := by
      intro k
      have hb : 0 < q k ∧ q k < 1 := by
        simpa [q] using half_bounds hpos hsum (hne k)
      exact hb.1
    have hq1 : ∀ k, q k < 1 := by
      intro k
      have hb : 0 < q k ∧ q k < 1 := by
        simpa [q] using half_bounds hpos hsum (hne k)
      exact hb.2
    let T := pairTree hn q hq0 hq1
    let f := attainDecoder hn q hq0 hq1 A B
    refine ⟨T, f, ?_, ?_, ?_⟩
    · simpa [f] using attain_accurate w ε hε hsum hn A B hgap q (fun _ => rfl) hq0 hq1
    · simpa [T] using pairTree_depth hn q hq0 hq1
    · intro i
      constructor
      · intro hbad
        exact bad_mem_defect w ε f
          (attain_accurate w ε hε hsum hn A B hgap q (fun _ => rfl) hq0 hq1) i hbad
      · intro hi
        have hiD : i ∈ D := by
          simpa [D, defectFinset, Finset.mem_filter] using hi
        let k : Fin D.card := e ⟨i, hiD⟩
        have hid : idx k = i := by
          simp [idx, k, Equiv.symm_apply_apply]
        have hsym : i ∈ seedSym (A k) (B k) := hid ▸ hmem k
        simpa [f] using sym_bad hn q hq0 hq1 A B k i hsym

/-- Indices with no realizing strategy, as a finset. -/
def badFinset {m : ℕ} {T : Tree} (f : Decoder (m := m) T) : Finset (Fin m) :=
  Finset.univ.filter fun i => ¬ seedRealizable (oneAssign f i)

theorem bad_subset_defect {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) {T : Tree}
    (f : Decoder (m := m) T) (hf : Accurate w ε f) :
    badFinset f ⊆ defectFinset w ε := by
  intro i hi
  have hbad : ¬ seedRealizable (oneAssign f i) := by
    simpa [badFinset, Finset.mem_filter] using hi
  simpa [defectFinset, Finset.mem_filter] using bad_mem_defect w ε f hf i hbad

/-- The incompatible mass of any `ε`-accurate family is at most the defect mass. -/
theorem incompatible_mass_le {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) (hpos : ∀ i, 0 < w i)
    {T : Tree} (f : Decoder (m := m) T) (hf : Accurate w ε f) :
    subsetSum w (badFinset f) ≤ defectMass w ε := by
  simpa [subsetSum, defectMass] using
    Finset.sum_le_sum_of_subset_of_nonneg (bad_subset_defect w ε f hf)
      (fun i _ _ => (hpos i).le)

/-- The defect mass is attained: some depth-two family has incompatible mass exactly `r_ε(w)`. -/
theorem profile_mass_attained {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    ∃ (T : Tree) (f : Decoder (m := m) T),
      Accurate w ε f ∧ treeDepth T ≤ 2 ∧
        subsetSum w (badFinset f) = defectMass w ε := by
  obtain ⟨T, f, hf, hd, hiff⟩ := profile_attainment w ε hε hpos hsum
  refine ⟨T, f, hf, hd, ?_⟩
  have hset : badFinset f = defectFinset w ε := by
    ext i
    simp only [badFinset, defectFinset, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hiff i
  simp [defectMass, hset]

/-- Distinct subset sums are equivalent to universal exact causal rigidity. -/
theorem exact_rigidity {m : ℕ} (w : Fin m → ℝ) (hpos : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) :
    subsetSumsDistinct w ↔
      ∀ (T : Tree) (f : Decoder (m := m) T), Accurate w 0 f →
        ∀ i, seedRealizable (oneAssign f i) := by
  constructor
  · intro hdist T f hf i
    have hempty : ∀ j, ¬ inDefect w 0 j :=
      (subsetSumsDistinct_iff_defect_empty w).1 hdist
    apply not_not.mp
    intro hbad
    exact hempty i (bad_mem_defect w 0 f hf i hbad)
  · intro hall
    rw [subsetSumsDistinct_iff_defect_empty]
    intro i hi
    obtain ⟨T, f, hf, _, hchar⟩ := profile_attainment w 0 le_rfl hpos hsum
    exact (hchar i).mpr hi (hall T f hf i)

/-- `2ε < γ(w)` is the sharp threshold for every `ε`-accurate family to be realizable. -/
theorem sharp_threshold {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    (∀ (T : Tree) (f : Decoder (m := m) T), Accurate w ε f →
        ∀ i, seedRealizable (oneAssign f i)) ↔
      2 * ε < gamma hm w := by
  rw [← defect_empty_iff_lt_gamma hm w hε]
  constructor
  · intro hall i hi
    obtain ⟨T, f, hf, _, hchar⟩ := profile_attainment w ε hε hpos hsum
    exact (hchar i).mpr hi (hall T f hf i)
  · intro hempty T f hf i
    apply not_not.mp
    intro hbad
    exact hempty i (bad_mem_defect w ε f hf i hbad)

#print axioms bad_mem_defect
#print axioms unrealizable_splits
#print axioms profile_attainment
#print axioms incompatible_mass_le
#print axioms profile_mass_attained
#print axioms exact_rigidity
#print axioms sharp_threshold

end CausalSpectrum
end

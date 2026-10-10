/-
Causal gluing by probability-preserving relabeling.

`relabelRepair_iff_countStable`: one shared strategy per seed and a
weight-preserving permutation per policy reproduce the decoder if and only
if, inside every weight class, the number of seeds whose transcript extends
a history does not depend on the policy among those that follow that history.
No marginal-accuracy hypothesis is used.

`sharp_relabel`: every `ε`-accurate family on every finite controlled tree
admits such a repair if and only if `2ε < deltaRel w`. The constant is the
minimum mass gap between subsets with different weight-class count vectors.
It is not the subset-sum separation `gamma`, and it does not use the Shannon bound.

The Lebesgue statement for generic tensor powers is not a theorem of this file.
-/
import CausalSeed.Profile
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Fin.Basic

noncomputable section
open Classical
namespace CausalSpectrum

inductive Hist : Tree → Type where
  | here {T : Tree} : Hist T
  | under {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
      {K : (a : Fin nA) → Fin (nY a) → ℝ}
      {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
      {child : (a : Fin nA) → Fin (nY a) → Tree}
      (a : Fin nA) (y : Fin (nY a)) (t : Hist (child a y)) :
      Hist (.node nA hA nY hY K Kpos Ksum child)

def followsHist {T : Tree} (h : Hist T) (π : Policy T) : Prop :=
  match h with
  | .here => True
  | .under a y t => π.1 = a ∧ followsHist t (π.2 a y)

/-- Move a child leaf along `a0 = a` and the transported output equality. -/
def pushChild {nA : ℕ} {nY : Fin nA → ℕ}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {a0 : Fin nA} {y0 : Fin (nY a0)}
    (sub : Leaf (child a0 y0))
    {a : Fin nA} {y : Fin (nY a)}
    (ha : a0 = a)
    (hy : cast (congrArg (fun b => Fin (nY b)) ha) y0 = y) :
    Leaf (child a y) :=
  cast (by subst ha; subst hy; rfl) sub

def extendsHist {T : Tree} (h : Hist T) (ℓ : Leaf T) : Prop :=
  match h with
  | .here => True
  | @Hist.under nA hA nY hY K Kpos Ksum child a y t =>
      ∃ ha : ℓ.1 = a,
        ∃ hy : cast (congrArg (fun b : Fin nA => Fin (nY b)) ha) ℓ.2.1 = y,
          extendsHist t (pushChild (child := child) ℓ.2.2 ha hy)

def ofLeaf : {T : Tree} → Leaf T → Hist T
  | .leaf, _ => .here
  | .node _ _ _ _ _ _ _ _, ⟨a, y, ℓ⟩ => .under a y (ofLeaf ℓ)

variable {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
  {K : (a : Fin nA) → Fin (nY a) → ℝ}
  {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
  {child : (a : Fin nA) → Fin (nY a) → Tree}

theorem pushChild_rfl (a : Fin nA) (y : Fin (nY a)) (sub : Leaf (child a y))
    (ha : a = a) (hy : cast (congrArg (fun b => Fin (nY b)) ha) y = y) :
    pushChild sub ha hy = sub := by
  cases ha
  cases hy
  rfl

theorem extends_mk (a : Fin nA) (y : Fin (nY a)) (t : Hist (child a y))
    (ℓ : Leaf (child a y)) :
    extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y t)
        (⟨a, y, ℓ⟩ : Leaf (.node nA hA nY hY K Kpos Ksum child)) ↔
      extendsHist t ℓ := by
  constructor
  · intro h
    rcases h with ⟨ha, hy, ht⟩
    rw [pushChild_rfl a y ℓ ha hy] at ht
    exact ht
  · intro ht
    exact ⟨rfl, rfl, by simpa [pushChild_rfl a y ℓ rfl rfl] using ht⟩

theorem not_extends_mk (a : Fin nA) {y y' : Fin (nY a)} (hne : y' ≠ y)
    (t : Hist (child a y)) (ℓ : Leaf (child a y')) :
    ¬ extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y t)
        (⟨a, y', ℓ⟩ : Leaf (.node nA hA nY hY K Kpos Ksum child)) := by
  intro h
  rcases h with ⟨_ha, hy, _⟩
  exact hne (by simpa [cast_eq] using hy)

theorem extends_here_iff (a : Fin nA) (y : Fin (nY a))
    (ℓ : Leaf (.node nA hA nY hY K Kpos Ksum child)) :
    extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y (.here : Hist (child a y))) ℓ ↔
      ∃ ha : ℓ.1 = a, cast (congrArg (fun b => Fin (nY b)) ha) ℓ.2.1 = y := by
  simp only [extendsHist]
  constructor
  · rintro ⟨ha, hy, _⟩
    exact ⟨ha, hy⟩
  · rintro ⟨ha, hy⟩
    exact ⟨ha, hy, trivial⟩

theorem extAct {a : Fin nA} {y : Fin (nY a)} {t : Hist (child a y)}
    {ℓ : Leaf (.node nA hA nY hY K Kpos Ksum child)}
    (h : extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y t) ℓ) :
    ℓ.1 = a := h.choose

theorem extOut {a : Fin nA} {y : Fin (nY a)} {t : Hist (child a y)}
    {ℓ : Leaf (.node nA hA nY hY K Kpos Ksum child)}
    (h : extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y t) ℓ) :
    cast (congrArg (fun b => Fin (nY b)) (extAct h)) ℓ.2.1 = y := by
  have hy := h.choose_spec.choose
  simpa [show extAct h = h.choose from rfl] using hy

theorem extends_push {a : Fin nA} {y : Fin (nY a)} (t : Hist (child a y))
    (ℓ : Leaf (.node nA hA nY hY K Kpos Ksum child))
    (ha : ℓ.1 = a) (hy : cast (congrArg (fun b => Fin (nY b)) ha) ℓ.2.1 = y) :
    extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y t) ℓ ↔
      extendsHist t (pushChild ℓ.2.2 ha hy) := by
  constructor
  · rintro ⟨ha', hy', ht⟩
    have hha : ha' = ha := Subsingleton.elim _ _
    subst hha
    have hhy : hy' = hy := Subsingleton.elim _ _
    subst hhy
    exact ht
  · intro ht
    exact ⟨ha, hy, ht⟩

theorem leaf_of_push (ℓ : Leaf (.node nA hA nY hY K Kpos Ksum child))
    (a : Fin nA) (y : Fin (nY a)) (ℓc : Leaf (child a y))
    (ha : ℓ.1 = a) (hy : cast (congrArg (fun b => Fin (nY b)) ha) ℓ.2.1 = y)
    (hc : pushChild ℓ.2.2 ha hy = ℓc) :
    ℓ = ⟨a, y, ℓc⟩ := by
  rcases ℓ with ⟨a0, y0, sub⟩
  obtain rfl := ha
  obtain rfl := hy
  have hsub : pushChild sub rfl rfl = sub := pushChild_rfl a0 y0 sub rfl rfl
  rw [hsub] at hc
  obtain rfl := hc
  rfl

variable {m : ℕ}

theorem extends_ofLeaf_iff {T : Tree} (ℓ ℓ' : Leaf T) :
    extendsHist (ofLeaf ℓ) ℓ' ↔ ℓ' = ℓ := by
  induction T with
  | leaf =>
      cases ℓ
      cases ℓ'
      exact ⟨fun _ => rfl, fun _ => trivial⟩
  | node nA hA nY hY K Kpos Ksum child ih =>
      rcases ℓ with ⟨a, y, ℓc⟩
      constructor
      · intro h
        simp only [ofLeaf, extendsHist] at h
        rcases h with ⟨ha, hy, ht⟩
        have hc := (ih a y ℓc (pushChild ℓ'.2.2 ha hy)).1 ht
        exact leaf_of_push ℓ' a y ℓc ha hy hc
      · intro h
        subst h
        exact (extends_mk a y (ofLeaf ℓc) ℓc).2 ((ih a y ℓc ℓc).2 rfl)

theorem compatible_follows {T : Tree} {ℓ : Leaf T} {π : Policy T}
    (h : CompatiblePolicy ℓ π) : followsHist (ofLeaf ℓ) π := by
  induction T with
  | leaf => simp [ofLeaf, followsHist]
  | node nA hA nY hY K Kpos Ksum child ih =>
      rcases ℓ with ⟨a, y, ℓ⟩
      simp only [ofLeaf, followsHist]
      rcases h with ⟨ha, hℓ⟩
      subst ha
      exact ⟨rfl, ih π.1 y hℓ⟩

def extendPol (a : Fin nA) (y0 : Fin (nY a)) (ρ : Policy (child a y0)) :
    Policy (.node nA hA nY hY K Kpos Ksum child) :=
  (a, fun a' y =>
    if ha : a' = a then
      if hy : y = ha ▸ y0 then
        cast (by subst ha; subst hy; rfl) ρ
      else
        defaultPolicy (child a' y)
    else
      defaultPolicy (child a' y))

theorem extendPol_child (a : Fin nA) (y0 : Fin (nY a)) (ρ : Policy (child a y0)) :
    ((extendPol a y0 ρ : Policy (.node nA hA nY hY K Kpos Ksum child)).2 a y0) = ρ := by
  simp [extendPol, cast_eq]

theorem follows_extendPol (a : Fin nA) (y0 : Fin (nY a)) (t : Hist (child a y0))
    (ρ : Policy (child a y0)) (ht : followsHist t ρ) :
    followsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y0 t)
        (extendPol a y0 ρ) := by
  show (extendPol a y0 ρ).1 = a ∧
    followsHist t ((extendPol a y0 ρ).2 a y0)
  rw [extendPol_child]
  exact ⟨rfl, ht⟩

def classCount {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ) (lam : ℝ)
    (f : Decoder (m := m) T) (π : Policy T) (h : Hist T) : ℕ :=
  (active.filter fun i => w i = lam ∧ extendsHist h (f π i).1).card

def CountStable {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) : Prop :=
  ∀ (h : Hist T) (lam : ℝ) (π ρ : Policy T),
    followsHist h π → followsHist h ρ →
      classCount active w lam f π h = classCount active w lam f ρ h

/-- Policy-dependent weight-preserving relabeling plus one strategy per seed. -/
def RelabelRepair (w : Fin m → ℝ) {T : Tree} (f : Decoder (m := m) T) : Prop :=
  ∃ (σ : Policy T → (Fin m ≃ Fin m)) (s : Fin m → Strategy T),
    (∀ π i, w (σ π i) = w i) ∧
    ∀ π i, (f π (σ π i)).1 = run (s i) π

def FiberAgree {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) (s : Fin m → Strategy T) : Prop :=
  ∀ (π : Policy T) (ℓ : Leaf T) (_hℓ : CompatiblePolicy ℓ π) (lam : ℝ),
    (active.filter fun i => w i = lam ∧ run (s i) π = ℓ).card =
      (active.filter fun i => w i = lam ∧ (f π i).1 = ℓ).card

theorem extends_run_follows {T : Tree} (s : Strategy T) (h : Hist T)
    {π ρ : Policy T} (hπ : followsHist h π) (hρ : followsHist h ρ) :
    extendsHist h (run s π) ↔ extendsHist h (run s ρ) := by
  induction h with
  | here => simp [extendsHist]
  | under a y t ih =>
      rcases hπ with ⟨hπa, hπt⟩
      rcases hρ with ⟨hρa, hρt⟩
      have hπt' : followsHist t (π.2 a y) := by simpa [hπa] using hπt
      have hρt' : followsHist t (ρ.2 a y) := by simpa [hρa] using hρt
      by_cases hy : s.1 a = y
      · have hleft : extendsHist (Hist.under a y t) (run s π) ↔
            extendsHist t (run (s.2 a y) (π.2 a y)) := by
          have hrun : run s π = ⟨a, y, run (s.2 a y) (π.2 a y)⟩ := by
            rw [run, hπa, hy]
          rw [hrun]
          exact extends_mk a y t _
        have hright : extendsHist (Hist.under a y t) (run s ρ) ↔
            extendsHist t (run (s.2 a y) (ρ.2 a y)) := by
          have hrun : run s ρ = ⟨a, y, run (s.2 a y) (ρ.2 a y)⟩ := by
            rw [run, hρa, hy]
          rw [hrun]
          exact extends_mk a y t _
        exact hleft.trans ((ih (s.2 a y) hπt' hρt').trans hright.symm)
      · have hnotπ : ¬ extendsHist (Hist.under a y t) (run s π) := by
          have hrun : run s π = ⟨a, s.1 a, run (s.2 a (s.1 a)) (π.2 a (s.1 a))⟩ := by
            rw [run, hπa]
          rw [hrun]
          exact not_extends_mk a hy t _
        have hnotρ : ¬ extendsHist (Hist.under a y t) (run s ρ) := by
          have hrun : run s ρ = ⟨a, s.1 a, run (s.2 a (s.1 a)) (ρ.2 a (s.1 a))⟩ := by
            rw [run, hρa]
          rw [hrun]
          exact not_extends_mk a hy t _
        exact iff_of_false hnotπ hnotρ

theorem relabel_implies_stable (w : Fin m → ℝ) {T : Tree}
    (f : Decoder (m := m) T) (hrep : RelabelRepair w f) :
    CountStable (Finset.univ : Finset (Fin m)) w f := by
  rcases hrep with ⟨σ, s, hw, hrun⟩
  intro h lam π ρ hπ hρ
  let τ : Fin m ≃ Fin m := σ π
  have hτ : ∀ i, w (τ i) = w i := hw π
  have hcard : classCount Finset.univ w lam f π h =
      (Finset.univ.filter fun i => w i = lam ∧ extendsHist h (run (s i) π)).card := by
    refine Finset.card_bij (fun i hi => τ.symm i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hi' : w (τ (τ.symm i)) = w (τ.symm i) := hτ _
      rw [τ.apply_symm_apply] at hi'
      refine ⟨hi'.symm.trans hi.1, ?_⟩
      have hr : (f π i).1 = run (s (τ.symm i)) π := by
        have hr' := hrun π (τ.symm i)
        rwa [τ.apply_symm_apply] at hr'
      simpa [hr] using hi.2
    · intro i _ i' _ heq
      simpa using congrArg τ heq
    · intro j hj
      refine ⟨τ j, ?_, τ.symm_apply_apply j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      refine ⟨(hτ j).trans hj.1, ?_⟩
      have hr : (f π (τ j)).1 = run (s j) π := hrun π j
      simpa [hr] using hj.2
  have hcardρ : classCount Finset.univ w lam f ρ h =
      (Finset.univ.filter fun i => w i = lam ∧ extendsHist h (run (s i) ρ)).card := by
    refine Finset.card_bij (fun i hi => (σ ρ).symm i) ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
      have hσ : ∀ i, w (σ ρ i) = w i := hw ρ
      have hi' : w (σ ρ ((σ ρ).symm i)) = w ((σ ρ).symm i) := hσ _
      rw [(σ ρ).apply_symm_apply] at hi'
      refine ⟨hi'.symm.trans hi.1, ?_⟩
      have hr : (f ρ i).1 = run (s ((σ ρ).symm i)) ρ := by
        have hr' := hrun ρ ((σ ρ).symm i)
        rwa [(σ ρ).apply_symm_apply] at hr'
      simpa [hr] using hi.2
    · intro i _ i' _ heq
      simpa using congrArg (σ ρ) heq
    · intro j hj
      refine ⟨σ ρ j, ?_, (σ ρ).symm_apply_apply j⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      have hσ : ∀ i, w (σ ρ i) = w i := hw ρ
      refine ⟨(hσ j).trans hj.1, ?_⟩
      have hr : (f ρ (σ ρ j)).1 = run (s j) ρ := hrun ρ j
      simpa [hr] using hj.2
  have hsame : (Finset.univ.filter fun i => w i = lam ∧ extendsHist h (run (s i) π)).card =
      (Finset.univ.filter fun i => w i = lam ∧ extendsHist h (run (s i) ρ)).card := by
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ⟨hw, he⟩
      exact ⟨hw, (extends_run_follows (s i) h hπ hρ).1 he⟩
    · intro ⟨hw, he⟩
      exact ⟨hw, (extends_run_follows (s i) h hπ hρ).2 he⟩
  exact hcard.trans (hsame.trans hcardρ.symm)

omit nA hA nY hY K Kpos Ksum child

/-! ## Bijections between equally large pieces -/

def finCastEquiv {n n' : ℕ} (h : n = n') : Fin n ≃ Fin n' where
  toFun := Fin.cast h
  invFun := Fin.cast h.symm
  left_inv i := by
    apply Fin.ext
    simp [Fin.cast]
  right_inv i := by
    apply Fin.ext
    simp [Fin.cast]

theorem finCastEquiv_symm {n n' : ℕ} (h : n = n') :
    (finCastEquiv h).symm = finCastEquiv h.symm := by
  ext i
  simp [finCastEquiv, Fin.cast]

def pieceEquiv {s t : Finset (Fin m)} (h : s.card = t.card) :
    {x // x ∈ s} ≃ {x // x ∈ t} :=
  (s.orderIsoOfFin rfl).symm.toEquiv.trans
    ((finCastEquiv h).trans (t.orderIsoOfFin rfl).toEquiv)

theorem pieceEquiv_symm {s t : Finset (Fin m)} (h : s.card = t.card) :
    (pieceEquiv h).symm = pieceEquiv (s := t) (t := s) h.symm := by
  ext x
  simp [pieceEquiv, finCastEquiv_symm]

theorem pieceEquiv_val_irrel {s t : Finset (Fin m)} (h h' : s.card = t.card)
    (x : {a // a ∈ s}) :
    (pieceEquiv h x).1 = (pieceEquiv h' x).1 := by
  unfold pieceEquiv
  have hcast : finCastEquiv h ((s.orderIsoOfFin rfl).symm x) =
      finCastEquiv h' ((s.orderIsoOfFin rfl).symm x) := by
    apply Fin.ext
    simp [finCastEquiv, Fin.cast]
  simp [hcast]

def classSlice (w : Fin m → ℝ) (A : Finset (Fin m)) (lam : ℝ) : Finset (Fin m) :=
  A.filter fun i => w i = lam

theorem classSlice_self (w : Fin m → ℝ) (A : Finset (Fin m)) (i : Fin m) (hi : i ∈ A) :
    i ∈ classSlice w A (w i) := by
  simp [classSlice, hi]

def classMap (w : Fin m → ℝ) (A B : Finset (Fin m))
    (h : ∀ lam, (classSlice w A lam).card = (classSlice w B lam).card)
    (i : Fin m) (hi : i ∈ A) : Fin m :=
  (pieceEquiv (h (w i)) ⟨i, classSlice_self w A i hi⟩).1

theorem classMap_mem (w : Fin m → ℝ) (A B : Finset (Fin m))
    (h : ∀ lam, (classSlice w A lam).card = (classSlice w B lam).card)
    (i : Fin m) (hi : i ∈ A) :
    classMap w A B h i hi ∈ classSlice w B (w i) :=
  (pieceEquiv (h (w i)) ⟨i, classSlice_self w A i hi⟩).2

theorem classMap_weight (w : Fin m → ℝ) (A B : Finset (Fin m))
    (h : ∀ lam, (classSlice w A lam).card = (classSlice w B lam).card)
    (i : Fin m) (hi : i ∈ A) :
    w (classMap w A B h i hi) = w i := by
  have hmem := classMap_mem w A B h i hi
  simp only [classSlice, Finset.mem_filter] at hmem
  exact hmem.2

theorem classMap_in (w : Fin m → ℝ) (A B : Finset (Fin m))
    (h : ∀ lam, (classSlice w A lam).card = (classSlice w B lam).card)
    (i : Fin m) (hi : i ∈ A) :
    classMap w A B h i hi ∈ B := by
  have hmem := classMap_mem w A B h i hi
  simp only [classSlice, Finset.mem_filter] at hmem
  exact hmem.1

theorem classMap_proof_irrel (w : Fin m → ℝ) (A B : Finset (Fin m))
    (h : ∀ lam, (classSlice w A lam).card = (classSlice w B lam).card)
    (i : Fin m) (hi hi' : i ∈ A) :
    classMap w A B h i hi = classMap w A B h i hi' := by
  have hs : (⟨i, classSlice_self w A i hi⟩ : {x // x ∈ classSlice w A (w i)}) =
      ⟨i, classSlice_self w A i hi'⟩ := Subtype.ext rfl
  exact congrArg (fun z : {x // x ∈ classSlice w A (w i)} => (pieceEquiv (h (w i)) z).1) hs

theorem classSlice_subset (w : Fin m → ℝ) (A : Finset (Fin m)) (lam : ℝ)
    {i : Fin m} (hi : i ∈ classSlice w A lam) : i ∈ A := by
  simp only [classSlice, Finset.mem_filter] at hi
  exact hi.1

/-- Moving a predicate across one weight-class bijection preserves its cardinality. -/
theorem slice_pred_card {s t : Finset (Fin m)} (h : s.card = t.card) (p : Fin m → Prop) :
    (s.filter fun i => ∃ hi : i ∈ s, p ((pieceEquiv h ⟨i, hi⟩).1)).card =
      (t.filter fun j => p j).card := by
  classical
  let e := pieceEquiv h
  refine Finset.card_bij
      (s := s.filter fun i => ∃ hi : i ∈ s, p ((e ⟨i, hi⟩).1))
      (t := t.filter fun j => p j)
      (fun i hi => (e ⟨i, (Finset.mem_filter.mp hi).1⟩).1) ?_ ?_ ?_
  · intro i hi
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    rcases (Finset.mem_filter.mp hi).2 with ⟨hi', hp⟩
    have hs : (⟨i, hi'⟩ : {x // x ∈ s}) = ⟨i, his⟩ := Subtype.ext rfl
    have hp' : p (e ⟨i, his⟩).1 := by
      simpa [hs] using hp
    exact Finset.mem_filter.mpr ⟨(e ⟨i, his⟩).2, hp'⟩
  · intro i hi i' hi' heq
    have his : i ∈ s := (Finset.mem_filter.mp hi).1
    have his' : i' ∈ s := (Finset.mem_filter.mp hi').1
    exact congrArg Subtype.val (e.injective (Subtype.ext heq))
  · intro j hj
    have hjt : j ∈ t := (Finset.mem_filter.mp hj).1
    have hp : p j := (Finset.mem_filter.mp hj).2
    obtain ⟨x, hx⟩ := e.surjective ⟨j, hjt⟩
    refine ⟨x.1, ?_, congrArg Subtype.val hx⟩
    refine Finset.mem_filter.mpr ⟨x.2, ⟨x.2, ?_⟩⟩
    simpa [hx] using hp

/-! ## Rank buckets -/

def cumul {k : ℕ} (c : Fin k → ℕ) (y : Fin k) : ℕ :=
  ∑ z ∈ Finset.univ.filter fun z : Fin k => z.1 < y.1, c z

theorem cumul_ite {k : ℕ} (c : Fin k → ℕ) (y : Fin k) :
    cumul c y = ∑ z : Fin k, if z.1 < y.1 then c z else 0 := by
  simp [cumul, Finset.sum_filter]

theorem cumul_succ {k : ℕ} (c : Fin (k + 1) → ℕ) (i : Fin k) :
    cumul c i.succ = c 0 + cumul (fun j => c j.succ) i := by
  rw [cumul_ite, cumul_ite, Fin.sum_univ_succ]
  have h0 : (0 : Fin (k + 1)).1 < i.succ.1 := by simp [Fin.val_succ]
  simp only [h0, ite_true]
  refine congrArg (fun n => c 0 + n) ?_
  refine Finset.sum_congr rfl ?_
  intro j _
  have hiff : j.succ.1 < i.succ.1 ↔ j.1 < i.1 := by simp [Fin.val_succ]
  by_cases hj : j.1 < i.1
  · simp [hj, hiff]
  · simp [hj, hiff]

theorem cumul_split_sum {k : ℕ} (c : Fin k → ℕ) (y : Fin k) :
    cumul c y + c y = ∑ z : Fin k, if z.1 < y.1 ∨ z = y then c z else 0 := by
  have hc : c y = ∑ z : Fin k, if z = y then c z else 0 := by simp [Finset.sum_ite_eq]
  rw [cumul_ite, hc, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro z _
  by_cases h1 : z.1 < y.1
  · have hz : z ≠ y := by
      intro heq
      subst heq
      simp at h1
    simp [h1, hz]
  · by_cases h2 : z = y
    · simp [h1, h2]
    · simp [h1, h2]

theorem cumul_add_le_sum {k : ℕ} (c : Fin k → ℕ) (y : Fin k) :
    cumul c y + c y ≤ ∑ z, c z := by
  rw [cumul_split_sum]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : z.1 < y.1 ∨ z = y
  · rw [if_pos hz]
  · rw [if_neg hz]
    exact Nat.zero_le _

theorem cumul_mono {k : ℕ} (c : Fin k → ℕ) {y1 y2 : Fin k} (h : y1.1 < y2.1) :
    cumul c y1 + c y1 ≤ cumul c y2 := by
  rw [cumul_split_sum, cumul_ite]
  apply Finset.sum_le_sum
  intro z _
  by_cases hz : z.1 < y1.1 ∨ z = y1
  · have hlt : z.1 < y2.1 := by
      rcases hz with hlt | rfl
      · exact lt_trans hlt h
      · exact h
    rw [if_pos hz, if_pos hlt]
  · rw [if_neg hz]
    exact Nat.zero_le _

theorem exists_bucket {k : ℕ} :
    ∀ (c : Fin k → ℕ) (r : ℕ), r < ∑ y, c y →
      ∃ y, cumul c y ≤ r ∧ r < cumul c y + c y := by
  induction k with
  | zero =>
      intro c r hr
      simp at hr
  | succ k ih =>
      intro c r hr
      rw [Fin.sum_univ_succ] at hr
      cases lt_or_ge r (c 0) with
      | inl hlt =>
          refine ⟨0, ?_, ?_⟩
          · simp [cumul]
          · simpa [cumul] using hlt
      | inr hge =>
          have hr' : r - c 0 < ∑ i : Fin k, c i.succ :=
            Nat.sub_lt_left_of_lt_add hge hr
          obtain ⟨i, h1, h2⟩ := ih (fun j => c j.succ) (r - c 0) hr'
          refine ⟨i.succ, ?_, ?_⟩
          · rw [cumul_succ]
            exact le_trans (Nat.add_le_add_left h1 (c 0)) (le_of_eq (Nat.add_sub_of_le hge))
          · rw [cumul_succ]
            have hlt := Nat.add_lt_add_left h2 (c 0)
            rw [Nat.add_sub_of_le hge] at hlt
            simpa [Nat.add_assoc] using hlt

theorem bucket_unique {k : ℕ} (c : Fin k → ℕ) {y1 y2 : Fin k} {r : ℕ}
    (h1 : cumul c y1 ≤ r ∧ r < cumul c y1 + c y1)
    (h2 : cumul c y2 ≤ r ∧ r < cumul c y2 + c y2) : y1 = y2 := by
  by_contra hne
  have hlt : y1.1 ≠ y2.1 := fun heq => hne (Fin.ext heq)
  rcases Nat.lt_or_gt_of_ne hlt with h | h
  · have := cumul_mono c h
    omega
  · have := cumul_mono c h
    omega

def bucketOf {k : ℕ} (c : Fin k → ℕ) (hk : 0 < k) (r : ℕ) : Fin k :=
  if h : ∃ y, cumul c y ≤ r ∧ r < cumul c y + c y then Classical.choose h else ⟨0, hk⟩

theorem bucketOf_spec {k : ℕ} (c : Fin k → ℕ) (hk : 0 < k) {r : ℕ}
    (hr : r < ∑ y, c y) :
    cumul c (bucketOf c hk r) ≤ r ∧ r < cumul c (bucketOf c hk r) + c (bucketOf c hk r) := by
  have hex := exists_bucket c r hr
  simp only [bucketOf, hex, dite_true]
  exact Classical.choose_spec hex

theorem bucketOf_eq {k : ℕ} (c : Fin k → ℕ) (hk : 0 < k) {y : Fin k} {r : ℕ}
    (hr : r < ∑ z, c z) (h : cumul c y ≤ r ∧ r < cumul c y + c y) :
    bucketOf c hk r = y :=
  bucket_unique c (bucketOf_spec c hk hr) h

def rankOf (s : Finset (Fin m)) (i : Fin m) (hi : i ∈ s) : ℕ :=
  ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).1

theorem rankOf_lt (s : Finset (Fin m)) (i : Fin m) (hi : i ∈ s) :
    rankOf s i hi < s.card :=
  ((s.orderIsoOfFin rfl).symm ⟨i, hi⟩).2

theorem rankOf_iso (s : Finset (Fin m)) (r : Fin s.card) :
    rankOf s ((s.orderIsoOfFin rfl) r).1 ((s.orderIsoOfFin rfl) r).2 = r.1 := by
  unfold rankOf
  exact congrArg Fin.val ((s.orderIsoOfFin rfl).symm_apply_apply r)

theorem card_rank_Ico {n lo len : ℕ} (h : lo + len ≤ n) :
    ((Finset.univ : Finset (Fin n)).filter fun i => lo ≤ i.1 ∧ i.1 < lo + len).card = len := by
  classical
  let f : Fin len → Fin n := fun i => ⟨lo + i.1, by
    have hlt : lo + i.1 < lo + len := Nat.add_lt_add_left i.isLt lo
    exact lt_of_lt_of_le hlt h⟩
  refine (Finset.card_bij (s := (Finset.univ : Finset (Fin len)))
      (t := Finset.univ.filter fun i : Fin n => lo ≤ i.1 ∧ i.1 < lo + len)
      (fun i _ => f i) ?_ ?_ ?_).symm.trans (by simp)
  · intro i _
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact Nat.le_add_right lo i.1
    · exact Nat.add_lt_add_left i.isLt lo
  · intro i _ i' _ heq
    apply Fin.ext
    have hv := congrArg Fin.val heq
    exact Nat.add_left_cancel hv
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨⟨b.1 - lo, Nat.sub_lt_left_of_lt_add hb.1 hb.2⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    simp [f]
    exact Nat.add_sub_of_le hb.1

theorem bucket_card {k : ℕ} (c : Fin k → ℕ) (hk : 0 < k) (s : Finset (Fin m))
    (hsum : ∑ y, c y = s.card) (y : Fin k) :
    (s.filter fun i =>
      ∃ hi : i ∈ s, bucketOf c hk (rankOf s i hi) = y).card = c y := by
  classical
  have hle : cumul c y + c y ≤ s.card := by
    rw [← hsum]
    exact cumul_add_le_sum c y
  let t := s.filter fun i => ∃ hi : i ∈ s, bucketOf c hk (rankOf s i hi) = y
  let ranks := (Finset.univ : Finset (Fin s.card)).filter fun r =>
    cumul c y ≤ r.1 ∧ r.1 < cumul c y + c y
  have hrank : ranks.card = c y := by
    simpa [ranks] using card_rank_Ico (n := s.card) (lo := cumul c y) (len := c y) hle
  have hbij : ranks.card = t.card := by
    refine Finset.card_bij (s := ranks) (t := t)
      (fun r (_ : r ∈ ranks) => ((s.orderIsoOfFin rfl) r).1) ?_ ?_ ?_
    · intro r hr
      simp only [ranks, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      have hmem := ((s.orderIsoOfFin rfl) r).2
      have hrlt : r.1 < ∑ z, c z := by simpa [hsum] using r.isLt
      have hb := bucketOf_eq c hk hrlt hr
      have hrk : rankOf s ((s.orderIsoOfFin rfl) r).1 ((s.orderIsoOfFin rfl) r).2 = r.1 :=
        rankOf_iso s r
      rw [← hrk] at hb
      refine Finset.mem_filter.mpr ⟨hmem, hmem, hb⟩
    · intro r _ r' _ heq
      apply (s.orderIsoOfFin rfl).injective
      exact Subtype.ext heq
    · intro i hi
      simp only [t, Finset.mem_filter] at hi
      rcases hi with ⟨his, hiB⟩
      rcases hiB with ⟨hi', hb⟩
      have hrlt : rankOf s i hi' < ∑ z, c z := by
        simpa [hsum] using rankOf_lt s i hi'
      have hint := by
        have hspec := bucketOf_spec c hk hrlt
        simpa [hb] using hspec
      let r : Fin s.card := (s.orderIsoOfFin rfl).symm ⟨i, his⟩
      have hrk : rankOf s i his = r.1 := rfl
      have heq : hi' = his := Subsingleton.elim _ _
      refine ⟨r, ?_, ?_⟩
      · have hint' : cumul c y ≤ r.1 ∧ r.1 < cumul c y + c y := by
          simpa [heq, hrk] using hint
        simp [ranks, hint']
      · exact congrArg Subtype.val ((s.orderIsoOfFin rfl).apply_symm_apply ⟨i, his⟩)
  exact hbij.symm.trans hrank

/-! ## Counts along one history -/

def policyThrough {T : Tree} : Hist T → Policy T
  | .here => defaultPolicy T
  | .under a y t => extendPol a y (policyThrough t)

theorem policyThrough_follows {T : Tree} (h : Hist T) :
    followsHist h (policyThrough h) := by
  induction h with
  | here => simp [policyThrough, followsHist]
  | under a y t ih =>
      exact follows_extendPol a y t (policyThrough t) ih

def countOf {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) (h : Hist T) (lam : ℝ) : ℕ :=
  classCount active w lam f (policyThrough h) h

theorem count_stable_eq {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) (hstab : CountStable active w f)
    (h : Hist T) (lam : ℝ) (π : Policy T) (hπ : followsHist h π) :
    classCount active w lam f π h = countOf active w f h lam :=
  hstab h lam π (policyThrough h) hπ (policyThrough_follows h)

theorem count_here {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) (lam : ℝ) :
    countOf active w f (.here : Hist T) lam =
      (active.filter fun i => w i = lam).card := by
  simp [countOf, classCount, extendsHist]

theorem sum_unique {α : Type*} [Fintype α] [DecidableEq α] {k : ℕ}
    (s : Finset α) (p : Fin k → α → Prop) [∀ y i, Decidable (p y i)]
    (h : ∀ i ∈ s, ∃! y, p y i) :
    ∑ y, (s.filter fun i => p y i).card = s.card := by
  classical
  have hsum : ∀ i ∈ s, ∑ y, (if p y i then (1 : ℕ) else 0) = 1 := by
    intro i hi
    obtain ⟨y0, hy0, hunq⟩ := h i hi
    rw [Finset.sum_eq_single y0]
    · simp [hy0]
    · intro y _ hy
      have : ¬ p y i := fun hp => hy (hunq y hp)
      simp [this]
    · intro hy
      exact (hy (Finset.mem_univ y0)).elim
  calc
    ∑ y, (s.filter fun i => p y i).card
        = ∑ y, ∑ i ∈ s, (if p y i then 1 else 0) := by
          refine Finset.sum_congr rfl ?_
          intro y _
          rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ i ∈ s, ∑ y, (if p y i then 1 else 0) := Finset.sum_comm
    _ = ∑ i ∈ s, 1 := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hsum i hi
    _ = s.card := by rw [← Finset.card_eq_sum_ones]

/-! ## Prefix mass does not depend on the policy that follows it -/

theorem hit_under {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ} {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (a : Fin nA) (y0 : Fin (nY a)) (t : Hist (child a y0))
    (π : Policy (.node nA hA nY hY K Kpos Ksum child)) (hπ : π.1 = a) :
    hitMass (extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y0 t)) π =
      K a y0 * hitMass (extendsHist t) (π.2 a y0) := by
  unfold hitMass
  simp only [policySum]
  rw [hπ]
  rw [Finset.sum_eq_single y0]
  · rw [← policySum_mul]
    apply congrArg (fun g => policySum g (π.2 a y0))
    funext ℓc
    rw [extends_mk a y0 t ℓc]
    by_cases ht : extendsHist t ℓc
    · simp [ht, leafMass]
    · simp [ht]
  · intro y _ hy
    have hzero : ∀ ℓc,
        ¬ extendsHist (@Hist.under nA hA nY hY K Kpos Ksum child a y0 t)
            (⟨a, y, ℓc⟩ : Leaf (.node nA hA nY hY K Kpos Ksum child)) :=
      fun ℓc => not_extends_mk a hy t ℓc
    simp only [hzero, ite_false]
    exact policySum_zero _
  · intro hy
    exact (hy (Finset.mem_univ y0)).elim

theorem hitMass_extends {T : Tree} (h : Hist T) {π ρ : Policy T}
    (hπ : followsHist h π) (hρ : followsHist h ρ) :
    hitMass (extendsHist h) π = hitMass (extendsHist h) ρ := by
  induction h with
  | here =>
      simp [hitMass, extendsHist, policySum_leafMass]
  | under a y t ih =>
      rcases hπ with ⟨hπa, hπt⟩
      rcases hρ with ⟨hρa, hρt⟩
      have hπt' : followsHist t (π.2 a y) := by simpa [hπa] using hπt
      have hρt' : followsHist t (ρ.2 a y) := by simpa [hρa] using hρt
      rw [hit_under a y t π hπa, hit_under a y t ρ hρa]
      rw [ih hπt' hρt']

/-! ## Class-count separation -/

def extSet {T : Tree} (f : Decoder (m := m) T) (π : Policy T) (h : Hist T) :
    Finset (Fin m) :=
  Finset.univ.filter fun i => extendsHist h (f π i).1

theorem classCount_ext {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) (π : Policy T) (h : Hist T) (lam : ℝ) :
    classCount active w lam f π h =
      (classSlice w (active.filter fun i => extendsHist h (f π i).1) lam).card := by
  simp only [classCount, classSlice]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hi, hw, he⟩
    exact ⟨⟨hi, he⟩, hw⟩
  · intro ⟨⟨hi, he⟩, hw⟩
    exact ⟨hi, hw, he⟩

theorem classCount_univ_ext {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (π : Policy T) (h : Hist T) (lam : ℝ) :
    classCount Finset.univ w lam f π h = (classSlice w (extSet f π h) lam).card := by
  simpa [extSet] using
    classCount_ext (Finset.univ : Finset (Fin m)) w f π h lam

theorem subsetSum_ext {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (π : Policy T) (h : Hist T) :
    subsetSum w (extSet f π h) = seedMass w (fun i => extendsHist h (f π i).1) := by
  simp [subsetSum, seedMass, extSet]

def classCountsEq (w : Fin m → ℝ) (A B : Finset (Fin m)) : Prop :=
  ∀ lam ∈ (Finset.univ : Finset (Fin m)).image w,
    (classSlice w A lam).card = (classSlice w B lam).card

theorem classCountsEq_all (w : Fin m → ℝ) {A B : Finset (Fin m)}
    (h : classCountsEq w A B) (lam : ℝ) :
    (classSlice w A lam).card = (classSlice w B lam).card := by
  by_cases hmem : lam ∈ (Finset.univ : Finset (Fin m)).image w
  · exact h lam hmem
  · have hemptyA : classSlice w A lam = ∅ := by
      ext i
      simp only [classSlice, Finset.mem_filter]
      constructor
      · intro ⟨hi, hw⟩
        exact False.elim (hmem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hw⟩))
      · intro hempty
        cases hempty
    have hemptyB : classSlice w B lam = ∅ := by
      ext i
      simp only [classSlice, Finset.mem_filter]
      constructor
      · intro ⟨hi, hw⟩
        exact False.elim (hmem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hw⟩))
      · intro hempty
        cases hempty
    simp [hemptyA, hemptyB]

def relPairs (w : Fin m → ℝ) : Finset (Finset (Fin m) × Finset (Fin m)) :=
  Finset.univ.filter fun p => ¬ classCountsEq w p.1 p.2

def relGapSet (w : Fin m → ℝ) : Finset ℝ :=
  (relPairs w).image fun p => |subsetSum w p.1 - subsetSum w p.2|

theorem relGapSet_nonempty {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) :
    (relGapSet (m := m) w).Nonempty := by
  let i0 : Fin m := ⟨0, hm⟩
  have hne : ¬ classCountsEq w (∅ : Finset (Fin m)) {i0} := by
    intro h
    have himg : w i0 ∈ (Finset.univ : Finset (Fin m)).image w :=
      Finset.mem_image.mpr ⟨i0, Finset.mem_univ _, rfl⟩
    have hc := h (w i0) himg
    have hL : classSlice w (∅ : Finset (Fin m)) (w i0) = ∅ := by simp [classSlice]
    have hR : (classSlice w ({i0} : Finset (Fin m)) (w i0)).Nonempty := by
      refine ⟨i0, ?_⟩
      simp [classSlice]
    rw [hL, Finset.card_empty] at hc
    have hpos : 0 < (classSlice w ({i0} : Finset (Fin m)) (w i0)).card :=
      Finset.card_pos.mpr hR
    exact lt_irrefl _ (hc.symm ▸ hpos)
  refine ⟨|subsetSum w (∅ : Finset (Fin m)) - subsetSum w {i0}|, ?_⟩
  exact Finset.mem_image.mpr ⟨(∅, {i0}), by simp [relPairs, hne], rfl⟩

def deltaRel {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) : ℝ :=
  (relGapSet w).min' (relGapSet_nonempty hm w)

theorem deltaRel_le {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ)
    {A B : Finset (Fin m)} (h : ¬ classCountsEq w A B) :
    deltaRel hm w ≤ |subsetSum w A - subsetSum w B| := by
  have hp : (A, B) ∈ relPairs w := by simp [relPairs, h]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(A, B), hp, rfl⟩)

theorem exists_delta_pair {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) :
    ∃ A B : Finset (Fin m), ¬ classCountsEq w A B ∧
      |subsetSum w A - subsetSum w B| = deltaRel hm w := by
  have hmem := Finset.min'_mem (relGapSet w) (relGapSet_nonempty hm w)
  obtain ⟨p, hp, hg⟩ := Finset.mem_image.mp hmem
  refine ⟨p.1, p.2, ?_, hg⟩
  simpa [relPairs] using hp

theorem ext_mass_close {T : Tree} (w : Fin m → ℝ) (ε : ℝ)
    (f : Decoder (m := m) T) (hf : Accurate w ε f) (h : Hist T)
    {π ρ : Policy T} (hπ : followsHist h π) (hρ : followsHist h ρ) :
    |subsetSum w (extSet f π h) - subsetSum w (extSet f ρ h)| ≤ 2 * ε := by
  have hhit := hitMass_extends h hπ hρ
  have hπe := hf π (extendsHist h)
  have hρe := hf ρ (extendsHist h)
  have hsmπ := subsetSum_ext w f π h
  have hsmρ := subsetSum_ext w f ρ h
  have habs : ∀ x y : ℝ, |x + y| ≤ |x| + |y| := by
    intro x y
    rcases le_total 0 (x + y) with hxy | hxy
    · rw [abs_of_nonneg hxy]
      linarith [le_abs_self x, le_abs_self y]
    · rw [abs_of_nonpos hxy]
      linarith [neg_abs_le x, neg_abs_le y]
  have htri : |subsetSum w (extSet f π h) - subsetSum w (extSet f ρ h)| ≤
      |subsetSum w (extSet f π h) - hitMass (extendsHist h) π| +
      |subsetSum w (extSet f ρ h) - hitMass (extendsHist h) ρ| := by
    have hstep : subsetSum w (extSet f π h) - subsetSum w (extSet f ρ h) =
        (subsetSum w (extSet f π h) - hitMass (extendsHist h) π) +
          (hitMass (extendsHist h) ρ - subsetSum w (extSet f ρ h)) := by
      rw [hhit]
      ring
    rw [hstep]
    have hle := habs
      (subsetSum w (extSet f π h) - hitMass (extendsHist h) π)
      (hitMass (extendsHist h) ρ - subsetSum w (extSet f ρ h))
    refine hle.trans ?_
    rw [abs_sub_comm (hitMass (extendsHist h) ρ) (subsetSum w (extSet f ρ h))]
  have hπe' : |subsetSum w (extSet f π h) - hitMass (extendsHist h) π| ≤ ε := by
    simpa [hsmπ] using hπe
  have hρe' : |subsetSum w (extSet f ρ h) - hitMass (extendsHist h) ρ| ≤ ε := by
    simpa [hsmρ] using hρe
  linarith

theorem accurate_count_stable {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) (ε : ℝ)
    (hlt : 2 * ε < deltaRel hm w) {T : Tree} (f : Decoder (m := m) T)
    (hf : Accurate w ε f) :
    CountStable (Finset.univ : Finset (Fin m)) w f := by
  intro h lam π ρ hπ hρ
  by_contra hne
  let A := extSet f π h
  let B := extSet f ρ h
  have hdiff : ¬ classCountsEq w A B := by
    intro heq
    apply hne
    have hc := classCountsEq_all w heq lam
    simpa [classCount_univ_ext w f π h lam, classCount_univ_ext w f ρ h lam, A, B] using hc
  have hle := deltaRel_le hm w hdiff
  have hclose := ext_mass_close w ε f hf h hπ hρ
  linarith

/-! ## One node of the gluing -/

include nA hA nY hY K Kpos Ksum child

local notation "nodeT" => Tree.node nA hA nY hY K Kpos Ksum child

def stepHist (a : Fin nA) (y : Fin (nY a)) : Hist nodeT :=
  Hist.under a y (.here : Hist (child a y))

def ePol (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y)) : Policy nodeT :=
  (a, fun a' y' =>
    if ha : a' = a then
      if hy : y' = ha ▸ y then
        cast (by subst ha; subst hy; rfl) ρ
      else
        defaultPolicy (child a' y')
    else
      defaultPolicy (child a' y'))

theorem ePol_child (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y)) :
    ((ePol a y ρ : Policy nodeT).2 a y) = ρ := by
  simp [ePol, cast_eq]

theorem unique_step (a1 : Fin nA) (π : Policy nodeT) (hπ : π.1 = a1)
    (f : Decoder (m := m) nodeT) (i : Fin m) :
    ∃! y : Fin (nY a1), extendsHist (stepHist a1 y) (f π i).1 := by
  rcases f π i with ⟨ℓ, hc⟩
  rcases ℓ with ⟨a0, y0, ℓc⟩
  have ha0 : a0 = π.1 := hc.1
  have ha : a0 = a1 := ha0.trans hπ
  obtain rfl := ha
  refine ⟨y0, ?_, ?_⟩
  · exact (extends_here_iff a0 y0 (⟨a0, y0, ℓc⟩ : Leaf nodeT)).2 ⟨rfl, by simp⟩
  · intro y hy
    rcases (extends_here_iff a0 y (⟨a0, y0, ℓc⟩ : Leaf nodeT)).1 hy with ⟨_, hy'⟩
    exact hy'.symm

theorem step_class_sum (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (lam : ℝ) :
    ∑ y, countOf active w f (stepHist a y) lam = (classSlice w active lam).card := by
  let y0 : Fin (nY a) := ⟨0, hY a⟩
  let π : Policy nodeT := ePol a y0 (defaultPolicy (child a y0))
  have hfol : ∀ y, followsHist (stepHist a y) (π : Policy nodeT) := fun _ => ⟨rfl, trivial⟩
  let s := classSlice w active lam
  have huniq : ∀ i ∈ s, ∃! y, extendsHist (stepHist a y) (f π i).1 :=
    fun i _ => unique_step a π rfl f i
  have hfilt : ∀ y, classCount active w lam f π (stepHist a y) =
      (s.filter fun i => extendsHist (stepHist a y) (f π i).1).card := by
    intro y
    simp only [classCount, s, classSlice]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨hi, hw, he⟩
      exact ⟨⟨hi, hw⟩, he⟩
    · intro ⟨⟨hi, hw⟩, he⟩
      exact ⟨hi, hw, he⟩
  have hct : ∀ y, countOf active w f (stepHist a y) lam =
      (s.filter fun i => extendsHist (stepHist a y) (f π i).1).card := by
    intro y
    exact (count_stable_eq active w f hstab (stepHist a y) lam π (hfol y)).symm.trans (hfilt y)
  have hsum : ∑ y, (s.filter fun i => extendsHist (stepHist a y) (f π i).1).card = s.card :=
    sum_unique s (fun y i => extendsHist (stepHist a y) (f π i).1) huniq
  have hcong : ∑ y, countOf active w f (stepHist a y) lam =
      ∑ y, (s.filter fun i => extendsHist (stepHist a y) (f π i).1).card := by
    refine Finset.sum_congr rfl ?_
    intro y _
    exact hct y
  exact hcong.trans hsum

def fixedThru (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (a : Fin nA) (y : Fin (nY a)) : Finset (Fin m) :=
  Finset.univ.filter fun i =>
    ∃ hi : i ∈ active,
      bucketOf (fun z => countOf active w f (stepHist a z) (w i)) (hY a)
        (rankOf (classSlice w active (w i)) i (classSlice_self w active i hi)) = y

def polThru (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (a : Fin nA) (y : Fin (nY a))
    (ρ : Policy (child a y)) : Finset (Fin m) :=
  active.filter fun i => extendsHist (stepHist a y) (f (ePol a y ρ) i).1

theorem follows_step (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y)) :
    followsHist (stepHist a y) (ePol a y ρ : Policy nodeT) :=
  ⟨rfl, trivial⟩

theorem pol_class_card (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y)) (lam : ℝ) :
    (classSlice w (polThru active w f a y ρ) lam).card =
      countOf active w f (stepHist a y) lam := by
  have hcount := count_stable_eq active w f hstab (stepHist a y) lam
    (ePol a y ρ) (follows_step a y ρ)
  rw [← hcount]
  congr 1
  ext i
  simp only [classCount, classSlice, polThru, Finset.mem_filter]
  exact ⟨fun ⟨⟨ha, he⟩, hw⟩ => ⟨ha, hw, he⟩, fun ⟨ha, hw, he⟩ => ⟨⟨ha, he⟩, hw⟩⟩

theorem fixed_class_card (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (lam : ℝ) (y : Fin (nY a)) :
    (classSlice w (fixedThru active w f a y) lam).card =
      countOf active w f (stepHist a y) lam := by
  let s := classSlice w active lam
  let c : Fin (nY a) → ℕ := fun z => countOf active w f (stepHist a z) lam
  have hsum := step_class_sum active w f hstab a lam
  have hb := bucket_card c (hY a) s hsum y
  have hEq : classSlice w (fixedThru active w f a y) lam =
      s.filter fun i => ∃ hi : i ∈ s, bucketOf c (hY a) (rankOf s i hi) = y := by
    ext i
    unfold classSlice fixedThru s c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hiA, hbkt⟩, hw⟩
      have his : i ∈ classSlice w active lam := by
        simp [classSlice, Finset.mem_filter, hiA, hw]
      refine ⟨his, his, ?_⟩
      simp only [hw] at hbkt
      simpa using hbkt
    · rintro ⟨his, hi, hbkt⟩
      have hiA : i ∈ active := by
        simp [classSlice, Finset.mem_filter] at his
        exact his.1
      have hw : w i = lam := by
        simp [classSlice, Finset.mem_filter] at his
        exact his.2
      refine ⟨⟨hiA, ?_⟩, hw⟩
      simpa [hw] using hbkt
  rw [hEq]
  exact hb

theorem carried_child (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (ℓ : Leaf nodeT) (hext : extendsHist (stepHist a y) ℓ)
    (hc : CompatiblePolicy ℓ (ePol a y ρ : Policy nodeT)) :
    CompatiblePolicy
      (pushChild ℓ.2.2
        ((extends_here_iff a y ℓ).1 hext).choose
        ((extends_here_iff a y ℓ).1 hext).choose_spec) ρ := by
  have hex := (extends_here_iff a y ℓ).1 hext
  obtain rfl := hex.choose
  have hy := hex.choose_spec
  simp only [cast_eq] at hy
  obtain rfl := hy
  have hpush : pushChild ℓ.2.2 rfl rfl = ℓ.2.2 := pushChild_rfl ℓ.1 ℓ.2.1 ℓ.2.2 rfl rfl
  rw [hpush]
  have hc2 := hc.2
  simpa [ePol, ePol_child] using hc2

theorem extends_longer (a : Fin nA) (y : Fin (nY a)) (t : Hist (child a y))
    (ℓ : Leaf nodeT) :
    extendsHist (Hist.under a y t) ℓ → extendsHist (stepHist a y) ℓ := by
  intro h
  rcases h with ⟨ha, hy, _⟩
  exact ⟨ha, hy, trivial⟩

theorem sliceCard (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y)) (lam : ℝ) :
    (classSlice w (fixedThru active w f a y) lam).card =
      (classSlice w (polThru active w f a y ρ) lam).card := by
  rw [fixed_class_card active w f hstab a lam y,
    pol_class_card active w f hstab a y ρ lam]

noncomputable def transported (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (i : Fin m) (hi : i ∈ fixedThru active w f a y) : Fin m :=
  (pieceEquiv (sliceCard active w f hstab a y ρ (w i))
    ⟨i, classSlice_self w (fixedThru active w f a y) i hi⟩).1

theorem transported_mem (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (i : Fin m) (hi : i ∈ fixedThru active w f a y) :
    transported active w f hstab a y ρ i hi ∈
      classSlice w (polThru active w f a y ρ) (w i) :=
  (pieceEquiv (sliceCard active w f hstab a y ρ (w i))
    ⟨i, classSlice_self w (fixedThru active w f a y) i hi⟩).2

theorem transported_extends (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (i : Fin m) (hi : i ∈ fixedThru active w f a y) :
    extendsHist (stepHist a y)
      (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1 := by
  have hjmem := transported_mem active w f hstab a y ρ i hi
  unfold classSlice polThru at hjmem
  rw [Finset.mem_filter, Finset.mem_filter] at hjmem
  exact hjmem.1.2

theorem transported_eq_piece (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (lam : ℝ) (i : Fin m) (hiF : i ∈ fixedThru active w f a y)
    (his : i ∈ classSlice w (fixedThru active w f a y) lam) (hw : w i = lam) :
    transported active w f hstab a y ρ i hiF =
      (pieceEquiv (sliceCard active w f hstab a y ρ lam) ⟨i, his⟩).1 := by
  subst hw
  unfold transported
  have hs : (⟨i, classSlice_self w (fixedThru active w f a y) i hiF⟩ :
      {x // x ∈ classSlice w (fixedThru active w f a y) (w i)}) = ⟨i, his⟩ :=
    Subtype.ext rfl
  exact congrArg
    (fun z : {x // x ∈ classSlice w (fixedThru active w f a y) (w i)} =>
      (pieceEquiv (sliceCard active w f hstab a y ρ (w i)) z).1) hs

noncomputable def childLeafOf (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (i : Fin m) (hi : i ∈ fixedThru active w f a y) : Leaf (child a y) :=
  pushChild (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1.2.2
    ((extends_here_iff a y
        (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1).1
      (transported_extends active w f hstab a y ρ i hi)).choose
    ((extends_here_iff a y
        (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1).1
      (transported_extends active w f hstab a y ρ i hi)).choose_spec

theorem childLeaf_compat (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (i : Fin m) (hi : i ∈ fixedThru active w f a y) :
    CompatiblePolicy (childLeafOf active w f hstab a y ρ i hi) ρ := by
  simpa [childLeafOf] using
    carried_child a y ρ
      (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1
      (transported_extends active w f hstab a y ρ i hi)
      (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).2

theorem childLeaf_extends (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (t : Hist (child a y))
    (ρ : Policy (child a y)) (i : Fin m) (hi : i ∈ fixedThru active w f a y) :
    extendsHist t (childLeafOf active w f hstab a y ρ i hi) ↔
      extendsHist (Hist.under a y t)
        (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1 := by
  simpa [childLeafOf] using
    (extends_push t
      (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1
      ((extends_here_iff a y
          (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1).1
        (transported_extends active w f hstab a y ρ i hi)).choose
      ((extends_here_iff a y
          (f (ePol a y ρ) (transported active w f hstab a y ρ i hi)).1).1
        (transported_extends active w f hstab a y ρ i hi)).choose_spec).symm

noncomputable def childDec (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) : Decoder (m := m) (child a y) :=
  fun ρ i =>
    if hi : i ∈ fixedThru active w f a y then
      ⟨childLeafOf active w f hstab a y ρ i hi,
        childLeaf_compat active w f hstab a y ρ i hi⟩
    else
      ⟨run (defaultStrategy (child a y)) ρ, run_compatible_policy _ ρ⟩

theorem childDec_mem (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (i : Fin m) (hi : i ∈ fixedThru active w f a y) :
    (childDec active w f hstab a y ρ i).1 =
      childLeafOf active w f hstab a y ρ i hi := by
  simp [childDec, hi]

theorem child_count (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) (ρ : Policy (child a y))
    (t : Hist (child a y)) (lam : ℝ) :
    classCount (fixedThru active w f a y) w lam
        (childDec active w f hstab a y) ρ t =
      classCount active w lam f (ePol a y ρ : Policy nodeT)
        (Hist.under a y t) := by
  classical
  let fix := fixedThru active w f a y
  let g := childDec active w f hstab a y
  let s := classSlice w fix lam
  let tgt := classSlice w (polThru active w f a y ρ) lam
  have hsc : s.card = tgt.card := sliceCard active w f hstab a y ρ lam
  let p : Fin m → Prop := fun j =>
    extendsHist (Hist.under a y t) (f (ePol a y ρ) j).1
  have hleft : classCount fix w lam g ρ t =
      (s.filter fun i => extendsHist t (g ρ i).1).card := by
    simp only [classCount, s, classSlice]
    congr 1
    ext i
    simp only [Finset.mem_filter]
    exact ⟨fun ⟨hi, hw, he⟩ => ⟨⟨hi, hw⟩, he⟩, fun ⟨⟨hi, hw⟩, he⟩ => ⟨hi, hw, he⟩⟩
  have hmid : (s.filter fun i => extendsHist t (g ρ i).1) =
      s.filter fun i => ∃ hi : i ∈ s, p ((pieceEquiv hsc ⟨i, hi⟩).1) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · intro ⟨his, he⟩
      have hiF : i ∈ fix := classSlice_subset w fix lam his
      have hw : w i = lam :=
        (Finset.mem_filter.mp (show i ∈ classSlice w fix lam from by simpa [s] using his)).2
      have hleaf : (g ρ i).1 = childLeafOf active w f hstab a y ρ i hiF :=
        childDec_mem active w f hstab a y ρ i hiF
      have hext :=
        (childLeaf_extends active w f hstab a y t ρ i hiF).1 (hleaf ▸ he)
      have htr := transported_eq_piece active w f hstab a y ρ lam i hiF his hw
      refine ⟨his, his, ?_⟩
      simpa [p, htr] using hext
    · intro ⟨his, hex⟩
      rcases hex with ⟨hi, hp⟩
      have hiF : i ∈ fix := classSlice_subset w fix lam his
      have hw : w i = lam :=
        (Finset.mem_filter.mp (show i ∈ classSlice w fix lam from by simpa [s] using his)).2
      have htr := transported_eq_piece active w f hstab a y ρ lam i hiF his hw
      have hext : extendsHist (Hist.under a y t)
          (f (ePol a y ρ) (transported active w f hstab a y ρ i hiF)).1 := by
        simpa [p, htr] using hp
      have he : extendsHist t (childLeafOf active w f hstab a y ρ i hiF) :=
        (childLeaf_extends active w f hstab a y t ρ i hiF).2 hext
      refine ⟨his, ?_⟩
      simpa [g, childDec_mem active w f hstab a y ρ i hiF] using he
  have hslice := slice_pred_card hsc p
  have hright : (tgt.filter fun j => p j).card =
      classCount active w lam f (ePol a y ρ) (Hist.under a y t) := by
    simp only [classCount]
    congr 1
    ext j
    constructor
    · intro hj
      have htgt : j ∈ tgt := (Finset.mem_filter.mp hj).1
      have hpj : p j := (Finset.mem_filter.mp hj).2
      have hpw : j ∈ polThru active w f a y ρ ∧ w j = lam := by
        simpa [tgt, classSlice, Finset.mem_filter] using htgt
      have hact : j ∈ active ∧
          extendsHist (stepHist a y) (f (ePol a y ρ) j).1 := by
        simpa [polThru, Finset.mem_filter] using hpw.1
      exact Finset.mem_filter.mpr ⟨hact.1, ⟨hpw.2, by simpa [p] using hpj⟩⟩
    · intro hj
      have hmem := Finset.mem_filter.mp hj
      have ha : j ∈ active := hmem.1
      have hw : w j = lam := hmem.2.1
      have he : extendsHist (Hist.under a y t) (f (ePol a y ρ) j).1 := hmem.2.2
      have hstep : extendsHist (stepHist a y) (f (ePol a y ρ) j).1 :=
        extends_longer a y t _ he
      have hp : j ∈ polThru active w f a y ρ := by
        exact Finset.mem_filter.mpr ⟨ha, hstep⟩
      have ht : j ∈ tgt := by
        exact Finset.mem_filter.mpr ⟨hp, hw⟩
      exact Finset.mem_filter.mpr ⟨ht, by simpa [p] using he⟩
  exact hleft.trans (congrArg Finset.card hmid |>.trans (hslice.trans hright))

theorem child_stable (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) nodeT) (hstab : CountStable active w f)
    (a : Fin nA) (y : Fin (nY a)) :
    CountStable (fixedThru active w f a y) w
      (childDec active w f hstab a y) := by
  intro t lam ρ ρ' hρ hρ'
  have h1 := child_count active w f hstab a y ρ t lam
  have h2 := child_count active w f hstab a y ρ' t lam
  have hfol : followsHist (Hist.under a y t) (ePol a y ρ : Policy nodeT) := by
    refine ⟨rfl, ?_⟩
    rw [ePol_child]
    exact hρ
  have hfol' : followsHist (Hist.under a y t) (ePol a y ρ' : Policy nodeT) := by
    refine ⟨rfl, ?_⟩
    rw [ePol_child]
    exact hρ'
  have heq := hstab (Hist.under a y t) lam (ePol a y ρ) (ePol a y ρ') hfol hfol'
  exact h1.trans (heq.trans h2.symm)

omit nA hA nY hY K Kpos Ksum child

/-! ## Strategies from stable counts -/

theorem classCount_leaf {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
    (f : Decoder (m := m) T) (π : Policy T) (ℓ : Leaf T) (lam : ℝ) :
    classCount active w lam f π (ofLeaf ℓ) =
      (active.filter fun i => w i = lam ∧ (f π i).1 = ℓ).card := by
  simp only [classCount]
  congr 1
  ext i
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hi, hw, he⟩
    exact ⟨hi, hw, (extends_ofLeaf_iff ℓ (f π i).1).1 he⟩
  · intro ⟨hi, hw, he⟩
    exact ⟨hi, hw, (extends_ofLeaf_iff ℓ (f π i).1).2 he⟩

theorem nodeLeaf_eq {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ} {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    {a : Fin nA} {y1 y2 : Fin (nY a)}
    {c1 : Leaf (child a y1)} {c2 : Leaf (child a y2)} :
    (⟨a, y1, c1⟩ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) = ⟨a, y2, c2⟩ ↔
      y1 = y2 ∧ HEq c1 c2 := by
  constructor
  · intro h
    have h1 := (PSigma.mk.inj_iff).mp h
    have hin := eq_of_heq h1.2
    have h2 := (PSigma.mk.inj_iff).mp hin
    exact ⟨h2.1, h2.2⟩
  · rintro ⟨rfl, hc⟩
    obtain rfl := eq_of_heq hc
    rfl

theorem run_triplet {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ} {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (d : Strategy (Tree.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (Tree.node nA hA nY hY K Kpos Ksum child)) :
    run d π =
      ⟨π.1, d.1 π.1, run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))⟩ := rfl

theorem ofLeaf_triplet {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ} {Kpos : ∀ a y, 0 < K a y}
    {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (a : Fin nA) (y : Fin (nY a)) (ℓc : Leaf (child a y)) :
    ofLeaf (pack nA hA nY hY K Kpos Ksum child a y ℓc) =
      Hist.under a y (ofLeaf ℓc) := by
  let ℓ : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) := ⟨a, y, ℓc⟩
  have hp : pack nA hA nY hY K Kpos Ksum child a y ℓc = ℓ := by
    unfold pack ℓ
    apply eq_of_heq
    apply cast_heq
  have hof : ofLeaf ℓ = Hist.under a y (ofLeaf ℓc) := by
    unfold ℓ
    rfl
  simpa [hp] using hof

theorem stable_fiber :
    ∀ {T : Tree} (active : Finset (Fin m)) (w : Fin m → ℝ)
      (f : Decoder (m := m) T),
      CountStable active w f →
        ∃ s : Fin m → Strategy T, FiberAgree active w f s := by
  intro T
  induction T with
  | leaf =>
      intro active w f _
      refine ⟨fun _ => PUnit.unit, ?_⟩
      intro π ℓ _ lam
      cases ℓ
      apply congrArg Finset.card
      ext i
      constructor
      · intro h
        have hmem := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.1, by
          cases (f π i).1
          rfl⟩
      · intro h
        have hmem := Finset.mem_filter.mp h
        exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.1, rfl⟩
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro active w f hstab
      let hex := fun a y =>
        ih a y (fixedThru active w f a y) w (childDec active w f hstab a y)
          (child_stable active w f hstab a y)
      let sch : (a : Fin nA) → (y : Fin (nY a)) → Fin m → Strategy (child a y) :=
        fun a y => Classical.choose (hex a y)
      have hsch : ∀ a y, FiberAgree (fixedThru active w f a y) w
          (childDec active w f hstab a y) (sch a y) :=
        fun a y => Classical.choose_spec (hex a y)
      let out : Fin m → (a : Fin nA) → Fin (nY a) := fun i a =>
        if hi : i ∈ active then
          bucketOf (fun z => countOf active w f (stepHist a z) (w i)) (hY a)
            (rankOf (classSlice w active (w i)) i (classSlice_self w active i hi))
        else
          ⟨0, hY a⟩
      let s : Fin m → Strategy (Tree.node nA hA nY hY K Kpos Ksum child) := fun i =>
        (out i, fun a y =>
          if i ∈ fixedThru active w f a y then sch a y i
          else defaultStrategy (child a y))
      refine ⟨s, ?_⟩
      intro π ℓ hℓ lam
      rcases ℓ with ⟨a, y, ℓc⟩
      rcases hℓ with ⟨ha, hℓc⟩
      have hπ : π.1 = a := ha.symm
      have hfix_act : ∀ {i}, i ∈ fixedThru active w f a y → i ∈ active := by
        intro i hi
        exact (Finset.mem_filter.mp hi).2.choose
      have hout : ∀ i, i ∈ active →
          (out i a = y ↔ i ∈ fixedThru active w f a y) := by
        intro i hi
        constructor
        · intro heq
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨hi, ?_⟩⟩
          simpa [out, hi] using heq
        · intro hmem
          rcases (Finset.mem_filter.mp hmem).2 with ⟨hi', hbkt⟩
          have : hi' = hi := Subsingleton.elim _ _
          simpa [out, hi, this] using hbkt
      have hrun : ∀ i, i ∈ active →
          (run (s i) π = (⟨a, y, ℓc⟩ :
              Leaf (Tree.node nA hA nY hY K Kpos Ksum child)) ↔
            i ∈ fixedThru active w f a y ∧ run (sch a y i) (π.2 a y) = ℓc) := by
        intro i hi
        constructor
        · intro hr
          have hform := run_triplet (s i) π
          rw [hr, hπ] at hform
          have hleaf := (nodeLeaf_eq (hA := hA) (hY := hY) (K := K) (Kpos := Kpos)
            (Ksum := Ksum) (child := child)).mp hform.symm
          have hy : out i a = y := by simpa [s] using hleaf.1
          have hiF : i ∈ fixedThru active w f a y := (hout i hi).1 hy
          have hst : (s i).2 a y = sch a y i := by simp [s, hiF]
          have hs1 : (s i).1 a = y := by simpa [s] using hleaf.1
          have hc : run ((s i).2 a y) (π.2 a y) = ℓc := by
            have hheq := hleaf.2
            rw [hs1] at hheq
            exact eq_of_heq hheq
          exact ⟨hiF, by simpa [hst] using hc⟩
        · intro ⟨hiF, hc⟩
          have hy : out i a = y := (hout i hi).2 hiF
          subst hy
          rw [run_triplet (s i) π, hπ]
          have hs1 : (s i).1 a = out i a := by simp [s]
          have hst : (s i).2 a (out i a) = sch a (out i a) i := by simp [s, hiF]
          apply (nodeLeaf_eq (hA := hA) (hY := hY) (K := K) (Kpos := Kpos)
            (Ksum := Ksum) (child := child)).mpr
          refine ⟨hs1, ?_⟩
          rw [hs1, hst]
          exact heq_of_eq hc
      have hL : (active.filter fun i => w i = lam ∧ run (s i) π = ⟨a, y, ℓc⟩) =
          (fixedThru active w f a y).filter fun i =>
            w i = lam ∧ run (sch a y i) (π.2 a y) = ℓc := by
        ext i
        simp only [Finset.mem_filter]
        constructor
        · intro ⟨hiA, hw, hr⟩
          have hiff := (hrun i hiA).1 hr
          exact ⟨hiff.1, hw, hiff.2⟩
        · intro ⟨hiF, hw, hr⟩
          have hiA := hfix_act hiF
          exact ⟨hiA, hw, (hrun i hiA).2 ⟨hiF, hr⟩⟩
      have hF := hsch a y (π.2 a y) ℓc hℓc lam
      have hC := classCount_leaf (fixedThru active w f a y) w
        (childDec active w f hstab a y) (π.2 a y) ℓc lam
      have hbridge := child_count active w f hstab a y (π.2 a y) (ofLeaf ℓc) lam
      let ℓnode : Leaf (Tree.node nA hA nY hY K Kpos Ksum child) := ⟨a, y, ℓc⟩
      have hpk : pack nA hA nY hY K Kpos Ksum child a y ℓc = ℓnode := by
        unfold pack ℓnode
        apply eq_of_heq
        apply cast_heq
      have hof := ofLeaf_triplet (nA := nA) (hA := hA) (nY := nY) (hY := hY)
        (K := K) (Kpos := Kpos) (Ksum := Ksum) (child := child) a y ℓc
      have hof' : ofLeaf ℓnode = Hist.under a y (ofLeaf ℓc) := by
        simpa [hpk] using hof
      have hfolπ : followsHist (ofLeaf ℓnode) π :=
        compatible_follows ⟨ha, hℓc⟩
      have hfolE : followsHist (ofLeaf ℓnode) (ePol a y (π.2 a y)) := by
        rw [hof']
        refine ⟨rfl, ?_⟩
        rw [ePol_child]
        exact compatible_follows hℓc
      have hmove := hstab (ofLeaf ℓnode) lam (ePol a y (π.2 a y)) π hfolE hfolπ
      have hP := classCount_leaf active w f π ℓnode lam
      calc
        (active.filter fun i => w i = lam ∧ run (s i) π = ℓnode).card
            = ((fixedThru active w f a y).filter fun i =>
                w i = lam ∧ run (sch a y i) (π.2 a y) = ℓc).card := by
              exact congrArg Finset.card hL
          _ = ((fixedThru active w f a y).filter fun i =>
                w i = lam ∧ (childDec active w f hstab a y (π.2 a y) i).1 = ℓc).card := hF
          _ = classCount (fixedThru active w f a y) w lam
                (childDec active w f hstab a y) (π.2 a y) (ofLeaf ℓc) := hC.symm
          _ = classCount active w lam f (ePol a y (π.2 a y))
                (Hist.under a y (ofLeaf ℓc)) := hbridge
          _ = classCount active w lam f (ePol a y (π.2 a y))
                (ofLeaf ℓnode) := by rw [hof']
          _ = classCount active w lam f π (ofLeaf ℓnode) := hmove
          _ = (active.filter fun i => w i = lam ∧ (f π i).1 = ℓnode).card := hP

/-! ## Terminal fibers give the relabeling -/

def runFiber {T : Tree} (w : Fin m → ℝ) (s : Fin m → Strategy T)
    (π : Policy T) (lam : ℝ) (ℓ : Leaf T) : Finset (Fin m) :=
  Finset.univ.filter fun j => w j = lam ∧ run (s j) π = ℓ

def decFiber {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (π : Policy T) (lam : ℝ) (ℓ : Leaf T) : Finset (Fin m) :=
  Finset.univ.filter fun j => w j = lam ∧ (f π j).1 = ℓ

theorem fiber_card {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) (ℓ : Leaf T) (hℓ : CompatiblePolicy ℓ π) (lam : ℝ) :
    (runFiber w s π lam ℓ).card = (decFiber w f π lam ℓ).card := by
  simpa [runFiber, decFiber] using hF π ℓ hℓ lam

theorem runFiber_self {T : Tree} (w : Fin m → ℝ) (s : Fin m → Strategy T)
    (π : Policy T) (i : Fin m) :
    i ∈ runFiber w s π (w i) (run (s i) π) := by
  simp [runFiber]

noncomputable def relabelFun {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) (i : Fin m) : Fin m :=
  (pieceEquiv (fiber_card w f s hF π (run (s i) π)
      (run_compatible_policy (s i) π) (w i)) ⟨i, runFiber_self w s π i⟩).1

theorem relabelFun_mem {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) (i : Fin m) :
    relabelFun w f s hF π i ∈ decFiber w f π (w i) (run (s i) π) :=
  (pieceEquiv (fiber_card w f s hF π (run (s i) π)
      (run_compatible_policy (s i) π) (w i)) ⟨i, runFiber_self w s π i⟩).2

theorem relabelFun_weight {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) (i : Fin m) :
    w (relabelFun w f s hF π i) = w i := by
  have h := Finset.mem_filter.mp (relabelFun_mem w f s hF π i)
  exact h.2.1

theorem relabelFun_run {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) (i : Fin m) :
    (f π (relabelFun w f s hF π i)).1 = run (s i) π := by
  have h := Finset.mem_filter.mp (relabelFun_mem w f s hF π i)
  exact h.2.2

theorem relabelFun_at {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) (i : Fin m) (lam : ℝ) (ℓ : Leaf T)
    (hw : w i = lam) (hr : run (s i) π = ℓ)
    (hi : i ∈ runFiber w s π lam ℓ) :
    relabelFun w f s hF π i =
      (pieceEquiv (fiber_card w f s hF π ℓ (hr ▸ run_compatible_policy (s i) π) lam)
        ⟨i, hi⟩).1 := by
  subst hw
  subst hr
  unfold relabelFun
  apply congrArg (fun z =>
    (pieceEquiv (fiber_card w f s hF π (run (s i) π)
      (run_compatible_policy (s i) π) (w i)) z).1)
  exact Subtype.ext rfl

theorem relabelFun_injective {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s) (π : Policy T) :
    Function.Injective (relabelFun w f s hF π) := by
  intro i1 i2 heq
  have h1 := Finset.mem_filter.mp (relabelFun_mem w f s hF π i1)
  have h2 := Finset.mem_filter.mp (relabelFun_mem w f s hF π i2)
  have hj : relabelFun w f s hF π i1 = relabelFun w f s hF π i2 := heq
  rw [hj] at h1
  have hw : w i1 = w i2 := h1.2.1.symm.trans h2.2.1
  have hℓ : run (s i1) π = run (s i2) π := h1.2.2.symm.trans h2.2.2
  let lam := w i1
  let ℓ := run (s i1) π
  have hw1 : w i1 = lam := rfl
  have hw2 : w i2 = lam := hw.symm
  have hr1 : run (s i1) π = ℓ := rfl
  have hr2 : run (s i2) π = ℓ := hℓ.symm
  have hi1 : i1 ∈ runFiber w s π lam ℓ := by
    simpa [runFiber, hw1, hr1] using runFiber_self w s π i1
  have hi2 : i2 ∈ runFiber w s π lam ℓ := by
    simpa [runFiber, hw2, hr2] using runFiber_self w s π i2
  have e1 := relabelFun_at w f s hF π i1 lam ℓ hw1 hr1 hi1
  have e2 := relabelFun_at w f s hF π i2 lam ℓ hw2 hr2 hi2
  rw [e1, e2] at heq
  have hcard1 := fiber_card w f s hF π ℓ (hr1 ▸ run_compatible_policy (s i1) π) lam
  have hcard2 := fiber_card w f s hF π ℓ (hr2 ▸ run_compatible_policy (s i2) π) lam
  have hsame : (pieceEquiv hcard1 ⟨i2, hi2⟩).1 = (pieceEquiv hcard2 ⟨i2, hi2⟩).1 :=
    (pieceEquiv_val_irrel hcard1 hcard2 ⟨i2, hi2⟩)
  have hvals : (pieceEquiv hcard1 ⟨i1, hi1⟩).1 = (pieceEquiv hcard1 ⟨i2, hi2⟩).1 :=
    heq.trans hsame
  exact congrArg Subtype.val
    ((pieceEquiv hcard1).injective (Subtype.ext hvals))

noncomputable def relabelEquiv {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s)
    (π : Policy T) : Fin m ≃ Fin m :=
  Equiv.ofBijective (relabelFun w f s hF π)
    (relabelFun_injective w f s hF π).bijective_of_finite

theorem fiber_to_repair {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (s : Fin m → Strategy T) (hF : FiberAgree Finset.univ w f s) :
    RelabelRepair w f := by
  refine ⟨relabelEquiv w f s hF, s, ?_, ?_⟩
  · intro π i
    simpa [relabelEquiv, Equiv.ofBijective_apply] using relabelFun_weight w f s hF π i
  · intro π i
    simpa [relabelEquiv, Equiv.ofBijective_apply] using relabelFun_run w f s hF π i

/-- A weight-preserving relabeling and one strategy per seed reproduce the decoder
if and only if every history has a policy-independent count inside each weight class.
No marginal-accuracy hypothesis is used. -/
theorem relabelRepair_iff_countStable {T : Tree} (w : Fin m → ℝ)
    (f : Decoder (m := m) T) :
    RelabelRepair w f ↔ CountStable (Finset.univ : Finset (Fin m)) w f := by
  constructor
  · exact relabel_implies_stable w f
  · intro hstab
    obtain ⟨s, hF⟩ := stable_fiber (Finset.univ : Finset (Fin m)) w f hstab
    exact fiber_to_repair w f s hF

/-! ## Sharp threshold -/

theorem seedMass_permute (w : Fin m → ℝ) (σ : Fin m ≃ Fin m)
    (hσ : ∀ i, w (σ i) = w i) (p : Fin m → Prop) :
    seedMass w (fun i => p (σ i)) = seedMass w p := by
  rw [seedMass_ite, seedMass_ite]
  exact Fintype.sum_equiv σ
    (fun i => if p (σ i) then w i else 0)
    (fun j => if p j then w j else 0)
    (fun i => by
      by_cases hp : p (σ i)
      · simp [hp, hσ]
      · simp [hp])

theorem repair_same_law {T : Tree} (w : Fin m → ℝ) (f : Decoder (m := m) T)
    (σ : Policy T → (Fin m ≃ Fin m)) (s : Fin m → Strategy T)
    (hw : ∀ π i, w (σ π i) = w i)
    (hr : ∀ π i, (f π (σ π i)).1 = run (s i) π)
    (π : Policy T) (S : Leaf T → Prop) :
    seedMass w (fun i => S (run (s i) π)) =
      seedMass w (fun i => S (f π i).1) := by
  have hfun : (fun i => S (run (s i) π)) = (fun i => S ((f π (σ π i)).1)) := by
    funext i
    rw [hr π i]
  rw [hfun]
  exact seedMass_permute w (σ π) (hw π) (fun j => S (f π j).1)

/-- Every `ε`-accurate family on every finite controlled tree admits a relabeling
repair if and only if `2ε < deltaRel w`. The witness that the bound is sharp is
the depth-at-most-two `pairTree`. `deltaRel` is the gap between subsets with
different weight-class count vectors; it is not `gamma`. -/
theorem sharp_relabel {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) (ε : ℝ)
    (hε : 0 ≤ ε) (hpos : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1) :
    (∀ (T : Tree) (f : Decoder (m := m) T), Accurate w ε f → RelabelRepair w f) ↔
      2 * ε < deltaRel hm w := by
  constructor
  · intro hall
    by_contra hge
    push Not at hge
    obtain ⟨A, B, hdiff, hgap⟩ := exists_delta_pair hm w
    have hne : A ≠ B := by
      intro hAB
      apply hdiff
      rw [hAB]
      intro _ _
      rfl
    have hq := half_bounds hpos hsum hne
    have hn : 0 < (1 : ℕ) := by decide
    let q : Fin 1 → ℝ := fun _ => (subsetSum w A + subsetSum w B) / 2
    have hq0 : ∀ j, 0 < q j := fun _ => hq.1
    have hq1 : ∀ j, q j < 1 := fun _ => hq.2
    let Af : Fin 1 → Finset (Fin m) := fun _ => A
    let Bf : Fin 1 → Finset (Fin m) := fun _ => B
    have hgap1 : ∀ j, |subsetSum w (Af j) - subsetSum w (Bf j)| ≤ 2 * ε := by
      intro _
      simpa [Af, Bf] using (hgap ▸ hge : |subsetSum w A - subsetSum w B| ≤ 2 * ε)
    let T := pairTree hn q hq0 hq1
    let f := attainDecoder hn q hq0 hq1 Af Bf
    have hf : Accurate w ε f :=
      attain_accurate w ε hε hsum hn Af Bf hgap1 q (fun _ => rfl) hq0 hq1
    have hrep := hall T f hf
    have hstable := relabel_implies_stable w f hrep
    let h : Hist T := Hist.under 0 0 (.here : Hist (pairChild 0))
    have hexLam : ∃ lam ∈ (Finset.univ : Finset (Fin m)).image w,
        (classSlice w A lam).card ≠ (classSlice w B lam).card := by
      by_contra hallEq
      push Not at hallEq
      exact hdiff hallEq
    obtain ⟨lam, _, hcne⟩ := hexLam
    have hfol : ∀ later : Fin 2, followsHist h (polAt hn q hq0 hq1 0 later) := by
      intro later
      unfold h
      exact ⟨rfl, trivial⟩
    have hext_yes : ∀ later : Fin 2,
        extendsHist h (yesLeaf hn q hq0 hq1 0 later) := by
      intro later
      let ℓyes : Leaf (Tree.node 1 hn (fun _ => 2) (fun _ => Nat.two_pos)
          (pairK q) (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y)) :=
        ⟨0, 0, goLeaf later⟩
      have hp : yesLeaf hn q hq0 hq1 0 later = ℓyes := by
        unfold yesLeaf pack ℓyes
        apply eq_of_heq
        apply cast_heq
      rw [hp]
      unfold h
      exact ⟨rfl, rfl, trivial⟩
    have hnot_no : ¬ extendsHist h (noLeaf hn q hq0 hq1 0) := by
      let ℓno : Leaf (Tree.node 1 hn (fun _ => 2) (fun _ => Nat.two_pos)
          (pairK q) (pairK_pos hq0 hq1) (pairK_sum q) (fun _ y => pairChild y)) :=
        ⟨0, 1, PUnit.unit⟩
      have hp : noLeaf hn q hq0 hq1 0 = ℓno := by
        unfold noLeaf pack ℓno
        apply eq_of_heq
        apply cast_heq
      intro hext
      rw [hp] at hext
      unfold h at hext
      rcases hext with ⟨_, hy, _⟩
      have hcontr : (1 : Fin 2) = 0 := by
        simpa [ℓno] using hy
      exact absurd hcontr (by decide)
    have hdec : ∀ later : Fin 2, ∀ i,
        (f (polAt hn q hq0 hq1 0 later) i).1 =
          if i ∈ (if later = 0 then A else B) then
            yesLeaf hn q hq0 hq1 0 later
          else noLeaf hn q hq0 hq1 0 := by
      intro later i
      simpa [f, sideSet, pol_root, pol_later, Af, Bf] using
        dec_eq_side hn q hq0 hq1 Af Bf (polAt hn q hq0 hq1 0 later) i
    have hcount : ∀ later : Fin 2,
        classCount Finset.univ w lam f (polAt hn q hq0 hq1 0 later) h =
          (classSlice w (if later = 0 then A else B) lam).card := by
      intro later
      have hext_iff : ∀ i,
          extendsHist h (f (polAt hn q hq0 hq1 0 later) i).1 ↔
            i ∈ (if later = 0 then A else B) := by
        intro i
        rw [hdec later i]
        by_cases hi : i ∈ if later = 0 then A else B
        · rw [if_pos hi]
          exact ⟨fun _ => hi, fun _ => hext_yes later⟩
        · rw [if_neg hi]
          exact ⟨fun h => (hnot_no h).elim, fun h => (hi h).elim⟩
      simp only [classCount]
      congr 1
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, classSlice]
      constructor
      · intro ⟨hw, he⟩
        exact ⟨(hext_iff i).1 he, hw⟩
      · intro ⟨hs, hw⟩
        exact ⟨hw, (hext_iff i).2 hs⟩
    have heq := hstable h lam (polAt hn q hq0 hq1 0 0) (polAt hn q hq0 hq1 0 1)
      (hfol 0) (hfol 1)
    have hA := hcount 0
    have hB := hcount 1
    simp only [ite_true, ite_false] at hA hB
    exact hcne (hA.symm.trans (heq.trans hB))
  · intro hlt T f hf
    exact (relabelRepair_iff_countStable w f).2
      (accurate_count_stable hm w ε hlt f hf)

#print axioms relabelRepair_iff_countStable
#print axioms sharp_relabel
#print axioms repair_same_law

end CausalSpectrum
end




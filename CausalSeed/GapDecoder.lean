/-
The interleaved decoder of block absorption.

Fix a kernel `κ` and an action `j₀`; the other actions form the kernel `subK κ j₀`. A
history splits into the outputs of `j₀` (the list `Z h`) and the history of the other
actions (the list `S h`, reindexed). A *plan* places the `j₀`-outputs into consecutive
blocks of a product sample and the other events into consecutive windows read by seeds for
`subK κ j₀`. The decoder reads each round from the block or window its counter falls in.
When every block and its paired window are never both touched (the anti-diagonal
condition), the decoder is exact and its entropy is the sum of the pair entropies.
-/
import CausalSeed.GapImage
import CausalSeed.GapProduct

noncomputable section
open Classical Finset
open scoped ENNReal

namespace CausalSpectrum.Kernel
open Completion
variable (κ : Kernel)

/-! ### Step-by-step agreement and path mass for stationary kernels -/

/-- One-round weight of an event. -/
def wt (e : ℕ × ℕ) : ℝ :=
  if ha : e.1 < κ.nA then if hy : e.2 < κ.nY ⟨e.1, ha⟩ then κ.K ⟨e.1, ha⟩ ⟨e.2, hy⟩ else 0
  else 0

theorem pathMass_eq_prod : ∀ L : List (ℕ × ℕ), pathMass κ.toITree L = (L.map κ.wt).prod
  | [] => by simp [pathMass_nil]
  | e :: t => by
    rw [List.map_cons, List.prod_cons, ← pathMass_eq_prod t]
    unfold pathMass
    by_cases ha : e.1 < κ.nA
    · by_cases hy : e.2 < κ.nY ⟨e.1, ha⟩
      · rw [pm_cons_ok (ι := κ.toITree) ha hy, κ.pm_stationary]
        simp [wt, ha, hy, toITree]
      · rw [pm_cons_out (ι := κ.toITree) ha hy]; simp [wt, ha, hy]
    · rw [pm_cons_act (ι := κ.toITree) ha]; simp [wt, ha]

theorem sval_congr (s : IStrategy κ.toITree) {h h' : List (ℕ × ℕ)} (e : h = h') (a : ℕ)
    (ha : a < κ.nA) (ha' : a < κ.nA) :
    (s ⟨h, ⟨a, ha⟩⟩).val = (s ⟨h', ⟨a, ha'⟩⟩).val := by subst e; rfl

theorem agreesFrom_iff (s : IStrategy κ.toITree) :
    ∀ (t pref : List (ℕ × ℕ)), agreesFrom κ.toITree s pref t ↔
      ∀ k (hk : k < t.length), ∃ ha : t[k].1 < κ.nA,
        (s ⟨pref ++ t.take k, ⟨t[k].1, ha⟩⟩).val = t[k].2
  | [], pref => by simp [agreesFrom]
  | (a1, z1) :: t, pref => by
    rw [agreesFrom_cons, agreesFrom_iff s t]
    constructor
    · rintro ⟨⟨⟨av, hav⟩, ha, hs⟩, h⟩ k hk
      simp only at ha; subst ha
      cases k with
      | zero => exact ⟨hav, (κ.sval_congr s (by simp) _ _ _).trans hs⟩
      | succ k =>
        obtain ⟨hk', hs'⟩ := h k (by simpa using hk)
        refine ⟨by simpa using hk', ?_⟩
        simp only [List.take_succ_cons, List.getElem_cons_succ]
        rw [List.append_cons]; exact hs'
    · intro h
      obtain ⟨ha0, hs0⟩ := h 0 (by simp)
      refine ⟨⟨⟨a1, (by simpa using ha0 : a1 < κ.nA)⟩, rfl,
        (κ.sval_congr s (by simp) _ _ _).trans hs0⟩, fun k hk => ?_⟩
      obtain ⟨hk', hs'⟩ := h (k + 1) (by simpa using hk)
      simp only [List.take_succ_cons, List.getElem_cons_succ] at hk' hs'
      rw [List.append_cons] at hs'
      exact ⟨hk', hs'⟩

theorem iAgree_iff_forall (s : IStrategy κ.toITree) (t : List (ℕ × ℕ)) :
    iAgree κ.toITree s t ↔ ∀ k (hk : k < t.length), ∃ ha : t[k].1 < κ.nA,
        (s ⟨t.take k, ⟨t[k].1, ha⟩⟩).val = t[k].2 := by
  rw [iAgree_iff, κ.agreesFrom_iff s t []]; simp

theorem iAgree_snoc (s : IStrategy κ.toITree) (h : List (ℕ × ℕ)) (a1 z1 : ℕ) :
    iAgree κ.toITree s (h ++ [(a1, z1)]) ↔ iAgree κ.toITree s h ∧
      ∃ ha : a1 < κ.nA, (s ⟨h, ⟨a1, ha⟩⟩).val = z1 := by
  rw [iAgree_concat, agreesFrom_cons]
  simp only [agreesFrom_nil, and_true]
  constructor
  · rintro ⟨h1, ⟨⟨av, hav⟩, rfl, hs⟩⟩; exact ⟨h1, hav, hs⟩
  · rintro ⟨h1, hav, hs⟩; exact ⟨h1, ⟨a1, hav⟩, rfl, hs⟩

/-! ### The subfamily kernel -/

variable {κ} (j₀ : Fin κ.nA)

def emb (b : Fin (κ.nA - 1)) : Fin κ.nA :=
  ⟨if b.val < j₀.val then b.val else b.val + 1, by split_ifs <;> omega⟩

theorem subK_hA (h2 : 2 ≤ κ.nA) : 0 < κ.nA - 1 := by omega

/-- The kernel of the actions other than `j₀`. -/
def subK (h2 : 2 ≤ κ.nA) : Kernel where
  nA := κ.nA - 1
  hA := subK_hA h2
  nY := fun b => κ.nY (emb j₀ b)
  hY := fun b => κ.hY _
  K := fun b => κ.K (emb j₀ b)
  Kpos := fun b => κ.Kpos _
  Ksum := fun b => κ.Ksum _

/-- Index of an action in the subfamily (as a natural number). -/
def subN (a : ℕ) : ℕ := if a < j₀.val then a else a - 1

theorem subN_lt {a : ℕ} (ha : a < κ.nA) (hne : a ≠ j₀.val) : subN j₀ a < κ.nA - 1 := by
  unfold subN; have := j₀.isLt; split_ifs <;> omega

theorem emb_subN {a : ℕ} (ha : a < κ.nA) (hne : a ≠ j₀.val) :
    emb j₀ ⟨subN j₀ a, subN_lt j₀ ha hne⟩ = ⟨a, ha⟩ := by
  ext; simp only [emb, subN]; split_ifs <;> omega

theorem subN_ge {a : ℕ} (ha : ¬ a < κ.nA) : ¬ subN j₀ a < κ.nA - 1 := by
  unfold subN; have := j₀.isLt; split_ifs <;> omega

/-- Outputs of `j₀`. -/
def Zl (h : List (ℕ × ℕ)) : List ℕ :=
  h.filterMap fun e => if e.1 = j₀.val then some e.2 else none

/-- The history of the other actions. -/
def Sl (h : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  h.filterMap fun e => if e.1 = j₀.val then none else some (subN j₀ e.1, e.2)

theorem Zl_snoc (h e) : Zl j₀ (h ++ [e]) = if e.1 = j₀.val then Zl j₀ h ++ [e.2] else Zl j₀ h := by
  unfold Zl; rw [List.filterMap_append]; split_ifs with he <;> simp [he]

theorem Sl_snoc (h e) : Sl j₀ (h ++ [e]) =
    if e.1 = j₀.val then Sl j₀ h else Sl j₀ h ++ [(subN j₀ e.1, e.2)] := by
  unfold Sl; rw [List.filterMap_append]; split_ifs with he <;> simp [he]

theorem length_Zl_Sl : ∀ h : List (ℕ × ℕ), (Zl j₀ h).length + (Sl j₀ h).length = h.length := by
  intro h
  induction h using List.reverseRecOn with
  | nil => simp [Zl, Sl]
  | append_singleton h e ih =>
    rw [Zl_snoc, Sl_snoc]; split_ifs <;> simp <;> omega

/-- Weight of an output of `j₀`. -/
def kz (z : ℕ) : ℝ := if hz : z < κ.nY j₀ then κ.K j₀ ⟨z, hz⟩ else 0

/-- Path mass splits into the `j₀` part and the subfamily part. -/
theorem pathMass_split (h2 : 2 ≤ κ.nA) (h : List (ℕ × ℕ)) :
    pathMass κ.toITree h = ((Zl j₀ h).map (kz j₀)).prod *
      pathMass (subK j₀ h2).toITree (Sl j₀ h) := by
  rw [κ.pathMass_eq_prod, (subK j₀ h2).pathMass_eq_prod]
  induction h using List.reverseRecOn with
  | nil => simp [Zl, Sl]
  | append_singleton h e ih =>
    rw [Zl_snoc, Sl_snoc, List.map_append, List.prod_append, ih]
    split_ifs with he
    · have hj : e.1 < κ.nA := he ▸ j₀.isLt
      simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      have : κ.wt e = kz j₀ e.2 := by
        simp only [wt, kz, dif_pos hj]
        have : (⟨e.1, hj⟩ : Fin κ.nA) = j₀ := Fin.ext he
        subst this; rfl
      rw [this]; ring
    · simp only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, mul_one]
      have : κ.wt e = (subK j₀ h2).wt (subN j₀ e.1, e.2) := by
        by_cases ha : e.1 < κ.nA
        · have hs := subN_lt j₀ ha he
          have hE := emb_subN j₀ ha he
          simp only [wt]
          rw [dif_pos ha, dif_pos (show subN j₀ e.1 < (subK j₀ h2).nA from hs)]
          show _ = (if hy : e.2 < κ.nY (emb j₀ ⟨subN j₀ e.1, hs⟩) then
            κ.K (emb j₀ ⟨subN j₀ e.1, hs⟩) ⟨e.2, hy⟩ else 0)
          rw [hE]
        · simp [wt, ha, subN_ge j₀ ha, subK]
      rw [this]; ring

end CausalSpectrum.Kernel

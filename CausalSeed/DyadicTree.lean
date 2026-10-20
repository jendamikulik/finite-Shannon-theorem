/-
Exact optimality for dyadic trees: if every kernel entry is a power of `1/2`, a finite
dyadic seed realizes the envelope exactly, `seedShannon = envelopeMean` (no rounding
overhead).  Construction node by node: the children's optimal dyadic seeds, shifted by
the branch levels, give one dyadic law per action; `Dyadic.couple` refines all of them
by a single dyadic law whose CDF dominates their minimum, which dominates `F*`.
-/
import CausalSeed.DyadicCouple
import CausalSeed.Gap
import CausalSeed.SqrtBridge

noncomputable section
open Classical MeasureTheory Set
namespace CausalSpectrum.Dyadic

/-- Every kernel entry is `2^{-c}` for some `c : ℕ`. -/
def DyadicTree : Tree → Prop
  | .leaf => True
  | .node _ _ _ _ K _ _ child =>
      (∀ a y, ∃ c : ℕ, K a y = wt c) ∧ ∀ a y, DyadicTree (child a y)

/-- A default strategy. -/
def dflt : (T : Tree) → Strategy T
  | .leaf => PUnit.unit
  | .node _ _ _ hY _ _ _ child => (fun a => ⟨0, hY a⟩, fun a y => dflt (child a y))

section maps
variable {β γ : Type}

theorem massL_map_snd (L : List (ℕ × β)) (f : β → γ) (g : γ → ℝ) :
    massL (L.map fun m => (m.1, f m.2)) g = massL L (fun x => g (f x)) := by
  simp [massL, Function.comp_def]

theorem cdfL_map_snd (L : List (ℕ × β)) (f : β → γ) (t : ℝ) :
    cdfL (L.map fun m => (m.1, f m.2)) t = cdfL L t := by
  simp [cdfL, Function.comp_def]

theorem massL_shift (L : List (ℕ × β)) (c : ℕ) (f : β → γ) (g : γ → ℝ) :
    massL (L.map fun m => (m.1 + c, f m.2)) g = wt c * massL L (fun x => g (f x)) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, massL_cons] at ih ⊢
    rw [ih, wt, pow_add]; ring

theorem cdfL_shift (L : List (ℕ × β)) (c : ℕ) (f : β → γ) (t : ℝ) :
    cdfL (L.map fun m => (m.1 + c, f m.2)) t = wt c * cdfL L (t - c) := by
  induction L with
  | nil => simp
  | cons m L ih =>
    simp only [List.map_cons, cdfL_cons] at ih ⊢
    rw [ih, wt, pow_add]
    push_cast
    by_cases h : (m.1 : ℝ) + c ≤ t
    · rw [if_pos h, if_pos (by linarith)]; ring
    · rw [if_neg h, if_neg (by intro h'; apply h; linarith)]; ring

theorem massL_flatMap {ι : Type} (l : List ι) (f : ι → List (ℕ × β)) (g : β → ℝ) :
    massL (l.flatMap f) g = (l.map fun i => massL (f i) g).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, massL_append, ih]

theorem cdfL_flatMap {ι : Type} (l : List ι) (f : ι → List (ℕ × β)) (t : ℝ) :
    cdfL (l.flatMap f) t = (l.map fun i => cdfL (f i) t).sum := by
  induction l with
  | nil => simp
  | cons i l ih => simp [List.flatMap_cons, cdfL_append, ih]

theorem exists_bound (L : List (ℕ × β)) : ∃ N, ∀ m ∈ L, m.1 ≤ N :=
  ⟨(L.map Prod.fst).sum, fun m hm =>
    List.le_sum_of_mem (List.mem_map_of_mem (f := Prod.fst) hm)⟩

end maps

theorem infoMass_wt (c : ℕ) : infoMass (wt c) = c := by
  simp [infoMass, wt, Real.logb_pow, Real.logb_inv]

/-- The invariant: an exact dyadic seed whose CDF dominates the envelope. -/
def DSeed (T : Tree) (D : List (ℕ × Strategy T)) : Prop :=
  (∀ ℓ : Leaf T, massL D (fun d => if CompatibleStrategy ℓ d then 1 else 0) = leafMass ℓ) ∧
    (∀ t, Fstar T t ≤ cdfL D t) ∧ massL D (fun _ => 1) = 1

theorem exists_dseed : ∀ T : Tree, DyadicTree T → ∃ D, DSeed T D := by
  intro T
  induction T with
  | leaf =>
    intro _
    refine ⟨[(0, PUnit.unit)], fun ℓ => ?_, fun t => ?_, ?_⟩
    · simp [CompatibleStrategy, leafMass]
    · refine (Fstar_le Tree.leaf t (PUnit.unit : Policy Tree.leaf)).trans (le_of_eq ?_)
      simp [policyCDF, policySum, leafMass, infoMass]
    · simp
  | node nA hA nY hY K Kpos Ksum child ih =>
    intro hT
    obtain ⟨hK, hch⟩ := hT
    choose c hc using hK
    choose D hD using fun a y => ih a y (hch a y)
    haveI : Nonempty (Fin nA) := ⟨⟨0, hA⟩⟩
    let β : Fin nA → Type := fun a => Σ y : Fin (nY a), Strategy (child a y)
    let M : ∀ a, List (ℕ × β a) := fun a => (List.finRange (nY a)).flatMap fun y =>
      (D a y).map fun m => (m.1 + c a y, (⟨y, m.2⟩ : β a))
    have hMm : ∀ a (g : β a → ℝ), massL (M a) g =
        ∑ y, wt (c a y) * massL (D a y) (fun d => g ⟨y, d⟩) := fun a g => by
      simp only [M, massL_flatMap, massL_shift]
      rw [Fin.sum_univ_def]
    have hMc : ∀ a t, cdfL (M a) t = ∑ y, wt (c a y) * cdfL (D a y) (t - c a y) := fun a t => by
      simp only [M, cdfL_flatMap, cdfL_shift]
      rw [Fin.sum_univ_def]
    have hM1 : ∀ a, massL (M a) (fun _ => 1) = 1 := fun a => by
      rw [hMm]
      simp_rw [(hD a _).2.2, mul_one, ← hc]
      exact Ksum a
    obtain ⟨N, hN⟩ : ∃ N, ∀ a, ∀ m ∈ M a, m.1 ≤ N := by
      choose N hN using fun a => exists_bound (M a)
      exact ⟨Finset.univ.sup N, fun a m hm =>
        (hN a m hm).trans (Finset.le_sup (f := N) (Finset.mem_univ a))⟩
    obtain ⟨R, hRm, hRc⟩ := couple N M hN hM1
    let strat : (∀ a, β a) → Strategy (.node nA hA nY hY K Kpos Ksum child) := fun p =>
      (fun a => (p a).1, fun a y => if h : (p a).1 = y then h ▸ (p a).2 else dflt _)
    refine ⟨R.map fun r => (r.1, strat r.2), fun ℓ => ?_, fun t => ?_, ?_⟩
    · obtain ⟨a, y, ℓ'⟩ := ℓ
      rw [massL_map_snd]
      let g : β a → ℝ := fun q =>
        if h : q.1 = y then (if CompatibleStrategy ℓ' (h ▸ q.2) then 1 else 0) else 0
      have hg : ∀ p : ∀ a, β a, (if CompatibleStrategy (T := Tree.node nA hA nY hY K Kpos Ksum child)
          (PSigma.mk a (PSigma.mk y ℓ')) (strat p) then (1:ℝ) else 0) =
          g (p a) := by
        intro p
        have hiff : CompatibleStrategy (T := Tree.node nA hA nY hY K Kpos Ksum child)
            (PSigma.mk a (PSigma.mk y ℓ')) (strat p) ↔
            y = (p a).1 ∧ CompatibleStrategy ℓ' ((strat p).2 a y) := Iff.rfl
        simp only [g]
        by_cases h : (p a).1 = y
        · rw [dif_pos h]
          have e : (strat p).2 a y = h ▸ (p a).2 := dif_pos h
          rw [e] at hiff
          by_cases hc : CompatibleStrategy ℓ' (h ▸ (p a).2)
          · rw [if_pos (hiff.mpr ⟨h.symm, hc⟩), if_pos hc]
          · rw [if_neg (fun hh => hc (hiff.mp hh).2), if_neg hc]
        · rw [dif_neg h, if_neg (fun hh => h (hiff.mp hh).1.symm)]
      simp_rw [hg]
      rw [hRm a g, hMm, Finset.sum_eq_single y]
      · have : (fun d => g ⟨y, d⟩) = fun d => if CompatibleStrategy ℓ' d then 1 else 0 := by
          funext d; simp [g]
        rw [this, (hD a y).1 ℓ', ← hc]
        rfl
      · intro y' _ hy'
        have : (fun d => g ⟨y', d⟩) = fun _ => 0 := by funext d; simp [g, hy']
        rw [this]; simp [massL]
      · simp
    · rw [cdfL_map_snd]
      obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf' univ_ne (fun a => cdfL (M a) t)
      refine le_trans ?_ ((hRc t).trans' (le_of_eq ha.symm))
      let π : Policy (.node nA hA nY hY K Kpos Ksum child) :=
        (a, fun a' y => envelopePolicy (child a' y) (t - c a' y))
      calc Fstar _ t ≤ policyCDF _ π t := Fstar_le _ t π
        _ = ∑ y, wt (c a y) * Fstar (child a y) (t - c a y) := by
          show ∑ y, policySum (fun ℓ : Leaf (child a y) => if infoMass (K a y * leafMass ℓ) ≤ t
            then K a y * leafMass ℓ else 0) (envelopePolicy (child a y) (t - c a y)) = _
          apply Finset.sum_congr rfl
          intro y _
          have hf : (fun ℓ : Leaf (child a y) => if infoMass (K a y * leafMass ℓ) ≤ t then
              K a y * leafMass ℓ else 0) = fun ℓ => wt (c a y) *
              (if infoMass (leafMass ℓ) ≤ t - c a y then leafMass ℓ else 0) := by
            funext ℓ
            rw [hc, Kernel.infoMass_mul (wt_pos _) (leafMass_pos ℓ), infoMass_wt]
            by_cases h : (c a y : ℝ) + infoMass (leafMass ℓ) ≤ t
            · rw [if_pos h, if_pos (by linarith)]
            · rw [if_neg h, if_neg (by intro h'; apply h; linarith), mul_zero]
          rw [hf, policySum_mul]
          rfl
        _ ≤ cdfL (M a) t := by
          rw [hMc]
          exact Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left ((hD a y).2.1 _) (wt_pos _).le
    · rw [massL_map_snd]
      obtain ⟨a⟩ := (inferInstance : Nonempty (Fin nA))
      rw [hRm a (fun _ => 1), hM1]

/-- **Exact optimality for dyadic trees.** If every kernel entry is a power of `1/2`,
there is an exact finite seed, with dyadic atoms, whose entropy equals the envelope mean:
no rounding overhead, `C = L`. -/
theorem dyadic_exact (T : Tree) (hT : DyadicTree T) :
    ∃ atoms : List (Atom T),
      (∀ a ∈ atoms, 0 < a.1) ∧ (∀ a ∈ atoms, a.1 ≤ 1) ∧ totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      (∀ t, seedCDF atoms t = Fstar T t) ∧
      seedShannon atoms = envelopeMean T := by
  obtain ⟨D, hE, hC, h1⟩ := exists_dseed T hT
  set atoms : List (Atom T) := D.map fun m => (wt m.1, m.2)
  have hpos : ∀ a ∈ atoms, 0 < a.1 := by
    intro a ha; simp only [atoms, List.mem_map] at ha
    obtain ⟨m, -, rfl⟩ := ha; exact wt_pos _
  have hle : ∀ a ∈ atoms, a.1 ≤ 1 := by
    intro a ha; simp only [atoms, List.mem_map] at ha
    obtain ⟨m, -, rfl⟩ := ha; exact pow_le_one₀ (by norm_num) (by norm_num)
  have htot : totalWeight atoms = 1 := by
    rw [← h1]; simp [totalWeight, atoms, massL, Function.comp_def]
  have hex : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0 := by
    intro π ℓ
    rw [transcriptWeight_eq]
    congr 1
    rw [← hE ℓ]
    simp only [representedLeaf, atoms, massL, List.map_map, Function.comp_def]
    congr 1; apply List.map_congr_left; intro m _
    split_ifs <;> simp
  have hcdf : ∀ t, seedCDF atoms t = cdfL D t := by
    intro t
    simp only [seedCDF, atoms, cdfL, List.map_map, Function.comp_def, infoMass_wt]
  have heq : ∀ t, seedCDF atoms t = Fstar T t := fun t =>
    le_antisymm (seedCDF_le_Fstar hex hpos t) (by rw [hcdf]; exact hC t)
  refine ⟨atoms, hpos, hle, htot, hex, heq, ?_⟩
  have hint := integral_cdfGap atoms hpos hle htot
  simp_rw [heq, sub_self, integral_zero] at hint
  linarith

end CausalSpectrum.Dyadic

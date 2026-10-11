/-
The bridge between the countable-seed entropy and the finite envelopes.
`envelopeMean` is measured in bits (`infoMass = -log₂`); seed entropies use
`Real.negMulLog`, hence nats. Every comparison below carries the factor
`Real.log 2` explicitly: nats = log 2 * bits.

`LInf ι = sup_n envelopeMean (trunc ι n [])` (bits, in [0,∞]).
Lower bound: every seed exact up to horizon n induces a coupling of the
finite joint transcripts of `trunc ι n []`; grouping atoms does not raise
entropy, and every coupling is above the envelope (`entropy_ge_envelope`).
Upper bound: the finite greedy seed of `trunc ι n []`, extended to the
infinite tree by `extend`, is exact up to horizon n and has entropy at most
`envelopeMean + shannonOverhead` bits (`seedShannon_le_envelope`).
-/
import CausalSeed.SeedRanking
import CausalSeed.Penalty

noncomputable section
open Classical Finset Filter MeasureTheory
open scoped Topology ENNReal
namespace CausalSpectrum.Completion

/-! ## Unit conversion and grouping -/

theorem log_two_mul_entTerm (x : ℝ) : Real.log 2 * entTerm x = Real.negMulLog x := by
  by_cases hx : x = 0
  · simp [entTerm, hx]
  · have hl : Real.log 2 ≠ 0 := by positivity
    simp only [entTerm, hx, if_false, infoMass, Real.logb, Real.negMulLog]
    field_simp

/-- Merging the atoms of a summable family into one atom does not increase
entropy, even for a countable family. -/
theorem negMulLog_hasSum_le {c : ℕ → ℝ} {m : ℝ} (hc : ∀ i, 0 ≤ c i)
    (hm : HasSum c m) (hm1 : m ≤ 1) :
    ENNReal.ofReal (Real.negMulLog m) ≤ ∑' i, ENNReal.ofReal (Real.negMulLog (c i)) := by
  have hm0 : 0 ≤ m := hm.nonneg hc
  have hlog : 0 ≤ -Real.log m := neg_nonneg.mpr (Real.log_nonpos hm0 hm1)
  have hci : ∀ i, c i ≤ m := fun i => le_hasSum hm i (fun j _ => hc j)
  have hterm : ∀ i, c i * -Real.log m ≤ Real.negMulLog (c i) := by
    intro i
    by_cases h0 : c i = 0
    · simp [h0]
    · have hp : 0 < c i := lt_of_le_of_ne (hc i) (Ne.symm h0)
      have hl := Real.log_le_log hp (hci i)
      simp only [Real.negMulLog]
      nlinarith
  have hs : HasSum (fun i => c i * -Real.log m) (m * -Real.log m) := hm.mul_right _
  have he : Real.negMulLog m = m * -Real.log m := by simp [Real.negMulLog]
  rw [he, ← hs.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hc i) hlog)
    hs.summable]
  exact ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal (hterm i)

/-! ## Lower bound: finite joint transcripts -/

namespace CountableSeed
variable {ι : ITree}

/-- The joint transcript of one infinite strategy under all horizon-`n` policies. -/
def assign (ι : ITree) (n : ℕ) (s : IStrategy ι) : CausalSpectrum.Assignment (trunc ι n []) :=
  fun π => policyRead ι n π s

/-- Mass of atom `i` placed on the joint transcript `α`. -/
def part (G : CountableSeed ι) (n : ℕ) (α : CausalSpectrum.Assignment (trunc ι n [])) (i : ℕ) :
    ℝ := if assign ι n (G.strategy i) = α then G.weight i else 0

theorem part_nonneg (G : CountableSeed ι) (n α i) : 0 ≤ G.part n α i := by
  unfold part; split_ifs
  · exact G.nonneg i
  · exact le_rfl

theorem part_le (G : CountableSeed ι) (n α i) : G.part n α i ≤ G.weight i := by
  unfold part; split_ifs
  · exact le_rfl
  · exact G.nonneg i

theorem part_summable (G : CountableSeed ι) (n α) : Summable (G.part n α) :=
  Summable.of_nonneg_of_le (G.part_nonneg n α) (G.part_le n α) G.mass.summable

theorem sum_part (G : CountableSeed ι) (n i) : ∑ α, G.part n α i = G.weight i := by
  simp [part]

theorem fiber_iff (n : ℕ) (π : Policy (trunc ι n [])) (ℓ : Leaf (trunc ι n []))
    (hc : CompatiblePolicy ℓ π) (s : IStrategy ι) :
    (policyRead ι n π s).1 = ℓ ↔ iAgree ι s (truncPath ι n [] ℓ) := by
  have h := Set.ext_iff.mp (policyRead_fiber ι n π ⟨ℓ, hc⟩) s
  simp only [Set.mem_preimage, Set.mem_singleton_iff, cylinder] at h
  rw [← Subtype.ext_iff (a1 := policyRead ι n π s) (a2 := ⟨ℓ, hc⟩)] at *
  exact h

/-- The coupling of the horizon-`n` transcripts induced by a seed exact to `n`. -/
def coupling (G : CountableSeed ι) (n : ℕ) (hG : G.ExactTo n) :
    CausalSpectrum.Coupling (trunc ι n []) where
  mass α := ∑' i, G.part n α i
  nonneg α := tsum_nonneg (G.part_nonneg n α)
  total := by
    rw [← Summable.tsum_finsetSum (fun α _ => G.part_summable n α)]
    simp_rw [sum_part]
    exact G.mass.tsum_eq
  marginal := by
    intro π ℓ hc
    have hswap : ∑ α, (if (α π).1 = ℓ then ∑' i, G.part n α i else 0) =
        ∑ α, ∑' i, (if (α π).1 = ℓ then G.part n α i else 0) := by
      apply Finset.sum_congr rfl
      intro α _
      split_ifs <;> simp
    rw [hswap, ← Summable.tsum_finsetSum]
    · have hterm : ∀ i, (∑ α, if (α π).1 = ℓ then G.part n α i else 0) =
          G.hit (truncPath ι n [] ℓ) i := by
        intro i
        have hs : (∑ α, if (α π).1 = ℓ then G.part n α i else 0) =
            if (assign ι n (G.strategy i) π).1 = ℓ then G.weight i else 0 := by
          simp only [part]
          rw [Finset.sum_eq_single (assign ι n (G.strategy i))]
          · simp
          · intro b _ hb
            simp [Ne.symm hb]
          · simp
        rw [hs, hit, indAgree]
        have hf := fiber_iff n π ℓ hc (G.strategy i)
        simp only [assign] at hf ⊢
        by_cases ha : iAgree ι (G.strategy i) (truncPath ι n [] ℓ)
        · simp [ha, hf.mpr ha]
        · simp [ha, mt hf.mp ha]
      simp_rw [hterm]
      rw [hG _ (by rw [truncPath_length]), pathMass_leaf]
    · intro α _
      apply Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [G.part_nonneg n α i, le_rfl])
        (fun i => by split_ifs; exacts [le_rfl, G.part_nonneg n α i]) (G.part_summable n α)

theorem coupling_entropy_le (G : CountableSeed ι) (n : ℕ) (hG : G.ExactTo n) :
    ENNReal.ofReal (Real.log 2 * (G.coupling n hG).entropy) ≤ G.entropy := by
  have hmass_le : ∀ α, ∑' i, G.part n α i ≤ 1 := by
    intro α
    rw [← G.mass.tsum_eq]
    exact Summable.tsum_le_tsum (G.part_le n α) (G.part_summable n α) G.mass.summable
  have h1 : Real.log 2 * (G.coupling n hG).entropy =
      ∑ α, Real.negMulLog (∑' i, G.part n α i) := by
    simp only [CausalSpectrum.Coupling.entropy, pmfEntropy, Finset.mul_sum,
      log_two_mul_entTerm]
    rfl
  rw [h1, ENNReal.ofReal_sum_of_nonneg (fun α _ =>
    Real.negMulLog_nonneg (tsum_nonneg (G.part_nonneg n α)) (hmass_le α))]
  calc
    (∑ α, ENNReal.ofReal (Real.negMulLog (∑' i, G.part n α i))) ≤
        ∑ α, ∑' i, ENNReal.ofReal (Real.negMulLog (G.part n α i)) :=
      Finset.sum_le_sum fun α _ => negMulLog_hasSum_le (G.part_nonneg n α)
        (G.part_summable n α).hasSum (hmass_le α)
    _ = ∑' i, ∑ α, ENNReal.ofReal (Real.negMulLog (G.part n α i)) :=
      (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
    _ = G.entropy := by
      unfold entropy
      apply tsum_congr
      intro i
      simp only [part]
      rw [Finset.sum_eq_single (assign ι n (G.strategy i))]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp

/-- Lower bound for one seed, in nats. -/
theorem envelope_le_entropy (G : CountableSeed ι) (n : ℕ) (hG : G.ExactTo n) :
    ENNReal.ofReal (Real.log 2 * envelopeMean (trunc ι n [])) ≤ G.entropy := by
  refine le_trans (ENNReal.ofReal_le_ofReal ?_) (G.coupling_entropy_le n hG)
  exact mul_le_mul_of_nonneg_left (entropy_ge_envelope _) (Real.log_nonneg (by norm_num))

end CountableSeed

theorem envelope_le_finiteCost (ι : ITree) (n : ℕ) :
    ENNReal.ofReal (Real.log 2 * envelopeMean (trunc ι n [])) ≤ finiteCost ι n := by
  refine le_iInf fun S => ?_
  rw [← S.1.toCountable_entropy]
  exact S.1.toCountable.envelope_le_entropy n S.2

/-! ## Upper bound: extending the finite greedy seed -/

theorem stratAgrees_of_prefix :
    ∀ {T : Tree} (s : Strategy T) (L todo : List (ℕ × ℕ)),
      stratAgrees s L → todo <+: L → stratAgrees s todo := by
  intro T
  induction T with
  | leaf =>
      intro s L todo hL hp
      have hL' : L = [] := by simpa [stratAgrees] using hL
      subst hL'
      have : todo = [] := List.prefix_nil.mp hp
      simp [stratAgrees, this]
  | node nA hA nY hY K Kpos Ksum child ih =>
      intro s L todo hL hp
      cases todo with
      | nil => simp [stratAgrees]
      | cons p t =>
          cases L with
          | nil => exact absurd hp (by simp)
          | cons q L' =>
              obtain ⟨rfl, ht⟩ := List.cons_prefix_cons.mp hp
              simp only [stratAgrees] at hL ⊢
              obtain ⟨a, ha, hy, hrest⟩ := hL
              exact ⟨a, ha, hy, ih _ _ _ _ _ hrest ht⟩

theorem agrees_of_run_mem {T : Tree} (s : Strategy T) (todo : List (ℕ × ℕ))
    (h : run s (followPol todo) ∈ prefixLeaves todo) : stratAgrees s todo := by
  simp only [prefixLeaves, Finset.mem_filter, Finset.mem_univ, true_and] at h
  have hs : stratAgrees s (leafPath (run s (followPol todo))) :=
    (stratAgrees_iff_compat s _).mpr (run_compatible_strategy s _)
  exact stratAgrees_of_prefix s _ _ hs h.1

theorem prefix_transcript_le_hitSum {T : Tree} (todo : List (ℕ × ℕ)) :
    ∀ (atoms : List (Atom T)), (∀ a ∈ atoms, 0 ≤ a.1) →
      ∑ ℓ ∈ prefixLeaves (T := T) todo, transcriptWeight atoms (followPol todo) ℓ ≤
        hitSum atoms todo := by
  intro atoms
  induction atoms with
  | nil => intro _; simp [transcriptWeight, hitSum]
  | cons a t ih =>
      intro hnn
      have hcons : ∀ ℓ, transcriptWeight (a :: t) (followPol todo) ℓ =
          (if run a.2 (followPol todo) = ℓ then a.1 else 0) +
            transcriptWeight t (followPol todo) ℓ := by
        intro ℓ; simp [transcriptWeight]
      simp_rw [hcons]
      rw [Finset.sum_add_distrib, hitSum_cons, Finset.sum_ite_eq]
      have ht := ih (fun b hb => hnn b (by simp [hb]))
      have ha : 0 ≤ a.1 := hnn a (by simp)
      have hhead : (if run a.2 (followPol todo) ∈ prefixLeaves todo then a.1 else 0) ≤
          (if stratAgrees a.2 todo then a.1 else 0) := by
        by_cases hm : run a.2 (followPol todo) ∈ prefixLeaves todo
        · simp [hm, agrees_of_run_mem a.2 todo hm]
        · rw [if_neg hm]; split_ifs <;> simp [ha]
      linarith

theorem greedy_hitSum_eq (ι : ITree) (n : ℕ) (todo : List (ℕ × ℕ)) (hn : todo.length ≤ n) :
    hitSum (greedyList (trunc ι n [])) todo = pathMass ι todo := by
  set T := trunc ι n []
  set atoms := greedyList T
  have hle : hitSum atoms todo ≤ pathMass ι todo := by
    have := greedy_cylinder ι n todo hn atoms.length
    rwa [List.take_length] at this
  apply le_antisymm hle
  have ht := greedyList_trace T
  have hbounds := greedy_atom_bounds ht
  obtain ⟨-, -, -, hrep⟩ := greedyTrace_properties ht (Field.p_isFlow T) (Field.p_nonneg T)
  have hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0 := by
    intro π ℓ
    rw [transcriptWeight_eq, hrep]
    have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
      simpa [Field.p] using leafValue_probability T 1 ℓ
    rw [hp]
  have hmass := prefix_mass ι n [] todo hn
  have hsum : ∑ ℓ ∈ prefixLeaves (T := T) todo, leafMass ℓ =
      ∑ ℓ ∈ prefixLeaves (T := T) todo, transcriptWeight atoms (followPol todo) ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hc : CompatiblePolicy ℓ (followPol todo) := by
      simp only [prefixLeaves, Finset.mem_filter] at hℓ
      exact hℓ.2.2
    rw [hexact, if_pos hc]
  calc
    pathMass ι todo = ∑ ℓ ∈ prefixLeaves (T := T) todo, leafMass ℓ := by
      simpa [pathMass] using hmass.symm
    _ = _ := hsum
    _ ≤ hitSum atoms todo :=
      prefix_transcript_le_hitSum todo atoms (fun a ha => (hbounds.1 a ha).le)

theorem gWeight_zero_of_ge (ι : ITree) (n i : ℕ)
    (hi : (greedyList (trunc ι n [])).length ≤ i) : gWeight ι n i = 0 := by
  rw [gWeight_eq, atomWeight_ge _ hi]

theorem greedy_tsum_hit (ι : ITree) (n : ℕ) (todo : List (ℕ × ℕ)) (hn : todo.length ≤ n) :
    ∑' i, gWeight ι n i * indAgree ι (greedyCode ι n i) todo = pathMass ι todo := by
  set L := (greedyList (trunc ι n [])).length
  rw [tsum_eq_sum (s := range L)]
  · rw [greedy_hit_eq ι n todo hn L, List.take_length, greedy_hitSum_eq ι n todo hn]
  · intro i hi
    rw [gWeight_zero_of_ge ι n i (by simpa [L] using hi), zero_mul]

theorem gWeight_nonneg (ι : ITree) (n i : ℕ) : 0 ≤ gWeight ι n i :=
  (gWeight_mem_Icc ι n i).1

theorem gWeight_hasSum (ι : ITree) (n : ℕ) : HasSum (gWeight ι n) 1 := by
  set L := (greedyList (trunc ι n [])).length
  have hz : ∀ i ∉ range L, gWeight ι n i = 0 := fun i hi =>
    gWeight_zero_of_ge ι n i (by simpa [L] using hi)
  have h : HasSum (gWeight ι n) (∑ i ∈ range L, gWeight ι n i) :=
    hasSum_sum_of_ne_finset_zero hz
  have he : ∑ i ∈ range L, gWeight ι n i = 1 := by
    have := greedy_tsum_hit ι n [] (Nat.zero_le _)
    rw [tsum_eq_sum (s := range L) (fun i hi => by rw [hz i hi, zero_mul])] at this
    simpa [indAgree_nil, pathMass_nil] using this
  rwa [he] at h

/-- The finite greedy seed of horizon `n`, extended to the infinite tree. -/
def greedySeed (ι : ITree) (n : ℕ) : CountableSeed ι :=
  ⟨gWeight ι n, gWeight_nonneg ι n, gWeight_hasSum ι n, greedyCode ι n⟩

theorem greedySeed_exactTo (ι : ITree) (n : ℕ) : (greedySeed ι n).ExactTo n :=
  fun h hn => greedy_tsum_hit ι n h hn

theorem sum_range_atomWeight {T : Tree} (g : ℝ → ℝ) :
    ∀ atoms : List (Atom T),
      ∑ i ∈ range atoms.length, g (atomWeight atoms i) = (atoms.map fun a => g a.1).sum := by
  intro atoms
  induction atoms with
  | nil => simp
  | cons a t ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
      have h0 : atomWeight (a :: t) 0 = a.1 := by simp [atomWeight]
      have hs : ∀ i, atomWeight (a :: t) (i + 1) = atomWeight t i := by
        intro i; simp [atomWeight]
      simp only [h0, hs]
      ring

theorem negMulLog_eq_bits (x : ℝ) : Real.negMulLog x = Real.log 2 * (x * infoMass x) := by
  rw [← log_two_mul_entTerm]
  by_cases h0 : x = 0
  · simp [entTerm, h0]
  · simp [entTerm, h0]

theorem list_negMulLog_eq {T : Tree} : ∀ atoms : List (Atom T),
    (atoms.map fun a => Real.negMulLog a.1).sum =
      Real.log 2 * (atoms.map fun a => a.1 * infoMass a.1).sum := by
  intro atoms
  induction atoms with
  | nil => simp
  | cons a t ih =>
      rw [List.map_cons, List.sum_cons, ih, negMulLog_eq_bits, List.map_cons, List.sum_cons]
      ring

theorem greedySeed_entropy (ι : ITree) (n : ℕ) :
    (greedySeed ι n).entropy =
      ENNReal.ofReal (Real.log 2 * seedShannon (greedyList (trunc ι n []))) := by
  set atoms := greedyList (trunc ι n [])
  set L := atoms.length
  have hz : ∀ i ∉ range L, ENNReal.ofReal (Real.negMulLog (gWeight ι n i)) = 0 := by
    intro i hi
    rw [gWeight_zero_of_ge ι n i (by simpa [L] using hi)]; simp
  unfold CountableSeed.entropy greedySeed
  simp only
  rw [tsum_eq_sum hz, ← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    Real.negMulLog_nonneg (gWeight_nonneg ι n i) (gWeight_mem_Icc ι n i).2)]
  congr 1
  simp_rw [gWeight_eq]
  rw [sum_range_atomWeight Real.negMulLog atoms, seedShannon]
  exact list_negMulLog_eq atoms

theorem finiteCost_le_envelope (ι : ITree) (n : ℕ) :
    finiteCost ι n ≤
      ENNReal.ofReal (Real.log 2 * (envelopeMean (trunc ι n []) + shannonOverhead)) := by
  set T := trunc ι n []
  have ht := greedyList_trace T
  have hb := greedy_atom_bounds ht
  have hsh := seedShannon_le_envelope ht hb.1 hb.2
  have hc : finiteCost ι n ≤ (greedySeed ι n).entropy := by
    rw [← (greedySeed ι n).ranked_entropy]
    exact finiteCost_le_seed ι n _ (((greedySeed ι n).ranked_exactTo_iff n).mpr
      (greedySeed_exactTo ι n))
  refine hc.trans ?_
  rw [greedySeed_entropy]
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_left hsh (Real.log_nonneg (by norm_num)))

/-! ## The bridge to `L_∞` -/

/-- `L_∞ = sup_n L_n`, in bits. -/
def LInf (ι : ITree) : ℝ≥0∞ := ⨆ n, ENNReal.ofReal (envelopeMean (trunc ι n []))

/-- Horizon-wise sandwich, in nats. -/
theorem finiteCost_sandwich (ι : ITree) (n : ℕ) :
    ENNReal.ofReal (Real.log 2 * envelopeMean (trunc ι n [])) ≤ finiteCost ι n ∧
      finiteCost ι n ≤
        ENNReal.ofReal (Real.log 2 * (envelopeMean (trunc ι n []) + shannonOverhead)) :=
  ⟨envelope_le_finiteCost ι n, finiteCost_le_envelope ι n⟩

/-- `log 2 · L_∞ ≤ C_∞ ≤ log 2 · (L_∞ + c_*)`, with `C_∞ = infiniteCost` in nats. -/
theorem infiniteCost_bridge (ι : ITree) :
    ENNReal.ofReal (Real.log 2) * LInf ι ≤ infiniteCost ι ∧
      infiniteCost ι ≤ ENNReal.ofReal (Real.log 2) * (LInf ι + ENNReal.ofReal shannonOverhead) := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [projective_entropy_identity]
  constructor
  · rw [LInf, ENNReal.mul_iSup]
    refine iSup_mono fun n => ?_
    rw [← ENNReal.ofReal_mul hl]
    exact envelope_le_finiteCost ι n
  · refine iSup_le fun n => (finiteCost_le_envelope ι n).trans ?_
    rw [ENNReal.ofReal_mul hl]
    gcongr
    refine ENNReal.ofReal_add_le.trans ?_
    gcongr
    exact le_iSup (fun n => ENNReal.ofReal (envelopeMean (trunc ι n []))) n

/-- In particular, a finite-entropy exact seed exists iff `L_∞ < ∞`. -/
theorem infiniteCost_lt_top_iff (ι : ITree) : infiniteCost ι < ∞ ↔ LInf ι < ∞ := by
  obtain ⟨hlo, hhi⟩ := infiniteCost_bridge ι
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl0 : ENNReal.ofReal (Real.log 2) ≠ 0 := by simpa using hl
  constructor
  · intro h
    by_contra hL
    rw [not_lt, top_le_iff] at hL
    rw [hL, ENNReal.mul_top hl0] at hlo
    exact absurd (lt_of_le_of_lt hlo h) (lt_irrefl _)
  · intro h
    refine lt_of_le_of_lt hhi (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
    exact ENNReal.add_lt_top.mpr ⟨h, ENNReal.ofReal_lt_top⟩

#print axioms CountableSeed.envelope_le_entropy
#print axioms finiteCost_sandwich
#print axioms infiniteCost_bridge
#print axioms infiniteCost_lt_top_iff

end CausalSpectrum.Completion
end

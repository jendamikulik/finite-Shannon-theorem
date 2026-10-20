/-
The interval coupling behind block absorption.

Two finite laws `a` (on `0, …, N-1`) and `b` (on `0, …, M-1`) are laid out as consecutive
intervals of `[0,1)`. The coupling `ρ i c = |I_i ∩ J_c|` has the two laws as marginals. An
atom `i` whose interval lies inside a single `J_c` contributes no conditional entropy; at
most `M - 1` atoms of positive mass are split by a boundary of the `J`-partition. Hence
`H(ρ) ≤ H(a) + log M · (a{a_i > θ} + (M - 1) θ)` for every `θ ≥ 0`.
-/
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

noncomputable section
open Classical Finset MeasureTheory
open scoped ENNReal

namespace CausalSpectrum.Gap

/-- `Σ nml(u_c) ≤ nml(Σ u) + (Σ u) log |s|`. -/
theorem sum_negMulLog_le (s : Finset ℕ) (u : ℕ → ℝ) (hu : ∀ c ∈ s, 0 ≤ u c) :
    ∑ c ∈ s, Real.negMulLog (u c) ≤
      Real.negMulLog (∑ c ∈ s, u c) + (∑ c ∈ s, u c) * Real.log s.card := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  have hk : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hJ := Real.concaveOn_negMulLog.le_map_sum (t := s) (w := fun _ => (s.card : ℝ)⁻¹)
    (p := u) (fun _ _ => by positivity) (by simp [hk.ne']) (fun c hc => hu c hc)
  simp only [smul_eq_mul, ← mul_sum] at hJ
  set U := ∑ c ∈ s, u c
  have hU : 0 ≤ U := sum_nonneg hu
  rcases hU.eq_or_lt with hU0 | hUp
  · rw [← hU0] at hJ ⊢
    simp only [mul_zero, Real.negMulLog_zero, zero_mul, add_zero] at hJ ⊢
    nlinarith [inv_pos.2 hk]
  have e : Real.negMulLog ((s.card : ℝ)⁻¹ * U) =
      (s.card : ℝ)⁻¹ * (Real.negMulLog U + U * Real.log s.card) := by
    simp only [Real.negMulLog, Real.log_mul (inv_pos.2 hk).ne' hUp.ne', Real.log_inv]
    ring
  rw [e] at hJ
  have := (mul_le_mul_iff_of_pos_left (inv_pos.2 hk)).1 hJ
  linarith

/-- Cumulative sums. -/
def cum (a : ℕ → ℝ) (k : ℕ) : ℝ := ∑ j ∈ range k, a j

/-- The interval of atom `k`. -/
def Iv (a : ℕ → ℝ) (k : ℕ) : Set ℝ := Set.Ico (cum a k) (cum a (k + 1))

theorem cum_succ (a : ℕ → ℝ) (k) : cum a (k + 1) = cum a k + a k := sum_range_succ _ _

theorem cum_mono {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) : Monotone (cum a) := fun i j hij =>
  sum_le_sum_of_subset_of_nonneg (range_mono hij) fun k _ _ => ha k

theorem Iv_disj {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Iv a i) (Iv a j) := by
  rcases lt_or_gt_of_ne hij with h | h
  · exact Set.disjoint_left.2 fun x hx hx' => by
        have := cum_mono ha (Nat.succ_le_of_lt h)
        exact absurd (lt_of_lt_of_le hx.2 this) (not_lt.2 hx'.1)
  · exact Set.disjoint_left.2 fun x hx hx' => by
        have := cum_mono ha (Nat.succ_le_of_lt h)
        exact absurd (lt_of_lt_of_le hx'.2 this) (not_lt.2 hx.1)

theorem iUnion_Iv {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) (K : ℕ) :
    (⋃ k ∈ range K, Iv a k) = Set.Ico 0 (cum a K) := by
  induction K with
  | zero => simp [cum]
  | succ K ih =>
    rw [range_add_one, Finset.set_biUnion_insert, ih, Set.union_comm]
    exact Set.Ico_union_Ico_eq_Ico (by simpa [cum] using cum_mono ha (Nat.zero_le K))
      (cum_mono ha (Nat.le_succ K))

theorem volume_Iv (a : ℕ → ℝ) (k) : volume (Iv a k) = ENNReal.ofReal (a k) := by
  simp [Iv, Real.volume_Ico, cum_succ]

/-- Any measurable subset of the covered range is split additively by the partition. -/
theorem sum_vol_inter {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k) (M : ℕ) {S : Set ℝ}
    (hS : MeasurableSet S) (hsub : S ⊆ Set.Ico 0 (cum b M)) :
    ∑ c ∈ range M, volume (S ∩ Iv b c) = volume S := by
  have h := measure_biUnion_finset (μ := volume) (s := range M) (f := fun c => S ∩ Iv b c)
    (fun i _ j _ hij => (Iv_disj hb hij).mono Set.inter_subset_right Set.inter_subset_right)
    (fun c _ => hS.inter measurableSet_Ico)
  rw [← h, ← Set.inter_iUnion₂, iUnion_Iv hb, Set.inter_eq_left.2 hsub]

theorem vol_ne_top (a b : ℕ → ℝ) (i c : ℕ) : volume (Iv a i ∩ Iv b c) ≠ ⊤ := by
  have : volume (Iv a i) < ⊤ := by rw [volume_Iv]; exact ENNReal.ofReal_lt_top
  exact ((measure_mono Set.inter_subset_left).trans_lt this).ne

variable {a b : ℕ → ℝ} {N M : ℕ}

/-- The interval coupling. -/
def rho (a b : ℕ → ℝ) (i c : ℕ) : ℝ := (volume (Iv a i ∩ Iv b c)).toReal

theorem rho_nonneg (i c) : 0 ≤ rho a b i c := ENNReal.toReal_nonneg

theorem Iv_sub {a : ℕ → ℝ} (ha : ∀ k, 0 ≤ a k) {N i} (hi : i < N) :
    Iv a i ⊆ Set.Ico 0 (cum a N) := fun x hx =>
  ⟨le_trans (show (0:ℝ) ≤ cum a i by simpa [cum] using cum_mono ha (Nat.zero_le i)) hx.1,
    lt_of_lt_of_le hx.2 (cum_mono ha hi)⟩

theorem rho_sum_right (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {i} (hi : i < N) : ∑ c ∈ range M, rho a b i c = a i := by
  unfold rho
  rw [← ENNReal.toReal_sum fun c _ => vol_ne_top a b i c,
    sum_vol_inter hb M (S := Iv a i) measurableSet_Ico (he ▸ Iv_sub ha hi), volume_Iv,
    ENNReal.toReal_ofReal (ha i)]

theorem rho_sum_left (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {c} (hc : c < M) : ∑ i ∈ range N, rho a b i c = b c := by
  unfold rho
  simp_rw [Set.inter_comm (Iv a _)]
  rw [← ENNReal.toReal_sum fun i _ => vol_ne_top b a c i,
    sum_vol_inter ha N (S := Iv b c) measurableSet_Ico (he.symm ▸ Iv_sub hb hc), volume_Iv,
    ENNReal.toReal_ofReal (hb c)]

/-- Atom `i` is split when its interval lies in no single `J_c`. -/
def Split (a b : ℕ → ℝ) (M i : ℕ) : Prop := ¬ ∃ c < M, Iv a i ⊆ Iv b c

theorem row_entropy_le (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {i} (hi : i < N) :
    ∑ c ∈ range M, Real.negMulLog (rho a b i c) ≤
      Real.negMulLog (a i) + (if Split a b M i then a i else 0) * Real.log M := by
  by_cases hs : Split a b M i
  · rw [if_pos hs]
    have := sum_negMulLog_le (range M) (rho a b i) fun c _ => rho_nonneg i c
    rwa [rho_sum_right ha hb he hi, card_range] at this
  · rw [if_neg hs, zero_mul, add_zero]
    obtain ⟨c, hc, hsub⟩ := not_not.1 hs
    rw [sum_eq_single_of_mem c (mem_range.2 hc)]
    · have : rho a b i c = a i := by
        rw [← rho_sum_right ha hb he hi, sum_eq_single_of_mem c (mem_range.2 hc)]
        intro c' _ hc'
        simp [rho, ((Iv_disj hb hc').mono_right hsub).symm.inter_eq]
      rw [this]
    · intro c' _ hc'
      simp [rho, ((Iv_disj hb hc').mono_right hsub).symm.inter_eq]

/-- Entropy of the interval coupling. -/
theorem rho_entropy_le (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M) :
    ∑ i ∈ range N, ∑ c ∈ range M, Real.negMulLog (rho a b i c) ≤
      ∑ i ∈ range N, Real.negMulLog (a i) +
        (∑ i ∈ range N, if Split a b M i then a i else 0) * Real.log M := by
  rw [sum_mul, ← sum_add_distrib]
  exact sum_le_sum fun i hi => row_entropy_le ha hb he (mem_range.1 hi)

/-- A split atom of positive mass contains a boundary point `cum b k`, `1 ≤ k < M`. -/
theorem split_boundary (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {i} (hi : i < N) (hpos : 0 < a i) (hs : Split a b M i) :
    ∃ k ∈ Finset.Icc 1 (M - 1), cum a i < cum b k ∧ cum b k < cum a (i + 1) := by
  have hst : cum a i ∈ Set.Ico 0 (cum b M) := by
    rw [← he]; exact Iv_sub ha hi ⟨le_rfl, by rw [cum_succ]; linarith⟩
  rw [← iUnion_Iv hb] at hst
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_range] at hst
  obtain ⟨c, hc, hmem⟩ := hst
  by_cases hle : cum a (i + 1) ≤ cum b (c + 1)
  · exact absurd ⟨c, hc, fun x hx => ⟨hmem.1.trans hx.1, lt_of_lt_of_le hx.2 hle⟩⟩ hs
  push_neg at hle
  have hc1 : c + 1 < M := by
    by_contra h
    have : c + 1 = M := by omega
    rw [this, ← he] at hle
    exact absurd (cum_mono ha hi) (not_le.2 hle)
  exact ⟨c + 1, mem_Icc.2 ⟨by omega, by omega⟩, hmem.2, hle⟩

/-- At most `M - 1` atoms of positive mass are split. -/
theorem card_split_le (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M) :
    ((range N).filter fun i => Split a b M i ∧ 0 < a i).card ≤ M - 1 := by
  have key : ∀ i ∈ (range N).filter (fun i => Split a b M i ∧ 0 < a i),
      ∃ k ∈ Finset.Icc 1 (M - 1), cum a i < cum b k ∧ cum b k < cum a (i + 1) := fun i hi => by
    simp only [mem_filter, Finset.mem_range] at hi
    exact split_boundary ha hb he hi.1 hi.2.2 hi.2.1
  choose! g hg hlt using key
  calc _ ≤ (Finset.Icc 1 (M - 1)).card := card_le_card_of_injOn g (fun i hi => hg i hi) ?_
    _ = M - 1 := by simp
  intro i hi j hj hij
  by_contra hne
  have hd := Iv_disj ha hne
  have h1 := hlt i hi
  have h2 := hlt j hj
  rw [hij] at h1
  exact Set.disjoint_left.1 hd (show cum b (g j) ∈ Iv a i from ⟨h1.1.le, h1.2⟩)
    (show cum b (g j) ∈ Iv a j from ⟨h2.1.le, h2.2⟩)

/-- Split mass: heavy atoms plus at most `M - 1` light ones. -/
theorem split_mass_le (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    (∑ i ∈ range N, if Split a b M i then a i else 0) ≤
      (∑ i ∈ range N, if θ < a i then a i else 0) + (M - 1 : ℕ) * θ := by
  set T := (range N).filter fun i => Split a b M i ∧ 0 < a i
  have hT := card_split_le ha hb he
  calc (∑ i ∈ range N, if Split a b M i then a i else 0)
      ≤ ∑ i ∈ range N, ((if θ < a i then a i else 0) + if i ∈ T then θ else 0) := by
        refine sum_le_sum fun i hi => ?_
        by_cases hs : Split a b M i
        · rw [if_pos hs]
          by_cases h1 : θ < a i
          · rw [if_pos h1]; split_ifs <;> linarith
          · rw [if_neg h1, zero_add]
            rcases (ha i).eq_or_lt with h0 | h0
            · rw [← h0]; split_ifs <;> linarith
            · rw [if_pos (mem_filter.2 ⟨hi, hs, h0⟩)]; linarith
        · rw [if_neg hs]; split_ifs <;> linarith [ha i]
    _ = (∑ i ∈ range N, if θ < a i then a i else 0) + T.card * θ := by
        rw [sum_add_distrib]
        congr 1
        rw [sum_ite_mem, inter_eq_right.2 (filter_subset _ _), sum_const, nsmul_eq_mul]
    _ ≤ _ := by gcongr

/-- **Interval coupling bound.** For laws `a` on `range N` and `b` on `range M` with equal
total mass, the interval coupling has entropy at most
`H(a) + log M · (a{a_i > θ} + (M - 1) θ)`. -/
theorem rho_entropy_bound (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ i ∈ range N, ∑ c ∈ range M, Real.negMulLog (rho a b i c) ≤
      ∑ i ∈ range N, Real.negMulLog (a i) +
        ((∑ i ∈ range N, if θ < a i then a i else 0) + (M - 1 : ℕ) * θ) * Real.log M := by
  refine (rho_entropy_le ha hb he).trans ?_
  have hl : 0 ≤ Real.log M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  gcongr
  exact split_mass_le ha hb he hθ

/-- Support of `b` on `range M`. -/
def supp (b : ℕ → ℝ) (M : ℕ) : Finset ℕ := (range M).filter fun c => 0 < b c

theorem rho_eq_zero_of_not_supp (hb : ∀ k, 0 ≤ b k) {c} (hc : ¬ 0 < b c) (i) :
    rho a b i c = 0 := by
  have : b c = 0 := le_antisymm (not_lt.1 hc) (hb c)
  have hE : Iv b c = ∅ := by
    simp [Iv, cum_succ, this]
  simp [rho, hE]

theorem row_entropy_le' (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {i} (hi : i < N) :
    ∑ c ∈ range M, Real.negMulLog (rho a b i c) ≤
      Real.negMulLog (a i) + (if Split a b M i then a i else 0) * Real.log (supp b M).card := by
  have hS : ∀ f : ℕ → ℝ, (∀ c, ¬ 0 < b c → f c = 0) →
      ∑ c ∈ range M, f c = ∑ c ∈ supp b M, f c := fun f hf => by
    rw [supp, sum_filter]; exact sum_congr rfl fun c _ => by split_ifs with h <;> simp [hf c, h]
  by_cases hs : Split a b M i
  · rw [if_pos hs]
    have := sum_negMulLog_le (supp b M) (rho a b i) fun c _ => rho_nonneg i c
    rw [hS _ fun c hc => by rw [rho_eq_zero_of_not_supp hb hc]; simp]
    rwa [← hS _ fun c hc => rho_eq_zero_of_not_supp hb hc i, rho_sum_right ha hb he hi] at this
  · rw [if_neg hs, zero_mul, add_zero]
    exact (row_entropy_le ha hb he hi).trans (by rw [if_neg hs]; simp)

theorem split_boundary' (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {i} (hi : i < N) (hpos : 0 < a i) (hs : Split a b M i) :
    ∃ c ∈ supp b M, cum a i < cum b (c + 1) ∧ cum b (c + 1) < cum a (i + 1) := by
  have hst : cum a i ∈ Set.Ico 0 (cum b M) := by
    rw [← he]; exact Iv_sub ha hi ⟨le_rfl, by rw [cum_succ]; linarith⟩
  rw [← iUnion_Iv hb] at hst
  simp only [Set.mem_iUnion, exists_prop, Finset.mem_range] at hst
  obtain ⟨c, hc, hmem⟩ := hst
  have hbc : 0 < b c := by
    have := lt_of_le_of_lt hmem.1 hmem.2; rw [cum_succ] at this; linarith
  by_cases hle : cum a (i + 1) ≤ cum b (c + 1)
  · exact absurd ⟨c, hc, fun x hx => ⟨hmem.1.trans hx.1, lt_of_lt_of_le hx.2 hle⟩⟩ hs
  push_neg at hle
  exact ⟨c, mem_filter.2 ⟨mem_range.2 hc, hbc⟩, hmem.2, hle⟩

theorem card_split_le' (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M) :
    ((range N).filter fun i => Split a b M i ∧ 0 < a i).card ≤ (supp b M).card := by
  have key : ∀ i ∈ (range N).filter (fun i => Split a b M i ∧ 0 < a i),
      ∃ c ∈ supp b M, cum a i < cum b (c + 1) ∧ cum b (c + 1) < cum a (i + 1) := fun i hi => by
    simp only [mem_filter, Finset.mem_range] at hi
    exact split_boundary' ha hb he hi.1 hi.2.2 hi.2.1
  choose! g hg hlt using key
  refine card_le_card_of_injOn g (fun i hi => hg i hi) ?_
  intro i hi j hj hij
  by_contra hne
  have hd := Iv_disj ha hne
  have h1 := hlt i hi
  have h2 := hlt j hj
  rw [hij] at h1
  exact Set.disjoint_left.1 hd (show cum b (g j + 1) ∈ Iv a i from ⟨h1.1.le, h1.2⟩)
    (show cum b (g j + 1) ∈ Iv a j from ⟨h2.1.le, h2.2⟩)

/-- Support form of the interval coupling bound. -/
theorem rho_entropy_bound' (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ i ∈ range N, ∑ c ∈ range M, Real.negMulLog (rho a b i c) ≤
      ∑ i ∈ range N, Real.negMulLog (a i) +
        ((∑ i ∈ range N, if θ < a i then a i else 0) + (supp b M).card * θ) *
          Real.log (supp b M).card := by
  have hl : 0 ≤ Real.log (supp b M).card := by
    rcases Nat.eq_zero_or_pos (supp b M).card with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  calc _ ≤ ∑ i ∈ range N, (Real.negMulLog (a i) +
          (if Split a b M i then a i else 0) * Real.log (supp b M).card) :=
        sum_le_sum fun i hi => row_entropy_le' ha hb he (mem_range.1 hi)
    _ = ∑ i ∈ range N, Real.negMulLog (a i) +
          (∑ i ∈ range N, if Split a b M i then a i else 0) * Real.log (supp b M).card := by
        rw [sum_add_distrib, sum_mul]
    _ ≤ _ := by
      gcongr
      set T := (range N).filter fun i => Split a b M i ∧ 0 < a i
      calc (∑ i ∈ range N, if Split a b M i then a i else 0)
          ≤ ∑ i ∈ range N, ((if θ < a i then a i else 0) + if i ∈ T then θ else 0) := by
            refine sum_le_sum fun i hi => ?_
            by_cases hs : Split a b M i
            · rw [if_pos hs]
              by_cases h1 : θ < a i
              · rw [if_pos h1]; split_ifs <;> linarith
              · rw [if_neg h1, zero_add]
                rcases (ha i).eq_or_lt with h0 | h0
                · rw [← h0]; split_ifs <;> linarith
                · rw [if_pos (mem_filter.2 ⟨hi, hs, h0⟩)]; linarith
            · rw [if_neg hs]; split_ifs <;> linarith [ha i]
        _ = (∑ i ∈ range N, if θ < a i then a i else 0) + T.card * θ := by
            rw [sum_add_distrib]
            congr 1
            rw [sum_ite_mem, inter_eq_right.2 (filter_subset _ _), sum_const, nsmul_eq_mul]
        _ ≤ _ := by
            have : (T.card : ℝ) ≤ (supp b M).card := by exact_mod_cast card_split_le' ha hb he
            nlinarith

end CausalSpectrum.Gap

/-
The pair coupling of block absorption.

A finite law `a` (the product sample) is coupled with a finite law `b` (the atoms of a seed
for the other actions). Atoms of `b` of weight at least `θ_B` are retained; the others are
merged into one tail atom of mass `v`. The interval coupling of `a` with the merged law is
then refined proportionally inside the tail atom. The entropy exceeds `H(a)` by at most
`(a{a > θ} + (k+1) θ) log (k+1)` plus the tail entropy `Σ_{b_i < θ_B} -b_i log b_i`,
where `k` is the number of retained atoms.
-/
import CausalSeed.GapCoupling

noncomputable section
open Classical Finset

namespace CausalSpectrum.Gap

variable (a b : ℕ → ℝ) (M : ℕ) (θB : ℝ)

/-- Mass of the tail atoms. -/
def tmass : ℝ := ∑ i ∈ range M, if b i < θB then b i else 0

/-- The merged law on `range (M + 1)`: retained atoms, then the tail atom at index `M`. -/
def bR (i : ℕ) : ℝ :=
  if i < M then (if θB ≤ b i then b i else 0) else if i = M then tmass b M θB else 0

/-- The refined coupling on `range N × range M`. -/
def piC (x i : ℕ) : ℝ :=
  if θB ≤ b i then rho a (bR b M θB) x i
  else rho a (bR b M θB) x M * (b i / tmass b M θB)

variable {a b M θB}

theorem tmass_nonneg (hb : ∀ k, 0 ≤ b k) : 0 ≤ tmass b M θB :=
  sum_nonneg fun i _ => by split_ifs <;> simp [hb i]

theorem bR_nonneg (hb : ∀ k, 0 ≤ b k) (i) : 0 ≤ bR b M θB i := by
  unfold bR; split_ifs <;> simp [hb i, tmass_nonneg hb]

theorem cum_bR (b : ℕ → ℝ) (M θB) : cum (bR b M θB) (M + 1) = cum b M := by
  unfold cum
  rw [sum_range_succ, bR, if_neg (lt_irrefl M), if_pos rfl, tmass, ← sum_add_distrib]
  refine sum_congr rfl fun i hi => ?_
  rw [bR, if_pos (mem_range.1 hi)]
  split_ifs <;> first | linarith | simp

theorem rho_tail_zero (hb : ∀ k, 0 ≤ b k) {i} (hi : i < M) (ht : ¬ θB ≤ b i) (x) :
    rho a (bR b M θB) x i = 0 :=
  rho_eq_zero_of_not_supp (bR_nonneg hb) (by simp [bR, hi, ht]) x

theorem rho_M_zero_of (hb : ∀ k, 0 ≤ b k) (hv : tmass b M θB = 0) (x) :
    rho a (bR b M θB) x M = 0 :=
  rho_eq_zero_of_not_supp (bR_nonneg hb) (by simp [bR, hv]) x

theorem piC_nonneg (hb : ∀ k, 0 ≤ b k) (x i) : 0 ≤ piC a b M θB x i := by
  unfold piC; split_ifs
  · exact rho_nonneg _ _
  · exact mul_nonneg (rho_nonneg _ _) (div_nonneg (hb i) (tmass_nonneg hb))

variable {N : ℕ}

theorem piC_sum_right (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {x} (hx : x < N) : ∑ i ∈ range M, piC a b M θB x i = a x := by
  have hm := rho_sum_right ha (bR_nonneg hb) (he.trans (cum_bR b M θB).symm) hx
  rw [sum_range_succ] at hm
  rw [← hm]
  unfold piC
  rw [sum_ite, ← sum_filter_add_sum_filter_not (range M) (fun i => θB ≤ b i)
    (rho a (bR b M θB) x)]
  have h0 : ∑ i ∈ (range M).filter (fun i => ¬ θB ≤ b i), rho a (bR b M θB) x i = 0 :=
    sum_eq_zero fun i hi => by
      simp only [mem_filter, mem_range] at hi; exact rho_tail_zero hb hi.1 hi.2 x
  rw [h0, add_zero]
  congr 1
  rw [← mul_sum, ← sum_div]
  by_cases hv : tmass b M θB = 0
  · rw [rho_M_zero_of hb hv]; simp
  · have : ∑ i ∈ (range M).filter (fun i => ¬ θB ≤ b i), b i = tmass b M θB := by
      rw [tmass, sum_filter]; refine sum_congr rfl fun i _ => ?_
      split_ifs <;> first | rfl | (exfalso; linarith) | (exfalso; tauto)
    rw [this, div_self hv, mul_one]

theorem piC_sum_left (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    {i} (hi : i < M) : ∑ x ∈ range N, piC a b M θB x i = b i := by
  have he' := he.trans (cum_bR b M θB).symm
  unfold piC
  by_cases h : θB ≤ b i
  · simp only [if_pos h]
    rw [rho_sum_left ha (bR_nonneg hb) he' (Nat.lt_succ_of_lt hi)]
    simp [bR, hi, h]
  · simp only [if_neg h]
    rw [← sum_mul, rho_sum_left ha (bR_nonneg hb) he' (Nat.lt_succ_self M)]
    simp only [bR, lt_irrefl, if_false, if_true]
    by_cases hv : tmass b M θB = 0
    · have : b i = 0 := by
        have hle : b i ≤ tmass b M θB := by
          rw [tmass]
          have := single_le_sum (f := fun j => if b j < θB then b j else 0)
            (fun j _ => by split_ifs <;> simp [hb j]) (mem_range.2 hi)
          simpa [not_le.1 h] using this
        linarith [hb i]
      simp [this]
    · field_simp

/-- Entropy of the refined coupling. -/
theorem piC_entropy_le (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    (h1 : cum b M = 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ x ∈ range N, ∑ i ∈ range M, Real.negMulLog (piC a b M θB x i) ≤
      ∑ x ∈ range N, Real.negMulLog (a x) +
        ((∑ x ∈ range N, if θ < a x then a x else 0) + (supp (bR b M θB) (M + 1)).card * θ) *
          Real.log (supp (bR b M θB) (M + 1)).card +
        ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i) else 0) := by
  have he' := he.trans (cum_bR b M θB).symm
  set ρ := rho a (bR b M θB)
  set v := tmass b M θB
  have hv0 : 0 ≤ v := tmass_nonneg hb
  have hv1 : v ≤ 1 := by
    rw [← h1]; unfold v tmass cum
    exact sum_le_sum fun i _ => by split_ifs <;> simp [hb i]
  have hρ1 : ∀ x ∈ range N, ρ x M ≤ 1 := by
    intro x hx
    have := rho_sum_right ha (bR_nonneg hb) he' (mem_range.1 hx)
    have hax : a x ≤ 1 := by
      rw [← h1, ← he]; unfold cum
      exact single_le_sum (fun k _ => ha k) hx
    have h' := rho_sum_right ha (bR_nonneg hb) he' (mem_range.1 hx)
    rw [sum_range_succ] at h'
    have : 0 ≤ ∑ c ∈ range M, rho a (bR b M θB) x c := sum_nonneg fun c _ => rho_nonneg _ _
    linarith
  -- each row
  have hrow : ∀ x ∈ range N, ∑ i ∈ range M, Real.negMulLog (piC a b M θB x i) ≤
      ∑ c ∈ range (M + 1), Real.negMulLog (ρ x c) +
        ρ x M * ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i / v) else 0) := by
    intro x hx
    rw [sum_range_succ]
    unfold piC
    have hsplit : ∀ i ∈ range M, Real.negMulLog (if θB ≤ b i then ρ x i else ρ x M * (b i / v)) =
        Real.negMulLog (ρ x i) + (if b i < θB then
          (b i / v) * Real.negMulLog (ρ x M) + ρ x M * Real.negMulLog (b i / v) else 0) := by
      intro i hi
      by_cases h : θB ≤ b i
      · simp [h, not_lt.2 h]
      · rw [if_neg h, if_pos (not_le.1 h), show ρ x i = 0 from rho_tail_zero hb (mem_range.1 hi) h x,
          Real.negMulLog_mul]; simp
    rw [sum_congr rfl hsplit, sum_add_distrib, mul_sum]
    have ht : ∑ i ∈ range M, (if b i < θB then
          (b i / v) * Real.negMulLog (ρ x M) + ρ x M * Real.negMulLog (b i / v) else 0) ≤
        Real.negMulLog (ρ x M) +
          ∑ i ∈ range M, ρ x M * (if b i < θB then Real.negMulLog (b i / v) else 0) := by
      have e : ∀ i ∈ range M, (if b i < θB then
          (b i / v) * Real.negMulLog (ρ x M) + ρ x M * Real.negMulLog (b i / v) else 0) =
          (if b i < θB then b i / v else 0) * Real.negMulLog (ρ x M) +
            ρ x M * (if b i < θB then Real.negMulLog (b i / v) else 0) := fun i _ => by
        split_ifs <;> simp
      rw [sum_congr rfl e, sum_add_distrib, ← sum_mul]
      gcongr
      have hn : 0 ≤ Real.negMulLog (ρ x M) := Real.negMulLog_nonneg (rho_nonneg _ _) (hρ1 x hx)
      have hs : ∑ i ∈ range M, (if b i < θB then b i / v else 0) ≤ 1 := by
        have : ∑ i ∈ range M, (if b i < θB then b i / v else 0) = v / v := by
          rw [show v = tmass b M θB from rfl, tmass, sum_div]
          exact sum_congr rfl fun i _ => by split_ifs <;> simp
        rw [this]; exact div_self_le_one v
      nlinarith
    linarith
  have hvb : ∀ i ∈ range M, b i < θB → b i ≤ v := fun i hi hlt => by
    have := single_le_sum (f := fun j => if b j < θB then b j else 0)
      (fun j _ => by split_ifs <;> simp [hb j]) hi
    simp only [hlt, if_true] at this
    exact this.trans_eq rfl
  have hsc : ∀ i ∈ range M, v * (if b i < θB then Real.negMulLog (b i / v) else 0) ≤
      (if b i < θB then Real.negMulLog (b i) else 0) := by
    intro i hi
    split_ifs with hlt
    · have hbv := hvb i hi hlt
      rcases (hb i).eq_or_lt with h0 | h0
      · rw [← h0]; simp
      have hvp : 0 < v := lt_of_lt_of_le h0 hbv
      rw [Real.negMulLog, Real.negMulLog, Real.log_div h0.ne' hvp.ne']
      have : Real.log v ≤ 0 := Real.log_nonpos hv0 hv1
      have : v * (-(b i / v) * (Real.log (b i) - Real.log v)) = -b i * Real.log (b i) +
          b i * Real.log v := by field_simp; ring
      rw [this]; nlinarith [hb i]
    · simp
  have hRb := rho_entropy_bound' (a := a) (b := bR b M θB) (N := N) (M := M + 1) ha
    (bR_nonneg hb) he' hθ
  have hcol : ∑ x ∈ range N, ρ x M = v := by
    rw [rho_sum_left ha (bR_nonneg hb) he' (Nat.lt_succ_self M)]; simp [bR, v]
  calc _ ≤ ∑ x ∈ range N, (∑ c ∈ range (M + 1), Real.negMulLog (ρ x c) +
          ρ x M * ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i / v) else 0)) :=
        sum_le_sum hrow
    _ = ∑ x ∈ range N, ∑ c ∈ range (M + 1), Real.negMulLog (ρ x c) +
          v * ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i / v) else 0) := by
        rw [sum_add_distrib, ← sum_mul, hcol]
    _ ≤ _ := by
        have : v * ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i / v) else 0) ≤
            ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i) else 0) := by
          rw [mul_sum]; exact sum_le_sum hsc
        linarith

theorem card_supp_bR_le :
    (supp (bR b M θB) (M + 1)).card ≤ ((range M).filter fun i => θB ≤ b i).card + 1 := by
  have : supp (bR b M θB) (M + 1) ⊆ insert M ((range M).filter fun i => θB ≤ b i) := by
    intro i hi
    simp only [supp, mem_filter, mem_range] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi.1 with h | h
    · refine mem_insert_of_mem (mem_filter.2 ⟨mem_range.2 h, ?_⟩)
      by_contra hn; have := hi.2; simp [bR, h, hn] at this
    · exact h ▸ mem_insert_self _ _
  exact (card_le_card this).trans (card_insert_le _ _)

/-- Pair-coupling bound with `k` retained atoms. -/
theorem piC_entropy_le' (ha : ∀ k, 0 ≤ a k) (hb : ∀ k, 0 ≤ b k) (he : cum a N = cum b M)
    (h1 : cum b M = 1) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ x ∈ range N, ∑ i ∈ range M, Real.negMulLog (piC a b M θB x i) ≤
      ∑ x ∈ range N, Real.negMulLog (a x) +
        ((∑ x ∈ range N, if θ < a x then a x else 0) +
          (((range M).filter fun i => θB ≤ b i).card + 1) * θ) *
          Real.log (((range M).filter fun i => θB ≤ b i).card + 1) +
        ∑ i ∈ range M, (if b i < θB then Real.negMulLog (b i) else 0) := by
  refine (piC_entropy_le ha hb he h1 hθ).trans ?_
  have hc : ((supp (bR b M θB) (M + 1)).card : ℝ) ≤
      ((range M).filter fun i => θB ≤ b i).card + 1 := by exact_mod_cast card_supp_bR_le
  have hH : 0 ≤ ∑ x ∈ range N, if θ < a x then a x else 0 :=
    sum_nonneg fun x _ => by split_ifs <;> simp [ha x]
  have hl : Real.log (supp (bR b M θB) (M + 1)).card ≤
      Real.log (((range M).filter fun i => θB ≤ b i).card + 1) := by
    rcases Nat.eq_zero_or_pos (supp (bR b M θB) (M + 1)).card with h | h
    · rw [h]; simp; exact Real.log_nonneg (by linarith [(Nat.cast_nonneg _ : (0:ℝ) ≤
        ((range M).filter fun i => θB ≤ b i).card)])
    · exact Real.log_le_log (by exact_mod_cast h) hc
  have hl0 : 0 ≤ Real.log (supp (bR b M θB) (M + 1)).card := by
    rcases Nat.eq_zero_or_pos (supp (bR b M θB) (M + 1)).card with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  gcongr

end CausalSpectrum.Gap

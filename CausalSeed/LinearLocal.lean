/-
Exact local cost for `m = 2^k - 1` pairwise independent fair bits.

The seed is uniform on `𝔽₂^k`. The `2^k - 1` nonzero linear forms of that vector
are pairwise independent and fair, and the evaluation map is injective, so the
response law has Shannon entropy exactly `k = log₂(m+1)`.

Combined with `LocalSeparation.pairwise_entropy_ge`, this is the matching upper
bound from linear forms. It is not a Hadamard matrix, and it is not the sharp
approximate coefficient `(1-4ε) log₂ log₂ m`.
-/
import CausalSeed.LocalSeparation
import CausalSeed.CapacityScale
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Fintype.Card

noncomputable section

open Real Finset

namespace LinearLocal

def flipAt {k : ℕ} (i : Fin k) (s : Fin k → Bool) : Fin k → Bool :=
  Function.update s i (!s i)

theorem flipAt_ne {k : ℕ} (i : Fin k) (s : Fin k → Bool) : flipAt i s ≠ s := by
  intro h
  have := congrFun h i
  simp [flipAt, Function.update] at this

theorem flipAt_involutive {k : ℕ} (i : Fin k) (s : Fin k → Bool) :
    flipAt i (flipAt i s) = s := by
  ext j
  by_cases hj : j = i
  · subst hj
    simp [flipAt, Function.update]
  · simp [flipAt, Function.update, hj]

/-- Parity of the overlap of two Boolean vectors. -/
def dot {k : ℕ} (v s : Fin k → Bool) : Bool :=
  decide ((univ.filter fun i : Fin k => v i = true ∧ s i = true).card % 2 = 1)

theorem dot_flip {k : ℕ} (v s : Fin k → Bool) (i : Fin k) (hv : v i = true) :
    dot v (flipAt i s) = !(dot v s) := by
  classical
  let old := univ.filter fun j : Fin k => v j = true ∧ s j = true
  let new := univ.filter fun j : Fin k => v j = true ∧ flipAt i s j = true
  have hagree : ∀ j, j ≠ i → (j ∈ old ↔ j ∈ new) := by
    intro j hj
    simp [old, new, flipAt, Function.update, hj]
  have hi_old : i ∈ old ↔ s i = true := by simp [old, hv]
  have hi_new : i ∈ new ↔ flipAt i s i = true := by simp [new, hv]
  have hflipi : flipAt i s i = !s i := by simp [flipAt, Function.update]
  cases hs : s i
  · have hnew : new = insert i old := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [hi_new, hflipi, hs, hi_old]
      · simp [hj, hagree j hj]
    have hnot : i ∉ old := by simp [hi_old, hs]
    have hcard : new.card = old.card + 1 := by
      rw [hnew, Finset.card_insert_of_notMem hnot]
    have hmod : (new.card % 2 = 1) ↔ ¬ (old.card % 2 = 1) := by
      rw [hcard]
      omega
    change decide (new.card % 2 = 1) = !decide (old.card % 2 = 1)
    by_cases h : old.card % 2 = 1
    · have hnewp : ¬ new.card % 2 = 1 := fun hn => (hmod.mp hn) h
      simp [h, hnewp]
    · have hnewp : new.card % 2 = 1 := (hmod.mpr h)
      simp [h, hnewp]
  · have hold : old = insert i new := by
      ext j
      by_cases hj : j = i
      · subst hj
        simp [hi_old, hs, hi_new, hflipi]
      · simp [hj, hagree j hj]
    have hnot : i ∉ new := by simp [hi_new, hflipi, hs]
    have hcard : old.card = new.card + 1 := by
      rw [hold, Finset.card_insert_of_notMem hnot]
    have hmod : (new.card % 2 = 1) ↔ ¬ (old.card % 2 = 1) := by
      rw [hcard]
      omega
    change decide (new.card % 2 = 1) = !decide (old.card % 2 = 1)
    by_cases h : old.card % 2 = 1
    · have hnewp : ¬ new.card % 2 = 1 := fun hn => (hmod.mp hn) h
      simp [h, hnewp]
    · have hnewp : new.card % 2 = 1 := (hmod.mpr h)
      simp [h, hnewp]

theorem char_sum {k : ℕ} (v : Fin k → Bool) (hv : ∃ i, v i = true) :
    ∑ s : Fin k → Bool, (if dot v s then (-1 : ℝ) else 1) = 0 := by
  classical
  obtain ⟨i, hi⟩ := hv
  refine Finset.sum_involution (fun s (_ : s ∈ univ) => flipAt i s) ?_ ?_ ?_ ?_
  · intro s _
    have hdot := dot_flip v s i hi
    cases hds : dot v s <;> simp [hds, hdot]
  · intro s _ _
    exact flipAt_ne i s
  · intro s _
    simp
  · intro s _
    exact flipAt_involutive i s

theorem fiber_half {k : ℕ} (hk : 1 ≤ k) (v : Fin k → Bool) (hv : ∃ i, v i = true)
    (b : Bool) :
    (univ.filter fun s : Fin k → Bool => dot v s = b).card = 2 ^ (k - 1) := by
  classical
  have hsum := char_sum v hv
  have hsplit : ∑ s, (if dot v s = true then (-1 : ℝ) else (1 : ℝ)) =
      ((univ.filter fun s => dot v s = false).card : ℝ) -
        ((univ.filter fun s => dot v s = true).card : ℝ) := by
    rw [Finset.sum_ite]
    simp [Finset.sum_const, nsmul_eq_mul]
    ring
  have hdiff : (univ.filter fun s => dot v s = false).card =
      (univ.filter fun s => dot v s = true).card := by
    have hsub : ((univ.filter fun s => dot v s = false).card : ℝ) -
        ((univ.filter fun s => dot v s = true).card : ℝ) = 0 := by
      rw [← hsplit]
      simpa using hsum
    exact Nat.cast_inj.mp (sub_eq_zero.mp hsub)
  have htot : (univ.filter fun s => dot v s = true).card +
      (univ.filter fun s => dot v s = false).card = 2 ^ k := by
    have hdisj : Disjoint (univ.filter fun s => dot v s = true)
        (univ.filter fun s => dot v s = false) := by
      simp [Finset.disjoint_left]
    have hunion : (univ.filter fun s => dot v s = true) ∪
        (univ.filter fun s => dot v s = false) = univ := by
      ext s
      cases h : dot v s <;> simp [h]
    rw [← Finset.card_union_of_disjoint hdisj, hunion, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := by congr 1; omega
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (k - 1) := by rw [mul_comm]
  have htrue : (univ.filter fun s => dot v s = true).card = 2 ^ (k - 1) := by
    have : (univ.filter fun s => dot v s = true).card +
        (univ.filter fun s => dot v s = true).card = 2 ^ k := by
      simpa [hdiff] using htot
    rw [← two_mul, hpow] at this
    omega
  cases b
  · simpa [hdiff] using htrue
  · exact htrue

/-- Binary representation of `i + 1`. This enumerates the nonzero vectors of `𝔽₂^k`. -/
def nonzeroVec {k : ℕ} (i : Fin (2 ^ k - 1)) : Fin k → Bool :=
  fun j => (i.val + 1).testBit j.val

theorem nonzeroVec_exists_true {k : ℕ} (hk : 1 ≤ k) (i : Fin (2 ^ k - 1)) :
    ∃ j, nonzeroVec i j = true := by
  have hlt : i.val + 1 < 2 ^ k := by
    have := i.isLt
    omega
  have hpos : i.val + 1 ≠ 0 := by omega
  by_contra h
  push_neg at h
  have hall : ∀ j, (i.val + 1).testBit j = false := by
    intro j
    by_cases hj : j < k
    · simpa [nonzeroVec] using h ⟨j, hj⟩
    · have hpow : 2 ^ k ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (le_of_not_gt hj)
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt hpow)
  exact hpos (Nat.zero_of_testBit_eq_false hall)

def basisIndex {k : ℕ} (j : Fin k) : Fin (2 ^ k - 1) :=
  ⟨2 ^ j.val - 1, by
    have hj : j.val < k := j.isLt
    have hlt : 2 ^ j.val < 2 ^ k := Nat.pow_lt_pow_right (by decide) hj
    have hle : 2 ^ j.val ≤ 2 ^ k - 1 := Nat.le_sub_one_of_lt hlt
    have hpos : 0 < 2 ^ j.val := Nat.two_pow_pos _
    exact lt_of_lt_of_le (Nat.sub_lt hpos (by decide)) hle⟩

theorem nonzeroVec_basis {k : ℕ} (j : Fin k) :
    nonzeroVec (basisIndex j) = fun i => decide (i = j) := by
  ext i
  have hidx : (basisIndex j).val + 1 = 2 ^ j.val := by
    simp [basisIndex]
    exact Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))
  simp [nonzeroVec, hidx, Nat.testBit_two_pow, Fin.ext_iff, eq_comm]

theorem dot_basis {k : ℕ} (j : Fin k) (s : Fin k → Bool) :
    dot (fun i => decide (i = j)) s = s j := by
  classical
  have hcard : (univ.filter fun i : Fin k => decide (i = j) = true ∧ s i = true).card =
      if s j = true then 1 else 0 := by
    by_cases hs : s j = true
    · have hset : univ.filter (fun i : Fin k => decide (i = j) = true ∧ s i = true) = {j} := by
        ext i
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · rintro ⟨hij, _⟩
          simpa using hij
        · intro hij
          subst hij
          exact ⟨by simp, hs⟩
      rw [hset]
      simp [hs]
    · have hset : univ.filter (fun i : Fin k => decide (i = j) = true ∧ s i = true) = ∅ := by
        ext i
        simp only [mem_filter, mem_univ, true_and, notMem_empty, iff_false]
        rintro ⟨hij, hsi⟩
        have : i = j := by simpa using hij
        subst this
        exact hs hsi
      rw [hset]
      simp [hs]
  cases hs : s j
  · rw [dot, hcard, hs]
    decide
  · rw [dot, hcard, hs]
    decide

def eval {k : ℕ} (s : Fin k → Bool) : Fin (2 ^ k - 1) → Bool :=
  fun i => dot (nonzeroVec i) s

theorem eval_injective {k : ℕ} (hk : 1 ≤ k) : Function.Injective (eval : _ → Fin (2 ^ k - 1) → Bool) := by
  intro s t hst
  ext j
  have h := congrFun hst (basisIndex j)
  simp [eval, nonzeroVec_basis, dot_basis] at h
  exact h

noncomputable def f2Law {k : ℕ} (x : Fin (2 ^ k - 1) → Bool) : ℝ :=
  (∑ s : Fin k → Bool, if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k)

theorem f2Law_nonneg {k : ℕ} (x : Fin (2 ^ k - 1) → Bool) : 0 ≤ f2Law x := by
  unfold f2Law
  positivity

theorem f2Law_of_eval {k : ℕ} (hk : 1 ≤ k) (s : Fin k → Bool) :
    f2Law (eval s) = (1 / 2 : ℝ) ^ k := by
  classical
  unfold f2Law
  have hinj := eval_injective hk
  have hsum : (∑ t : Fin k → Bool, if eval t = eval s then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single s]
    · simp
    · intro t _ ht
      have : eval t ≠ eval s := fun h => ht (hinj h)
      simp [this]
    · intro hs
      exact absurd (mem_univ s) hs
  rw [hsum]
  have : (1 / 2 : ℝ) ^ k * (2 : ℝ) ^ k = 1 := by
    rw [← mul_pow]
    norm_num
  field_simp
  simpa [mul_comm] using this.symm

theorem f2Law_total {k : ℕ} (hk : 1 ≤ k) :
    ∑ x : Fin (2 ^ k - 1) → Bool, f2Law x = 1 := by
  classical
  unfold f2Law
  have hswap : (∑ x : Fin (2 ^ k - 1) → Bool,
        (∑ s : Fin k → Bool, if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k)) =
      (∑ s : Fin k → Bool, (1 : ℝ)) / ((2 : ℝ) ^ k) := by
    calc
      (∑ x : Fin (2 ^ k - 1) → Bool,
          (∑ s : Fin k → Bool, if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k))
          = ∑ x : Fin (2 ^ k - 1) → Bool,
              ∑ s : Fin k → Bool, (if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k) := by
            apply Finset.sum_congr rfl
            intro x _
            rw [Finset.sum_div]
      _ = ∑ s : Fin k → Bool, ∑ x : Fin (2 ^ k - 1) → Bool,
            (if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k) := by
          rw [Finset.sum_comm]
      _ = ∑ s : Fin k → Bool, (1 / ((2 : ℝ) ^ k)) := by
          apply Finset.sum_congr rfl
          intro s _
          rw [Finset.sum_eq_single (eval s)]
          · simp
          · intro x _ hx
            simp [Ne.symm hx]
          · intro hx
            exact absurd (mem_univ (eval s)) hx
      _ = (∑ s : Fin k → Bool, (1 : ℝ)) / ((2 : ℝ) ^ k) := by
          rw [← Finset.sum_div]
  rw [hswap]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_bool]

theorem dot_xor {k : ℕ} (v w s : Fin k → Bool) :
    dot (fun i => (v i).xor (w i)) s = (dot v s).xor (dot w s) := by
  classical
  let A := univ.filter fun i : Fin k => v i = true ∧ s i = true
  let B := univ.filter fun i : Fin k => w i = true ∧ s i = true
  let C := univ.filter fun i : Fin k => (v i).xor (w i) = true ∧ s i = true
  have hC : C = (A \ B) ∪ (B \ A) := by
    ext i
    simp [A, B, C]
    cases hv : v i <;> cases hw : w i <;> cases hs : s i <;> simp [hv, hw, hs]
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    have ha' : a ∈ A ∧ a ∉ B := by simpa [A, B] using ha
    have hb' : a ∈ B ∧ a ∉ A := by simpa [A, B] using hb
    exact ha'.2 hb'.1
  have hcard : C.card = A.card + B.card - 2 * (A ∩ B).card := by
    rw [hC, Finset.card_union_of_disjoint hdisj]
    have h1 : (A \ B).card = A.card - (A ∩ B).card := by
      rw [Finset.card_sdiff, Finset.inter_comm]
    have h2 : (B \ A).card = B.card - (A ∩ B).card := by
      rw [Finset.card_sdiff]
    have hAle : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
    have hBle : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    rw [h1, h2]
    omega
  have hsumAB : A.card + B.card = C.card + 2 * (A ∩ B).card := by
    rw [hcard]
    have hAle : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
    have hBle : (A ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
    omega
  have h2 : (2 * (A ∩ B).card) % 2 = 0 := by
    simp [Nat.mul_mod]
  have hmod : C.card % 2 = (A.card + B.card) % 2 := by
    rw [hsumAB, Nat.add_mod, h2, Nat.add_zero]
    exact (Nat.mod_mod _ _).symm
  have hxor : (decide (A.card % 2 = 1) ^^ decide (B.card % 2 = 1)) =
      decide ((A.card + B.card) % 2 = 1) := by
    have ha : A.card % 2 = 0 ∨ A.card % 2 = 1 := by omega
    have hb : B.card % 2 = 0 ∨ B.card % 2 = 1 := by omega
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb, Nat.add_mod]
  change (decide (C.card % 2 = 1)) = (decide (A.card % 2 = 1) ^^ decide (B.card % 2 = 1))
  rw [hmod]
  exact hxor.symm

theorem xor_exists_true {k : ℕ} (v w : Fin k → Bool) (hvw : v ≠ w) :
    ∃ i, (v i).xor (w i) = true := by
  by_contra h
  push_neg at h
  apply hvw
  ext i
  have := h i
  cases hv : v i <;> cases hw : w i <;> simp_all

theorem pair_fiber {k : ℕ} (hk : 2 ≤ k) (v w : Fin k → Bool) (hvw : v ≠ w)
    (hv : ∃ i, v i = true) (hw : ∃ i, w i = true) (b c : Bool) :
    (univ.filter fun s : Fin k → Bool => dot v s = b ∧ dot w s = c).card = 2 ^ (k - 2) := by
  classical
  let N (b c : Bool) :=
    (univ.filter fun s : Fin k → Bool => dot v s = b ∧ dot w s = c).card
  have hvT : N true false + N true true = 2 ^ (k - 1) := by
    have hsplit : univ.filter (fun s => dot v s = true) =
        (univ.filter fun s => dot v s = true ∧ dot w s = false) ∪
        (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
      apply Finset.ext
      intro s
      constructor
      · intro hs
        have hdv : dot v s = true := (Finset.mem_filter.mp hs).2
        refine Finset.mem_union.mpr ?_
        cases hws : dot w s
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hdv, hws⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hdv, hws⟩)
      · intro hs
        rcases Finset.mem_union.mp hs with hs | hs
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, (Finset.mem_filter.mp hs).2.1⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, (Finset.mem_filter.mp hs).2.1⟩
    have hdisj : Disjoint (univ.filter fun s => dot v s = true ∧ dot w s = false)
        (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
      rw [Finset.disjoint_left]
      intro s hs ht
      have h1 := (Finset.mem_filter.mp hs).2
      have h2 := (Finset.mem_filter.mp ht).2
      have : (false : Bool) = true := by
        rw [← h1.2]
        exact h2.2
      cases this
    rw [← Finset.card_union_of_disjoint hdisj, ← hsplit]
    exact fiber_half (by omega) v hv true
  have hwT : N false true + N true true = 2 ^ (k - 1) := by
    have hsplit : univ.filter (fun s => dot w s = true) =
        (univ.filter fun s => dot v s = false ∧ dot w s = true) ∪
        (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
      apply Finset.ext
      intro s
      constructor
      · intro hs
        have hdw : dot w s = true := (Finset.mem_filter.mp hs).2
        refine Finset.mem_union.mpr ?_
        cases hvs : dot v s
        · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hvs, hdw⟩)
        · exact Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ s, hvs, hdw⟩)
      · intro hs
        rcases Finset.mem_union.mp hs with hs | hs
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, (Finset.mem_filter.mp hs).2.2⟩
        · exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, (Finset.mem_filter.mp hs).2.2⟩
    have hdisj : Disjoint (univ.filter fun s => dot v s = false ∧ dot w s = true)
        (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
      rw [Finset.disjoint_left]
      intro s hs ht
      have h1 := (Finset.mem_filter.mp hs).2
      have h2 := (Finset.mem_filter.mp ht).2
      have : (false : Bool) = true := by
        rw [← h1.1]
        exact h2.1
      cases this
    rw [← Finset.card_union_of_disjoint hdisj, ← hsplit]
    exact fiber_half (by omega) w hw true
  have heq : N false false + N true true = 2 ^ (k - 1) := by
    have hsplit : univ.filter (fun s => (dot v s).xor (dot w s) = false) =
        (univ.filter fun s => dot v s = false ∧ dot w s = false) ∪
        (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
      apply Finset.ext
      intro s
      constructor
      · intro hs
        have hxor : (dot v s).xor (dot w s) = false := (Finset.mem_filter.mp hs).2
        cases h1 : dot v s <;> cases h2 : dot w s
        · exact Finset.mem_union.mpr
            (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h1, h2⟩))
        · simp [h1, h2] at hxor
        · simp [h1, h2] at hxor
        · exact Finset.mem_union.mpr
            (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ s, h1, h2⟩))
      · intro hs
        rcases Finset.mem_union.mp hs with hs | hs
        · have h := (Finset.mem_filter.mp hs).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, by simp [h.1, h.2]⟩
        · have h := (Finset.mem_filter.mp hs).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, by simp [h.1, h.2]⟩
    have hdisj : Disjoint (univ.filter fun s => dot v s = false ∧ dot w s = false)
        (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
      rw [Finset.disjoint_left]
      intro s hs ht
      have h1 := (Finset.mem_filter.mp hs).2
      have h2 := (Finset.mem_filter.mp ht).2
      have : (false : Bool) = true := by
        rw [← h1.1]
        exact h2.1
      cases this
    have hxorset : univ.filter (fun s => (dot v s).xor (dot w s) = false) =
        univ.filter (fun s => dot (fun i => (v i).xor (w i)) s = false) := by
      apply Finset.ext
      intro s
      constructor
      · intro hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, by
          rw [dot_xor]
          exact (Finset.mem_filter.mp hs).2⟩
      · intro hs
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ s, by
          rw [← dot_xor]
          exact (Finset.mem_filter.mp hs).2⟩
    rw [← Finset.card_union_of_disjoint hdisj, ← hsplit, hxorset]
    exact fiber_half (by omega) (fun i => (v i).xor (w i)) (xor_exists_true v w hvw) false
  have hpow1 : 2 ^ (k - 1) = 2 * 2 ^ (k - 2) := by
    have : k - 1 = (k - 2) + 1 := by omega
    rw [this, pow_succ, mul_comm]
  have hpowk : 2 ^ k = 2 * 2 ^ (k - 1) := by
    have hexp : k = (k - 1) + 1 := by omega
    calc
      2 ^ k = 2 ^ ((k - 1) + 1) := congrArg (fun n => 2 ^ n) hexp
      _ = 2 ^ (k - 1) * 2 := by rw [pow_succ]
      _ = 2 * 2 ^ (k - 1) := by rw [mul_comm]
  have hNtt : N true true = 2 ^ (k - 2) := by
    have h2 : 2 * N true true =
        (N true false + N true true) + (N false true + N true true) +
          (N false false + N true true) -
          (N false false + N false true + N true false + N true true) := by
      omega
    rw [hvT, hwT, heq] at h2
    have : 2 * N true true = 2 ^ (k - 1) := by
      have htot : N false false + N false true + N true false + N true true = 2 ^ k := by
        have hpart : univ =
            (univ.filter fun s => dot v s = false ∧ dot w s = false) ∪
            (univ.filter fun s => dot v s = false ∧ dot w s = true) ∪
            (univ.filter fun s => dot v s = true ∧ dot w s = false) ∪
            (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
          ext s
          simp only [mem_univ, mem_union, mem_filter, true_and, iff_true]
          cases dot v s <;> cases dot w s <;> simp
        have hdisj12 : Disjoint (univ.filter fun s => dot v s = false ∧ dot w s = false)
            (univ.filter fun s => dot v s = false ∧ dot w s = true) := by
          rw [Finset.disjoint_left]
          intro s hs ht
          have h1 := (Finset.mem_filter.mp hs).2
          have h2 := (Finset.mem_filter.mp ht).2
          have : (false : Bool) = true := by
            rw [← h1.2]
            exact h2.2
          cases this
        have hdisj34 : Disjoint (univ.filter fun s => dot v s = true ∧ dot w s = false)
            (univ.filter fun s => dot v s = true ∧ dot w s = true) := by
          rw [Finset.disjoint_left]
          intro s hs ht
          have h1 := (Finset.mem_filter.mp hs).2
          have h2 := (Finset.mem_filter.mp ht).2
          have : (false : Bool) = true := by
            rw [← h1.2]
            exact h2.2
          cases this
        have hleft : (univ.filter fun s => dot v s = false ∧ dot w s = false) ∪
            (univ.filter fun s => dot v s = false ∧ dot w s = true) =
            univ.filter fun s => dot v s = false := by
          ext s
          simp only [mem_union, mem_filter, mem_univ, true_and]
          cases dot w s <;> simp
        have hright : (univ.filter fun s => dot v s = true ∧ dot w s = false) ∪
            (univ.filter fun s => dot v s = true ∧ dot w s = true) =
            univ.filter fun s => dot v s = true := by
          ext s
          simp only [mem_union, mem_filter, mem_univ, true_and]
          cases dot w s <;> simp
        have hdisj : Disjoint (univ.filter fun s => dot v s = false)
            (univ.filter fun s => dot v s = true) := by
          rw [Finset.disjoint_left]
          intro s hs ht
          have h1 := (Finset.mem_filter.mp hs).2
          have h2 := (Finset.mem_filter.mp ht).2
          have : (false : Bool) = true := by
            rw [← h1]
            exact h2
          cases this
        have hunion : (univ.filter fun s => dot v s = false) ∪
            (univ.filter fun s => dot v s = true) = univ := by
          ext s
          simp only [mem_union, mem_filter, mem_univ, true_and, iff_true]
          cases dot v s <;> simp
        calc
          N false false + N false true + N true false + N true true
              = ((univ.filter fun s => dot v s = false ∧ dot w s = false) ∪
                  (univ.filter fun s => dot v s = false ∧ dot w s = true)).card +
                ((univ.filter fun s => dot v s = true ∧ dot w s = false) ∪
                  (univ.filter fun s => dot v s = true ∧ dot w s = true)).card := by
                rw [Finset.card_union_of_disjoint hdisj12, Finset.card_union_of_disjoint hdisj34]
                ring
          _ = (univ.filter fun s => dot v s = false).card +
                (univ.filter fun s => dot v s = true).card := by
                rw [hleft, hright]
          _ = univ.card := by
                rw [← Finset.card_union_of_disjoint hdisj, hunion]
          _ = 2 ^ k := by
                rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      rw [htot, hpowk] at h2
      omega
    omega
  have hNtf : N true false = 2 ^ (k - 2) := by
    have := hvT
    rw [hNtt, hpow1] at this
    omega
  have hNft : N false true = 2 ^ (k - 2) := by
    have := hwT
    rw [hNtt, hpow1] at this
    omega
  have hNff : N false false = 2 ^ (k - 2) := by
    have := heq
    rw [hNtt, hpow1] at this
    omega
  cases b <;> cases c
  · simpa [N] using hNff
  · simpa [N] using hNft
  · simpa [N] using hNtf
  · simpa [N] using hNtt

theorem f2_pairwise {k : ℕ} (hk : 1 ≤ k) :
    LocalSeparation.PairwiseFair (f2Law : (Fin (2 ^ k - 1) → Bool) → ℝ) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x
    exact f2Law_nonneg x
  · exact f2Law_total hk
  · intro i b
    unfold LocalSeparation.bitMass
    have hpull : ∑ x, (if x i = b then f2Law x else 0) =
        (∑ s : Fin k → Bool, if eval s i = b then (1 : ℝ) else 0) / ((2 : ℝ) ^ k) := by
      unfold f2Law
      have hstep : ∀ x, (if x i = b then
            (∑ s : Fin k → Bool, if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k) else 0) =
          (∑ s : Fin k → Bool, if x i = b ∧ eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k) := by
        intro x
        by_cases hx : x i = b
        · rw [if_pos hx]
          apply congrArg (fun t => t / ((2 : ℝ) ^ k))
          apply Finset.sum_congr rfl
          intro s _
          simp only [hx, true_and]
        · rw [if_neg hx]
          have hzero : ∀ s, (if x i = b ∧ eval s = x then (1 : ℝ) else 0) = 0 := by
            intro s
            simp only [hx, false_and, if_false]
          rw [Finset.sum_congr rfl fun s _ => hzero s, Finset.sum_const_zero, zero_div]
      simp_rw [hstep]
      calc
        ∑ x, (∑ s : Fin k → Bool, if x i = b ∧ eval s = x then (1 : ℝ) else 0) /
            ((2 : ℝ) ^ k)
            = (∑ x, ∑ s : Fin k → Bool, if x i = b ∧ eval s = x then (1 : ℝ) else 0) /
                ((2 : ℝ) ^ k) := (Finset.sum_div _ _ _).symm
        _ = (∑ s : Fin k → Bool, ∑ x, if x i = b ∧ eval s = x then (1 : ℝ) else 0) /
              ((2 : ℝ) ^ k) := by
              apply congrArg (fun t => t / ((2 : ℝ) ^ k))
              exact Finset.sum_comm
        _ = (∑ s : Fin k → Bool, if eval s i = b then (1 : ℝ) else 0) /
              ((2 : ℝ) ^ k) := by
              apply congrArg (fun t => t / ((2 : ℝ) ^ k))
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.sum_eq_single (eval s)]
              · simp
              · intro x _ hx
                simp [Ne.symm hx]
              · intro hmem
                exact absurd (mem_univ (eval s)) hmem
    rw [hpull]
    have hcard : (univ.filter fun s : Fin k → Bool => eval s i = b).card = 2 ^ (k - 1) := by
      change (univ.filter fun s : Fin k → Bool => dot (nonzeroVec i) s = b).card = 2 ^ (k - 1)
      exact fiber_half hk (nonzeroVec i) (nonzeroVec_exists_true hk i) b
    have hsum : (∑ s, if eval s i = b then (1 : ℝ) else 0) =
        ((univ.filter fun s => eval s i = b).card : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
      simp
    rw [hsum, hcard]
    have hpow : ((2 : ℝ) ^ (k - 1)) / ((2 : ℝ) ^ k) = 1 / 2 := by
      have hk' : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
        have hexp : k = (k - 1) + 1 := by omega
        calc
          (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 1) + 1) :=
            congrArg (fun n : ℕ => (2 : ℝ) ^ n) hexp
          _ = (2 : ℝ) ^ (k - 1) * 2 := by rw [pow_succ]
      rw [hk']
      field_simp
    simpa [Nat.cast_pow] using hpow
  · intro i j hij b c
    unfold LocalSeparation.pairMass
    have hk2 : 2 ≤ k := by
      by_contra hk1
      have hk0 : k = 1 := by omega
      subst hk0
      have : i = j := by
        fin_cases i <;> fin_cases j <;> rfl
      exact hij this
    have hpull : ∑ x, (if x i = b ∧ x j = c then f2Law x else 0) =
        (∑ s : Fin k → Bool, if eval s i = b ∧ eval s j = c then (1 : ℝ) else 0) /
          ((2 : ℝ) ^ k) := by
      unfold f2Law
      have hstep : ∀ x, (if x i = b ∧ x j = c then
            (∑ s : Fin k → Bool, if eval s = x then (1 : ℝ) else 0) / ((2 : ℝ) ^ k) else 0) =
          (∑ s : Fin k → Bool, if (x i = b ∧ x j = c) ∧ eval s = x then (1 : ℝ) else 0) /
            ((2 : ℝ) ^ k) := by
        intro x
        by_cases hx : x i = b ∧ x j = c
        · rw [if_pos hx]
          apply congrArg (fun t => t / ((2 : ℝ) ^ k))
          apply Finset.sum_congr rfl
          intro s _
          simp only [hx, true_and]
        · rw [if_neg hx]
          have hzero : ∀ s,
              (if (x i = b ∧ x j = c) ∧ eval s = x then (1 : ℝ) else 0) = 0 := by
            intro s
            simp only [hx, false_and, if_false]
          rw [Finset.sum_congr rfl fun s _ => hzero s, Finset.sum_const_zero, zero_div]
      simp_rw [hstep]
      calc
        ∑ x, (∑ s : Fin k → Bool, if (x i = b ∧ x j = c) ∧ eval s = x then (1 : ℝ) else 0) /
            ((2 : ℝ) ^ k)
            = (∑ x, ∑ s : Fin k → Bool,
                if (x i = b ∧ x j = c) ∧ eval s = x then (1 : ℝ) else 0) /
                ((2 : ℝ) ^ k) := (Finset.sum_div _ _ _).symm
        _ = (∑ s : Fin k → Bool, ∑ x,
              if (x i = b ∧ x j = c) ∧ eval s = x then (1 : ℝ) else 0) /
              ((2 : ℝ) ^ k) := by
              apply congrArg (fun t => t / ((2 : ℝ) ^ k))
              exact Finset.sum_comm
        _ = (∑ s : Fin k → Bool, if eval s i = b ∧ eval s j = c then (1 : ℝ) else 0) /
              ((2 : ℝ) ^ k) := by
              apply congrArg (fun t => t / ((2 : ℝ) ^ k))
              apply Finset.sum_congr rfl
              intro s _
              rw [Finset.sum_eq_single (eval s)]
              · simp
              · intro x _ hx
                simp [Ne.symm hx]
              · intro hmem
                exact absurd (mem_univ (eval s)) hmem
    rw [hpull]
    have hvw : nonzeroVec i ≠ nonzeroVec j := by
      intro h
      apply hij
      apply Fin.ext
      have ha := congrFun h
      have hbit : ∀ t, (i.val + 1).testBit t = (j.val + 1).testBit t := by
        intro t
        by_cases ht : t < k
        · simpa [nonzeroVec] using ha ⟨t, ht⟩
        · have hi' : i.val + 1 < 2 ^ k := by have := i.isLt; omega
          have hj' : j.val + 1 < 2 ^ k := by have := j.isLt; omega
          have hpow : 2 ^ k ≤ 2 ^ t := Nat.pow_le_pow_right (by decide) (le_of_not_gt ht)
          rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hi' hpow),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hj' hpow)]
      have heq : i.val + 1 = j.val + 1 := Nat.eq_of_testBit_eq hbit
      omega
    have hcard : (univ.filter fun s : Fin k → Bool =>
        eval s i = b ∧ eval s j = c).card = 2 ^ (k - 2) := by
      change (univ.filter fun s : Fin k → Bool =>
        dot (nonzeroVec i) s = b ∧ dot (nonzeroVec j) s = c).card = 2 ^ (k - 2)
      exact pair_fiber hk2 (nonzeroVec i) (nonzeroVec j) hvw
        (nonzeroVec_exists_true hk i) (nonzeroVec_exists_true hk j) b c
    have hsum : (∑ s, if eval s i = b ∧ eval s j = c then (1 : ℝ) else 0) =
        (2 ^ (k - 2) : ℝ) := by
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
      simp [hcard, nsmul_eq_mul]
    rw [hsum]
    have hpow : ((2 : ℝ) ^ (k - 2)) / ((2 : ℝ) ^ k) = 1 / 4 := by
      have hk' : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 2) * 4 := by
        have hexp : k = (k - 2) + 2 := by omega
        calc
          (2 : ℝ) ^ k = (2 : ℝ) ^ ((k - 2) + 2) :=
            congrArg (fun n : ℕ => (2 : ℝ) ^ n) hexp
          _ = (2 : ℝ) ^ (k - 2) * 2 ^ 2 := by rw [pow_add]
          _ = (2 : ℝ) ^ (k - 2) * 4 := by norm_num
      rw [hk']
      field_simp
    simpa using hpow

theorem f2_entropy {k : ℕ} (hk : 1 ≤ k) :
    ∑ x : Fin (2 ^ k - 1) → Bool, Vanishing.shannonTerm (f2Law x) = (k : ℝ) := by
  classical
  have hinj : Function.Injective (eval (k := k)) := eval_injective hk
  have hpos : ∀ s : Fin k → Bool, f2Law (eval s) = (1 / 2 : ℝ) ^ k :=
    fun s => f2Law_of_eval hk s
  have hzero : ∀ x : Fin (2 ^ k - 1) → Bool,
      (∀ s : Fin k → Bool, eval s ≠ x) → f2Law x = 0 := by
    intro x hx
    unfold f2Law
    simp [hx]
  let img : Finset (Fin (2 ^ k - 1) → Bool) := univ.image (eval (k := k))
  have himage : ∑ x ∈ img, Vanishing.shannonTerm (f2Law x) =
      ∑ s : Fin k → Bool, Vanishing.shannonTerm (f2Law (eval (k := k) s)) := by
    simpa [img] using (Finset.sum_image hinj.injOn :
      ∑ x ∈ univ.image (eval (k := k)), Vanishing.shannonTerm (f2Law x) =
        ∑ s ∈ univ, Vanishing.shannonTerm (f2Law (eval (k := k) s)))
  have hrest : ∑ x ∈ univ \ img, Vanishing.shannonTerm (f2Law x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    have hx' : ∀ s : Fin k → Bool, eval s ≠ x := by
      intro s hs
      have hx'' : x ∉ img := (Finset.mem_sdiff.mp hx).2
      exact hx'' (Finset.mem_image.mpr ⟨s, mem_univ s, hs⟩)
    simp [hzero x hx', Vanishing.shannonTerm]
  have hunion : ∑ x : Fin (2 ^ k - 1) → Bool, Vanishing.shannonTerm (f2Law x) =
      ∑ x ∈ img, Vanishing.shannonTerm (f2Law x) +
        ∑ x ∈ univ \ img, Vanishing.shannonTerm (f2Law x) := by
    have hcover : img ∪ (univ \ img) =
        (univ : Finset (Fin (2 ^ k - 1) → Bool)) :=
      Finset.union_sdiff_of_subset (Finset.subset_univ img)
    calc
      ∑ x : Fin (2 ^ k - 1) → Bool, Vanishing.shannonTerm (f2Law x)
          = ∑ x ∈ img ∪ (univ \ img), Vanishing.shannonTerm (f2Law x) := by
            rw [hcover]
      _ = ∑ x ∈ img, Vanishing.shannonTerm (f2Law x) +
            ∑ x ∈ univ \ img, Vanishing.shannonTerm (f2Law x) :=
        Finset.sum_union Finset.disjoint_sdiff
  rw [hunion, hrest, add_zero, himage]
  simp_rw [hpos]
  exact CapacityScale.fairBlock_entropy k

/-- For `m = 2^k - 1`, pairwise independent fair bits are realized at entropy `k`. -/
theorem f2_exact {k : ℕ} (hk : 1 ≤ k) :
    ∃ μ : (Fin (2 ^ k - 1) → Bool) → ℝ,
      LocalSeparation.PairwiseFair μ ∧
        ∑ x, Vanishing.shannonTerm (μ x) = (k : ℝ) :=
  ⟨f2Law, f2_pairwise hk, f2_entropy hk⟩

/-- Every pairwise fair law on `2^k - 1` bits costs at least `k`, so the construction is optimal. -/
theorem f2_optimal {k : ℕ} (hk : 1 ≤ k) (μ : (Fin (2 ^ k - 1) → Bool) → ℝ)
    (h : LocalSeparation.PairwiseFair μ) :
    (k : ℝ) ≤ ∑ x, Vanishing.shannonTerm (μ x) := by
  have hge := LocalSeparation.pairwise_entropy_ge μ h
  have hcast : ((2 ^ k - 1 : ℕ) : ℝ) + 1 = ((2 ^ k : ℕ) : ℝ) := by
    have hpos : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by decide)
    rw [Nat.cast_sub hpos, Nat.cast_one]
    ring
  rw [hcast, LocalSeparation.logb_two_pow] at hge
  exact hge

end LinearLocal

end

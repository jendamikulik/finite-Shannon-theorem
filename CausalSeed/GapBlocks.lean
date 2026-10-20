/-
Finite bookkeeping for the interleaved decoder: products over a partition of `range n`
into blocks, list products as range products, windows of a list, and the entropy of a
product of independent finite laws.
-/
import CausalSeed.GapDecoder

noncomputable section
open Classical Finset

namespace CausalSpectrum.Gap

/-- A partition of `range n` into the blocks `[O j, O j + s j)`. -/
structure Blocks (n r : ℕ) where
  O : Fin r → ℕ
  s : Fin r → ℕ
  le : ∀ j, O j + s j ≤ n
  uniq : ∀ j j' c, O j ≤ c → c < O j + s j → O j' ≤ c → c < O j' + s j' → j = j'
  cover : ∀ c < n, ∃ j, O j ≤ c ∧ c < O j + s j

theorem Blocks.prod_eq {n r : ℕ} (B : Blocks n r) {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ j, ∏ t ∈ range (B.s j), f (B.O j + t) = ∏ c ∈ range n, f c := by
  rw [← Finset.prod_sigma (s := univ) (t := fun j => range (B.s j))
    (f := fun x => f (B.O x.1 + x.2))]
  refine prod_bij (fun x _ => B.O x.1 + x.2) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x hx
    simp only [mem_sigma, mem_range] at hx
    exact mem_range.2 (lt_of_lt_of_le (by omega) (B.le x.1))
  · intro x hx y hy hxy
    simp only [mem_sigma, mem_range] at hx hy
    have hj := B.uniq x.1 y.1 (B.O x.1 + x.2) (by omega) (by omega) (by omega) (by omega)
    obtain ⟨j, t⟩ := x; obtain ⟨j', t'⟩ := y
    simp only at hj hxy; subst hj
    have : t = t' := by omega
    subst this; rfl
  · intro c hc
    obtain ⟨j, h1, h2⟩ := B.cover c (mem_range.1 hc)
    exact ⟨⟨j, c - B.O j⟩, by simp only [mem_sigma, mem_range]; exact ⟨mem_univ _, by omega⟩,
      by simp only; omega⟩

theorem list_prod_eq_range {α M : Type*} [CommMonoid M] (f : α → M) (d : α) :
    ∀ L : List α, (L.map f).prod = ∏ c ∈ range L.length, f (L.getD c d)
  | [] => by simp
  | e :: L => by
    rw [List.map_cons, List.prod_cons, list_prod_eq_range f d L, List.length_cons,
      prod_range_succ']
    simp [mul_comm]

/-- The window `[O, O + q)` of a list. -/
def win {α : Type*} (O q : ℕ) (L : List α) : List α := (L.drop O).take q

theorem win_getD {α : Type*} (O q : ℕ) (L : List α) (d : α) {k} (hk : k < q) :
    (win O q L).getD k d = L.getD (O + k) d := by
  simp only [win, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hk, List.getElem?_drop]

theorem length_win {α : Type*} (O q : ℕ) (L : List α) :
    (win O q L).length = min q (L.length - O) := by
  simp [win, min_comm]

theorem win_prod {α M : Type*} [CommMonoid M] (f : α → M) (d : α) (O q : ℕ) (L : List α) :
    ((win O q L).map f).prod =
      ∏ t ∈ range q, (if O + t < L.length then f (L.getD (O + t) d) else 1) := by
  rw [list_prod_eq_range f d, ← prod_filter, length_win]
  have : (range q).filter (fun t => O + t < L.length) = range (min q (L.length - O)) := by
    ext t; simp only [mem_filter, mem_range, lt_min_iff]; omega
  rw [this]
  refine prod_congr rfl fun t ht => ?_
  rw [win_getD O q L d (lt_of_lt_of_le (mem_range.1 ht) (min_le_left _ _))]

/-- Entropy of a product of independent finite laws. -/
theorem entropy_pi {r : ℕ} {Ω : Fin r → Type*} [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (w : ∀ j, Ω j → ℝ) (hw : ∀ j o, 0 ≤ w j o) (hs : ∀ j, ∑ o, w j o = 1) :
    ∑ ω : (∀ j, Ω j), Real.negMulLog (∏ j, w j (ω j)) = ∑ j, ∑ o, Real.negMulLog (w j o) := by
  set g : Fin r → ∀ t, Ω t → ℝ := fun s t o => w t o * (if t = s then -Real.log (w t o) else 1)
  have e : ∀ ω : (∀ j, Ω j), Real.negMulLog (∏ j, w j (ω j)) = ∑ s, ∏ t, g s t (ω t) := by
    intro ω
    have : ∀ s, ∏ t, g s t (ω t) = (∏ j, w j (ω j)) * -Real.log (w s (ω s)) := fun s => by
      simp only [g, prod_mul_distrib]
      rw [prod_ite_eq' univ s]; simp
    simp_rw [this, ← mul_sum]
    by_cases hz : ∀ j, w j (ω j) ≠ 0
    · rw [Real.negMulLog, Real.log_prod (fun t _ => hz t)]
      simp only [sum_neg_distrib]; ring
    · push_neg at hz
      obtain ⟨j, hj⟩ := hz
      rw [prod_eq_zero (mem_univ j) hj]; simp
  simp_rw [e]
  rw [sum_comm]
  have h2 : ∀ s, ∑ ω : (∀ j, Ω j), ∏ t, g s t (ω t) = ∑ o, Real.negMulLog (w s o) := by
    intro s
    rw [← Fintype.prod_sum]
    have : ∀ t, ∑ o, g s t o = if t = s then ∑ o, Real.negMulLog (w s o) else 1 := by
      intro t; by_cases h : t = s
      · subst h; simp only [g, if_true]; refine sum_congr rfl fun y _ => ?_; simp [Real.negMulLog]
      · simp [g, h, hs]
    simp_rw [this]
    rw [prod_ite_eq' univ s]; simp
  simp_rw [h2]

end CausalSpectrum.Gap

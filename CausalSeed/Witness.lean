/-
Lower bound `2/9 ≤ gapSup` on the recorded five-parameter witness.

At `θ₀ = (4/9, 1/4, 1/2, 2/5, 1/5)` an ordinary coupling has entropy
`H(3,2,2,1,1)/9`, and every causal coupling has entropy at least
`H(3,2,1,1,1,1)/9`. Those profile entropies differ by `2/9`, so
`2/9 ≤ gapOf witnessTree` and therefore `2/9 ≤ gapSup`. The number was
already recorded; this file checks that inequality. It does not identify
`gapSup`, it does not prove that either minimum equals its profile, and
it does not claim priority.

Not proved here: the open box of kernels with gap above `1/20`, and the claim
that every ordinary minimizer on that box has an integer relation of `ℓ¹` norm
at most 13.
-/
import CausalSeed.Penalty
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

noncomputable section
open Classical
open Finset
namespace CausalSpectrum

/-! ## Entropy as a concave function -/

theorem entTerm_eq_negMulLog (w : ℝ) :
    entTerm w = Real.negMulLog w / Real.log 2 := by
  unfold entTerm infoMass Real.negMulLog
  by_cases hw : w = 0
  · simp [hw, Real.logb]
  · rw [if_neg hw, Real.logb]
    field_simp

theorem strictConcaveOn_entTerm : StrictConcaveOn ℝ (Set.Ici (0 : ℝ)) entTerm := by
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hconc := (Real.strictConcaveOn_negMulLog).2 hx hy hxy ha hb hab
  simp only [smul_eq_mul] at hconc ⊢
  have hsum : a * entTerm x + b * entTerm y =
      (a * Real.negMulLog x + b * Real.negMulLog y) / Real.log 2 := by
    rw [entTerm_eq_negMulLog, entTerm_eq_negMulLog]
    field_simp
  have hmid : entTerm (a * x + b * y) =
      Real.negMulLog (a * x + b * y) / Real.log 2 := entTerm_eq_negMulLog _
  rw [hsum, hmid]
  exact div_lt_div_of_pos_right hconc hlog

theorem concaveOn_entTerm : ConcaveOn ℝ (Set.Ici (0 : ℝ)) entTerm :=
  strictConcaveOn_entTerm.concaveOn

theorem convexOn_negEntTerm : ConvexOn ℝ (Set.Ici (0 : ℝ)) fun w => -entTerm w :=
  concaveOn_entTerm.neg

theorem strictConvexOn_negEntTerm : StrictConvexOn ℝ (Set.Ici (0 : ℝ)) fun w => -entTerm w :=
  strictConcaveOn_entTerm.neg

/-! ## Partial sums and Karamata -/

def psum {n : ℕ} (z : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i : Fin n, if i.1 < k then z i else 0

theorem psum_zero {n : ℕ} (z : Fin n → ℝ) : psum z 0 = 0 := by
  unfold psum
  apply Finset.sum_eq_zero
  intro i _
  simp

theorem psum_of_ge {n : ℕ} (z : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) : psum z k = ∑ i, z i := by
  unfold psum
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [lt_of_lt_of_le i.isLt hk]

theorem psum_succ {n : ℕ} (z : Fin (n + 1) → ℝ) (k : ℕ) (hk : k < n + 1) :
    psum z (k + 1) = psum z k + z ⟨k, hk⟩ := by
  unfold psum
  have hsplit :
      ∑ i : Fin (n + 1), (if i.1 < k + 1 then z i else 0) =
        ∑ i, (if i.1 < k then z i else 0) +
          ∑ i, (if i.1 = k then z i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hik : i.1 < k
    · simp [hik, Nat.lt_succ_of_lt hik, Nat.ne_of_lt hik]
    · by_cases he : i.1 = k
      · simp [hik, he, Nat.lt_succ_self]
      · have hge : ¬ i.1 < k + 1 := by omega
        simp [hik, he, hge]
  rw [hsplit]
  congr 1
  have hpt : ∀ i : Fin (n + 1),
      (if i.1 = k then z i else 0) = if i = ⟨k, hk⟩ then z ⟨k, hk⟩ else 0 := by
    intro i
    by_cases he : i = ⟨k, hk⟩
    · simp [he]
    · have hne : i.1 ≠ k := by
        intro hv
        apply he
        ext
        exact hv
      simp [he, hne]
  simp_rw [hpt]
  have hconst : ∀ i : Fin (n + 1),
      (if i = ⟨k, hk⟩ then z ⟨k, hk⟩ else 0) =
        if i = ⟨k, hk⟩ then z i else 0 := by
    intro i
    by_cases he : i = ⟨k, hk⟩ <;> simp [he]
  simp_rw [hconst]
  have hflip : ∀ i : Fin (n + 1),
      (if i = ⟨k, hk⟩ then z i else 0) = if ⟨k, hk⟩ = i then z i else 0 := by
    intro i
    by_cases he : i = ⟨k, hk⟩
    · simp [he]
    · simp [he, Ne.symm he]
  simp_rw [hflip]
  rw [Finset.sum_ite_eq]
  simp [hk]

def negEnt (w : ℝ) : ℝ := -entTerm w

theorem negEnt_sum_eq {n : ℕ} (z : Fin n → ℝ) :
    ∑ i, negEnt (z i) = -∑ i, entTerm (z i) := by
  simp [negEnt, Finset.sum_neg_distrib]

/-- Secant of `-entTerm`. At a repeated point the value is unused. -/
def negSlope (a b : ℝ) : ℝ :=
  if a = b then 0 else (negEnt a - negEnt b) / (a - b)

theorem ratio_swap (u v p q : ℝ) : (u - v) / (p - q) = (v - u) / (q - p) := by
  have h1 : u - v = -(v - u) := by ring
  have h2 : p - q = -(q - p) := by ring
  rw [h1, h2]
  exact neg_div_neg_eq (v - u) (q - p)

theorem negSlope_eq {a b : ℝ} (hne : a ≠ b) :
    negSlope a b = (negEnt a - negEnt b) / (a - b) := by
  simp [negSlope, hne]

theorem negSlope_mono {a1 b1 a2 b2 : ℝ}
    (ha1 : 0 ≤ a1) (hb1 : 0 ≤ b1) (ha2 : 0 ≤ a2) (hb2 : 0 ≤ b2)
    (ha : a2 ≤ a1) (hb : b2 ≤ b1) (hne1 : a1 ≠ b1) (hne2 : a2 ≠ b2) :
    negSlope a2 b2 ≤ negSlope a1 b1 := by
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) negEnt := by
    unfold negEnt
    exact convexOn_negEntTerm
  have hmem1a : a1 ∈ Set.Ici (0 : ℝ) := ha1
  have hmem1b : b1 ∈ Set.Ici (0 : ℝ) := hb1
  have hmem2a : a2 ∈ Set.Ici (0 : ℝ) := ha2
  have hmem2b : b2 ∈ Set.Ici (0 : ℝ) := hb2
  by_cases hmid : a2 = b1
  · subst hmid
    have ha12 : b2 < a2 := lt_of_le_of_ne hb (Ne.symm hne2)
    have ha21 : a2 < a1 := lt_of_le_of_ne ha (Ne.symm hne1)
    have hslope := hconv.slope_mono_adjacent hmem2b hmem1a ha12 ha21
    rw [negSlope_eq hne2, negSlope_eq hne1]
    simpa [negEnt] using hslope
  · have hstep2 : negSlope a2 b2 ≤ negSlope a2 b1 := by
      rw [negSlope_eq hne2, negSlope_eq hmid]
      have hmono := hconv.slope_mono hmem2a
      have hmemB2 : b2 ∈ Set.Ici 0 \ {a2} := by simp [hmem2b, Ne.symm hne2]
      have hmemB1 : b1 ∈ Set.Ici 0 \ {a2} := by simp [hmem1b, Ne.symm hmid]
      have hs := hmono hmemB2 hmemB1 hb
      simp only [slope_def_field] at hs
      have hL := ratio_swap (negEnt a2) (negEnt b2) a2 b2
      have hR := ratio_swap (negEnt a2) (negEnt b1) a2 b1
      unfold negEnt at hs hL hR ⊢
      linarith
    have hstep1 : negSlope a2 b1 ≤ negSlope a1 b1 := by
      rw [negSlope_eq hmid, negSlope_eq hne1]
      have hmono := hconv.slope_mono hmem1b
      have hmemA2 : a2 ∈ Set.Ici 0 \ {b1} := by simp [hmem2a, hmid]
      have hmemA1 : a1 ∈ Set.Ici 0 \ {b1} := by simp [hmem1a, hne1]
      have hs := hmono hmemA2 hmemA1 ha
      simp only [slope_def_field] at hs
      have hL := ratio_swap (negEnt a2) (negEnt b1) a2 b1
      have hR := ratio_swap (negEnt a1) (negEnt b1) a1 b1
      unfold negEnt at hs hL hR ⊢
      linarith
    exact le_trans hstep2 hstep1

theorem telescope_range (n : ℕ) (c A : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, c i * (A (i + 1) - A i) =
      (if n = 0 then 0 else c (n - 1) * A n) -
        (if n = 0 then 0 else c 0 * A 0) -
        ∑ i ∈ Finset.range (n - 1), (c (i + 1) - c i) * A (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      cases n with
      | zero =>
          simp
          ring
      | succ m =>
          simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero _)]
          rw [Finset.sum_range_succ]
          ring

theorem abel_nonneg {n : ℕ} (c : Fin n → ℝ) (A : ℕ → ℝ)
    (hA0 : A 0 = 0) (hAn : A n = 0)
    (hAnti : ∀ i : ℕ, (hi : i + 1 < n) → c ⟨i + 1, hi⟩ ≤ c ⟨i, Nat.lt_of_succ_lt hi⟩)
    (hA : ∀ k, k ≤ n → 0 ≤ A k)
    (δ : Fin n → ℝ) (hδ : ∀ i, δ i = A (i.1 + 1) - A i.1) :
    0 ≤ ∑ i, c i * δ i := by
  by_cases hn : n = 0
  · subst hn
    simp
  · let cN : ℕ → ℝ := fun i => if h : i < n then c ⟨i, h⟩ else 0
    have hsum :
        ∑ i : Fin n, c i * δ i =
          ∑ i ∈ Finset.range n, cN i * (A (i + 1) - A i) := by
      rw [Finset.sum_fin_eq_sum_range]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i < n := Finset.mem_range.mp hi
      simp [cN, hi', hδ]
    rw [hsum, telescope_range]
    simp only [hn, ite_false, hA0, hAn, mul_zero, sub_zero, zero_sub, neg_neg]
    rw [neg_nonneg]
    apply Finset.sum_nonpos
    intro i hi
    have hi' : i + 1 < n := by
      have := Finset.mem_range.mp hi
      omega
    have hile : i < n := Nat.lt_of_succ_lt hi'
    have hc : cN (i + 1) ≤ cN i := by
      simp [cN, hi', hile, hAnti i hi']
    have hAk : 0 ≤ A (i + 1) := hA (i + 1) (by omega)
    exact mul_nonpos_of_nonpos_of_nonneg (by linarith) hAk

theorem psum_sub {n : ℕ} (x y : Fin n → ℝ) (k : ℕ) :
    psum (fun i => x i - y i) k = psum x k - psum y k := by
  unfold psum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i.1 < k <;> simp [h]

theorem psum_next {n : ℕ} (z : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    psum z (k + 1) = psum z k + z ⟨k, hk⟩ := by
  unfold psum
  have hsplit :
      ∑ i : Fin n, (if i.1 < k + 1 then z i else 0) =
        ∑ i, (if i.1 < k then z i else 0) +
          ∑ i, (if i.1 = k then z i else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hik : i.1 < k
    · simp [hik, Nat.lt_succ_of_lt hik, Nat.ne_of_lt hik]
    · by_cases he : i.1 = k
      · simp [he]
      · have hge : ¬ i.1 < k + 1 := by omega
        simp [hik, he, hge]
  rw [hsplit]
  congr 1
  have hpt : ∀ i : Fin n,
      (if i.1 = k then z i else 0) = if i = ⟨k, hk⟩ then z ⟨k, hk⟩ else 0 := by
    intro i
    by_cases he : i = ⟨k, hk⟩
    · simp [he]
    · have hne : i.1 ≠ k := by
        intro hv
        exact he (Fin.ext hv)
      simp [he, hne]
  simp_rw [hpt]
  have hflip : ∀ i : Fin n,
      (if i = ⟨k, hk⟩ then z ⟨k, hk⟩ else 0) = if ⟨k, hk⟩ = i then z i else 0 := by
    intro i
    by_cases he : i = ⟨k, hk⟩
    · simp [he]
    · have hne : ⟨k, hk⟩ ≠ i := Ne.symm he
      simp [he, hne]
  simp_rw [hflip]
  rw [Finset.sum_ite_eq]
  simp [hk]

def punch {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun j => z (p.succAbove j)

theorem succAbove_val_le {n : ℕ} (p : Fin (n + 1)) {j k : Fin n} (h : j.1 ≤ k.1) :
    (p.succAbove j).1 ≤ (p.succAbove k).1 := by
  unfold Fin.succAbove
  by_cases hj : j.castSucc < p <;> by_cases hk : k.castSucc < p
  · simp [hj, hk, Fin.val_castSucc, h]
  · simp [hj, hk, Fin.val_castSucc, Fin.val_succ]
    have hjv : j.1 < p.1 := by simpa [Fin.castSucc, Fin.lt_def] using hj
    have hkp : p.1 ≤ k.1 := by
      have hnk : ¬ k.1 < p.1 := by simpa [Fin.castSucc, Fin.lt_def] using hk
      omega
    omega
  · simp [hj, hk, Fin.val_castSucc, Fin.val_succ]
    have hjn : ¬ j.1 < p.1 := by simpa [Fin.castSucc, Fin.lt_def] using hj
    have hkv : k.1 < p.1 := by simpa [Fin.castSucc, Fin.lt_def] using hk
    omega
  · simp [hj, hk, Fin.val_succ, h]

theorem punch_antitone {n : ℕ} (p : Fin (n + 1)) {z : Fin (n + 1) → ℝ}
    (hz : ∀ i j : Fin (n + 1), i.1 ≤ j.1 → z j ≤ z i) :
    ∀ i j : Fin n, i.1 ≤ j.1 → punch p z j ≤ punch p z i := by
  intro i j hij
  exact hz _ _ (succAbove_val_le p hij)

theorem psum_punch {n : ℕ} (p : Fin (n + 1)) (z : Fin (n + 1) → ℝ) :
    ∀ k, psum (punch p z) k =
      if k ≤ p.1 then psum z k else psum z (k + 1) - z p := by
  intro k
  induction k with
  | zero =>
      simp [psum_zero]
  | succ k ih =>
      by_cases hk : k < n
      · have hpk : psum (punch p z) (k + 1) =
            psum (punch p z) k + z (p.succAbove ⟨k, hk⟩) :=
          psum_next (punch p z) hk
        rw [hpk, ih]
        by_cases hle : k ≤ p.1
        · by_cases hlt : k + 1 ≤ p.1
          · have hklt : k < p.1 := by omega
            have hidx : p.succAbove ⟨k, hk⟩ = ⟨k, Nat.lt_succ_of_lt hk⟩ := by
              have hcast : (⟨k, hk⟩ : Fin n).castSucc < p := by
                rw [Fin.lt_def]
                simpa [Fin.val_castSucc] using hklt
              rw [Fin.succAbove_of_castSucc_lt _ _ hcast]
              apply Fin.ext
              simp [Fin.val_castSucc]
            have hk' : k < n + 1 := Nat.lt_succ_of_lt hk
            have hstep := psum_next z hk'
            simp only [hle, hlt, ite_true, hidx, hstep]
          · have heq : k = p.1 := by omega
            have hk' : k < n + 1 := Nat.lt_succ_of_lt hk
            have hk2 : k + 1 < n + 1 := by omega
            have hidx : p.succAbove ⟨k, hk⟩ = ⟨k + 1, hk2⟩ := by
              have hltp : p < (⟨k, hk⟩ : Fin n).succ := by
                rw [Fin.lt_def]
                simpa [Fin.val_succ, heq] using Nat.lt_succ_self k
              rw [Fin.succAbove_of_lt_succ _ _ hltp]
              apply Fin.ext
              simp [Fin.val_succ]
            have hp : p = ⟨k, hk'⟩ := by
              apply Fin.ext
              simp [heq]
            have hstep := psum_next z hk'
            have hstep2 := psum_next z hk2
            rw [if_pos hle, if_neg hlt, hidx, hstep2, hstep, hp]
            ring
        · have hgt : ¬ k + 1 ≤ p.1 := by omega
          have hk' : k + 1 < n + 1 := by omega
          have hidx : p.succAbove ⟨k, hk⟩ = ⟨k + 1, hk'⟩ := by
            have hltp : p < (⟨k, hk⟩ : Fin n).succ := by
              rw [Fin.lt_def]
              simp [Fin.val_succ]
              omega
            rw [Fin.succAbove_of_lt_succ _ _ hltp]
            apply Fin.ext
            simp [Fin.val_succ]
          have hstep := psum_next z hk'
          simp only [hle, hgt, ite_false, hidx, hstep]
          ring
      · have hkge : n ≤ k := by omega
        rw [psum_of_ge _ (Nat.le_succ_of_le hkge)]
        have hgt : ¬ k + 1 ≤ p.1 := by
          have hp : p.1 < n + 1 := p.isLt
          omega
        simp only [hgt, ite_false]
        have hsump : ∑ j : Fin n, punch p z j = ∑ i, z i - z p := by
          have hsplit := Fin.sum_univ_succAbove z p
          simp only [punch] at hsplit ⊢
          linarith
        have htail : psum z (k + 1 + 1) = ∑ i, z i :=
          psum_of_ge _ (by omega)
        rw [hsump, htail]

/-- If `x` majorizes the nonnegative antitone vector `y`, entropy cannot fall. -/
theorem entTerm_le_of_majorized {n : ℕ} (x y : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hxA : ∀ i j : Fin n, i.1 ≤ j.1 → x j ≤ x i)
    (hyA : ∀ i j : Fin n, i.1 ≤ j.1 → y j ≤ y i)
    (hpart : ∀ k, psum y k ≤ psum x k)
    (hsum : ∑ i, x i = ∑ i, y i) :
    ∑ i, entTerm (x i) ≤ ∑ i, entTerm (y i) := by
  have hneg : ∑ i, negEnt (y i) ≤ ∑ i, negEnt (x i) := by
    induction n using Nat.strongRecOn with
    | ind n ih =>
      by_cases hEq : ∃ i, x i = y i
      · obtain ⟨p, hp⟩ := hEq
        have hn : n ≠ 0 := by
          intro hn0
          subst hn0
          exact Fin.elim0 p
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
        let x' := punch p x
        let y' := punch p y
        have hx' : ∀ i, 0 ≤ x' i := fun i => hx _
        have hy' : ∀ i, 0 ≤ y' i := fun i => hy _
        have hxA' := punch_antitone p hxA
        have hyA' := punch_antitone p hyA
        have hsum' : ∑ i, x' i = ∑ i, y' i := by
          have hxsum := Fin.sum_univ_succAbove (fun i => x i) p
          have hysum := Fin.sum_univ_succAbove (fun i => y i) p
          simp only [punch, x', y'] at hxsum hysum ⊢
          linarith [hsum, hp]
        have hpart' : ∀ k, psum y' k ≤ psum x' k := by
          intro k
          have hxpu := psum_punch p x k
          have hypu := psum_punch p y k
          simp only [x', y'] at hxpu hypu ⊢
          rw [hxpu, hypu, hp]
          by_cases hk : k ≤ p.1
          · simp [hk, hpart k]
          · simp [hk]
            have hdiff := hpart (k + 1)
            linarith
        have hIH := ih m (Nat.lt_succ_self m) x' y' hx' hy' hxA' hyA' hpart' hsum'
        have hxadd := Fin.sum_univ_succAbove (fun i => negEnt (x i)) p
        have hyadd := Fin.sum_univ_succAbove (fun i => negEnt (y i)) p
        simp only [punch, x', y'] at hIH hxadd hyadd
        have hpe : negEnt (x p) = negEnt (y p) := by simp [hp]
        linarith
      · push Not at hEq
        by_cases hn : n = 0
        · subst hn
          simp
        · let A : ℕ → ℝ := fun k => psum (fun i => x i - y i) k
          let c : Fin n → ℝ := fun i => negSlope (x i) (y i)
          let δ : Fin n → ℝ := fun i => x i - y i
          have hA0 : A 0 = 0 := by simp [A, psum_zero]
          have hAn : A n = 0 := by
            simp [A, psum_of_ge _ (le_refl n), psum_sub, hsum]
          have hAnti : ∀ i : ℕ, (hi : i + 1 < n) →
              c ⟨i + 1, hi⟩ ≤ c ⟨i, Nat.lt_of_succ_lt hi⟩ := by
            intro i hi
            have hi0 : i < n := Nat.lt_of_succ_lt hi
            exact negSlope_mono (hx _) (hy _) (hx _) (hy _)
              (hxA ⟨i, hi0⟩ ⟨i + 1, hi⟩ (by simp))
              (hyA ⟨i, hi0⟩ ⟨i + 1, hi⟩ (by simp))
              (hEq _) (hEq _)
          have hA : ∀ k, k ≤ n → 0 ≤ A k := by
            intro k hk
            have hdiff : 0 ≤ psum x k - psum y k := by linarith [hpart k]
            simpa [A, psum_sub] using hdiff
          have hδ : ∀ i, δ i = A (i.1 + 1) - A i.1 := by
            intro i
            have hstep := psum_next (fun j => x j - y j) i.isLt
            simp [A, δ, hstep]
          have hAbel := abel_nonneg c A hA0 hAn hAnti hA δ hδ
          have hterm : ∀ i, c i * δ i = negEnt (x i) - negEnt (y i) := by
            intro i
            have hne := hEq i
            simp only [c, δ]
            rw [negSlope_eq hne]
            field_simp [sub_ne_zero.mpr hne]
          have hsumδ : ∑ i, c i * δ i = ∑ i, negEnt (x i) - ∑ i, negEnt (y i) := by
            simp_rw [hterm, Finset.sum_sub_distrib]
          linarith
  simpa [negEnt, Finset.sum_neg_distrib] using hneg

/-! ## The recorded witness tree

Root output `X` has mass `4/9` on `0`. Each child has two actions and a binary
output. Policies are pairs `(a₀, a₁)`.
-/

def quadK (a b c d : ℝ) (act y : Fin 2) : ℝ :=
  match act, y with
  | 0, 0 => a
  | 0, 1 => b
  | 1, 0 => c
  | 1, 1 => d

theorem quadK_pos {a b c d : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (act y : Fin 2) : 0 < quadK a b c d act y := by
  fin_cases act <;> fin_cases y <;> simp [quadK, ha, hb, hc, hd]

theorem quadK_sum {a b c d : ℝ} (hab : a + b = 1) (hcd : c + d = 1) (act : Fin 2) :
    ∑ y : Fin 2, quadK a b c d act y = 1 := by
  fin_cases act <;> simp [quadK, Fin.sum_univ_two, hab, hcd]

abbrev wLeafTree : Tree := .leaf

abbrev branch0 : Tree :=
  .node 2 (Nat.succ_pos 1) (fun _ => 2) (fun _ => Nat.succ_pos 1)
    (quadK (3 / 4) (1 / 4) (1 / 2) (1 / 2))
    (quadK_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (quadK_sum (by norm_num) (by norm_num))
    (fun _ _ => wLeafTree)

abbrev branch1 : Tree :=
  .node 2 (Nat.succ_pos 1) (fun _ => 2) (fun _ => Nat.succ_pos 1)
    (quadK (3 / 5) (2 / 5) (4 / 5) (1 / 5))
    (quadK_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num))
    (quadK_sum (by norm_num) (by norm_num))
    (fun _ _ => wLeafTree)

def rootK : Fin 1 → Fin 2 → ℝ := fun _ y => if y = 0 then (4 : ℝ) / 9 else 5 / 9

theorem rootK_pos (a : Fin 1) (y : Fin 2) : 0 < rootK a y := by
  fin_cases y <;> simp [rootK] <;> norm_num

theorem rootK_sum (a : Fin 1) : ∑ y : Fin 2, rootK a y = 1 := by
  simp [rootK, Fin.sum_univ_two]
  norm_num

abbrev witnessTree : Tree :=
  .node 1 (Nat.succ_pos 0) (fun _ => 2) (fun _ => Nat.succ_pos 1)
    rootK rootK_pos rootK_sum
    (fun _ y => match y with | 0 => branch0 | 1 => branch1)

def wPol (a0 a1 : Fin 2) : Policy witnessTree :=
  ⟨0, fun _ y =>
    match y with
    | 0 => ⟨a0, fun _ _ => PUnit.unit⟩
    | 1 => ⟨a1, fun _ _ => PUnit.unit⟩⟩

def actAt (π : Policy witnessTree) (x : Fin 2) : Fin 2 :=
  match x with
  | 0 => (π.2 0 0).1
  | 1 => (π.2 0 1).1

theorem wRoot (π : Policy witnessTree) : π.1 = 0 :=
  Subsingleton.elim _ _

def wLeafOf (x act y : Fin 2) : Leaf witnessTree :=
  ⟨0, x, match x with
    | 0 => ⟨act, y, PUnit.unit⟩
    | 1 => ⟨act, y, PUnit.unit⟩⟩

def leafX (ℓ : Leaf witnessTree) : Fin 2 := ℓ.2.1

def leafY (ℓ : Leaf witnessTree) : Fin 2 :=
  match ℓ with
  | ⟨_, 0, ⟨_, y, _⟩⟩ => y
  | ⟨_, 1, ⟨_, y, _⟩⟩ => y

def leafAct (ℓ : Leaf witnessTree) : Fin 2 :=
  match ℓ with
  | ⟨_, 0, ⟨act, _, _⟩⟩ => act
  | ⟨_, 1, ⟨act, _, _⟩⟩ => act

theorem leafX_wLeaf (x act y : Fin 2) : leafX (wLeafOf x act y) = x := by
  fin_cases x <;> simp [leafX, wLeafOf]

theorem leafY_wLeaf (x act y : Fin 2) : leafY (wLeafOf x act y) = y := by
  fin_cases x <;> fin_cases y <;> simp [leafY, wLeafOf]

theorem leafAct_wLeaf (x act y : Fin 2) : leafAct (wLeafOf x act y) = act := by
  fin_cases x <;> simp [leafAct, wLeafOf]

theorem wLeafOf_inj (x act y x' act' y' : Fin 2) :
    wLeafOf x act y = wLeafOf x' act' y' ↔ x = x' ∧ act = act' ∧ y = y' := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa [leafX_wLeaf] using congrArg leafX h
    · simpa [leafAct_wLeaf] using congrArg leafAct h
    · simpa [leafY_wLeaf] using congrArg leafY h
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem leaf_of_compat (π : Policy witnessTree) (ℓ : Leaf witnessTree)
    (hc : CompatiblePolicy ℓ π) :
    ℓ = wLeafOf (leafX ℓ) (actAt π (leafX ℓ)) (leafY ℓ) := by
  match ℓ with
  | ⟨a, x, sub⟩ =>
      fin_cases a
      fin_cases x
      · match sub with
        | ⟨act, y, u⟩ =>
            cases u
            have hact : act = actAt π 0 := by
              simp only [CompatiblePolicy] at hc
              simpa [actAt] using hc.2.1
            subst hact
            rfl
      · match sub with
        | ⟨act, y, u⟩ =>
            cases u
            have hact : act = actAt π 1 := by
              simp only [CompatiblePolicy] at hc
              simpa [actAt] using hc.2.1
            subst hact
            rfl

theorem leaf_compat (π : Policy witnessTree) (x y : Fin 2) :
    CompatiblePolicy (wLeafOf x (actAt π x) y) π := by
  fin_cases x <;> fin_cases y <;>
    simp [CompatiblePolicy, wLeafOf, actAt, wRoot]

def sym (x y : Fin 2) : Fin 4 := ⟨x.1 * 2 + y.1, by omega⟩

def sx (s : Fin 4) : Fin 2 := ⟨s.1 / 2, by omega⟩

def sy (s : Fin 4) : Fin 2 := ⟨s.1 % 2, by omega⟩

theorem sx_sym (x y : Fin 2) : sx (sym x y) = x := by
  fin_cases x <;> fin_cases y <;> apply Fin.ext <;> simp [sx, sym]

theorem sy_sym (x y : Fin 2) : sy (sym x y) = y := by
  fin_cases x <;> fin_cases y <;> apply Fin.ext <;> simp [sx, sy, sym]

def pIdx (a0 a1 : Fin 2) : Fin 4 := ⟨a0.1 * 2 + a1.1, by omega⟩

theorem pIdx_sx (j : Fin 4) : pIdx (sx j) (sy j) = j := by
  fin_cases j <;> apply Fin.ext <;> simp [pIdx, sx, sy]

def assignOf (f : Fin 4 → Fin 4) : Assignment witnessTree :=
  fun π =>
    let s := f (pIdx (actAt π 0) (actAt π 1))
    ⟨wLeafOf (sx s) (actAt π (sx s)) (sy s), leaf_compat π (sx s) (sy s)⟩

/-- Columns of the ordinary decoder, rows ordered `00, 01, 10, 11`. -/
def colSym : Fin 5 → Fin 4 → Fin 4
  | 0, 0 => 0
  | 0, 1 => 0
  | 0, 2 => 2
  | 0, 3 => 2
  | 1, 0 => 2
  | 1, 1 => 2
  | 1, 2 => 0
  | 1, 3 => 0
  | 2, 0 => 3
  | 2, 1 => 2
  | 2, 2 => 1
  | 2, 3 => 1
  | 3, 0 => 2
  | 3, 1 => 1
  | 3, 2 => 3
  | 3, 3 => 2
  | 4, 0 => 1
  | 4, 1 => 3
  | 4, 2 => 3
  | 4, 3 => 3

def wgt : Fin 5 → ℝ
  | 0 => 3 / 9
  | 1 => 2 / 9
  | 2 => 2 / 9
  | 3 => 1 / 9
  | 4 => 1 / 9

theorem sum_fin5 (f : Fin 5 → ℝ) :
    ∑ i, f i = f 0 + f 1 + f 2 + f 3 + f 4 := by
  simp [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  abel

theorem wgt_nonneg (i : Fin 5) : 0 ≤ wgt i := by
  fin_cases i <;> simp [wgt] <;> norm_num

theorem wgt_sum : ∑ i : Fin 5, wgt i = 1 := by
  simp [sum_fin5, wgt]
  norm_num

theorem wgt_entropy :
    ∑ i : Fin 5, entTerm (wgt i) =
      entTerm ((3 : ℝ) / 9) + 2 * entTerm ((2 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) := by
  simp [sum_fin5, wgt]
  ring

noncomputable abbrev ordMass (α : Assignment witnessTree) : ℝ :=
  ∑ i : Fin 5, if assignOf (colSym i) = α then wgt i else 0

theorem ordMass_nonneg (α : Assignment witnessTree) : 0 ≤ ordMass α := by
  unfold ordMass
  apply Finset.sum_nonneg
  intro i _
  by_cases h : assignOf (colSym i) = α <;> simp [h, wgt_nonneg]

theorem sum_point (a : Assignment witnessTree) (c : ℝ) :
    ∑ α, (if a = α then c else 0) = c := by
  have hflip : ∀ α, (if a = α then c else (0 : ℝ)) =
      if α = a then (fun _ => c) α else 0 := by
    intro α
    by_cases h : a = α
    · simp [h]
    · simp [h, Ne.symm h]
  simp_rw [hflip]
  rw [Finset.sum_ite_eq']
  simp

theorem ordMass_total : ∑ α, ordMass α = 1 := by
  simp only [ordMass, sum_fin5, Finset.sum_add_distrib, sum_point]
  rw [← sum_fin5]
  exact wgt_sum

theorem column_marginal (π : Policy witnessTree) (ℓ : Leaf witnessTree) (i : Fin 5) :
    ∑ α, (if (α π).1 = ℓ then (if assignOf (colSym i) = α then wgt i else 0) else 0) =
      if ((assignOf (colSym i)) π).1 = ℓ then wgt i else 0 := by
  have hfun : ∀ α,
      (if (α π).1 = ℓ then (if assignOf (colSym i) = α then wgt i else (0 : ℝ)) else 0) =
        if assignOf (colSym i) = α then
          (if ((assignOf (colSym i)) π).1 = ℓ then wgt i else 0) else 0 := by
    intro α
    by_cases ha : assignOf (colSym i) = α
    · subst ha
      simp
    · simp [ha]
  simp_rw [hfun, sum_point]

theorem ord_marginal_sum (π : Policy witnessTree) (ℓ : Leaf witnessTree) :
    ∑ α, (if (α π).1 = ℓ then ordMass α else 0) =
      ∑ i : Fin 5, if ((assignOf (colSym i)) π).1 = ℓ then wgt i else 0 := by
  have hpush : ∀ α,
      (if (α π).1 = ℓ then ordMass α else 0) =
        ∑ i : Fin 5,
          if (α π).1 = ℓ then (if assignOf (colSym i) = α then wgt i else 0) else 0 := by
    intro α
    by_cases h : (α π).1 = ℓ
    · simp [h, ordMass, sum_fin5]
    · simp [h, sum_fin5]
  simp_rw [hpush, sum_fin5, Finset.sum_add_distrib, column_marginal]


theorem assign_leaf (f : Fin 4 → Fin 4) (π : Policy witnessTree) :
    ((assignOf f) π).1 =
      wLeafOf (sx (f (pIdx (actAt π 0) (actAt π 1))))
        (actAt π (sx (f (pIdx (actAt π 0) (actAt π 1)))))
        (sy (f (pIdx (actAt π 0) (actAt π 1)))) := rfl

theorem leafMass_quad (x act y : Fin 2) :
    leafMass (wLeafOf x act y) =
      (if x = 0 then (4 : ℝ) / 9 else 5 / 9) *
        quadK (if x = 0 then 3 / 4 else 3 / 5) (if x = 0 then 1 / 4 else 2 / 5)
          (if x = 0 then 1 / 2 else 4 / 5) (if x = 0 then 1 / 2 else 1 / 5) act y := by
  fin_cases x <;> fin_cases act <;> fin_cases y <;>
    simp [wLeafOf, leafMass, rootK, quadK, branch0, branch1]

/-- Ninths carried by each policy/symbol of the five columns. -/
theorem col_ninth (a0 a1 x y : Fin 2) :
    (∑ i : Fin 5, if colSym i (pIdx a0 a1) = sym x y then wgt i else 0) =
      leafMass (wLeafOf x (if x = 0 then a0 else a1) y) := by
  fin_cases a0 <;> fin_cases a1 <;> fin_cases x <;> fin_cases y <;>
    simp [colSym, wgt, pIdx, sym, sum_fin5, leafMass_quad, quadK] <;>
    norm_num

theorem sym_parts (s : Fin 4) : sym (sx s) (sy s) = s := by
  fin_cases s <;> apply Fin.ext <;> simp [sym, sx, sy]

theorem actAt_branch (π : Policy witnessTree) (x : Fin 2) :
    actAt π x = if x = 0 then actAt π 0 else actAt π 1 := by
  fin_cases x <;> simp [actAt]

theorem ord_hit (π : Policy witnessTree) (x y : Fin 2) :
    (∑ i : Fin 5,
        if ((assignOf (colSym i)) π).1 = wLeafOf x (actAt π x) y then wgt i else 0) =
      leafMass (wLeafOf x (actAt π x) y) := by
  have hfun : ∀ i : Fin 5,
      (((assignOf (colSym i)) π).1 = wLeafOf x (actAt π x) y) ↔
        colSym i (pIdx (actAt π 0) (actAt π 1)) = sym x y := by
    intro i
    rw [assign_leaf, wLeafOf_inj]
    constructor
    · rintro ⟨hx, hact, hy⟩
      have hsx : sx (colSym i (pIdx (actAt π 0) (actAt π 1))) = x := hx
      have hsy : sy (colSym i (pIdx (actAt π 0) (actAt π 1))) = y := hy
      rw [← sym_parts (colSym i (pIdx (actAt π 0) (actAt π 1))), hsx, hsy]
    · intro hs
      refine ⟨?_, ?_, ?_⟩
      · rw [hs, sx_sym]
      · rw [hs, sx_sym]
      · rw [hs, sy_sym]
  simp_rw [hfun]
  have hact : actAt π x = if x = 0 then actAt π 0 else actAt π 1 := actAt_branch π x
  rw [hact]
  exact col_ninth (actAt π 0) (actAt π 1) x y

theorem ord_marginal (π : Policy witnessTree) (ℓ : Leaf witnessTree)
    (hc : CompatiblePolicy ℓ π) :
    ∑ α, (if (α π).1 = ℓ then ordMass α else 0) = leafMass ℓ := by
  rw [ord_marginal_sum]
  have hℓ := leaf_of_compat π ℓ hc
  rw [hℓ]
  exact ord_hit π (leafX ℓ) (leafY ℓ)

noncomputable def ordCoupling : Coupling witnessTree where
  mass := ordMass
  nonneg := ordMass_nonneg
  total := ordMass_total
  marginal := ord_marginal

theorem colSym_inj (i j : Fin 5) (h : ∀ k, colSym i k = colSym j k) : i = j := by
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact False.elim (by simpa [colSym] using h 0)
    | exact False.elim (by simpa [colSym] using h 1)
    | exact False.elim (by simpa [colSym] using h 2)
    | exact False.elim (by simpa [colSym] using h 3)

theorem assign_sym (f : Fin 4 → Fin 4) (a0 a1 : Fin 2) :
    sym (leafX ((assignOf f) (wPol a0 a1)).1) (leafY ((assignOf f) (wPol a0 a1)).1) =
      f (pIdx a0 a1) := by
  have h0 : actAt (wPol a0 a1) 0 = a0 := by simp [actAt, wPol]
  have h1 : actAt (wPol a0 a1) 1 = a1 := by simp [actAt, wPol]
  rw [assign_leaf, leafX_wLeaf, leafY_wLeaf, h0, h1]
  exact sym_parts _

theorem cols_distinct (i j : Fin 5) (hij : i ≠ j) :
    assignOf (colSym i) ≠ assignOf (colSym j) := by
  intro heq
  apply hij
  apply colSym_inj
  intro k
  have hk : k = pIdx (sx k) (sy k) := (pIdx_sx k).symm
  rw [hk]
  have hi := assign_sym (colSym i) (sx k) (sy k)
  have hj := assign_sym (colSym j) (sx k) (sy k)
  rw [heq] at hi
  exact hi.symm.trans hj

theorem ord_entropy_eq :
    ordCoupling.entropy = ∑ i : Fin 5, entTerm (wgt i) := by
  unfold Coupling.entropy pmfEntropy ordCoupling ordMass
  have hmass : ∀ α : Assignment witnessTree,
      entTerm (∑ i : Fin 5, if assignOf (colSym i) = α then wgt i else 0) =
        ∑ i : Fin 5, if assignOf (colSym i) = α then entTerm (wgt i) else 0 := by
    intro α
    by_cases hex : ∃ i, assignOf (colSym i) = α
    · obtain ⟨j, hj⟩ := hex
      have huniq : ∀ i, assignOf (colSym i) = α ↔ i = j := by
        intro i
        constructor
        · intro hi
          by_contra hne
          exact cols_distinct i j hne (hi.trans hj.symm)
        · intro hi
          simpa [hi] using hj
      have hleft : (∑ i : Fin 5, if assignOf (colSym i) = α then wgt i else 0) = wgt j := by
        have hfun : ∀ i, (if assignOf (colSym i) = α then wgt i else 0) =
            if i = j then wgt i else 0 := by
          intro i
          by_cases hi : i = j
          · simp [hi, hj]
          · have hne : assignOf (colSym i) ≠ α := by
              intro he
              exact hi ((huniq i).1 he)
            simp [hi, hne]
        simp_rw [hfun]
        rw [Finset.sum_ite_eq']
        simp
      have hright : (∑ i : Fin 5, if assignOf (colSym i) = α then entTerm (wgt i) else 0) =
          entTerm (wgt j) := by
        have hfun : ∀ i, (if assignOf (colSym i) = α then entTerm (wgt i) else 0) =
            if i = j then entTerm (wgt i) else 0 := by
          intro i
          by_cases hi : i = j
          · simp [hi, hj]
          · have hne : assignOf (colSym i) ≠ α := by
              intro he
              exact hi ((huniq i).1 he)
            simp [hi, hne]
        simp_rw [hfun]
        rw [Finset.sum_ite_eq']
        simp
      rw [hleft, hright]
    · push Not at hex
      have hzero : (∑ i : Fin 5, if assignOf (colSym i) = α then wgt i else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [hex i]
      have hzero' : (∑ i : Fin 5, if assignOf (colSym i) = α then entTerm (wgt i) else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        simp [hex i]
      rw [hzero, hzero', entTerm_zero]
  simp_rw [hmass]
  simp only [sum_fin5, Finset.sum_add_distrib, sum_point]

theorem ordinaryMin_witness_le :
    ordinaryMin witnessTree ≤
      entTerm ((3 : ℝ) / 9) + 2 * entTerm ((2 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) := by
  have hle := ordinaryMin_le_entropy ordCoupling
  rw [ord_entropy_eq, wgt_entropy] at hle
  exact hle


/-! ## Causal assignments on the eight transcripts `(X, Z₀, Z₁)` -/

def cWord (x z0 z1 : Fin 2) : Fin 4 → Fin 4 :=
  fun j =>
    let a0 := sx j
    let a1 := sy j
    let y :=
      if x = 0 then (if a0 = 0 then z0 else z1) else (if a1 = 0 then z0 else z1)
    sym x y

def cAssign (x z0 z1 : Fin 2) : Assignment witnessTree :=
  assignOf (cWord x z0 z1)

theorem sym_inj {x y x' y' : Fin 2} : sym x y = sym x' y' ↔ x = x' ∧ y = y' := by
  constructor
  · intro h
    exact ⟨by simpa [sx_sym] using congrArg sx h, by simpa [sy_sym] using congrArg sy h⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem cWord_at (x z0 z1 : Fin 2) (a0 a1 : Fin 2) :
    cWord x z0 z1 (pIdx a0 a1) =
      sym x (if x = 0 then (if a0 = 0 then z0 else z1) else (if a1 = 0 then z0 else z1)) := by
  have hp : pIdx a0 a1 = sym a0 a1 := rfl
  simp [cWord, hp, sx_sym, sy_sym]

def cStrat (x z0 z1 : Fin 2) : Strategy witnessTree :=
  ⟨fun _ => x, fun _ y =>
    match y with
    | 0 => ⟨fun a => if x = 0 then (if a = 0 then z0 else z1) else 0, fun _ _ => PUnit.unit⟩
    | 1 => ⟨fun a => if x = 1 then (if a = 0 then z0 else z1) else 0, fun _ _ => PUnit.unit⟩⟩

def stratX (d : Strategy witnessTree) : Fin 2 := d.1 0

def stratZ (d : Strategy witnessTree) (a : Fin 2) : Fin 2 :=
  match stratX d with
  | 0 => (d.2 0 0).1 a
  | 1 => (d.2 0 1).1 a

theorem run_witness (d : Strategy witnessTree) (π : Policy witnessTree) :
    run d π = wLeafOf (stratX d) (actAt π (stratX d)) (stratZ d (actAt π (stratX d))) := by
  have hπ : π.1 = 0 := wRoot π
  have hr :
      run d π = ⟨π.1, d.1 π.1, run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))⟩ := by
    simp only [run, witnessTree]
    rfl
  rw [hr, hπ]
  match hxd : d.1 0 with
  | 0 =>
      simp [run, branch0, wLeafTree, stratX, stratZ, actAt, wLeafOf]
      rw [hxd]
  | 1 =>
      simp [run, branch1, wLeafTree, stratX, stratZ, actAt, wLeafOf]
      rw [hxd]

theorem stratX_cStrat (x z0 z1 : Fin 2) : stratX (cStrat x z0 z1) = x := by
  simp [stratX, cStrat]

theorem stratZ_cStrat (x z0 z1 a : Fin 2) :
    stratZ (cStrat x z0 z1) a = if a = 0 then z0 else z1 := by
  unfold stratZ stratX cStrat
  fin_cases x <;> fin_cases a <;> simp

theorem response_y (x a0 a1 z0 z1 : Fin 2) :
    (if x = 0 then (if a0 = 0 then z0 else z1) else (if a1 = 0 then z0 else z1)) =
      if (if x = 0 then a0 else a1) = 0 then z0 else z1 := by
  fin_cases x <;> fin_cases a0 <;> fin_cases a1 <;> rfl

theorem cAssign_leaf (x z0 z1 : Fin 2) (π : Policy witnessTree) :
    ((cAssign x z0 z1) π).1 =
      wLeafOf x (actAt π x) (if actAt π x = 0 then z0 else z1) := by
  rw [cAssign, assign_leaf, cWord_at, sx_sym, sy_sym]
  have hy := response_y x (actAt π 0) (actAt π 1) z0 z1
  rw [← actAt_branch π x] at hy
  rw [hy]

theorem realizes_cStrat (x z0 z1 : Fin 2) :
    realizes (cStrat x z0 z1) = cAssign x z0 z1 := by
  funext π
  apply Subtype.ext
  simp only [realizes]
  rw [run_witness, stratX_cStrat, stratZ_cStrat, cAssign_leaf]

theorem stratZ_if (d : Strategy witnessTree) (a : Fin 2) :
    stratZ d a = if a = 0 then stratZ d 0 else stratZ d 1 := by
  fin_cases a <;> rfl

theorem realizes_strat (d : Strategy witnessTree) :
    realizes d = cAssign (stratX d) (stratZ d 0) (stratZ d 1) := by
  funext π
  apply Subtype.ext
  simp only [realizes]
  rw [run_witness, cAssign_leaf, stratZ_if d (actAt π (stratX d))]

theorem cWord_00 (x z0 z1 : Fin 2) : cWord x z0 z1 (pIdx 0 0) = sym x z0 := by
  rw [cWord_at]
  fin_cases x <;> simp

theorem cWord_11 (x z0 z1 : Fin 2) : cWord x z0 z1 (pIdx 1 1) = sym x z1 := by
  rw [cWord_at]
  fin_cases x <;> simp

theorem cAssign_inj (x z0 z1 x' z0' z1' : Fin 2)
    (h : cAssign x z0 z1 = cAssign x' z0' z1') : x = x' ∧ z0 = z0' ∧ z1 = z1' := by
  have h0 := congrArg (fun α : Assignment witnessTree =>
    sym (leafX (α (wPol 0 0)).1) (leafY (α (wPol 0 0)).1)) h
  have h1 := congrArg (fun α : Assignment witnessTree =>
    sym (leafX (α (wPol 1 1)).1) (leafY (α (wPol 1 1)).1)) h
  simp only [cAssign, assign_sym, cWord_00, cWord_11] at h0 h1
  rw [sym_inj] at h0 h1
  exact ⟨h0.1, h0.2, h1.2⟩

theorem cAssign_eq_iff (x z0 z1 x' z0' z1' : Fin 2) :
    cAssign x z0 z1 = cAssign x' z0' z1' ↔ x = x' ∧ z0 = z0' ∧ z1 = z1' := by
  constructor
  · exact cAssign_inj x z0 z1 x' z0' z1'
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem cAssign_realizable (x z0 z1 : Fin 2) : realizable (cAssign x z0 z1) :=
  ⟨cStrat x z0 z1, realizes_cStrat x z0 z1⟩

theorem realizable_cAssign (α : Assignment witnessTree) :
    realizable α ↔ ∃ x z0 z1, cAssign x z0 z1 = α := by
  constructor
  · intro hr
    obtain ⟨d, hd⟩ := hr
    exact ⟨stratX d, stratZ d 0, stratZ d 1, by rw [← realizes_strat, hd]⟩
  · rintro ⟨x, z0, z1, rfl⟩
    exact cAssign_realizable x z0 z1

theorem mass_zero_of_not_realizable {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0)
    {α : Assignment witnessTree} (hr : ¬ realizable α) : Γ.mass α = 0 := by
  have hnn : ∀ β ∈ (Finset.univ : Finset (Assignment witnessTree)),
      0 ≤ (if realizable β then (0 : ℝ) else Γ.mass β) := by
    intro β _
    by_cases hb : realizable β <;> simp [hb, Γ.nonneg]
  have hle := Finset.single_le_sum hnn (Finset.mem_univ α)
  have hterm : (if realizable α then (0 : ℝ) else Γ.mass α) = Γ.mass α := by simp [hr]
  rw [hterm] at hle
  have hsum : ∑ β, (if realizable β then (0 : ℝ) else Γ.mass β) = 0 := by
    simpa [Coupling.badMass] using hbad
  linarith [Γ.nonneg α]

theorem mass_off_cells {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0)
    {α : Assignment witnessTree} (h : ∀ x z0 z1, cAssign x z0 z1 ≠ α) : Γ.mass α = 0 := by
  apply mass_zero_of_not_realizable hbad
  intro hr
  rcases (realizable_cAssign α).1 hr with ⟨x, z0, z1, hx⟩
  exact h x z0 z1 hx

def cell (Γ : Coupling witnessTree) (x z0 z1 : Fin 2) : ℝ :=
  Γ.mass (cAssign x z0 z1)

theorem cell_nonneg (Γ : Coupling witnessTree) (x z0 z1 : Fin 2) : 0 ≤ cell Γ x z0 z1 := by
  unfold cell
  exact Γ.nonneg _

set_option maxHeartbeats 2000000 in
theorem mass_eight {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) (α : Assignment witnessTree) :
    Γ.mass α =
      (if cAssign 0 0 0 = α then cell Γ 0 0 0 else 0) +
      (if cAssign 0 0 1 = α then cell Γ 0 0 1 else 0) +
      (if cAssign 0 1 0 = α then cell Γ 0 1 0 else 0) +
      (if cAssign 0 1 1 = α then cell Γ 0 1 1 else 0) +
      (if cAssign 1 0 0 = α then cell Γ 1 0 0 else 0) +
      (if cAssign 1 0 1 = α then cell Γ 1 0 1 else 0) +
      (if cAssign 1 1 0 = α then cell Γ 1 1 0 else 0) +
      (if cAssign 1 1 1 = α then cell Γ 1 1 1 else 0) := by
  by_cases hex : ∃ x z0 z1, cAssign x z0 z1 = α
  · rcases hex with ⟨x, z0, z1, rfl⟩
    simp only [cell]
    fin_cases x <;> fin_cases z0 <;> fin_cases z1 <;> simp [cAssign_eq_iff]
  · push Not at hex
    rw [mass_off_cells hbad hex]
    simp [hex 0 0 0, hex 0 0 1, hex 0 1 0, hex 0 1 1, hex 1 0 0, hex 1 0 1, hex 1 1 0, hex 1 1 1]

set_option maxHeartbeats 2000000 in
theorem margin_eight {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0)
    (π : Policy witnessTree) (ℓ : Leaf witnessTree) (hc : CompatiblePolicy ℓ π) :
    (if ((cAssign 0 0 0) π).1 = ℓ then cell Γ 0 0 0 else 0) +
        (if ((cAssign 0 0 1) π).1 = ℓ then cell Γ 0 0 1 else 0) +
        (if ((cAssign 0 1 0) π).1 = ℓ then cell Γ 0 1 0 else 0) +
        (if ((cAssign 0 1 1) π).1 = ℓ then cell Γ 0 1 1 else 0) +
        (if ((cAssign 1 0 0) π).1 = ℓ then cell Γ 1 0 0 else 0) +
        (if ((cAssign 1 0 1) π).1 = ℓ then cell Γ 1 0 1 else 0) +
        (if ((cAssign 1 1 0) π).1 = ℓ then cell Γ 1 1 0 else 0) +
        (if ((cAssign 1 1 1) π).1 = ℓ then cell Γ 1 1 1 else 0) =
      leafMass ℓ := by
  rw [← Γ.marginal π ℓ hc]
  have hterm : ∀ (α β : Assignment witnessTree) (v : ℝ),
      (if (α π).1 = ℓ then if β = α then v else (0 : ℝ) else 0) =
        if β = α then if (β π).1 = ℓ then v else 0 else 0 := by
    intro α β v
    by_cases hb : β = α
    · subst hb
      simp
    · simp [hb]
  have hsplit (p : Prop) [Decidable p] (t1 t2 t3 t4 t5 t6 t7 t8 : ℝ) :
      (if p then t1 + t2 + t3 + t4 + t5 + t6 + t7 + t8 else 0) =
        (if p then t1 else 0) + (if p then t2 else 0) + (if p then t3 else 0) +
          (if p then t4 else 0) + (if p then t5 else 0) + (if p then t6 else 0) +
          (if p then t7 else 0) + (if p then t8 else 0) := by
    by_cases hp : p <;> simp [hp]
  have hpush : ∀ α,
      (if (α π).1 = ℓ then Γ.mass α else 0) =
        (if cAssign 0 0 0 = α then if ((cAssign 0 0 0) π).1 = ℓ then cell Γ 0 0 0 else 0 else 0) +
        (if cAssign 0 0 1 = α then if ((cAssign 0 0 1) π).1 = ℓ then cell Γ 0 0 1 else 0 else 0) +
        (if cAssign 0 1 0 = α then if ((cAssign 0 1 0) π).1 = ℓ then cell Γ 0 1 0 else 0 else 0) +
        (if cAssign 0 1 1 = α then if ((cAssign 0 1 1) π).1 = ℓ then cell Γ 0 1 1 else 0 else 0) +
        (if cAssign 1 0 0 = α then if ((cAssign 1 0 0) π).1 = ℓ then cell Γ 1 0 0 else 0 else 0) +
        (if cAssign 1 0 1 = α then if ((cAssign 1 0 1) π).1 = ℓ then cell Γ 1 0 1 else 0 else 0) +
        (if cAssign 1 1 0 = α then if ((cAssign 1 1 0) π).1 = ℓ then cell Γ 1 1 0 else 0 else 0) +
        (if cAssign 1 1 1 = α then if ((cAssign 1 1 1) π).1 = ℓ then cell Γ 1 1 1 else 0 else 0) := by
    intro α
    rw [mass_eight hbad α, hsplit]
    rw [hterm α (cAssign 0 0 0) (cell Γ 0 0 0), hterm α (cAssign 0 0 1) (cell Γ 0 0 1),
      hterm α (cAssign 0 1 0) (cell Γ 0 1 0), hterm α (cAssign 0 1 1) (cell Γ 0 1 1),
      hterm α (cAssign 1 0 0) (cell Γ 1 0 0), hterm α (cAssign 1 0 1) (cell Γ 1 0 1),
      hterm α (cAssign 1 1 0) (cell Γ 1 1 0), hterm α (cAssign 1 1 1) (cell Γ 1 1 1)]
  simp_rw [hpush, Finset.sum_add_distrib, sum_point]

theorem leaf000 : leafMass (wLeafOf 0 0 0) = (3 : ℝ) / 9 := by
  simp [leafMass_quad, quadK]

theorem leaf001 : leafMass (wLeafOf 0 0 1) = (1 : ℝ) / 9 := by
  simp only [leafMass_quad, quadK]; norm_num

theorem leaf010 : leafMass (wLeafOf 0 1 0) = (2 : ℝ) / 9 := by
  simp only [leafMass_quad, quadK]; norm_num

theorem leaf011 : leafMass (wLeafOf 0 1 1) = (2 : ℝ) / 9 := by
  simp only [leafMass_quad, quadK]; norm_num

theorem leaf100 : leafMass (wLeafOf 1 0 0) = (3 : ℝ) / 9 := by
  simp [leafMass_quad, quadK]

theorem leaf101 : leafMass (wLeafOf 1 0 1) = (2 : ℝ) / 9 := by
  simp [leafMass_quad, quadK]

theorem leaf110 : leafMass (wLeafOf 1 1 0) = (4 : ℝ) / 9 := by
  simp [leafMass_quad, quadK]

theorem leaf111 : leafMass (wLeafOf 1 1 1) = (1 : ℝ) / 9 := by
  simp only [leafMass_quad, quadK]; norm_num

theorem cLeaf00 (x z0 z1 : Fin 2) :
    ((cAssign x z0 z1) (wPol 0 0)).1 = wLeafOf x 0 z0 := by
  rw [cAssign_leaf]
  have h0 : actAt (wPol 0 0) x = 0 := by fin_cases x <;> simp [actAt, wPol]
  simp [h0]

theorem cLeaf11 (x z0 z1 : Fin 2) :
    ((cAssign x z0 z1) (wPol 1 1)).1 = wLeafOf x 1 z1 := by
  rw [cAssign_leaf]
  have h1 : actAt (wPol 1 1) x = 1 := by fin_cases x <;> simp [actAt, wPol]
  simp [h1]

set_option maxHeartbeats 2000000 in
theorem cells_act0 {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) (x y : Fin 2) :
    cell Γ x y 0 + cell Γ x y 1 = leafMass (wLeafOf x 0 y) := by
  have hact : actAt (wPol 0 0) x = 0 := by
    fin_cases x <;> simp [actAt, wPol]
  have hc : CompatiblePolicy (wLeafOf x 0 y) (wPol 0 0) := by
    simpa [hact] using leaf_compat (wPol 0 0) x y
  have hm := margin_eight hbad (wPol 0 0) (wLeafOf x 0 y) hc
  rw [← hm]
  simp_rw [cLeaf00]
  fin_cases x <;> fin_cases y <;> simp [wLeafOf_inj]

set_option maxHeartbeats 2000000 in
theorem cells_act1 {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) (x y : Fin 2) :
    cell Γ x 0 y + cell Γ x 1 y = leafMass (wLeafOf x 1 y) := by
  have hact : actAt (wPol 1 1) x = 1 := by
    fin_cases x <;> simp [actAt, wPol]
  have hc : CompatiblePolicy (wLeafOf x 1 y) (wPol 1 1) := by
    simpa [hact] using leaf_compat (wPol 1 1) x y
  have hm := margin_eight hbad (wPol 1 1) (wLeafOf x 1 y) hc
  rw [← hm]
  simp_rw [cLeaf11]
  fin_cases x <;> fin_cases y <;> simp [wLeafOf_inj]

set_option maxHeartbeats 2000000 in
theorem entTerm_eight {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) (α : Assignment witnessTree) :
    entTerm (Γ.mass α) =
      (if cAssign 0 0 0 = α then entTerm (cell Γ 0 0 0) else 0) +
      (if cAssign 0 0 1 = α then entTerm (cell Γ 0 0 1) else 0) +
      (if cAssign 0 1 0 = α then entTerm (cell Γ 0 1 0) else 0) +
      (if cAssign 0 1 1 = α then entTerm (cell Γ 0 1 1) else 0) +
      (if cAssign 1 0 0 = α then entTerm (cell Γ 1 0 0) else 0) +
      (if cAssign 1 0 1 = α then entTerm (cell Γ 1 0 1) else 0) +
      (if cAssign 1 1 0 = α then entTerm (cell Γ 1 1 0) else 0) +
      (if cAssign 1 1 1 = α then entTerm (cell Γ 1 1 1) else 0) := by
  by_cases hex : ∃ x z0 z1, cAssign x z0 z1 = α
  · rcases hex with ⟨x, z0, z1, rfl⟩
    have hm : Γ.mass (cAssign x z0 z1) = cell Γ x z0 z1 := rfl
    rw [hm]
    fin_cases x <;> fin_cases z0 <;> fin_cases z1 <;> simp [cAssign_eq_iff, cell]
  · push Not at hex
    rw [mass_off_cells hbad hex, entTerm_zero]
    simp [hex 0 0 0, hex 0 0 1, hex 0 1 0, hex 0 1 1, hex 1 0 0, hex 1 0 1, hex 1 1 0, hex 1 1 1]

theorem entropy_eq_cells {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) :
    Γ.entropy =
      entTerm (cell Γ 0 0 0) + entTerm (cell Γ 0 0 1) + entTerm (cell Γ 0 1 0) +
        entTerm (cell Γ 0 1 1) + entTerm (cell Γ 1 0 0) + entTerm (cell Γ 1 0 1) +
        entTerm (cell Γ 1 1 0) + entTerm (cell Γ 1 1 1) := by
  unfold Coupling.entropy pmfEntropy
  simp_rw [entTerm_eight hbad, Finset.sum_add_distrib, sum_point]

theorem entTerm_chord {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * entTerm a + t * entTerm b ≤ entTerm ((1 - t) * a + t * b) := by
  have h := concaveOn_entTerm.2 ha hb (by linarith : 0 ≤ 1 - t) ht0 (by ring : (1 - t) + t = 1)
  simpa [smul_eq_mul] using h

theorem entTerm_pos_formula {w : ℝ} (hw : 0 < w) : entTerm w = w * Real.logb 2 (1 / w) := by
  rw [entTerm_of_pos hw]
  unfold infoMass
  have hlog : Real.logb 2 w = -Real.logb 2 (1 / w) := by
    rw [Real.logb_div (by norm_num) (ne_of_gt hw), Real.logb_one]
    ring
  rw [hlog]
  ring

theorem branch_gap_pos :
    0 ≤ 2 * entTerm ((2 : ℝ) / 9) + entTerm ((1 : ℝ) / 9) -
      (entTerm ((1 : ℝ) / 3) + 2 * entTerm ((1 : ℝ) / 9)) := by
  rw [entTerm_pos_formula (by norm_num : (0 : ℝ) < 2 / 9),
    entTerm_pos_formula (by norm_num : (0 : ℝ) < 1 / 9),
    entTerm_pos_formula (by norm_num : (0 : ℝ) < 1 / 3)]
  have e2 : (1 : ℝ) / ((2 : ℝ) / 9) = 9 / 2 := by norm_num
  have e1 : (1 : ℝ) / ((1 : ℝ) / 9) = 9 := by norm_num
  have e3 : (1 : ℝ) / ((1 : ℝ) / 3) = 3 := by norm_num
  rw [e2, e1, e3]
  have h4 : (4 : ℝ) * Real.logb 2 ((9 : ℝ) / 2) = Real.logb 2 (((9 : ℝ) / 2) ^ (4 : ℕ)) := by
    have hnat : (4 : ℝ) * Real.logb 2 ((9 : ℝ) / 2) = (4 : ℕ) * Real.logb 2 ((9 : ℝ) / 2) := by
      norm_num
    rw [hnat, ← Real.logb_pow]
  have h3 : (3 : ℝ) * Real.logb 2 3 = Real.logb 2 (3 ^ (3 : ℕ)) := by
    have hnat : (3 : ℝ) * Real.logb 2 3 = (3 : ℕ) * Real.logb 2 3 := by norm_num
    rw [hnat, ← Real.logb_pow]
  calc
    2 * (2 / 9 * Real.logb 2 ((9 : ℝ) / 2)) + 1 / 9 * Real.logb 2 9 -
          (1 / 3 * Real.logb 2 3 + 2 * (1 / 9 * Real.logb 2 9))
        = (1 / 9) * (4 * Real.logb 2 ((9 : ℝ) / 2) - 3 * Real.logb 2 3 - Real.logb 2 9) := by ring
    _ = (1 / 9) * (Real.logb 2 (((9 : ℝ) / 2) ^ 4) - Real.logb 2 (3 ^ 3) - Real.logb 2 9) := by
          rw [h4, h3]
    _ = (1 / 9) * Real.logb 2 (((((9 : ℝ) / 2) ^ 4) / (3 ^ 3)) / 9) := by
          rw [← Real.logb_div (by norm_num) (by norm_num), ← Real.logb_div (by norm_num) (by norm_num)]
    _ = (1 / 9) * Real.logb 2 ((27 : ℝ) / 16) := by norm_num
    _ ≥ 0 := mul_nonneg (by norm_num) (Real.logb_nonneg (by norm_num) (by norm_num))

theorem profile_gap_eq :
    (entTerm ((3 : ℝ) / 9) + entTerm ((2 : ℝ) / 9) + 4 * entTerm ((1 : ℝ) / 9)) -
        (entTerm ((3 : ℝ) / 9) + 2 * entTerm ((2 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9)) =
      (2 : ℝ) / 9 := by
  have hdiff :
      (entTerm ((3 : ℝ) / 9) + entTerm ((2 : ℝ) / 9) + 4 * entTerm ((1 : ℝ) / 9)) -
          (entTerm ((3 : ℝ) / 9) + 2 * entTerm ((2 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9)) =
        2 * entTerm ((1 : ℝ) / 9) - entTerm ((2 : ℝ) / 9) := by ring
  rw [hdiff, entTerm_pos_formula (by norm_num : (0 : ℝ) < 1 / 9),
    entTerm_pos_formula (by norm_num : (0 : ℝ) < 2 / 9)]
  have e1 : (1 : ℝ) / ((1 : ℝ) / 9) = 9 := by norm_num
  have e2 : (1 : ℝ) / ((2 : ℝ) / 9) = 9 / 2 := by norm_num
  rw [e1, e2]
  have hlog : Real.logb 2 (9 : ℝ) - Real.logb 2 ((9 : ℝ) / 2) = Real.logb 2 2 := by
    rw [← Real.logb_div (by norm_num) (by norm_num)]
    norm_num
  have hself : Real.logb 2 2 = 1 := Real.logb_self_eq_one (by norm_num)
  have hmain :
      2 * ((1 / 9) * Real.logb 2 (9 : ℝ)) - (2 / 9) * Real.logb 2 ((9 : ℝ) / 2) =
        (2 / 9) * (Real.logb 2 (9 : ℝ) - Real.logb 2 ((9 : ℝ) / 2)) := by ring
  rw [hmain, hlog, hself]
  ring

theorem branch0_ge {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) :
    entTerm ((2 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) ≤
      entTerm (cell Γ 0 0 0) + entTerm (cell Γ 0 0 1) + entTerm (cell Γ 0 1 0) +
        entTerm (cell Γ 0 1 1) := by
  have e00 : cell Γ 0 0 0 + cell Γ 0 0 1 = 3 / 9 := by rw [cells_act0 hbad 0 0, leaf000]
  have e01 : cell Γ 0 1 0 + cell Γ 0 1 1 = 1 / 9 := by rw [cells_act0 hbad 0 1, leaf001]
  have e10 : cell Γ 0 0 0 + cell Γ 0 1 0 = 2 / 9 := by rw [cells_act1 hbad 0 0, leaf010]
  have e11 : cell Γ 0 0 1 + cell Γ 0 1 1 = 2 / 9 := by rw [cells_act1 hbad 0 1, leaf011]
  set t := cell Γ 0 1 1 with _ht
  have h10 : cell Γ 0 1 0 = 1 / 9 - t := by linarith
  have h01 : cell Γ 0 0 1 = 2 / 9 - t := by linarith
  have h00 : cell Γ 0 0 0 = 1 / 9 + t := by linarith
  have ht0 : 0 ≤ t := by
    rw [show t = cell Γ 0 1 1 from rfl]
    exact cell_nonneg Γ 0 1 1
  have ht1 : t ≤ 1 / 9 := by linarith [cell_nonneg Γ 0 1 0]
  rw [h00, h01, h10]
  set s := (9 : ℝ) * t with hs
  have hs0 : 0 ≤ s := by rw [hs]; exact mul_nonneg (by norm_num) ht0
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have c00 : (1 : ℝ) / 9 + t = (1 - s) * (1 / 9) + s * (2 / 9) := by rw [hs]; ring
  have c01 : (2 : ℝ) / 9 - t = (1 - s) * (2 / 9) + s * (1 / 9) := by rw [hs]; ring
  have c10 : (1 : ℝ) / 9 - t = (1 - s) * (1 / 9) + s * 0 := by rw [hs]; ring
  have c11 : t = (1 - s) * 0 + s * ((1 : ℝ) / 9) := by rw [hs]; ring
  have d00 := entTerm_chord (a := (1 : ℝ) / 9) (b := (2 : ℝ) / 9) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  have d01 := entTerm_chord (a := (2 : ℝ) / 9) (b := (1 : ℝ) / 9) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  have d10 := entTerm_chord (a := (1 : ℝ) / 9) (b := (0 : ℝ)) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  have d11 := entTerm_chord (a := (0 : ℝ)) (b := (1 : ℝ) / 9) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  rw [← c00] at d00
  rw [← c01] at d01
  rw [← c10] at d10
  rw [← c11] at d11
  have hident :
      ((1 - s) * entTerm ((1 : ℝ) / 9) + s * entTerm ((2 : ℝ) / 9)) +
          ((1 - s) * entTerm ((2 : ℝ) / 9) + s * entTerm ((1 : ℝ) / 9)) +
          ((1 - s) * entTerm ((1 : ℝ) / 9) + s * entTerm 0) +
          ((1 - s) * entTerm 0 + s * entTerm ((1 : ℝ) / 9)) =
        entTerm ((2 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) + entTerm 0 := by ring
  rw [entTerm_zero] at d10 d11 hident
  simp only [add_zero] at hident
  have hle := add_le_add (add_le_add (add_le_add d00 d01) d10) d11
  rw [← hident]
  exact hle

theorem branch1_ge {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) :
    entTerm ((3 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) ≤
      entTerm (cell Γ 1 0 0) + entTerm (cell Γ 1 0 1) + entTerm (cell Γ 1 1 0) +
        entTerm (cell Γ 1 1 1) := by
  have e00 : cell Γ 1 0 0 + cell Γ 1 0 1 = 3 / 9 := by rw [cells_act0 hbad 1 0, leaf100]
  have e01 : cell Γ 1 1 0 + cell Γ 1 1 1 = 2 / 9 := by rw [cells_act0 hbad 1 1, leaf101]
  have e10 : cell Γ 1 0 0 + cell Γ 1 1 0 = 4 / 9 := by rw [cells_act1 hbad 1 0, leaf110]
  have e11 : cell Γ 1 0 1 + cell Γ 1 1 1 = 1 / 9 := by rw [cells_act1 hbad 1 1, leaf111]
  set u := cell Γ 1 1 1 with _hu
  have h10 : cell Γ 1 1 0 = 2 / 9 - u := by linarith
  have h01 : cell Γ 1 0 1 = 1 / 9 - u := by linarith
  have h00 : cell Γ 1 0 0 = 2 / 9 + u := by linarith
  have hu0 : 0 ≤ u := by
    rw [show u = cell Γ 1 1 1 from rfl]
    exact cell_nonneg Γ 1 1 1
  have hu1 : u ≤ 1 / 9 := by linarith [cell_nonneg Γ 1 0 1]
  rw [h00, h01, h10]
  set s := (9 : ℝ) * u with hs
  have hs0 : 0 ≤ s := by rw [hs]; exact mul_nonneg (by norm_num) hu0
  have hs1 : s ≤ 1 := by rw [hs]; linarith
  have c00 : (2 : ℝ) / 9 + u = (1 - s) * (2 / 9) + s * (3 / 9) := by rw [hs]; ring
  have c01 : (1 : ℝ) / 9 - u = (1 - s) * (1 / 9) + s * 0 := by rw [hs]; ring
  have c10 : (2 : ℝ) / 9 - u = (1 - s) * (2 / 9) + s * (1 / 9) := by rw [hs]; ring
  have c11 : u = (1 - s) * 0 + s * ((1 : ℝ) / 9) := by rw [hs]; ring
  have d00 := entTerm_chord (a := (2 : ℝ) / 9) (b := (3 : ℝ) / 9) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  have d01 := entTerm_chord (a := (1 : ℝ) / 9) (b := (0 : ℝ)) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  have d10 := entTerm_chord (a := (2 : ℝ) / 9) (b := (1 : ℝ) / 9) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  have d11 := entTerm_chord (a := (0 : ℝ)) (b := (1 : ℝ) / 9) (t := s)
    (by norm_num) (by norm_num) hs0 hs1
  rw [← c00] at d00
  rw [← c01] at d01
  rw [← c10] at d10
  rw [← c11] at d11
  have hsmall : entTerm ((3 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) ≤
      2 * entTerm ((2 : ℝ) / 9) + entTerm ((1 : ℝ) / 9) := by
    have h39 : (3 : ℝ) / 9 = 1 / 3 := by norm_num
    rw [h39]
    linarith [branch_gap_pos]
  have hident :
      ((1 - s) * entTerm ((2 : ℝ) / 9) + s * entTerm ((3 : ℝ) / 9)) +
          ((1 - s) * entTerm ((1 : ℝ) / 9) + s * entTerm 0) +
          ((1 - s) * entTerm ((2 : ℝ) / 9) + s * entTerm ((1 : ℝ) / 9)) +
          ((1 - s) * entTerm 0 + s * entTerm ((1 : ℝ) / 9)) =
        (1 - s) * (2 * entTerm ((2 : ℝ) / 9) + entTerm ((1 : ℝ) / 9)) +
          s * (entTerm ((3 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9)) + entTerm 0 := by ring
  rw [entTerm_zero] at d01 d11 hident
  simp only [add_zero] at hident
  have hle := add_le_add (add_le_add (add_le_add d00 d01) d10) d11
  have hchord : entTerm ((3 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9) ≤
      (1 - s) * (2 * entTerm ((2 : ℝ) / 9) + entTerm ((1 : ℝ) / 9)) +
        s * (entTerm ((3 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9)) := by
    have hs' : 0 ≤ 1 - s := by linarith
    have hdiff : 0 ≤ (2 * entTerm ((2 : ℝ) / 9) + entTerm ((1 : ℝ) / 9)) -
        (entTerm ((3 : ℝ) / 9) + 2 * entTerm ((1 : ℝ) / 9)) := by linarith
    linarith [mul_nonneg hs' hdiff]
  rw [← hident] at hchord
  exact le_trans hchord hle

theorem causal_entropy_ge {Γ : Coupling witnessTree} (hbad : Γ.badMass = 0) :
    entTerm ((3 : ℝ) / 9) + entTerm ((2 : ℝ) / 9) + 4 * entTerm ((1 : ℝ) / 9) ≤ Γ.entropy := by
  rw [entropy_eq_cells hbad]
  linarith [branch0_ge hbad, branch1_ge hbad]

theorem causalMin_witness_ge :
    entTerm ((3 : ℝ) / 9) + entTerm ((2 : ℝ) / 9) + 4 * entTerm ((1 : ℝ) / 9) ≤
      causalMin witnessTree := by
  refine le_csInf (causalEntropySet_nonempty witnessTree) ?_
  intro x hx
  rcases hx with ⟨Γ, hbad, rfl⟩
  exact causal_entropy_ge hbad

theorem witness_gap_lower : (2 : ℝ) / 9 ≤ gapOf witnessTree := by
  unfold gapOf
  linarith [ordinaryMin_witness_le, causalMin_witness_ge, profile_gap_eq]

theorem witness_gapSup_lower : (2 : ℝ) / 9 ≤ gapSup :=
  le_trans witness_gap_lower (gapOf_le_gapSup witnessTree)

#print axioms witness_gapSup_lower

end CausalSpectrum
end

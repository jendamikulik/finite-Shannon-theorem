/-
Finite-horizon sandwich for the geometric-gated seed.

Proved here, with no `sorry`:
* `shannonTerm (a*b) = b*shannonTerm a + a*shannonTerm b`;
* merging a group of nonnegative masses totalling at most `1` cannot raise
  the Shannon sum (`shannonTerm_group`);
* a product of two probability laws has entropy equal to the sum of the
  factors (`entropy_prod`).

These are the two analytic steps of the finite-horizon sandwich. The wiring
to a readout and to `Cₙ` is not in this file.
-/
import CausalSeed.Vanishing
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section

open Real Filter

namespace Vanishing

theorem shannonTerm_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    shannonTerm (a * b) = b * shannonTerm a + a * shannonTerm b := by
  by_cases ha0 : a = 0
  · simp [shannonTerm, ha0]
  by_cases hb0 : b = 0
  · simp [shannonTerm, hb0]
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  rw [shannonTerm_of_pos (mul_pos ha' hb'), shannonTerm_of_pos ha', shannonTerm_of_pos hb',
    logb_mul (ne_of_gt ha') (ne_of_gt hb')]
  ring

theorem shannonTerm_nonneg_of_le_one {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1) : 0 ≤ shannonTerm w := by
  by_cases h : w = 0
  · simp [shannonTerm, h]
  · have hpos : 0 < w := lt_of_le_of_ne h0 (Ne.symm h)
    rw [shannonTerm_of_pos hpos]
    have hlog : logb 2 w ≤ 0 := (logb_nonpos_iff (by norm_num : (1 : ℝ) < 2) hpos).2 h1
    nlinarith

theorem tsum_shannonTerm_nonneg {α : Type*} (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (h1 : ∀ a, μ a ≤ 1) :
    0 ≤ ∑' a, shannonTerm (μ a) :=
  tsum_nonneg fun a => shannonTerm_nonneg_of_le_one (h0 a) (h1 a)

theorem term_le_sum {ι : Type*} (w : ι → ℝ) (h0 : ∀ i, 0 ≤ w i) (hs : Summable w) (i : ι) :
    w i ≤ ∑' j, w j := by
  classical
  have hrest : 0 ≤ ∑' j, if j = i then (0 : ℝ) else w j :=
    tsum_nonneg fun j => by split_ifs <;> simp [h0]
  have h := hs.tsum_eq_add_tsum_ite i
  linarith

/-- A group of nonnegative masses totalling at most `1` has Shannon sum at least the
Shannon term of the total. -/
theorem shannonTerm_group {ι : Type*} (w : ι → ℝ) (h0 : ∀ i, 0 ≤ w i) (hs : Summable w)
    (hS : Summable fun i => shannonTerm (w i)) (hA1 : ∑' i, w i ≤ 1) :
    shannonTerm (∑' i, w i) ≤ ∑' i, shannonTerm (w i) := by
  classical
  set A := ∑' i, w i with hA
  have hA0 : 0 ≤ A := tsum_nonneg h0
  by_cases hAz : A = 0
  · have hzero : shannonTerm A = 0 := by simp [shannonTerm, hAz]
    rw [hzero]
    exact tsum_shannonTerm_nonneg w h0 fun i => le_trans (term_le_sum w h0 hs i) hA1
  have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hAz)
  have hpoint : ∀ i, (if w i = 0 then 0 else -w i * logb 2 A) ≤ shannonTerm (w i) := by
    intro i
    by_cases hi : w i = 0
    · simp [shannonTerm, hi]
    · have hpos : 0 < w i := lt_of_le_of_ne (h0 i) (Ne.symm hi)
      have hle : w i ≤ A := term_le_sum w h0 hs i
      have hratio : w i / A ≤ 1 := (div_le_one hApos).2 hle
      have hlog : logb 2 (w i / A) ≤ 0 :=
        (logb_nonpos_iff (by norm_num : (1 : ℝ) < 2) (div_pos hpos hApos)).2 hratio
      rw [shannonTerm_of_pos hpos]
      have hlogw : logb 2 (w i) = logb 2 (w i / A) + logb 2 A := by
        rw [← logb_mul (ne_of_gt (div_pos hpos hApos)) (ne_of_gt hApos)]
        congr 1
        field_simp
      rw [hlogw]
      simp [hi]
      nlinarith
  have hcross_nonneg : ∀ i, 0 ≤ (if w i = 0 then 0 else -w i * logb 2 A) := by
    intro i
    by_cases hi : w i = 0
    · simp [hi]
    · have hlogA : logb 2 A ≤ 0 := (logb_nonpos_iff (by norm_num : (1 : ℝ) < 2) hApos).2 hA1
      simp [hi]
      nlinarith [h0 i]
  have hcross_summable : Summable fun i => if w i = 0 then 0 else -w i * logb 2 A :=
    Summable.of_nonneg_of_le hcross_nonneg hpoint hS
  have hfun : (fun i => if w i = 0 then 0 else -w i * logb 2 A) =
      fun i => w i * (-logb 2 A) := by
    funext i; by_cases hi : w i = 0 <;> simp [hi, mul_comm]
  have hcross : ∑' i, (if w i = 0 then 0 else -w i * logb 2 A) = -A * logb 2 A := by
    rw [hfun, tsum_mul_right]
    ring
  rw [shannonTerm_of_pos hApos, ← hcross]
  exact hcross_summable.tsum_le_tsum hpoint hS

theorem summable_norm_of_nonneg {α : Type*} (f : α → ℝ) (h0 : ∀ a, 0 ≤ f a) (hs : Summable f) :
    Summable fun a => ‖f a‖ := by
  simpa [Real.norm_eq_abs, abs_of_nonneg (h0 _)] using hs

set_option maxHeartbeats 800000 in
theorem entropy_prod {α β : Type*} (μ : α → ℝ) (ν : β → ℝ)
    (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ b, 0 ≤ ν b)
    (hμ1 : ∑' a, μ a = 1) (hν1 : ∑' b, ν b = 1)
    (hμS : Summable μ) (hνS : Summable ν)
    (hμE : Summable fun a => shannonTerm (μ a))
    (hνE : Summable fun b => shannonTerm (ν b))
    (hμ1' : ∀ a, μ a ≤ 1) (hν1' : ∀ b, ν b ≤ 1) :
    ∑' p : α × β, shannonTerm (μ p.1 * ν p.2) =
      (∑' a, shannonTerm (μ a)) + ∑' b, shannonTerm (ν b) := by
  have hμN := summable_norm_of_nonneg μ hμ0 hμS
  have hνN := summable_norm_of_nonneg ν hν0 hνS
  have hμEN := summable_norm_of_nonneg (fun a => shannonTerm (μ a))
    (fun a => shannonTerm_nonneg_of_le_one (hμ0 a) (hμ1' a)) hμE
  have hνEN := summable_norm_of_nonneg (fun b => shannonTerm (ν b))
    (fun b => shannonTerm_nonneg_of_le_one (hν0 b) (hν1' b)) hνE
  have hs1 : Summable fun p : α × β => ν p.2 * shannonTerm (μ p.1) := by
    simpa [Function.comp_def, Prod.swap] using
      (summable_mul_of_summable_norm hνN hμEN).comp_injective
        (Prod.swap_injective : Function.Injective (Prod.swap : α × β → β × α))
  have hs2 : Summable fun p : α × β => μ p.1 * shannonTerm (ν p.2) :=
    summable_mul_of_summable_norm hμN hνEN
  have hpt : ∀ p : α × β, shannonTerm (μ p.1 * ν p.2) =
      ν p.2 * shannonTerm (μ p.1) + μ p.1 * shannonTerm (ν p.2) :=
    fun p => shannonTerm_mul (hμ0 p.1) (hν0 p.2)
  simp_rw [hpt]
  rw [hs1.tsum_add hs2]
  have e1 : ∑' p : α × β, shannonTerm (μ p.1) * ν p.2 =
      (∑' a, shannonTerm (μ a)) * ∑' b, ν b :=
    (tsum_mul_tsum_of_summable_norm hμEN hνN).symm
  have e2 : ∑' p : α × β, μ p.1 * shannonTerm (ν p.2) =
      (∑' a, μ a) * ∑' b, shannonTerm (ν b) :=
    (tsum_mul_tsum_of_summable_norm hμN hνEN).symm
  have e1' : ∑' p : α × β, ν p.2 * shannonTerm (μ p.1) =
      (∑' a, shannonTerm (μ a)) * ∑' b, ν b := by
    simpa [mul_comm] using e1
  rw [e1', e2, hμ1, hν1]
  ring




end Vanishing
end

/-
Quantitative core of "The Entropy Cost of Vanishing Activity".

Proved here, with no `sorry`:
* the positive geometric law `P(k) = 2^{-k}` has Shannon entropy `2` bits;
* the explicit coordinate law `P(0) = 1-p`, `P(k) = p·2^{-k}` (`k ≥ 1`)
  has entropy `h₂(p) + 2p`, for every `p ∈ (0,1)`;
* a finite family of such coordinates therefore costs exactly
  `∑ h₂(pᵢ) + 2 ∑ pᵢ` more than `∑ h₂(pᵢ)` by the gap `2 ∑ pᵢ`;
* `h₂(p) ≥ p` on `(0, 1/2]`, so summability of `h₂(pₜ)` forces
  summability of `pₜ`.

Not in this file: the causal embedding into a common seed for every adaptive
policy, the infinite-horizon trichotomy, and the `log₂ ln n` asymptotic.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

noncomputable section

open Real

namespace Vanishing

noncomputable def shannonTerm (w : ℝ) : ℝ :=
  if w = 0 then 0 else -w * logb 2 w

noncomputable def h2 (u : ℝ) : ℝ :=
  shannonTerm u + shannonTerm (1 - u)

theorem shannonTerm_of_pos {w : ℝ} (hw : 0 < w) :
    shannonTerm w = -w * logb 2 w := by
  simp [shannonTerm, ne_of_gt hw]

theorem logb_two_pow_half (k : ℕ) :
    logb 2 ((1 / 2 : ℝ) ^ k) = -(k : ℝ) := by
  rw [logb_pow, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, logb_inv,
    logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  ring

theorem half_norm_lt_one : ‖(1 / 2 : ℝ)‖ < 1 := by
  simp
  norm_num

theorem tsum_id_mul_half_pow : ∑' k : ℕ, k * (1 / 2 : ℝ) ^ k = 2 := by
  rw [tsum_coe_mul_geometric_of_norm_lt_one half_norm_lt_one]
  norm_num

theorem tsum_half_succ : ∑' k : ℕ, (1 / 2 : ℝ) ^ (k + 1) = 1 := by
  have h := summable_geometric_two.tsum_eq_zero_add
  rw [tsum_geometric_two] at h
  simp only [pow_zero] at h
  linarith

theorem summable_half_succ : Summable fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1) :=
  (summable_nat_add_iff 1).2 summable_geometric_two

theorem summable_id_half : Summable fun n : ℕ => n * (1 / 2 : ℝ) ^ n :=
  (hasSum_coe_mul_geometric_of_norm_lt_one half_norm_lt_one).summable

theorem tsum_id_half_succ :
    ∑' k : ℕ, (k + 1 : ℝ) * (1 / 2 : ℝ) ^ (k + 1) = 2 := by
  have h := summable_id_half.tsum_eq_zero_add
  rw [tsum_id_mul_half_pow] at h
  simpa using h.symm

noncomputable def geomProb (k : ℕ) : ℝ :=
  if k = 0 then 0 else (1 / 2 : ℝ) ^ k

theorem geomProb_zero : geomProb 0 = 0 := by simp [geomProb]

theorem geomProb_succ (k : ℕ) : geomProb (k + 1) = (1 / 2 : ℝ) ^ (k + 1) := by
  simp [geomProb]

theorem summable_geomProb : Summable geomProb :=
  (summable_nat_add_iff 1).1 (by simpa [geomProb_succ] using summable_half_succ)

theorem geomProb_tsum : ∑' k : ℕ, geomProb k = 1 := by
  rw [summable_geomProb.tsum_eq_zero_add, geomProb_zero, zero_add]
  simp_rw [geomProb_succ]
  exact tsum_half_succ

theorem geometric_entropy : ∑' k : ℕ, shannonTerm (geomProb k) = 2 := by
  have hterm : ∀ k : ℕ, shannonTerm (geomProb k) = k * (1 / 2 : ℝ) ^ k := by
    intro k
    cases k with
    | zero => simp [geomProb, shannonTerm]
    | succ n =>
      have hpos : (0 : ℝ) < (1 / 2) ^ (n + 1) := by positivity
      rw [geomProb_succ, shannonTerm_of_pos hpos, logb_two_pow_half]
      push_cast
      ring
  simp_rw [hterm]
  exact tsum_id_mul_half_pow

noncomputable def zProb (p : ℝ) (k : ℕ) : ℝ :=
  if k = 0 then 1 - p else p * (1 / 2 : ℝ) ^ k

theorem zProb_zero (p : ℝ) : zProb p 0 = 1 - p := by simp [zProb]

theorem zProb_succ (p : ℝ) (k : ℕ) : zProb p (k + 1) = p * (1 / 2 : ℝ) ^ (k + 1) := by
  simp [zProb]

theorem summable_zProb {p : ℝ} : Summable fun k : ℕ => zProb p k :=
  (summable_nat_add_iff 1).1 (by simpa [zProb_succ] using summable_half_succ.mul_left p)

theorem zProb_tsum {p : ℝ} (_hp0 : 0 ≤ p) (_hp1 : p ≤ 1) :
    ∑' k : ℕ, zProb p k = 1 := by
  rw [summable_zProb.tsum_eq_zero_add, zProb_zero]
  simp_rw [zProb_succ, tsum_mul_left, tsum_half_succ]
  ring

theorem sparseCoordinate_entropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    ∑' k : ℕ, shannonTerm (zProb p k) = h2 p + 2 * p := by
  have hshift : ∀ k : ℕ,
      shannonTerm (zProb p (k + 1)) =
        (-p * logb 2 p) * (1 / 2 : ℝ) ^ (k + 1) +
          p * ((k + 1 : ℝ) * (1 / 2 : ℝ) ^ (k + 1)) := by
    intro k
    have hpos : 0 < p * (1 / 2 : ℝ) ^ (k + 1) := by positivity
    rw [zProb_succ, shannonTerm_of_pos hpos,
      logb_mul (ne_of_gt hp0) (by positivity), logb_two_pow_half]
    push_cast
    ring
  have hs1 : Summable fun k : ℕ => (-p * logb 2 p) * (1 / 2 : ℝ) ^ (k + 1) :=
    summable_half_succ.mul_left _
  have hs2 : Summable fun k : ℕ =>
      p * ((k + 1 : ℝ) * (1 / 2 : ℝ) ^ (k + 1)) := by
    have h :=
      ((summable_nat_add_iff (f := fun n : ℕ => n * (1 / 2 : ℝ) ^ n) 1).2
        summable_id_half).mul_left p
    refine h.congr fun k => ?_
    simp [Nat.cast_add]
  have htail : ∑' k : ℕ, shannonTerm (zProb p (k + 1)) =
      (-p * logb 2 p) + p * 2 := by
    simp_rw [hshift]
    rw [hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, tsum_half_succ,
      tsum_id_half_succ]
    ring
  have hs_tail : Summable fun k : ℕ => shannonTerm (zProb p (k + 1)) := by
    simp_rw [hshift]
    exact hs1.add hs2
  have hs_full : Summable fun k : ℕ => shannonTerm (zProb p k) :=
    (summable_nat_add_iff 1).1 hs_tail
  rw [hs_full.tsum_eq_zero_add, zProb_zero, htail]
  have h1p : 0 < 1 - p := by linarith
  unfold h2
  rw [shannonTerm_of_pos h1p, shannonTerm_of_pos hp0]
  ring

theorem h2_ge_self {p : ℝ} (hp0 : 0 < p) (hp : p ≤ 1 / 2) : p ≤ h2 p := by
  have h1 : (1 : ℝ) < 2 := by norm_num
  have hone : logb 2 p ≤ -1 := by
    have hinv : (2 : ℝ) ≤ 1 / p := by
      rw [le_div_iff₀ hp0]
      linarith
    have hlog : logb 2 2 ≤ logb 2 (1 / p) :=
      logb_le_logb_of_le h1 (by norm_num : (0 : ℝ) < 2) hinv
    rw [logb_self_eq_one h1, logb_div one_ne_zero (ne_of_gt hp0), logb_one] at hlog
    linarith
  have hrest : 0 ≤ shannonTerm (1 - p) := by
    have h1p : 0 < 1 - p := by linarith
    rw [shannonTerm_of_pos h1p]
    have hlog : logb 2 (1 - p) ≤ 0 := by
      rw [logb_nonpos_iff h1 h1p]
      linarith
    nlinarith
  unfold h2
  rw [shannonTerm_of_pos hp0]
  nlinarith

theorem summable_prob_of_summable_h2 {p : ℕ → ℝ}
    (hp : ∀ t, 0 < p t ∧ p t ≤ 1 / 2)
    (h : Summable fun t => h2 (p t)) : Summable p :=
  h.of_nonneg_of_le (fun t => (hp t).1.le) fun t => h2_ge_self (hp t).1 (hp t).2

theorem sparseActivity_excess {ι : Type*} [Fintype ι] (p : ι → ℝ) :
    (∑ i, (h2 (p i) + 2 * p i)) - ∑ i, h2 (p i) = 2 * ∑ i, p i := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem sparseActivity_sandwich {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    ∑ i, h2 (p i) ≤ ∑ i, (h2 (p i) + 2 * p i) := by
  classical
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have : 0 ≤ (2 : ℝ) * ∑ i, p i := by
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg fun i _ => hp i
  linarith

end Vanishing

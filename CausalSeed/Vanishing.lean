/-
Quantitative core of "The Entropy Cost of Vanishing Activity".

Proved here, with no `sorry`:
* the positive geometric law `P(k) = 2^{-k}` has Shannon entropy `2` bits;
* the explicit coordinate law `P(0) = 1-p`, `P(k) = p·2^{-k}` (`k ≥ 1`)
  has entropy `h₂(p) + 2p`, for every `p ∈ (0,1)`;
* a finite family of such coordinates therefore costs exactly
  `∑ h₂(pᵢ) + 2 ∑ pᵢ` more than `∑ h₂(pᵢ)` by the gap `2 ∑ pᵢ`;
* `h₂(p) ≥ p` on `(0, 1/2]`, so summability of `h₂(pₜ)` forces
  summability of `pₜ`;
* a binary expansion makes the geometric gate return probability `q`;
* `∏(1-pᵢ) ≤ exp(-∑ pᵢ)`, and the product tends to `0` when `∑ p` diverges;
* `1 - ∏(1-x) ≤ ∑ x` for a finite list in `[0,1]`;
* a function of one fair bit cannot have success probability `1/4`, while the
  three-atom law `(1/2,1/4,1/4)` has entropy `3/2`.

Not in this file: a strategy space indexed by histories, cylinder exactness for
every adaptive policy, the infinite-horizon trichotomy, total-variation
approximation of strategy laws, and the `log₂ ln n` asymptotic.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Order.Filter.AtTopBot.Basic



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

theorem h2_half : h2 (1 / 2) = 1 := by
  unfold h2
  have hlog : logb 2 (1 / 2 : ℝ) = -1 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, logb_inv,
      logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  rw [shannonTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 2), hlog]
  have hlog' : logb 2 (1 - 1 / 2 : ℝ) = -1 := by
    have : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
    rw [this, hlog]
  rw [shannonTerm_of_pos (by norm_num : (0 : ℝ) < 1 - 1 / 2), hlog']
  ring

theorem shannonTerm_quarter : shannonTerm (1 / 4) = 1 / 2 := by
  rw [shannonTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  have hlog : logb 2 (1 / 4 : ℝ) = -2 := by
    rw [show (1 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, logb_two_pow_half 2]
    norm_num
  rw [hlog]
  norm_num

/-- The collapsed coupling `(1/2, 1/4, 1/4)` has entropy `3/2`. -/
theorem endpoint_entropy_three_halves :
    shannonTerm (1 / 2) + shannonTerm (1 / 4) + shannonTerm (1 / 4) = 3 / 2 := by
  have hhalf : shannonTerm (1 / 2) = 1 / 2 := by
    rw [shannonTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hlog : logb 2 (1 / 2 : ℝ) = -1 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, logb_inv,
        logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    rw [hlog]
    ring
  rw [hhalf]
  simp only [shannonTerm_quarter]
  norm_num

theorem bool_sum (g : Bool → ℝ) : ∑ b : Bool, g b = g false + g true := by
  classical
  have : (Finset.univ : Finset Bool) = {false, true} := by decide
  rw [this, Finset.sum_pair (by decide : (false : Bool) ≠ true)]

/-- No deterministic function of one fair bit has success probability `1/4`. -/
theorem fairBit_image_ne_quarter (f : Bool → Bool) :
    ¬ (∑ b : Bool, (if f b = true then (1 / 2 : ℝ) else 0)) = 1 / 4 := by
  rw [bool_sum]
  cases hfalse : f false <;> cases htrue : f true <;> norm_num [hfalse, htrue]

/-- If `q / p` has binary digits `b k ∈ {0,1}`, the geometric gate returns `1`
with probability `q`. -/
theorem gate_exact {p q : ℝ} {b : ℕ → ℝ} (hp : 0 < p)
    (hb : ∀ k, b k = 0 ∨ b k = 1)
    (hsum : ∑' k : ℕ, (if k = 0 then (0 : ℝ) else b k * (1 / 2) ^ k) = q / p) :
    ∑' k : ℕ, (if k = 0 then 0 else zProb p k * b k) = q := by
  have hpt : ∀ k, (if k = 0 then (0 : ℝ) else zProb p k * b k) =
      p * (if k = 0 then 0 else b k * (1 / 2) ^ k) := by
    intro k
    by_cases hk : k = 0
    · simp [hk]
    · simp [zProb, hk, mul_left_comm, mul_comm]
  have hs : Summable fun k : ℕ => if k = 0 then (0 : ℝ) else b k * (1 / 2) ^ k := by
    refine Summable.of_norm_bounded_eventually summable_geometric_two (Filter.Eventually.of_forall ?_)
    intro k
    simp only [Real.norm_eq_abs]
    by_cases hk : k = 0
    · simp [hk]
    · have hb01 : b k = 0 ∨ b k = 1 := hb k
      rcases hb01 with h0 | h1
      · simp [hk, h0]
      · simp [hk, h1]
  simp_rw [hpt, tsum_mul_left, hsum]
  field_simp

theorem log_one_sub_le_neg {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x < 1) :
    log (1 - x) ≤ -x := by
  have hpos : 0 < 1 - x := by linarith
  have h := log_le_sub_one_of_pos hpos
  linarith

theorem prod_one_sub_le_exp {ι : Type*} [Fintype ι] (p : ι → ℝ)
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i < 1) :
    ∏ i, (1 - p i) ≤ exp (-∑ i, p i) := by
  classical
  have hpos : ∀ i, 0 < 1 - p i := fun i => by linarith [hp1 i]
  have hlog : ∑ i, log (1 - p i) ≤ -∑ i, p i := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    exact log_one_sub_le_neg (hp0 i) (hp1 i)
  have hprod : ∏ i, (1 - p i) = exp (∑ i, log (1 - p i)) := by
    rw [Real.exp_sum, Finset.prod_congr rfl]
    intro i _
    exact (Real.exp_log (hpos i)).symm
  rw [hprod]
  exact exp_le_exp.mpr hlog

theorem prod_range_one_sub_le_exp (p : ℕ → ℝ) (n : ℕ)
    (hp0 : ∀ t, t < n → 0 ≤ p t) (hp1 : ∀ t, t < n → p t < 1) :
    ∏ i ∈ Finset.range n, (1 - p i) ≤ exp (-∑ i ∈ Finset.range n, p i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun t ht => hp0 t (Nat.lt_succ_of_lt ht))
      (fun t ht => hp1 t (Nat.lt_succ_of_lt ht))
    rw [Finset.prod_range_succ, Finset.sum_range_succ]
    have hpn : p n < 1 := hp1 n (Nat.lt_succ_self n)
    have hp0n : 0 ≤ p n := hp0 n (Nat.lt_succ_self n)
    have hp : 0 < 1 - p n := by linarith
    have hone : 1 - p n ≤ exp (-p n) := by
      rw [← Real.exp_log hp]
      exact exp_le_exp.mpr (log_one_sub_le_neg hp0n hpn)
    have hnonneg : 0 ≤ ∏ i ∈ Finset.range n, (1 - p i) := by
      apply Finset.prod_nonneg
      intro i hi
      have hi' : i < n := Finset.mem_range.mp hi
      linarith [hp1 i (Nat.lt_succ_of_lt hi')]
    have hexp : exp (-∑ i ∈ Finset.range n, p i) * exp (-p n) =
        exp (-((∑ i ∈ Finset.range n, p i) + p n)) := by
      rw [← Real.exp_add]
      ring_nf
    nlinarith [ih', hone, hnonneg, Real.exp_pos (-∑ i ∈ Finset.range n, p i)]

theorem prod_one_sub_tendsto_zero {p : ℕ → ℝ}
    (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t < 1)
    (hdiv : Filter.Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, p i) Filter.atTop Filter.atTop) :
    Filter.Tendsto (fun n : ℕ => ∏ i ∈ Finset.range n, (1 - p i)) Filter.atTop (nhds 0) := by
  have hle : ∀ n, ∏ i ∈ Finset.range n, (1 - p i) ≤ exp (-∑ i ∈ Finset.range n, p i) :=
    fun n => prod_range_one_sub_le_exp p n (fun t _ => hp0 t) (fun t _ => hp1 t)
  have hexp : Filter.Tendsto (fun n : ℕ => exp (-∑ i ∈ Finset.range n, p i))
      Filter.atTop (nhds 0) := by
    refine Real.tendsto_exp_atBot.comp ?_
    rw [Filter.tendsto_atTop_atBot]
    intro c
    rw [Filter.tendsto_atTop_atTop] at hdiv
    obtain ⟨N, hN⟩ := hdiv (-c)
    exact ⟨N, fun n hn => by linarith [hN n hn]⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hexp ?_ ?_
  · refine Filter.Eventually.of_forall fun n => ?_
    apply Finset.prod_nonneg
    intro i _
    linarith [hp1 i]
  · exact Filter.Eventually.of_forall hle

theorem one_sub_list_bounds (l : List ℝ)
    (h0 : ∀ x ∈ l, 0 ≤ x) (h1 : ∀ x ∈ l, x ≤ 1) :
    0 ≤ (l.map fun x => 1 - x).prod ∧
      (l.map fun x => 1 - x).prod ≤ 1 ∧
      1 - (l.map fun x => 1 - x).prod ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha0 : 0 ≤ a := h0 a (by simp)
    have ha1 : a ≤ 1 := h1 a (by simp)
    have ih' := ih (fun x hx => h0 x (by simp [hx])) (fun x hx => h1 x (by simp [hx]))
    rcases ih' with ⟨hp0, hp1, hp⟩
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have h1a0 : 0 ≤ 1 - a := by linarith
    have h1a1 : 1 - a ≤ 1 := by linarith
    refine ⟨?_, ?_, ?_⟩
    · nlinarith
    · nlinarith
    · have : 1 - (1 - a) * (l.map fun x => 1 - x).prod =
          (1 - (l.map fun x => 1 - x).prod) + a * (l.map fun x => 1 - x).prod := by ring
      rw [this]
      nlinarith

theorem one_sub_listProd_le_sum (l : List ℝ)
    (h0 : ∀ x ∈ l, 0 ≤ x) (h1 : ∀ x ∈ l, x ≤ 1) :
    1 - (l.map fun x => 1 - x).prod ≤ l.sum :=
  (one_sub_list_bounds l h0 h1).2.2

end Vanishing

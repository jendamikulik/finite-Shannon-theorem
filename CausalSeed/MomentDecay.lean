/-
Total-variation decay for smoothed random walks.

Finite signed measures on `ℝ` with finite support are elements of the group algebra
`ℝ[ℝ]` (`AddMonoidAlgebra ℝ ℝ`), convolution being the product. `tv c = Σ |c_z|` is the
total variation, which is submultiplicative. For `d = δ_{-b} - δ_b` and a law
`β = ρ δ_c (δ_{-b} + δ_b)/2 + ζ` with `tv ζ ≤ 1 - ρ`, the binomial expansion of `β^r` and the
bound `tv (d (δ_{-b}+δ_b)^m) ≤ 2^{m+1}/√(m+1)` give
`tv (d^q β^r) ≤ 2^q (√q)^q · E[(K+1)^{-q/2}]`, `K ~ Bin(r, ρ)`.
-/
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Algebra.BigOperators.Field

noncomputable section
open Classical Finset

namespace CausalSpectrum.Sqrt.Decay

/-- Finitely supported signed measures on `ℝ`. -/
abbrev Meas := AddMonoidAlgebra ℝ ℝ

open AddMonoidAlgebra

/-- Total variation `Σ_z |c_z|`. -/
def tv (c : Meas) : ℝ := c.coeff.sum fun _ w => |w|

theorem tv_eq_of_subset (c : Meas) {S : Finset ℝ} (h : c.coeff.support ⊆ S) :
    tv c = ∑ z ∈ S, |c.coeff z| :=
  Finsupp.sum_of_support_subset _ h _ (fun _ _ => abs_zero)

theorem tv_nonneg (c : Meas) : 0 ≤ tv c :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem tv_zero : tv 0 = 0 := by simp [tv]

theorem tv_add_le (c d : Meas) : tv (c + d) ≤ tv c + tv d := by
  set S := c.coeff.support ∪ d.coeff.support
  have hcd : (c + d).coeff.support ⊆ S := by
    rw [coeff_add]; exact Finsupp.support_add
  rw [tv_eq_of_subset _ hcd, tv_eq_of_subset c subset_union_left,
    tv_eq_of_subset d subset_union_right, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun z _ => ?_
  rw [coeff_add, Finsupp.add_apply]; exact abs_add_le _ _

theorem tv_smul (r : ℝ) (c : Meas) : tv (r • c) = |r| * tv c := by
  simp only [tv, coeff_smul]
  rw [Finsupp.sum_smul_index (fun _ => abs_zero), Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by simp only [smul_eq_mul, abs_mul]

theorem tv_neg (c : Meas) : tv (-c) = tv c := by
  rw [show -c = (-1 : ℝ) • c by simp, tv_smul]; simp

theorem tv_sub_le (c d : Meas) : tv (c - d) ≤ tv c + tv d := by
  rw [sub_eq_add_neg]; exact (tv_add_le _ _).trans (by rw [tv_neg])

theorem tv_single (z w : ℝ) : tv (single z w) = |w| := by
  simp only [tv, coeff_single]
  exact Finsupp.sum_single_index abs_zero

theorem tv_sum_le {ι : Type*} (s : Finset ι) (f : ι → Meas) : tv (∑ i ∈ s, f i) ≤ ∑ i ∈ s, tv (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [tv_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (tv_add_le _ _).trans (by linarith)

theorem tv_finsupp_sum_le (f : ℝ →₀ ℝ) (g : ℝ → ℝ → Meas) :
    tv (f.sum g) ≤ f.sum fun a b => tv (g a b) := tv_sum_le _ _

theorem tv_mul_le (c d : Meas) : tv (c * d) ≤ tv c * tv d := by
  rw [AddMonoidAlgebra.mul_def]
  refine (tv_finsupp_sum_le _ _).trans ?_
  conv_rhs => rw [tv, Finsupp.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  refine (tv_finsupp_sum_le _ _).trans (le_of_eq ?_)
  show _ = |c.coeff a| * d.coeff.sum fun _ w => |w|
  rw [Finsupp.mul_sum]
  exact Finsupp.sum_congr fun b _ => by rw [tv_single, abs_mul]


theorem tv_one : tv 1 = 1 := by rw [AddMonoidAlgebra.one_def, tv_single, abs_one]

theorem tv_pow_le (c : Meas) : ∀ n : ℕ, tv (c ^ n) ≤ tv c ^ n
  | 0 => by rw [pow_zero, pow_zero, tv_one]
  | n + 1 => by
    rw [pow_succ, pow_succ]
    exact (tv_mul_le _ _).trans (mul_le_mul_of_nonneg_right (tv_pow_le c n) (tv_nonneg c))

/-! ## Binomial sums -/

/-- Pascal transfer: `Σ_j C(N+1,j) f(j) = Σ_j C(N,j) (f(j) + f(j+1))`. -/
theorem sum_choose_succ (N : ℕ) (f : ℕ → ℝ) :
    ∑ j ∈ range (N + 1 + 1), ((N + 1).choose j : ℝ) * f j =
      ∑ j ∈ range (N + 1), (N.choose j : ℝ) * (f j + f (j + 1)) := by
  rw [Finset.sum_range_succ']
  simp only [Nat.choose_succ_succ, Nat.cast_add, add_mul, Finset.sum_add_distrib, mul_add]
  have h1 : ∑ j ∈ range (N + 1), (N.choose (j + 1) : ℝ) * f (j + 1) + (N + 1).choose 0 * f 0 =
      ∑ j ∈ range (N + 1), (N.choose j : ℝ) * f j := by
    rw [Finset.sum_range_succ (fun j => (N.choose (j + 1) : ℝ) * f (j + 1)),
      Finset.sum_range_succ' (fun j => (N.choose j : ℝ) * f j),
      Nat.choose_eq_zero_of_lt (show N < N + 1 by omega)]
    simp
  rw [add_assoc, h1]; ring

theorem sum_choose (N : ℕ) : ∑ j ∈ range (N + 1), (N.choose j : ℝ) = 2 ^ N := by
  have := Nat.sum_range_choose N
  exact_mod_cast this

/-- `Σ_j C(N,j) (N - 2j)² = N 2^N`. -/
theorem sum_choose_sq : ∀ N : ℕ,
    ∑ j ∈ range (N + 1), (N.choose j : ℝ) * ((N : ℝ) - 2 * j) ^ 2 = (N : ℝ) * 2 ^ N
  | 0 => by simp
  | N + 1 => by
    have key := sum_choose_succ N (fun j => (((N + 1 : ℕ) : ℝ) - 2 * j) ^ 2)
    rw [key]
    · have ih := sum_choose_sq N
      have h2 := sum_choose N
      have : ∀ j ∈ range (N + 1), (N.choose j : ℝ) * ((((N + 1 : ℕ) : ℝ) - 2 * j) ^ 2 +
          (((N + 1 : ℕ) : ℝ) - 2 * ((j + 1 : ℕ) : ℝ)) ^ 2) =
          2 * ((N.choose j : ℝ) * ((N : ℝ) - 2 * j) ^ 2) + 2 * (N.choose j : ℝ) := fun j _ => by
        push_cast; ring
      rw [Finset.sum_congr rfl this, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ih, h2]
      push_cast; ring

/-- `Σ_j C(N,j) |N - 2j| ≤ 2^N √N`. -/
theorem sum_choose_abs (N : ℕ) :
    ∑ j ∈ range (N + 1), (N.choose j : ℝ) * |(N : ℝ) - 2 * j| ≤ 2 ^ N * Real.sqrt N := by
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (range (N + 1))
    (fun j => Real.sqrt (N.choose j)) (fun j => Real.sqrt (N.choose j) * |(N : ℝ) - 2 * j|)
  have e1 : ∀ j, Real.sqrt (N.choose j) * (Real.sqrt (N.choose j) * |(N : ℝ) - 2 * j|) =
      (N.choose j : ℝ) * |(N : ℝ) - 2 * j| := fun j => by
    rw [← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  have e2 : ∀ j, Real.sqrt (N.choose j) ^ 2 = (N.choose j : ℝ) := fun j =>
    Real.sq_sqrt (Nat.cast_nonneg _)
  have e3 : ∀ j, (Real.sqrt (N.choose j) * |(N : ℝ) - 2 * j|) ^ 2 =
      (N.choose j : ℝ) * ((N : ℝ) - 2 * j) ^ 2 := fun j => by
    rw [mul_pow, e2, sq_abs]
  simp only [e1, e2, e3] at cs
  rw [sum_choose, sum_choose_sq] at cs
  have hS : 0 ≤ ∑ j ∈ range (N + 1), (N.choose j : ℝ) * |(N : ℝ) - 2 * j| :=
    Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)
  have : (2 ^ N * Real.sqrt N) ^ 2 = 2 ^ N * (N * 2 ^ N) := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  rw [← this] at cs
  exact (pow_le_pow_iff_left₀ hS (by positivity) two_ne_zero).1 cs


/-- `A_j - B_j` for the coefficients of `(X - 1)(X + 1)^m`. -/
def alt (m j : ℕ) : ℝ := (if j = 0 then 0 else (m.choose (j - 1) : ℝ)) - (m.choose j : ℝ)

theorem alt_eq (m j : ℕ) (hj : j ≤ m + 1) :
    alt m j = -(((m + 1).choose j : ℝ) * ((m + 1 : ℝ) - 2 * j) / (m + 1)) := by
  have hm : (m + 1 : ℝ) ≠ 0 := by positivity
  rcases j with _ | i
  · simp [alt]; field_simp
  · simp only [alt, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]
    have h1 : ((m + 1 : ℕ) : ℝ) * (m.choose i : ℝ) = ((m + 1).choose (i + 1) : ℝ) * (i + 1) := by
      exact_mod_cast Nat.add_one_mul_choose_eq m i
    have h2 : (m.choose (i + 1) : ℝ) * ((m + 1 : ℕ) : ℝ) =
        ((m + 1).choose (i + 1) : ℝ) * ((m + 1 - (i + 1) : ℕ) : ℝ) := by
      exact_mod_cast Nat.choose_mul_succ_eq m (i + 1)
    rw [Nat.cast_sub (by omega)] at h2
    push_cast at h1 h2 ⊢
    field_simp
    linear_combination h1 - h2

theorem sum_abs_alt (m : ℕ) :
    ∑ j ∈ range (m + 2), |alt m j| ≤ 2 ^ (m + 1) / Real.sqrt (m + 1) := by
  have hm : (0 : ℝ) < m + 1 := by positivity
  have e : ∀ j ∈ range (m + 2), |alt m j| =
      ((m + 1).choose j : ℝ) * |((m + 1 : ℕ) : ℝ) - 2 * j| / (m + 1) := fun j hj => by
    rw [alt_eq m j (by simp at hj; omega), abs_neg, abs_div, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_pos hm]
    push_cast; ring_nf
  rw [Finset.sum_congr rfl e, ← Finset.sum_div]
  have := sum_choose_abs (m + 1)
  rw [show m + 1 + 1 = m + 2 by ring] at this
  rw [div_le_div_iff₀ hm (Real.sqrt_pos.2 hm)]
  calc _ ≤ 2 ^ (m + 1) * Real.sqrt ((m + 1 : ℕ) : ℝ) * Real.sqrt (m + 1) :=
        mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg _)
    _ = 2 ^ (m + 1) * (m + 1) := by
        push_cast; rw [mul_assoc, Real.mul_self_sqrt hm.le]

/-! ## The two-point walk -/

/-- `δ_{-b} + δ_b`. -/
def sB (b : ℝ) : Meas := single (-b) 1 + single b 1

/-- `δ_{-b} - δ_b`. -/
def dB (b : ℝ) : Meas := single (-b) 1 - single b 1

theorem natCast_meas (n : ℕ) : (n : Meas) = single 0 (n : ℝ) := by
  apply AddMonoidAlgebra.coeff_injective
  rw [AddMonoidAlgebra.coeff_natCast, AddMonoidAlgebra.coeff_single]

theorem sB_pow (b : ℝ) (m : ℕ) :
    sB b ^ m = ∑ j ∈ range (m + 1), single (((m : ℝ) - 2 * j) * b) (m.choose j : ℝ) := by
  rw [sB, add_pow]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ m := by simp at hj; omega
  rw [AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_pow, natCast_meas,
    AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.single_mul_single]
  congr 1
  · simp only [nsmul_eq_mul, Nat.cast_sub hj', add_zero]; ring
  · simp

theorem single_sub' (z u v : ℝ) : (single z (u - v) : Meas) = single z u - single z v := by
  apply AddMonoidAlgebra.coeff_injective
  simp [AddMonoidAlgebra.coeff_single]

theorem dB_mul_sB_pow (b : ℝ) (m : ℕ) :
    dB b * sB b ^ m = ∑ j ∈ range (m + 2), single (((m + 1 : ℝ) - 2 * j) * b) (alt m j) := by
  rw [sB_pow, Finset.mul_sum, dB]
  simp only [sub_mul, AddMonoidAlgebra.single_mul_single, one_mul, Finset.sum_sub_distrib, alt,
    single_sub']
  rw [show m + 2 = m + 1 + 1 by ring]
  congr 1
  · conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.succ_ne_zero, if_false, Nat.add_sub_cancel, if_true]
    rw [show (single (((m : ℝ) + 1) * b - 2 * ((0 : ℕ) : ℝ) * b) (0 : ℝ) : Meas) = 0 by
      apply AddMonoidAlgebra.coeff_injective; simp [AddMonoidAlgebra.coeff_single], add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; push_cast; ring
  · conv_rhs => rw [Finset.sum_range_succ, Nat.choose_eq_zero_of_lt (show m < m + 1 by omega)]
    rw [show (single (((m : ℝ) + 1) * b - 2 * ((m + 1 : ℕ) : ℝ) * b) ((0 : ℕ) : ℝ) : Meas) = 0 by
      apply AddMonoidAlgebra.coeff_injective; simp [AddMonoidAlgebra.coeff_single], add_zero]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1; ring

/-- **`tv ((δ_{-b} - δ_b)(δ_{-b} + δ_b)^m) ≤ 2^{m+1}/√(m+1)`.** -/
theorem tv_dB_sB_pow (b : ℝ) (m : ℕ) : tv (dB b * sB b ^ m) ≤ 2 ^ (m + 1) / Real.sqrt (m + 1) := by
  rw [dB_mul_sB_pow]
  refine (tv_sum_le _ _).trans ?_
  simp only [tv_single]
  exact sum_abs_alt m


theorem tv_sB (b : ℝ) : tv (sB b) ≤ 2 := by
  refine (tv_add_le _ _).trans ?_; rw [tv_single, tv_single]; norm_num

/-- **Block bound.** `tv (d^q s^k) ≤ 2^{k+q} (√q / √(k+1))^q` for `q ≥ 1`. -/
theorem tv_dB_pow_sB_pow (b : ℝ) {q : ℕ} (hq : 1 ≤ q) (k : ℕ) :
    tv (dB b ^ q * sB b ^ k) ≤ 2 ^ (k + q) * (Real.sqrt q / Real.sqrt (k + 1)) ^ q := by
  set m := k / q
  set r0 := k % q
  have hk : k = q * m + r0 := (Nat.div_add_mod k q).symm
  have hr0 : r0 < q := Nat.mod_lt _ (by omega)
  have e : dB b ^ q * sB b ^ k = (dB b * sB b ^ m) ^ q * sB b ^ r0 := by
    rw [mul_pow, ← pow_mul, mul_assoc, ← pow_add, mul_comm m q, ← hk]
  rw [e]
  have h1 := tv_mul_le ((dB b * sB b ^ m) ^ q) (sB b ^ r0)
  have h2 := tv_pow_le (dB b * sB b ^ m) q
  have h3 := tv_pow_le (sB b) r0
  have h4 := tv_dB_sB_pow b m
  have h5 := tv_sB b
  have hm1 : (0 : ℝ) < m + 1 := by positivity
  have hs : 0 < Real.sqrt (m + 1) := Real.sqrt_pos.2 hm1
  have b1 : tv ((dB b * sB b ^ m) ^ q) ≤ (2 ^ (m + 1) / Real.sqrt (m + 1)) ^ q :=
    h2.trans (pow_le_pow_left₀ (tv_nonneg _) h4 q)
  have b2 : tv (sB b ^ r0) ≤ 2 ^ r0 := h3.trans (pow_le_pow_left₀ (tv_nonneg _) h5 r0)
  have b3 : tv ((dB b * sB b ^ m) ^ q * sB b ^ r0) ≤
      (2 ^ (m + 1) / Real.sqrt (m + 1)) ^ q * 2 ^ r0 :=
    h1.trans (mul_le_mul b1 b2 (tv_nonneg _) (by positivity))
  calc _ ≤ _ := b3
    _ = 2 ^ (k + q) * (1 / Real.sqrt (m + 1)) ^ q := by
        rw [div_pow, div_pow, one_pow, ← pow_mul, hk]; field_simp; ring
    _ ≤ _ := by
      refine mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ q) (by positivity)
      rw [div_le_div_iff₀ hs (Real.sqrt_pos.2 (by positivity)), one_mul, ← Real.sqrt_mul (by positivity)]
      refine Real.sqrt_le_sqrt ?_
      have : (k : ℝ) + 1 ≤ q * (m + 1) := by
        have : k + 1 ≤ q * (m + 1) := by rw [hk]; nlinarith
        exact_mod_cast this
      linarith

/-! ## Binomial averages -/

theorem binom_sum (ρ : ℝ) (n : ℕ) :
    ∑ k ∈ range (n + 1), (n.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (n - k) = 1 := by
  calc _ = ∑ k ∈ range (n + 1), ρ ^ k * (1 - ρ) ^ (n - k) * (n.choose k : ℝ) :=
        Finset.sum_congr rfl fun k _ => by ring
    _ = (ρ + (1 - ρ)) ^ n := (add_pow ρ (1 - ρ) n).symm
    _ = 1 := by rw [add_sub_cancel, one_pow]

theorem binom_term_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n k : ℕ) :
    0 ≤ (n.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (n - k) := by
  have : 0 ≤ 1 - ρ := by linarith
  positivity

/-- `E[1/(K+1)] ≤ 1/(ρ(r+1))` for `K ~ Bin(r, ρ)`. -/
theorem binom_inv {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (r : ℕ) :
    ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) ≤
      1 / (ρ * (r + 1)) := by
  have hpos : 0 < ρ * (r + 1) := by positivity
  rw [le_div_iff₀ hpos, Finset.sum_mul]
  have e : ∀ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) *
      (ρ * (r + 1)) = ((r + 1).choose (k + 1) : ℝ) * ρ ^ (k + 1) * (1 - ρ) ^ (r + 1 - (k + 1)) :=
    fun k _ => by
      have := Nat.add_one_mul_choose_eq r k
      have h : ((r : ℝ) + 1) * r.choose k = ((r + 1).choose (k + 1) : ℝ) * (k + 1) := by
        exact_mod_cast this
      rw [show r + 1 - (k + 1) = r - k by omega]
      field_simp
      linear_combination ρ * ρ ^ k * (1 - ρ) ^ (r - k) * h
  rw [Finset.sum_congr rfl e]
  have hs := binom_sum ρ (r + 1)
  rw [Finset.sum_range_succ'] at hs
  have : 0 ≤ ((r + 1).choose 0 : ℝ) * ρ ^ 0 * (1 - ρ) ^ (r + 1 - 0) := binom_term_nonneg h0.le h1 _ _
  linarith

/-- `E[1/(K+1)²] ≤ 2/(ρ²(r+1)(r+2))`. -/
theorem binom_inv_sq {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) (r : ℕ) :
    ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) ^ 2 ≤
      2 / (ρ ^ 2 * ((r + 1) * (r + 2))) := by
  have hpos : 0 < ρ ^ 2 * ((r + 1) * (r + 2)) := by positivity
  have step : ∀ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) ^ 2 ≤
      2 * (((r + 2).choose (k + 2) : ℝ) * ρ ^ (k + 2) * (1 - ρ) ^ (r + 2 - (k + 2))) /
        (ρ ^ 2 * ((r + 1) * (r + 2))) := fun k _ => by
    have c1 := Nat.add_one_mul_choose_eq r k
    have c2 := Nat.add_one_mul_choose_eq (r + 1) (k + 1)
    have h1' : ((r : ℝ) + 1) * r.choose k = ((r + 1).choose (k + 1) : ℝ) * (k + 1) := by
      exact_mod_cast c1
    have h2' : ((r : ℝ) + 1 + 1) * (r + 1).choose (k + 1) = ((r + 2).choose (k + 2) : ℝ) * (k + 1 + 1) := by
      exact_mod_cast c2
    have key : (r.choose k : ℝ) * ((r + 1) * (r + 2)) = ((r + 2).choose (k + 2) : ℝ) * ((k + 1) * (k + 2)) := by
      linear_combination (r + 2) * h1' + (k + 1) * h2'
    rw [show r + 2 - (k + 2) = r - k by omega, le_div_iff₀ hpos]
    have hk : (0 : ℝ) < k + 1 := by positivity
    have hle : (1 / ((k : ℝ) + 1)) ^ 2 * ((k + 1) * (k + 2)) ≤ 2 := by
      rw [div_pow, one_pow, div_mul_eq_mul_div, one_mul, div_le_iff₀ (by positivity)]; nlinarith
    calc (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) ^ 2 * (ρ ^ 2 * ((r + 1) * (r + 2)))
        = ((r + 2).choose (k + 2) : ℝ) * ρ ^ (k + 2) * (1 - ρ) ^ (r - k) *
            ((1 / ((k : ℝ) + 1)) ^ 2 * ((k + 1) * (k + 2))) := by
          rw [show (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) ^ 2 *
            (ρ ^ 2 * ((r + 1) * (r + 2))) = (r.choose k : ℝ) * ((r + 1) * (r + 2)) * ρ ^ (k + 2) *
            (1 - ρ) ^ (r - k) * (1 / (k + 1)) ^ 2 by ring, key]; ring
      _ ≤ ((r + 2).choose (k + 2) : ℝ) * ρ ^ (k + 2) * (1 - ρ) ^ (r - k) * 2 :=
          mul_le_mul_of_nonneg_left hle (by
            have : 0 ≤ 1 - ρ := by linarith
            positivity)
      _ = _ := by ring
  refine (Finset.sum_le_sum step).trans ?_
  rw [← Finset.sum_div, ← Finset.mul_sum, div_le_div_iff_of_pos_right hpos]
  have hs := binom_sum ρ (r + 2)
  rw [Finset.sum_range_succ', Finset.sum_range_succ'] at hs
  have t0 := binom_term_nonneg h0.le h1 (r + 2) 0
  have t1 := binom_term_nonneg h0.le h1 (r + 2) 1
  simp only [zero_add] at t0 t1 hs
  have : ∑ k ∈ range (r + 1), ((r + 2).choose (k + 2) : ℝ) * ρ ^ (k + 2) * (1 - ρ) ^ (r + 2 - (k + 2)) ≤ 1 := by
    simp only [show ∀ k : ℕ, k + 1 + 1 = k + 2 from fun k => rfl] at hs
    linarith
  linarith


theorem tv_algebraMap (t : ℝ) : tv (algebraMap ℝ Meas t) = |t| := by
  have : algebraMap ℝ Meas t = single 0 t := by
    rw [AddMonoidAlgebra.coe_algebraMap]; rfl
  rw [this, tv_single]

/-- **Binomial mixture bound.** If `β = ρ δ_c (δ_{-b} + δ_b)/2 + ζ` with `tv ζ ≤ 1 - ρ`, then
`tv (d^q β^r) ≤ 2^q E[(√q/√(K+1))^q]`, `K ~ Bin(r, ρ)`. -/
theorem tv_mixture (b c : ℝ) {q : ℕ} (hq : 1 ≤ q) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {ζ : Meas}
    (hζ : tv ζ ≤ 1 - ρ) (r : ℕ) :
    tv (dB b ^ q * (ρ • (single c (1 / 2) * sB b) + ζ) ^ r) ≤
      2 ^ q * ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) *
        (Real.sqrt q / Real.sqrt (k + 1)) ^ q := by
  rw [add_pow, Finset.mul_sum, Finset.mul_sum]
  refine (tv_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  have e : dB b ^ q * ((ρ • (single c (1 / 2) * sB b)) ^ k * ζ ^ (r - k) * (r.choose k : Meas)) =
      algebraMap ℝ Meas (ρ ^ k) * single (k • c) ((1 / 2 : ℝ) ^ k) * (dB b ^ q * sB b ^ k) *
        ζ ^ (r - k) * (r.choose k : Meas) := by
    rw [smul_pow, Algebra.smul_def, mul_pow, AddMonoidAlgebra.single_pow]; ring
  rw [e]
  have hρ' : 0 ≤ 1 - ρ := by linarith
  have t1 := tv_mul_le (algebraMap ℝ Meas (ρ ^ k) * single (k • c) ((1 / 2 : ℝ) ^ k) *
    (dB b ^ q * sB b ^ k) * ζ ^ (r - k)) (r.choose k : Meas)
  have t2 := tv_mul_le (algebraMap ℝ Meas (ρ ^ k) * single (k • c) ((1 / 2 : ℝ) ^ k) *
    (dB b ^ q * sB b ^ k)) (ζ ^ (r - k))
  have t3 := tv_mul_le (algebraMap ℝ Meas (ρ ^ k) * single (k • c) ((1 / 2 : ℝ) ^ k))
    (dB b ^ q * sB b ^ k)
  have t4 := tv_mul_le (algebraMap ℝ Meas (ρ ^ k)) (single (k • c) ((1 / 2 : ℝ) ^ k))
  rw [tv_algebraMap, tv_single, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at t4
  have t5 := tv_dB_pow_sB_pow b hq k
  have t6 : tv (ζ ^ (r - k)) ≤ (1 - ρ) ^ (r - k) :=
    (tv_pow_le _ _).trans (pow_le_pow_left₀ (tv_nonneg _) hζ _)
  have t7 : tv (r.choose k : Meas) = r.choose k := by
    rw [natCast_meas, tv_single, abs_of_nonneg (Nat.cast_nonneg _)]
  rw [t7] at t1
  have n1 := tv_nonneg (algebraMap ℝ Meas (ρ ^ k) * single (k • c) ((1 / 2 : ℝ) ^ k))
  have n2 := tv_nonneg (dB b ^ q * sB b ^ k)
  have n3 := tv_nonneg (ζ ^ (r - k))
  have hX : 0 ≤ (Real.sqrt q / Real.sqrt (k + 1)) ^ q := by positivity
  have hpow : (2 : ℝ) ^ (k + q) * (1 / 2) ^ k = 2 ^ q := by
    rw [pow_add, one_div, inv_pow]; field_simp
  calc _ ≤ _ := t1
    _ ≤ ρ ^ k * (1 / 2) ^ k * (2 ^ (k + q) * (Real.sqrt q / Real.sqrt (k + 1)) ^ q) *
          (1 - ρ) ^ (r - k) * r.choose k := by
        refine mul_le_mul_of_nonneg_right (t2.trans ?_) (Nat.cast_nonneg _)
        refine mul_le_mul (t3.trans ?_) t6 n3 (by positivity)
        exact mul_le_mul t4 t5 n2 (by positivity)
    _ = _ := by
        rw [show ρ ^ k * (1 / 2) ^ k * (2 ^ (k + q) * (Real.sqrt q / Real.sqrt (k + 1)) ^ q) *
          (1 - ρ) ^ (r - k) * r.choose k = (2 ^ (k + q) * (1 / 2) ^ k) * ((r.choose k : ℝ) *
          ρ ^ k * (1 - ρ) ^ (r - k) * (Real.sqrt q / Real.sqrt (k + 1)) ^ q) by ring, hpow]


/-- The law `ρ δ_c (δ_{-b}+δ_b)/2 + ζ`. -/
def mix (ρ b c : ℝ) (ζ : Meas) : Meas := ρ • (single c (1 / 2) * sB b) + ζ

theorem sqrt_div_sq (q k : ℕ) (n : ℕ) :
    (Real.sqrt q / Real.sqrt (k + 1)) ^ (2 * n) = ((q : ℝ) / (k + 1)) ^ n := by
  rw [pow_mul, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (by positivity), div_pow]

/-- **TV decay, `q = 2`.** -/
theorem tv_decay_two (b c : ℝ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {ζ : Meas}
    (hζ : tv ζ ≤ 1 - ρ) (r : ℕ) :
    tv (dB b ^ 2 * mix ρ b c ζ ^ r) ≤ 8 / (ρ * (r + 1)) := by
  refine (tv_mixture b c (by norm_num) h0 h1 hζ r).trans ?_
  have e : ∀ k : ℕ, (Real.sqrt (2 : ℕ) / Real.sqrt (k + 1)) ^ 2 = 2 * (1 / (k + 1)) := fun k => by
    rw [show (2 : ℕ) = 2 * 1 from rfl, sqrt_div_sq]; push_cast; ring
  simp only [e]
  have := binom_inv h0 h1 r
  have e2 : ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (2 * (1 / (k + 1))) =
      2 * ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e2]
  calc (2 : ℝ) ^ 2 * (2 * _) ≤ 2 ^ 2 * (2 * (1 / (ρ * (r + 1)))) := by gcongr
    _ = 8 / (ρ * (r + 1)) := by ring

/-- **TV decay, `q = 4`.** -/
theorem tv_decay_four (b c : ℝ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {ζ : Meas}
    (hζ : tv ζ ≤ 1 - ρ) (r : ℕ) :
    tv (dB b ^ 4 * mix ρ b c ζ ^ r) ≤ 512 / (ρ ^ 2 * ((r + 1) * (r + 2))) := by
  refine (tv_mixture b c (by norm_num) h0 h1 hζ r).trans ?_
  have e : ∀ k : ℕ, (Real.sqrt (4 : ℕ) / Real.sqrt (k + 1)) ^ 4 = 16 * (1 / (k + 1)) ^ 2 := fun k => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, sqrt_div_sq]; push_cast; ring
  simp only [e]
  have := binom_inv_sq h0 h1 r
  have e2 : ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (16 * (1 / (k + 1)) ^ 2) =
      16 * ∑ k ∈ range (r + 1), (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k) * (1 / (k + 1)) ^ 2 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e2]
  calc (2 : ℝ) ^ 4 * (16 * _) ≤ 2 ^ 4 * (16 * (2 / (ρ ^ 2 * ((r + 1) * (r + 2))))) := by gcongr
    _ = 512 / (ρ ^ 2 * ((r + 1) * (r + 2))) := by ring

/-- **TV decay, `q = 3`.** -/
theorem tv_decay_three (b c : ℝ) {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ ≤ 1) {ζ : Meas}
    (hζ : tv ζ ≤ 1 - ρ) (r : ℕ) :
    tv (dB b ^ 3 * mix ρ b c ζ ^ r) ≤
      24 * Real.sqrt 3 * Real.sqrt (1 / (ρ * (r + 1)) * (2 / (ρ ^ 2 * ((r + 1) * (r + 2))))) := by
  refine (tv_mixture b c (by norm_num) h0 h1 hζ r).trans ?_
  set w : ℕ → ℝ := fun k => (r.choose k : ℝ) * ρ ^ k * (1 - ρ) ^ (r - k)
  have hw : ∀ k, 0 ≤ w k := fun k => binom_term_nonneg h0.le h1 r k
  set x : ℕ → ℝ := fun k => 1 / Real.sqrt (k + 1)
  have hx : ∀ k, 0 ≤ x k := fun k => by positivity
  have hx2 : ∀ k : ℕ, x k ^ 2 = 1 / (k + 1) := fun k => by
    simp only [x, div_pow, one_pow]; rw [Real.sq_sqrt (by positivity)]
  have e : ∀ k : ℕ, (Real.sqrt (3 : ℕ) / Real.sqrt (k + 1)) ^ 3 = 3 * Real.sqrt 3 * x k ^ 3 := fun k => by
    simp only [x, div_pow, one_pow]; push_cast
    rw [show Real.sqrt 3 ^ 3 = Real.sqrt 3 ^ 2 * Real.sqrt 3 by ring, Real.sq_sqrt (by norm_num)]
    ring
  simp only [e]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq (range (r + 1)) (fun k => Real.sqrt (w k) * x k)
    (fun k => Real.sqrt (w k) * x k ^ 2)
  have f1 : ∀ k, Real.sqrt (w k) * x k * (Real.sqrt (w k) * x k ^ 2) = w k * x k ^ 3 := fun k => by
    rw [show Real.sqrt (w k) * x k * (Real.sqrt (w k) * x k ^ 2) =
      (Real.sqrt (w k) * Real.sqrt (w k)) * x k ^ 3 by ring, Real.mul_self_sqrt (hw k)]
  have f2 : ∀ k, (Real.sqrt (w k) * x k) ^ 2 = w k * (1 / (k + 1)) := fun k => by
    rw [mul_pow, Real.sq_sqrt (hw k), hx2]
  have f3 : ∀ k, (Real.sqrt (w k) * x k ^ 2) ^ 2 = w k * (1 / (k + 1)) ^ 2 := fun k => by
    rw [mul_pow, Real.sq_sqrt (hw k), ← pow_mul, show 2 * 2 = 2 * 2 from rfl, pow_mul, hx2]
  simp only [f1, f2, f3] at cs
  have A := binom_inv h0 h1 r
  have B := binom_inv_sq h0 h1 r
  have hS : 0 ≤ ∑ k ∈ range (r + 1), w k * x k ^ 3 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (pow_nonneg (hx k) 3)
  have hA0 : 0 ≤ ∑ k ∈ range (r + 1), w k * (1 / (k + 1)) :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (by positivity)
  have hB0 : 0 ≤ ∑ k ∈ range (r + 1), w k * (1 / (k + 1)) ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw k) (by positivity)
  have key : ∑ k ∈ range (r + 1), w k * x k ^ 3 ≤
      Real.sqrt (1 / (ρ * (r + 1)) * (2 / (ρ ^ 2 * ((r + 1) * (r + 2))))) := by
    refine Real.le_sqrt_of_sq_le (cs.trans ?_)
    exact mul_le_mul A B hB0 (by positivity)
  have e2 : ∑ k ∈ range (r + 1), w k * (3 * Real.sqrt 3 * x k ^ 3) =
      3 * Real.sqrt 3 * ∑ k ∈ range (r + 1), w k * x k ^ 3 := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  rw [e2]
  calc (2 : ℝ) ^ 3 * (3 * Real.sqrt 3 * _) ≤ 2 ^ 3 * (3 * Real.sqrt 3 *
        Real.sqrt (1 / (ρ * (r + 1)) * (2 / (ρ ^ 2 * ((r + 1) * (r + 2)))))) := by gcongr
    _ = _ := by ring


theorem tv_dB (b : ℝ) : tv (dB b) ≤ 2 := by
  refine (tv_sub_le _ _).trans ?_; rw [tv_single, tv_single]; norm_num

/-- `δ_{-Lb} - δ_{Lb} = ν_L * (δ_{-b} - δ_b)` with `ν_L` of total variation `L`. -/
theorem dB_scale (b : ℝ) (L : ℕ) :
    dB (L * b) = (∑ l ∈ range L, single (-(L * b) + b + 2 * b * l) (1 : ℝ)) * dB b := by
  rw [Finset.sum_mul]
  simp only [dB, mul_sub, AddMonoidAlgebra.single_mul_single, one_mul]
  have := Finset.sum_range_sub' (fun l : ℕ => (single (-(L * b) + 2 * b * l) (1 : ℝ) : Meas)) L
  simp only [Nat.cast_zero, mul_zero, add_zero, Nat.cast_add, Nat.cast_one] at this
  rw [show -(↑L * b) + 2 * b * ↑L = ↑L * b by ring] at this
  rw [← this]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2 <;> ring

theorem tv_dB_scale_pow (b : ℝ) (L : ℕ) (q : ℕ) (X : Meas) :
    tv (dB (L * b) ^ q * X) ≤ (L : ℝ) ^ q * tv (dB b ^ q * X) := by
  rw [dB_scale, mul_pow, mul_assoc]
  refine (tv_mul_le _ _).trans (mul_le_mul_of_nonneg_right ((tv_pow_le _ _).trans ?_) (tv_nonneg _))
  refine pow_le_pow_left₀ (tv_nonneg _) ((tv_sum_le _ _).trans (le_of_eq ?_)) q
  rw [Finset.sum_congr rfl (fun l _ => by rw [tv_single, abs_one])]
  simp

end CausalSpectrum.Sqrt.Decay

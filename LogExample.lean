/-
The dyadic information pair of the logarithmic-coefficient analysis:
`P = (1/4, 1/16 × 12)` and `Q = (1/8 × 6, 1/32 × 8)`. Both have entropy `7/2` bits and
information variance `3/4`; the centered third moments are `-3/4` and `3/4`. By the moment
classification, `C_n - 7n/2` is of exact order `log n`. The analytic coefficient
`(κ₊ - κ₋)/(3 v √(2πe)) = 2/(3√(2πe))` lies in `(0.1613, 0.1614)`.
-/
import CausalSeed.LogWidth
import Mathlib.Analysis.Real.Pi.Bounds

noncomputable section
open Classical Filter Topology
namespace CausalSpectrum.Kernel.LogPair

/-- Number of outputs: 13 for `P`, 14 for `Q`. -/
def nY (a : Fin 2) : ℕ := if a = 0 then 13 else 14

/-- Surprisal (in bits) of output `k` of action `a`. -/
def e (a : Fin 2) (k : ℕ) : ℕ := if a = 0 then (if k = 0 then 2 else 4) else (if k < 6 then 3 else 5)

def w (a : Fin 2) (k : ℕ) : ℝ := ((2 : ℝ) ^ e a k)⁻¹

/-- The kernel `(P, Q)`. -/
abbrev κ : Kernel where
  nA := 2
  hA := by norm_num
  nY := nY
  hY := fun a => by unfold nY; split_ifs <;> norm_num
  K := fun a y => w a y.val
  Kpos := fun a y => by unfold w; positivity
  Ksum := fun a => by
    rw [Fin.sum_univ_eq_sum_range (w a)]
    fin_cases a <;> simp [nY, w, e, Finset.sum_range_succ] <;> norm_num

theorem infoMass_w (a : Fin 2) (k : ℕ) : infoMass (w a k) = e a k := by
  change -Real.logb 2 ((2 : ℝ) ^ e a k)⁻¹ = _
  rw [Real.logb_inv, neg_neg, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

theorem sum_pow (a : Fin 2) (h : ℝ) (m : ℕ) :
    ∑ y, κ.K a y * (infoMass (κ.K a y) - h) ^ m =
      ∑ k ∈ Finset.range (nY a), w a k * ((e a k : ℝ) - h) ^ m := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => w a k * ((e a k : ℝ) - h) ^ m)]
  exact Finset.sum_congr rfl fun y _ => by rw [infoMass_w]

/-- Both actions have entropy `7/2` bits. -/
theorem equalEntropy : κ.EqualEntropy (7 / 2) := by
  intro a
  have := sum_pow a 0 1
  simp only [sub_zero, pow_one] at this
  change ∑ y, κ.K a y * infoMass (κ.K a y) = _
  rw [this]
  fin_cases a <;> simp [nY, w, e, Finset.sum_range_succ] <;> norm_num

/-- Both information variances equal `3/4`. -/
theorem sig2_eq (a : Fin 2) : (κ.fam (7 / 2)).sig2 a = 3 / 4 := by
  unfold Sqrt.IncFamily.sig2
  rw [show (∑ y, (κ.fam (7 / 2)).P a y * (κ.fam (7 / 2)).X a y ^ 2) =
    ∑ y, κ.K a y * (infoMass (κ.K a y) - 7 / 2) ^ 2 from rfl, sum_pow]
  fin_cases a <;> simp [nY, w, e, Finset.sum_range_succ] <;> norm_num

/-- Centered third moments `κ_P = -3/4`, `κ_Q = 3/4`. -/
theorem m3_P : (κ.fam (7 / 2)).m3 0 = -3 / 4 := by
  unfold Sqrt.IncFamily.m3
  rw [show (∑ y, (κ.fam (7 / 2)).P 0 y * (κ.fam (7 / 2)).X 0 y ^ 3) =
    ∑ y, κ.K 0 y * (infoMass (κ.K 0 y) - 7 / 2) ^ 3 from rfl, sum_pow]
  simp [nY, w, e, Finset.sum_range_succ]; norm_num

theorem m3_Q : (κ.fam (7 / 2)).m3 1 = 3 / 4 := by
  unfold Sqrt.IncFamily.m3
  rw [show (∑ y, (κ.fam (7 / 2)).P 1 y * (κ.fam (7 / 2)).X 1 y ^ 3) =
    ∑ y, κ.K 1 y * (infoMass (κ.K 1 y) - 7 / 2) ^ 3 from rfl, sum_pow]
  simp [nY, w, e, Finset.sum_range_succ]; norm_num

/-- **Logarithmic order.** `c log n ≤ C_n - 7n/2 ≤ C log n` (and the same for `L_n`) for all
large `n`. -/
theorem excess_log_theta :
    ∃ c > 0, ∃ C, ∀ᶠ n : ℕ in atTop,
      (c * Real.log n ≤ envelopeMean (κ.rounds n) - n * (7 / 2) ∧
        envelopeMean (κ.rounds n) - n * (7 / 2) ≤ C * Real.log n) ∧
      (c * Real.log n ≤ κ.costBits n - n * (7 / 2) ∧
        κ.costBits n - n * (7 / 2) ≤ C * Real.log n) :=
  κ.excess_log_theta equalEntropy (fun j k => by rw [sig2_eq, sig2_eq])
    (j := 0) (k := 1) (by rw [m3_P, m3_Q]; norm_num)

/-- **Width bound for the pair.** `e_n ≤ C(1 + log n)` and `w_n ≤ C(1 + log n)`. -/
theorem width_log_upper :
    ∃ C, ∀ n : ℕ, (κ.fam (7 / 2)).eG ((κ.fam (7 / 2)).G n) ≤ C * (1 + Real.log n) ∧
      (κ.fam (7 / 2)).Wint n ≤ ENNReal.ofReal (C * (1 + Real.log n)) :=
  (κ.fam (7 / 2)).width_log_upper (κ.fam_centered equalEntropy) (by norm_num : (0:ℝ) < 3 / 4)
    sig2_eq

/-- The predicted coefficient `(κ₊ - κ₋)/(3 v √(2πe))` for this pair. -/
def coeff : ℝ := (3 / 4 - (-3 / 4)) / (3 * (3 / 4) * Real.sqrt (2 * Real.pi * Real.exp 1))

theorem coeff_eq : coeff = 2 / (3 * Real.sqrt (2 * Real.pi * Real.exp 1)) := by
  unfold coeff; field_simp; ring

/-- `0.1613 < 2/(3√(2πe)) < 0.1614`. -/
theorem coeff_bounds : 0.1613 < coeff ∧ coeff < 0.1614 := by
  rw [coeff_eq]
  have hp1 := Real.pi_gt_d4
  have hp2 := Real.pi_lt_d4
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  set s := Real.sqrt (2 * Real.pi * Real.exp 1)
  have hs2 : s ^ 2 = 2 * Real.pi * Real.exp 1 := Real.sq_sqrt (by positivity)
  have hs0 : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hlo : 2 * Real.pi * Real.exp 1 < 17.0823 := by nlinarith
  have hhi : 17.0612 < 2 * Real.pi * Real.exp 1 := by nlinarith
  constructor
  · rw [lt_div_iff₀ (by positivity)]; nlinarith
  · rw [div_lt_iff₀ (by positivity)]; nlinarith

end CausalSpectrum.Kernel.LogPair

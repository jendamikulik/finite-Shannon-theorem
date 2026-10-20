/-
Stage 6: the seed-entropy corollary and the dyadic pair.

The centered envelope of a kernel with common entropy `h` is `G_n` of the surprisal family,
and `L_n - nh = e_n`. With the finite-tree sandwich `L_n ≤ C_n ≤ L_n + c⋆` the sharp
coefficient of `e_n` transfers to the optimal seed entropy `C_n` (bits).
-/
import CausalSeed.LogFinal
import CausalSeed.LogExample
import CausalSeed.DyadicKernel

open Real

namespace CausalSpectrum.Kernel
open LogGauss

variable (κ : Kernel)

/-- `√(ln n · ln ln n) ≥ 1` for `n ≥ 16`. -/
theorem one_le_sqrt_loglog {n : ℕ} (hn : 16 ≤ n) : 1 ≤ √(log n * log (log n)) := by
  obtain ⟨hL, hℓ, -, -⟩ := log_facts hn
  have : 1 ≤ log (n:ℝ) := by linarith [Real.exp_one_gt_d9]
  exact Real.one_le_sqrt.2 (by nlinarith)

/-- **Corollary (causal seed entropy).** For a finite stationary kernel whose action laws have
common entropy `h` (bits) and common information variance `v > 0`, with
`κ_i = E(-log₂ P_i(Y_i) - h)³`, `κ₊ = max κ_i`, `κ₋ = min κ_i`, there is `C` such that for all
`n ≥ 16`
`|C_n - nh - (κ₊ - κ₋)/(3v√(2πe)) ln n| ≤ C √(ln n ln ln n)`, and the same for the lower
envelope mean `L_n`. -/
theorem cost_sharp {h v : ℝ} (hh : κ.EqualEntropy h) (hv : 0 < v)
    (hσ : ∀ a, (κ.fam h).sig2 a = v) :
    ∃ C, ∀ n : ℕ, 16 ≤ n →
      |κ.costBits n - n * h - (kmax (κ.fam h) - kmin (κ.fam h)) / (3 * v * √(2 * π * exp 1)) *
          log n| ≤ C * √(log n * log (log n)) ∧
      |envelopeMean (κ.rounds n) - n * h -
          (kmax (κ.fam h) - kmin (κ.fam h)) / (3 * v * √(2 * π * exp 1)) * log n| ≤
        C * √(log n * log (log n)) := by
  obtain ⟨C, hC⟩ := main_mean (κ.fam h) v (κ.fam_centered hh) hv hσ
  refine ⟨|C| + shannonOverhead, fun n hn => ?_⟩
  have hQ := one_le_sqrt_loglog hn
  have hso : 0 ≤ shannonOverhead := by unfold shannonOverhead; positivity
  rw [← cdrift_eq (κ.fam h) v hv]
  have e := κ.envelope_sub_eq_eG hh (n := n) (by omega)
  have hm := (hC n hn).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith))
  obtain ⟨s1, s2⟩ := κ.costBits_sandwich n
  rw [← e] at hm
  set Q := √(log n * log (log n))
  have hCQ : 0 ≤ |C| * Q := mul_nonneg (abs_nonneg _) (by linarith)
  constructor
  · rw [abs_le] at hm ⊢
    constructor <;> nlinarith
  · exact hm.trans (by nlinarith)

/-- Any sequence within a bounded additive amount of `L_n` (for example the entropies of exact
seeds within `D` bits of the envelope mean) has the same expansion. -/
theorem near_envelope_sharp {h v : ℝ} (hh : κ.EqualEntropy h) (hv : 0 < v)
    (hσ : ∀ a, (κ.fam h).sig2 a = v) {D : ℝ} (s : ℕ → ℝ)
    (hs : ∀ n, |s n - envelopeMean (κ.rounds n)| ≤ D) :
    ∃ C, ∀ n : ℕ, 16 ≤ n →
      |s n - n * h - (kmax (κ.fam h) - kmin (κ.fam h)) / (3 * v * √(2 * π * exp 1)) * log n| ≤
        C * √(log n * log (log n)) := by
  obtain ⟨C, hC⟩ := κ.cost_sharp hh hv hσ
  refine ⟨|C| + |D|, fun n hn => ?_⟩
  have hQ := one_le_sqrt_loglog hn
  have h2 := (hC n hn).2
  have h3 := hs n
  set Q := √(log n * log (log n))
  have a1 : C * Q ≤ |C| * Q := mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have a2 : D ≤ |D| * Q := (le_abs_self D).trans (le_mul_of_one_le_right (abs_nonneg D) hQ)
  calc _ = |(s n - envelopeMean (κ.rounds n)) + (envelopeMean (κ.rounds n) - n * h -
        (kmax (κ.fam h) - kmin (κ.fam h)) / (3 * v * √(2 * π * exp 1)) * log n)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (by nlinarith)

end CausalSpectrum.Kernel

namespace CausalSpectrum.Kernel.LogPair
open LogGauss

theorem isDyadic : κ.IsDyadic := fun a y =>
  ⟨e a y.val, by simp [κ, w, Dyadic.wt, inv_pow]⟩

theorem kmax_eq : kmax (κ.fam (7 / 2)) = 3 / 4 := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun a _ => ?_
    fin_cases a
    · show (κ.fam (7 / 2)).m3 0 ≤ 3 / 4; rw [m3_P]; norm_num
    · show (κ.fam (7 / 2)).m3 1 ≤ 3 / 4; rw [m3_Q]
  · rw [← m3_Q]; exact Finset.le_sup' _ (Finset.mem_univ _)

theorem kmin_eq : kmin (κ.fam (7 / 2)) = -3 / 4 := by
  apply le_antisymm
  · rw [← m3_P]; exact Finset.inf'_le _ (Finset.mem_univ _)
  · refine Finset.le_inf' _ _ fun a _ => ?_
    fin_cases a
    · show -3 / 4 ≤ (κ.fam (7 / 2)).m3 0; rw [m3_P]
    · show -3 / 4 ≤ (κ.fam (7 / 2)).m3 1; rw [m3_Q]; norm_num

/-- **The dyadic pair.** `C_n = L_n` at every horizon, and
`C_n = 7n/2 + 2/(3√(2πe)) ln n + O(√(ln n ln ln n))`: for all `n ≥ 16`,
`|C_n - 7n/2 - coeff · ln n| ≤ C √(ln n ln ln n)`, with `coeff = 2/(3√(2πe)) ∈ (0.1613, 0.1614)`. -/
theorem cost_sharp :
    ∃ C, ∀ n : ℕ, 16 ≤ n →
      κ.costBits n = envelopeMean (κ.rounds n) ∧
      |κ.costBits n - n * (7 / 2) - coeff * log n| ≤ C * √(log n * log (log n)) := by
  obtain ⟨C, hC⟩ := κ.cost_sharp equalEntropy (by norm_num : (0:ℝ) < 3 / 4) sig2_eq
  refine ⟨C, fun n hn => ⟨κ.cost_eq_envelope_of_dyadic isDyadic n, ?_⟩⟩
  have := (hC n hn).1
  rw [kmax_eq, kmin_eq] at this
  exact this

end CausalSpectrum.Kernel.LogPair

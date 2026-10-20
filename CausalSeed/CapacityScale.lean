/-
Finite pieces of "Atomic Capacity Does Not Determine Sublinear Causal Entropy Growth".

Proved here, with no `sorry`:
* the uniform law on `{0,1}^k` has Shannon entropy `k`;
* any `K` of its atoms have total mass at most `K · 2^{-k}`;
* `h₂` on `[0,1]` is at most `1`;
* the displayed mixture formula then has the numerical error shape
  `-1 ≤ C - f ≤ 1 + a log₂(e(f+1))`, once an entropy bound
  `H ≤ log₂(e(f+1))` and a floor proxy `t ≤ f ≤ t+1` are assumed.

Not proved here: the processes `Y` and `Z`, `atomQ`, the equivalence
`Cₙ ~ f(n)`, countable realizability, or the absence of a universal
sublinear rate.
-/
import CausalSeed.VanishingEmbed
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

noncomputable section

open Real Finset

namespace CapacityScale

/-- `k` independent fair bits, as the uniform law on `{0,1}^k`, have entropy `k`. -/
theorem fairBlock_entropy (k : ℕ) :
    ∑ _x : Fin k → Bool, Vanishing.shannonTerm ((1 / 2 : ℝ) ^ k) = (k : ℝ) := by
  have hterm : Vanishing.shannonTerm ((1 / 2 : ℝ) ^ k) = (k : ℝ) * (1 / 2 : ℝ) ^ k := by
    by_cases hk : k = 0
    · subst hk
      simp [Vanishing.shannonTerm, pow_zero, logb_one]
    · have hpos : (0 : ℝ) < (1 / 2 : ℝ) ^ k := by positivity
      rw [Vanishing.shannonTerm_of_pos hpos, Vanishing.logb_two_pow_half]
      ring
  rw [Finset.sum_const, Finset.card_univ, hterm, nsmul_eq_mul]
  have hc : (Fintype.card (Fin k → Bool) : ℝ) = (2 : ℝ) ^ k := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
    simp
  rw [hc]
  calc
    (2 : ℝ) ^ k * ((k : ℝ) * (1 / 2 : ℝ) ^ k)
        = (k : ℝ) * ((2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k) := by ring
    _ = (k : ℝ) * ((2 * (1 / 2) : ℝ) ^ k) := by rw [mul_pow]
    _ = (k : ℝ) := by norm_num

/-- Any `K` atoms of that uniform law carry total mass at most `K · 2^{-k}`. -/
theorem fairBlock_heavy_mass (k K : ℕ) (S : Finset (Fin k → Bool)) (hS : S.card ≤ K) :
    ∑ _ ∈ S, ((1 / 2 : ℝ) ^ k) ≤ (K : ℝ) * (1 / 2 : ℝ) ^ k := by
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hS) (by positivity)

theorem h2_eq_binEntropy {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    Vanishing.h2 p = binEntropy p / log 2 := by
  have h1 : 0 < 1 - p := by linarith
  rw [Vanishing.h2, Vanishing.shannonTerm_of_pos hp0, Vanishing.shannonTerm_of_pos h1,
    logb, logb, binEntropy, log_inv p, log_inv (1 - p)]
  field_simp

/-- Binary entropy on the unit interval is at most one bit. -/
theorem h2_le_one {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Vanishing.h2 p ≤ 1 := by
  rcases eq_or_lt_of_le hp0 with rfl | hp0
  · simp [Vanishing.h2, Vanishing.shannonTerm]
  rcases eq_or_lt_of_le hp1 with rfl | hp1
  · simp [Vanishing.h2, Vanishing.shannonTerm]
  rw [h2_eq_binEntropy hp0 hp1]
  have hlog : 0 < log 2 := log_pos (by norm_num : (1 : ℝ) < 2)
  rw [div_le_one hlog]
  exact binEntropy_le_log_two

/-- Numerical error shape of the mixture formula in the capacity-scale note.
`H ≤ log₂(e(f+1))` and the floor proxy `t` are hypotheses, not constructions. -/
theorem mixture_scale_error (a f H t : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hH0 : 0 ≤ H)
    (hH : H ≤ logb 2 (Real.exp 1 * (f + 1))) (htf : t ≤ f) (hft : f ≤ t + 1) :
    -1 ≤ Vanishing.h2 a + a * (f + H) + (1 - a) * t - f ∧
      Vanishing.h2 a + a * (f + H) + (1 - a) * t - f ≤
        1 + a * logb 2 (Real.exp 1 * (f + 1)) := by
  set C := Vanishing.h2 a + a * (f + H) + (1 - a) * t with hCdef
  have hh0 : 0 ≤ Vanishing.h2 a :=
    add_nonneg (Vanishing.shannonTerm_nonneg_of_le_one ha0 ha1)
      (Vanishing.shannonTerm_nonneg_of_le_one (sub_nonneg.mpr ha1) (by linarith))
  have hh1 : Vanishing.h2 a ≤ 1 := h2_le_one ha0 ha1
  have hgap : -1 ≤ t - f := by linarith
  have hnonpos : t - f ≤ 0 := by linarith
  have ha' : 0 ≤ 1 - a := by linarith
  have hC : C - f = Vanishing.h2 a + a * H + (1 - a) * (t - f) := by
    rw [hCdef]
    ring
  constructor
  · rw [hC]
    have hprod : -1 ≤ (1 - a) * (t - f) := by
      have h1 : -(1 - a) ≤ (1 - a) * (t - f) := by
        simpa using mul_le_mul_of_nonneg_left hgap ha'
      linarith
    nlinarith
  · rw [hC]
    have hprod : (1 - a) * (t - f) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha' hnonpos
    have hAH : a * H ≤ a * logb 2 (Real.exp 1 * (f + 1)) :=
      mul_le_mul_of_nonneg_left hH ha0
    nlinarith

end CapacityScale

end

/-
Let it be. An information clock.

A step of conditional probability `p > 0` advances a clock by `d(p)` bits.
The clock never runs backward, cutting a passage in two leaves the total
unchanged, and one outcome of a fair toss counts as one bit:

* `d(p) ≥ 0` for `p ∈ (0, 1]`;
* `d(p * q) = d(p) + d(q)`;
* `d(1/2) = 1`.

Proved, with no sorry: there is exactly one such clock, `d(p) = -log₂ p`.
Along a finite history the reading is the sum of the steps, hence
`-log₂` of their product. A certain step contributes nothing. A fair step
contributes one bit.

Not proved: that this reading is physical time. The order of the steps is
assumed. The groove, the turntable and the listener are not part of the
statement.
-/

import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

noncomputable section

open Classical

namespace CausalSpectrum
namespace LetItBe

/-- The three requirements. `q` is the probability of the next step given
the first; the two steps need not be independent. -/
structure Clock where
  d : ℝ → ℝ
  nonneg : ∀ p : ℝ, 0 < p → p ≤ 1 → 0 ≤ d p
  cut : ∀ p q : ℝ, 0 < p → p ≤ 1 → 0 < q → q ≤ 1 → d (p * q) = d p + d q
  fair : d (1 / 2) = 1

def surprisal (p : ℝ) : ℝ := -Real.logb 2 p

theorem surprisal_nonneg {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) : 0 ≤ surprisal p := by
  unfold surprisal
  have h : Real.logb 2 p ≤ 0 :=
    Real.logb_nonpos (b := 2) (by norm_num : (1 : ℝ) < 2) hp.le hp1
  linarith

theorem surprisal_cut {p q : ℝ} (hp : p ≠ 0) (hq : q ≠ 0) :
    surprisal (p * q) = surprisal p + surprisal q := by
  unfold surprisal
  rw [Real.logb_mul hp hq]
  ring

theorem surprisal_half : surprisal (1 / 2) = 1 := by
  unfold surprisal
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.logb_inv,
    Real.logb_self_eq_one (by norm_num)]
  norm_num

theorem surprisal_one : surprisal 1 = 0 := by
  simp [surprisal, Real.logb_one]

def shannonClock : Clock where
  d := surprisal
  nonneg := fun _ hp hp1 => surprisal_nonneg hp hp1
  cut := fun p q hp _ hq _ => surprisal_cut hp.ne' hq.ne'
  fair := surprisal_half

/-- A certain step. On the second pass the known beat adds nothing. -/
theorem certain_step (C : Clock) : C.d 1 = 0 := by
  have h := C.cut 1 1 one_pos le_rfl one_pos le_rfl
  rw [mul_one] at h
  linarith

theorem fair_step (C : Clock) : C.d (1 / 2) = 1 :=
  C.fair

/-! The change of coordinate `g(x) = d(2^{-x})`. -/

variable (C : Clock)

def g (x : ℝ) : ℝ := C.d ((2 : ℝ) ^ (-x))

theorem step_bounds {x : ℝ} (hx : 0 ≤ x) :
    0 < (2 : ℝ) ^ (-x) ∧ (2 : ℝ) ^ (-x) ≤ 1 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
  exact Real.rpow_le_one_of_one_le_of_nonpos (by norm_num : (1 : ℝ) ≤ 2) (neg_nonpos.mpr hx)

theorem g_add {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) : g C (x + y) = g C x + g C y := by
  unfold g
  have hpow : (2 : ℝ) ^ (-(x + y)) = (2 : ℝ) ^ (-x) * (2 : ℝ) ^ (-y) := by
    rw [neg_add, Real.rpow_add (by norm_num)]
  rw [hpow]
  exact C.cut _ _ (step_bounds hx).1 (step_bounds hx).2
    (step_bounds hy).1 (step_bounds hy).2

theorem g_zero : g C 0 = 0 := by
  have h := g_add C (le_refl (0 : ℝ)) (le_refl (0 : ℝ))
  simp only [add_zero] at h
  linarith

theorem g_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ g C x :=
  C.nonneg _ (step_bounds hx).1 (step_bounds hx).2

theorem g_one : g C 1 = 1 := by
  unfold g
  rw [Real.rpow_neg_one, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  exact C.fair

theorem g_nat (n : ℕ) : g C (n : ℝ) = n := by
  induction n with
  | zero =>
      simpa using g_zero C
  | succ n ih =>
      have h := g_add C (Nat.cast_nonneg n) zero_le_one
      rw [ih, g_one C] at h
      simpa [Nat.cast_add, Nat.cast_one] using h

theorem g_nsmul (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : g C ((n : ℝ) * x) = (n : ℝ) * g C x := by
  induction n with
  | zero =>
      simp [g_zero]
  | succ n ih =>
      have hx' : 0 ≤ (n : ℝ) * x := mul_nonneg (Nat.cast_nonneg n) hx
      have hmul : ((n : ℝ) + 1) * x = (n : ℝ) * x + x := by ring
      rw [Nat.cast_succ, hmul, g_add C hx' hx, ih]
      ring

theorem g_div_nat (m n : ℕ) (hn : 0 < n) :
    g C ((m : ℝ) / n) = (m : ℝ) / n := by
  have hx : 0 ≤ (m : ℝ) / n := div_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg n)
  have h := g_nsmul C n hx
  have hprod : (n : ℝ) * ((m : ℝ) / n) = m := by
    field_simp
  rw [hprod, g_nat C m] at h
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmul : (n : ℝ) * g C ((m : ℝ) / n) = (n : ℝ) * ((m : ℝ) / n) := by
    rw [← h]
    field_simp [hn0]
  exact mul_left_cancel₀ hn0 hmul

theorem g_rat {q : ℚ} (hq : 0 ≤ q) : g C (q : ℝ) = q := by
  have hnum : 0 ≤ q.num := Rat.num_nonneg.mpr hq
  rw [Rat.cast_def, ← Int.natAbs_of_nonneg hnum, Int.cast_natCast]
  exact g_div_nat C q.num.natAbs q.den q.den_pos

theorem g_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : g C x ≤ g C y := by
  have hdiff : 0 ≤ y - x := sub_nonneg.mpr hxy
  have h := g_add C hx hdiff
  have hy : g C (x + (y - x)) = g C y := by
    congr 1
    ring
  rw [hy] at h
  linarith [g_nonneg C hdiff]

theorem g_eq {x : ℝ} (hx : 0 ≤ x) : g C x = x := by
  apply le_antisymm
  · by_contra hlt
    push_neg at hlt
    obtain ⟨q, hxq, hqg⟩ := exists_rat_btwn hlt
    have hq0 : 0 ≤ (q : ℝ) := le_trans hx hxq.le
    have hqrat : 0 ≤ q := by exact_mod_cast hq0
    linarith [g_mono C hx hxq.le, g_rat C hqrat]
  · by_contra hlt
    push_neg at hlt
    obtain ⟨q, hgq, hqx⟩ := exists_rat_btwn hlt
    by_cases hqneg : (q : ℝ) < 0
    · linarith [g_nonneg C hx]
    · have hq0 : 0 ≤ (q : ℝ) := not_lt.mp hqneg
      have hqrat : 0 ≤ q := by exact_mod_cast hq0
      linarith [g_mono C hq0 hqx.le, g_rat C hqrat]

/-- The three requirements fix the clock. -/
theorem clock_eq_surprisal (C : Clock) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    C.d p = surprisal p := by
  have hlog : 0 ≤ surprisal p := surprisal_nonneg hp hp1
  have hg := g_eq C hlog
  unfold g surprisal at hg
  have hrepr : (2 : ℝ) ^ (- -Real.logb 2 p) = p := by
    rw [neg_neg]
    exact Real.rpow_logb (by norm_num) (by norm_num) hp
  rw [hrepr] at hg
  exact hg

/-! A finite history. The step probabilities are conditional, and they multiply. -/

def reading (C : Clock) (ps : List ℝ) : ℝ :=
  (ps.map C.d).sum

theorem prod_pos {ps : List ℝ} (h : ∀ p ∈ ps, 0 < p) : 0 < ps.prod := by
  induction ps with
  | nil =>
      simp
  | cons p ps ih =>
      rw [List.prod_cons]
      exact mul_pos (h p (by simp)) (ih fun q hq => h q (by simp [hq]))

theorem reading_eq (C : Clock) (ps : List ℝ) (h : ∀ p ∈ ps, 0 < p ∧ p ≤ 1) :
    reading C ps = surprisal ps.prod := by
  induction ps with
  | nil =>
      simp [reading, surprisal_one]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hps : ∀ q ∈ ps, 0 < q ∧ q ≤ 1 := fun q hq => h q (by simp [hq])
      have hpos : 0 < ps.prod := prod_pos fun q hq => (hps q hq).1
      simp only [reading, List.map_cons, List.sum_cons, List.prod_cons]
      rw [clock_eq_surprisal C hp.1 hp.2]
      have htail : (ps.map C.d).sum = surprisal ps.prod := by
        simpa [reading] using ih hps
      rw [htail, surprisal_cut hp.1.ne' hpos.ne']

end LetItBe
end CausalSpectrum

end

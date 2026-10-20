/-
Finite identities behind "Contraction, Atomic Capacity, and Exact One-Seed Simulation".

Proved here, with no `sorry`:
* one fair bit followed by independent Bernoulli flips has Shannon entropy
  `1 + ∑ h₂(pₜ)`;
* if `0 ≤ pₜ ≤ 1/2`, every atom of that law is at most `(1/2) ∏ (1-pₜ)`,
  and that product is at most `exp(-∑ pₜ)` whenever `pₜ < 1`;
* the scalar recurrence `d_{j+1} ≤ q_{j+1} d_j + ε_{j+1}` iterates to the
  displayed product-sum bound;
* under uniform factors `0 ≤ qⱼ ≤ q < 1` and `0 ≤ εⱼ ≤ ε`, the bound is at most
  `qⁿ d₀ + ε(1-qⁿ)/(1-q)`.

Not proved here: a quantum instrument, atomic capacity of an infinite-path law,
Borel--Cantelli, the three regimes as statements about a process, or the claim
that a finite prefix cannot identify infinite atomic capacity.
-/
import CausalSeed.VanishingClose
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Field.GeomSum

noncomputable section

open Real Finset

namespace ClosureScale

/-- Entropy of one fair bit followed by independent Bernoulli flips.
This is the finite identity `Cₙ = 1 + ∑ h₂(pⱼ)` of the closure note. It is not
a theorem about a quantum instrument. -/
theorem record_entropy {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp1 : ∀ t, p t ≤ 1) :
    ∑ y : Fin (n + 1) → Bool,
        Vanishing.shannonTerm (Vanishing.bernJoint (Fin.cons (1 / 2 : ℝ) p) y) =
      1 + ∑ t, Vanishing.h2 (p t) := by
  let r : Fin (n + 1) → ℝ := Fin.cons (1 / 2 : ℝ) p
  have hp0' : ∀ t, 0 ≤ r t := by
    intro t
    cases t using Fin.cases with
    | zero =>
      simp [r, Fin.cons_zero]
    | succ t =>
      simpa [r, Fin.cons_succ] using hp0 t
  have hp1' : ∀ t, r t ≤ 1 := by
    intro t
    cases t using Fin.cases with
    | zero =>
      simp [r, Fin.cons_zero]
      norm_num
    | succ t =>
      simpa [r, Fin.cons_succ] using hp1 t
  have h := Vanishing.bernJoint_entropy r hp0' hp1'
  rw [h, Fin.sum_univ_succ (fun t => Vanishing.h2 (r t))]
  have hz : r 0 = 1 / 2 := by simp [r, Fin.cons_zero]
  have hs : ∀ t : Fin n, r t.succ = p t := by
    intro t
    simp [r, Fin.cons_succ]
  have hh : Vanishing.h2 (r 0) = 1 := by
    rw [hz]
    exact Vanishing.h2_half
  simp only [hh, hs]

/-- Every atom of that law is at most the all-nonflip cylinder. -/
theorem record_atom_le {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t) (hp : ∀ t, p t ≤ 1 / 2)
    (y : Fin (n + 1) → Bool) :
    Vanishing.bernJoint (Fin.cons (1 / 2 : ℝ) p) y ≤
      (1 / 2) * ∏ t, (1 - p t) := by
  rw [Vanishing.bernJoint, Fin.prod_univ_succ]
  have hhalf : Vanishing.bern (1 / 2 : ℝ) (y 0) = 1 / 2 := by
    cases y 0
    · simp [Vanishing.bern]; norm_num
    · simp [Vanishing.bern]
  simp only [Fin.cons_zero, Fin.cons_succ, hhalf]
  apply mul_le_mul_of_nonneg_left
  · apply Finset.prod_le_prod₀
    · intro t _
      exact Vanishing.bern_nonneg (hp0 t) (by linarith [hp t]) (y t.succ)
    · intro t _
      exact Vanishing.bern_le_one_sub (hp t) (y t.succ)
  · norm_num

/-- The all-nonflip cylinder is at most the exponential tail. -/
theorem record_cylinder_le_exp {n : ℕ} (p : Fin n → ℝ) (hp0 : ∀ t, 0 ≤ p t)
    (hp1 : ∀ t, p t < 1) :
    (1 / 2) * ∏ t, (1 - p t) ≤ (1 / 2) * exp (-∑ t, p t) := by
  apply mul_le_mul_of_nonneg_left
  · exact Vanishing.prod_one_sub_le_exp p hp0 hp1
  · norm_num

/-- Iterate `d_{j+1} ≤ q_{j+1} d_j + ε_{j+1}`. The empty product is `1`. -/
theorem contraction_iterate (n : ℕ) (d q ε : ℕ → ℝ)
    (hq : ∀ j, j < n → 0 ≤ q (j + 1))
    (hstep : ∀ j, j < n → d (j + 1) ≤ q (j + 1) * d j + ε (j + 1)) :
    d n ≤ (∏ j ∈ Finset.range n, q (j + 1)) * d 0 +
      ∑ k ∈ Finset.range n,
        ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun j hj => hq j (Nat.lt_succ_of_lt hj))
      (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
    have h := hstep n (Nat.lt_succ_self n)
    have hq0 : 0 ≤ q (n + 1) := hq n (Nat.lt_succ_self n)
    have hmul :
        q (n + 1) * d n ≤
          q (n + 1) * ((∏ j ∈ Finset.range n, q (j + 1)) * d 0 +
            ∑ k ∈ Finset.range n,
              ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1)) :=
      mul_le_mul_of_nonneg_left ih' hq0
    have hle :
        d (n + 1) ≤
          q (n + 1) * ((∏ j ∈ Finset.range n, q (j + 1)) * d 0 +
            ∑ k ∈ Finset.range n,
              ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1)) +
            ε (n + 1) := by
      linarith
    have hprod :
        q (n + 1) * ∏ j ∈ Finset.range n, q (j + 1) =
          ∏ j ∈ Finset.range (n + 1), q (j + 1) := by
      rw [Finset.prod_range_succ (fun j => q (j + 1)), mul_comm]
    have hsum :
        q (n + 1) *
            ∑ k ∈ Finset.range n,
              ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) +
            ε (n + 1) =
          ∑ k ∈ Finset.range (n + 1),
            ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) (n + 1), q (j + 1) := by
      rw [Finset.mul_sum, Finset.sum_range_succ]
      have hlast : ∏ j ∈ Finset.Ico (n + 1) (n + 1), q (j + 1) = 1 := by simp
      rw [hlast, mul_one]
      refine congrArg (fun t => t + ε (n + 1)) ?_
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
      calc
        q (n + 1) * (ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1)) =
            ε (k + 1) * (q (n + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1)) := by
          rw [mul_left_comm]
        _ = ε (k + 1) *
            ((∏ j ∈ Finset.Ico (k + 1) n, q (j + 1)) * q (n + 1)) := by
          rw [mul_comm (q (n + 1))]
        _ = ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) (n + 1), q (j + 1) := by
          rw [← Finset.prod_Ico_succ_top hk' (fun j => q (j + 1))]
    rw [mul_add, ← mul_assoc, hprod, add_assoc, hsum] at hle
    exact hle

/-- Closed geometric majorant. `q = 1` is excluded by the denominator. -/
theorem geom_majorant (n : ℕ) (q : ℝ) (hq : q ≠ 1) :
    ∑ k ∈ Finset.range n, q ^ k = (1 - q ^ n) / (1 - q) := by
  have h := geom_sum_eq hq n
  have hden1 : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  have hden2 : (1 : ℝ) - q ≠ 0 := sub_ne_zero.mpr (Ne.symm hq)
  have hsub : (q ^ n - 1) / (q - 1) = (1 - q ^ n) / (1 - q) := by
    rw [div_eq_div_iff hden1 hden2]
    ring
  rw [h, hsub]

/-- Uniform factors give the geometric bound of the note. -/
theorem uniform_contraction (n : ℕ) (d q ε : ℕ → ℝ) (q0 ε0 : ℝ)
    (hq0 : 0 ≤ q0) (hq1 : q0 < 1) (hε0 : 0 ≤ ε0)
    (hq : ∀ j, j < n → 0 ≤ q (j + 1) ∧ q (j + 1) ≤ q0)
    (hε : ∀ j, j < n → 0 ≤ ε (j + 1) ∧ ε (j + 1) ≤ ε0)
    (hstep : ∀ j, j < n → d (j + 1) ≤ q (j + 1) * d j + ε (j + 1))
    (hd0 : 0 ≤ d 0) :
    d n ≤ q0 ^ n * d 0 + ε0 * (1 - q0 ^ n) / (1 - q0) := by
  have _ : 0 ≤ q0 ^ n := pow_nonneg hq0 n
  have hiter := contraction_iterate n d q ε (fun j hj => (hq j hj).1) hstep
  have hprod : ∏ j ∈ Finset.range n, q (j + 1) ≤ q0 ^ n := by
    have hle : ∏ j ∈ Finset.range n, q (j + 1) ≤ ∏ j ∈ Finset.range n, q0 := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact (hq j (Finset.mem_range.mp hj)).1
      · intro j hj
        exact (hq j (Finset.mem_range.mp hj)).2
    simpa [Finset.prod_const, Finset.card_range] using hle
  have htail : ∀ k ∈ Finset.range n,
      ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) ≤ q0 ^ (n - (k + 1)) := by
    intro k hk
    have hle : ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) ≤
        ∏ j ∈ Finset.Ico (k + 1) n, q0 := by
      apply Finset.prod_le_prod₀
      · intro j hj
        exact (hq j (Finset.mem_Ico.mp hj).2).1
      · intro j hj
        exact (hq j (Finset.mem_Ico.mp hj).2).2
    simpa [Finset.prod_const, Nat.card_Ico] using hle
  have hsum : ∑ k ∈ Finset.range n,
      ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) ≤
      ∑ k ∈ Finset.range n, ε0 * q0 ^ (n - (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hεk : ε (k + 1) ≤ ε0 := (hε k (Finset.mem_range.mp hk)).2
    have hprod' : 0 ≤ ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) := by
      apply Finset.prod_nonneg
      intro j hj
      exact (hq j (Finset.mem_Ico.mp hj).2).1
    calc
      ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) ≤
          ε0 * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) :=
        mul_le_mul_of_nonneg_right hεk hprod'
      _ ≤ ε0 * q0 ^ (n - (k + 1)) :=
        mul_le_mul_of_nonneg_left (htail k hk) hε0
  have hreindex : ∑ k ∈ Finset.range n, q0 ^ (n - (k + 1)) =
      ∑ k ∈ Finset.range n, q0 ^ k := by
    have hpt : ∀ k ∈ Finset.range n, q0 ^ (n - (k + 1)) = q0 ^ (n - 1 - k) := by
      intro k hk
      have : n - (k + 1) = n - 1 - k := by
        have hk' : k < n := Finset.mem_range.mp hk
        omega
      rw [this]
    rw [Finset.sum_congr rfl hpt]
    exact Finset.sum_range_reflect (fun j => q0 ^ j) n
  have hclosed : ∑ k ∈ Finset.range n, ε0 * q0 ^ (n - (k + 1)) =
      ε0 * (1 - q0 ^ n) / (1 - q0) := by
    rw [← Finset.mul_sum, hreindex, geom_majorant n q0 (by linarith), mul_div_assoc]
  have hsumle : ∑ k ∈ Finset.range n,
      ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) ≤
      ε0 * (1 - q0 ^ n) / (1 - q0) :=
    le_trans hsum (le_of_eq hclosed)
  have hd : (∏ j ∈ Finset.range n, q (j + 1)) * d 0 ≤ q0 ^ n * d 0 :=
    mul_le_mul_of_nonneg_right hprod hd0
  calc
    d n ≤ (∏ j ∈ Finset.range n, q (j + 1)) * d 0 +
        ∑ k ∈ Finset.range n,
          ε (k + 1) * ∏ j ∈ Finset.Ico (k + 1) n, q (j + 1) := hiter
    _ ≤ q0 ^ n * d 0 + ε0 * (1 - q0 ^ n) / (1 - q0) :=
      add_le_add hd hsumle

end ClosureScale

end

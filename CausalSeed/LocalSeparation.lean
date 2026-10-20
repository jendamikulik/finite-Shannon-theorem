/-
Finite obstructions to a universal local overhead.

Proved here, with no `sorry`:
* two independent fair bits have Shannon entropy `2`;
* a finite seed pushed onto a uniform four-point law has entropy at least `2`;
* every finite law of pairwise independent fair bits has atoms of mass at most
  `1/(n+1)` and entropy at least `log₂(n+1)`;
* that lower bound is unbounded in the number of inputs, while the centralized
  two-bit seed is not;
* every deterministic local CHSH table has value in `{-2, 2}`, so no finite
  mixture attains Bell value `4v` for `v > 1/2`;
* `h₂(1/4) = 2 - (3/4) log₂ 3`, and the equal/opposite mixture has correlation `1/2`.

Not proved here: the sharp coefficient `(1-4ε) log log m`, existence of a
Hadamard matrix, countable (as opposed to finite) seeds, history-indexed
strategies, and the `log₂ ln n` asymptotic.
-/
import CausalSeed.VanishingEmbed
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean

noncomputable section

open Real Finset

namespace LocalSeparation

/-- Sign associated with a Boolean output. `false ↦ 1`, `true ↦ -1`. -/
def sign (b : Bool) : ℝ :=
  if b then -1 else 1

theorem sign_sq (b : Bool) : sign b * sign b = 1 := by
  cases b <;> simp [sign]

/-- Shannon entropy of the uniform law on four outcomes. -/
theorem uniform_four_entropy :
    ∑ _ : Bool × Bool, Vanishing.shannonTerm (1 / 4 : ℝ) = 2 := by
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_bool,
    Vanishing.shannonTerm_quarter]
  norm_num

/-- Pushing a finite seed forward cannot raise Shannon entropy. -/
theorem finite_shannon_push_le {ι β : Type*} [Fintype ι] [Fintype β] [DecidableEq β]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i : ι, w i = 1) (f : ι → β) :
    ∑ b : β, Vanishing.shannonTerm (∑ i, if f i = b then w i else 0) ≤
      ∑ i, Vanishing.shannonTerm (w i) := by
  classical
  let fiber (b : β) (i : ι) : ℝ := if f i = b then w i else 0
  have hfiber0 : ∀ b i, 0 ≤ fiber b i := by
    intro b i
    unfold fiber
    split_ifs <;> simp [hw i]
  have hgroup : ∀ b,
      Vanishing.shannonTerm (∑ i, fiber b i) ≤ ∑ i, Vanishing.shannonTerm (fiber b i) := by
    intro b
    have hs : Summable (fiber b) :=
      summable_of_ne_finset_zero
        (fun a (ha : a ∉ (Finset.univ : Finset ι)) => absurd (Finset.mem_univ a) ha)
    have hS : Summable fun i => Vanishing.shannonTerm (fiber b i) :=
      summable_of_ne_finset_zero
        (fun a (ha : a ∉ (Finset.univ : Finset ι)) => absurd (Finset.mem_univ a) ha)
    have hA : ∑' i, fiber b i ≤ 1 := by
      rw [tsum_fintype]
      unfold fiber
      have : ∑ i, (if f i = b then w i else 0) ≤ ∑ i, w i := by
        apply Finset.sum_le_sum
        intro i _
        split_ifs <;> simp [hw i]
      linarith [h1]
    have hg := Vanishing.shannonTerm_group (fiber b) (hfiber0 b) hs hS hA
    simpa [tsum_fintype] using hg
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hgroup b)
  have hRHS : ∑ b, ∑ i, Vanishing.shannonTerm (fiber b i) =
      ∑ i, Vanishing.shannonTerm (w i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_eq_single (f i)]
    · unfold fiber
      simp
    · intro b _ hb
      have hne : f i ≠ b := Ne.symm hb
      unfold fiber
      simp [hne, Vanishing.shannonTerm]
    · intro hmem
      exact absurd (Finset.mem_univ (f i)) hmem
  simpa [fiber, hRHS] using hsum

/-- A centralized unequal-input transcript is uniform on four points, so every
finite seed that realizes it has entropy at least `2`. -/
theorem central_entropy_ge_two {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (f : ι → Bool × Bool)
    (hunif : ∀ z, (∑ i, if f i = z then w i else 0) = 1 / 4) :
    2 ≤ ∑ i, Vanishing.shannonTerm (w i) := by
  have hpush := finite_shannon_push_le w hw h1 f
  have hout : ∑ z : Bool × Bool, Vanishing.shannonTerm
      (∑ i, if f i = z then w i else 0) = 2 := by
    refine Eq.trans ?_ uniform_four_entropy
    apply Finset.sum_congr rfl
    intro z _
    exact congrArg Vanishing.shannonTerm (hunif z)
  linarith

/-- Mass of one bit. -/
def bitMass {n : ℕ} (μ : (Fin n → Bool) → ℝ) (i : Fin n) (b : Bool) : ℝ :=
  ∑ x, if x i = b then μ x else 0

/-- Mass of one ordered pair of bits. -/
def pairMass {n : ℕ} (μ : (Fin n → Bool) → ℝ) (i j : Fin n) (b c : Bool) : ℝ :=
  ∑ x, if x i = b ∧ x j = c then μ x else 0

/-- Finite law of pairwise independent fair bits. -/
structure PairwiseFair {n : ℕ} (μ : (Fin n → Bool) → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ μ x
  total : ∑ x, μ x = 1
  fair : ∀ i b, bitMass μ i b = 1 / 2
  indep : ∀ i j, i ≠ j → ∀ b c, pairMass μ i j b c = 1 / 4

theorem expect_sign {n : ℕ} (μ : (Fin n → Bool) → ℝ) (h : PairwiseFair μ) (i : Fin n) :
    ∑ x, μ x * sign (x i) = 0 := by
  classical
  have hmul (b : Bool) (c : ℝ) :
      ∑ x, (if x i = b then μ x * c else 0) = c * bitMass μ i b := by
    unfold bitMass
    have hpt : ∀ x, (if x i = b then μ x * c else 0) =
        c * (if x i = b then μ x else 0) := by
      intro x
      by_cases hx : x i = b <;> simp [hx, mul_comm]
    simp_rw [hpt]
    rw [← Finset.mul_sum]
  have hpt : ∀ x, μ x * sign (x i) =
      (if x i = true then μ x * (-1) else 0) +
      (if x i = false then μ x * 1 else 0) := by
    intro x
    by_cases hx : x i = true
    · simp [sign, hx]
    · have hx' : x i = false := by
        cases hxi : x i
        · rfl
        · exact absurd hxi hx
      simp [sign, hx']
  simp_rw [hpt, Finset.sum_add_distrib, hmul, h.fair]
  norm_num

theorem expect_sign_mul {n : ℕ} (μ : (Fin n → Bool) → ℝ) (h : PairwiseFair μ)
    (i j : Fin n) :
    ∑ x, μ x * (sign (x i) * sign (x j)) = if i = j then (1 : ℝ) else 0 := by
  classical
  by_cases hij : i = j
  · subst hij
    have hsq : ∀ x : Fin n → Bool, sign (x i) * sign (x i) = 1 := fun x => sign_sq (x i)
    simp_rw [hsq, mul_one, h.total]
    simp
  · have hpt : ∀ x : Fin n → Bool, sign (x i) * sign (x j) =
        (if x i = false ∧ x j = false then (1 : ℝ) else 0) +
        (if x i = false ∧ x j = true then (-1 : ℝ) else 0) +
        (if x i = true ∧ x j = false then (-1 : ℝ) else 0) +
        (if x i = true ∧ x j = true then (1 : ℝ) else 0) := by
      intro x
      by_cases hxi : x i = true <;> by_cases hxj : x j = true
      · simp [sign, hxi, hxj]
      · have hj : x j = false := by
          cases h : x j
          · rfl
          · exact absurd h hxj
        simp [sign, hxi, hj]
      · have hi : x i = false := by
          cases h : x i
          · rfl
          · exact absurd h hxi
        simp [sign, hi, hxj]
      · have hi : x i = false := by
          cases h : x i
          · rfl
          · exact absurd h hxi
        have hj : x j = false := by
          cases h : x j
          · rfl
          · exact absurd h hxj
        simp [sign, hi, hj]
    have hmul (b c : Bool) (k : ℝ) :
        ∑ x, μ x * (if x i = b ∧ x j = c then k else 0) = k * pairMass μ i j b c := by
      unfold pairMass
      have hpt' : ∀ x, μ x * (if x i = b ∧ x j = c then k else 0) =
          k * (if x i = b ∧ x j = c then μ x else 0) := by
        intro x
        by_cases hx : x i = b ∧ x j = c <;> simp [hx, mul_comm]
      simp_rw [hpt']
      rw [← Finset.mul_sum]
    have hrewrite : ∀ x, μ x * (sign (x i) * sign (x j)) =
        μ x * (if x i = false ∧ x j = false then (1 : ℝ) else 0) +
        μ x * (if x i = false ∧ x j = true then (-1 : ℝ) else 0) +
        μ x * (if x i = true ∧ x j = false then (-1 : ℝ) else 0) +
        μ x * (if x i = true ∧ x j = true then (1 : ℝ) else 0) := by
      intro x
      rw [hpt x]
      ring
    simp_rw [hrewrite, Finset.sum_add_distrib]
    rw [hmul false false (1 : ℝ), hmul false true (-1 : ℝ),
      hmul true false (-1 : ℝ), hmul true true (1 : ℝ),
      h.indep i j hij false false, h.indep i j hij false true,
      h.indep i j hij true false, h.indep i j hij true true]
    have hif : (if i = j then (1 : ℝ) else 0) = 0 := by
      simp [hij]
    rw [hif]
    norm_num

def coeff {n : ℕ} (x0 x : Fin n → Bool) (i : Fin n) : ℝ :=
  sign (x0 i) * sign (x i)

def inner {n : ℕ} (x0 x : Fin n → Bool) : ℝ :=
  1 + ∑ i, coeff x0 x i

theorem inner_self {n : ℕ} (x0 : Fin n → Bool) :
    inner x0 x0 = (n : ℝ) + 1 := by
  unfold inner coeff
  have hsq : ∀ i, sign (x0 i) * sign (x0 i) = 1 := fun i => sign_sq _
  simp_rw [hsq]
  simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem expect_coeff {n : ℕ} (μ : (Fin n → Bool) → ℝ) (h : PairwiseFair μ)
    (x0 : Fin n → Bool) (i j : Fin n) :
    ∑ x, μ x * (coeff x0 x i * coeff x0 x j) = if i = j then (1 : ℝ) else 0 := by
  have hfac : ∀ x, coeff x0 x i * coeff x0 x j =
      (sign (x0 i) * sign (x0 j)) * (sign (x i) * sign (x j)) := by
    intro x
    unfold coeff
    ring
  simp_rw [hfac]
  have hpull : ∑ x, μ x * ((sign (x0 i) * sign (x0 j)) * (sign (x i) * sign (x j))) =
      (sign (x0 i) * sign (x0 j)) * ∑ x, μ x * (sign (x i) * sign (x j)) := by
    simp_rw [show ∀ x, μ x * ((sign (x0 i) * sign (x0 j)) * (sign (x i) * sign (x j))) =
        (sign (x0 i) * sign (x0 j)) * (μ x * (sign (x i) * sign (x j))) by
      intro x; ring]
    rw [← Finset.mul_sum]
  rw [hpull, expect_sign_mul μ h i j]
  by_cases hij : i = j
  · subst hij
    simp [sign_sq]
  · simp [hij]

theorem expect_inner_sq {n : ℕ} (μ : (Fin n → Bool) → ℝ) (h : PairwiseFair μ)
    (x0 : Fin n → Bool) :
    ∑ x, μ x * (inner x0 x) ^ 2 = (n : ℝ) + 1 := by
  have hexpand : ∀ x, (inner x0 x) ^ 2 =
      1 + 2 * (∑ i, coeff x0 x i) +
        ∑ i, ∑ j, coeff x0 x i * coeff x0 x j := by
    intro x
    unfold inner
    have hsq : (∑ i, coeff x0 x i) * (∑ j, coeff x0 x j) =
        ∑ i, ∑ j, coeff x0 x i * coeff x0 x j := by
      rw [Finset.sum_mul_sum]
    have hsqform : (1 + ∑ i, coeff x0 x i) ^ 2 =
        1 + 2 * (∑ i, coeff x0 x i) +
          (∑ i, coeff x0 x i) * (∑ j, coeff x0 x j) := by
      ring
    rw [hsqform, hsq]
  simp_rw [hexpand, mul_add, Finset.sum_add_distrib]
  have h0 : ∑ x, μ x * 1 = 1 := by simpa using h.total
  have hcross : ∑ x, μ x * (2 * ∑ i, coeff x0 x i) = 0 := by
    have hswap : ∀ x, μ x * (2 * ∑ i, coeff x0 x i) =
        ∑ i, μ x * (2 * coeff x0 x i) := by
      intro x
      calc
        μ x * (2 * ∑ i, coeff x0 x i)
            = (μ x * 2) * ∑ i, coeff x0 x i := by ring
        _ = ∑ i, (μ x * 2) * coeff x0 x i := by rw [Finset.mul_sum]
        _ = ∑ i, μ x * (2 * coeff x0 x i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
    simp_rw [hswap]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro i _
    unfold coeff
    have hpull : ∑ x, μ x * (2 * (sign (x0 i) * sign (x i))) =
        2 * sign (x0 i) * ∑ x, μ x * sign (x i) := by
      simp_rw [show ∀ x, μ x * (2 * (sign (x0 i) * sign (x i))) =
          (2 * sign (x0 i)) * (μ x * sign (x i)) by intro x; ring]
      exact (Finset.mul_sum _ _ _).symm
    rw [hpull, expect_sign μ h i, mul_zero]
  have hdiag : ∑ x, μ x * (∑ i, ∑ j, coeff x0 x i * coeff x0 x j) = (n : ℝ) := by
    have hswap : ∀ x, μ x * (∑ i, ∑ j, coeff x0 x i * coeff x0 x j) =
        ∑ i, ∑ j, μ x * (coeff x0 x i * coeff x0 x j) := by
      intro x
      calc
        μ x * (∑ i, ∑ j, coeff x0 x i * coeff x0 x j)
            = ∑ i, μ x * (∑ j, coeff x0 x i * coeff x0 x j) := by rw [Finset.mul_sum]
        _ = ∑ i, ∑ j, μ x * (coeff x0 x i * coeff x0 x j) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [Finset.mul_sum]
    simp_rw [hswap]
    have hord :
        ∑ x : Fin n → Bool, ∑ i : Fin n, ∑ j : Fin n,
            μ x * (coeff x0 x i * coeff x0 x j) =
        ∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → Bool,
            μ x * (coeff x0 x i * coeff x0 x j) := by
      calc
        ∑ x : Fin n → Bool, ∑ i : Fin n, ∑ j : Fin n,
              μ x * (coeff x0 x i * coeff x0 x j)
            = ∑ i : Fin n, ∑ x : Fin n → Bool, ∑ j : Fin n,
                μ x * (coeff x0 x i * coeff x0 x j) := Finset.sum_comm
        _ = ∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → Bool,
              μ x * (coeff x0 x i * coeff x0 x j) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact Finset.sum_comm
    rw [hord]
    have : ∑ i : Fin n, ∑ j : Fin n, ∑ x : Fin n → Bool,
        μ x * (coeff x0 x i * coeff x0 x j) =
        ∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      exact expect_coeff μ h x0 i j
    rw [this]
    have honly : ∑ i : Fin n, ∑ j : Fin n, (if i = j then (1 : ℝ) else 0) =
        ∑ i : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
      · intro j _ hj
        rw [ite_eq_right (Ne.symm hj)]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [honly]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  linarith

/-- Every atom of a pairwise independent fair family has mass at most `1/(n+1)`. -/
theorem atom_le {n : ℕ} (μ : (Fin n → Bool) → ℝ) (h : PairwiseFair μ)
    (x0 : Fin n → Bool) :
    μ x0 ≤ 1 / ((n : ℝ) + 1) := by
  have hE := expect_inner_sq μ h x0
  have hself := inner_self x0
  have hterm : ∀ x, 0 ≤ μ x * (inner x0 x) ^ 2 :=
    fun x => mul_nonneg (h.nonneg x) (sq_nonneg _)
  have hge : μ x0 * (inner x0 x0) ^ 2 ≤ ∑ x, μ x * (inner x0 x) ^ 2 := by
    classical
    simpa using Finset.single_le_sum (fun x (_ : x ∈ Finset.univ) => hterm x)
      (Finset.mem_univ x0)
  have hmul : μ x0 * ((n : ℝ) + 1) ^ 2 ≤ (n : ℝ) + 1 := by
    simpa [hself, hE] using hge
  have hnpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdiv : μ x0 * ((n : ℝ) + 1) ≤ 1 := by
    have h := div_le_div_of_nonneg_right hmul (le_of_lt hnpos)
    have hL : μ x0 * ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 1) = μ x0 * ((n : ℝ) + 1) := by
      field_simp [hnpos.ne']
    have hR : ((n : ℝ) + 1) / ((n : ℝ) + 1) = 1 := by
      field_simp [hnpos.ne']
    rw [hL, hR] at h
    exact h
  exact (le_div_iff₀ hnpos).2 (by simpa [mul_comm] using hdiv)

/-- Pairwise independent fair bits cost at least `log₂(n+1)`. -/
theorem pairwise_entropy_ge {n : ℕ} (μ : (Fin n → Bool) → ℝ) (h : PairwiseFair μ) :
    logb 2 ((n : ℝ) + 1) ≤ ∑ x, Vanishing.shannonTerm (μ x) := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlog : ∀ x, μ x * logb 2 ((n : ℝ) + 1) ≤ Vanishing.shannonTerm (μ x) := by
    intro x
    by_cases hx : μ x = 0
    · simp [hx, Vanishing.shannonTerm]
    · have hpos : 0 < μ x := lt_of_le_of_ne (h.nonneg x) (Ne.symm hx)
      have hle : μ x ≤ 1 / ((n : ℝ) + 1) := atom_le μ h x
      rw [Vanishing.shannonTerm_of_pos hpos]
      have hlogle : logb 2 (μ x) ≤ logb 2 (1 / ((n : ℝ) + 1)) :=
        logb_le_logb_of_le (b := 2) (by norm_num : (1 : ℝ) < 2) hpos hle
      have hinv : logb 2 (1 / ((n : ℝ) + 1)) = -logb 2 ((n : ℝ) + 1) := by
        rw [one_div, logb_inv]
      rw [hinv] at hlogle
      nlinarith
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ Finset.univ) => hlog x
  have hscaled : ∑ x, μ x * logb 2 ((n : ℝ) + 1) = logb 2 ((n : ℝ) + 1) := by
    simp_rw [mul_comm (μ _)]
    have : ∑ x, logb 2 ((n : ℝ) + 1) * μ x =
        logb 2 ((n : ℝ) + 1) * ∑ x, μ x :=
      (Finset.mul_sum _ _ _).symm
    rw [this, h.total, mul_one]
  simpa [hscaled] using hsum

theorem logb_two_pow (N : ℕ) : logb 2 ((2 ^ N : ℕ) : ℝ) = (N : ℝ) := by
  rw [Nat.cast_pow, Nat.cast_ofNat, logb_pow 2 2 N,
    logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  simp

/-- The local lower bound `log₂(n+1) - 2` is unbounded in the number of inputs.
The subtracted `2` is the entropy of the centralized two-bit seed. -/
theorem locality_gap_unbounded (K : ℝ) : ∃ n : ℕ, K ≤ logb 2 ((n : ℝ) + 1) - 2 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (K + 2)
  refine ⟨2 ^ N - 1, ?_⟩
  have hpos : 1 ≤ 2 ^ N := Nat.one_le_pow N 2 (by decide)
  have hcast : ((2 ^ N - 1 : ℕ) : ℝ) + 1 = ((2 ^ N : ℕ) : ℝ) := by
    rw [Nat.cast_sub hpos, Nat.cast_one]
    ring
  rw [hcast, logb_two_pow]
  linarith

/-- Deterministic local CHSH value. -/
def pm (b : Bool) : ℤ :=
  if b then 1 else -1

def chshInt (a0 a1 b0 b1 : Bool) : ℤ :=
  pm a0 * (pm b0 + pm b1) + pm a1 * (pm b0 - pm b1)

theorem chsh_deterministic (a0 a1 b0 b1 : Bool) :
    chshInt a0 a1 b0 b1 = 2 ∨ chshInt a0 a1 b0 b1 = -2 := by
  cases a0 <;> cases a1 <;> cases b0 <;> cases b1 <;> decide

theorem chsh_mixture_le {ι : Type*} [Fintype ι] (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) (c : ι → ℝ) (hc : ∀ i, c i = 2 ∨ c i = -2) :
    ∑ i, w i * c i ≤ 2 := by
  have hle : ∀ i, c i ≤ (2 : ℝ) := by
    intro i
    rcases hc i with h | h <;> simp [h]
  have : ∑ i, w i * c i ≤ ∑ i, w i * 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_left (hle i) (hw i)
  have htwo : ∑ i, w i * 2 = 2 := by
    simp_rw [mul_comm (w _)]
    have : ∑ i, 2 * w i = 2 * ∑ i, w i := (Finset.mul_sum _ _ _).symm
    rw [this, h1]
    ring
  linarith

theorem q_bell_value (v : ℝ) : v + v + v - (-v) = 4 * v := by ring

/-- No finite mixture of deterministic local tables attains Bell value `4v`
when `v > 1/2`. -/
theorem not_local_chsh_mixture (v : ℝ) (hv : 1 / 2 < v) {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (h1 : ∑ i, w i = 1) (c : ι → ℝ)
    (hc : ∀ i, c i = 2 ∨ c i = -2) :
    ∑ i, w i * c i ≠ 4 * v := by
  intro hEq
  have hle := chsh_mixture_le w hw h1 c hc
  linarith [q_bell_value v]

theorem same_opposite_correlation : (3 / 4 : ℝ) * 1 + (1 / 4) * (-1) = 1 / 2 := by
  norm_num

theorem h2_quarter : Vanishing.h2 (1 / 4) = 2 - (3 / 4) * logb 2 3 := by
  have h34 : (1 : ℝ) - 1 / 4 = 3 / 4 := by norm_num
  rw [Vanishing.h2, h34, Vanishing.shannonTerm_quarter]
  have hpos : (0 : ℝ) < 3 / 4 := by norm_num
  rw [Vanishing.shannonTerm_of_pos hpos]
  have hdiv : logb 2 (3 / 4 : ℝ) = logb 2 3 - logb 2 4 := by
    rw [logb_div (by norm_num) (by norm_num)]
  have h4 : logb 2 (4 : ℝ) = 2 := by
    have : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [this, logb_pow 2 2 2, logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
    norm_num
  rw [hdiv, h4]
  ring

end LocalSeparation
end

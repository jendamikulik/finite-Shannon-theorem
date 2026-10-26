/-
Predictive equivalence, and a counterexample to "stable implies cheap".

Self-contained part of "Stillness, Predictive Stability, and Causal
Simulation" (25 October 2026, revised).

Proved here, with no `sorry`:
* total variation on a finite alphabet is symmetric, satisfies the triangle
  inequality, and is invariant under a bijection of the alphabet;
* one-step predictive agreement is an equivalence relation;
* agreement survives a common extension when the kernel of an extended history
  is determined by the kernel of its prefix, so the update descends to the
  quotient;
* a kernel that ignores its history identifies every pair of histories;
* the constant kernel that emits a fair bit is completely stable, and the
  exact shared-seed cost of one step is exactly one bit (`Sharing`);
* total variation of two probabilities is at most one, and a chain of
  experiments drifts by at most the sum of the steps, and never by more than one;
* the history-free quiet kernel is predictively trivial, reports quiet with
  probability `1 - η`, separates the two probes by `1 - 2p`, and each step costs
  `h₂(η) + h₂(p)`; `n` neutral steps cost `n` times that.

Not proved here: the imported bound `L(Tₙ) ≤ C(Tₙ) ≤ L(Tₙ) + c⋆`, the adaptive
causal cost of the quiet kernel (only the neutral policy and the one-step cost
are identified), or any statement about consciousness.
-/

import CausalSeed.Sharing
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section

open Classical Finset

namespace Stillness

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- Total variation, `½ ∑ |p - q|`. -/
def tv (p q : Y → ℝ) : ℝ := (1 / 2) * ∑ y, |p y - q y|

theorem tv_nonneg (p q : Y → ℝ) : 0 ≤ tv p q :=
  mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

theorem tv_comm (p q : Y → ℝ) : tv p q = tv q p := by
  unfold tv
  congr 1
  refine Finset.sum_congr rfl fun y _ => abs_sub_comm (p y) (q y)

theorem tv_triangle (p q r : Y → ℝ) : tv p r ≤ tv p q + tv q r := by
  unfold tv
  have hpoint : ∀ y, |p y - r y| ≤ |p y - q y| + |q y - r y| := by
    intro y
    simpa [sub_add_sub_cancel] using abs_add_le (p y - q y) (q y - r y)
  have hsum : ∑ y, |p y - r y| ≤ ∑ y, |p y - q y| + ∑ y, |q y - r y| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun y _ => hpoint y
  have hhalf := mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 1 / 2)
  linarith [hhalf]

theorem tv_self (p : Y → ℝ) : tv p p = 0 := by unfold tv; simp

/-- Total variation of two probabilities is at most one. -/
theorem tv_le_one {p q : Y → ℝ} (hp0 : ∀ y, 0 ≤ p y) (hq0 : ∀ y, 0 ≤ q y)
    (hp : ∑ y, p y = 1) (hq : ∑ y, q y = 1) : tv p q ≤ 1 := by
  have hpoint : ∀ y, |p y - q y| ≤ p y + q y := by
    intro y
    rcases le_total (q y) (p y) with h | h
    · have : |p y - q y| = p y - q y := abs_of_nonneg (sub_nonneg.mpr h)
      linarith [hq0 y]
    · have : |p y - q y| = q y - p y := by
        rw [abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      linarith [hp0 y]
  have hsum : ∑ y, |p y - q y| ≤ ∑ y, (p y + q y) :=
    Finset.sum_le_sum fun y _ => hpoint y
  have : ∑ y, (p y + q y) = 2 := by
    rw [Finset.sum_add_distrib, hp, hq]
    norm_num
  unfold tv
  linarith

/-- Total variation is unchanged by a common bijection of the alphabet. -/
theorem tv_bijection {Z : Type*} [Fintype Z] [DecidableEq Z] (e : Y ≃ Z) (p q : Y → ℝ) :
    tv (fun z => p (e.symm z)) (fun z => q (e.symm z)) = tv p q := by
  unfold tv
  congr 1
  rw [← Equiv.sum_comp e.symm]

/-! ### Predictive equivalence -/

/-- A one-step experimental kernel: history, action, outcome. -/
abbrev Kernel (A Y Hist : Type*) := Hist → A → Y → ℝ

/-- One-step predictive agreement. -/
def predRel {A Y Hist : Type*} (k : Kernel A Y Hist) (h h' : Hist) : Prop :=
  ∀ a y, k h a y = k h' a y

theorem predRel_equivalence {A Y Hist : Type*} (k : Kernel A Y Hist) :
    Equivalence (predRel k) where
  refl := fun _ _ _ => rfl
  symm := fun h a y => (h a y).symm
  trans := fun h1 h2 a y => (h1 a y).trans (h2 a y)

def predSetoid {A Y Hist : Type*} (k : Kernel A Y Hist) : Setoid Hist where
  r := predRel k
  iseqv := predRel_equivalence k

/-- Agreement survives a common extension when an extended history is scored
by the kernel of its prefix. -/
theorem extension_respects {A Y Hist : Type*} (k : Kernel A Y Hist)
    (extend : Hist → A → Y → Hist)
    (hcompat : ∀ h a y b z, k (extend h a y) b z = k h b z)
    {h h' : Hist} (he : predRel k h h') (a : A) (y : Y) :
    predRel k (extend h a y) (extend h' a y) := by
  intro b z
  rw [hcompat, hcompat, he b z]

/-- The update `([h], a, y) ↦ [hay]` is well-defined on predictive classes. -/
theorem update_well_defined {A Y Hist : Type*} (k : Kernel A Y Hist)
    (extend : Hist → A → Y → Hist)
    (hcompat : ∀ h a y b z, k (extend h a y) b z = k h b z)
    {h h' : Hist} (he : predRel k h h') (a : A) (y : Y) :
    Quotient.mk (predSetoid k) (extend h a y) =
      Quotient.mk (predSetoid k) (extend h' a y) :=
  Quotient.sound (extension_respects k extend hcompat he a y)

/-! ### Drift of a fixed experiment -/

/-- **Finite drift.** Along a chain of experiments whose successive laws differ by at most `εⱼ`
in total variation, the endpoints differ by at most the sum, and never by more than one. -/
theorem drift_bound {m : ℕ} (law : ℕ → Y → ℝ)
    (h0 : ∀ j y, 0 ≤ law j y) (htot : ∀ j, ∑ y, law j y = 1)
    (ε : ℕ → ℝ) (hstep : ∀ j, j < m → tv (law j) (law (j + 1)) ≤ ε j) :
    tv (law 0) (law m) ≤ min 1 (∑ j ∈ Finset.range m, ε j) := by
  have hone : tv (law 0) (law m) ≤ 1 := tv_le_one (h0 0) (h0 m) (htot 0) (htot m)
  have hchain : tv (law 0) (law m) ≤ ∑ j ∈ Finset.range m, ε j := by
    induction m with
    | zero => simp [tv_self]
    | succ m ih =>
        have hprev := ih (fun j hj => hstep j (Nat.lt_succ_of_lt hj))
          (tv_le_one (h0 0) (h0 m) (htot 0) (htot m))
        have htail := hstep m (Nat.lt_succ_self m)
        have htri := tv_triangle (law 0) (law m) (law (m + 1))
        have hsum :
            ∑ j ∈ Finset.range (m + 1), ε j = (∑ j ∈ Finset.range m, ε j) + ε m :=
          Finset.sum_range_succ ε m
        linarith
  exact le_min hone hchain

/-! ### Stable does not mean free -/

/-- A kernel that ignores its history. -/
def constantKernel {A Y : Type*} (p : A → Y → ℝ) : Kernel A Y Unit := fun _ a y => p a y

theorem constantKernel_stable {A Y : Type*} (p : A → Y → ℝ) :
    predRel (constantKernel p) () () := fun _ _ => rfl

theorem ignore_history_stable {A Y Hist : Type*} (p : A → Y → ℝ) (k : Kernel A Y Hist)
    (hk : ∀ h a y, k h a y = p a y) (h h' : Hist) : predRel k h h' := by
  intro a y
  rw [hk, hk]

open Sharing CausalSpectrum

/-- A fair bit. -/
def fair : Bool → ℝ := fun _ => 1 / 2

theorem fair_nonneg (b : Bool) : 0 ≤ fair b := by unfold fair; norm_num

/-- A fair bit as a joint law on a trivial first coordinate. -/
def fairStep : Unit × Bool → ℝ := fun p => fair p.2

theorem fairStep_nonneg (p : Unit × Bool) : 0 ≤ fairStep p := fair_nonneg p.2

theorem fairStep_total : ∑ p : Unit × Bool, fairStep p = 1 := by
  simp [fairStep, fair, Finset.univ_unique]

theorem fairStep_entropy : H fairStep = 1 := by
  unfold H pmfEntropy fairStep fair entTerm infoMass
  have hne : (1 / 2 : ℝ) ≠ 0 := by norm_num
  simp only [Finset.univ_unique, Finset.sum_singleton, hne, ite_false]
  have hlog : Real.logb 2 (1 / 2 : ℝ) = -1 := by
    rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.logb_inv,
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  rw [hlog]
  norm_num

/-- **Stable does not mean free.** Emitting a fair bit with no dependence on
the history is predictively trivial, and the exact seed cost of that one step
is one bit. -/
theorem fair_stable_not_free :
    predRel (constantKernel (fun (_ : Unit) => fair)) () () ∧ cost fairStep = 1 := by
  refine ⟨constantKernel_stable _, ?_⟩
  rw [sharing_criterion fairStep fairStep_nonneg fairStep_total, fairStep_entropy]


/-! ### A stable kernel that is not free -/

/-- One step of the quiet kernel: a report bit of bias `η`, independent of a response bit whose
bias is `p` on action `false` and `1 - p` on action `true`. -/
def quietStep (η p : ℝ) (a : Bool) : Bool × Bool → ℝ :=
  fun rb => bernoulli η rb.1 * bernoulli (if a then 1 - p else p) rb.2

theorem quietStep_nonneg {η p : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Bool) (rb : Bool × Bool) : 0 ≤ quietStep η p a rb := by
  unfold quietStep
  apply mul_nonneg
  · exact bernoulli_nonneg hη0 hη1 _
  · by_cases ha : a
    · simp [ha]; exact bernoulli_nonneg (by linarith) (by linarith) _
    · simp [ha]; exact bernoulli_nonneg hp0 hp1 _

theorem quietStep_total {η p : ℝ} (a : Bool) : ∑ rb, quietStep η p a rb = 1 := by
  unfold quietStep
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, bernoulli_total, mul_one, bernoulli_total]

/-- The kernel ignores its history, so every pair of histories is predictively equivalent. -/
theorem quiet_stable {η p : ℝ} {Hist : Type*} (h h' : Hist) :
    predRel (fun (_ : Hist) (a : Bool) => quietStep η p a) h h' := by
  intro _ _
  rfl

/-- Quiet-report probability under the neutral action `false`. -/
theorem quiet_report {η p : ℝ} :
    (∑ r, bernoulli η r * (if r = false then (1 : ℝ) else 0)) = 1 - η := by
  have hpair : (univ : Finset Bool) = {false, true} := by
    ext b; cases b <;> decide
  rw [hpair, Finset.sum_pair (by decide : false ≠ true)]
  unfold bernoulli
  simp

theorem quiet_response_true {η p : ℝ} (b : Bool) :
    (∑ r, quietStep η p true (r, b)) = bernoulli (1 - p) b := by
  have hstep : ∀ r, quietStep η p true (r, b) = bernoulli η r * bernoulli (1 - p) b := by
    intro r
    simp [quietStep]
  simp_rw [hstep, ← Finset.sum_mul, bernoulli_total, one_mul]

theorem quiet_response_false {η p : ℝ} (b : Bool) :
    (∑ r, quietStep η p false (r, b)) = bernoulli p b := by
  have hstep : ∀ r, quietStep η p false (r, b) = bernoulli η r * bernoulli p b := by
    intro r
    simp [quietStep]
  simp_rw [hstep, ← Finset.sum_mul, bernoulli_total, one_mul]

/-- Discrimination of the response bit between the two probes is `1 - 2p` for `p ≤ 1/2`. -/
theorem quiet_discrimination {p : ℝ} (η : ℝ) (hp : p ≤ 1 / 2) :
    tv (fun b => ∑ r, quietStep η p true (r, b)) (fun b => ∑ r, quietStep η p false (r, b)) =
      1 - 2 * p := by
  have hL : (fun b => ∑ r, quietStep η p true (r, b)) = bernoulli (1 - p) :=
    funext quiet_response_true
  have hR : (fun b => ∑ r, quietStep η p false (r, b)) = bernoulli p :=
    funext quiet_response_false
  rw [hL, hR]
  unfold tv
  have hpair : (univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  rw [hpair, Finset.sum_pair (by decide : false ≠ true)]
  simp only [bernoulli]
  repeat rw [if_neg (by decide : (false : Bool) ≠ true)]
  simp only [ite_true]
  have h1 : |1 - (1 - p) - (1 - p)| = 1 - 2 * p := by
    have : 1 - (1 - p) - (1 - p) ≤ 0 := by linarith
    rw [abs_of_nonpos this]
    ring
  have h2 : |(1 - p) - p| = 1 - 2 * p := by
    have : 0 ≤ (1 - p) - p := by linarith
    rw [abs_of_nonneg this]
    ring
  rw [h1, h2]
  ring

theorem quietStep_eq {η p : ℝ} (a : Bool) :
    quietStep η p a = indepJoint (bernoulli η) (bernoulli (if a then 1 - p else p)) := rfl

/-- One quiet step costs `h₂(η) + h₂(p)`, for either action. -/
theorem quiet_step_cost {η p : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (a : Bool) : cost (quietStep η p a) = binEntropy η + binEntropy p := by
  rw [quietStep_eq]
  by_cases ha : a
  · have hq0 : 0 ≤ 1 - p := by linarith
    have hq1 : 1 - p ≤ 1 := by linarith
    rw [if_pos ha]
    rw [indep_cost (bernoulli_nonneg hη0 hη1) (bernoulli_nonneg hq0 hq1)
        (bernoulli_total η) (bernoulli_total (1 - p))]
    rw [bernoulli_entropy hη0 hη1, bernoulli_entropy hq0 hq1, binEntropy_symm]
  · rw [if_neg ha]
    rw [indep_cost (bernoulli_nonneg hη0 hη1) (bernoulli_nonneg hp0 hp1)
        (bernoulli_total η) (bernoulli_total p)]
    rw [bernoulli_entropy hη0 hη1, bernoulli_entropy hp0 hp1]

/-- The product seed of `n` independent quiet steps. -/
def quietSeedN (η p : ℝ) (n : ℕ) : (Fin n → Bool × Bool) → ℝ :=
  fun u => ∏ i, indepJoint (bernoulli η) (bernoulli p) (u i)

/-- `n` independent quiet steps cost `n` times one step. -/
theorem quietSeedN_entropy {η p : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) : H (quietSeedN η p n) = (n : ℝ) * (binEntropy η + binEntropy p) := by
  unfold quietSeedN
  have h0 := indepJoint_nonneg (bernoulli_nonneg hη0 hη1) (bernoulli_nonneg hp0 hp1)
  have htot := indepJoint_total (bernoulli_total η) (bernoulli_total p)
  have hent : pmfEntropy (indepJoint (bernoulli η) (bernoulli p)) =
      binEntropy η + binEntropy p := by
    have hcost := indep_cost (bernoulli_nonneg hη0 hη1) (bernoulli_nonneg hp0 hp1)
      (bernoulli_total η) (bernoulli_total p)
    rw [sharing_criterion _ h0 htot] at hcost
    rw [bernoulli_entropy hη0 hη1, bernoulli_entropy hp0 hp1] at hcost
    simpa [H] using hcost
  rw [H, product_entropy n _ h0 htot, hent]

/-- Neutral continuation, every step, is exactly that product seed. -/
theorem quiet_neutral_law {η p : ℝ} (n : ℕ) :
    (fun w : Fin n → Bool × Bool => ∏ i, quietStep η p false (w i)) = quietSeedN η p n := by
  funext w
  unfold quietSeedN
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [quietStep_eq]
  simp

end Stillness

end

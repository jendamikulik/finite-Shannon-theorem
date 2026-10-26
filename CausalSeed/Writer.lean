/-
Cancellation, observable memory, and exact causal seeds for a moment writer.

Formalization of the finite probabilistic bridge (26 October 2026).

Proved here, with no `sorry`:
* on any additive group, successive differences invert partial sums;
* the terminal cancellation identities `S₂ = 0` and `M₂ = (x₁ - x₂) • W`;
* on a finite additive alphabet the always-sum transcript is an injective
  function of the deposit vector, so its exact one-seed cost equals the joint
  deposit entropy, attained by using the deposits;
* every deterministic readout of those deposits costs at most that entropy;
* the sum-only terminal interface of the cancellation costs `0`; an injective
  moment readout costs `H(W)`;
* on a torsion-free group, a nonzero integer address gap acts injectively;
* one decoder on the deposit seed reproduces every adaptive sum-or-moment
  policy, and the exact interface cost equals the joint deposit entropy.

Not proved here: a general controlled-tree simulator for kernels that are not
functions of one deposit vector, the companion sandwich on zero branches,
or any physiological, energetic, or consciousness reading. The finite-support
law is represented on a finite additive alphabet, so every transcript label
that actually occurs is an element of that alphabet.
-/

import CausalSeed.Sharing
import CausalSeed.Penalty
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Torsion
import Mathlib.Data.Fin.Basic

noncomputable section

open Classical Finset Sharing CausalSpectrum

namespace Writer

variable {β : Type} [AddCommGroup β]

/-- Values visible up to time `t`, summed in order. -/
def accumulate {n : ℕ} (v : Fin n → β) (t : Fin n) : β :=
  ∑ i ∈ univ.filter (fun j : Fin n => j.val ≤ t.val), v i

/-- Running sum `S_t = S_{t-1} + Z_t`. -/
def partialSums {n : ℕ} (z : Fin n → β) : Fin n → β :=
  fun t => accumulate z t

/-- Running moment `M_t = M_{t-1} + x_t Z_t`. -/
def moments {n : ℕ} (x : Fin n → ℤ) (z : Fin n → β) : Fin n → β :=
  fun t => accumulate (fun i => x i • z i) t

theorem accumulate_zero {n : ℕ} (v : Fin n → β) (hn : 0 < n) :
    accumulate v ⟨0, hn⟩ = v ⟨0, hn⟩ := by
  unfold accumulate
  have hs : univ.filter (fun j : Fin n => j.val ≤ 0) = {⟨0, hn⟩} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro hj
      exact Fin.ext (Nat.eq_zero_of_le_zero hj)
    · intro hj
      simp [hj]
  rw [hs, Finset.sum_singleton]

private theorem prefix_succ {n : ℕ} (k : ℕ) (hk : k + 1 < n) :
    (univ.filter fun j : Fin n => j.val ≤ k + 1) =
      insert (⟨k + 1, hk⟩ : Fin n)
        (univ.filter fun j : Fin n => j.val ≤ k) := by
  ext j
  simp only [mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro hj
    rcases Nat.lt_or_eq_of_le hj with hlt | heq
    · right
      exact Nat.le_of_lt_succ hlt
    · left
      exact Fin.ext heq
  · intro h
    rcases h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_trans h (Nat.le_succ k)

theorem accumulate_succ {n : ℕ} (v : Fin n → β) (k : ℕ) (hk : k + 1 < n) :
    accumulate v ⟨k + 1, hk⟩ =
      accumulate v ⟨k, Nat.lt_of_succ_lt hk⟩ + v ⟨k + 1, hk⟩ := by
  unfold accumulate
  rw [prefix_succ k hk]
  have hnot : (⟨k + 1, hk⟩ : Fin n) ∉ univ.filter (fun j : Fin n => j.val ≤ k) := by
    intro h
    have hle : (⟨k + 1, hk⟩ : Fin n).val ≤ k := (Finset.mem_filter.mp h).2
    have : k + 1 ≤ k := by
      change (⟨k + 1, hk⟩ : Fin n).val ≤ k at hle
      simpa using hle
    exact Nat.not_succ_le_self k this
  rw [Finset.sum_insert hnot]
  abel

/-- Deposits recovered by `Z_0 = S_0` and `Z_t = S_t - S_{t-1}`. -/
def differences {n : ℕ} (s : Fin n → β) : Fin n → β :=
  fun t =>
    if ht : t.val = 0 then s t
    else s t - s ⟨t.val - 1, Nat.lt_trans (Nat.pred_lt ht) t.isLt⟩

theorem differences_partialSums {n : ℕ} (z : Fin n → β) :
    differences (partialSums z) = z := by
  funext t
  suffices ∀ k, ∀ hk : k < n, differences (partialSums z) ⟨k, hk⟩ = z ⟨k, hk⟩ by
    simpa using this t.val t.isLt
  intro k
  induction k with
  | zero =>
      intro hk
      have hz := accumulate_zero z hk
      simp [differences, partialSums, hz]
  | succ k ih =>
      intro hk
      have hk0 : k < n := Nat.lt_of_succ_lt hk
      have hne : (⟨k + 1, hk⟩ : Fin n).val ≠ 0 := by
        change k + 1 ≠ 0
        omega
      have hpred :
          (⟨(⟨k + 1, hk⟩ : Fin n).val - 1,
            Nat.lt_trans (Nat.pred_lt hne) (⟨k + 1, hk⟩ : Fin n).isLt⟩ : Fin n) =
            ⟨k, hk0⟩ := by
        apply Fin.ext
        change (k + 1) - 1 = k
        omega
      rw [differences, dif_neg hne, hpred]
      simp only [partialSums]
      have hidx : (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) = ⟨k, hk0⟩ := Fin.ext rfl
      rw [accumulate_succ z k hk, hidx]
      abel


theorem partialSums_differences {n : ℕ} (s : Fin n → β) :
    partialSums (differences s) = s := by
  funext t
  suffices ∀ k, ∀ hk : k < n, partialSums (differences s) ⟨k, hk⟩ = s ⟨k, hk⟩ by
    simpa using this t.val t.isLt
  intro k
  induction k with
  | zero =>
      intro hk
      have hdiff : differences s ⟨0, hk⟩ = s ⟨0, hk⟩ := by
        simp [differences]
      rw [partialSums, accumulate_zero (differences s) hk, hdiff]
  | succ k ih =>
      intro hk
      have hk0 : k < n := Nat.lt_of_succ_lt hk
      have hne : (⟨k + 1, hk⟩ : Fin n).val ≠ 0 := by
        change k + 1 ≠ 0
        omega
      have hpred :
          (⟨(⟨k + 1, hk⟩ : Fin n).val - 1,
            Nat.lt_trans (Nat.pred_lt hne) (⟨k + 1, hk⟩ : Fin n).isLt⟩ : Fin n) =
            ⟨k, hk0⟩ := by
        apply Fin.ext
        change (k + 1) - 1 = k
        omega
      rw [partialSums, accumulate_succ (differences s) k hk]
      have hidx : (⟨k, Nat.lt_of_succ_lt hk⟩ : Fin n) = ⟨k, hk0⟩ := Fin.ext rfl
      rw [hidx, ← partialSums, ih hk0, differences, dif_neg hne, hpred]
      abel

/-- Partial sums are a bijection: the deposit vector and the sum transcript
determine one another. -/
def sumEquiv {n : ℕ} : (Fin n → β) ≃ (Fin n → β) where
  toFun := partialSums
  invFun := differences
  left_inv := differences_partialSums
  right_inv := partialSums_differences

theorem partialSums_injective {n : ℕ} :
    Function.Injective (partialSums : (Fin n → β) → Fin n → β) :=
  sumEquiv.injective

/-- On a torsion-free additive group a nonzero integer acts injectively.
A finite nontrivial group need not be torsion-free; the entropy statements
below therefore keep injectivity as a hypothesis unless this instance is
present. -/
theorem gap_injective [HasUniqueDiv β] {x1 x2 : ℤ} (h : x1 ≠ x2) :
    Function.Injective (fun w : β => (x1 - x2) • w) :=
  zsmul_right_injective (sub_ne_zero.mpr h)

/-! ### Adaptive probes

One decoder reads the deposit seed. A policy only chooses, at each time and
history, whether the answer is the running sum or the running moment.
-/

inductive Probe
  | sum
  | moment
  deriving DecidableEq

instance : Fintype Probe where
  elems := {Probe.sum, Probe.moment}
  complete := by
    intro p
    cases p <;> simp

abbrev Policy (n : ℕ) (β : Type) := (t : Fin n) → (Fin t.val → β) → Probe

def step {n : ℕ} (x : Fin n → ℤ) (z : Fin n → β) (t : Fin n) : Probe → β
  | .sum => partialSums z t
  | .moment => moments x z t

def writerDecode {n : ℕ} (x : Fin n → ℤ) :
    (Fin n → β) → (t : Fin n) → Probe → β :=
  fun z t p => step x z t p

/-- Replay a decoder under an adaptive policy. The recursive call is only the
strictly shorter history. -/
def run {n : ℕ} {σ : Type} (decode : σ → (t : Fin n) → Probe → β)
    (choose : Policy n β) (s : σ) (t : Fin n) : β :=
  decode s t (choose t (fun i =>
    run decode choose s ⟨i.val, Nat.lt_trans i.isLt t.isLt⟩))
termination_by t.val

def alwaysSum {n : ℕ} : Policy n β := fun _ _ => .sum

def transcript {n : ℕ} (x : Fin n → ℤ) (choose : Policy n β) (z : Fin n → β) :
    Fin n → β :=
  fun t => run (writerDecode x) choose z t

theorem run_writer_alwaysSum {n : ℕ} (x : Fin n → ℤ) (z : Fin n → β) (t : Fin n) :
    run (writerDecode x) alwaysSum z t = partialSums z t := by
  rw [run, alwaysSum, writerDecode, step]

theorem transcript_alwaysSum {n : ℕ} (x : Fin n → ℤ) (z : Fin n → β) :
    transcript x alwaysSum z = partialSums z := by
  funext t
  exact run_writer_alwaysSum x z t

/-! ### Cancellation -/

/-- Two deposits that cancel: `Z₁ = W`, `Z₂ = -W`. -/
def cancelZ (w : β) : Fin 2 → β :=
  fun t => if t.val = 0 then w else -w

theorem cancel_terminal_sum (w : β) :
    partialSums (cancelZ w) ⟨1, by decide⟩ = 0 := by
  have hstep := accumulate_succ (cancelZ w) 0 (by decide : 0 + 1 < 2)
  rw [partialSums, hstep, accumulate_zero (cancelZ w) (by decide)]
  simp [cancelZ]

theorem cancel_terminal_moment (x1 x2 : ℤ) (w : β) :
    moments (fun t : Fin 2 => if t.val = 0 then x1 else x2) (cancelZ w) ⟨1, by decide⟩ =
      (x1 - x2) • w := by
  have hstep := accumulate_succ
      (fun t : Fin 2 => (if t.val = 0 then x1 else x2) • cancelZ w t) 0
      (by decide : 0 + 1 < 2)
  rw [moments, hstep,
    accumulate_zero (fun t : Fin 2 => (if t.val = 0 then x1 else x2) • cancelZ w t)
      (by decide)]
  simp [cancelZ, smul_neg, sub_smul]
  abel

/-! ### Entropy on a finite alphabet -/

variable {α γ : Type} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]

def push (μ : α → ℝ) (f : α → γ) : γ → ℝ :=
  fun c => ∑ a, if f a = c then μ a else 0

theorem push_nonneg {μ : α → ℝ} (h0 : ∀ a, 0 ≤ μ a) (f : α → γ) (c : γ) :
    0 ≤ push μ f c := by
  unfold push
  exact Finset.sum_nonneg fun a _ => by
    by_cases h : f a = c
    · simp [h, h0 a]
    · simp [h]

theorem push_total {μ : α → ℝ} (htot : ∑ a, μ a = 1) (f : α → γ) :
    ∑ c, push μ f c = 1 := by
  unfold push
  rw [Finset.sum_comm]
  have hpoint : ∀ a, ∑ c, (if f a = c then μ a else 0) = μ a := by
    intro a
    rw [Finset.sum_eq_single (f a)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · intro h
      exact absurd (Finset.mem_univ (f a)) h
  simp [hpoint, htot]

def dirac (c : γ) : γ → ℝ :=
  fun y => if y = c then 1 else 0

theorem dirac_nonneg (c : γ) (y : γ) : 0 ≤ dirac c y := by
  unfold dirac
  by_cases h : y = c <;> simp [h]

theorem dirac_total (c : γ) : ∑ y, dirac c y = 1 := by
  unfold dirac
  rw [Finset.sum_eq_single c]
  · simp
  · intro y _ hy
    rw [if_neg hy]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem H_dirac (c : γ) : H (dirac c) = 0 := by
  unfold H pmfEntropy dirac
  rw [Finset.sum_eq_single c]
  · simp [entTerm_one]
  · intro y _ hy
    rw [if_neg hy, entTerm_zero]
  · intro h
    exact absurd (Finset.mem_univ c) h

theorem push_const {μ : α → ℝ} (htot : ∑ a, μ a = 1) (c : γ) :
    push μ (fun _ : α => c) = dirac c := by
  funext y
  unfold push dirac
  by_cases hy : y = c
  · subst hy
    simp [htot]
  · have hc : ¬ c = y := Ne.symm hy
    simp [hy, hc]

theorem entropy_push_le (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (f : α → γ) :
    H (push μ f) ≤ H μ :=
  entropy_of_function μ h0 f

private theorem entTerm_sum_at_most_one (g : α → ℝ) (a0 : α)
    (hg : ∀ a, a ≠ a0 → g a = 0) :
    entTerm (∑ a, g a) = ∑ a, entTerm (g a) := by
  have hsum : ∑ a, g a = g a0 := by
    rw [Finset.sum_eq_single a0]
    · intro a _ ha
      exact hg a ha
    · intro h
      exact absurd (Finset.mem_univ a0) h
  have hent : ∑ a, entTerm (g a) = entTerm (g a0) := by
    rw [Finset.sum_eq_single a0]
    · intro a _ ha
      rw [hg a ha, entTerm_zero]
    · intro h
      exact absurd (Finset.mem_univ a0) h
  rw [hsum, hent]

theorem entropy_push_injective (μ : α → ℝ) (f : α → γ) (hf : Function.Injective f) :
    H (push μ f) = H μ := by
  unfold H pmfEntropy push
  have hpoint : ∀ a, entTerm (μ a) =
      ∑ c, entTerm (if f a = c then μ a else 0) := by
    intro a
    rw [Finset.sum_eq_single (f a)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc, entTerm_zero]
    · intro h
      exact absurd (Finset.mem_univ (f a)) h
  rw [Finset.sum_congr rfl fun a _ => hpoint a, Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases h : ∃ a, f a = c
  · obtain ⟨a0, ha0⟩ := h
    refine entTerm_sum_at_most_one (fun a => if f a = c then μ a else 0) a0 ?_
    intro a ha
    have hne : f a ≠ c := by
      intro heq
      exact ha (hf (heq.trans ha0.symm))
    simp [hne]
  · have hnone : ∀ a, f a ≠ c := by
      intro a ha
      exact h ⟨a, ha⟩
    have hzero : ∀ a, (if f a = c then μ a else 0) = 0 := by
      intro a
      simp [hnone a]
    simp [hzero, entTerm_zero]

def readoutRealization (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1)
    (f : α → γ) : OneRealization (push μ f) where
  Seed := α
  fin := inferInstance
  decEq := inferInstance
  law := μ
  nonneg := h0
  total := htot
  decode := f
  exact := fun _ => rfl

theorem readout_cost_le (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1)
    (f : α → γ) : oneCost (push μ f) ≤ H μ := by
  refine csInf_le ?_ ⟨readoutRealization μ h0 htot f, rfl⟩
  use 0
  rintro z ⟨r, rfl⟩
  exact H_nonneg r.nonneg fun s => prob_le_one r.nonneg r.total s

theorem injective_readout_cost (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1)
    (f : α → γ) (hf : Function.Injective f) :
    oneCost (push μ f) = H μ := by
  rw [one_criterion (push_nonneg h0 f) (push_total htot f), entropy_push_injective μ f hf]

theorem const_readout_cost (μ : α → ℝ) (_h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1)
    (c : γ) : oneCost (push μ (fun _ : α => c)) = 0 := by
  rw [push_const htot c, one_criterion (dirac_nonneg c) (dirac_total c), H_dirac c]

variable [Fintype β] [DecidableEq β]

/-- **Observable writer.** The always-sum transcript costs exactly `H(Z)`. -/
theorem observable_writer_cost {n : ℕ} (μ : (Fin n → β) → ℝ)
    (h0 : ∀ z, 0 ≤ μ z) (htot : ∑ z, μ z = 1) :
    oneCost (push μ partialSums) = H μ ∧
      ∀ {γ : Type} [Fintype γ] [DecidableEq γ] (f : (Fin n → β) → γ),
        oneCost (push μ f) ≤ H μ := by
  refine ⟨injective_readout_cost μ h0 htot partialSums partialSums_injective, ?_⟩
  intro γ _ _ f
  exact readout_cost_le μ h0 htot f

theorem independent_writer_cost {n : ℕ} (ρ : β → ℝ)
    (h0 : ∀ b, 0 ≤ ρ b) (htot : ∑ b, ρ b = 1) :
    oneCost (push (fun f : Fin n → β => ∏ i, ρ (f i)) partialSums) =
      (n : ℝ) * H ρ := by
  have h0f : ∀ f : Fin n → β, 0 ≤ (∏ i, ρ (f i)) :=
    fun f => Finset.prod_nonneg fun i _ => h0 (f i)
  have htotf := product_total n ρ htot
  rw [injective_readout_cost _ h0f htotf partialSums partialSums_injective]
  simpa [H] using product_entropy n ρ h0 htot

theorem writer_chain
    {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : X × Y → ℝ) (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    H μ = H (Sharing.marginal μ) + Sharing.condEntropy μ :=
  Sharing.chain_rule h0 htot

/-- Sum-only terminal cost is zero; an injective moment costs `H(W)`. -/
theorem readout_dependent_cost (μ : β → ℝ) (h0 : ∀ w, 0 ≤ μ w) (htot : ∑ w, μ w = 1)
    {γ : Type} [Fintype γ] [DecidableEq γ] (moment : β → γ)
    (hmom : Function.Injective moment) :
    oneCost (push μ (fun w => partialSums (cancelZ w) ⟨1, by decide⟩)) = 0 ∧
      oneCost (push μ moment) = H μ := by
  have hconst : (fun w : β => partialSums (cancelZ w) ⟨1, by decide⟩) = fun _ => (0 : β) := by
    funext w
    exact cancel_terminal_sum w
  constructor
  · rw [hconst]
    exact const_readout_cost μ h0 htot (0 : β)
  · exact injective_readout_cost μ h0 htot moment hmom

theorem moment_gap_cost (μ : β → ℝ) (h0 : ∀ w, 0 ≤ μ w) (htot : ∑ w, μ w = 1)
    (x1 x2 : ℤ) (hinj : Function.Injective (fun w : β => (x1 - x2) • w)) :
    oneCost (push μ (fun w =>
      moments (fun t : Fin 2 => if t.val = 0 then x1 else x2) (cancelZ w) ⟨1, by decide⟩)) =
      H μ := by
  have heq : (fun w : β =>
      moments (fun t : Fin 2 => if t.val = 0 then x1 else x2) (cancelZ w) ⟨1, by decide⟩) =
      fun w => (x1 - x2) • w := by
    funext w
    exact cancel_terminal_moment x1 x2 w
  rw [heq]
  exact injective_readout_cost μ h0 htot (fun w => (x1 - x2) • w) hinj

theorem moment_gap_cost_torsionFree [HasUniqueDiv β]
    (μ : β → ℝ) (h0 : ∀ w, 0 ≤ μ w) (htot : ∑ w, μ w = 1)
    {x1 x2 : ℤ} (hgap : x1 ≠ x2) :
    oneCost (push μ (fun w =>
      moments (fun t : Fin 2 => if t.val = 0 then x1 else x2) (cancelZ w) ⟨1, by decide⟩)) =
      H μ :=
  moment_gap_cost μ h0 htot x1 x2 (gap_injective hgap)

/-! ### One seed for every adaptive policy -/

structure WriterSeed {n : ℕ} (x : Fin n → ℤ) (μ : (Fin n → β) → ℝ) where
  Seed : Type
  fin : Fintype Seed
  decEq : DecidableEq Seed
  law : Seed → ℝ
  nonneg : ∀ s, 0 ≤ law s
  total : ∑ s, law s = 1
  decode : Seed → (t : Fin n) → Probe → β
  exact : ∀ choose : Policy n β, ∀ y : Fin n → β,
    (∑ s, if (fun t => run decode choose s t) = y then law s else 0) =
      (∑ z, if transcript x choose z = y then μ z else 0)

attribute [instance] WriterSeed.fin WriterSeed.decEq

def interfaceCost {n : ℕ} (x : Fin n → ℤ) (μ : (Fin n → β) → ℝ) : ℝ :=
  sInf { H r.law | r : WriterSeed x μ }

def depositSeed {n : ℕ} (x : Fin n → ℤ) (μ : (Fin n → β) → ℝ)
    (h0 : ∀ z, 0 ≤ μ z) (htot : ∑ z, μ z = 1) : WriterSeed x μ where
  Seed := Fin n → β
  fin := inferInstance
  decEq := inferInstance
  law := μ
  nonneg := h0
  total := htot
  decode := writerDecode x
  exact := fun _ _ => rfl

theorem writerSeed_entropy_ge {n : ℕ} (x : Fin n → ℤ) {μ : (Fin n → β) → ℝ}
    (r : WriterSeed x μ) : H μ ≤ H r.law := by
  let f : r.Seed → (Fin n → β) := fun s t => run r.decode alwaysSum s t
  have hpush : push r.law f = push μ partialSums := by
    funext y
    have hexact := r.exact alwaysSum y
    simp only [push, f, transcript_alwaysSum] at hexact ⊢
    exact hexact
  have hle : H (push μ partialSums) ≤ H r.law := by
    simpa [hpush] using entropy_push_le r.law r.nonneg f
  simpa [entropy_push_injective μ partialSums partialSums_injective] using hle

/-- **Observable writer, adaptive interface.** One deposit seed and one decoder
serve every policy, at entropy `H(Z)`. Every exact interface seed costs at
least that, because the always-sum policy recovers the deposits. -/
theorem adaptive_interface_cost {n : ℕ} (x : Fin n → ℤ) (μ : (Fin n → β) → ℝ)
    (h0 : ∀ z, 0 ≤ μ z) (htot : ∑ z, μ z = 1) :
    interfaceCost x μ = H μ := by
  apply le_antisymm
  · refine csInf_le ?_ ⟨depositSeed x μ h0 htot, rfl⟩
    use 0
    rintro z ⟨r, rfl⟩
    exact H_nonneg r.nonneg fun s => prob_le_one r.nonneg r.total s
  · refine le_csInf ⟨H μ, depositSeed x μ h0 htot, rfl⟩ ?_
    rintro z ⟨r, rfl⟩
    exact writerSeed_entropy_ge x r

end Writer

end

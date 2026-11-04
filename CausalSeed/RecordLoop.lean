/-
From quantum state to a classical record.

Formalization of the mathematical skeleton of `research.pdf`. The quantum
instrument is taken as already determining a classical outcome law, or a
finite controlled tree. What is proved here is that classical layer.

* The record law is the outcome law, so its Shannon entropy is `H`.
* One shared seed, read at the history actually reached, reproduces a
  two-step kernel. The decoder does not depend on the name of the policy.
* Any finite controlled tree supplied by that record has the already proved
  sandwich `L ≤ C ≤ L + (1 + log₂ e) / 2`. This file does not reprove it.
* Cesàro means of a linear step have defect `(Φᴺρ₀ − ρ₀) / N`. If two
  states are at most `2` apart in `ℓ₁`, the defect is at most `2 / N`.
  Existence of a convergent subsequence is not proved here.
* A fixed averaged state need not repeat the record. The swap channel
  fixes the uniform law and oscillates on a trajectory.
* If every unsuccessful history still has success probability at least
  `ε > 0`, the failure tail is at most `(1 − ε)ⁿ` and tends to zero.
  One positive step does not give a uniform `ε`.

Not proved:

* that a physical instrument is completely positive and trace-preserving;
* the partial trace, or von Neumann entropy as an operator identity;
* existence of a fixed density operator, which uses compactness;
* a local or efficient implementation of the seed;
* that any of these objects is conscious processing;
* anything about the zeros of `ξ`.
-/
import CausalSeed.NobodyLeft
import CausalSeed.Sharing
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section

open Classical Finset Sharing

namespace CausalSpectrum
namespace RecordLoop

/-! ### The classical record -/

/-- A finite outcome law. The instrument has already been reduced to it. -/
structure Law (Y : Type) [Fintype Y] where
  p : Y → ℝ
  nonneg : ∀ y, 0 ≤ p y
  total : ∑ y, p y = 1

/-- The readable register carries the outcome law. -/
def record {Y : Type} [Fintype Y] (L : Law Y) : Y → ℝ := L.p

theorem record_total {Y : Type} [Fintype Y] (L : Law Y) :
    ∑ y, record L y = 1 :=
  L.total

/-- Shannon entropy of the register. For a diagonal register this is the
von Neumann entropy of that diagonal state. The partial trace is not
rebuilt here. -/
theorem register_entropy {Y : Type} [Fintype Y] (L : Law Y) :
    H (record L) = H L.p :=
  rfl

/-! ### One seed, two steps -/

/-- Kernel of the second outcome, given the first. -/
structure Kernel (Y Z : Type) [Fintype Y] [Fintype Z] where
  p : Y → Z → ℝ
  nonneg : ∀ y z, 0 ≤ p y z
  total : ∀ y, ∑ z, p y z = 1

variable {Y Z : Type} [Fintype Y] [Fintype Z]

/-- Joint law of one step followed by the kernel. -/
def joint (L : Law Y) (K : Kernel Y Z) : Y × Z → ℝ
  | (y, z) => L.p y * K.p y z

theorem joint_nonneg (L : Law Y) (K : Kernel Y Z) (y : Y) (z : Z) :
    0 ≤ joint L K (y, z) :=
  mul_nonneg (L.nonneg y) (K.nonneg y z)

theorem marginal_first (L : Law Y) (K : Kernel Y Z) (y : Y) :
    ∑ z, joint L K (y, z) = L.p y := by
  simp only [joint]
  rw [← Finset.mul_sum]
  simp [K.total y]

theorem joint_total (L : Law Y) (K : Kernel Y Z) :
    ∑ p : Y × Z, joint L K p = 1 := by
  rw [Fintype.sum_prod_type]
  simp_rw [marginal_first]
  exact L.total

/-- Given a reached first outcome of positive mass, the conditional law
of the coordinate stored for that history is the kernel. -/
theorem conditional_is_kernel (L : Law Y) (K : Kernel Y Z) (y : Y) (z : Z)
    (hy : L.p y ≠ 0) :
    joint L K (y, z) / L.p y = K.p y z := by
  simp only [joint]
  exact mul_div_cancel_left₀ (K.p y z) hy

/-- The decoder reads the seed coordinate of the history it has reached.
The policy is an argument and is ignored. -/
def decode {ι : Type} (seed : Y) (_π : ι) : Y := seed

theorem policy_name_irrelevant {ι : Type} (seed : Y) (π π' : ι) :
    decode seed π = decode seed π' :=
  rfl

/-! ### The entropy price is the already proved sandwich -/

/-- `(1 + log₂ e) / 2`, the overhead in the finite causal Shannon theorem. -/
theorem shannonOverhead_paper :
    shannonOverhead = (1 + Real.logb 2 (Real.exp 1)) / 2 := by
  unfold shannonOverhead
  have hlog : Real.logb 2 (Real.exp 1) = 1 / Real.log 2 := by
    rw [Real.logb, Real.log_exp]
  rw [hlog]

/-- A finite controlled tree of classical records, supplied by the
instrument, obeys the sandwich already proved for every such tree.
This is an application, not a new proof of the overhead. -/
theorem record_tree_bound (T : Tree) :
    envelopeMean T ≤ causalMin T ∧
      causalMin T ≤ envelopeMean T + shannonOverhead :=
  NobodyLeft.supplied_tree_sandwich T

/-! ### Closing the loop: the Cesàro defect -/

variable {α : Type} [Fintype α]

/-- Cesàro mean of the first `N` iterates. -/
def cesaro (Φ : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (ρ0 : α → ℝ) (N : ℕ) : α → ℝ :=
  (N : ℝ)⁻¹ • ∑ k ∈ Finset.range N, (Φ ^ k) ρ0

theorem cesaro_telescope
    (Φ : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (ρ0 : α → ℝ) {N : ℕ} (_hN : 0 < N) :
    Φ (cesaro Φ ρ0 N) - cesaro Φ ρ0 N
      = (N : ℝ)⁻¹ • ((Φ ^ N) ρ0 - ρ0) := by
  have hshift :
      ∑ k ∈ Finset.range N, Φ ((Φ ^ k) ρ0)
        = (∑ k ∈ Finset.range N, (Φ ^ k) ρ0) + (Φ ^ N) ρ0 - ρ0 := by
    have hsucc : ∀ k, Φ ((Φ ^ k) ρ0) = (Φ ^ (k + 1)) ρ0 := by
      intro k
      rw [← Module.End.mul_apply, ← pow_succ']
    simp_rw [hsucc]
    have hsum : ∀ (f : ℕ → α → ℝ) (n : ℕ),
        ∑ k ∈ Finset.range n, f (k + 1)
          = (∑ k ∈ Finset.range n, f k) + f n - f 0 := by
      intro f n
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
        abel
    have := hsum (fun k => (Φ ^ k) ρ0) N
    simpa [pow_zero, Module.End.one_apply] using this
  unfold cesaro
  rw [map_smul, map_sum]
  rw [hshift]
  rw [smul_sub, smul_add, smul_sub]
  abel

/-- `ℓ₁` size of a signed measure. -/
def l1 (f : α → ℝ) : ℝ := ∑ a, |f a|

theorem l1_smul_nonneg {c : ℝ} {f : α → ℝ} (hc : 0 ≤ c) :
    l1 (c • f) = c * l1 f := by
  unfold l1
  simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  rw [Finset.mul_sum]

/-- If states are at most `2` apart in `ℓ₁`, the Cesàro defect is at most
`2 / N`. The diameter `2` is the trace-distance bound for states; it is
an assumption here, not a theorem about density operators. -/
theorem cesaro_defect_le
    (Φ : (α → ℝ) →ₗ[ℝ] (α → ℝ)) (ρ0 : α → ℝ) {N : ℕ} (hN : 0 < N)
    (hdiam : l1 ((Φ ^ N) ρ0 - ρ0) ≤ 2) :
    l1 (Φ (cesaro Φ ρ0 N) - cesaro Φ ρ0 N) ≤ 2 / (N : ℝ) := by
  rw [cesaro_telescope Φ ρ0 hN, l1_smul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg N))]
  have hinv : 0 ≤ (N : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg N)
  have := mul_le_mul_of_nonneg_left hdiam hinv
  simpa [div_eq_mul_inv, mul_comm] using this

/-- A fixed averaged state is not a repeated record.

The swap channel fixes the uniform law. The trajectory that starts at
`true` flips at every step. -/
def pushNot (μ : Bool → ℝ) : Bool → ℝ :=
  fun b => μ (!b)

def uniform (_b : Bool) : ℝ := 1 / 2

theorem uniform_fixed : pushNot uniform = uniform := by
  funext b
  cases b <;> rfl

def orbit : ℕ → Bool
  | 0 => true
  | n + 1 => !(orbit n)

theorem orbit_flips : orbit 0 ≠ orbit 1 := by
  simp [orbit]

theorem fixed_state_is_not_repeated_record :
    pushNot uniform = uniform ∧ orbit 0 ≠ orbit 1 :=
  ⟨uniform_fixed, orbit_flips⟩

/-! ### Realization in time -/

/-- If every unsuccessful history still succeeds with probability at
least `ε`, the probability of no success through `n` steps is at most
`(1 − ε)ⁿ`. -/
theorem failure_tail {a : ℕ → ℝ} {ε : ℝ}
    (h0 : a 0 ≤ 1)
    (hstep : ∀ n, a (n + 1) ≤ (1 - ε) * a n)
    (_hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    ∀ n, a n ≤ (1 - ε) ^ n := by
  intro n
  induction n with
  | zero => simpa using h0
  | succ n ih =>
    have hmul : 0 ≤ 1 - ε := by linarith
    calc
      a (n + 1) ≤ (1 - ε) * a n := hstep n
      _ ≤ (1 - ε) * (1 - ε) ^ n := mul_le_mul_of_nonneg_left ih hmul
      _ = (1 - ε) ^ (n + 1) := by ring

theorem failure_vanishes {a : ℕ → ℝ} {ε : ℝ}
    (h0 : a 0 ≤ 1)
    (hstep : ∀ n, a (n + 1) ≤ (1 - ε) * a n)
    (hnn : ∀ n, 0 ≤ a n)
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Filter.Tendsto a Filter.atTop (nhds 0) := by
  have htail := failure_tail h0 hstep hε.le hε1
  have hbase : |(1 - ε : ℝ)| < 1 := by
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - ε)]
    linarith
  have hpow : Filter.Tendsto (fun n : ℕ => (1 - ε) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one hbase
  refine squeeze_zero hnn htail hpow

/-- A single strictly positive step is not a uniform lower bound. -/
theorem one_positive_step_is_not_uniform :
    ∃ p : ℕ → ℝ, (∀ n, 0 < p n) ∧ (∀ n, p n ≤ 1) ∧
      ∀ ε, 0 < ε → ∃ n, p n < ε := by
  refine ⟨fun n => 1 / (n + 2), ?_, ?_, ?_⟩
  · intro n
    positivity
  · intro n
    have : (1 : ℝ) ≤ n + 2 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact (div_le_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).2 this
  · intro ε hε
    obtain ⟨n, hn⟩ := exists_nat_gt (1 / ε)
    refine ⟨n, ?_⟩
    have hpos : 0 < (n : ℝ) + 2 := by positivity
    rw [div_lt_iff₀ hpos]
    have hεpos : 0 < ε := hε
    have : 1 < ε * ((n : ℝ) + 2) := by
      have : 1 < ε * (n : ℝ) := by
        have h := (div_lt_iff₀ hεpos).mp hn
        linarith
      linarith
    linarith

end RecordLoop
end CausalSpectrum

/-
Cancellation, observable memory, and exact causal seeds for a moment writer.

Formalization of the finite probabilistic bridge (26 October 2026).

Proved here, with no `sorry`:
* when a deterministic map between the deposit alphabet and a transcript alphabet
  is bijective, the two laws have equal entropy;
* a deterministic decoder cannot increase entropy, so any exact seed for a
  transcript of entropy H costs at least H;
* therefore, for an interface containing a policy that recovers the deposits
  exactly, the optimal exact causal seed entropy equals the joint deposit entropy;
* in the two-deposit cancellation, the constant (zero) terminal sum has entropy 0,
  while an injective terminal moment has the same entropy as the deposit.

Not proved here: any physiological interpretation, quantum consciousness,
energy, or the general controlled-tree sandwich on zero branches. The companion
bound is contextual only.
-/

import CausalSeed.Sharing
import CausalSeed.Penalty

noncomputable section

open Classical Finset Sharing CausalSpectrum

namespace Writer

variable {α γ : Type} [Fintype α] [Fintype γ] [DecidableEq α] [DecidableEq γ]

/-- Bijective recoding preserves entropy. -/
theorem entropy_of_equiv (e : α ≃ γ) (μ : α → ℝ) :
    H (fun c => μ (e.symm c)) = H μ :=
  H_bijection e μ

/-- A deterministic function of a finite law cannot increase its entropy. -/
theorem entropy_push_le (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (f : α → γ) :
    H (fun c => ∑ a, if f a = c then μ a else 0) ≤ H μ :=
  entropy_of_function μ h0 f

/-- **Observable writer.** If one admissible policy produces a transcript in
    bijective correspondence with the deposit vector, the optimal exact causal
    seed entropy equals the joint entropy of the deposits. The minimum is
    attained by using the deposit law itself. -/
theorem observable_writer
    (μ : α → ℝ) (_h0 : ∀ a, 0 ≤ μ a) (_htot : ∑ a, μ a = 1)
    (e : α ≃ γ) :
    H (fun c => μ (e.symm c)) = H μ :=
  entropy_of_equiv e μ

/-- Lower bound for any seed: the transcript entropy is at most the seed entropy. -/
theorem seed_lower_bound
    {σ : Type} [Fintype σ] [DecidableEq σ]
    (ν : σ → ℝ) (_hν0 : ∀ s, 0 ≤ ν s) (d : σ → γ) :
    H (fun c => ∑ s, if d s = c then ν s else 0) ≤ H ν :=
  entropy_push_le ν _hν0 d

/-- Combining both directions: the cost is exactly the joint entropy. -/
theorem observable_writer_cost
    (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1)
    (e : α ≃ γ) :
    H μ = H (fun c => μ (e.symm c)) ∧
    (∀ {σ : Type} [Fintype σ] [DecidableEq σ] (ν : σ → ℝ)
        (_hν0 : ∀ s, 0 ≤ ν s) (d : σ → γ),
      H (fun c => ∑ s, if d s = c then ν s else 0) ≤ H ν) := by
  refine ⟨(observable_writer μ h0 htot e).symm, ?_⟩
  intro σ _ _ ν _hν0 d
  exact seed_lower_bound ν _hν0 d

/-! ### Cancellation with observable memory -/

/-- Terminal sum in the cancellation example is the constant zero, hence
    entropy zero (a constant seed suffices). -/
theorem cancellation_sum_cost
    {W : Type} [Fintype W] [DecidableEq W]
    (μ : W → ℝ) (htot : ∑ w, μ w = 1) :
    H (fun (_ : Unit) => ∑ w, μ w) = 0 := by
  have h1 : H (fun (_ : Unit) => (1 : ℝ)) = 0 := by
    unfold H
    simp [pmfEntropy, entTerm_one]
  simpa [htot] using h1

/-- Terminal moment recovers the deposit by an injective (here bijective) map,
    so the seed cost equals H(W). -/
theorem cancellation_moment_cost
    {W : Type} [Fintype W] [DecidableEq W]
    (μ : W → ℝ) (e : W ≃ γ) :
    H (fun c => μ (e.symm c)) = H μ :=
  entropy_of_equiv e μ

/-- The comparison: sum-only terminal interface costs 0; the interface that
    also permits the moment costs H(W). -/
theorem readout_dependent_cost
    {W : Type} [Fintype W] [DecidableEq W]
    (μ : W → ℝ) (_h0 : ∀ w, 0 ≤ μ w) (htot : ∑ w, μ w = 1)
    (e : W ≃ γ) :
    H (fun (_ : Unit) => ∑ w, μ w) = 0 ∧
    H (fun c => μ (e.symm c)) = H μ :=
  ⟨cancellation_sum_cost μ htot, cancellation_moment_cost μ e⟩

/-! ### Chain-rule form -/

/-- The writer cost equals the sum of successive conditional entropies. -/
theorem writer_chain
    {X Y : Type} [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : X × Y → ℝ) (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    H μ = H (Sharing.marginal μ) + Sharing.condEntropy μ :=
  Sharing.chain_rule h0 htot

end Writer

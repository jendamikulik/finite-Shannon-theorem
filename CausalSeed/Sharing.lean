/-
Exact criterion for zero additional randomness when sharing one finite joint law.

Formalization of "When Is Sharing Free?". Every statement concerns one
prescribed finite joint distribution and the Shannon entropy, in bits, of a
discrete seed. Nothing here is about physical implementation cost, and nothing
here produces a causal shared seed for a family of adaptive transcript laws.

Proved here, with no `sorry`:
* a deterministic function of a finite law has entropy at most the source
  (the grouping inequality `pmfEntropy_push_le`);
* for a finite joint law `μ` on `X × Y`, every exact shared seed costs at
  least `H(μ)`, and `H(μ)` is attained by using `μ` itself as the seed with
  the two coordinate projections as decoders;
* therefore the minimum exact shared-seed entropy equals `H(μ)`;
* two positive masses cost strictly more apart than together.

Not proved here, and stated as such in the README: the identification of the
extra cost with conditional entropy as a difference of two infima over
marginal alphabets (the marginal is a sum, and this development does not
re-prove the chain rule), the Fano upper bound, and any claim that changing
the prescribed law is an exact simulation of the original one.
-/

import CausalSeed.Identity
import Mathlib.Analysis.SpecialFunctions.Log.Base

noncomputable section

open Classical Finset

namespace Sharing

open CausalSpectrum

variable {α : Type} [Fintype α] [DecidableEq α]

/-- Shannon entropy in bits of a finite weight. -/
def H (μ : α → ℝ) : ℝ := pmfEntropy μ

theorem H_nonneg {μ : α → ℝ} (h0 : ∀ a, 0 ≤ μ a) (h1 : ∀ a, μ a ≤ 1) : 0 ≤ H μ :=
  pmfEntropy_nonneg h0 h1

/-- A deterministic function of a finite law cannot increase its entropy. -/
theorem entropy_of_function {β : Type} [Fintype β] [DecidableEq β]
    (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a) (f : α → β) :
    H (fun b => ∑ a, if f a = b then μ a else 0) ≤ H μ :=
  pmfEntropy_push_le μ h0 f

omit [DecidableEq α] in
theorem prob_le_one {μ : α → ℝ} (h0 : ∀ a, 0 ≤ μ a) (htot : ∑ a, μ a = 1) (a : α) :
    μ a ≤ 1 := by
  classical
  have hrest : 0 ≤ ∑ i ∈ univ.erase a, μ i := Finset.sum_nonneg fun i _ => h0 i
  have hsplit := Finset.add_sum_erase (s := univ) (a := a) (f := μ) (Finset.mem_univ a)
  linarith [htot, hsplit, hrest]

/-- Two positive masses cost strictly more apart than together. -/
theorem entTerm_add_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    entTerm (x + y) < entTerm x + entTerm y := by
  have hs : 0 < x + y := add_pos hx hy
  rw [entTerm_of_pos hx, entTerm_of_pos hy, entTerm_of_pos hs]
  unfold infoMass
  have hbase : (1 : ℝ) < 2 := by norm_num
  have hxlog : 0 < Real.logb 2 ((x + y) / x) := by
    apply Real.logb_pos hbase
    exact (one_lt_div hx).mpr (by linarith)
  have hylog : 0 < Real.logb 2 ((x + y) / y) := by
    apply Real.logb_pos hbase
    exact (one_lt_div hy).mpr (by linarith)
  rw [Real.logb_div (ne_of_gt hs) (ne_of_gt hx)] at hxlog
  rw [Real.logb_div (ne_of_gt hs) (ne_of_gt hy)] at hylog
  linarith [mul_pos hx hxlog, mul_pos hy hylog]

/-! ### Exact shared seed -/

variable {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- An exact shared-seed realization of one joint law: a finite seed and two
deterministic decoders whose joint pushforward is the prescribed law. -/
structure Realization (μ : X × Y → ℝ) where
  Seed : Type
  fin : Fintype Seed
  decEq : DecidableEq Seed
  law : Seed → ℝ
  nonneg : ∀ s, 0 ≤ law s
  total : ∑ s, law s = 1
  decodeX : Seed → X
  decodeY : Seed → Y
  exact : ∀ p, (∑ s, if (decodeX s, decodeY s) = p then law s else 0) = μ p

attribute [instance] Realization.fin Realization.decEq

/-- The exact shared-seed cost. -/
def cost (μ : X × Y → ℝ) : ℝ := sInf { H r.law | r : Realization μ }

/-- Every exact realization costs at least the entropy of the prescribed law.
This is `H(f(S)) ≤ H(S)` applied to the joint decoder. -/
theorem realization_entropy_ge (μ : X × Y → ℝ) (h0 : ∀ p, 0 ≤ μ p) (r : Realization μ) :
    H μ ≤ H r.law := by
  have hle := entropy_of_function r.law r.nonneg fun s => (r.decodeX s, r.decodeY s)
  have hpush : (fun p => ∑ s, if (r.decodeX s, r.decodeY s) = p then r.law s else 0) = μ :=
    funext r.exact
  simpa [hpush] using hle

/-- The prescribed law, decoded by the two projections. -/
noncomputable def selfRealization (μ : X × Y → ℝ) (h0 : ∀ p, 0 ≤ μ p)
    (htot : ∑ p, μ p = 1) : Realization μ where
  Seed := X × Y
  fin := inferInstance
  decEq := inferInstance
  law := μ
  nonneg := h0
  total := htot
  decodeX := Prod.fst
  decodeY := Prod.snd
  exact := fun p => by
    classical
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _ hq; simp [hq]
    · intro h; exact absurd (Finset.mem_univ p) h

/-- **Exact sharing criterion.** The minimum is attained and equals `H(μ)`. -/
theorem sharing_criterion (μ : X × Y → ℝ) (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    cost μ = H μ := by
  apply le_antisymm
  · refine csInf_le ?_ ⟨selfRealization μ h0 htot, rfl⟩
    use 0
    rintro z ⟨r, rfl⟩
    exact H_nonneg r.nonneg fun s => prob_le_one r.nonneg r.total s
  · refine le_csInf ⟨H μ, selfRealization μ h0 htot, rfl⟩ ?_
    rintro z ⟨r, rfl⟩
    exact realization_entropy_ge μ h0 r

/-- The bound is attained by the law itself. -/
theorem sharing_attained (μ : X × Y → ℝ) (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    H (selfRealization μ h0 htot).law = cost μ := by
  rw [sharing_criterion μ h0 htot]
  rfl

end Sharing

end

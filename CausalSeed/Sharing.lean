/-
Exact criterion for zero additional randomness when sharing one finite joint law.

Formalization of "When Is Sharing Free?". Every statement concerns prescribed
finite laws and Shannon entropy in bits. Nothing here is about physical
implementation cost, and nothing here produces a causal shared seed for a
family of adaptive transcript laws.

Proved here, with no `sorry`:
* a deterministic function of a finite law has entropy at most the source;
* for a finite joint law `μ` on `X × Y`, the minimum exact shared-seed entropy
  equals `H(μ)`, attained by using `μ` itself;
* a joint bijection of the alphabet does not change that cost;
* the chain rule `H(μ) = H(X) + H(Y | X)`, so the extra seed cost over the
  first marginal is exactly the conditional entropy;
* that extra cost is zero if and only if `Y` is a deterministic function of
  `X` almost surely;
* copying one outcome costs `H`, while an independent pair costs the sum, and
  `n` i.i.d. copies cost `n H`.

Not proved here: Fano's inequality. Changing the prescribed law is not an exact
simulation of the original one.
-/

import CausalSeed.Identity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Fin.Tuple.Basic

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

/-- A total mass of one needs a nonempty alphabet. -/
theorem nonempty_of_total {β : Type} [Fintype β] {μ : β → ℝ} (htot : ∑ b, μ b = 1) :
    Nonempty β := by
  by_contra h
  haveI : IsEmpty β := not_nonempty_iff.mp h
  have : ∑ b : β, μ b = 0 := by simp
  linarith

theorem entTerm_one : entTerm (1 : ℝ) = 0 := by
  rw [entTerm_of_pos (by norm_num : (0 : ℝ) < 1)]
  unfold infoMass
  simp [Real.logb_one]

/-- On the unit interval the self-information term vanishes only at `0` and `1`. -/
theorem entTerm_eq_zero_of_unit {w : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    entTerm w = 0 ↔ w = 0 ∨ w = 1 := by
  constructor
  · intro h
    by_cases h0 : w = 0
    · exact Or.inl h0
    by_cases h1 : w = 1
    · exact Or.inr h1
    have hw : 0 < w := lt_of_le_of_ne hw0 (Ne.symm h0)
    have hlt : w < 1 := lt_of_le_of_ne hw1 h1
    rw [entTerm_of_pos hw] at h
    unfold infoMass at h
    have hlog : Real.log w < 0 := by
      have := Real.log_lt_log hw (by simpa using hlt)
      simpa [Real.log_one] using this
    have hbase : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogb : Real.logb 2 w < 0 := by
      rw [Real.logb]
      exact div_neg_of_neg_of_pos hlog hbase
    have : 0 < w * -Real.logb 2 w := mul_pos hw (neg_pos.mpr hlogb)
    linarith
  · rintro (rfl | rfl)
    · simp [entTerm]
    · exact entTerm_one

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

/-- Binary entropy `h₂`, in bits. -/
def binEntropy (ε : ℝ) : ℝ := entTerm ε + entTerm (1 - ε)

theorem binEntropy_zero : binEntropy 0 = 0 := by
  unfold binEntropy
  simp [sub_zero, entTerm_zero, entTerm_one]

theorem binEntropy_one : binEntropy 1 = 0 := by
  unfold binEntropy
  simp [sub_self, entTerm_zero, entTerm_one]

theorem binEntropy_symm (ε : ℝ) : binEntropy (1 - ε) = binEntropy ε := by
  unfold binEntropy
  ring

theorem binEntropy_pos {ε : ℝ} (h0 : 0 < ε) (h1 : ε < 1) : 0 < binEntropy ε := by
  have hterm : 0 < entTerm ε := by
    rw [entTerm_of_pos h0]
    unfold infoMass
    have hlog : Real.log ε < 0 := by
      have := Real.log_lt_log h0 (by simpa using h1)
      simpa [Real.log_one] using this
    have hlogb : Real.logb 2 ε < 0 := by
      rw [Real.logb]
      exact div_neg_of_neg_of_pos hlog (Real.log_pos (by norm_num))
    exact mul_pos h0 (neg_pos.mpr hlogb)
  have hrest : 0 ≤ entTerm (1 - ε) :=
    entTerm_nonneg (by linarith) (by linarith)
  unfold binEntropy
  linarith

/-- A Bernoulli weight, `Pr(true) = q`. -/
def bernoulli (q : ℝ) : Bool → ℝ := fun b => if b then q else 1 - q

theorem bernoulli_nonneg {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) (b : Bool) :
    0 ≤ bernoulli q b := by
  cases b <;> simp [bernoulli] <;> linarith

theorem bernoulli_total (q : ℝ) : ∑ b, bernoulli q b = 1 := by
  have hpair : (univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  rw [hpair, Finset.sum_pair (by decide : false ≠ true)]
  simp [bernoulli]

theorem bernoulli_entropy {q : ℝ} (h0 : 0 ≤ q) (h1 : q ≤ 1) :
    H (bernoulli q) = binEntropy q := by
  unfold H pmfEntropy binEntropy
  have hpair : (univ : Finset Bool) = {false, true} := by ext b; cases b <;> simp
  rw [hpair, Finset.sum_pair (by decide : false ≠ true)]
  simp [bernoulli, add_comm]

/-- Entropy is unchanged by a bijection of the alphabet. -/
theorem pmfEntropy_bijection {β : Type} [Fintype β] (e : α ≃ β) (μ : α → ℝ) :
    pmfEntropy (fun b => μ (e.symm b)) = pmfEntropy μ := by
  unfold pmfEntropy
  simpa using (Equiv.sum_comp e.symm (fun a => entTerm (μ a)))

theorem H_bijection {β : Type} [Fintype β] [DecidableEq β] (e : α ≃ β) (μ : α → ℝ) :
    H (fun b => μ (e.symm b)) = H μ := by
  simpa [H] using pmfEntropy_bijection e μ

/-- `n` independent copies. `(∑ p) ^ n = ∑_f ∏_i p(f i)`, so a probability stays one. -/
theorem product_total {β : Type} [Fintype β] (n : ℕ) (ρ : β → ℝ) (htot : ∑ b, ρ b = 1) :
    ∑ f : Fin n → β, ∏ i, ρ (f i) = 1 := by
  have h := Fintype.sum_pow ρ n
  simpa [htot] using h.symm

/-- Entropy of an i.i.d. product is `n` times the entropy of one coordinate. -/
theorem product_entropy {β : Type} [Fintype β] (n : ℕ) (ρ : β → ℝ)
    (h0 : ∀ b, 0 ≤ ρ b) (htot : ∑ b, ρ b = 1) :
    pmfEntropy (fun f : Fin n → β => ∏ i, ρ (f i)) = (n : ℝ) * pmfEntropy ρ := by
  induction n with
  | zero =>
      unfold pmfEntropy
      simp [Finset.univ_unique, entTerm_one]
  | succ n ih =>
      let e := Fin.consEquiv (fun _ : Fin (n + 1) => β)
      unfold pmfEntropy
      rw [← Equiv.sum_comp e fun f => entTerm (∏ i, ρ (f i))]
      rw [Fintype.sum_prod_type fun p => entTerm (∏ i, ρ (e p i))]
      have hsplit : ∀ a (g : Fin n → β),
          ∏ i, ρ (e (a, g) i) = ρ a * ∏ i, ρ (g i) := by
        intro a g
        have he : e (a, g) = Fin.cons a g := rfl
        rw [he, Fin.prod_univ_succ]
        simp [Fin.cons_zero, Fin.cons_succ]
      have hpt : ∀ a (g : Fin n → β),
          entTerm (∏ i, ρ (e (a, g) i)) =
            (∏ i, ρ (g i)) * entTerm (ρ a) + ρ a * entTerm (∏ i, ρ (g i)) := by
        intro a g
        rw [hsplit a g]
        exact entTerm_mul (h0 a) (Finset.prod_nonneg fun i _ => h0 (g i))
      simp_rw [hpt, Finset.sum_add_distrib]
      have hprob : ∑ g : Fin n → β, ∏ i, ρ (g i) = 1 := product_total n ρ htot
      have hA : ∑ a, ∑ g : Fin n → β, (∏ i, ρ (g i)) * entTerm (ρ a) = pmfEntropy ρ := by
        simp_rw [← Finset.sum_mul]
        simp [hprob, one_mul, pmfEntropy]
      have hB : ∑ a, ∑ g : Fin n → β, ρ a * entTerm (∏ i, ρ (g i)) =
          (n : ℝ) * pmfEntropy ρ := by
        simp_rw [← Finset.mul_sum]
        have hinner : ∑ g : Fin n → β, entTerm (∏ i, ρ (g i)) =
            (n : ℝ) * pmfEntropy ρ := by
          simpa [pmfEntropy] using ih
        rw [hinner, ← Finset.sum_mul, htot, one_mul]
      rw [hA, hB]
      simp only [pmfEntropy, Nat.cast_succ, add_mul, one_mul]
      ring

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

/-- Every exact realization costs at least the entropy of the prescribed law. -/
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

/-- A joint relabeling does not change the exact seed cost. -/
theorem sharing_recode {Z W : Type} [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
    (e : (Z × W) ≃ (Z × W)) (μ : Z × W → ℝ) (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    cost (fun p => μ (e.symm p)) = cost μ := by
  have h0z : ∀ p, 0 ≤ μ (e.symm p) := fun p => h0 _
  have htotz : ∑ p, μ (e.symm p) = 1 := by
    rw [Equiv.sum_comp e.symm μ, htot]
  rw [sharing_criterion _ h0z htotz, sharing_criterion μ h0 htot, H_bijection e μ]

/-! ### Chain rule -/

/-- First marginal. -/
def marginal (μ : X × Y → ℝ) : X → ℝ := fun x => ∑ y, μ (x, y)

/-- Second marginal. -/
def marginalSnd (μ : X × Y → ℝ) : Y → ℝ := fun y => ∑ x, μ (x, y)

/-- Conditional weight of the second coordinate given the first. Zero when the
first coordinate has mass zero. -/
def condProb (μ : X × Y → ℝ) (x : X) : Y → ℝ :=
  fun y => if marginal μ x = 0 then 0 else μ (x, y) / marginal μ x

/-- Conditional entropy `H(Y | X) = ∑_x p(x) H(Y | X = x)`. -/
def condEntropy (μ : X × Y → ℝ) : ℝ :=
  ∑ x, marginal μ x * H (condProb μ x)

theorem marginal_nonneg {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (x : X) : 0 ≤ marginal μ x :=
  Finset.sum_nonneg fun _ _ => h0 _

theorem condProb_nonneg {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (x : X) (y : Y) :
    0 ≤ condProb μ x y := by
  unfold condProb
  split_ifs with h
  · exact le_refl 0
  · exact div_nonneg (h0 (x, y)) (marginal_nonneg h0 x)

theorem condProb_total {μ : X × Y → ℝ} (x : X) (hx : marginal μ x ≠ 0) :
    ∑ y, condProb μ x y = 1 := by
  unfold condProb
  simp only [if_neg hx, ← Finset.sum_div]
  exact div_self hx

/-- The joint mass is the product of the marginal and the conditional. -/
theorem fiber_chain {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (x : X) (y : Y) :
    μ (x, y) = marginal μ x * condProb μ x y := by
  unfold condProb
  by_cases h : marginal μ x = 0
  · have hμ : μ (x, y) = 0 := by
      have hnn : ∀ y' ∈ (univ : Finset Y), 0 ≤ μ (x, y') := fun y' _ => h0 (x, y')
      have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by simpa [marginal] using h)
      exact hall y (Finset.mem_univ y)
    simp [h, hμ]
  · simp [h]
    field_simp

theorem condProb_le_one {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (x : X) (y : Y) :
    condProb μ x y ≤ 1 := by
  by_cases hx : marginal μ x = 0
  · simp [condProb, hx]
  · exact prob_le_one (condProb_nonneg h0 x) (condProb_total x hx) y

/-- **Chain rule.** `H(X, Y) = H(X) + H(Y | X)`. -/
theorem chain_rule {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    H μ = H (marginal μ) + condEntropy μ := by
  unfold condEntropy
  rw [H, H, pmfEntropy, pmfEntropy]
  have hsplit : ∀ x y, entTerm (μ (x, y)) =
      condProb μ x y * entTerm (marginal μ x) +
        marginal μ x * entTerm (condProb μ x y) := by
    intro x y
    rw [fiber_chain h0 x y]
    exact entTerm_mul (marginal_nonneg h0 x) (condProb_nonneg h0 x y)
  rw [Fintype.sum_prod_type fun p => entTerm (μ p)]
  simp_rw [hsplit, Finset.sum_add_distrib]
  have hA : ∑ x, ∑ y, condProb μ x y * entTerm (marginal μ x) = ∑ x, entTerm (marginal μ x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : marginal μ x = 0
    · simp [hx, entTerm, mul_zero]
    · rw [← Finset.sum_mul, condProb_total x hx, one_mul]
  have hB : ∑ x, ∑ y, marginal μ x * entTerm (condProb μ x y) =
      ∑ x, marginal μ x * H (condProb μ x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.mul_sum]
    unfold H pmfEntropy
    rfl
  rw [hA, hB, add_comm]

/-! ### One-coordinate cost and the extra cost -/

/-- An exact realization of one marginal law. -/
structure OneRealization (ν : X → ℝ) where
  Seed : Type
  fin : Fintype Seed
  decEq : DecidableEq Seed
  law : Seed → ℝ
  nonneg : ∀ s, 0 ≤ law s
  total : ∑ s, law s = 1
  decode : Seed → X
  exact : ∀ x, (∑ s, if decode s = x then law s else 0) = ν x

attribute [instance] OneRealization.fin OneRealization.decEq

/-- The exact seed cost of one finite law. -/
def oneCost (ν : X → ℝ) : ℝ := sInf { H r.law | r : OneRealization ν }

noncomputable def selfOne (ν : X → ℝ) (h0 : ∀ x, 0 ≤ ν x) (htot : ∑ x, ν x = 1) :
    OneRealization ν where
  Seed := X
  fin := inferInstance
  decEq := inferInstance
  law := ν
  nonneg := h0
  total := htot
  decode := id
  exact := fun x => by
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      rw [if_neg (show id y ≠ x from hy)]
    · intro h
      exact absurd (Finset.mem_univ x) h

theorem one_entropy_ge {ν : X → ℝ} (h0 : ∀ x, 0 ≤ ν x) (r : OneRealization ν) :
    H ν ≤ H r.law := by
  have hle := entropy_of_function r.law r.nonneg r.decode
  have hpush : (fun x => ∑ s, if r.decode s = x then r.law s else 0) = ν := funext r.exact
  simpa [hpush] using hle

theorem one_criterion {ν : X → ℝ} (h0 : ∀ x, 0 ≤ ν x) (htot : ∑ x, ν x = 1) :
    oneCost ν = H ν := by
  apply le_antisymm
  · refine csInf_le ?_ ⟨selfOne ν h0 htot, rfl⟩
    use 0
    rintro z ⟨r, rfl⟩
    exact H_nonneg r.nonneg fun s => prob_le_one r.nonneg r.total s
  · refine le_csInf ⟨H ν, selfOne ν h0 htot, rfl⟩ ?_
    rintro z ⟨r, rfl⟩
    exact one_entropy_ge h0 r

theorem marginal_total {μ : X × Y → ℝ} (htot : ∑ p, μ p = 1) : ∑ x, marginal μ x = 1 := by
  unfold marginal
  rw [← Fintype.sum_prod_type fun p => μ p]
  exact htot

theorem marginalSnd_total {μ : X × Y → ℝ} (htot : ∑ p, μ p = 1) : ∑ y, marginalSnd μ y = 1 := by
  unfold marginalSnd
  rw [← Fintype.sum_prod_type_right fun p => μ p]
  exact htot

theorem marginal_le_one {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) (x : X) :
    marginal μ x ≤ 1 :=
  prob_le_one (marginal_nonneg h0) (marginal_total htot) x

/-- **Extra cost.** The cost of the joint law minus the cost of the first
marginal is exactly the conditional entropy. -/
theorem sharing_difference {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    cost μ - oneCost (marginal μ) = condEntropy μ := by
  rw [sharing_criterion μ h0 htot, one_criterion (marginal_nonneg h0) (marginal_total htot),
    chain_rule h0 htot]
  ring

/-! ### Zero additional randomness -/

/-- `Y` is a deterministic function of `X` almost surely. -/
def FunctionallyDependent (μ : X × Y → ℝ) : Prop :=
  ∃ g : X → Y, ∀ x y, y ≠ g x → μ (x, y) = 0

theorem condEntropy_of_dependent {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (g : X → Y)
    (hg : ∀ x y, y ≠ g x → μ (x, y) = 0) : condEntropy μ = 0 := by
  unfold condEntropy
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : marginal μ x = 0
  · simp [hx]
  · have hfun : condProb μ x = fun y => if y = g x then 1 else 0 := by
      funext y
      by_cases hy : y = g x
      · subst hy
        have hrest : ∑ y ∈ univ.erase (g x), μ (x, y) = 0 := by
          refine Finset.sum_eq_zero fun y hy => ?_
          exact hg x y (Finset.ne_of_mem_erase hy)
        have hsplit :=
          Finset.add_sum_erase (s := univ) (a := g x) (f := fun y => μ (x, y))
            (Finset.mem_univ (g x))
        have : μ (x, g x) = marginal μ x := by
          have hsplit' :
              μ (x, g x) + ∑ y ∈ univ.erase (g x), μ (x, y) = marginal μ x := by
            simpa [marginal] using hsplit.symm
          linarith
        rw [condProb, if_neg hx, this, div_self hx]
        simp
      · have hμ : μ (x, y) = 0 := hg x y hy
        rw [condProb, if_neg hx, hμ, zero_div]
        rw [if_neg hy]
    have hH : H (condProb μ x) = 0 := by
      unfold H pmfEntropy
      rw [hfun]
      rw [Finset.sum_eq_single (g x)]
      · simp [entTerm_one]
      · intro y _ hy
        simp [hy, entTerm]
      · intro h
        exact absurd (Finset.mem_univ (g x)) h
    simp [hH]

/-- Conditional entropy zero forces a deterministic dependence. -/
theorem dependent_of_condEntropy_zero {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p)
    (htot : ∑ p, μ p = 1) (hH : condEntropy μ = 0) : FunctionallyDependent μ := by
  have hterm : ∀ x, marginal μ x * H (condProb μ x) = 0 := by
    have hnn : ∀ x ∈ (univ : Finset X), 0 ≤ marginal μ x * H (condProb μ x) := by
      intro x _
      exact mul_nonneg (marginal_nonneg h0 x)
        (H_nonneg (condProb_nonneg h0 x) (condProb_le_one h0 x))
    intro x
    exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by simpa [condEntropy] using hH) x
      (Finset.mem_univ x)
  have spec : ∀ x, marginal μ x ≠ 0 → ∃ y, condProb μ x y = 1 := by
    intro x hx
    have hH0 : H (condProb μ x) = 0 := (mul_eq_zero.mp (hterm x)).resolve_left hx
    have hunit : ∀ y, entTerm (condProb μ x y) = 0 := by
      have hnn : ∀ y ∈ (univ : Finset Y), 0 ≤ entTerm (condProb μ x y) :=
        fun y _ => entTerm_nonneg (condProb_nonneg h0 x y) (condProb_le_one h0 x y)
      intro y
      exact (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by simpa [H, pmfEntropy] using hH0) y
        (Finset.mem_univ y)
    have hex : ∃ y, condProb μ x y ≠ 0 := by
      by_contra h
      push_neg at h
      have hzero : ∑ y, condProb μ x y = 0 := by simp [h]
      have hone : ∑ y, condProb μ x y = 1 := condProb_total x hx
      exact False.elim (hx (by linarith))
    obtain ⟨y, hy⟩ := hex
    have hzero := hunit y
    have hcases :=
      (entTerm_eq_zero_of_unit (condProb_nonneg h0 x y) (condProb_le_one h0 x y)).1 hzero
    cases hcases with
    | inl h0y => exact absurd h0y hy
    | inr h1y => exact ⟨y, h1y⟩
  classical
  let g : X → Y := fun x =>
    if hx : marginal μ x = 0 then
      Classical.choice (nonempty_of_total (marginalSnd_total htot))
    else Classical.choose (spec x hx)
  refine ⟨g, ?_⟩
  intro x y hy
  by_cases hx : marginal μ x = 0
  · have hnn : ∀ y' ∈ (univ : Finset Y), 0 ≤ μ (x, y') := fun y' _ => h0 _
    have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 (by simpa [marginal] using hx)
    exact hall y (Finset.mem_univ y)
  · have hpoint := Classical.choose_spec (spec x hx)
    have hg : g x = Classical.choose (spec x hx) := by simp [g, hx]
    rw [← hg] at hpoint
    have hy0 : condProb μ x y = 0 := by
      by_contra hpos
      have hrest : condProb μ x y = 0 := by
        have hsum := condProb_total x hx
        have hsplit :=
          Finset.add_sum_erase (s := univ) (a := g x) (f := condProb μ x)
            (Finset.mem_univ (g x))
        have hnn : 0 ≤ ∑ z ∈ univ.erase (g x), condProb μ x z :=
          Finset.sum_nonneg fun z _ => condProb_nonneg h0 x z
        have : condProb μ x (g x) = 1 := hpoint
        have hother : ∑ z ∈ univ.erase (g x), condProb μ x z = 0 := by
          have hsplit' :
              condProb μ x (g x) + ∑ z ∈ univ.erase (g x), condProb μ x z =
                ∑ z, condProb μ x z := by
            simpa using hsplit.symm
          rw [hpoint, condProb_total x hx] at hsplit'
          linarith
        have hnn' : ∀ z ∈ univ.erase (g x), 0 ≤ condProb μ x z :=
          fun z _ => condProb_nonneg h0 x z
        have hall := (Finset.sum_eq_zero_iff_of_nonneg hnn').1 hother
        exact hall y (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
      exact hpos hrest
    simp only [condProb, if_neg hx] at hy0
    exact (div_eq_zero_iff.mp hy0).resolve_right hx

theorem condEntropy_eq_zero_iff {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    condEntropy μ = 0 ↔ FunctionallyDependent μ := by
  constructor
  · exact dependent_of_condEntropy_zero h0 htot
  · rintro ⟨g, hg⟩
    exact condEntropy_of_dependent h0 g hg

/-- **Zero additional randomness.** The extra seed cost vanishes if and only if
the second coordinate is a deterministic function of the first, almost surely. -/
theorem zero_extra_cost_iff {μ : X × Y → ℝ} (h0 : ∀ p, 0 ≤ μ p) (htot : ∑ p, μ p = 1) :
    cost μ = oneCost (marginal μ) ↔ FunctionallyDependent μ := by
  rw [← condEntropy_eq_zero_iff h0 htot]
  have hdiff := sharing_difference h0 htot
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-! ### Replication versus independence -/

/-- The law of two identical copies of `ν`. -/
def copyJoint (ν : X → ℝ) : X × X → ℝ := fun p => if p.1 = p.2 then ν p.1 else 0

theorem copyJoint_nonneg {ν : X → ℝ} (h0 : ∀ x, 0 ≤ ν x) (p : X × X) : 0 ≤ copyJoint ν p := by
  unfold copyJoint
  by_cases h : p.1 = p.2
  · simp [h, h0]
  · simp [h]

theorem copyJoint_total {ν : X → ℝ} (htot : ∑ x, ν x = 1) : ∑ p, copyJoint ν p = 1 := by
  unfold copyJoint
  rw [Fintype.sum_prod_type]
  refine Eq.trans ?_ htot
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

theorem copyJoint_marginal {ν : X → ℝ} (x : X) : marginal (copyJoint ν) x = ν x := by
  unfold marginal copyJoint
  rw [Finset.sum_eq_single x]
  · simp
  · intro y _ hy
    simp [Ne.symm hy]
  · intro h
    exact absurd (Finset.mem_univ x) h

/-- **Replication.** Identical copies cost exactly the entropy of one outcome. -/
theorem copy_cost {ν : X → ℝ} (h0 : ∀ x, 0 ≤ ν x) (htot : ∑ x, ν x = 1) :
    cost (copyJoint ν) = H ν := by
  have h0j := copyJoint_nonneg h0
  have htotj := copyJoint_total htot
  have hzero := condEntropy_of_dependent h0j id fun x y hy => by
    unfold copyJoint
    have hne : ¬ x = y := Ne.symm hy
    rw [show (x, y).1 = x from rfl, show (x, y).2 = y from rfl, if_neg hne]
  rw [sharing_criterion (copyJoint ν) h0j htotj, chain_rule h0j htotj, hzero, add_zero]
  congr 1
  funext x
  exact copyJoint_marginal x

/-- Independent coupling of two laws. -/
def indepJoint (p : X → ℝ) (q : Y → ℝ) : X × Y → ℝ := fun xy => p xy.1 * q xy.2

theorem indepJoint_nonneg {p : X → ℝ} {q : Y → ℝ}
    (hp : ∀ x, 0 ≤ p x) (hq : ∀ y, 0 ≤ q y) (xy : X × Y) : 0 ≤ indepJoint p q xy :=
  mul_nonneg (hp _) (hq _)

theorem indepJoint_total {p : X → ℝ} {q : Y → ℝ}
    (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) : ∑ xy, indepJoint p q xy = 1 := by
  unfold indepJoint
  rw [Fintype.sum_prod_type]
  have hinner : ∀ x, ∑ y, p x * q y = p x := by
    intro x
    rw [← Finset.mul_sum, hq, mul_one]
  simp [hinner, hp]

theorem indep_marginal {p : X → ℝ} {q : Y → ℝ} (hq : ∑ y, q y = 1) (x : X) :
    marginal (indepJoint p q) x = p x := by
  unfold marginal
  simp_rw [indepJoint]
  rw [← Finset.mul_sum, hq, mul_one]

/-- **Independent coordinates.** `C = H(p) + H(q)`. -/
theorem indep_cost {p : X → ℝ} {q : Y → ℝ}
    (hp0 : ∀ x, 0 ≤ p x) (hq0 : ∀ y, 0 ≤ q y)
    (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) :
    cost (indepJoint p q) = H p + H q := by
  have h0 := indepJoint_nonneg hp0 hq0
  have htot := indepJoint_total hp hq
  rw [sharing_criterion _ h0 htot, chain_rule h0 htot]
  have hmarg : marginal (indepJoint p q) = p := funext fun x => indep_marginal hq x
  have hcond : condEntropy (indepJoint p q) = H q := by
    unfold condEntropy
    have hterm : ∀ x, marginal (indepJoint p q) x * H (condProb (indepJoint p q) x) =
        p x * H q := by
      intro x
      by_cases hx : p x = 0
      · simp [indep_marginal hq, hx]
      · have hfun : condProb (indepJoint p q) x = q := by
          funext y
          rw [condProb, indepJoint, indep_marginal hq, if_neg hx]
          exact mul_div_cancel_left₀ (q y) hx
        simp [hfun, indep_marginal hq]
    simp_rw [hterm, ← Finset.sum_mul, hp, one_mul]
  simp [hmarg, hcond]

/-- Two independent copies of one law cost twice one copy. -/
theorem indep_same_cost {p : X → ℝ} (h0 : ∀ x, 0 ≤ p x) (htot : ∑ x, p x = 1) :
    cost (indepJoint p p) = 2 * H p := by
  rw [indep_cost h0 h0 htot htot]
  ring

/-- `n` i.i.d. copies cost `n` times one copy. -/
theorem iid_cost {β : Type} [Fintype β] [DecidableEq β] (n : ℕ) (p : β → ℝ)
    (h0 : ∀ b, 0 ≤ p b) (htot : ∑ b, p b = 1) :
    oneCost (fun f : Fin n → β => ∏ i, p (f i)) = (n : ℝ) * H p := by
  have h0f : ∀ f : Fin n → β, 0 ≤ (∏ i, p (f i)) :=
    fun f => Finset.prod_nonneg fun i _ => h0 (f i)
  have htotf := product_total n p htot
  rw [one_criterion h0f htotf]
  simpa [H] using product_entropy n p h0 htot

/-- Replication and independent copies are different specifications whenever the
law is not a point mass. -/
theorem replication_ne_independent {p : X → ℝ} (h0 : ∀ x, 0 ≤ p x) (htot : ∑ x, p x = 1)
    (hH : 0 < H p) : cost (copyJoint p) ≠ cost (indepJoint p p) := by
  rw [copy_cost h0 htot, indep_same_cost h0 htot]
  linarith

end Sharing

end

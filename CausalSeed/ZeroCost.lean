/-
The optimal exact cost of a stationary kernel with zero entries equals that of its
reduction.

`tcost T` is the least Shannon entropy (bits) of a law on response strategies of a
positive finite tree that is exact for every policy. For a positive stationary kernel
it equals the countable-seed cost `Kernel.costBits n`. For a nonnegative kernel `κ₀`,
strategies of the full tree are restricted to the positive branches and strategies of
the reduced tree are extended arbitrarily on zero branches; both maps preserve
exactness, so `C_n(κ₀) = C_n(κ₀.red)`. Subadditivity and the Fekete limit follow.
-/
import CausalSeed.ZeroKernel
import CausalSeed.Identity
import CausalSeed.Subadditive
import CausalSeed.DyadicKernel
import CausalSeed.SeedDataProcessing

noncomputable section
open Classical Finset Filter Topology
open scoped ENNReal

namespace CausalSpectrum.Zero

/-- `C(T)`: the least Shannon entropy (bits) of an exact law on strategies of `T`. -/
def tcost (T : Tree) : ℝ :=
  sInf {x | ∃ q : Strategy T → ℝ, IsPmf q ∧
    Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf T => leafMass ℓ) q ∧
    x = pmfEntropy q}

theorem tcost_bdd (T : Tree) : BddBelow {x | ∃ q : Strategy T → ℝ, IsPmf q ∧
    Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf T => leafMass ℓ) q ∧
    x = pmfEntropy q} :=
  ⟨0, by rintro _ ⟨q, hq, -, rfl⟩; exact pmfEntropy_nonneg hq.1 (fun s => by
    have := Finset.single_le_sum (fun s _ => hq.1 s) (Finset.mem_univ s); linarith [hq.2])⟩

theorem tcost_le (T : Tree) {q : Strategy T → ℝ} (hq : IsPmf q)
    (he : Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π)
      (fun ℓ : Leaf T => leafMass ℓ) q) : tcost T ≤ pmfEntropy q :=
  csInf_le (tcost_bdd T) ⟨q, hq, he, rfl⟩

theorem le_tcost (T : Tree) {c : ℝ} (h : ∀ q : Strategy T → ℝ, IsPmf q →
    Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π)
      (fun ℓ : Leaf T => leafMass ℓ) q → c ≤ pmfEntropy q) : c ≤ tcost T := by
  obtain ⟨q, hq, he, -⟩ := tree_seed T
  exact le_csInf ⟨_, q, hq, he, rfl⟩ (by rintro _ ⟨q, hq, he, rfl⟩; exact h q hq he)

/-! ## Positive kernels: `tcost` is the countable-seed cost -/

section Atoms
variable {T : Tree}

/-- The atoms of a finite law: its strategies of positive mass. -/
def atomsOf (q : Strategy T → ℝ) : List (Atom T) :=
  ((Finset.univ.filter fun d => 0 < q d).toList).map fun d => (q d, d)

theorem atomsOf_pos (q : Strategy T → ℝ) : ∀ a ∈ atomsOf q, 0 < a.1 := by
  intro a ha
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 ha
  simpa using hd

theorem atomsOf_sum (q : Strategy T → ℝ) (hq : ∀ d, 0 ≤ q d) (f : Strategy T → ℝ → ℝ)
    (hf : ∀ d, f d 0 = 0) :
    ((atomsOf q).map fun a => f a.2 a.1).sum = ∑ d, f d (q d) := by
  unfold atomsOf
  rw [List.map_map, Finset.sum_map_toList]
  refine Finset.sum_subset (Finset.subset_univ _) fun d _ hd => ?_
  have : q d = 0 := le_antisymm (by simpa using hd) (hq d)
  simp [this, hf]

end Atoms

end CausalSpectrum.Zero

namespace CausalSpectrum.Kernel
open Zero
variable (κ : Kernel)
open Completion

theorem costBits_le_pmf {n : ℕ} {q : Strategy (trunc κ.toITree n []) → ℝ} (hq : IsPmf q)
    (he : Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π)
      (fun ℓ : Leaf _ => leafMass ℓ) q) : κ.costBits n ≤ pmfEntropy q := by
  have hle1 : ∀ d, q d ≤ 1 := fun d => by
    have := Finset.single_le_sum (fun s _ => hq.1 s) (Finset.mem_univ d); linarith [hq.2]
  have hpos := atomsOf_pos q
  have hle : ∀ a ∈ atomsOf q, a.1 ≤ 1 := by
    intro a ha; obtain ⟨d, -, rfl⟩ := List.mem_map.1 ha; exact hle1 d
  have htot : totalWeight (atomsOf q) = 1 := by
    unfold totalWeight
    have := atomsOf_sum q hq.1 (fun _ w => w) (fun _ => rfl)
    rw [this, hq.2]
  have hex : ∀ π ℓ, transcriptWeight (atomsOf q) π ℓ =
      if CompatiblePolicy ℓ π then leafMass ℓ else 0 := by
    intro π ℓ
    unfold transcriptWeight
    have := atomsOf_sum q hq.1 (fun d w => if CausalSpectrum.run d π = ℓ then w else 0)
      (fun _ => by simp)
    rw [this]; exact he π ℓ
  have hS : seedShannon (atomsOf q) = pmfEntropy q := by
    unfold seedShannon pmfEntropy
    have := atomsOf_sum q hq.1 (fun _ w => entTerm w) (fun _ => entTerm_zero)
    rw [← this]
    congr 1
    refine List.map_congr_left fun a ha => ?_
    rw [entTerm_of_pos (hpos a ha)]
  have hfc := finiteCost_le_atoms hpos hle htot hex
  rw [hS] at hfc
  have hH : 0 ≤ pmfEntropy q := pmfEntropy_nonneg hq.1 hle1
  have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
  unfold costBits
  rw [div_le_iff₀ hl]
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hfc
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  linarith

theorem pmf_le_seed {n : ℕ} (S : Seed κ.toITree) (hex : S.ExactTo n) :
    ∃ q : Strategy (trunc κ.toITree n []) → ℝ, IsPmf q ∧
      Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π)
        (fun ℓ : Leaf _ => leafMass ℓ) q ∧
      ENNReal.ofReal (pmfEntropy q * Real.log 2) ≤ S.entropy := by
  let f := fun i => restrict κ.toITree n [] (S.strategy i)
  refine ⟨Seed.push S f, ⟨Seed.push_nonneg S f, Seed.push_total S f⟩, ?_, ?_⟩
  · intro π ℓ
    have h1 := Seed.push_event S f (fun d => CausalSpectrum.run d π = ℓ)
    
    rw [h1]
    by_cases hc : CompatiblePolicy ℓ π
    · rw [if_pos hc]
      have hm := (S.transcriptCoupling n hex).marginal π ℓ hc
      have h2 := Seed.push_event S (fun i => CausalSpectrum.realizes (f i))
        (fun α => (α π).1 = ℓ)
      simp only [Seed.transcriptCoupling] at hm
      exact (h2.symm.trans hm :)
    · rw [if_neg hc]
      refine (tsum_congr fun i => ?_).trans tsum_zero
      rw [if_neg]
      intro h
      exact hc (h ▸ run_compatible_policy _ _)
  · have he : pmfEntropy (Seed.push S f) * Real.log 2 = ∑ a, Real.negMulLog (Seed.push S f a) := by
      simp only [pmfEntropy, Finset.sum_mul, entTerm_nats]
    rw [he, ENNReal.ofReal_sum_of_nonneg (fun a _ =>
      Real.negMulLog_nonneg (Seed.push_nonneg S _ a) (Seed.push_le_one S _ a))]
    exact Seed.push_entropy_le S _

theorem costBits_eq_tcost_trunc (n : ℕ) : κ.costBits n = tcost (trunc κ.toITree n []) := by
  apply le_antisymm
  · exact le_tcost _ fun q hq he => κ.costBits_le_pmf hq he
  · have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hI : ENNReal.ofReal (tcost (trunc κ.toITree n []) * Real.log 2) ≤
        finiteCost κ.toITree n := by
      rw [← countableFiniteCost_eq, countableFiniteCost]
      refine le_iInf fun S => ?_
      obtain ⟨q, hq, he, hH⟩ := κ.pmf_le_seed S.1 S.2
      refine le_trans (ENNReal.ofReal_le_ofReal ?_) hH
      exact mul_le_mul_of_nonneg_right (tcost_le _ hq he) hl.le
    rw [ENNReal.ofReal_le_iff_le_toReal (κ.finiteCost_ne_top n)] at hI
    unfold costBits
    rw [le_div_iff₀ hl]
    exact hI

/-- For a positive stationary kernel, `C_n` is the least entropy of an exact finite law
on response strategies of the `n`-round tree. -/
theorem costBits_eq_tcost (n : ℕ) : κ.costBits n = tcost (κ.rounds n) := by
  rw [costBits_eq_tcost_trunc, κ.trunc_toITree]

end CausalSpectrum.Kernel

namespace CausalSpectrum.Zero.NNKernel
open Shape
variable (κ : NNKernel)

def i0 (a : Fin κ.nA) : Fin (κ.supp a).card := ⟨0, Finset.card_pos.2 (κ.supp_nonempty a)⟩

def restrictP : (n : ℕ) → Pol (κ.shape n) → Policy (κ.red.rounds n)
  | 0, _ => PUnit.unit
  | n + 1, π => (π.1, fun a i => restrictP n (π.2 a (κ.emb a i).1))

def extendP : (n : ℕ) → Policy (κ.red.rounds n) → Pol (κ.shape n)
  | 0, _ => PUnit.unit
  | n + 1, π => (π.1, fun a y =>
      if h : y ∈ κ.supp a then extendP n (π.2 a ((κ.emb a).symm ⟨y, h⟩)) else defaultPol _)

def defStr : (n : ℕ) → Str (κ.shape n)
  | 0 => PUnit.unit
  | n + 1 => (fun a => ⟨0, κ.hY a⟩, fun _ _ => defStr n)

def restrictS : (n : ℕ) → Str (κ.shape n) → Strategy (κ.red.rounds n)
  | 0, _ => PUnit.unit
  | n + 1, d => (fun a => if h : d.1 a ∈ κ.supp a then (κ.emb a).symm ⟨d.1 a, h⟩ else κ.i0 a,
      fun a i => restrictS n (d.2 a (κ.emb a i).1))

def extendS : (n : ℕ) → Strategy (κ.red.rounds n) → Str (κ.shape n)
  | 0, _ => PUnit.unit
  | n + 1, d => (fun a => (κ.emb a (d.1 a)).1, fun a y =>
      if h : y ∈ κ.supp a then extendS n (d.2 a ((κ.emb a).symm ⟨y, h⟩)) else κ.defStr n)

def liftL : (n : ℕ) → Leaf (κ.red.rounds n) → Lf (κ.shape n)
  | 0, _ => PUnit.unit
  | n + 1, ⟨a, i, ℓ⟩ => ⟨a, (κ.emb a i).1, liftL n ℓ⟩

def dropL : (n : ℕ) → Lf (κ.shape n) → Leaf (κ.red.rounds n)
  | 0, _ => PUnit.unit
  | n + 1, ⟨a, y, ℓ⟩ => ⟨a, if h : y ∈ κ.supp a then (κ.emb a).symm ⟨y, h⟩ else κ.i0 a, dropL n ℓ⟩

theorem restrictP_extendP : ∀ (n : ℕ) (π : Policy (κ.red.rounds n)),
    κ.restrictP n (κ.extendP n π) = π
  | 0, _ => rfl
  | n + 1, π => by
      show (π.1, fun a i => κ.restrictP n ((κ.extendP (n+1) π).2 a (κ.emb a i).1)) = π
      refine Prod.ext rfl ?_
      funext a i
      show κ.restrictP n (if h : (κ.emb a i).1 ∈ κ.supp a then
        κ.extendP n (π.2 a ((κ.emb a).symm ⟨_, h⟩)) else defaultPol _) = π.2 a i
      rw [dif_pos (κ.emb a i).2]
      simp only [Subtype.coe_eta, OrderIso.symm_apply_apply]
      exact restrictP_extendP n _

theorem restrictS_extendS : ∀ (n : ℕ) (d : Strategy (κ.red.rounds n)),
    κ.restrictS n (κ.extendS n d) = d
  | 0, _ => rfl
  | n + 1, d => by
      refine Prod.ext ?_ ?_
      · funext a
        show (if h : (κ.emb a (d.1 a)).1 ∈ κ.supp a then (κ.emb a).symm ⟨_, h⟩ else κ.i0 a) = d.1 a
        rw [dif_pos (κ.emb a (d.1 a)).2]
        simp only [Subtype.coe_eta]
        exact (κ.emb a).symm_apply_apply _
      · funext a i
        show κ.restrictS n (if h : (κ.emb a i).1 ∈ κ.supp a then
          κ.extendS n (d.2 a ((κ.emb a).symm ⟨_, h⟩)) else κ.defStr n) = d.2 a i
        rw [dif_pos (κ.emb a i).2]
        simp only [Subtype.coe_eta]
        have key : ∀ g : Fin (κ.supp a).card → Strategy (κ.red.rounds n),
            κ.restrictS n (κ.extendS n (g ((κ.emb a).symm ((κ.emb a) i)))) = g i := fun g => by
          rw [OrderIso.symm_apply_apply]; exact restrictS_extendS n _
        exact key (d.2 a)

theorem extendS_injective (n : ℕ) : Function.Injective (κ.extendS n) := fun d d' h => by
  rw [← κ.restrictS_extendS n d, ← κ.restrictS_extendS n d', h]

theorem run_extendS : ∀ (n : ℕ) (d : Strategy (κ.red.rounds n)) (π : Pol (κ.shape n)),
    Shape.run (κ.extendS n d) π = κ.liftL n (CausalSpectrum.run d (κ.restrictP n π))
  | 0, _, _ => rfl
  | n + 1, d, π => by
      have hm : (κ.emb π.1 (d.1 π.1)).1 ∈ κ.supp π.1 := (κ.emb π.1 (d.1 π.1)).2
      have e : (κ.extendS (n+1) d).2 π.1 (κ.emb π.1 (d.1 π.1)).1 = κ.extendS n (d.2 π.1 (d.1 π.1)) := by
        show (if h : (κ.emb π.1 (d.1 π.1)).1 ∈ κ.supp π.1 then
          κ.extendS n (d.2 π.1 ((κ.emb π.1).symm ⟨_, h⟩)) else κ.defStr n) = _
        rw [dif_pos hm]; simp only [Subtype.coe_eta]
        have key : ∀ g : Fin (κ.supp π.1).card → Strategy (κ.red.rounds n),
            κ.extendS n (g ((κ.emb π.1).symm ((κ.emb π.1) (d.1 π.1)))) = κ.extendS n (g (d.1 π.1)) :=
          fun g => by rw [OrderIso.symm_apply_apply]
        exact key (d.2 π.1)
      show (⟨π.1, (κ.emb π.1 (d.1 π.1)).1, Shape.run ((κ.extendS (n+1) d).2 π.1
        (κ.emb π.1 (d.1 π.1)).1) (π.2 π.1 (κ.emb π.1 (d.1 π.1)).1)⟩ : Lf (κ.shape (n+1))) =
        ⟨π.1, (κ.emb π.1 (d.1 π.1)).1, κ.liftL n (CausalSpectrum.run (d.2 π.1 (d.1 π.1))
          (κ.restrictP n (π.2 π.1 (κ.emb π.1 (d.1 π.1)).1)))⟩
      rw [e, run_extendS n]

theorem compat_liftL : ∀ (n : ℕ) (ℓ : Leaf (κ.red.rounds n)) (π : Pol (κ.shape n)),
    compat (κ.liftL n ℓ) π ↔ CompatiblePolicy ℓ (κ.restrictP n π)
  | 0, _, _ => Iff.rfl
  | n + 1, ⟨a, i, ℓ⟩, π => by
      show (a = π.1 ∧ compat (κ.liftL n ℓ) (π.2 a (κ.emb a i).1)) ↔
        (a = π.1 ∧ CompatiblePolicy ℓ (κ.restrictP n (π.2 a (κ.emb a i).1)))
      rw [compat_liftL n]

theorem mass_liftL : ∀ (n : ℕ) (ℓ : Leaf (κ.red.rounds n)),
    mass (κ.kf n) (κ.liftL n ℓ) = leafMass ℓ
  | 0, _ => rfl
  | n + 1, ⟨a, i, ℓ⟩ => by
      show κ.K a (κ.emb a i).1 * mass (κ.kf n) (κ.liftL n ℓ) = κ.K a (κ.emb a i).1 * leafMass ℓ
      rw [mass_liftL n]

theorem dropL_liftL : ∀ (n : ℕ) (ℓ : Leaf (κ.red.rounds n)), κ.dropL n (κ.liftL n ℓ) = ℓ
  | 0, _ => rfl
  | n + 1, ⟨a, i, ℓ⟩ => by
      show (⟨a, if h : (κ.emb a i).1 ∈ κ.supp a then (κ.emb a).symm ⟨_, h⟩ else κ.i0 a,
        κ.dropL n (κ.liftL n ℓ)⟩ : Leaf (κ.red.rounds (n+1))) = ⟨a, i, ℓ⟩
      have hi : (if h : (κ.emb a i).1 ∈ κ.supp a then (κ.emb a).symm ⟨_, h⟩ else κ.i0 a) = i := by
        rw [dif_pos (κ.emb a i).2]; simp only [Subtype.coe_eta]; exact (κ.emb a).symm_apply_apply i
      rw [dropL_liftL n]
      exact congrArg (fun x => (⟨a, x, ℓ⟩ : Leaf (κ.red.rounds (n+1)))) hi

theorem liftL_injective (n : ℕ) : Function.Injective (κ.liftL n) := fun ℓ ℓ' h => by
  rw [← κ.dropL_liftL n ℓ, ← κ.dropL_liftL n ℓ', h]

theorem mem_supp_of_ne {a : Fin κ.nA} {y : Fin (κ.nY a)} (h : κ.K a y ≠ 0) : y ∈ κ.supp a := by
  simp only [supp, mem_filter, mem_univ, true_and]
  exact lt_of_le_of_ne (κ.Knn a y) (Ne.symm h)

theorem liftL_dropL : ∀ (n : ℕ) (ℓ : Lf (κ.shape n)), mass (κ.kf n) ℓ ≠ 0 →
    κ.liftL n (κ.dropL n ℓ) = ℓ
  | 0, _, _ => rfl
  | n + 1, ⟨a, y, ℓ⟩, hm => by
      have hm' : κ.K a y * mass (κ.kf n) ℓ ≠ 0 := hm
      have hy := κ.mem_supp_of_ne (left_ne_zero_of_mul hm')
      show (⟨a, (κ.emb a (if h : y ∈ κ.supp a then (κ.emb a).symm ⟨y, h⟩ else κ.i0 a)).1,
        κ.liftL n (κ.dropL n ℓ)⟩ : Lf (κ.shape (n+1))) = ⟨a, y, ℓ⟩
      rw [dif_pos hy, liftL_dropL n ℓ (right_ne_zero_of_mul hm')]
      simp only [OrderIso.apply_symm_apply]

theorem liftL_restrictS : ∀ (n : ℕ) (d : Str (κ.shape n)) (π : Pol (κ.shape n)),
    mass (κ.kf n) (Shape.run d π) ≠ 0 →
    κ.liftL n (CausalSpectrum.run (κ.restrictS n d) (κ.restrictP n π)) = Shape.run d π
  | 0, _, _, _ => rfl
  | n + 1, d, π, hm => by
      have hm' : κ.K π.1 (d.1 π.1) * mass (κ.kf n) (Shape.run (d.2 π.1 (d.1 π.1))
          (π.2 π.1 (d.1 π.1))) ≠ 0 := hm
      have hy := κ.mem_supp_of_ne (left_ne_zero_of_mul hm')
      have ih := liftL_restrictS n (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))
        (right_ne_zero_of_mul hm')
      have e : (κ.restrictS (n+1) d).1 π.1 = (κ.emb π.1).symm ⟨d.1 π.1, hy⟩ := by
        show (if h : d.1 π.1 ∈ κ.supp π.1 then (κ.emb π.1).symm ⟨d.1 π.1, h⟩ else κ.i0 π.1) = _
        rw [dif_pos hy]
      show (⟨π.1, (κ.emb π.1 ((κ.restrictS (n+1) d).1 π.1)).1,
        κ.liftL n (CausalSpectrum.run (κ.restrictS n (d.2 π.1 (κ.emb π.1 ((κ.restrictS (n+1) d).1 π.1)).1))
          (κ.restrictP n (π.2 π.1 (κ.emb π.1 ((κ.restrictS (n+1) d).1 π.1)).1)))⟩ :
          Lf (κ.shape (n+1))) = ⟨π.1, d.1 π.1, Shape.run (d.2 π.1 (d.1 π.1)) (π.2 π.1 (d.1 π.1))⟩
      rw [e]
      simp only [OrderIso.apply_symm_apply]
      rw [ih]

/-! ## Transfer of exact laws -/

theorem sum_push_event {α β : Type} [Fintype α] [Fintype β] (φ : α → β) (w : α → ℝ)
    (P : β → Prop) :
    (∑ b, if P b then (∑ a, if φ a = b then w a else 0) else 0) =
      ∑ a, if P (φ a) then w a else 0 := by
  calc _ = ∑ b, ∑ a, if φ a = b then (if P b then w a else 0) else 0 := by
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs with h
        · refine Finset.sum_congr rfl fun a _ => ?_; split_ifs <;> simp_all
        · simp [h]
    _ = ∑ a, ∑ b, if φ a = b then (if P b then w a else 0) else 0 := Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_ite_eq]; simp

theorem exact_of_red (n : ℕ) {q' : Strategy (κ.red.rounds n) → ℝ} (hq : IsPmf q')
    (he : Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π)
      (fun ℓ : Leaf _ => leafMass ℓ) q') :
    IsPmf (fun d => ∑ d', if κ.extendS n d' = d then q' d' else 0) ∧
      (∀ (π : Pol (κ.shape n)) (ℓ : Lf (κ.shape n)),
        (∑ d, if Shape.run d π = ℓ then (∑ d', if κ.extendS n d' = d then q' d' else 0) else 0) =
          if compat ℓ π then mass (κ.kf n) ℓ else 0) ∧
      pmfEntropy (fun d => ∑ d', if κ.extendS n d' = d then q' d' else 0) ≤ pmfEntropy q' := by
  refine ⟨⟨fun d => Finset.sum_nonneg fun d' _ => by split_ifs; exacts [hq.1 d', le_rfl], ?_⟩,
    ?_, pmfEntropy_push_le q' hq.1 (κ.extendS n)⟩
  · have := sum_push_event (κ.extendS n) q' (fun _ => True)
    simp only [if_true] at this; rw [this, hq.2]
  · intro π ℓ
    rw [sum_push_event (κ.extendS n) q' (fun d => Shape.run d π = ℓ)]
    simp only [κ.run_extendS]
    by_cases hm : mass (κ.kf n) ℓ = 0
    · rw [hm]; simp only [ite_self]
      refine Finset.sum_eq_zero fun d' _ => ?_
      rw [if_neg]
      intro h
      have := κ.mass_liftL n (CausalSpectrum.run d' (κ.restrictP n π))
      rw [h, hm] at this
      exact absurd this (ne_of_lt (leafMass_pos _))
    · have hℓ := κ.liftL_dropL n ℓ hm
      rw [← hℓ]
      simp only [(κ.liftL_injective n).eq_iff]
      rw [he, κ.compat_liftL, κ.mass_liftL]

theorem exact_to_red (n : ℕ) {q : Str (κ.shape n) → ℝ} (hq : IsPmf q)
    (he : ∀ (π : Pol (κ.shape n)) (ℓ : Lf (κ.shape n)),
      (∑ d, if Shape.run d π = ℓ then q d else 0) = if compat ℓ π then mass (κ.kf n) ℓ else 0) :
    IsPmf (fun d' => ∑ d, if κ.restrictS n d = d' then q d else 0) ∧
      Exact CausalSpectrum.run (fun ℓ π => CompatiblePolicy ℓ π) (fun ℓ : Leaf _ => leafMass ℓ)
        (fun d' => ∑ d, if κ.restrictS n d = d' then q d else 0) ∧
      pmfEntropy (fun d' => ∑ d, if κ.restrictS n d = d' then q d else 0) ≤ pmfEntropy q := by
  refine ⟨⟨fun d => Finset.sum_nonneg fun d' _ => by split_ifs; exacts [hq.1 d', le_rfl], ?_⟩,
    ?_, pmfEntropy_push_le q hq.1 (κ.restrictS n)⟩
  · have := sum_push_event (κ.restrictS n) q (fun _ => True)
    simp only [if_true] at this; rw [this, hq.2]
  · intro πr ℓr
    show (∑ d', if CausalSpectrum.run d' πr = ℓr then
      (∑ d, if κ.restrictS n d = d' then q d else 0) else 0) = _
    rw [sum_push_event (κ.restrictS n) q (fun d' => CausalSpectrum.run d' πr = ℓr)]
    set π := κ.extendP n πr
    have hπ : κ.restrictP n π = πr := κ.restrictP_extendP n πr
    have hterm : ∀ d, (if CausalSpectrum.run (κ.restrictS n d) πr = ℓr then q d else 0) =
        if Shape.run d π = κ.liftL n ℓr then q d else 0 := by
      intro d
      by_cases hq0 : q d = 0
      · simp [hq0]
      have hpos : 0 < q d := lt_of_le_of_ne (hq.1 d) (Ne.symm hq0)
      have hmass : mass (κ.kf n) (Shape.run d π) ≠ 0 := by
        intro h0
        have hx := he π (Shape.run d π)
        rw [if_pos (run_compat d π), h0] at hx
        have : q d ≤ ∑ d2, if Shape.run d2 π = Shape.run d π then q d2 else 0 := by
          have := Finset.single_le_sum (f := fun d2 => if Shape.run d2 π = Shape.run d π
            then q d2 else 0) (fun d2 _ => by split_ifs; exacts [hq.1 d2, le_rfl])
            (Finset.mem_univ d)
          simpa using this
        linarith
      have hl := κ.liftL_restrictS n d π hmass
      rw [hπ] at hl
      have hiff : CausalSpectrum.run (κ.restrictS n d) πr = ℓr ↔ Shape.run d π = κ.liftL n ℓr := by
        rw [← hl]; exact (κ.liftL_injective n).eq_iff.symm
      simp only [hiff]
    rw [Finset.sum_congr rfl fun d _ => hterm d, he, κ.compat_liftL, κ.mass_liftL, hπ]

theorem zcost_bdd (Z : ZTree) : BddBelow {x | ∃ q : Z.Str → ℝ, IsPmf q ∧
    (∀ (π : Z.Pol) (ℓ : Z.Lf),
      (∑ s, if Shape.run s π = ℓ then q s else 0) = if compat ℓ π then Z.P ℓ else 0) ∧
    x = pmfEntropy q} :=
  ⟨Z.L, by rintro _ ⟨q, hq, he, rfl⟩; exact zero_lower Z hq he⟩

/-- **`C_n(κ₀) = C_n(κ₀.red)`**: the exact cost of the full `n`-round tree, zero branches
kept, equals the exact cost of the reduced positive tree. -/
theorem zcost_ztree (n : ℕ) : zcost (κ.ztree n) = tcost (κ.red.rounds n) := by
  apply le_antisymm
  · obtain ⟨q0, hq0, he0, -⟩ := tree_seed (κ.red.rounds n)
    refine le_csInf ⟨_, q0, hq0, he0, rfl⟩ ?_
    rintro _ ⟨q', hq', he', rfl⟩
    obtain ⟨hp, hex, hH⟩ := κ.exact_of_red n hq' he'
    exact (csInf_le (zcost_bdd _) ⟨_, hp, hex, rfl⟩).trans hH
  · obtain ⟨q0, hq0, he0, -⟩ := zero_closure (κ.ztree n)
    refine le_csInf ⟨_, q0, hq0, he0, rfl⟩ ?_
    rintro _ ⟨q, hq, he, rfl⟩
    obtain ⟨hp, hex, hH⟩ := κ.exact_to_red n hq he
    exact (tcost_le _ hp hex).trans hH

/-- `C_n(κ₀) = C_n(κ₀.red)` in terms of the countable-seed cost of the reduction. -/
theorem costBits_eq_red (n : ℕ) : κ.costBits n = κ.red.costBits n := by
  rw [costBits, zcost_ztree, Kernel.costBits_eq_tcost]

/-- **Subadditivity for nonnegative kernels**: `C_{m+n} ≤ C_m + C_n`. -/
theorem costBits_subadditive (m n : ℕ) :
    κ.costBits (m + n) ≤ κ.costBits m + κ.costBits n := by
  simp only [costBits_eq_red]; exact κ.red.costBits_subadditive m n

/-- **Fekete for nonnegative kernels**: `C_n/n → h_max = inf_{n ≥ 1} C_n/n`. -/
theorem hmax_eq_inf :
    κ.hmax = sInf ((fun n : ℕ => κ.costBits n / n) '' Set.Ici 1) := by
  simp only [costBits_eq_red, hmax_eq]; exact κ.red.hmax_eq_inf

theorem costBits_fekete :
    Tendsto (fun n : ℕ => κ.costBits n / n) atTop
      (𝓝 (sInf ((fun n : ℕ => κ.costBits n / n) '' Set.Ici 1))) := by
  simp only [costBits_eq_red]; exact κ.red.costBits_fekete

/-- **Exact lower bound** `n · h_max ≤ C_n` for nonnegative kernels. -/
theorem hmax_mul_le_costBits {n : ℕ} (hn : 1 ≤ n) : n * κ.hmax ≤ κ.costBits n := by
  rw [costBits_eq_red, hmax_eq]; exact κ.red.hmax_mul_le_costBits hn

end CausalSpectrum.Zero.NNKernel
/-
The zero set of the residual `C_n - n h_max`.

`C_1` is bounded below by the least entropy of a coupling of the output laws (data
processing to the tuple of first answers). The couplings form a compact set, so the least
entropy is attained. A coupling whose entropy equals the entropy `h_max` of one marginal
makes every other coordinate a function of that marginal. Hence the residual vanishes at
one horizon `n ≥ 1` (equivalently at all horizons) if and only if every output law is a
deterministic image of a maximizing law.
-/
import CausalSeed.GapImage
import CausalSeed.SeedDataProcessing

noncomputable section
open Classical Finset Topology
open scoped ENNReal

namespace CausalSpectrum

theorem negMulLog_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  rcases hx.eq_or_lt with rfl | hx'
  · simp
  rcases hy.eq_or_lt with rfl | hy'
  · simp
  simp only [Real.negMulLog]
  have h1 := Real.log_le_log hx' (le_add_of_nonneg_right hy)
  have h2 := Real.log_le_log hy' (le_add_of_nonneg_left hx)
  nlinarith

theorem negMulLog_add_lt {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.negMulLog (x + y) < Real.negMulLog x + Real.negMulLog y := by
  simp only [Real.negMulLog]
  have h1 := Real.log_lt_log hx (lt_add_of_pos_right x hy)
  have h2 := Real.log_lt_log hy (lt_add_of_pos_left y hx)
  nlinarith

theorem negMulLog_sum_le {α : Type*} (s : Finset α) (u : α → ℝ) (hu : ∀ a ∈ s, 0 ≤ u a) :
    Real.negMulLog (∑ a ∈ s, u a) ≤ ∑ a ∈ s, Real.negMulLog (u a) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    have h0 : 0 ≤ ∑ b ∈ s, u b := sum_nonneg fun b hb => hu b (mem_insert_of_mem hb)
    exact (negMulLog_add_le (hu a (mem_insert_self a s)) h0).trans
      (add_le_add le_rfl (ih fun b hb => hu b (mem_insert_of_mem hb)))

/-- Equality in the subadditivity of `negMulLog` forces at most one positive term. -/
theorem eq_single_of_negMulLog {α : Type*} (s : Finset α) (u : α → ℝ) (hu : ∀ a ∈ s, 0 ≤ u a)
    (heq : ∑ a ∈ s, Real.negMulLog (u a) ≤ Real.negMulLog (∑ a ∈ s, u a))
    {a b : α} (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) (hpa : 0 < u a) : u b = 0 := by
  by_contra hne
  have hpb : 0 < u b := lt_of_le_of_ne (hu b hb) (Ne.symm hne)
  set r := (s.erase a).erase b
  have hb' : b ∈ s.erase a := mem_erase.2 ⟨Ne.symm hab, hb⟩
  have hr : ∀ c ∈ r, 0 ≤ u c := fun c hc => hu c (mem_of_mem_erase (mem_of_mem_erase hc))
  have e1 : ∑ c ∈ s, u c = u a + (u b + ∑ c ∈ r, u c) := by
    rw [← add_sum_erase _ _ ha, ← add_sum_erase _ _ hb']
  have e2 : ∑ c ∈ s, Real.negMulLog (u c) =
      Real.negMulLog (u a) + (Real.negMulLog (u b) + ∑ c ∈ r, Real.negMulLog (u c)) := by
    rw [← add_sum_erase _ _ ha, ← add_sum_erase _ _ hb']
  have hR := negMulLog_sum_le r u hr
  have hR0 : 0 ≤ ∑ c ∈ r, u c := sum_nonneg hr
  have h3 := negMulLog_add_lt hpa hpb
  have h4 := negMulLog_add_le (add_pos hpa hpb).le hR0
  rw [e1, e2, ← add_assoc] at heq
  rw [← add_assoc] at heq
  linarith

namespace Kernel
open Completion
variable (κ : Kernel)

/-- Tuples of first answers, one per action. -/
abbrev Tup := (a : Fin κ.nA) → Fin (κ.nY a)

/-- Couplings of the output laws. -/
def Cpl : Set (κ.Tup → ℝ) :=
  {τ | (∀ t, 0 ≤ τ t) ∧ ∀ a z, (∑ t, if t a = z then τ t else 0) = κ.K a z}

def tupEnt (τ : κ.Tup → ℝ) : ℝ := ∑ t, Real.negMulLog (τ t)

theorem K_le_one (a : Fin κ.nA) (z : Fin (κ.nY a)) : κ.K a z ≤ 1 := by
  have := κ.Ksum a
  exact this ▸ Finset.single_le_sum (fun y _ => (κ.Kpos a y).le) (Finset.mem_univ z)

theorem cpl_le_one {τ : κ.Tup → ℝ} (hτ : τ ∈ κ.Cpl) (t : κ.Tup) : τ t ≤ 1 := by
  set a : Fin κ.nA := ⟨0, κ.hA⟩
  have h := hτ.2 a (t a)
  calc τ t = if t a = t a then τ t else 0 := by simp
    _ ≤ ∑ t', if t' a = t a then τ t' else 0 :=
        Finset.single_le_sum (f := fun t' => if t' a = t a then τ t' else 0)
          (fun t' _ => by split_ifs <;> simp [hτ.1 t']) (mem_univ t)
    _ = κ.K a (t a) := h
    _ ≤ 1 := κ.K_le_one _ _

theorem isCompact_cpl : IsCompact κ.Cpl := by
  apply Metric.isCompact_of_isClosed_isBounded
  · have e : κ.Cpl = (⋂ t, {τ : κ.Tup → ℝ | 0 ≤ τ t}) ∩ ⋂ a, ⋂ z,
        {τ : κ.Tup → ℝ | (∑ t, if t a = z then τ t else 0) = κ.K a z} := by
      ext τ; simp [Cpl, Set.mem_iInter]
    rw [e]
    refine (isClosed_iInter fun t => isClosed_le continuous_const (continuous_apply t)).inter ?_
    · refine isClosed_iInter fun a => isClosed_iInter fun z => isClosed_eq ?_ continuous_const
      exact continuous_finsetSum _ fun t _ => by
        split_ifs
        · exact continuous_apply t
        · exact continuous_const
  · refine (Metric.isBounded_closedBall (x := (0 : κ.Tup → ℝ)) (r := 1)).subset ?_
    intro τ hτ
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hτ.1 t)]
    exact κ.cpl_le_one hτ t

theorem continuous_tupEnt : Continuous κ.tupEnt :=
  continuous_finsetSum _ fun t _ => Real.continuous_negMulLog.comp (continuous_apply t)

/-- The tuple of first answers of each strategy of a seed. -/
def tupOf (S : Seed κ.toITree) : ℕ → κ.Tup := fun i a => S.strategy i ⟨[], a⟩

/-- The tuple law of a seed exact to horizon `1` is a coupling. -/
theorem push_mem_cpl (S : Seed κ.toITree) (hS : S.ExactTo 1) :
    S.push (κ.tupOf S) ∈ κ.Cpl := by
  refine ⟨fun t => S.push_nonneg _ t, fun a z => ?_⟩
  rw [show (∑ t, if t a = z then S.push (κ.tupOf S) t else 0) =
      ∑' i, if (κ.tupOf S i) a = z then S.weight i else 0 by
    convert S.push_event (κ.tupOf S) (fun t : κ.Tup => t a = z)]
  have := hS [(a.val, z.val)] (by simp)
  rw [κ.pathMass_cons, pathMass_nil, mul_one] at this
  rw [← this]
  refine tsum_congr fun i => ?_
  show _ = S.weight i * indAgree κ.toITree (S.strategy i) [(a.val, z.val)]
  rw [κ.indAgree_single]
  by_cases e : S.strategy i ⟨[], a⟩ = z
  · rw [if_pos (show κ.tupOf S i a = z from e), if_pos e, mul_one]
  · rw [if_neg (show ¬ κ.tupOf S i a = z from e), if_neg e, mul_zero]

theorem exists_seed_one : ∃ S : Seed κ.toITree, S.ExactTo 1 := by
  by_contra h
  push_neg at h
  have := κ.finiteCost_ne_top 1
  rw [← countableFiniteCost_eq, countableFiniteCost] at this
  apply this
  have : IsEmpty {S : Seed κ.toITree // S.ExactTo 1} := ⟨fun S => h S.1 S.2⟩
  exact iInf_of_empty _

/-- The least coupling entropy is attained. -/
theorem exists_min_cpl : ∃ τ ∈ κ.Cpl, ∀ σ ∈ κ.Cpl, κ.tupEnt τ ≤ κ.tupEnt σ := by
  obtain ⟨S, hS⟩ := κ.exists_seed_one
  obtain ⟨τ, hτ, hmin⟩ := κ.isCompact_cpl.exists_isMinOn ⟨_, κ.push_mem_cpl S hS⟩
    κ.continuous_tupEnt.continuousOn
  exact ⟨τ, hτ, fun σ hσ => hmin hσ⟩

/-- `C_1 ≥` least coupling entropy (nats). -/
theorem finiteCost_one_ge {τ : κ.Tup → ℝ} (hτ : τ ∈ κ.Cpl)
    (hmin : ∀ σ ∈ κ.Cpl, κ.tupEnt τ ≤ κ.tupEnt σ) :
    ENNReal.ofReal (κ.tupEnt τ) ≤ finiteCost κ.toITree 1 := by
  rw [← countableFiniteCost_eq, countableFiniteCost]
  refine le_iInf fun ⟨S, hS⟩ => ?_
  refine le_trans ?_ (S.push_entropy_le (κ.tupOf S))
  rw [← ENNReal.ofReal_sum_of_nonneg fun t _ =>
    Real.negMulLog_nonneg (S.push_nonneg _ t) (S.push_le_one _ t)]
  exact ENNReal.ofReal_le_ofReal (hmin _ (κ.push_mem_cpl S hS))

/-- A coupling with entropy at most that of the `j`-th marginal is supported on a graph. -/
theorem image_of_cpl {τ : κ.Tup → ℝ} (hτ : τ ∈ κ.Cpl) (j : Fin κ.nA)
    (hle : κ.tupEnt τ ≤ ∑ y, Real.negMulLog (κ.K j y)) :
    ∃ f : (a : Fin κ.nA) → Fin (κ.nY j) → Fin (κ.nY a), κ.IsImage j f := by
  set F : Fin (κ.nY j) → Finset κ.Tup := fun y => univ.filter fun t => t j = y
  have hFs : ∀ y, ∑ t ∈ F y, τ t = κ.K j y := fun y => by
    rw [← hτ.2 j y, sum_filter]
  have hsplit : κ.tupEnt τ = ∑ y, ∑ t ∈ F y, Real.negMulLog (τ t) :=
    (Finset.sum_fiberwise univ (fun t : κ.Tup => t j) (fun t => Real.negMulLog (τ t))).symm
  have hle' : ∀ y, Real.negMulLog (∑ t ∈ F y, τ t) ≤ ∑ t ∈ F y, Real.negMulLog (τ t) :=
    fun y => negMulLog_sum_le _ _ fun t _ => hτ.1 t
  have heq : ∀ y, ∑ t ∈ F y, Real.negMulLog (τ t) ≤ Real.negMulLog (∑ t ∈ F y, τ t) := by
    intro y
    by_contra hlt
    push_neg at hlt
    have : ∑ y, Real.negMulLog (∑ t ∈ F y, τ t) < ∑ y, ∑ t ∈ F y, Real.negMulLog (τ t) :=
      Finset.sum_lt_sum (fun y _ => hle' y) ⟨y, mem_univ y, hlt⟩
    simp only [hFs] at this
    linarith
  -- in each fiber, one tuple carries all the mass
  have hex : ∀ y, ∃ t ∈ F y, τ t = κ.K j y := by
    intro y
    obtain ⟨t, ht, hpos⟩ : ∃ t ∈ F y, 0 < τ t := by
      by_contra hno
      push_neg at hno
      have : ∑ t ∈ F y, τ t ≤ 0 := sum_nonpos hno
      rw [hFs] at this
      linarith [κ.Kpos j y]
    refine ⟨t, ht, ?_⟩
    rw [← hFs, ← add_sum_erase _ _ ht, sum_eq_zero, add_zero]
    intro t' ht'
    exact eq_single_of_negMulLog _ _ (fun t _ => hτ.1 t) (heq y) ht (mem_of_mem_erase ht')
      (Ne.symm (ne_of_mem_erase ht')) hpos
  choose g hgF hgK using hex
  have hzero : ∀ t, (∀ y, t ≠ g y) → τ t = 0 := by
    intro t ht
    have hmem : t ∈ F (t j) := by simp [F]
    have := hFs (t j)
    rw [← add_sum_erase _ _ (hgF (t j)), hgK, add_eq_left] at this
    exact (sum_eq_zero_iff_of_nonneg fun s _ => hτ.1 s).1 this t
      (mem_erase.2 ⟨fun h => ht _ h, hmem⟩)
  refine ⟨fun a y => g y a, fun a z => ?_⟩
  rw [← hτ.2 a z]
  have hgj : ∀ y, g y j = y := fun y => by simpa [F] using hgF y
  have hginj : Function.Injective g := fun y y' h => by rw [← hgj y, ← hgj y', h]
  calc ∑ y ∈ univ.filter (fun y => g y a = z), κ.K j y
      = ∑ y, if g y a = z then τ (g y) else 0 := by
        rw [sum_filter]; exact sum_congr rfl fun y _ => by rw [hgK]
    _ = ∑ t ∈ univ.image g, if t a = z then τ t else 0 := by
        rw [sum_image fun y _ y' _ h => hginj h]
    _ = ∑ t, if t a = z then τ t else 0 := by
        refine sum_subset (subset_univ _) fun t _ ht => ?_
        have : ∀ y, t ≠ g y := fun y h => ht (mem_image.2 ⟨y, mem_univ y, h.symm⟩)
        simp [hzero t this]

/-- **The zero set.** `C_1 = h_max` iff every output law is a deterministic image of a
maximizing law, iff `C_n = n h_max` for every `n`. -/
theorem zero_set :
    List.TFAE [κ.costBits 1 = κ.hmax,
      ∃ j₀ f, κ.IsImage j₀ f,
      ∀ n : ℕ, κ.costBits n = n * κ.hmax] := by
  tfae_have 1 → 2 := by
    intro h1
    obtain ⟨j, hj⟩ := κ.exists_hmax
    obtain ⟨τ, hτ, hmin⟩ := κ.exists_min_cpl
    refine ⟨j, κ.image_of_cpl hτ j ?_⟩
    have hge := κ.finiteCost_one_ge hτ hmin
    have hl : 0 < Real.log 2 := Real.log_pos one_lt_two
    have hc : (finiteCost κ.toITree 1).toReal = Real.log 2 * κ.hmax := by
      have : (finiteCost κ.toITree 1).toReal / Real.log 2 = κ.hmax := h1
      field_simp at this; linarith
    have h0 : 0 ≤ κ.tupEnt τ := sum_nonneg fun t _ =>
      Real.negMulLog_nonneg (hτ.1 t) (κ.cpl_le_one hτ t)
    have := ENNReal.toReal_mono (κ.finiteCost_ne_top 1) hge
    rw [ENNReal.toReal_ofReal h0, hc, ← hj] at this
    refine this.trans (le_of_eq ?_)
    simp only [actEntropy, Finset.mul_sum, negMulLog_eq_bits]
  tfae_have 2 → 3 := fun ⟨j₀, f, hf⟩ => (costBits_eq_of_image hf).2
  tfae_have 3 → 1 := fun h => by simpa using h 1
  tfae_finish

end Kernel
end CausalSpectrum

namespace CausalSpectrum.Kernel
variable (κ : Kernel)

/-- Since the residual is nondecreasing, a bound along any unbounded sequence of horizons
bounds it at every horizon. -/
theorem residual_bdd_of_subseq {K : ℝ} (N : ℕ → ℕ) (hN : ∀ n, ∃ k, n ≤ N k)
    (hK : ∀ k, κ.costBits (N k) - (N k) * κ.hmax ≤ K) (n : ℕ) :
    κ.costBits n - n * κ.hmax ≤ K := by
  obtain ⟨k, hk⟩ := hN n
  exact (κ.residual_mono hk).trans (hK k)

end CausalSpectrum.Kernel

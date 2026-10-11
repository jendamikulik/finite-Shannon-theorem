/-
Rényi spectrum, stage 1: one finite controlled tree.

On a finite tree the greedy seed `J` satisfies the stochastic sandwich
`Z ≼st J ≼st Z + W` (`seedCDF_le_Fstar`, `survival_le_wMixture`), and every
ordinary exact source `U` (a `Coupling`) satisfies `Z ≼st I_U`.  Here these are
turned, by a layer-cake identity for `t ↦ 2^{λ t}`, into the Rényi bounds of the
note, simultaneously for every order `α > 0`, `α ≠ 1`:
  `R_α(Z) ≤ H_α(seed) ≤ R_α(Z) + d_α`,   `R_α(Z) ≤ H_α(U)`,
with `d_α = log₂(1/2 + 2^{-α}/α)/(1-α)` (bits).
-/
import CausalSeed.Note
import CausalSeed.Penalty
import Mathlib.MeasureTheory.Integral.ExpDecay

noncomputable section
open Classical MeasureTheory Set
namespace CausalSpectrum.Renyi

/-! ### The layer-cake kernel `g(t) = λ ln 2 · 2^{λ t}` -/

def gw (l t : ℝ) : ℝ := l * Real.log 2 * (2:ℝ) ^ (l * t)

theorem rpow_two_eq (x : ℝ) : (2:ℝ) ^ x = Real.exp (Real.log 2 * x) :=
  Real.rpow_def_of_pos (by norm_num) x

theorem continuous_gw (l : ℝ) : Continuous (gw l) := by
  unfold gw; simp_rw [rpow_two_eq]; fun_prop

theorem hasDerivAt_pow2 (l t : ℝ) : HasDerivAt (fun t => (2:ℝ) ^ (l * t)) (gw l t) t := by
  simp_rw [rpow_two_eq]
  have := (((hasDerivAt_id t).const_mul l).const_mul (Real.log 2)).exp
  unfold gw; rw [rpow_two_eq]
  convert this using 1
  · funext x; simp
  · simp; ring

theorem interval_gw (l a b : ℝ) : ∫ t in a..b, gw l t = (2:ℝ) ^ (l * b) - (2:ℝ) ^ (l * a) :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hasDerivAt_pow2 l t)
    ((continuous_gw l).intervalIntegrable _ _)

theorem setIntegral_Ioc_gw (l : ℝ) {a b : ℝ} (hab : a ≤ b) :
    ∫ t in Ioc a b, gw l t = (2:ℝ) ^ (l * b) - (2:ℝ) ^ (l * a) := by
  rw [← intervalIntegral.integral_of_le hab, interval_gw]

theorem gw_nonneg {l : ℝ} (hl : 0 ≤ l) (t : ℝ) : 0 ≤ gw l t := by
  unfold gw; have := Real.log_pos (show (1:ℝ) < 2 by norm_num); positivity

theorem gw_nonpos {l : ℝ} (hl : l ≤ 0) (t : ℝ) : gw l t ≤ 0 := by
  unfold gw
  have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have : 0 < (2:ℝ) ^ (l * t) := by positivity
  exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hl (by linarith)) this.le

/-- One atom: `∫_0^∞ g(t) [t < x] w dt = w (2^{λ x} - 1)`. -/
theorem atom_layer (l : ℝ) {x : ℝ} (hx : 0 ≤ x) (w : ℝ) :
    IntegrableOn (fun t => gw l t * (if t < x then w else 0)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), gw l t * (if t < x then w else 0) = w * ((2:ℝ) ^ (l * x) - 1) := by
  have hfun : (fun t => gw l t * (if t < x then w else 0)) =
      (Iio x).indicator (fun t => w * gw l t) := by
    funext t; simp only [Set.indicator, Set.mem_Iio]; split_ifs <;> ring
  rw [hfun]
  have hset : Iio x ∩ Ioi (0:ℝ) = Ioo 0 x := by ext t; simp [and_comm]
  constructor
  · refine (integrable_indicator_iff measurableSet_Iio).2 ?_
    rw [IntegrableOn, Measure.restrict_restrict measurableSet_Iio, hset]
    exact (((continuous_const.mul (continuous_gw l)).integrableOn_Icc (a := 0) (b := x)).mono_set
      Ioo_subset_Icc_self)
  · rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio, hset,
      ← integral_Ioc_eq_integral_Ioo, integral_const_mul, setIntegral_Ioc_gw l hx]
    simp

/-- A finite family of atoms. -/
theorem finset_layer {ι : Type*} (s : Finset ι) (l : ℝ) (w x : ι → ℝ) (hx : ∀ k, 0 ≤ x k) :
    IntegrableOn (fun t => gw l t * ∑ k ∈ s, (if t < x k then w k else 0)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), gw l t * ∑ k ∈ s, (if t < x k then w k else 0) =
        ∑ k ∈ s, w k * ((2:ℝ) ^ (l * x k) - 1) := by
  simp_rw [Finset.mul_sum]
  exact ⟨integrable_finset_sum _ fun k _ => (atom_layer l (hx k) (w k)).1,
    (integral_finset_sum _ fun k _ => (atom_layer l (hx k) (w k)).1).trans
      (Finset.sum_congr rfl fun k _ => (atom_layer l (hx k) (w k)).2)⟩

/-- The noise `W`: `∫_0^∞ g(t) P(z + W ≥ t) dt = 2^{λ z} θ - 1`, `λ < 1`. -/
theorem w_layer {l : ℝ} (hl : l < 1) {z : ℝ} (hz : 0 ≤ z) :
    IntegrableOn (fun t => gw l t * wSurvival (t - z)) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), gw l t * wSurvival (t - z) =
        (2:ℝ) ^ (l * z) * (1 / 2 + (2:ℝ) ^ (l - 1) / (1 - l)) - 1 := by
  set L := Real.log 2
  have hL : 0 < L := Real.log_pos (by norm_num)
  set a := (l - 1) * L
  have ha : a < 0 := mul_neg_of_neg_of_pos (by linarith) hL
  set c := l * L * (2:ℝ) ^ z
  have e1 : EqOn (fun t => gw l t * wSurvival (t - z)) (gw l) (Ioc 0 z) := by
    intro t ht; simp only [wSurvival, if_pos (show t - z ≤ 0 by linarith [ht.2])]; ring
  have e2 : EqOn (fun t => gw l t * wSurvival (t - z)) (fun t => gw l t / 2) (Ioc z (z + 1)) := by
    intro t ht
    simp only [wSurvival, if_neg (show ¬ t - z ≤ 0 by linarith [ht.1])]
    rcases lt_or_eq_of_le (show t - z ≤ 1 by linarith [ht.2]) with h | h
    · rw [if_pos h]; ring
    · rw [if_neg (by linarith), h]; norm_num; ring
  have e3 : EqOn (fun t => gw l t * wSurvival (t - z)) (fun t => c * Real.exp (a * t))
      (Ioi (z + 1)) := by
    intro t ht
    have ht' : z + 1 < t := ht
    simp only [wSurvival, if_neg (show ¬ t - z ≤ 0 by linarith), if_neg (show ¬ t - z < 1 by linarith)]
    simp only [gw, c, a, rpow_two_eq, L]
    rw [show l * Real.log 2 * Real.exp (Real.log 2 * (l * t)) * Real.exp (Real.log 2 * -(t - z)) =
      l * Real.log 2 * (Real.exp (Real.log 2 * (l * t)) * Real.exp (Real.log 2 * -(t - z))) by ring,
      ← Real.exp_add, mul_assoc (l * Real.log 2), ← Real.exp_add]
    congr 2; ring
  have i1 : IntegrableOn (fun t => gw l t * wSurvival (t - z)) (Ioc 0 z) :=
    (((continuous_gw l).integrableOn_Icc (a := 0) (b := z)).mono_set Ioc_subset_Icc_self).congr_fun
      e1.symm measurableSet_Ioc
  have i2 : IntegrableOn (fun t => gw l t * wSurvival (t - z)) (Ioc z (z + 1)) :=
    ((((continuous_gw l).div_const 2).integrableOn_Icc (a := z) (b := z + 1)).mono_set
      Ioc_subset_Icc_self).congr_fun e2.symm measurableSet_Ioc
  have i3 : IntegrableOn (fun t => gw l t * wSurvival (t - z)) (Ioi (z + 1)) := by
    have := (exp_neg_integrableOn_Ioi (z + 1) (show 0 < -a by linarith)).const_mul c
    exact IntegrableOn.congr_fun (IntegrableOn.congr_fun this (fun t _ => by simp only [neg_neg])
      measurableSet_Ioi) e3.symm measurableSet_Ioi
  have hU1 : Ioc 0 z ∪ Ioc z (z + 1) = Ioc 0 (z + 1) := Ioc_union_Ioc_eq_Ioc hz (by linarith)
  have hU2 : Ioc 0 (z + 1) ∪ Ioi (z + 1) = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by linarith)
  have d1 : Disjoint (Ioc 0 z) (Ioc z (z + 1)) :=
    Set.disjoint_left.2 fun t h1 h2 => by
      simp only [Set.mem_Ioc] at h1 h2; linarith
  have d2 : Disjoint (Ioc 0 (z + 1)) (Ioi (z + 1)) :=
    Set.disjoint_left.2 fun t h1 h2 => by
      simp only [Set.mem_Ioc, Set.mem_Ioi] at h1 h2; linarith
  have i12 : IntegrableOn (fun t => gw l t * wSurvival (t - z)) (Ioc 0 (z + 1)) :=
    hU1 ▸ i1.union i2
  refine ⟨hU2 ▸ i12.union i3, ?_⟩
  rw [← hU2, setIntegral_union d2 measurableSet_Ioi i12 i3, ← hU1,
    setIntegral_union d1 measurableSet_Ioc i1 i2, setIntegral_congr_fun measurableSet_Ioc e1,
    setIntegral_congr_fun measurableSet_Ioc e2, setIntegral_congr_fun measurableSet_Ioi e3,
    integral_div, setIntegral_Ioc_gw l hz,
    setIntegral_Ioc_gw l (show z ≤ z + 1 by linarith), integral_const_mul,
    integral_exp_mul_Ioi ha]
  -- algebra
  have k1 : (2:ℝ) ^ (l * (z + 1)) = (2:ℝ) ^ (l * z) * (2:ℝ) ^ l := by
    rw [← Real.rpow_add (by norm_num)]; ring_nf
  have k2 : (2:ℝ) ^ z * Real.exp (a * (z + 1)) = (2:ℝ) ^ (l * z) * (2:ℝ) ^ (l - 1) := by
    simp only [rpow_two_eq, a, L, ← Real.exp_add]; congr 1; ring
  have k3 : (2:ℝ) ^ (l - 1) = (2:ℝ) ^ l / 2 := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_one]
  have hl1 : (1 - l) ≠ 0 := by linarith
  simp only [mul_zero, Real.rpow_zero]
  simp only [c]
  rw [show l * L * (2:ℝ) ^ z * (-Real.exp (a * (z + 1)) / a) =
      -(l * L) * ((2:ℝ) ^ z * Real.exp (a * (z + 1))) / a by ring, k2, k1]
  simp only [a]
  rw [k3]
  have hl2 : l - 1 ≠ 0 := fun h => hl1 (by linarith)
  have hL0 : L ≠ 0 := hL.ne'
  field_simp
  ring

theorem infoMass_nonneg_of_le {w : ℝ} (h0 : 0 < w) (h1 : w ≤ 1) : 0 ≤ infoMass w := by
  unfold infoMass
  have := Real.logb_nonpos (b := 2) (by norm_num) h0.le h1
  linarith

/-! ### Rényi moments and entropies -/

/-- `∑ w^α` with `α = 1 - λ`, written as `E 2^{λ I}`. -/
theorem rpow_eq_moment {α w : ℝ} (hα : 0 < α) (hw : 0 ≤ w) :
    w ^ α = w * (2:ℝ) ^ ((1 - α) * infoMass w) := by
  rcases eq_or_lt_of_le hw with h | h
  · subst h; simp [Real.zero_rpow hα.ne']
  · have : (2:ℝ) ^ ((1 - α) * infoMass w) = w ^ (α - 1) := by
      rw [infoMass, show (1 - α) * -Real.logb 2 w = Real.logb 2 w * (α - 1) by ring,
        Real.rpow_mul (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) h]
    rw [this, ← Real.rpow_one_add' hw (by linarith)]
    ring_nf

/-- Rényi entropy of order `α ≠ 1` of a finite family of weights, in bits. -/
def renyiF {ι : Type*} (s : Finset ι) (α : ℝ) (w : ι → ℝ) : ℝ :=
  Real.logb 2 (∑ k ∈ s, w k ^ α) / (1 - α)

/-- The note's constant `d_α`. -/
def dAlpha (α : ℝ) : ℝ := Real.logb 2 (theta α) / (1 - α)

theorem theta_pos {α : ℝ} (hα : 0 < α) : 0 < theta α := by unfold theta; positivity

/-! ### The envelope variable `Z` of a finite tree -/

variable (T : Tree)

def zval (i : ℕ) : ℝ := if h : i < (infoValues T).length then (infoValues T)[i] else 0

theorem zval_nonneg (i : ℕ) : 0 ≤ zval T i := by
  unfold zval; split_ifs with h
  · exact info_nonneg_get T h
  · exact le_rfl

theorem sum_envInc : ∑ i ∈ Finset.range (infoValues T).length, envInc T i = 1 := by
  rw [← cumsum_eq_sum, cumsum_envInc_last]

/-- `E 2^{λ Z}`. -/
def zMoment (l : ℝ) : ℝ := ∑ i ∈ Finset.range (infoValues T).length, envInc T i * (2:ℝ) ^ (l * zval T i)

/-- `R_α(Z)`. -/
def zRenyi (α : ℝ) : ℝ := Real.logb 2 (zMoment T (1 - α)) / (1 - α)

theorem zMoment_pos (l : ℝ) : 0 < zMoment T l := by
  obtain ⟨i, hi, hpos⟩ : ∃ i ∈ Finset.range (infoValues T).length, 0 < envInc T i := by
    by_contra h
    push_neg at h
    have := Finset.sum_nonpos h
    rw [sum_envInc] at this; linarith
  exact Finset.sum_pos' (fun i _ => mul_nonneg (envInc_nonneg T i) (by positivity))
    ⟨i, hi, mul_pos hpos (by positivity)⟩

theorem one_sub_Fstar_eq (t : ℝ) :
    1 - Fstar T t = ∑ i ∈ Finset.range (infoValues T).length, (if t < zval T i then envInc T i else 0) := by
  rw [one_sub_Fstar_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := Finset.mem_range.mp hi
  simp [envTail, zval, hi']

theorem zMoment_layer (l : ℝ) :
    IntegrableOn (fun t => gw l t * (1 - Fstar T t)) (Ioi 0) ∧
      zMoment T l = 1 + ∫ t in Ioi (0:ℝ), gw l t * (1 - Fstar T t) := by
  have h := finset_layer (Finset.range (infoValues T).length) l (envInc T) (zval T) (zval_nonneg T)
  simp_rw [← one_sub_Fstar_eq] at h
  refine ⟨h.1, ?_⟩
  rw [h.2, zMoment]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sum_envInc]; ring

theorem zw_layer {l : ℝ} (hl : l < 1) :
    IntegrableOn (fun t => gw l t * ∑ i ∈ Finset.range (infoValues T).length,
        envInc T i * wSurvival (t - zval T i)) (Ioi 0) ∧
      1 + ∫ t in Ioi (0:ℝ), gw l t * ∑ i ∈ Finset.range (infoValues T).length,
        envInc T i * wSurvival (t - zval T i) =
        (1 / 2 + (2:ℝ) ^ (l - 1) / (1 - l)) * zMoment T l := by
  simp_rw [Finset.mul_sum, show ∀ t i, gw l t * (envInc T i * wSurvival (t - zval T i)) =
    envInc T i * (gw l t * wSurvival (t - zval T i)) from fun t i => by ring]
  have hi := fun i => (w_layer hl (zval_nonneg T i))
  refine ⟨integrable_finset_sum _ fun i _ => (hi i).1.const_mul _, ?_⟩
  rw [integral_finset_sum _ fun i _ => (hi i).1.const_mul _]
  simp_rw [integral_const_mul, (hi _).2]
  unfold zMoment
  rw [Finset.mul_sum]
  have expand : ∑ i ∈ Finset.range (infoValues T).length, envInc T i *
      ((2:ℝ) ^ (l * zval T i) * (1 / 2 + (2:ℝ) ^ (l - 1) / (1 - l)) - 1) =
      ∑ i ∈ Finset.range (infoValues T).length, (1 / 2 + (2:ℝ) ^ (l - 1) / (1 - l)) *
        (envInc T i * (2:ℝ) ^ (l * zval T i)) -
      ∑ i ∈ Finset.range (infoValues T).length, envInc T i := by
    rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [expand, sum_envInc]; ring

/-! ### The seed -/

def seedMoment (l : ℝ) (atoms : List (Atom T)) : ℝ :=
  (atoms.map fun a => a.1 * (2:ℝ) ^ (l * infoMass a.1)).sum

theorem seed_layer (l : ℝ) : ∀ (atoms : List (Atom T)), (∀ a ∈ atoms, 0 < a.1 ∧ a.1 ≤ 1) →
    IntegrableOn (fun t => gw l t * seedTail atoms t) (Ioi 0) ∧
      seedMoment T l atoms = totalWeight atoms + ∫ t in Ioi (0:ℝ), gw l t * seedTail atoms t := by
  intro atoms
  induction atoms with
  | nil => intro _; simp [seedTail, seedMoment, totalWeight]
  | cons a tail ih =>
      intro h
      obtain ⟨i1, e1⟩ := ih fun b hb => h b (List.mem_cons_of_mem a hb)
      have hx : 0 ≤ infoMass a.1 := infoMass_nonneg_of_le (h a (by simp)).1 (h a (by simp)).2
      obtain ⟨i0, e0⟩ := atom_layer l hx a.1
      have hf : (fun t => gw l t * seedTail (a :: tail) t) =
          fun t => gw l t * (if t < infoMass a.1 then a.1 else 0) + gw l t * seedTail tail t := by
        funext t; rw [seedTail_cons]; ring
      rw [hf]
      refine ⟨i0.add i1, ?_⟩
      rw [integral_add i0 i1, e0]
      simp only [seedMoment, totalWeight, List.map_cons, List.sum_cons] at e1 ⊢
      rw [e1]; ring

/-- `∑ p^α` of the seed equals `E 2^{(1-α) J}`. -/
theorem seed_rpow_sum {α : ℝ} (hα : 0 < α) (atoms : List (Atom T))
    (h : ∀ a ∈ atoms, 0 < a.1) :
    (atoms.map fun a => a.1 ^ α).sum = seedMoment T (1 - α) atoms := by
  unfold seedMoment
  congr 1
  exact List.map_congr_left fun a ha => rpow_eq_moment hα (h a ha).le

def seedRenyi (α : ℝ) (atoms : List (Atom T)) : ℝ :=
  Real.logb 2 ((atoms.map fun a => a.1 ^ α).sum) / (1 - α)

/-! ### Ordinary sources -/

def coupMoment (l : ℝ) (Γ : Coupling T) : ℝ :=
  ∑ α, Γ.mass α * (2:ℝ) ^ (l * infoMass (Γ.mass α))

def coupRenyi (α : ℝ) (Γ : Coupling T) : ℝ :=
  Real.logb 2 (∑ a, Γ.mass a ^ α) / (1 - α)

theorem coup_layer (l : ℝ) (Γ : Coupling T) :
    IntegrableOn (fun t => gw l t * ∑ a, (if t < infoMass (Γ.mass a) then Γ.mass a else 0))
        (Ioi 0) ∧
      coupMoment T l Γ = 1 + ∫ t in Ioi (0:ℝ),
        gw l t * ∑ a, (if t < infoMass (Γ.mass a) then Γ.mass a else 0) := by
  have h := finset_layer Finset.univ l Γ.mass (fun a => infoMass (Γ.mass a))
    (fun a => by
      rcases eq_or_lt_of_le (Γ.nonneg a) with h | h
      · rw [← h]; simp [infoMass]
      · exact infoMass_nonneg_of_le h (mass_le_one Γ a))
  refine ⟨h.1, ?_⟩
  rw [h.2, coupMoment]
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, Γ.total]; ring

/-- `Z ≼st I_U`: the information tail of every ordinary exact source dominates. -/
theorem coup_tail_ge (Γ : Coupling T) (t : ℝ) :
    1 - Fstar T t ≤ ∑ a, (if t < infoMass (Γ.mass a) then Γ.mass a else 0) := by
  set π := envelopePolicy T t
  have h1 : 1 - Fstar T t =
      ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else 0) := by
    rw [policy_info_tail]; rfl
  rw [h1]
  calc ∑ ℓ : Leaf T, (if CompatiblePolicy ℓ π ∧ t < infoMass (leafMass ℓ) then leafMass ℓ else 0)
      = ∑ ℓ : Leaf T, ∑ a, (if (a π).1 = ℓ ∧ t < infoMass (leafMass ℓ) then Γ.mass a else 0) := by
        refine Finset.sum_congr rfl fun ℓ _ => ?_
        by_cases hc : CompatiblePolicy ℓ π
        · by_cases ht : t < infoMass (leafMass ℓ)
          · rw [if_pos ⟨hc, ht⟩]
            conv_lhs => rw [← Γ.marginal π ℓ hc]
            exact Finset.sum_congr rfl fun a _ => by
              split_ifs <;> first | rfl | (exfalso; tauto)
          · rw [if_neg (fun h => ht h.2)]
            exact (Finset.sum_eq_zero fun a _ => by
              split_ifs <;> first | rfl | (exfalso; tauto)).symm
        · rw [if_neg (fun h => hc h.1)]
          refine (Finset.sum_eq_zero fun a _ => ?_).symm
          rw [if_neg]; rintro ⟨h, -⟩; exact hc (h ▸ (a π).2)
    _ = ∑ a, (if t < infoMass (leafMass (a π).1) then Γ.mass a else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_eq_single (a π).1]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp
    _ ≤ _ := by
        refine Finset.sum_le_sum fun a _ => ?_
        by_cases hm : Γ.mass a = 0
        · simp [hm]
        have hpos : 0 < Γ.mass a := lt_of_le_of_ne (Γ.nonneg a) (Ne.symm hm)
        by_cases ht : t < infoMass (leafMass (a π).1)
        · rw [if_pos ht, if_pos]
          refine lt_of_lt_of_le ht ?_
          unfold infoMass
          have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos (mass_le_leaf Γ a π)
          linarith
        · rw [if_neg ht]; split_ifs <;> simp [Γ.nonneg a]

theorem coup_rpow_sum {α : ℝ} (hα : 0 < α) (Γ : Coupling T) :
    ∑ a, Γ.mass a ^ α = coupMoment T (1 - α) Γ :=
  Finset.sum_congr rfl fun a _ => rpow_eq_moment hα (Γ.nonneg a)

theorem coupMoment_pos (l : ℝ) (Γ : Coupling T) : 0 < coupMoment T l Γ := by
  obtain ⟨a, -, hpos⟩ : ∃ a ∈ Finset.univ, 0 < Γ.mass a := by
    by_contra h; push_neg at h
    have := Finset.sum_nonpos h; rw [Γ.total] at this; linarith
  exact Finset.sum_pos' (fun a _ => mul_nonneg (Γ.nonneg a) (by positivity))
    ⟨a, Finset.mem_univ _, mul_pos hpos (by positivity)⟩

/-! ### Dividing logarithms by `1 - α` -/

theorem div_bounds {α A B : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (hA : 0 < A) (hB : 0 < B)
    (hθ : 0 < theta α)
    (hlow : (0 < 1 - α → A ≤ B) ∧ (1 - α < 0 → B ≤ A))
    (hup : (0 < 1 - α → B ≤ theta α * A) ∧ (1 - α < 0 → theta α * A ≤ B)) :
    Real.logb 2 A / (1 - α) ≤ Real.logb 2 B / (1 - α) ∧
      Real.logb 2 B / (1 - α) ≤ Real.logb 2 A / (1 - α) + dAlpha α := by
  have hlog : ∀ {x y : ℝ}, 0 < x → x ≤ y → Real.logb 2 x ≤ Real.logb 2 y :=
    fun hx hxy => Real.logb_le_logb_of_le (by norm_num) hx hxy
  have hmul : Real.logb 2 (theta α * A) = Real.logb 2 (theta α) + Real.logb 2 A :=
    Real.logb_mul hθ.ne' hA.ne'
  unfold dAlpha
  rw [← add_div]
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr (Ne.symm hα1)) with h | h
  · -- `α > 1`
    have h1 := hlog hB (hlow.2 h)
    have h2 := hlog (mul_pos hθ hA) (hup.2 h)
    rw [hmul] at h2
    constructor
    · exact div_le_div_of_nonpos_of_le h.le h1
    · rw [add_comm]; exact div_le_div_of_nonpos_of_le h.le h2
  · have h1 := hlog hA (hlow.1 h)
    have h2 := hlog hB (hup.1 h)
    rw [hmul] at h2
    constructor
    · exact div_le_div_of_nonneg_right h1 h.le
    · rw [add_comm]; exact div_le_div_of_nonneg_right h2 h.le

/-! ### Main finite statements -/

theorem theta_eq {α : ℝ} : (1 / 2 + (2:ℝ) ^ ((1 - α) - 1) / (1 - (1 - α))) = theta α := by
  unfold theta; congr 2 <;> ring_nf

/-- **Every ordinary exact source** (any `Coupling`, history-consistent or not) has
`H_α(U) ≥ R_α(Z)` for every order `α > 0`, `α ≠ 1`. -/
theorem coupRenyi_ge {α : ℝ} (hα : 0 < α) (hα1 : α ≠ 1) (Γ : Coupling T) :
    zRenyi T α ≤ coupRenyi T α Γ := by
  have hl := zMoment_layer T (1 - α)
  have hc := coup_layer T (1 - α) Γ
  unfold zRenyi coupRenyi
  rw [coup_rpow_sum T hα]
  have hA := zMoment_pos T (1 - α)
  have hB := coupMoment_pos T (1 - α) Γ
  rcases lt_or_gt_of_ne (sub_ne_zero.mpr (Ne.symm hα1)) with h | h
  · have hle : coupMoment T (1 - α) Γ ≤ zMoment T (1 - α) := by
      rw [hl.2, hc.2]
      have := setIntegral_mono_on hc.1 hl.1 measurableSet_Ioi fun t _ =>
        mul_le_mul_of_nonpos_left (coup_tail_ge T Γ t) (gw_nonpos h.le t)
      linarith
    exact div_le_div_of_nonpos_of_le h.le (Real.logb_le_logb_of_le (by norm_num) hB hle)
  · have hle : zMoment T (1 - α) ≤ coupMoment T (1 - α) Γ := by
      rw [hl.2, hc.2]
      have := setIntegral_mono_on hl.1 hc.1 measurableSet_Ioi fun t _ =>
        mul_le_mul_of_nonneg_left (coup_tail_ge T Γ t) (gw_nonneg h.le t)
      linarith
    exact div_le_div_of_nonneg_right (Real.logb_le_logb_of_le (by norm_num) hA hle) h.le

/-- Exactness data of any greedy trace (as in `one_seed_shannon`). -/
theorem trace_data {T : Tree} {atoms : List (Atom T)} (ht : GreedyTrace (Field.p T) atoms) :
    (∀ a ∈ atoms, 0 < a.1) ∧ (∀ a ∈ atoms, a.1 ≤ 1) ∧ totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) := by
  have hbounds := greedy_atom_bounds ht
  obtain ⟨-, -, hsum, hrep⟩ :=
    greedyTrace_properties ht (Field.p_isFlow T) (Field.p_nonneg T)
  refine ⟨hbounds.1, hbounds.2, by simpa using hsum, fun π ℓ => ?_⟩
  rw [transcriptWeight_eq, hrep]
  have hp : leafValue (Field.p T) ℓ = leafMass ℓ := by
    simpa [Field.p] using leafValue_probability T 1 ℓ
  rw [hp]

/-- The upper tail of any greedy seed is dominated by that of `Z + W`. -/
theorem trace_tail_upper {T : Tree} {atoms : List (Atom T)} (ht : GreedyTrace (Field.p T) atoms)
    (t : ℝ) : seedTail atoms t ≤
      ∑ i ∈ Finset.range (infoValues T).length, envInc T i * wSurvival (t - zval T i) :=
  (seedTail_le_smallWeight atoms t (trace_data ht).1).trans (survival_le_wMixture ht t)

/-- Finite-horizon sandwich for an arbitrary greedy trace. -/
theorem sandwich_of_trace {T : Tree} {atoms : List (Atom T)} (ht : GreedyTrace (Field.p T) atoms)
    (α : ℝ) (hα : 0 < α) (hα1 : α ≠ 1) :
    zRenyi T α ≤ seedRenyi T α atoms ∧ seedRenyi T α atoms ≤ zRenyi T α + dAlpha α := by
  obtain ⟨hpos, hle, htot, hex⟩ := trace_data ht
  set l := 1 - α
  have hl1 : l < 1 := by simp only [l]; linarith
  obtain ⟨iz, ez⟩ := zMoment_layer T l
  obtain ⟨is, es⟩ := seed_layer T l atoms fun a ha => ⟨hpos a ha, hle a ha⟩
  obtain ⟨iw, ew⟩ := zw_layer T hl1
  rw [theta_eq] at ew
  rw [htot] at es
  -- tails
  have tlow : ∀ t, 1 - Fstar T t ≤ seedTail atoms t := fun t => by
    rw [← one_sub_seedCDF atoms t htot]; linarith [seedCDF_le_Fstar hex hpos t]
  have tup : ∀ t, seedTail atoms t ≤
      ∑ i ∈ Finset.range (infoValues T).length, envInc T i * wSurvival (t - zval T i) := fun t =>
    (seedTail_le_smallWeight atoms t hpos).trans (survival_le_wMixture ht t)
  have hB : 0 < seedMoment T l atoms := by
    rw [← seed_rpow_sum T hα atoms hpos]
    obtain ⟨a, ha⟩ : ∃ a, a ∈ atoms := by
      by_contra h; push_neg at h
      have : atoms = [] := List.eq_nil_iff_forall_not_mem.mpr h
      rw [this] at htot; simp [totalWeight] at htot
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos (hpos a ha) α) (List.single_le_sum (fun x hx => by
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx; exact (Real.rpow_pos_of_pos (hpos b hb) _).le)
      _ (List.mem_map.mpr ⟨a, ha, rfl⟩))
  have key := div_bounds hα hα1 (zMoment_pos T l) hB (theta_pos hα)
    ⟨fun h => by
      rw [ez, es]
      have := setIntegral_mono_on iz is measurableSet_Ioi fun t _ =>
        mul_le_mul_of_nonneg_left (tlow t) (gw_nonneg h.le t)
      linarith,
     fun h => by
      rw [ez, es]
      have := setIntegral_mono_on is iz measurableSet_Ioi fun t _ =>
        mul_le_mul_of_nonpos_left (tlow t) (gw_nonpos h.le t)
      linarith⟩
    ⟨fun h => by
      rw [← ew, es]
      have := setIntegral_mono_on is iw measurableSet_Ioi fun t _ =>
        mul_le_mul_of_nonneg_left (tup t) (gw_nonneg h.le t)
      linarith,
     fun h => by
      rw [← ew, es]
      have := setIntegral_mono_on iw is measurableSet_Ioi fun t _ =>
        mul_le_mul_of_nonpos_left (tup t) (gw_nonpos h.le t)
      linarith⟩
  unfold seedRenyi zRenyi
  rw [seed_rpow_sum T hα atoms hpos]
  exact key

/-- **Finite Rényi sandwich for one seed, all orders at once.** The greedy exact
causal seed of `one_seed_shannon` satisfies, for every `α > 0`, `α ≠ 1`,
`R_α(Z) ≤ H_α(seed) ≤ R_α(Z) + d_α`. -/
theorem seed_renyi_sandwich (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧ (∀ a ∈ atoms, 0 < a.1) ∧ totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      ∀ α : ℝ, 0 < α → α ≠ 1 →
        zRenyi T α ≤ seedRenyi T α atoms ∧ seedRenyi T α atoms ≤ zRenyi T α + dAlpha α := by
  obtain ⟨atoms, ht, hpos, htot, hex, -, -⟩ := one_seed_shannon T
  exact ⟨atoms, ht, hpos, htot, hex, fun α hα hα1 => sandwich_of_trace ht α hα hα1⟩

/-- **Corollary (finite horizon).** One greedy causal seed is within `d_α` of every
ordinary exact source, simultaneously for all `α > 0`, `α ≠ 1`; for `α = 1` the
constant is `c⋆` (`one_seed_shannon`, `entropy_ge_envelope`). -/
theorem seed_renyi_vs_ordinary (T : Tree) :
    ∃ atoms : List (Atom T),
      GreedyTrace (Field.p T) atoms ∧ (∀ a ∈ atoms, 0 < a.1) ∧ totalWeight atoms = 1 ∧
      (∀ (π : Policy T) (ℓ : Leaf T),
        transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) ∧
      (∀ α : ℝ, 0 < α → α ≠ 1 → ∀ Γ : Coupling T,
        seedRenyi T α atoms ≤ coupRenyi T α Γ + dAlpha α) ∧
      (∀ Γ : Coupling T, seedShannon atoms ≤ Γ.entropy + shannonOverhead) := by
  obtain ⟨atoms, ht, hpos, htot, hex, hR⟩ := seed_renyi_sandwich T
  refine ⟨atoms, ht, hpos, htot, hex, fun α hα hα1 Γ => ?_, fun Γ => ?_⟩
  · linarith [(hR α hα hα1).2, coupRenyi_ge T hα hα1 Γ]
  · linarith [seedShannon_le_envelope ht (greedy_atom_bounds ht).1 (greedy_atom_bounds ht).2,
      entropy_ge_envelope Γ]

theorem dAlpha_two : dAlpha 2 = Real.logb 2 (8 / 5) := by
  unfold dAlpha; exact gTilde_two

#print axioms seed_renyi_sandwich
#print axioms coupRenyi_ge
#print axioms seed_renyi_vs_ordinary

end CausalSpectrum.Renyi

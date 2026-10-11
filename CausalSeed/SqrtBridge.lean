/-
The mean identity (meanidentity) for a stationary kernel
with common entropy `h`, connecting the repository's `envelopeMean` of
`κ.rounds n` to the Bellman envelope `G_n` of the centered surprisal
increments `X_a = -log₂ K_a(Y) - h`.
-/
import CausalSeed.SqrtRate
import CausalSeed.EnvelopeBridge

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum
namespace Kernel

variable (κ : Kernel)

/-- The common binary entropy hypothesis: `H₂(K_a) = h` for every action. -/
def EqualEntropy (h : ℝ) : Prop := ∀ a, ∑ y, κ.K a y * infoMass (κ.K a y) = h

/-- Centered surprisal increments `X_a(y) = -log₂ K_a(y) - h`. -/
abbrev fam (h : ℝ) : Sqrt.IncFamily where
  nA := κ.nA
  hA := κ.hA
  nY := κ.nY
  hY := κ.hY
  P := κ.K
  Ppos := κ.Kpos
  Psum := κ.Ksum
  X := fun a y => infoMass (κ.K a y) - h

theorem fam_centered {h : ℝ} (hh : κ.EqualEntropy h) : (κ.fam h).Centered := by
  unfold Sqrt.IncFamily.Centered
  dsimp only [fam]
  intro a
  simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [hh a, κ.Ksum]; ring

theorem infoMass_mul {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    infoMass (p * q) = infoMass p + infoMass q := by
  unfold infoMass; rw [Real.logb_mul hp.ne' hq.ne']; ring

theorem infoMass_one : infoMass 1 = 0 := by simp [infoMass]

def toAPol (h : ℝ) : (n : ℕ) → Policy (κ.rounds n) → (κ.fam h).APol n
  | 0, _ => PUnit.unit
  | n + 1, π => ⟨π.1, fun y => toAPol h n (π.2 π.1 y)⟩

def ofAPol (h : ℝ) : (n : ℕ) → (κ.fam h).APol n → Policy (κ.rounds n)
  | 0, _ => PUnit.unit
  | n + 1, π => (π.1, fun a y =>
      if ha : a = π.1 then ofAPol h n (π.2 (ha ▸ y)) else defaultPolicy (κ.rounds n))

theorem toAPol_ofAPol (h : ℝ) : ∀ (n : ℕ) (π : (κ.fam h).APol n),
    κ.toAPol h n (κ.ofAPol h n π) = π
  | 0, _ => rfl
  | n + 1, π => by
    obtain ⟨j, k⟩ := π
    simp only [toAPol, ofAPol]
    congr 1
    funext y
    simp only [dite_true]
    exact toAPol_ofAPol h n (k y)

theorem policyCDF_eq (h : ℝ) : ∀ (n : ℕ) (π : Policy (κ.rounds n)) (t : ℝ),
    policyCDF (κ.rounds n) π t = (κ.fam h).cdfPol n (κ.toAPol h n π) (t - n * h)
  | 0, π, t => by
    simp only [Nat.cast_zero, zero_mul, sub_zero]
    show (if infoMass 1 ≤ t then (1:ℝ) else 0) = if 0 ≤ t then 1 else 0
    rw [infoMass_one]
  | n + 1, π, t => by
    show (∑ y, policySum (fun ℓ => if infoMass (κ.K π.1 y * leafMass ℓ) ≤ t then
        κ.K π.1 y * leafMass ℓ else 0) (π.2 π.1 y)) =
      ∑ y, κ.K π.1 y * (κ.fam h).cdfPol n (κ.toAPol h n (π.2 π.1 y))
        (t - ((n + 1 : ℕ) : ℝ) * h - (infoMass (κ.K π.1 y) - h))
    apply Finset.sum_congr rfl
    intro y _
    have hf : (fun ℓ : Leaf (κ.rounds n) => if infoMass (κ.K π.1 y * leafMass ℓ) ≤ t then
        κ.K π.1 y * leafMass ℓ else 0) = fun ℓ => κ.K π.1 y *
        (if infoMass (leafMass ℓ) ≤ t - infoMass (κ.K π.1 y) then leafMass ℓ else 0) := by
      funext ℓ
      rw [infoMass_mul (κ.Kpos _ _) (leafMass_pos ℓ)]
      by_cases hc : infoMass (κ.K π.1 y) + infoMass (leafMass ℓ) ≤ t
      · rw [if_pos hc, if_pos (by linarith)]
      · rw [if_neg hc, if_neg (by intro h'; apply hc; linarith), mul_zero]
    rw [hf, policySum_mul]
    have := policyCDF_eq h n (π.2 π.1 y) (t - infoMass (κ.K π.1 y))
    unfold policyCDF at this
    rw [this]
    congr 2
    push_cast; ring

/-- `F*_n(t) = G_n(t - n h)`: the repository's envelope is the Bellman envelope. -/
theorem Fstar_eq_G (h : ℝ) (n : ℕ) (t : ℝ) :
    Fstar (κ.rounds n) t = (κ.fam h).G n (t - n * h) := by
  apply le_antisymm
  · obtain ⟨π, hπ⟩ := ((κ.fam h).G_envelope n (t - n * h)).2
    have := Fstar_le (κ.rounds n) t (κ.ofAPol h n π)
    rw [κ.policyCDF_eq h, toAPol_ofAPol, hπ] at this
    exact this
  · unfold Fstar
    rw [κ.policyCDF_eq h]
    exact ((κ.fam h).G_envelope n _).1 _

theorem infoMass_K_nonneg (a : Fin κ.nA) (y : Fin (κ.nY a)) : 0 ≤ infoMass (κ.K a y) := by
  unfold infoMass
  have h1 : κ.K a y ≤ 1 := by
    have := Finset.single_le_sum (f := κ.K a) (fun y _ => (κ.Kpos a y).le) (Finset.mem_univ y)
    rw [κ.Ksum] at this; exact this
  have := Real.logb_nonpos (b := 2) (by norm_num) (κ.Kpos a y).le h1
  linarith

theorem X_ge (h : ℝ) (a : Fin (κ.fam h).nA) (y : Fin ((κ.fam h).nY a)) :
    -h ≤ (κ.fam h).X a y := by
  have := κ.infoMass_K_nonneg a y
  change -h ≤ infoMass (κ.K a y) - h
  linarith

/-- Surprisal is nonnegative, so `G_n = 0` below `-n h`. -/
theorem G_zero_below (h : ℝ) : ∀ (n : ℕ) (y : ℝ), y < -(n * h) → (κ.fam h).G n y = 0
  | 0, y, hy => by
    simp only [Sqrt.IncFamily.G]; rw [if_neg]; simp at hy; linarith
  | n + 1, y, hy => by
    apply le_antisymm _ (((κ.fam h).G_cdf (n + 1)).2.2.1 y).1
    refine ((κ.fam h).T_le _ y ⟨0, κ.hA⟩).trans (le_of_eq ?_)
    apply Finset.sum_eq_zero; intro k _
    rw [G_zero_below h n, mul_zero]
    have := κ.X_ge h ⟨0, κ.hA⟩ k
    push_cast at hy
    linarith

theorem entropy_nonneg {h : ℝ} (hh : κ.EqualEntropy h) : 0 ≤ h := by
  rw [← hh ⟨0, κ.hA⟩]
  exact Finset.sum_nonneg fun y _ => mul_nonneg (κ.Kpos _ _).le (κ.infoMass_K_nonneg _ y)

/-- Translation on a half-line. -/
theorem integral_Ioi_sub (g : ℝ → ℝ) (c : ℝ) :
    ∫ t in Ioi (0:ℝ), g (t - c) = ∫ y in Ioi (-c), g y := by
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have : (Ioi (0:ℝ)).indicator (fun t => g (t - c)) =
      fun t => (Ioi (-c)).indicator g (t - c) := by
    funext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (mem_Ioi.mpr ht), indicator_of_mem (mem_Ioi.mpr (by linarith))]
    · rw [indicator_of_notMem (by simpa using ht), indicator_of_notMem (by simp; linarith)]
  rw [this, integral_sub_right_eq_self]

/-- **Mean identity (meanidentity).** -/
theorem mean_identity {h : ℝ} (hh : κ.EqualEntropy h) {n : ℕ} (hn : 1 ≤ n) :
    (envelopeMean (κ.rounds n) - n * h) / Real.sqrt n = (κ.fam h).Mn n := by
  set F := κ.fam h
  have hc := κ.fam_centered hh
  have h0 := κ.entropy_nonneg hh
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  set c := (n : ℝ) * h
  have hc0 : 0 ≤ c := by positivity
  have hGb := fun z => (F.G_cdf n).2.2.1 z
  have hM := F.G_measurable n
  set f := fun y => 1 - F.G n y
  have hfm : Measurable f := measurable_const.sub hM
  -- integrability of `f` on `(-c, ∞)`, from the repository's integrability
  have hI := integrableOn_one_sub_Fstar (κ.rounds n)
  simp only [κ.Fstar_eq_G h] at hI
  have hind : (Ioi (0:ℝ)).indicator (fun t => f (t - c)) =
      fun t => (Ioi (-c)).indicator f (t - c) := by
    funext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (mem_Ioi.mpr ht), indicator_of_mem (mem_Ioi.mpr (by linarith))]
    · rw [indicator_of_notMem (by simpa using ht), indicator_of_notMem (by simp; linarith)]
  have iC : IntegrableOn f (Ioi (-c)) := by
    rw [← integrable_indicator_iff measurableSet_Ioi] at hI ⊢
    have h1 : Integrable (fun t => (Ioi (-c)).indicator f (t - c)) := by
      rw [← hind]; exact hI
    have := h1.comp_add_right c
    simpa using this
  have i0 : IntegrableOn f (Ioi 0) := iC.mono_set (Ioi_subset_Ioi (by linarith))
  have hmean : envelopeMean (κ.rounds n) = ∫ y in Ioi (-c), f y := by
    rw [← integral_one_sub_Fstar]
    simp only [κ.Fstar_eq_G h]
    exact integral_Ioi_sub f c
  -- split at `0`
  have hsplit : ∫ y in Ioi (-c), f y = (∫ y in Ioc (-c) 0, f y) + ∫ y in Ioi 0, f y := by
    rw [← Ioc_union_Ioi_eq_Ioi (show -c ≤ 0 by linarith)]
    exact setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (iC.mono_set Ioc_subset_Ioi_self) i0
  have hGi : IntervalIntegrable (F.G n) volume (-c) 0 := (F.G_cdf n).1.intervalIntegrable
  have hneg_int : ∫ y in Ioc (-c) 0, f y = c - ∫ y in (-c)..0, F.G n y := by
    rw [← intervalIntegral.integral_of_le (by linarith)]
    simp only [f]
    rw [intervalIntegral.integral_sub intervalIntegrable_const hGi]
    simp
  -- the negative tail
  have hzero : ∀ y ∈ Ioi c, F.G n (-y) = 0 := fun y hy =>
    κ.G_zero_below h n (-y) (by simp only [c] at hy; linarith [mem_Ioi.mp hy])
  have hGm : Measurable fun y => F.G n (-y) := hM.comp measurable_neg
  have iIoc : IntegrableOn (fun y => F.G n (-y)) (Ioc 0 c) := by
    refine Measure.integrableOn_of_bounded (M := 1) ?_ hGm.aestronglyMeasurable ?_
    · simp
    · exact ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hGb _).1]; exact (hGb _).2
  have iIoi : IntegrableOn (fun y => F.G n (-y)) (Ioi c) :=
    integrableOn_zero.congr_fun (fun y hy => (hzero y hy).symm) measurableSet_Ioi
  have hnegtail : ∫ y in Ioi (0:ℝ), F.G n (-y) = ∫ y in (-c)..0, F.G n y := by
    rw [← Ioc_union_Ioi_eq_Ioi hc0, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      iIoc iIoi, setIntegral_congr_fun measurableSet_Ioi hzero, integral_zero, add_zero,
      ← intervalIntegral.integral_of_le hc0, intervalIntegral.integral_comp_neg]
    simp
  -- scaling
  have hscale : ∀ g : ℝ → ℝ, ∫ x in Ioi (0:ℝ), g (x * Real.sqrt n) =
      (Real.sqrt n)⁻¹ * ∫ y in Ioi (0:ℝ), g y := by
    intro g
    rw [integral_comp_mul_right_Ioi g 0 hs, zero_mul, smul_eq_mul]
  have e1 : (∫ x in Ioi (0:ℝ), (1 - F.G n (x * Real.sqrt n))) =
      (Real.sqrt n)⁻¹ * ∫ y in Ioi (0:ℝ), f y := hscale f
  have e2 : (∫ x in Ioi (0:ℝ), F.G n (-(x * Real.sqrt n))) =
      (Real.sqrt n)⁻¹ * ∫ y in Ioi (0:ℝ), F.G n (-y) := hscale (fun y => F.G n (-y))
  unfold Sqrt.IncFamily.Mn
  rw [e1, e2, hnegtail, hmean, hsplit, hneg_int]
  field_simp
  ring

end Kernel
end CausalSpectrum

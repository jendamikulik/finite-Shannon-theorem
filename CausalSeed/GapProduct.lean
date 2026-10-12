/-
Product samples of one law: total mass, marginals of coordinate constraints, entropy,
and the Chernoff–Hoeffding bound for atoms of low information.
-/
import CausalSeed.CausalFloor

noncomputable section
open Classical Finset

namespace CausalSpectrum.Gap

variable {N : ℕ} (w : Fin N → ℝ)

/-- Weight of a product sample. -/
def prodW {p : ℕ} (x : Fin p → Fin N) : ℝ := ∏ t, w (x t)

theorem sum_prod_fun {p : ℕ} (g : Fin p → Fin N → ℝ) :
    ∑ x : Fin p → Fin N, ∏ t, g t (x t) = ∏ t, ∑ y, g t y := by
  rw [Finset.prod_univ_sum]; simp

variable {w}

theorem prodW_pos (hw : ∀ y, 0 < w y) {p} (x : Fin p → Fin N) : 0 < prodW w x :=
  prod_pos fun t _ => hw _

theorem sum_prodW (hs : ∑ y, w y = 1) (p : ℕ) : ∑ x : Fin p → Fin N, prodW w x = 1 := by
  unfold prodW; rw [sum_prod_fun (fun _ => w)]; simp [hs]

/-- Entropy of the product law. -/
theorem entropy_prodW (hw : ∀ y, 0 < w y) (hs : ∑ y, w y = 1) (p : ℕ) :
    ∑ x : Fin p → Fin N, Real.negMulLog (prodW w x) = p * ∑ y, Real.negMulLog (w y) := by
  set g : Fin p → Fin p → Fin N → ℝ := fun s t y => w y * (if t = s then -Real.log (w y) else 1)
  have e : ∀ x : Fin p → Fin N, Real.negMulLog (prodW w x) = ∑ s, ∏ t, g s t (x t) := by
    intro x
    have : ∀ s, ∏ t, g s t (x t) = prodW w x * -Real.log (w (x s)) := fun s => by
      simp only [g, prod_mul_distrib, prodW]
      rw [prod_ite_eq' univ s]; simp
    simp_rw [this, ← mul_sum]
    rw [Real.negMulLog, prodW, Real.log_prod (fun t _ => (hw _).ne')]
    simp only [sum_neg_distrib]; ring
  simp_rw [e]
  rw [sum_comm]
  have h2 : ∀ s, ∑ x : Fin p → Fin N, ∏ t, g s t (x t) = ∑ y, Real.negMulLog (w y) := by
    intro s
    rw [sum_prod_fun]
    have : ∀ t, ∑ y, g s t y = if t = s then ∑ y, Real.negMulLog (w y) else 1 := by
      intro t; by_cases h : t = s
      · simp only [g, h, if_true]; refine sum_congr rfl fun y _ => ?_; simp [Real.negMulLog]
      · simp [g, h, hs]
    simp_rw [this]
    rw [prod_ite_eq' univ s]; simp
  simp_rw [h2]; simp

/-- Marginal of a constraint on the first `r` coordinates. -/
theorem sum_prodW_prefix (hs : ∑ y, w y = 1) {p : ℕ} (P : Fin p → Fin N → Prop) :
    ∑ x : Fin p → Fin N, prodW w x * (if ∀ t, P t (x t) then 1 else 0) =
      ∏ t, ∑ y, w y * (if P t y then 1 else 0) := by
  rw [← sum_prod_fun]
  refine sum_congr rfl fun x _ => ?_
  rw [prodW, prod_mul_distrib]
  congr 1
  by_cases h : ∀ t, P t (x t)
  · rw [if_pos h]; exact (prod_eq_one fun t _ => if_pos (h t)).symm
  · rw [if_neg h]; push_neg at h
    obtain ⟨t, ht⟩ := h
    exact (prod_eq_zero (mem_univ t) (if_neg ht)).symm

/-- Entropy of one law in bits. -/
def Hb (w : Fin N → ℝ) : ℝ := ∑ y, w y * infoMass (w y)

/-- The one-action increment family `X(y) = H - info(y)`. -/
def fam1 (hN : 0 < N) (hw : ∀ y, 0 < w y) (hs : ∑ y, w y = 1) : Sqrt.IncFamily where
  nA := 1
  hA := one_pos
  nY := fun _ => N
  hY := fun _ => hN
  P := fun _ => w
  Ppos := fun _ => hw
  Psum := fun _ => hs
  X := fun _ y => Hb w - infoMass (w y)

theorem infoMass_prodW (hw : ∀ y, 0 < w y) {p} (x : Fin p → Fin N) :
    infoMass (prodW w x) = ∑ t, infoMass (w (x t)) := by
  simp only [infoMass, prodW, Real.logb, Real.log_prod (fun t _ => (hw _).ne'), sum_div,
    ← sum_neg_distrib]

/-- **Chernoff–Hoeffding.** The product law gives mass at most
`exp(-p δ² / (2 (M² + 1)))` to atoms whose information is below `p (H - δ)`. -/
theorem heavy_mass_le (hN : 0 < N) (hw : ∀ y, 0 < w y) (hs : ∑ y, w y = 1) (p : ℕ)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    ∑ x : Fin p → Fin N,
        prodW w x * (if infoMass (prodW w x) < p * (Hb w - δ) then 1 else 0) ≤
      Real.exp (-(p * δ ^ 2 / (2 * ((fam1 hN hw hs).M ^ 2 + 1)))) := by
  set F := fam1 hN hw hs
  set M := F.M
  set lam := δ / (M ^ 2 + 1)
  have hM1 : 0 < M ^ 2 + 1 := by positivity
  have hl : 0 ≤ lam := div_nonneg hδ hM1.le
  have hmean : ∑ y, F.P ⟨0, F.hA⟩ y * F.X ⟨0, F.hA⟩ y ≤ 0 := by
    show ∑ y, w y * (Hb w - infoMass (w y)) ≤ 0
    rw [show ∑ y, w y * (Hb w - infoMass (w y)) = (∑ y, w y) * Hb w - Hb w by
      simp only [mul_sub, sum_sub_distrib, ← sum_mul, Hb]]
    rw [hs]; simp
  have hmgf := F.step_mgf_le hmean hl
  simp only [F, fam1] at hmgf
  have hpt : ∀ x : Fin p → Fin N,
      prodW w x * (if infoMass (prodW w x) < p * (Hb w - δ) then 1 else 0) ≤
        Real.exp (-(lam * p * δ)) *
          ∏ t, (w (x t) * Real.exp (lam * (Hb w - infoMass (w (x t))))) := by
    intro x
    rw [prod_mul_distrib, ← Real.exp_sum, ← prodW]
    have hp := prodW_pos hw x
    split_ifs with h
    · rw [mul_one, mul_left_comm]
      refine le_mul_of_one_le_right hp.le ?_
      rw [← Real.exp_add, Real.one_le_exp_iff, ← mul_sum, sum_sub_distrib, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul, ← infoMass_prodW hw]
      nlinarith
    · rw [mul_zero]; positivity
  calc _ ≤ ∑ x : Fin p → Fin N, Real.exp (-(lam * p * δ)) *
          ∏ t, (w (x t) * Real.exp (lam * (Hb w - infoMass (w (x t))))) := sum_le_sum fun x _ => hpt x
    _ = Real.exp (-(lam * p * δ)) *
          (∑ y, w y * Real.exp (lam * (Hb w - infoMass (w y)))) ^ p := by
        rw [← mul_sum, sum_prod_fun (fun _ y => w y * Real.exp (lam * (Hb w - infoMass (w y))))]
        simp
    _ ≤ Real.exp (-(lam * p * δ)) * Real.exp (lam ^ 2 * M ^ 2 / 2) ^ p := by
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀
          (sum_nonneg fun y _ => mul_nonneg (hw y).le (Real.exp_pos _).le) hmgf p)
          (Real.exp_pos _).le
    _ = Real.exp (p * lam * (lam * M ^ 2 / 2 - δ)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]; ring_nf
    _ ≤ _ := by
        apply Real.exp_le_exp.2
        have hlM : lam * M ^ 2 ≤ δ := by
          rw [div_mul_eq_mul_div, div_le_iff₀ hM1]; nlinarith [sq_nonneg M]
        have : p * lam * (lam * M ^ 2 / 2 - δ) ≤ p * lam * (-(δ / 2)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
        refine this.trans (le_of_eq ?_)
        simp only [lam]; field_simp

end CausalSpectrum.Gap

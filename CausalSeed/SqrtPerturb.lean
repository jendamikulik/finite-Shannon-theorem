/-
The independent-noise perturbation `X_j + ε ξ`, and the
noise comparison (noisecompare), proved at the level of the Bellman recursion.
The controller of the perturbed system observes the pair `(y, ξ)`; the
"randomized policy" step of the note becomes plain averaging over `ξ`.
We prove the comparison with the sub-Gaussian error `exp(-η²/(2ε²))`, which
is sharper than (and implies) the note's Chebyshev error `ε²/η²`.
-/
import CausalSeed.SqrtRate

noncomputable section
open Classical Finset
namespace CausalSpectrum.Sqrt
namespace IncFamily
variable (F : IncFamily)

def sg (s : Fin 2) : ℝ := if s = 0 then 1 else -1

/-- The perturbed family: outcomes `(y, s) ∈ Fin (nY j) × Fin 2`. -/
abbrev perturb (ε : ℝ) : IncFamily where
  nA := F.nA
  hA := F.hA
  nY := fun j => F.nY j * 2
  hY := fun j => Nat.mul_pos (F.hY j) (by norm_num)
  P := fun j i => F.P j (finProdFinEquiv.symm i).1 / 2
  Ppos := fun j i => by have := F.Ppos j (finProdFinEquiv.symm i).1; positivity
  Psum := fun j => by
    rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Fin.sum_univ_two, add_halves]
    exact F.Psum j
  X := fun j i => F.X j (finProdFinEquiv.symm i).1 + ε * sg (finProdFinEquiv.symm i).2

theorem perturb_sum (ε : ℝ) (j : Fin F.nA) (g : Fin ((F.perturb ε).nY j) → ℝ) :
    ∑ i, g i = ∑ y, (g (finProdFinEquiv (y, 0)) + g (finProdFinEquiv (y, 1))) := by
  change ∑ i : Fin (F.nY j * 2), g i = _
  rw [← finProdFinEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]

theorem perturb_expect (ε : ℝ) (j : Fin F.nA) (f : ℝ → ℝ) (x : ℝ) :
    (F.perturb ε).expect j f x =
      ∑ y, F.P j y * ((f (x - F.X j y - ε) + f (x - F.X j y + ε)) / 2) := by
  unfold expect
  rw [F.perturb_sum ε j]
  apply Finset.sum_congr rfl; intro y _
  simp only [perturb, Equiv.symm_apply_apply, sg]
  norm_num
  ring_nf

/-- `Q_n(w) = P(w + ε N_n < 0)` for a simple random walk `N_n`, by recursion. -/
def Q (ε : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun w => if w < 0 then 1 else 0
  | n + 1 => fun w => (Q ε n (w + ε) + Q ε n (w - ε)) / 2

theorem Q_nonneg (ε : ℝ) : ∀ n w, 0 ≤ Q ε n w
  | 0, w => by simp only [Q]; split_ifs <;> norm_num
  | n + 1, w => by simp only [Q]; have := Q_nonneg ε n (w + ε); have := Q_nonneg ε n (w - ε); linarith

theorem Q_le_exp (ε : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) : ∀ n w,
    Q ε n w ≤ Real.exp (-(θ * w)) * Real.cosh (θ * ε) ^ n
  | 0, w => by
    simp only [Q, pow_zero, mul_one]
    split_ifs with h
    · exact Real.one_le_exp (by nlinarith)
    · exact (Real.exp_pos _).le
  | n + 1, w => by
    simp only [Q]
    have h1 := Q_le_exp ε hθ n (w + ε)
    have h2 := Q_le_exp ε hθ n (w - ε)
    have e : Real.exp (-(θ * w)) * Real.cosh (θ * ε) ^ (n + 1) =
        (Real.exp (-(θ * (w + ε))) * Real.cosh (θ * ε) ^ n +
          Real.exp (-(θ * (w - ε))) * Real.cosh (θ * ε) ^ n) / 2 := by
      rw [Real.cosh_eq, pow_succ]
      rw [show -(θ * (w + ε)) = -(θ * w) + -(θ * ε) by ring,
        show -(θ * (w - ε)) = -(θ * w) + θ * ε by ring, Real.exp_add, Real.exp_add]
      ring
    rw [e]; linarith

/-- Sub-Gaussian bound for `Q` at `w = η√n`. -/
theorem Q_le {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) {n : ℕ} (hn : 0 < n) :
    Q ε n (η * Real.sqrt n) ≤ Real.exp (-(η ^ 2 / (2 * ε ^ 2))) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  set θ := η / (ε ^ 2 * Real.sqrt n)
  have hθ : 0 ≤ θ := by positivity
  refine (Q_le_exp ε hθ n _).trans ?_
  have hc : Real.cosh (θ * ε) ^ n ≤ Real.exp (n * ((θ * ε) ^ 2 / 2)) :=
    calc Real.cosh (θ * ε) ^ n ≤ Real.exp ((θ * ε) ^ 2 / 2) ^ n :=
          pow_le_pow_left₀ (Real.cosh_pos _).le (Real.cosh_le_exp_half_sq _) n
      _ = _ := by rw [← Real.exp_nat_mul]
  refine (mul_le_mul_of_nonneg_left hc (Real.exp_pos _).le).trans (le_of_eq ?_)
  rw [← Real.exp_add]
  congr 1
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  simp only [θ]
  field_simp
  rw [hsq]; ring

/-- Upper noise comparison: `G_n(x) ≤ G^ε_n(x + w) + Q_n(w)`. -/
theorem noise_upper (ε : ℝ) : ∀ (n : ℕ) (x w : ℝ),
    F.G n x ≤ (F.perturb ε).G n (x + w) + Q ε n w
  | 0, x, w => by
    simp only [G, Q]
    split_ifs <;> first | (exfalso; simp only [not_le, not_lt] at *; linarith) | norm_num
  | n + 1, x, w => by
    obtain ⟨j, hj⟩ := (F.perturb ε).T_attained ((F.perturb ε).G n) (x + w)
    change F.T (F.G n) x ≤ (F.perturb ε).T ((F.perturb ε).G n) (x + w) + _
    rw [hj, F.perturb_expect ε j]
    refine (F.T_le _ x j).trans ?_
    unfold expect
    simp only [Q]
    have hQ : (Q ε n (w + ε) + Q ε n (w - ε)) / 2 =
        ∑ y, F.P j y * ((Q ε n (w - ε) + Q ε n (w + ε)) / 2) := by
      rw [← Finset.sum_mul, F.Psum]; ring
    rw [hQ, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro y _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (F.Ppos _ _).le
    have h1 := noise_upper ε n (x - F.X j y) (w - ε)
    have h2 := noise_upper ε n (x - F.X j y) (w + ε)
    rw [show x - F.X j y + (w - ε) = x + w - F.X j y - ε by ring] at h1
    rw [show x - F.X j y + (w + ε) = x + w - F.X j y + ε by ring] at h2
    linarith

/-- Lower noise comparison: `G^ε_n(x - w) ≤ G_n(x) + Q_n(w)`. -/
theorem noise_lower (ε : ℝ) : ∀ (n : ℕ) (x w : ℝ),
    (F.perturb ε).G n (x - w) ≤ F.G n x + Q ε n w
  | 0, x, w => by
    simp only [G, Q]
    split_ifs <;> first | (exfalso; simp only [not_le, not_lt] at *; linarith) | norm_num
  | n + 1, x, w => by
    obtain ⟨j, hj⟩ := F.T_attained (F.G n) x
    change (F.perturb ε).T ((F.perturb ε).G n) (x - w) ≤ F.T (F.G n) x + _
    rw [hj]
    refine ((F.perturb ε).T_le _ _ j).trans ?_
    rw [F.perturb_expect ε j]
    unfold expect
    simp only [Q]
    have hQ : (Q ε n (w + ε) + Q ε n (w - ε)) / 2 =
        ∑ y, F.P j y * ((Q ε n (w + ε) + Q ε n (w - ε)) / 2) := by
      rw [← Finset.sum_mul, F.Psum]; ring
    rw [hQ, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro y _
    rw [← mul_add]
    apply mul_le_mul_of_nonneg_left _ (F.Ppos _ _).le
    have h1 := noise_lower ε n (x - F.X j y) (w + ε)
    have h2 := noise_lower ε n (x - F.X j y) (w - ε)
    rw [show x - F.X j y - (w + ε) = x - w - F.X j y - ε by ring] at h1
    rw [show x - F.X j y - (w - ε) = x - w - F.X j y + ε by ring] at h2
    linarith

/-- **Noise comparison (noisecompare)**, with error `q = exp(-η²/(2ε²))`. -/
theorem noise_compare {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) {n : ℕ} (hn : 0 < n) (x : ℝ) :
    (F.perturb ε).G n ((x - η) * Real.sqrt n) - Real.exp (-(η ^ 2 / (2 * ε ^ 2))) ≤
        F.G n (x * Real.sqrt n) ∧
      F.G n (x * Real.sqrt n) ≤
        (F.perturb ε).G n ((x + η) * Real.sqrt n) + Real.exp (-(η ^ 2 / (2 * ε ^ 2))) := by
  have hq := Q_le hε hη hn
  constructor
  · have := F.noise_lower ε n (x * Real.sqrt n) (η * Real.sqrt n)
    rw [show x * Real.sqrt n - η * Real.sqrt n = (x - η) * Real.sqrt n by ring] at this
    linarith
  · have := F.noise_upper ε n (x * Real.sqrt n) (η * Real.sqrt n)
    rw [show x * Real.sqrt n + η * Real.sqrt n = (x + η) * Real.sqrt n by ring] at this
    linarith

/-! ### The perturbed family is centered with `σ_j'² = σ_j² + ε²` -/

theorem perturb_centered (hc : F.Centered) (ε : ℝ) : (F.perturb ε).Centered := by
  intro j
  rw [F.perturb_sum ε j]
  have := hc j
  simp only [perturb, Equiv.symm_apply_apply, sg]
  norm_num
  rw [← this]
  apply Finset.sum_congr rfl; intro y _; ring

theorem perturb_sig2 (ε : ℝ) (j : Fin F.nA) : (F.perturb ε).sig2 j = F.sig2 j + ε ^ 2 := by
  unfold sig2
  rw [F.perturb_sum ε j]
  simp only [perturb, Equiv.symm_apply_apply, sg]
  norm_num
  rw [show ε ^ 2 = ∑ y, F.P j y * ε ^ 2 by rw [← Finset.sum_mul, F.Psum, one_mul],
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro y _; ring

theorem perturb_sigma (ε : ℝ) (j : Fin F.nA) :
    (F.perturb ε).sigma j = Real.sqrt (F.sigma j ^ 2 + ε ^ 2) := by
  unfold sigma; rw [F.perturb_sig2, Real.sq_sqrt (F.sig2_nonneg j)]

theorem perturb_sB_pos {ε : ℝ} (hε : 0 < ε) : 0 < (F.perturb ε).sB := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' (F.perturb ε).univ_nonempty (F.perturb ε).sigma
  unfold sB; rw [hj, F.perturb_sigma]
  exact Real.sqrt_pos.mpr (by positivity)

theorem perturb_sA_bounds (ε : ℝ) :
    F.sA ≤ (F.perturb ε).sA ∧ (F.perturb ε).sA ≤ Real.sqrt (F.sA ^ 2 + ε ^ 2) := by
  constructor
  · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' F.univ_nonempty F.sigma
    unfold sA; rw [hj]
    refine le_trans ?_ ((F.perturb ε).sigma_le_sA j)
    rw [F.perturb_sigma]
    rw [show F.sigma j = Real.sqrt (F.sigma j ^ 2) from
      (Real.sqrt_sq (Real.sqrt_nonneg _)).symm]
    apply Real.sqrt_le_sqrt
    rw [Real.sq_sqrt (sq_nonneg _)]; nlinarith
  · apply Finset.sup'_le; intro j _
    rw [F.perturb_sigma]
    apply Real.sqrt_le_sqrt
    have h0 : 0 ≤ F.sigma j := Real.sqrt_nonneg _
    nlinarith [pow_le_pow_left₀ h0 (F.sigma_le_sA j) 2]

theorem perturb_sB_bounds (ε : ℝ) :
    (F.perturb ε).sB ≤ Real.sqrt (F.sB ^ 2 + ε ^ 2) := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_inf' F.univ_nonempty F.sigma
  refine ((F.perturb ε).sB_le_sigma j).trans (le_of_eq ?_)
  rw [F.perturb_sigma]
  unfold sB; rw [hj]

#print axioms noise_compare

end IncFamily
end CausalSpectrum.Sqrt

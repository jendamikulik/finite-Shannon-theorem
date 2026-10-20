/-
Conditional Hoeffding for adaptive policies, uniform in the
policy and in `n`:
`1 - G_n(x√n) ≤ exp(-x²/(2M²))` and `G_n(-x√n) ≤ exp(-x²/(2M²))`, `x > 0`.
Needs the increments to be centered (hypothesis `Centered`).
-/
import CausalSeed.Bellman
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

noncomputable section
open Classical Finset
namespace CausalSpectrum.Sqrt
namespace IncFamily
variable (F : IncFamily)

def Centered : Prop := ∀ j, ∑ y, F.P j y * F.X j y = 0

def mgfPol : (n : ℕ) → F.APol n → ℝ → ℝ
  | 0, _ => fun _ => 1
  | n + 1, π => fun θ => ∑ y, F.P π.1 y * Real.exp (θ * F.X π.1 y) * mgfPol n (π.2 y) θ

theorem mgfPol_nonneg : ∀ (n : ℕ) (π : F.APol n) (θ : ℝ), 0 ≤ F.mgfPol n π θ
  | 0, _, _ => zero_le_one
  | n + 1, π, θ => Finset.sum_nonneg fun y _ =>
      mul_nonneg (mul_nonneg (F.Ppos _ _).le (Real.exp_pos _).le) (mgfPol_nonneg n _ θ)

/-- Convexity: `e^{θx} ≤ cosh(θM) + (x/M) sinh(θM)` on `[-M, M]`. -/
theorem exp_le_chord {M x θ : ℝ} (hM : 0 < M) (hx : |x| ≤ M) :
    Real.exp (θ * x) ≤ Real.cosh (θ * M) + x / M * Real.sinh (θ * M) := by
  obtain ⟨h1, h2⟩ := abs_le.mp hx
  have hl : 0 ≤ (M - x) / (2 * M) := div_nonneg (by linarith) (by linarith)
  have hm : 0 ≤ (M + x) / (2 * M) := div_nonneg (by linarith) (by linarith)
  have hs : (M - x) / (2 * M) + (M + x) / (2 * M) = 1 := by field_simp; ring
  have := convexOn_exp.2 (Set.mem_univ (-(θ * M))) (Set.mem_univ (θ * M)) hl hm hs
  simp only [smul_eq_mul] at this
  have e : (M - x) / (2 * M) * -(θ * M) + (M + x) / (2 * M) * (θ * M) = θ * x := by
    field_simp; ring
  rw [e] at this
  refine this.trans (le_of_eq ?_)
  rw [Real.cosh_eq, Real.sinh_eq]
  field_simp
  ring

theorem step_mgf (hc : F.Centered) (j : Fin F.nA) (θ : ℝ) :
    ∑ y, F.P j y * Real.exp (θ * F.X j y) ≤ Real.exp (θ ^ 2 * F.M ^ 2 / 2) := by
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · have hx : ∀ y, F.X j y = 0 := fun y => abs_nonpos_iff.mp (h0 ▸ F.abs_X_le j y)
    simp [hx, F.Psum, ← h0]
  · calc ∑ y, F.P j y * Real.exp (θ * F.X j y)
        ≤ ∑ y, F.P j y * (Real.cosh (θ * F.M) + F.X j y / F.M * Real.sinh (θ * F.M)) :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (exp_le_chord hM (F.abs_X_le j y)) (F.Ppos _ _).le
      _ = Real.cosh (θ * F.M) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, F.Psum, one_mul]
          have : ∑ y, F.P j y * (F.X j y / F.M * Real.sinh (θ * F.M)) =
              (∑ y, F.P j y * F.X j y) / F.M * Real.sinh (θ * F.M) := by
            rw [Finset.sum_div, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro y _; ring
          rw [this, hc j]; simp
      _ ≤ Real.exp ((θ * F.M) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = _ := by ring_nf

theorem mgfPol_le (hc : F.Centered) : ∀ (n : ℕ) (π : F.APol n) (θ : ℝ),
    F.mgfPol n π θ ≤ Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2))
  | 0, _, _ => by simp [mgfPol]
  | n + 1, π, θ => by
    calc F.mgfPol (n + 1) π θ
        ≤ ∑ y, F.P π.1 y * Real.exp (θ * F.X π.1 y) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (mgfPol_le hc n _ θ)
            (mul_nonneg (F.Ppos _ _).le (Real.exp_pos _).le)
      _ = (∑ y, F.P π.1 y * Real.exp (θ * F.X π.1 y)) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) := by
          rw [Finset.sum_mul]
      _ ≤ Real.exp (θ ^ 2 * F.M ^ 2 / 2) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right (F.step_mgf hc π.1 θ) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf

/-- Chernoff, upper tail, for every adaptive policy. -/
theorem upper_chernoff : ∀ (n : ℕ) (π : F.APol n) (x θ : ℝ), 0 ≤ θ →
    1 - F.cdfPol n π x ≤ Real.exp (-(θ * x)) * F.mgfPol n π θ
  | 0, _, x, θ, hθ => by
    simp only [cdfPol, mgfPol, mul_one]
    split_ifs with h
    · simp [(Real.exp_pos _).le]
    · simp only [sub_zero]; apply Real.one_le_exp; nlinarith [not_le.mp h]
  | n + 1, π, x, θ, hθ => by
    simp only [cdfPol, mgfPol]
    have e : 1 - ∑ y, F.P π.1 y * F.cdfPol n (π.2 y) (x - F.X π.1 y) =
        ∑ y, F.P π.1 y * (1 - F.cdfPol n (π.2 y) (x - F.X π.1 y)) := by
      simp [mul_sub, Finset.sum_sub_distrib, F.Psum]
    rw [e, Finset.mul_sum]
    apply Finset.sum_le_sum; intro y _
    have := upper_chernoff n (π.2 y) (x - F.X π.1 y) θ hθ
    have hp := (F.Ppos π.1 y).le
    calc F.P π.1 y * (1 - F.cdfPol n (π.2 y) (x - F.X π.1 y))
        ≤ F.P π.1 y * (Real.exp (-(θ * (x - F.X π.1 y))) * F.mgfPol n (π.2 y) θ) :=
          mul_le_mul_of_nonneg_left this hp
      _ = _ := by
          rw [show -(θ * (x - F.X π.1 y)) = -(θ * x) + θ * F.X π.1 y by ring, Real.exp_add]
          ring

/-- Chernoff, lower tail. -/
theorem lower_chernoff : ∀ (n : ℕ) (π : F.APol n) (y θ : ℝ), 0 ≤ θ →
    F.cdfPol n π y ≤ Real.exp (θ * y) * F.mgfPol n π (-θ)
  | 0, _, y, θ, hθ => by
    simp only [cdfPol, mgfPol, mul_one]
    split_ifs with h
    · exact Real.one_le_exp (mul_nonneg hθ h)
    · exact (Real.exp_pos _).le
  | n + 1, π, y, θ, hθ => by
    simp only [cdfPol, mgfPol]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro k _
    have := lower_chernoff n (π.2 k) (y - F.X π.1 k) θ hθ
    have hp := (F.Ppos π.1 k).le
    calc F.P π.1 k * F.cdfPol n (π.2 k) (y - F.X π.1 k)
        ≤ F.P π.1 k * (Real.exp (θ * (y - F.X π.1 k)) * F.mgfPol n (π.2 k) (-θ)) :=
          mul_le_mul_of_nonneg_left this hp
      _ = _ := by
          rw [show θ * (y - F.X π.1 k) = θ * y + -θ * F.X π.1 k by ring, Real.exp_add]
          ring

theorem exponent_opt {n : ℕ} (hn : 0 < n) {M x : ℝ} (hM : 0 < M) :
    -(x / (M ^ 2 * Real.sqrt n) * (x * Real.sqrt n)) +
      n * ((x / (M ^ 2 * Real.sqrt n)) ^ 2 * M ^ 2 / 2) = -(x ^ 2 / (2 * M ^ 2)) := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hsq : Real.sqrt n ^ 2 = n := Real.sq_sqrt (by positivity)
  field_simp
  rw [hsq]; ring

/-- Uniform upper tail of the envelope. -/
theorem G_upper_tail (hc : F.Centered) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    1 - F.G n (x * Real.sqrt n) ≤ Real.exp (-(x ^ 2 / (2 * F.M ^ 2))) := by
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · rw [← h0]; simp; exact (F.G_cdf n).2.2.1 _ |>.1
  obtain ⟨π, hπ⟩ := (F.G_envelope n (x * Real.sqrt n)).2
  rw [← hπ]
  set θ := x / (F.M ^ 2 * Real.sqrt n)
  have hθ : 0 ≤ θ := by positivity
  refine (F.upper_chernoff n π _ θ hθ).trans ?_
  refine (mul_le_mul_of_nonneg_left (F.mgfPol_le hc n π θ) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, exponent_opt hn hM]

/-- Uniform lower tail of the envelope. -/
theorem G_lower_tail (hc : F.Centered) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    F.G n (-(x * Real.sqrt n)) ≤ Real.exp (-(x ^ 2 / (2 * F.M ^ 2))) := by
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · rw [← h0]; simp; exact (F.G_cdf n).2.2.1 _ |>.2
  refine ((F.G_envelope n _).1 (F.defaultPol n)).trans ?_
  set θ := x / (F.M ^ 2 * Real.sqrt n)
  have hθ : 0 ≤ θ := by positivity
  refine (F.lower_chernoff n _ _ θ hθ).trans ?_
  refine (mul_le_mul_of_nonneg_left (F.mgfPol_le hc n _ (-θ)) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, neg_sq, show θ * -(x * Real.sqrt n) = -(θ * (x * Real.sqrt n)) by ring,
    exponent_opt hn hM]

#print axioms G_upper_tail
#print axioms G_lower_tail

end IncFamily
end CausalSpectrum.Sqrt

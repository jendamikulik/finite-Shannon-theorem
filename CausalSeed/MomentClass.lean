/-
The square-root branch of the moment classification at equal entropy.

For a stationary kernel whose actions share the entropy `h`, let `a ≥ b` be the largest
and smallest information standard deviations. If `a > b` (the variances differ) the
excess `C_n - n h` is of exact order `√n`; if `a = b` it is `o(√n)`.
-/
import CausalSeed.SqrtGeneral

noncomputable section
open Filter Topology

namespace CausalSpectrum.Kernel
variable (κ : Kernel)

theorem sB_le_sA (h : ℝ) : (κ.fam h).sB ≤ (κ.fam h).sA :=
  (Finset.inf'_le _ (Finset.mem_univ ⟨0, κ.hA⟩)).trans (Finset.le_sup' _ (Finset.mem_univ _))

/-- **`Θ(√n)` when the variances differ.** -/
theorem excess_theta_sqrt {h : ℝ} (hh : κ.EqualEntropy h) (hab : (κ.fam h).sB < (κ.fam h).sA) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ n : ℕ in atTop,
      c₁ * Real.sqrt n ≤ κ.costBits n - n * h ∧ κ.costBits n - n * h ≤ c₂ * Real.sqrt n := by
  set c := secondOrderCoeff (κ.fam h).sA (κ.fam h).sB
  have hc : 0 < c := mul_pos (Real.sqrt_pos.mpr (by positivity)) (by linarith)
  have hT := κ.cost_tendsto hh
  refine ⟨c / 2, 2 * c, by linarith, by linarith, ?_⟩
  filter_upwards [hT.eventually (lt_mem_nhds (show c / 2 < c by linarith)),
    hT.eventually (gt_mem_nhds (show c < 2 * c by linarith)), eventually_ge_atTop 1]
    with n h1 h2 hn
  have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [lt_div_iff₀ hs] at h1
  rw [div_lt_iff₀ hs] at h2
  exact ⟨h1.le, h2.le⟩

/-- **`o(√n)` when the variances agree.** -/
theorem excess_little_o {h : ℝ} (hh : κ.EqualEntropy h) (hab : (κ.fam h).sA = (κ.fam h).sB) :
    Tendsto (fun n : ℕ => (κ.costBits n - n * h) / Real.sqrt n) atTop (𝓝 0) := by
  have := κ.cost_tendsto hh
  rwa [secondOrderCoeff, hab, sub_self, mul_zero] at this

end CausalSpectrum.Kernel

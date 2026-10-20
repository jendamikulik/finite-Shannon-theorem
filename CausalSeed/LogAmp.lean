/-
Stage 1 of the logarithmic-coefficient formalization: integrated amplification for functions
dominated by a `C¹` majorant, and its integrated stability and propagation forms.

If `|R| ≤ S` pointwise, where `S ∈ C¹` has a continuous integrable derivative and `S → 0`
at `-∞`, then `∫ U^n |R| ≤ ‖S‖₁ + ‖S'‖₁ w_n`. No regularity of `R` itself is needed, so
the residuals of the corrector (which contain a minimum over actions) and the initial
comparison functions (which contain an indicator) are covered once a smooth majorant is
exhibited.
-/
import CausalSeed.LogWidth

open Classical MeasureTheory Set Filter Topology Finset
open scoped ENNReal

namespace CausalSpectrum.Sqrt.IncFamily
variable (F : IncFamily)

theorem U_nonneg {g : ℝ → ℝ} (hg : ∀ x, 0 ≤ g x) : ∀ (n : ℕ) (x : ℝ), 0 ≤ F.U n g x
  | 0, x => hg x
  | n + 1, x => by
    refine le_trans ?_ (Finset.le_sup' (fun j => F.expect j (F.U n g) x)
      (Finset.mem_univ ⟨0, F.hA⟩))
    exact Finset.sum_nonneg fun y _ => mul_nonneg (F.Ppos _ _).le (U_nonneg hg n _)

/-- A `C¹` majorant: `S ≥ 0`, `S' ` continuous and integrable, `S → 0` at `-∞`. -/
structure Majorant (S S' : ℝ → ℝ) : Prop where
  deriv : ∀ y, HasDerivAt S (S' y) y
  cont : Continuous S'
  integ : Integrable S'
  lim : Tendsto S atBot (𝓝 0)
  nonneg : ∀ y, 0 ≤ S y

theorem Majorant.measurable {S S' : ℝ → ℝ} (h : Majorant S S') : Measurable S :=
  (continuous_iff_continuousAt.2 fun y => (h.deriv y).continuousAt).measurable

/-- **Amplification under a majorant.** If `|R| ≤ S` with `S` a `C¹` majorant, then
`∫ U^n |R| ≤ ‖S‖₁ + ‖S'‖₁ w_n`. -/
theorem amp_majorant {R S S' : ℝ → ℝ} (hS : Majorant S S') (hRS : ∀ x, |R x| ≤ S x) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (F.U n (fun y => |R y|) x) ≤
      (∫⁻ x, ‖S x‖ₑ) + (∫⁻ x, ‖S' x‖ₑ) * F.Wint n := by
  have e : (fun y => |S y|) = S := funext fun y => abs_of_nonneg (hS.nonneg y)
  refine le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal
    (F.U_mono (g := fun y => |S y|) (fun y => by rw [abs_of_nonneg (hS.nonneg y)]; exact hRS y)
      n x)) ?_
  exact F.amp_lintegral hS.deriv hS.cont hS.integ hS.lim n

/-- **Integrated stability.** If `|f - g| ≤ S` with `S` a `C¹` majorant, then
`‖T^n f - T^n g‖₁ ≤ ‖S‖₁ + ‖S'‖₁ w_n`. -/
theorem stability_lintegral {f g S S' : ℝ → ℝ} (hS : Majorant S S')
    (hfg : ∀ x, |f x - g x| ≤ S x) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |F.Tit n f x - F.Tit n g x| ≤
      (∫⁻ x, ‖S x‖ₑ) + (∫⁻ x, ‖S' x‖ₑ) * F.Wint n :=
  le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (F.abs_Tit_sub_le f g n x))
    (F.amp_majorant (R := fun y => f y - g y) hS hfg n)

/-- **Integrated propagation.** For profiles `u_j` whose residuals `u_{j+1} - T u_j` are
dominated by `C¹` majorants `S_j`,
`‖T^n u_0 - u_n‖₁ ≤ Σ_{j<n} (‖S_j‖₁ + ‖S_j'‖₁ w_{n-1-j})`. -/
theorem propagation_lintegral (u : ℕ → ℝ → ℝ) (S S' : ℕ → ℝ → ℝ)
    (hS : ∀ j, Majorant (S j) (S' j))
    (hR : ∀ j x, |u (j + 1) x - F.T (u j) x| ≤ S j x) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |F.Tit n (u 0) x - u n x| ≤
      ∑ j ∈ range n, ((∫⁻ x, ‖S j x‖ₑ) + (∫⁻ x, ‖S' j x‖ₑ) * F.Wint (n - 1 - j)) := by
  have hmeas : ∀ j, Measurable fun x => F.U (n - 1 - j) (fun y => S j y) x :=
    fun j => F.measurable_U (hS j).measurable _
  calc ∫⁻ x, ENNReal.ofReal |F.Tit n (u 0) x - u n x|
      ≤ ∫⁻ x, ∑ j ∈ range n, ENNReal.ofReal (F.U (n - 1 - j) (fun y => S j y) x) := by
        refine lintegral_mono fun x => ?_
        refine (ENNReal.ofReal_le_ofReal ((F.propagation u n x).trans
          (Finset.sum_le_sum fun j _ => F.U_mono (fun y => hR j y) _ x))).trans ?_
        exact ofReal_sum_le _ _
    _ = ∑ j ∈ range n, ∫⁻ x, ENNReal.ofReal (F.U (n - 1 - j) (fun y => S j y) x) :=
        lintegral_finsetSum _ fun j _ => (hmeas j).ennreal_ofReal
    _ ≤ _ := Finset.sum_le_sum fun j _ => by
        have h := F.amp_majorant (R := S j) (hS j)
          (fun x => (abs_of_nonneg ((hS j).nonneg x)).le) (n - 1 - j)
        simpa only [abs_of_nonneg ((hS j).nonneg _)] using h

end CausalSpectrum.Sqrt.IncFamily

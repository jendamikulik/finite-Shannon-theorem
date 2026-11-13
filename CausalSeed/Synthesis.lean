/-
Exact causal simulation and the limits of informational inference.

The synthesis of 13 November 2026. The finite-tree constant is already
proved; this module records the distinctions and the elementary bounds
that the note adds.

Proved here, with no sorry:

* the overhead constant is `(1 + log₂ e) / 2`;
* for `0 ≤ ε_t ≤ 1`, the product deficit is at most the sum;
* the information lower bound on the observation count is positive in
  the small-angle regime;
* a fair binary probe has one bit of Shannon entropy.

Not formalized: continuous Gaussian channels, Hilbert-space instruments,
gravitational geometry. Not claimed: that any of these select a physics,
or that hidden entropy is a horizon.
-/
import CausalSeed.Entropy
import CausalSeed.BellReadout

noncomputable section

open Real

namespace CausalSpectrum
namespace Synthesis

/-- The universal overhead of the finite-tree causal theorem. -/
def cStar : ℝ := shannonOverhead

theorem cStar_eq : cStar = (1 + 1 / log 2) / 2 := rfl

/-- `cStar = (1 + log₂ e) / 2`, since `log₂ e = 1 / ln 2`. -/
theorem cStar_is_half_one_plus_log2e :
    cStar = (1 + (log 2)⁻¹) / 2 := by
  simp [cStar, shannonOverhead]

/-! ### Adaptive stability -/

/-- A product of factors in `[0, 1]` is at most `1`. -/
theorem prod_le_one :
    ∀ (εs : List ℝ), (∀ ε ∈ εs, 0 ≤ ε) → (∀ ε ∈ εs, ε ≤ 1) →
      (εs.map (fun ε => 1 - ε)).prod ≤ 1 := by
  intro εs h0 h1
  induction εs with
  | nil => simp
  | cons ε εs ih =>
    simp only [List.map_cons, List.prod_cons]
    have hε0 : 0 ≤ ε := h0 ε (List.Mem.head _)
    have hε1 : ε ≤ 1 := h1 ε (List.Mem.head _)
    have hrest0 : ∀ δ ∈ εs, 0 ≤ δ := fun δ hd => h0 δ (List.Mem.tail _ hd)
    have hrest1 : ∀ δ ∈ εs, δ ≤ 1 := fun δ hd => h1 δ (List.Mem.tail _ hd)
    have ih' := ih hrest0 hrest1
    have hfac : 0 ≤ 1 - ε := by linarith
    nlinarith

/-- For a finite list of factors in `[0, 1]`, the product deficit is
at most the sum. This is the numerical content of the stability bound. -/
theorem product_deficit :
    ∀ (εs : List ℝ),
      (∀ ε ∈ εs, 0 ≤ ε) → (∀ ε ∈ εs, ε ≤ 1) →
      1 - (εs.map (fun ε => 1 - ε)).prod ≤ εs.sum := by
  intro εs
  induction εs with
  | nil => intro _ _; simp
  | cons ε εs ih =>
    intro h0 h1
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hε0 : 0 ≤ ε := h0 ε (List.Mem.head _)
    have hε1 : ε ≤ 1 := h1 ε (List.Mem.head _)
    have hrest0 : ∀ δ ∈ εs, 0 ≤ δ := fun δ hd => h0 δ (List.Mem.tail _ hd)
    have hrest1 : ∀ δ ∈ εs, δ ≤ 1 := fun δ hd => h1 δ (List.Mem.tail _ hd)
    have ih' := ih hrest0 hrest1
    have hP0 : 0 ≤ (εs.map (fun δ => 1 - δ)).prod := by
      apply List.prod_nonneg
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨δ, hd, rfl⟩ := hx
      linarith [hrest0 δ hd, hrest1 δ hd]
    have hP1 := prod_le_one εs hrest0 hrest1
    nlinarith

/-- The stability bound: product form ≤ sum. -/
theorem stability_bound (εs : List ℝ)
    (h0 : ∀ ε ∈ εs, 0 ≤ ε) (h1 : ∀ ε ∈ εs, ε ≤ 1) :
    1 - (εs.map (fun ε => 1 - ε)).prod ≤ εs.sum :=
  product_deficit εs h0 h1

/-! ### Revelation time scale -/

/-- In the small-angle regime the information bound forces a lower
count of this order. -/
def revelationLower (η σ ε : ℝ) : ℝ :=
  (2 * η * log 2) * (σ / ε) ^ ((2 : ℝ) / 3)

theorem revelation_lower_pos {η σ ε : ℝ}
    (hη : 0 < η) (hσ : 0 < σ) (hε : 0 < ε) :
    0 < revelationLower η σ ε := by
  unfold revelationLower
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hratio : 0 < σ / ε := div_pos hσ hε
  have hpow : 0 < (σ / ε) ^ ((2 : ℝ) / 3) := Real.rpow_pos_of_pos hratio _
  positivity

/-! ### Open choice on a fixed sheet -/

/-- A fair binary probe has one bit of Shannon entropy. -/
theorem fair_probe : BellReadout.h2 (2⁻¹) = 1 := by
  rw [BellReadout.h2, Real.binEntropy_two_inv]
  field_simp [Real.log_pos (by norm_num : (1 : ℝ) < 2)]

end Synthesis
end CausalSpectrum

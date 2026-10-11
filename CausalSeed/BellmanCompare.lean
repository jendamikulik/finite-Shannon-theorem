/-
Stage 3 (order part): propagation of two translated barriers through `T^n`.
This is the operator-theoretic core of Lemma "Explicit CDF comparison":
it uses only monotonicity, translation, constants and a per-step defect
bound. The analytic input (the one-step defect of the explicit profile) is a
hypothesis here.
-/
import CausalSeed.Bellman

noncomputable section
open Classical Finset
namespace CausalSpectrum.Sqrt
namespace IncFamily
variable (F : IncFamily)

theorem T_shift_sub (f : ℝ → ℝ) (d c x : ℝ) :
    F.T (fun z => f (z - d) - c) x = F.T f (x - d) - c := by
  have h1 := F.T_add_const (fun z => f (z - d)) (-c) x
  have h2 := F.T_translate f (-d) x
  simp only [sub_eq_add_neg] at h1 h2 ⊢
  rw [h1, h2]

theorem barrier_propagation {u : ℝ → ℝ → ℝ} {e : ℝ → ℝ} (m d δ : ℝ)
    (hdef : ∀ k : ℕ, ∀ x, |F.T (u (m + k)) x - u (m + k + 1) x| ≤ e (m + k))
    (hlo : ∀ x, u m (x - d) - δ ≤ F.G 0 x) (hhi : ∀ x, F.G 0 x ≤ u m (x + d) + δ) :
    ∀ (n : ℕ) (x : ℝ),
      u (m + n) (x - d) - δ - ∑ k ∈ range n, e (m + k) ≤ F.G n x ∧
      F.G n x ≤ u (m + n) (x + d) + δ + ∑ k ∈ range n, e (m + k) := by
  intro n
  induction n with
  | zero => intro x; simp only [Nat.cast_zero, add_zero, Finset.range_zero, Finset.sum_empty, sub_zero]; exact ⟨hlo x, hhi x⟩
  | succ n ih =>
    intro x
    set E := ∑ k ∈ range n, e (m + k)
    have hc : (m + ((n + 1 : ℕ) : ℝ)) = m + n + 1 := by push_cast; ring
    rw [hc, Finset.sum_range_succ]
    constructor
    · have h1 := F.T_mono (fun z => (ih z).1) x
      have hl : F.T (fun z => u (m + n) (z - d) - δ - E) x =
          F.T (u (m + n)) (x - d) - (δ + E) := by
        rw [← F.T_shift_sub]; congr 1; funext z; ring
      rw [hl] at h1
      have h2 := (abs_le.mp (hdef n (x - d))).1
      change _ ≤ F.T (F.G n) x
      linarith
    · have h1 := F.T_mono (fun z => (ih z).2) x
      have hl : F.T (fun z => u (m + n) (z + d) + δ + E) x =
          F.T (u (m + n)) (x + d) + (δ + E) := by
        have := F.T_shift_sub (u (m + n)) (-d) (-(δ + E)) x
        simp only [sub_neg_eq_add] at this
        rw [← this]; congr 1; funext z; ring
      rw [hl] at h1
      have h2 := (abs_le.mp (hdef n (x + d))).2
      change F.T (F.G n) x ≤ _
      linarith

#print axioms barrier_propagation

end IncFamily
end CausalSpectrum.Sqrt

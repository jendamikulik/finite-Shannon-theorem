/-
Geometry is the picture, not the cause.

The map `s ↦ 1 - conj s` is an involution. Its fixed set is the line
`re = 1/2`. Any finite set of points closed under the map, counted with
multiplicity, has
`N - N₀ = 2 N₊`.
The difference is nonnegative and even. If it is strictly less than `2`,
it is zero. Four and six have the same parity and are not equal, so the
congruence seen by going once around a circle is weaker than equality.
The factor `π` is a choice of scale on a drawing. It does not appear in
the count.

Not proved: that the zero set of Riemann's `ξ` has `N₊ = 0`. Mathlib
records `Λ(1 - s) = Λ(s)` for the completed zeta function. That identity
is not used here, and it is not the Riemann hypothesis.
-/

import Mathlib.Basic.Complex.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Star.Basic
import Mathlib.Tactic

noncomputable section

namespace CausalSpectrum
namespace Mirror

def mirror (s : ℂ) : ℂ := 1 - star s

theorem mirror_involution (s : ℂ) : mirror (mirror s) = s := by
  simp [mirror]

theorem mirror_injective : Function.Injective mirror :=
  Function.Involutive.injective mirror_involution

theorem mirror_re (s : ℂ) : (mirror s).re = 1 - s.re := by
  simp [mirror, Complex.sub_re, Complex.one_re, Complex.conj_re]

theorem mirror_im (s : ℂ) : (mirror s).im = s.im := by
  simp [mirror, Complex.sub_im, Complex.one_im, Complex.conj_im]

/-- A horizontal strip is mirror-invariant because the map preserves height. -/
theorem strip_invariant (T : ℝ) (s : ℂ) :
    (0 < s.im ∧ s.im ≤ T) ↔ (0 < (mirror s).im ∧ (mirror s).im ≤ T) := by
  rw [mirror_im]

theorem fixed_iff (s : ℂ) : mirror s = s ↔ s.re = 1 / 2 := by
  constructor
  · intro h
    have hr : (mirror s).re = s.re := congrArg Complex.re h
    rw [mirror_re] at hr
    linarith
  · intro h
    apply Complex.ext
    · rw [mirror_re, h]
      norm_num
    · rw [mirror_im]

theorem zeros_closed {f : ℂ → ℂ} (h : ∀ s, f (mirror s) = star (f s)) {ρ : ℂ}
    (hρ : f ρ = 0) : f (mirror ρ) = 0 := by
  rw [h, hρ, star_zero]

def axis (S : Finset ℂ) : Finset ℂ := S.filter fun s => s.re = 1 / 2

def right (S : Finset ℂ) : Finset ℂ := S.filter fun s => (1 / 2 : ℝ) < s.re

def left (S : Finset ℂ) : Finset ℂ := S.filter fun s => s.re < 1 / 2

theorem left_card (S : Finset ℂ) (hS : ∀ s ∈ S, mirror s ∈ S) :
    (left S).card = (right S).card := by
  refine Finset.card_bij (fun s _ => mirror s) ?mem ?inj ?surj
  · intro s hs
    simp only [left, right, Finset.mem_filter] at hs ⊢
    refine ⟨hS s hs.1, ?_⟩
    rw [mirror_re]
    linarith
  · intro s₁ _ s₂ _ h
    exact mirror_injective h
  · intro t ht
    simp only [right, Finset.mem_filter] at ht
    refine ⟨mirror t, ?_, mirror_involution t⟩
    simp only [left, Finset.mem_filter]
    refine ⟨hS t ht.1, ?_⟩
    rw [mirror_re]
    linarith

theorem card_split (S : Finset ℂ) :
    S.card = (left S).card + (axis S).card + (right S).card := by
  classical
  have hdisj₁ : Disjoint (left S) (axis S) := by
    rw [Finset.disjoint_left]
    intro s hs ha
    simp only [left, axis, Finset.mem_filter] at hs ha
    linarith
  have hdisj₂ : Disjoint (left S ∪ axis S) (right S) := by
    rw [Finset.disjoint_left]
    intro s hs hr
    simp only [left, axis, right, Finset.mem_union, Finset.mem_filter] at hs hr
    rcases hs with hs | hs <;> linarith
  have hcover : left S ∪ axis S ∪ right S = S := by
    ext s
    constructor
    · intro hs
      simp only [left, axis, right, Finset.mem_union, Finset.mem_filter] at hs
      rcases hs with (hs | hs) | hs <;> exact hs.1
    · intro hs
      simp only [left, axis, right, Finset.mem_union, Finset.mem_filter]
      rcases lt_trichotomy s.re (1 / 2) with h | h | h
      · exact Or.inl (Or.inl ⟨hs, h⟩)
      · exact Or.inl (Or.inr ⟨hs, h⟩)
      · exact Or.inr ⟨hs, h⟩
  calc
    S.card = (left S ∪ axis S ∪ right S).card := by rw [hcover]
    _ = (left S ∪ axis S).card + (right S).card := Finset.card_union_of_disjoint hdisj₂
    _ = (left S).card + (axis S).card + (right S).card := by
      rw [Finset.card_union_of_disjoint hdisj₁]

/-- Off the axis the points come in mirror pairs, counted without multiplicity. -/
theorem excess (S : Finset ℂ) (hS : ∀ s ∈ S, mirror s ∈ S) :
    S.card - (axis S).card = 2 * (right S).card := by
  have hsplit := card_split S
  rw [left_card S hS] at hsplit
  have : S.card = 2 * (right S).card + (axis S).card := by omega
  rw [this, Nat.add_sub_cancel]

theorem excess_even (S : Finset ℂ) (hS : ∀ s ∈ S, mirror s ∈ S) :
    Even (S.card - (axis S).card) := by
  rw [excess S hS]
  exact even_two_mul _

theorem excess_lt_two (S : Finset ℂ) (hS : ∀ s ∈ S, mirror s ∈ S)
    (h : S.card - (axis S).card < 2) : S.card = (axis S).card := by
  have hex := excess S hS
  rw [excess S hS] at h
  have h0 : (right S).card = 0 := by omega
  rw [h0, mul_zero] at hex
  have hle : S.card ≤ (axis S).card := Nat.sub_eq_zero_iff_le.mp hex
  exact le_antisymm hle (Finset.card_filter_le S _)

/-- Same parity is not equality. The circle only saw the first. -/
theorem four_six : (4 : ℕ) % 2 = (6 : ℕ) % 2 ∧ (4 : ℕ) ≠ 6 := by
  decide

def N (μ : ℂ → ℕ) (S : Finset ℂ) : ℕ := ∑ s ∈ S, μ s

def Nplus (μ : ℂ → ℕ) (S : Finset ℂ) : ℕ := ∑ s ∈ right S, μ s

def Naxis (μ : ℂ → ℕ) (S : Finset ℂ) : ℕ := ∑ s ∈ axis S, μ s

theorem weighted_pair (μ : ℂ → ℕ) (S : Finset ℂ) (hS : ∀ s ∈ S, mirror s ∈ S)
    (hμ : ∀ s, μ (mirror s) = μ s) :
    ∑ s ∈ left S, μ s = ∑ s ∈ right S, μ s := by
  refine Finset.sum_bij (fun s _ => mirror s) ?mem ?inj ?surj ?weight
  · intro s hs
    simp only [left, right, Finset.mem_filter] at hs ⊢
    refine ⟨hS s hs.1, ?_⟩
    rw [mirror_re]
    linarith
  · intro s₁ _ s₂ _ h
    exact mirror_injective h
  · intro t ht
    simp only [right, Finset.mem_filter] at ht
    refine ⟨mirror t, ?_, mirror_involution t⟩
    simp only [left, Finset.mem_filter]
    refine ⟨hS t ht.1, ?_⟩
    rw [mirror_re]
    linarith
  · intro s _
    exact (hμ s).symm

theorem weighted_split (μ : ℂ → ℕ) (S : Finset ℂ) :
    N μ S = (∑ s ∈ left S, μ s) + Naxis μ S + Nplus μ S := by
  classical
  have hdisj₁ : Disjoint (left S) (axis S) := by
    rw [Finset.disjoint_left]
    intro s hs ha
    simp only [left, axis, Finset.mem_filter] at hs ha
    linarith
  have hdisj₂ : Disjoint (left S ∪ axis S) (right S) := by
    rw [Finset.disjoint_left]
    intro s hs hr
    simp only [left, axis, right, Finset.mem_union, Finset.mem_filter] at hs hr
    rcases hs with hs | hs <;> linarith
  have hcover : left S ∪ axis S ∪ right S = S := by
    ext s
    constructor
    · intro hs
      simp only [left, axis, right, Finset.mem_union, Finset.mem_filter] at hs
      rcases hs with (hs | hs) | hs <;> exact hs.1
    · intro hs
      simp only [left, axis, right, Finset.mem_union, Finset.mem_filter]
      rcases lt_trichotomy s.re (1 / 2) with h | h | h
      · exact Or.inl (Or.inl ⟨hs, h⟩)
      · exact Or.inl (Or.inr ⟨hs, h⟩)
      · exact Or.inr ⟨hs, h⟩
  unfold N Naxis Nplus
  calc
    ∑ s ∈ S, μ s = ∑ s ∈ left S ∪ axis S ∪ right S, μ s := by rw [hcover]
    _ = (∑ s ∈ left S ∪ axis S, μ s) + ∑ s ∈ right S, μ s :=
      Finset.sum_union hdisj₂
    _ = (∑ s ∈ left S, μ s) + ∑ s ∈ axis S, μ s + ∑ s ∈ right S, μ s := by
      rw [Finset.sum_union hdisj₁]

/-- With multiplicity: `N - N₀ = 2 N₊`. -/
theorem weighted_excess (μ : ℂ → ℕ) (S : Finset ℂ) (hS : ∀ s ∈ S, mirror s ∈ S)
    (hμ : ∀ s, μ (mirror s) = μ s) :
    N μ S - Naxis μ S = 2 * Nplus μ S := by
  have hsplit := weighted_split μ S
  rw [weighted_pair μ S hS hμ] at hsplit
  have : N μ S = 2 * Nplus μ S + Naxis μ S := by
    unfold Nplus at *
    omega
  rw [this, Nat.add_sub_cancel]

end Mirror
end CausalSpectrum

end

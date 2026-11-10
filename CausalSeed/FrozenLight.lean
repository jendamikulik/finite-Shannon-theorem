/-
Frozen light, two grooves. 10 November 2026.

Bohm's dye drop is an image: a whole prepared in advance, from which a later
motion unfolds one appearance. Here the whole is a finite seed and the motion
is which groove is played. The frozen rule is the decoder. The needle is not
a bit of the seed.

Proved, with no sorry:

* one shared fair bit, read by both grooves, has entropy `1`;
* two independent fair bits, one per groove, have entropy `2`;
* under either record, each groove alone is a fair bit;
* so equal single-groove laws do not determine the entropy of the whole,
  and the shared record uses half the entropy of the product;
* any finite seed whose left groove is a fair bit has entropy at least `1`;
* on the shared record the grooves agree on every atom; on the product they
  agree on mass `1/2`, and the off-diagonal joints differ;
* the two-friend tree of `ManyFriends.lean` attains the same one bit:
  `L(T) = C(T) = 1`.

Not proved: that this whole is Bohm's implicate order; that the finite causal
Shannon theorem is only a reinterpretation of that image; that free will is
this entropy; that a tachyon, an electron, or a worldline is a seed. The
image of unfolding does not determine `L(T)`. The sandwich
`L ≤ C ≤ L + (1 + log₂ e) / 2` remains the greedy theorem in `Entropy.lean`.
-/

import CausalSeed.ManyFriends
import CausalSeed.QuestionStructure

noncomputable section

open Classical Finset

namespace CausalSpectrum
namespace FrozenLight

/-- One fair bit. Both grooves read it. -/
def Shared : Fin 2 → ℝ := fun _ => 1 / 2

def leftShared : Fin 2 → Fin 2 := id

def rightShared : Fin 2 → Fin 2 := id

/-- Two independent fair bits, one per groove. -/
def Product : Fin 2 × Fin 2 → ℝ := fun _ => 1 / 4

def leftProduct : Fin 2 × Fin 2 → Fin 2 := Prod.fst

def rightProduct : Fin 2 × Fin 2 → Fin 2 := Prod.snd

theorem infoMass_quarter : infoMass ((1 : ℝ) / 4) = 2 := by
  unfold infoMass
  have hlogb : Real.logb 2 ((1 : ℝ) / 4) = -2 := by
    rw [Real.logb]
    have hlog : Real.log ((1 : ℝ) / 4) = -Real.log 4 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hlog]
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [h4]
    field_simp
  rw [hlogb]
  norm_num

theorem shared_entropy : pmfEntropy Shared = 1 := by
  unfold pmfEntropy
  have hterm : ∀ b : Fin 2, entTerm (Shared b) = (1 / 2 : ℝ) := by
    intro b
    rw [show Shared b = (1 : ℝ) / 2 by rfl,
      entTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 2), ManyFriends.infoMass_half]
    norm_num
  rw [Finset.sum_congr rfl fun b _ => hterm b]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  norm_num

theorem product_entropy : pmfEntropy Product = 2 := by
  unfold pmfEntropy
  have hterm : ∀ p : Fin 2 × Fin 2, entTerm (Product p) = (1 / 2 : ℝ) := by
    intro p
    have hp : Product p = 1 / 4 := by rfl
    rw [hp, entTerm_of_pos (by norm_num : (0 : ℝ) < 1 / 4), infoMass_quarter]
    norm_num
  rw [Finset.sum_congr rfl fun p _ => hterm p]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]
  norm_num

theorem shared_left (b : Fin 2) :
    (∑ a : Fin 2, if leftShared a = b then Shared a else 0) = 1 / 2 := by
  fin_cases b <;> simp [leftShared, Shared]

theorem shared_right (r : Fin 2) :
    (∑ a : Fin 2, if rightShared a = r then Shared a else 0) = 1 / 2 :=
  shared_left r

theorem product_left (b : Fin 2) :
    (∑ p : Fin 2 × Fin 2, if leftProduct p = b then Product p else 0) = 1 / 2 := by
  rw [Fintype.sum_prod_type]
  fin_cases b <;> simp [leftProduct, Product] <;> norm_num

theorem product_right (r : Fin 2) :
    (∑ p : Fin 2 × Fin 2, if rightProduct p = r then Product p else 0) = 1 / 2 := by
  rw [Fintype.sum_prod_type]
  fin_cases r <;> simp [rightProduct, Product] <;> norm_num

/-- Same groove, same atom: one bit, one answer. -/
theorem shared_agrees (a : Fin 2) : leftShared a = rightShared a := rfl

theorem product_agree_mass :
    (∑ p : Fin 2 × Fin 2, if leftProduct p = rightProduct p then Product p else 0) =
      1 / 2 := by
  rw [Fintype.sum_prod_type]
  simp [leftProduct, rightProduct, Product]
  norm_num

theorem shared_joint (b r : Fin 2) :
    (∑ a : Fin 2, if leftShared a = b ∧ rightShared a = r then Shared a else 0) =
      if b = r then (1 : ℝ) / 2 else 0 := by
  fin_cases b <;> fin_cases r <;>
    simp [leftShared, rightShared, Shared, Fin.sum_univ_two]

theorem product_joint (b r : Fin 2) :
    (∑ p : Fin 2 × Fin 2,
        if leftProduct p = b ∧ rightProduct p = r then Product p else 0) =
      1 / 4 := by
  rw [Fintype.sum_prod_type]
  fin_cases b <;> fin_cases r <;>
    simp [leftProduct, rightProduct, Product, Fin.sum_univ_two]

/-- The law of one groove does not see which record is on the spindle. -/
theorem same_grooves_different_wholes :
    (∀ b, (∑ a, if leftShared a = b then Shared a else 0) =
        ∑ p, if leftProduct p = b then Product p else 0) ∧
      (∀ r, (∑ a, if rightShared a = r then Shared a else 0) =
          ∑ p, if rightProduct p = r then Product p else 0) ∧
        pmfEntropy Shared = 1 ∧ pmfEntropy Product = 2 := by
  refine ⟨?_, ?_, shared_entropy, product_entropy⟩
  · intro b
    rw [shared_left, product_left]
  · intro r
    rw [shared_right, product_right]

theorem half_the_entropy : pmfEntropy Shared * 2 = pmfEntropy Product := by
  rw [shared_entropy, product_entropy]
  norm_num

theorem not_determined_by_unfolding : pmfEntropy Shared ≠ pmfEntropy Product := by
  rw [shared_entropy, product_entropy]
  norm_num

theorem joints_differ :
    (∑ a, if leftShared a = 0 ∧ rightShared a = 1 then Shared a else 0) ≠
      ∑ p, if leftProduct p = 0 ∧ rightProduct p = 1 then Product p else 0 := by
  rw [shared_joint, product_joint]
  norm_num

/-- A fair groove is a deterministic function of the seed, so one bit is least. -/
theorem one_bit_is_least {α : Type} [Fintype α] (μ : α → ℝ) (h0 : ∀ a, 0 ≤ μ a)
    (φ : α → Fin 2)
    (hfair : ∀ b, (∑ a, if φ a = b then μ a else 0) = 1 / 2) :
    1 ≤ pmfEntropy μ := by
  have h := QuestionStructure.uniform_seed_entropy (α := α) (n := 2)
    (by decide : 0 < 2) μ h0 φ ?_
  · simpa [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h
  · intro b
    simpa using hfair b

theorem shared_attains_the_least :
    pmfEntropy Shared = 1 ∧
      ∀ b, (∑ a, if leftShared a = b then Shared a else 0) = 1 / 2 :=
  ⟨shared_entropy, shared_left⟩

/-- The two-friend tree is this shared toss: one bit, and not less. -/
theorem friends_attain_the_bit :
    envelopeMean ManyFriends.friends = 1 ∧ causalMin ManyFriends.friends = 1 :=
  ⟨ManyFriends.sharp.1, ManyFriends.sharp.2.1⟩

end FrozenLight
end CausalSpectrum

end

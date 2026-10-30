/-
Logic and nonsense, and the dream that stays.

`LogicNonsense` is the two-point symmetry from the note.
`true` is logic, `false` is nonsense. The involution swaps them.
The projection onto the symmetric direction is the average.
The antisymmetric direction is the kernel.

What is proved:

* the swap is an involution;
* the projection is idempotent and kills the difference;
* the symmetric vector is fixed, the antisymmetric vector is sent to zero.

What is not proved:

* that the labels are propositions;
* that a constant observation implies a constant state;
* that an invariant is existence.

The dream half is `DreamStay.remains`: an admitted step lands in care,
so a trajectory of admitted steps stays in care. Existence of an
admission is assumed.
-/
import CausalSeed.RecordDream

noncomputable section

namespace CausalSpectrum
namespace LogicNonsense

/-- `true` is logic, `false` is nonsense. -/
abbrev Basis := Bool

/-- The involution: logic and nonsense exchange places. -/
def swap (f : Basis → ℝ) : Basis → ℝ
  | true => f false
  | false => f true

theorem swap_involution (f : Basis → ℝ) : swap (swap f) = f := by
  funext b
  cases b <;> rfl

/-- The symmetric projection: the average of a vector and its swap. -/
def proj (f : Basis → ℝ) : Basis → ℝ :=
  fun b => (f b + swap f b) / 2

theorem proj_idem (f : Basis → ℝ) : proj (proj f) = proj f := by
  funext b
  cases b <;> simp [proj, swap] <;> ring

/-- The symmetric direction. Both basis vectors contribute equally. -/
def psiPlus : Basis → ℝ
  | true => 1 / Real.sqrt 2
  | false => 1 / Real.sqrt 2

/-- The antisymmetric direction. The disagreement. -/
def psiMinus : Basis → ℝ
  | true => 1 / Real.sqrt 2
  | false => -(1 / Real.sqrt 2)

theorem proj_fixes_plus : proj psiPlus = psiPlus := by
  funext b
  cases b <;> simp [proj, swap, psiPlus]

theorem proj_kills_minus : proj psiMinus = 0 := by
  funext b
  cases b <;> simp [proj, swap, psiMinus]

/-- A constant observation does not force a constant state.
The projection of `psiMinus` is zero; the vector itself is not. -/
theorem hidden_disagreement : proj psiMinus = 0 ∧ psiMinus ≠ 0 := by
  constructor
  · exact proj_kills_minus
  · intro h
    have htrue := congrFun h true
    simp only [psiMinus] at htrue
    have hne : (1 : ℝ) / Real.sqrt 2 ≠ 0 := by
      apply div_ne_zero
      · norm_num
      · exact ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2))
    exact hne htrue

end LogicNonsense
end CausalSpectrum

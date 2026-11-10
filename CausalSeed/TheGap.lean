/-
The gap between the action and the reaction.

At a node the policy has already chosen an action. The reply is already a
cell of the seed. It is not yet an argument of the continuation, so the
next action is not yet a value.

Proved, with no sorry:

* on every node, the action written into the transcript is the policy's
  action, and the reply is the seed's cell at that action;
* those two equations can hold together: the reply is a function of the
  seed, and the kernel remains the law of that cell;
* the continuation is a function of the reply, so the rule can be fixed
  before the reply arrives and still not determine the next action;
* on the two-friend tree one such rule sends each reply to a different
  next action, and the transcript follows it;
* a certain reply contributes no bit to the information clock. The clock
  has no argument for how long the reply took.

Not proved: that the gap has a duration; that a certain reply arrives in
an hour; that the action is metaphysically past or the reply future.
-/

import CausalSeed.LetItBe
import CausalSeed.ManyFriends

noncomputable section

open Classical

namespace CausalSpectrum
namespace TheGap

/-- At a node the action comes from the policy and the reply from the seed. -/
theorem split_at_the_node
    {nA : ℕ} {hA : 0 < nA} {nY : Fin nA → ℕ} {hY : ∀ a, 0 < nY a}
    {K : (a : Fin nA) → Fin (nY a) → ℝ}
    {Kpos : ∀ a y, 0 < K a y} {Ksum : ∀ a, ∑ y, K a y = 1}
    {child : (a : Fin nA) → Fin (nY a) → Tree}
    (d : Strategy (.node nA hA nY hY K Kpos Ksum child))
    (π : Policy (.node nA hA nY hY K Kpos Ksum child)) :
    (run d π).1 = π.1 ∧ (run d π).2.1 = d.1 π.1 := by
  constructor <;> rfl

/-- One listener. The next action is whatever reply just arrived. -/
def listener : Policy ManyFriends.friends :=
  ⟨0, fun _ y => ⟨y, fun _ _ => PUnit.unit⟩⟩

theorem rule_before_the_reply (y : Fin 2) : (listener.2 0 y).1 = y := rfl

theorem two_replies_two_questions :
    (listener.2 0 0).1 ≠ (listener.2 0 1).1 := by
  simp [listener]

/-- The reply is already determined by the cell, and the next action uses it. -/
theorem received_then_asked (d : Strategy ManyFriends.friends) :
    (run d listener).1 = 0 ∧
      (run d listener).2.1 = d.1 0 ∧
        (run d listener).2.2.1 = d.1 0 := by
  refine ⟨rfl, rfl, ?_⟩
  rfl

theorem certain_reply_is_silent : infoMass 1 = 0 := by
  simp [infoMass, Real.logb_one]

theorem clock_has_no_duration (C : LetItBe.Clock) : C.d 1 = 0 :=
  LetItBe.certain_step C

end TheGap
end CausalSpectrum

end

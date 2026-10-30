/-
One note, two claims, neither of which is an existence theorem.

`DreamStay` is the consent-and-care step. An admitted action lands in
the care predicate by definition. If the initial state is cared for and
every later action is admitted, every state on the trajectory is cared
for. Nonemptiness of the admitted set is an assumption, not a theorem.

`Record` is the finite classical shadow of an idealized two-outcome
measurement. The entropy of the record is binary entropy. Reading the
same record again has conditional entropy zero, because the copy is a
function of the record (`ImmersionGap`, via `condEntropy_of_dependent`).

Not proved:

* that a shared modulus produces a shared step;
* that an admitted action exists;
* the operator `M(ρ)` or why one particular outcome occurs;
* that `H(C | C) = 0` removes every uncertainty about the system;
* a definition of love.
-/
import CausalSeed.ImmersionGap

namespace CausalSpectrum
namespace DreamStay

structure Model (X A : Type) where
  care : X → Prop
  admit : X → A → Prop
  step : X → A → X
  lands : ∀ x a, admit x a → care (step x a)

def traj {X A : Type} (M : Model X A) (x0 : X) (α : ℕ → A) : ℕ → X
  | 0 => x0
  | n + 1 => M.step (traj M x0 α n) (α n)

theorem remains {X A : Type} (M : Model X A) (x0 : X) (α : ℕ → A)
    (h0 : M.care x0)
    (hadm : ∀ t, M.admit (traj M x0 α t) (α t)) :
    ∀ t, M.care (traj M x0 α t) := by
  intro t
  cases t with
  | zero => simpa [traj] using h0
  | succ t => simpa [traj] using M.lands _ _ (hadm t)

end DreamStay

namespace Record

open Sharing

/-- Outcome law of a two-point record, `Pr(true) = p`. -/
def outcomeLaw (p : ℝ) : Bool → ℝ := bernoulli p

theorem entropy_of_record {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    H (outcomeLaw p) = binEntropy p := by
  simpa [outcomeLaw] using ImmersionGap.entropy_of_future h0 h1

/-- After the record is read, the entropy of that same record is zero.
The copy is a function of the record. This is not a claim about the
residual state of the measured system. -/
theorem entropy_after_reading {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    condEntropy (ImmersionGap.joint p) = 0 :=
  ImmersionGap.entropy_given_state h0 h1

theorem record_gap {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    H (outcomeLaw p) = binEntropy p ∧
      condEntropy (ImmersionGap.joint p) = 0 :=
  ⟨entropy_of_record h0 h1, entropy_after_reading h0 h1⟩

end Record
end CausalSpectrum

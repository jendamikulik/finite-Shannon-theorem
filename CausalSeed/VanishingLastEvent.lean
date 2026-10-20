/-
Last-event entropy for finite independent Bernoulli experiments.

Probabilities are listed NEWEST FIRST. `lastLaw p` lists the probabilities
that the last success is at each listed time, followed by the no-success atom.
All statements allow zero and unit probabilities.

UNCOMPILED DRAFT: written against the repository's Vanishing.lean, blob
f753b2d079823908cb3ac7e09dc63338e92e414c. No Lean installation was performed.
This module does not assert the infinite-horizon causal simulation theorem.
-/
import CausalSeed.Vanishing
import Mathlib.Tactic

noncomputable section
namespace Vanishing.LastEvent

def Valid (p : List ℝ) : Prop := ∀ x ∈ p, 0 ≤ x ∧ x ≤ 1

def entropy (w : List ℝ) : ℝ := (w.map shannonTerm).sum

def fullEntropy (p : List ℝ) : ℝ := (p.map h2).sum

def lastLaw : List ℝ → List ℝ
  | [] => [1]
  | p :: ps => p :: (lastLaw ps).map (fun w => (1 - p) * w)

/-- Each success case is paired with the entropy of the older experiments.
The no-success case contributes zero and is omitted. -/
def successCases : List ℝ → List (ℝ × ℝ)
  | [] => []
  | p :: ps => (p, fullEntropy ps) ::
      (successCases ps).map (fun z => ((1 - p) * z.1, z.2))

def hiddenEntropy (p : List ℝ) : ℝ :=
  ((successCases p).map (fun z => z.1 * z.2)).sum

theorem shannonTerm_zero : shannonTerm 0 = 0 := by
  simp [shannonTerm]

theorem shannonTerm_one : shannonTerm 1 = 0 := by
  simp [shannonTerm]

theorem shannonTerm_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    shannonTerm (a * b) = b * shannonTerm a + a * shannonTerm b := by
  by_cases ha0 : a = 0
  · simp [ha0, shannonTerm_zero]
  by_cases hb0 : b = 0
  · simp [hb0, shannonTerm_zero]
  have hap : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hbp : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  rw [shannonTerm_of_pos (mul_pos hap hbp), shannonTerm_of_pos hap,
    shannonTerm_of_pos hbp, Real.logb_mul ha0 hb0]
  ring

theorem sum_scale (c : ℝ) (w : List ℝ) :
    (w.map (fun x => c * x)).sum = c * w.sum := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons, List.sum_cons, ih]; ring

theorem entropy_scale {c : ℝ} (hc : 0 ≤ c) (w : List ℝ)
    (hw : ∀ x ∈ w, 0 ≤ x) :
    entropy (w.map (fun x => c * x)) =
      w.sum * shannonTerm c + c * entropy w := by
  induction w with
  | nil => simp [entropy]
  | cons a w ih =>
    have ha : 0 ≤ a := hw a (by simp)
    have ht : ∀ x ∈ w, 0 ≤ x := fun x hx => hw x (by simp [hx])
    have hi := ih ht
    simp only [List.map_cons, entropy, List.sum_cons] at hi ⊢
    rw [shannonTerm_mul hc ha, hi]
    ring

theorem lastLaw_sum (p : List ℝ) : (lastLaw p).sum = 1 := by
  induction p with
  | nil => simp [lastLaw]
  | cons a p ih =>
    simp only [lastLaw, List.sum_cons, sum_scale, ih]
    ring

theorem lastLaw_nonneg (p : List ℝ) (hp : Valid p) :
    ∀ w ∈ lastLaw p, 0 ≤ w := by
  induction p with
  | nil => simp [lastLaw]
  | cons a p ih =>
    have ha := hp a (by simp)
    have ht : Valid p := fun x hx => hp x (by simp [hx])
    intro w hw
    simp only [lastLaw, List.mem_cons, List.mem_map] at hw
    rcases hw with rfl | ⟨v, hv, rfl⟩
    · exact ha.1
    · exact mul_nonneg (sub_nonneg.mpr ha.2) (ih ht v hv)

theorem lastEntropy_cons {a : ℝ} {p : List ℝ} (hp : Valid (a :: p)) :
    entropy (lastLaw (a :: p)) = h2 a + (1 - a) * entropy (lastLaw p) := by
  have ha := hp a (by simp)
  have ht : Valid p := fun x hx => hp x (by simp [hx])
  change shannonTerm a + entropy ((lastLaw p).map (fun w => (1-a)*w)) = _
  rw [entropy_scale (sub_nonneg.mpr ha.2) _ (lastLaw_nonneg p ht), lastLaw_sum]
  simp [h2, add_assoc]

theorem hiddenEntropy_cons (a : ℝ) (p : List ℝ) :
    hiddenEntropy (a :: p) =
      a * fullEntropy p + (1 - a) * hiddenEntropy p := by
  unfold hiddenEntropy
  simp only [successCases, List.map_cons, List.sum_cons, List.map_map]
  congr 1
  calc
    _ = (((successCases p).map (fun z => z.1 * z.2)).map
        (fun x => (1 - a) * x)).sum := by
      simp only [List.map_map]
      apply congrArg List.sum
      apply congrArg (fun f : ℝ × ℝ → ℝ => List.map f (successCases p))
      funext z
      change ((1 - a) * z.1) * z.2 = (1 - a) * (z.1 * z.2)
      ring
    _ = _ := sum_scale _ _

/-- The exact finite last-event information identity. The right side is the
explicit sum of (last-success probability) × (entropy of older trials). -/
theorem last_event_identity (p : List ℝ) (hp : Valid p) :
    fullEntropy p - entropy (lastLaw p) = hiddenEntropy p := by
  induction p with
  | nil => simp [fullEntropy, entropy, lastLaw, hiddenEntropy, successCases,
      shannonTerm_one]
  | cons a p ih =>
    have ht : Valid p := fun x hx => hp x (by simp [hx])
    have hi := ih ht
    rw [lastEntropy_cons hp, hiddenEntropy_cons]
    change h2 a + fullEntropy p -
      (h2 a + (1-a)*entropy (lastLaw p)) =
      a * fullEntropy p + (1-a)*hiddenEntropy p
    rw [← hi]
    ring

/-- Algebraic transfer from a causal entropy sandwich to the last-event cost.
The two cost inequalities are explicit hypotheses, not hidden axioms.
This is NOT a proof of that sandwich for a controlled tree. -/
theorem cost_last_event_bounds (p : List ℝ) (hp : Valid p)
    (C R : ℝ) (hlower : fullEntropy p ≤ C)
    (hupper : C ≤ fullEntropy p + R) :
    hiddenEntropy p ≤ C - entropy (lastLaw p) ∧
      C - entropy (lastLaw p) ≤ hiddenEntropy p + R := by
  have hi := last_event_identity p hp
  constructor <;> linarith

end Vanishing.LastEvent

/-
One seed, two friends. 6 November 2026.

The tree is one shared fair question, then two private actions whose
output is the constant zero. A strategy answers the shared question
once, so both friends receive that answer.

Proved here, with no sorry:

* every terminal transcript has mass `1/2` and surprisal `1`, so the
  envelope is `L(T) = 1`;
* two atoms of mass `1/2`, answering `0` and `1`, are an exact causal
  seed of entropy `1`, hence `C(T) = 1` and the ordinary minimum is `1`;
* every strategy gives the two friends the same first bit;
* the anti-correlated pair has both prescribed marginals and is not the
  run of any strategy.

Not proved: anything about electrons or worldlines; that this sharpness
holds for an arbitrary tree. The general overhead
`(1 + log₂ e) / 2` is the greedy theorem already in `Entropy.lean`.
It is not used here, and it does not follow from coupling the two
terminal laws. The anti-correlated pairing is a realizability
obstruction, not a cheaper coupling: nothing here has entropy below `1`.
-/

import CausalSeed.Penalty

noncomputable section

open Classical

namespace CausalSpectrum
namespace ManyFriends

def halfK : Fin 1 → Fin 2 → ℝ := fun _ _ => 1 / 2

theorem halfK_pos (a : Fin 1) (y : Fin 2) : 0 < halfK a y := by
  simp only [halfK]
  norm_num

theorem halfK_sum (a : Fin 1) : ∑ y : Fin 2, halfK a y = 1 := by
  simp only [halfK, Fin.sum_univ_two]
  norm_num

/-- After the shared bit: two actions, one deterministic output. -/
def after : Tree :=
  .node 2 (Nat.succ_pos 1) (fun _ => 1) (fun _ => Nat.one_pos)
    (fun _ _ => 1) (fun _ _ => zero_lt_one)
    (fun _ => by simp [Fin.sum_univ_one])
    (fun _ _ => .leaf)

/-- One shared fair question, then the private node. -/
def friends : Tree :=
  .node 1 (Nat.succ_pos 0) (fun _ => 2) (fun _ => Nat.succ_pos 1)
    halfK halfK_pos halfK_sum
    (fun _ _ => after)

def quiet : Strategy after :=
  (fun _ => ⟨0, Nat.one_pos⟩, fun _ _ => PUnit.unit)

def reply (b : Fin 2) : Strategy friends :=
  (fun _ => b, fun _ _ => quiet)

/-- The first friend. After the shared bit, the next action is `0`. -/
def friendA : Policy friends :=
  ⟨0, fun _ _ => ⟨0, fun _ _ => PUnit.unit⟩⟩

/-- The second friend. After the shared bit, the next action is `1`. -/
def friendB : Policy friends :=
  ⟨0, fun _ _ => ⟨1, fun _ _ => PUnit.unit⟩⟩

/-- Transcript with shared reply `y` and private action `b`. -/
def leafOf (y b : Fin 2) : Leaf friends :=
  ⟨0, y, ⟨b, ⟨0, Nat.one_pos⟩, PUnit.unit⟩⟩

def firstBit (ℓ : Leaf friends) : Fin 2 := ℓ.2.1

theorem pi1 (π : Policy friends) : π.1 = 0 :=
  Subsingleton.elim _ _

theorem leaf_eq (ℓ : Leaf friends) : ∃ y b : Fin 2, ℓ = leafOf y b := by
  rcases ℓ with ⟨a, y, rest⟩
  fin_cases a
  rcases rest with ⟨b, z, u⟩
  fin_cases z
  cases u
  exact ⟨y, b, rfl⟩

theorem leafMass_leafOf (y b : Fin 2) : leafMass (leafOf y b) = 1 / 2 := by
  simp [leafOf, leafMass, friends, after, halfK]

theorem infoMass_half : infoMass ((1 : ℝ) / 2) = 1 := by
  unfold infoMass
  have hlogb : Real.logb 2 ((1 : ℝ) / 2) = -1 := by
    rw [Real.logb]
    have hlog : Real.log ((1 : ℝ) / 2) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hlog]
    field_simp
  rw [hlogb]
  norm_num

theorem info_one (ℓ : Leaf friends) : infoMass (leafMass ℓ) = 1 := by
  obtain ⟨y, b, rfl⟩ := leaf_eq ℓ
  rw [leafMass_leafOf, infoMass_half]

theorem values_one : infoValues friends = [1] := by
  have hmem : ∀ z ∈ infoValues friends, z = 1 := by
    intro z hz
    obtain ⟨ℓ, hℓ⟩ := (mem_infoValues).1 hz
    rw [← hℓ, info_one ℓ]
  have hnodup : (infoValues friends).Nodup := (sortedLT_infoValues friends).nodup
  match h : infoValues friends with
  | [] =>
      exact absurd h (infoValues_ne_nil friends)
  | z :: zs =>
      have hz : z = 1 := hmem z (by simpa [h] using List.mem_cons_self z zs)
      cases zs with
      | nil =>
          simp [h, hz]
      | cons w ws =>
          have hw : w = 1 :=
            hmem w (by simpa [h] using List.mem_cons_of_mem z (List.mem_cons_self w ws))
          have hnd : (z :: w :: ws).Nodup := by simpa [h] using hnodup
          simp [hz, hw, List.nodup_cons] at hnd

theorem policyCDF_friends (π : Policy friends) (t : ℝ) :
    policyCDF friends π t = if 1 ≤ t then 1 else 0 := by
  unfold policyCDF
  have hfun :
      (fun ℓ : Leaf friends => if infoMass (leafMass ℓ) ≤ t then leafMass ℓ else 0) =
        fun ℓ => if 1 ≤ t then leafMass ℓ else 0 := by
    funext ℓ
    rw [info_one ℓ]
  rw [hfun]
  by_cases ht : 1 ≤ t
  · simp [ht, policySum_leafMass]
  · simp [ht, policySum_zero]

theorem Fstar_friends (t : ℝ) : Fstar friends t = if 1 ≤ t then 1 else 0 := by
  unfold Fstar
  rw [policyCDF_friends]

theorem envInc_zero : envInc friends 0 = 1 := by
  unfold envInc
  simp only [values_one, List.length_cons, List.length_nil]
  simp [Fstar_friends]

theorem envelope_one : envelopeMean friends = 1 := by
  unfold envelopeMean
  simp only [values_one, List.length_cons, List.length_nil]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  simp [envInc_zero]

/-- One shared answer. The private questions are not consulted. -/
theorem same_first_answer (d : Strategy friends) :
    firstBit (run d friendA) = firstBit (run d friendB) := by
  have hA : run d friendA =
      ⟨friendA.1, d.1 friendA.1,
        run (d.2 friendA.1 (d.1 friendA.1)) (friendA.2 friendA.1 (d.1 friendA.1))⟩ := rfl
  have hB : run d friendB =
      ⟨friendB.1, d.1 friendB.1,
        run (d.2 friendB.1 (d.1 friendB.1)) (friendB.2 friendB.1 (d.1 friendB.1))⟩ := rfl
  rw [hA, hB]
  simp [firstBit, friendA, friendB]

theorem run_reply (b : Fin 2) (π : Policy friends) :
    run (reply b) π = leafOf b (π.2 0 b).1 := by
  have hπ : π.1 = 0 := pi1 π
  have hrun : run (reply b) π = ⟨π.1, b, run quiet (π.2 π.1 b)⟩ := rfl
  have hq : run quiet (π.2 π.1 b) =
      ⟨(π.2 π.1 b).1, ⟨0, Nat.one_pos⟩, PUnit.unit⟩ := rfl
  rw [hπ] at hrun hq
  rw [hrun, hq]
  rfl

theorem leafOf_eq_iff (y b y' b' : Fin 2) :
    leafOf y b = leafOf y' b' ↔ y = y' ∧ b = b' := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · simpa [firstBit, leafOf] using congrArg firstBit h
    · simpa [leafOf] using congrArg (fun ℓ : Leaf friends => ℓ.2.2.1) h
  · rintro ⟨rfl, rfl⟩
    rfl

theorem marginal_A (y : Fin 2) : CompatiblePolicy (leafOf y 0) friendA := by
  refine ⟨rfl, ⟨rfl, trivial⟩⟩

theorem marginal_B (y : Fin 2) : CompatiblePolicy (leafOf y 1) friendB := by
  refine ⟨rfl, ⟨rfl, trivial⟩⟩

theorem compatible_iff (π : Policy friends) (y b : Fin 2) :
    CompatiblePolicy (leafOf y b) π ↔ b = (π.2 0 y).1 := by
  constructor
  · intro h
    have hπ : π.1 = 0 := pi1 π
    rcases h with ⟨-, hrest⟩
    simpa [leafOf, hπ, CompatiblePolicy, friends, after] using hrest
  · intro hb
    have hπ : π.1 = 0 := pi1 π
    refine ⟨hπ.symm, ?_⟩
    simpa [leafOf, hb, CompatiblePolicy, friends, after]

/-- Opposite first replies match each prescribed transcript and no strategy produces both. -/
theorem anti_not_shared :
    leafMass (leafOf 0 0) = 1 / 2 ∧ leafMass (leafOf 1 1) = 1 / 2 ∧
      CompatiblePolicy (leafOf 0 0) friendA ∧ CompatiblePolicy (leafOf 1 1) friendB ∧
        ∀ d : Strategy friends,
          ¬ (run d friendA = leafOf 0 0 ∧ run d friendB = leafOf 1 1) := by
  refine ⟨leafMass_leafOf 0 0, leafMass_leafOf 1 1, marginal_A 0, marginal_B 1, ?_⟩
  intro d ⟨hA, hB⟩
  have hsame := same_first_answer d
  simp [firstBit, leafOf, hA, hB] at hsame

theorem shared_pair (b : Fin 2) :
    run (reply b) friendA = leafOf b 0 ∧ run (reply b) friendB = leafOf b 1 := by
  constructor
  · simpa [friendA] using run_reply b friendA
  · simpa [friendB] using run_reply b friendB

def sharedAtoms : List (Atom friends) :=
  [(1 / 2, reply 0), (1 / 2, reply 1)]

theorem shared_nonneg : ∀ a ∈ sharedAtoms, 0 ≤ a.1 := by
  intro a ha
  simp [sharedAtoms] at ha
  rcases ha with rfl | rfl <;> norm_num

theorem shared_pos : ∀ a ∈ sharedAtoms, 0 < a.1 := by
  intro a ha
  simp [sharedAtoms] at ha
  rcases ha with rfl | rfl <;> norm_num

theorem shared_total : totalWeight sharedAtoms = 1 := by
  simp [sharedAtoms, totalWeight]
  norm_num

theorem shared_shannon : seedShannon sharedAtoms = 1 := by
  simp only [seedShannon, sharedAtoms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [infoMass_half]
  norm_num

theorem shared_exact (π : Policy friends) (ℓ : Leaf friends) :
    transcriptWeight sharedAtoms π ℓ =
      if CompatiblePolicy ℓ π then leafMass ℓ else 0 := by
  classical
  obtain ⟨y, b, rfl⟩ := leaf_eq ℓ
  unfold transcriptWeight
  simp only [sharedAtoms, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  have h0 : run (reply 0) π = leafOf y b ↔ y = 0 ∧ b = (π.2 0 0).1 := by
    rw [run_reply]
    simpa using (leafOf_eq_iff 0 (π.2 0 0).1 y b).trans (by tauto)
  have h1 : run (reply 1) π = leafOf y b ↔ y = 1 ∧ b = (π.2 0 1).1 := by
    rw [run_reply]
    simpa using (leafOf_eq_iff 1 (π.2 0 1).1 y b).trans (by tauto)
  by_cases hc : CompatiblePolicy (leafOf y b) π
  · have hb : b = (π.2 0 y).1 := (compatible_iff π y b).1 hc
    rw [ite_eq_left hc, leafMass_leafOf]
    by_cases hy : y = 0
    · subst hy
      have hmatch : run (reply 0) π = leafOf 0 b := (h0.mpr ⟨rfl, hb⟩)
      have hmiss : run (reply 1) π ≠ leafOf 0 b := by
        intro h
        exact Fin.zero_ne_one (h1.mp h).1
      simp [hmatch, hmiss]
    · have hy1 : y = 1 := by
        fin_cases y <;> simp_all
      subst hy1
      have hmatch : run (reply 1) π = leafOf 1 b := (h1.mpr ⟨rfl, hb⟩)
      have hmiss : run (reply 0) π ≠ leafOf 1 b := by
        intro h
        exact Fin.zero_ne_one (h0.mp h).1.symm
      simp [hmatch, hmiss]
  · rw [ite_eq_right hc]
    have hmiss0 : run (reply 0) π ≠ leafOf y b := by
      intro h
      have ⟨hy, hb⟩ := h0.1 h
      have hc' : CompatiblePolicy (leafOf y b) π := (compatible_iff π y b).2 (hy ▸ hb)
      exact hc hc'
    have hmiss1 : run (reply 1) π ≠ leafOf y b := by
      intro h
      have ⟨hy, hb⟩ := h1.1 h
      have hc' : CompatiblePolicy (leafOf y b) π := (compatible_iff π y b).2 (hy ▸ hb)
      exact hc hc'
    simp [hmiss0, hmiss1]

theorem shared_entropy :
    (couplingOfAtoms sharedAtoms shared_nonneg shared_total shared_exact).entropy = 1 ∧
      (couplingOfAtoms sharedAtoms shared_nonneg shared_total shared_exact).badMass = 0 := by
  let Γ := couplingOfAtoms sharedAtoms shared_nonneg shared_total shared_exact
  have hbad : Γ.badMass = 0 :=
    couplingOfAtoms_badMass sharedAtoms shared_nonneg shared_total shared_exact
  have hle : Γ.entropy ≤ seedShannon sharedAtoms :=
    couplingOfAtoms_entropy_le sharedAtoms shared_nonneg shared_pos shared_total shared_exact
  have hge : envelopeMean friends ≤ Γ.entropy := entropy_ge_envelope Γ
  have hone : Γ.entropy = 1 := by
    rw [shared_shannon] at hle
    rw [envelope_one] at hge
    linarith
  exact ⟨hone, hbad⟩

theorem sharp :
    envelopeMean friends = 1 ∧ causalMin friends = 1 ∧ ordinaryMin friends = 1 := by
  let Γ := couplingOfAtoms sharedAtoms shared_nonneg shared_total shared_exact
  have hent : Γ.entropy = 1 := shared_entropy.1
  have hbad : Γ.badMass = 0 := shared_entropy.2
  have hC : causalMin friends ≤ 1 := by
    simpa [hent] using causalMin_le_entropy_of_badMass hbad
  have hL : 1 ≤ ordinaryMin friends := by
    simpa [envelope_one] using ordinaryMin_ge_envelope friends
  have hord : ordinaryMin friends ≤ causalMin friends := ordinaryMin_le_causalMin friends
  have hCge : 1 ≤ causalMin friends := le_trans hL hord
  have hCeq : causalMin friends = 1 := le_antisymm hC hCge
  have hOeq : ordinaryMin friends = 1 := le_antisymm (hord.trans hC) hL
  exact ⟨envelope_one, hCeq, hOeq⟩

theorem gap_zero : gapOf friends = 0 := by
  unfold gapOf
  have h := sharp
  linarith

end ManyFriends
end CausalSpectrum

end

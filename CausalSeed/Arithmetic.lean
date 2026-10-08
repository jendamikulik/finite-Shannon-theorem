/-
Arithmetic profile of a fixed finite seed.

An index lies in the defect when it belongs to the symmetric difference of
two subsets whose weights differ by at most `2ε`. Distinct subset sums are
equivalent to an empty defect at `ε = 0`, and the defect is empty if and only
if `2ε` is strictly below the minimum separation `gamma`.

The decoder half is not in this file. `CausalSeed/Probe.lean` puts every
unrealizable index of an `ε`-accurate family into that defect.
`CausalSeed/Profile.lean` attains the equality on one tree of depth at most
two and records the two corollaries. None of these files uses the Shannon bound.
-/
import CausalSeed.Spectrum
import CausalSeed.Entropy
import CausalSeed.Close
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

noncomputable section
open Classical
namespace CausalSpectrum

/-! ## Subset sums -/

def subsetSum {m : ℕ} (w : Fin m → ℝ) (A : Finset (Fin m)) : ℝ :=
  ∑ i ∈ A, w i

def seedSym {α : Type} [DecidableEq α] (A B : Finset α) : Finset α :=
  (A \ B) ∪ (B \ A)

theorem mem_seedSym {α : Type} [DecidableEq α] {A B : Finset α} {i : α} :
    i ∈ seedSym A B ↔ (i ∈ A ∧ i ∉ B) ∨ (i ∈ B ∧ i ∉ A) := by
  simp [seedSym, Finset.mem_union, Finset.mem_sdiff]

theorem seedSym_nonempty_of_ne {m : ℕ} {A B : Finset (Fin m)} (h : A ≠ B) :
    (seedSym A B).Nonempty := by
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  apply h
  ext i
  have hi : i ∉ seedSym A B := by simp [hempty]
  rw [mem_seedSym] at hi
  push_neg at hi
  constructor
  · intro hA
    exact hi.1 hA
  · intro hB
    exact hi.2 hB

def inDefect {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) (i : Fin m) : Prop :=
  ∃ A B : Finset (Fin m), A ≠ B ∧ |subsetSum w A - subsetSum w B| ≤ 2 * ε ∧
    i ∈ seedSym A B

def defectFinset {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) : Finset (Fin m) :=
  Finset.univ.filter (fun i => inDefect w ε i)

def defectMass {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) : ℝ :=
  subsetSum w (defectFinset w ε)

def unequalPairs (m : ℕ) : Finset (Finset (Fin m) × Finset (Fin m)) :=
  Finset.univ.filter (fun p : Finset (Fin m) × Finset (Fin m) => p.1 ≠ p.2)

theorem unequalPairs_nonempty {m : ℕ} (hm : 0 < m) :
    (unequalPairs m).Nonempty := by
  refine ⟨(∅, {⟨0, hm⟩}), ?_⟩
  simp only [unequalPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  intro h
  have : (⟨0, hm⟩ : Fin m) ∈ (∅ : Finset (Fin m)) := by
    rw [h]
    exact Finset.mem_singleton_self _
  simp at this

def subsetGapSet {m : ℕ} (w : Fin m → ℝ) : Finset ℝ :=
  (unequalPairs m).image (fun p => |subsetSum w p.1 - subsetSum w p.2|)

theorem subsetGapSet_nonempty {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) :
    (subsetGapSet w).Nonempty := by
  obtain ⟨p, hp⟩ := unequalPairs_nonempty hm
  exact ⟨_, Finset.mem_image.mpr ⟨p, hp, rfl⟩⟩

def gamma {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) : ℝ :=
  (subsetGapSet w).min' (subsetGapSet_nonempty hm w)

theorem gamma_le {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ)
    {A B : Finset (Fin m)} (hne : A ≠ B) :
    gamma hm w ≤ |subsetSum w A - subsetSum w B| := by
  have hp : (A, B) ∈ unequalPairs m := by
    simp [unequalPairs, hne]
  exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨(A, B), hp, rfl⟩)

theorem exists_gamma_pair {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ) :
    ∃ A B : Finset (Fin m), A ≠ B ∧
      |subsetSum w A - subsetSum w B| = gamma hm w := by
  have hmem := Finset.min'_mem (subsetGapSet w) (subsetGapSet_nonempty hm w)
  obtain ⟨p, hp, hg⟩ := Finset.mem_image.mp hmem
  refine ⟨p.1, p.2, ?_, hg⟩
  simpa [unequalPairs] using hp

def subsetSumsDistinct {m : ℕ} (w : Fin m → ℝ) : Prop :=
  ∀ A B : Finset (Fin m), A ≠ B → subsetSum w A ≠ subsetSum w B

theorem subsetSumsDistinct_iff_defect_empty {m : ℕ} (w : Fin m → ℝ) :
    subsetSumsDistinct w ↔ ∀ i, ¬ inDefect w 0 i := by
  constructor
  · intro h i ⟨A, B, hne, hgap, hi⟩
    have heq : subsetSum w A = subsetSum w B := by
      have h0 : |subsetSum w A - subsetSum w B| ≤ 0 := by simpa using hgap
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h0 (abs_nonneg _)))
    exact h A B hne heq
  · intro h A B hne heq
    have hsym : (seedSym A B).Nonempty := seedSym_nonempty_of_ne hne
    obtain ⟨i, hi⟩ := hsym
    exact h i ⟨A, B, hne, by simpa [heq], hi⟩

theorem defect_empty_iff_lt_gamma {m : ℕ} (hm : 0 < m) (w : Fin m → ℝ)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (∀ i, ¬ inDefect w ε i) ↔ 2 * ε < gamma hm w := by
  constructor
  · intro hempty
    by_contra hge
    push_neg at hge
    obtain ⟨A, B, hne, hg⟩ := exists_gamma_pair hm w
    have hgap : |subsetSum w A - subsetSum w B| ≤ 2 * ε := by
      rw [hg]; exact hge
    have hsym : (seedSym A B).Nonempty := seedSym_nonempty_of_ne hne
    obtain ⟨i, hi⟩ := hsym
    exact hempty i ⟨A, B, hne, hgap, hi⟩
  · intro hlt i ⟨A, B, hne, hgap, _⟩
    have hle : gamma hm w ≤ |subsetSum w A - subsetSum w B| := gamma_le hm w hne
    linarith

/-! ## Positive seeds -/

theorem subsetSum_nonneg {m : ℕ} {w : Fin m → ℝ} (hpos : ∀ i, 0 < w i)
    (A : Finset (Fin m)) : 0 ≤ subsetSum w A :=
  Finset.sum_nonneg fun i _ => (hpos i).le

theorem subsetSum_pos_of_mem {m : ℕ} {w : Fin m → ℝ} (hpos : ∀ i, 0 < w i)
    {A : Finset (Fin m)} {i : Fin m} (hi : i ∈ A) : 0 < subsetSum w A := by
  exact lt_of_lt_of_le (hpos i) (Finset.single_le_sum (fun j _ => (hpos j).le) hi)

theorem subsetSum_le_total {m : ℕ} {w : Fin m → ℝ} (hpos : ∀ i, 0 < w i)
    (A : Finset (Fin m)) : subsetSum w A ≤ ∑ i, w i := by
  have hsub : A ⊆ Finset.univ := Finset.subset_univ A
  simpa [subsetSum] using
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => (hpos i).le)

theorem subsetSum_eq_total_iff {m : ℕ} {w : Fin m → ℝ}
    (hpos : ∀ i, 0 < w i) (A : Finset (Fin m)) :
    subsetSum w A = ∑ i, w i ↔ A = Finset.univ := by
  constructor
  · intro h
    ext i
    constructor
    · intro _; exact Finset.mem_univ _
    · intro _
      by_contra hi
      have hA : A ⊆ Finset.univ.erase i := by
        intro j hj
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
        intro hji
        subst hji
        exact hi hj
      have hsum : subsetSum w A ≤ ∑ j ∈ Finset.univ.erase i, w j := by
        simpa [subsetSum] using
          Finset.sum_le_sum_of_subset_of_nonneg hA (fun j _ _ => (hpos j).le)
      have hsplit := Finset.sum_erase_add (Finset.univ : Finset (Fin m)) w
        (Finset.mem_univ i)
      have hlt : ∑ j ∈ Finset.univ.erase i, w j < ∑ j, w j := by
        rw [← hsplit]
        linarith [hpos i]
      have : subsetSum w A < ∑ i, w i := lt_of_le_of_lt hsum hlt
      linarith
  · intro h
    simp [subsetSum, h]

theorem half_bounds {m : ℕ} {w : Fin m → ℝ} (hpos : ∀ i, 0 < w i)
    (hsum : ∑ i, w i = 1) {A B : Finset (Fin m)} (hne : A ≠ B) :
    let q := (subsetSum w A + subsetSum w B) / 2
    0 < q ∧ q < 1 := by
  dsimp only
  have hsym : (seedSym A B).Nonempty := seedSym_nonempty_of_ne hne
  obtain ⟨i, hi⟩ := hsym
  have hi' : i ∈ A ∨ i ∈ B := by
    have : i ∈ A \ B ∨ i ∈ B \ A := by simpa [mem_seedSym] using hi
    rcases this with h | h
    · exact Or.inl (Finset.mem_sdiff.mp h).1
    · exact Or.inr (Finset.mem_sdiff.mp h).1
  have hpossum : 0 < subsetSum w A + subsetSum w B := by
    rcases hi' with h | h
    · exact lt_of_lt_of_le (subsetSum_pos_of_mem hpos h)
        (le_add_of_nonneg_right (subsetSum_nonneg hpos B))
    · exact lt_of_lt_of_le (subsetSum_pos_of_mem hpos h)
        (le_add_of_nonneg_left (subsetSum_nonneg hpos A))
  constructor
  · exact div_pos hpossum two_pos
  · rw [div_lt_one (by norm_num : (0 : ℝ) < 2)]
    by_contra hge
    push_neg at hge
    have hAle : subsetSum w A ≤ 1 := by simpa [hsum] using subsetSum_le_total hpos A
    have hBle : subsetSum w B ≤ 1 := by simpa [hsum] using subsetSum_le_total hpos B
    have hA1 : subsetSum w A = 1 := by linarith
    have hB1 : subsetSum w B = 1 := by linarith
    have hAu : A = Finset.univ :=
      (subsetSum_eq_total_iff hpos A).mp (by simpa [hsum] using hA1)
    have hBu : B = Finset.univ :=
      (subsetSum_eq_total_iff hpos B).mp (by simpa [hsum] using hB1)
    exact hne (hAu.trans hBu.symm)

theorem half_gap_le {a b ε : ℝ} (h : |a - b| ≤ 2 * ε) :
    |a - (a + b) / 2| ≤ ε ∧ |b - (a + b) / 2| ≤ ε := by
  have ha : a - (a + b) / 2 = (a - b) / 2 := by ring
  have hb : b - (a + b) / 2 = (b - a) / 2 := by ring
  constructor
  · rw [ha, abs_div, abs_two]
    have : |a - b| / 2 ≤ (2 * ε) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    simpa using this
  · rw [hb, abs_div, abs_two, abs_sub_comm]
    have : |a - b| / 2 ≤ (2 * ε) / 2 := div_le_div_of_nonneg_right h (by norm_num)
    simpa using this

/-! ## Decoder families -/

def SeedAssign (T : Tree) : Type :=
  ∀ π : Policy T, {ℓ : Leaf T // CompatiblePolicy ℓ π}

def seedRealizes {T : Tree} (d : Strategy T) : SeedAssign T :=
  fun π => ⟨run d π, run_compatible_policy d π⟩

def seedRealizable {T : Tree} (α : SeedAssign T) : Prop :=
  ∃ d : Strategy T, seedRealizes d = α

def seedMass {m : ℕ} (w : Fin m → ℝ) (p : Fin m → Prop) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i => p i), w i

/-- Mass, under one policy, of the compatible transcripts that lie in `S`. -/
def hitMass {T : Tree} (S : Leaf T → Prop) (π : Policy T) : ℝ :=
  policySum (fun ℓ => if S ℓ then leafMass ℓ else 0) π

def Decoder {m : ℕ} (T : Tree) : Type :=
  (π : Policy T) → Fin m → {ℓ : Leaf T // CompatiblePolicy ℓ π}

def Accurate {m : ℕ} (w : Fin m → ℝ) (ε : ℝ) {T : Tree}
    (f : Decoder (m := m) T) : Prop :=
  ∀ (π : Policy T) (S : Leaf T → Prop),
    |seedMass w (fun i => S ((f π i).1)) - hitMass S π| ≤ ε

def oneAssign {m : ℕ} {T : Tree} (f : Decoder (m := m) T) (i : Fin m) : SeedAssign T :=
  fun π => f π i

/-!
Checked here: the defect set, its symmetric-difference description, the
separation `gamma`, and the two equivalences `subsetSumsDistinct ↔ defect
empty at 0` and `defect empty ↔ 2ε < gamma`. The inclusion of every
incompatible decoder index in that defect is `bad_mem_defect` in
`CausalSeed/Probe.lean`. The depth-two attainment and the rigidity
corollaries are `profile_attainment`, `exact_rigidity` and `sharp_threshold`
in `CausalSeed/Profile.lean`.
-/

#print axioms subsetSumsDistinct_iff_defect_empty
#print axioms defect_empty_iff_lt_gamma
#print axioms half_bounds
#print axioms half_gap_le

end CausalSpectrum
end

/-
Exact decoding of a prescribed seed.

Given probability vectors `w = (w_0, …, w_n)` and `q = (q_0, …, q_m)`, the
exact-decoding problem asks for a decoder `d : {0,…,n} → {0,…,m}` with
`∑_{i : d i = j} w_i = q_j` for every `j`. Exact decoding of a prescribed seed
is NP-complete, by reduction from Subset Sum (binary output) and, in the strong
sense, from 3-Partition.

The complexity statement is proved in prose; Lean checks the reduction identities.

Proved here, with no sorry:

* the mass decoded to an output is a subset sum of the seed
  (`outMass_eq`, through `seedMass_eq_subsetSum`);
* binary reduction: with `w_i = a_i / A` and `p = B / A`, a decoder sends mass
  `p` to output `1` exactly when its preimage of `1` has `∑ a_i = B`, and an
  exact decoder exists exactly when the Subset Sum instance is a yes-instance
  (`binary_mass_iff`, `binary_iff`);
* heavy-atom binary reduction: with `w_0 = 1 - ε` and light atoms `ε a_i / A`,
  the iff holds whenever `ε B < (1 - ε) A`, in particular for `0 < ε < 1/2`
  (`heavy_binary_iff`, `heavy_binary_iff_of_lt_half`); without that condition
  it fails (`heavy_binary_not_iff`);
* 3-Partition reduction: with `w_0 = q_0 = 1 - ε`, `w_i = ε a_i / (m B)` and
  `q_j = ε / m`, an exact decoder exists exactly when the integers split into
  `m` classes of sum `B`, for every `ε > 0` with `ε / m < 1 - ε`, and in
  particular for `ε = (3m + 1)⁻²`; under `B/4 < a_i < B/2` every class has
  exactly three elements (`three_partition_iff`, `three_partition_iff_eps`,
  `card_eq_three`);
* the seeds are probability vectors, and their Shannon entropy (bits) obeys the
  chain rule `H(w) = h₂(ε) + ε H(u) ≤ h₂(ε) + ε log₂ n`
  (`heavy_entropy`, `heavy_entropy_le`, `tp_entropy_le`, `binary_entropy_le`);
* with a freely chosen seed law, two atoms realise any binary target
  (`free_law_two_atoms`).

Not formalized: polynomial time, membership in NP, and NP-hardness.
-/
import CausalSeed.Probe
import CausalSeed.Penalty
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

noncomputable section
open Classical

namespace CausalSpectrum
namespace ExactDecoding

open Finset

/-! ### Decoded mass -/

/-- Mass of the seed `w` that the decoder `d` sends to output `j`. -/
def outMass {k l : ℕ} (w : Fin k → ℝ) (d : Fin k → Fin l) (j : Fin l) : ℝ :=
  seedMass w (fun i => d i = j)

/-- `d` decodes the seed `w` exactly to the law `q`. -/
def IsExact {k l : ℕ} (w : Fin k → ℝ) (q : Fin l → ℝ) (d : Fin k → Fin l) : Prop :=
  ∀ j, outMass w d j = q j

/-- The decoded mass is the subset sum over the preimage. -/
theorem outMass_eq {k l : ℕ} (w : Fin k → ℝ) (d : Fin k → Fin l) (j : Fin l) :
    outMass w d j = subsetSum w (univ.filter fun i => d i = j) := by
  unfold outMass
  convert seedMass_eq_subsetSum w (univ.filter fun i => d i = j) using 2
  funext i; simp

theorem outMass_eq_sum {k l : ℕ} (w : Fin k → ℝ) (d : Fin k → Fin l) (j : Fin l) :
    outMass w d j = ∑ i, if d i = j then w i else 0 := by
  rw [outMass_eq, subsetSum, sum_filter]

/-- The decoded masses add up to the total mass of the seed. -/
theorem sum_outMass {k l : ℕ} (w : Fin k → ℝ) (d : Fin k → Fin l) :
    ∑ j, outMass w d j = ∑ i, w i := by
  simp only [outMass_eq, subsetSum]
  exact sum_fiberwise univ d w

/-- Decoded mass for a seed with a distinguished first atom. -/
theorem outMass_cons {n l : ℕ} (x : ℝ) (u : Fin n → ℝ) (d : Fin (n + 1) → Fin l)
    (j : Fin l) :
    outMass (Fin.cons x u : Fin (n + 1) → ℝ) d j =
      (if d 0 = j then x else 0) + ∑ i ∈ univ.filter (fun i => d i.succ = j), u i := by
  rw [outMass_eq_sum, Fin.sum_univ_succ, sum_filter]
  simp

/-- The seed with a heavy atom `1 - ε` followed by the light atoms `ε u_i`. -/
def heavyVec {n : ℕ} (ε : ℝ) (u : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cons (1 - ε) (fun i => ε * u i)

theorem heavyVec_sum {n : ℕ} (ε : ℝ) (u : Fin n → ℝ) (hu : ∑ i, u i = 1) :
    ∑ i, heavyVec ε u i = 1 := by
  rw [Fin.sum_univ_succ]
  simp [heavyVec, ← mul_sum, hu]

theorem heavyVec_nonneg {n : ℕ} {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {u : Fin n → ℝ}
    (hu : ∀ i, 0 ≤ u i) (i : Fin (n + 1)) : 0 ≤ heavyVec ε u i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [heavyVec]; linarith
  · simp [heavyVec]; exact mul_nonneg h0 (hu i)

/-! ### Binary output: Subset Sum -/

section Binary

variable {n : ℕ}

/-- The total `A = ∑ a_i`. -/
def total (a : Fin n → ℕ) : ℕ := ∑ i, a i

/-- The normalized weights `a_i / A`. -/
def subsetWeights (a : Fin n → ℕ) : Fin n → ℝ := fun i => (a i : ℝ) / (total a)

/-- The Subset Sum instance `(a, B)` is a yes-instance. -/
def SubsetSumYes (a : Fin n → ℕ) (B : ℕ) : Prop :=
  ∃ I : Finset (Fin n), ∑ i ∈ I, a i = B

theorem subsetWeights_sum (a : Fin n → ℕ) (hA : 0 < total a) :
    ∑ i, subsetWeights a i = 1 := by
  have hA' : (0 : ℝ) < total a := by exact_mod_cast hA
  simp only [subsetWeights, ← sum_div]
  rw [div_eq_one_iff_eq hA'.ne']
  simp [total]

theorem subsetWeights_nonneg (a : Fin n → ℕ) (i : Fin n) : 0 ≤ subsetWeights a i := by
  unfold subsetWeights; positivity

theorem sum_subsetWeights (a : Fin n → ℕ) (hA : 0 < total a) (I : Finset (Fin n))
    (c : ℕ) :
    ∑ i ∈ I, subsetWeights a i = (c : ℝ) / total a ↔ ∑ i ∈ I, a i = c := by
  have hA' : (0 : ℝ) < total a := by exact_mod_cast hA
  simp only [subsetWeights, ← sum_div]
  rw [div_left_inj' hA'.ne']
  exact_mod_cast Iff.rfl

/-- A decoder sends mass `B / A` to output `1` exactly when the preimage of `1`
has `∑ a_i = B`. -/
theorem binary_mass_iff (a : Fin n → ℕ) (B : ℕ) (hA : 0 < total a) (d : Fin n → Fin 2) :
    outMass (subsetWeights a) d 1 = (B : ℝ) / total a ↔
      ∑ i ∈ univ.filter (fun i => d i = 1), a i = B := by
  rw [outMass_eq, subsetSum]
  exact sum_subsetWeights a hA _ B

/-- The binary target `(1 - p, p)`. -/
def binTarget (p : ℝ) : Fin 2 → ℝ := ![1 - p, p]

/-- Two outputs: the second mass fixes the first. -/
theorem isExact_two {k : ℕ} (w : Fin k → ℝ) (hw : ∑ i, w i = 1) (d : Fin k → Fin 2)
    (p : ℝ) : IsExact w (binTarget p) d ↔ outMass w d 1 = p := by
  constructor
  · intro h; simpa [binTarget] using h 1
  · intro h j
    have hs := sum_outMass w d
    rw [Fin.sum_univ_two, hw] at hs
    fin_cases j
    · simp [binTarget]; linarith
    · simpa [binTarget] using h

/-- Binary reduction. An exact decoder of the seed `a_i / A` to the law
`(1 - B/A, B/A)` exists exactly when some subset has sum `B`. -/
theorem binary_iff (a : Fin n → ℕ) (B : ℕ) (hA : 0 < total a) :
    (∃ d, IsExact (subsetWeights a) (binTarget ((B : ℝ) / total a)) d) ↔
      SubsetSumYes a B := by
  have hw := subsetWeights_sum a hA
  constructor
  · rintro ⟨d, hd⟩
    exact ⟨_, (binary_mass_iff a B hA d).1 ((isExact_two _ hw d _).1 hd)⟩
  · rintro ⟨I, hI⟩
    refine ⟨fun i => if i ∈ I then 1 else 0, (isExact_two _ hw _ _).2 ?_⟩
    rw [binary_mass_iff a B hA]
    convert hI using 2
    ext i; simp

/-- Heavy-atom binary reduction. If `ε B < (1 - ε) A`, the heavy atom cannot be
sent to output `1`, and an exact decoder exists exactly when some subset has
sum `B`. -/
theorem heavy_binary_iff (a : Fin n → ℕ) (B : ℕ) (hA : 0 < total a) {ε : ℝ}
    (hε0 : 0 < ε) (hheavy : ε * B < (1 - ε) * total a) :
    (∃ d, IsExact (heavyVec ε (subsetWeights a))
        (binTarget (ε * B / total a)) d) ↔ SubsetSumYes a B := by
  have hA' : (0 : ℝ) < total a := by exact_mod_cast hA
  have hw := heavyVec_sum ε _ (subsetWeights_sum a hA)
  have hlight : ∀ (d : Fin (n + 1) → Fin 2),
      ∑ i ∈ univ.filter (fun i => d i.succ = 1), ε * subsetWeights a i =
        ε * ∑ i ∈ univ.filter (fun i => d i.succ = 1), subsetWeights a i :=
    fun d => (mul_sum _ _ _).symm
  constructor
  · rintro ⟨d, hd⟩
    have h1 := (isExact_two _ hw d _).1 hd
    unfold heavyVec at h1
    rw [outMass_cons, hlight] at h1
    have hnn : 0 ≤ ∑ i ∈ univ.filter (fun i => d i.succ = 1), subsetWeights a i :=
      sum_nonneg fun i _ => subsetWeights_nonneg a i
    by_cases h0 : d 0 = 1
    · exfalso
      simp only [h0, ↓reduceIte] at h1
      have : (1 - ε) ≤ ε * B / total a := by nlinarith
      rw [le_div_iff₀ hA'] at this
      linarith
    · simp only [h0, ↓reduceIte, zero_add] at h1
      refine ⟨univ.filter (fun i => d i.succ = 1), (sum_subsetWeights a hA _ B).1 ?_⟩
      field_simp at h1 ⊢
      nlinarith [h1]
  · rintro ⟨I, hI⟩
    refine ⟨Fin.cons 0 (fun i => if i ∈ I then 1 else 0), (isExact_two _ hw _ _).2 ?_⟩
    unfold heavyVec
    rw [outMass_cons, hlight]
    have hf : univ.filter (fun i : Fin n =>
        (Fin.cons 0 (fun i => if i ∈ I then 1 else 0) : Fin (n + 1) → Fin 2) i.succ = 1) = I := by
      ext i; simp
    rw [hf, (sum_subsetWeights a hA I B).2 hI]
    simp [mul_div_assoc]

/-- The heavy-atom reduction for every `0 < ε < 1/2`. -/
theorem heavy_binary_iff_of_lt_half (a : Fin n → ℕ) (B : ℕ) (hA : 0 < total a)
    (hB : B ≤ total a) {ε : ℝ} (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    (∃ d, IsExact (heavyVec ε (subsetWeights a))
        (binTarget (ε * B / total a)) d) ↔ SubsetSumYes a B := by
  refine heavy_binary_iff a B hA hε0 ?_
  have hA' : (0 : ℝ) < total a := by exact_mod_cast hA
  have hB' : (B : ℝ) ≤ total a := by exact_mod_cast hB
  nlinarith

/-- Without a bound on `ε` the heavy-atom reduction fails: for `a = (1, 3)`,
`B = 2` and `ε = 2/3` an exact decoder exists (the heavy atom alone fills
output `1`), but no subset of `{1, 3}` has sum `2`. -/
theorem heavy_binary_not_iff :
    (∃ d, IsExact (heavyVec (2 / 3) (subsetWeights ![1, 3]))
        (binTarget ((2 / 3) * (2 : ℕ) / total ![1, 3])) d) ∧
      ¬ SubsetSumYes ![1, 3] 2 := by
  have htot : total ![1, 3] = 4 := by simp [total]
  constructor
  · have hA : 0 < total ![1, 3] := by rw [htot]; norm_num
    have hw := heavyVec_sum (2 / 3 : ℝ) _ (subsetWeights_sum _ hA)
    refine ⟨Fin.cons 1 (fun _ => 0), (isExact_two _ hw _ _).2 ?_⟩
    unfold heavyVec
    rw [outMass_cons]
    simp [htot]
    norm_num
  · rintro ⟨I, hI⟩
    revert hI
    revert I
    decide

end Binary

/-! ### 3-Partition -/

section ThreePartition

variable {m : ℕ}

/-- The normalized light weights `a_i / (m B)`. -/
def tpWeights (a : Fin (3 * m) → ℕ) (B : ℕ) : Fin (3 * m) → ℝ :=
  fun i => (a i : ℝ) / ((m : ℝ) * B)

/-- The seed: heavy atom `1 - ε`, light atoms `ε a_i / (m B)`. -/
def tpSeed (ε : ℝ) (a : Fin (3 * m) → ℕ) (B : ℕ) : Fin (3 * m + 1) → ℝ :=
  heavyVec ε (tpWeights a B)

/-- The target law: `q_0 = 1 - ε` and `q_j = ε / m` for `j = 1, …, m`. -/
def tpTarget (m : ℕ) (ε : ℝ) : Fin (m + 1) → ℝ :=
  Fin.cons (1 - ε) (fun _ => ε / m)

/-- The integers split into `m` classes of sum `B`. -/
def FiberSums (a : Fin (3 * m) → ℕ) (B : ℕ) : Prop :=
  ∃ f : Fin (3 * m) → Fin m, ∀ j, ∑ i ∈ univ.filter (fun i => f i = j), a i = B

/-- The 3-Partition instance is a yes-instance: `m` triples of sum `B`. -/
def ThreePartitionYes (a : Fin (3 * m) → ℕ) (B : ℕ) : Prop :=
  ∃ f : Fin (3 * m) → Fin m, ∀ j,
    (univ.filter (fun i => f i = j)).card = 3 ∧
      ∑ i ∈ univ.filter (fun i => f i = j), a i = B

theorem tpWeights_sum (a : Fin (3 * m) → ℕ) (B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hsum : ∑ i, a i = m * B) : ∑ i, tpWeights a B i = 1 := by
  have hmB : (0 : ℝ) < (m : ℝ) * B := by positivity
  simp only [tpWeights, ← sum_div]
  rw [div_eq_one_iff_eq hmB.ne']
  exact_mod_cast hsum

theorem tpSeed_sum (ε : ℝ) (a : Fin (3 * m) → ℕ) (B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hsum : ∑ i, a i = m * B) : ∑ i, tpSeed ε a B i = 1 :=
  heavyVec_sum ε _ (tpWeights_sum a B hm hB hsum)

theorem tpTarget_sum (ε : ℝ) (hm : 0 < m) : ∑ j, tpTarget m ε j = 1 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [Fin.sum_univ_succ]
  simp [tpTarget]
  field_simp
  ring

/-- Exactly three. If every element lies strictly between `B/4` and `B/2` and a
set has sum `B > 0`, the set has exactly three elements. -/
theorem card_eq_three {ι : Type*} (S : Finset ι) (a : ι → ℕ) {B : ℕ} (hB : 0 < B)
    (hlo : ∀ i ∈ S, B < 4 * a i) (hhi : ∀ i ∈ S, 2 * a i < B)
    (hS : ∑ i ∈ S, a i = B) : S.card = 3 := by
  have hne : S.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp at hS
    omega
  have h1 : ∑ i ∈ S, B < ∑ i ∈ S, 4 * a i := sum_lt_sum_of_nonempty hne hlo
  have h2 : ∑ i ∈ S, 2 * a i < ∑ i ∈ S, B := sum_lt_sum_of_nonempty hne hhi
  rw [sum_const, smul_eq_mul, ← mul_sum, hS] at h1 h2
  have hc4 : S.card < 4 := by nlinarith
  have hc2 : 2 < S.card := by nlinarith
  omega

/-- 3-Partition reduction, for every `ε > 0` with `ε / m < 1 - ε`. An exact
decoder exists exactly when the integers split into `m` classes of sum `B`.
The heavy atom fills output `0`; every other output receives sum `B`. -/
theorem three_partition_iff (a : Fin (3 * m) → ℕ) (B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (ha : ∀ i, 0 < a i) {ε : ℝ} (hε0 : 0 < ε) (hε : ε / m < 1 - ε) :
    (∃ d, IsExact (tpSeed ε a B) (tpTarget m ε) d) ↔ FiberSums a B := by
  have hmB : (0 : ℝ) < (m : ℝ) * B := by positivity
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hlight : ∀ (d : Fin (3 * m + 1) → Fin (m + 1)) (j : Fin (m + 1)),
      ∑ i ∈ univ.filter (fun i => d i.succ = j), ε * tpWeights a B i =
        ε * ((∑ i ∈ univ.filter (fun i => d i.succ = j), (a i : ℝ)) / ((m : ℝ) * B)) := by
    intro d j
    rw [← mul_sum, sum_div]
    rfl
  constructor
  · rintro ⟨d, hd⟩
    have hnn : ∀ j, 0 ≤ ∑ i ∈ univ.filter (fun i => d i.succ = j), (a i : ℝ) :=
      fun j => sum_nonneg fun i _ => Nat.cast_nonneg _
    -- The heavy atom goes to output `0`.
    have h0 : d 0 = 0 := by
      by_contra hne
      obtain ⟨j, hj⟩ := Fin.exists_succ_eq.2 hne
      have h := hd j.succ
      unfold tpSeed heavyVec at h
      rw [outMass_cons, hlight] at h
      simp only [hj.symm, ↓reduceIte] at h
      simp only [tpTarget, Fin.cons_succ] at h
      have : 0 ≤ ε * ((∑ i ∈ univ.filter (fun i => d i.succ = j.succ), (a i : ℝ)) /
          ((m : ℝ) * B)) := mul_nonneg hε0.le (div_nonneg (hnn _) hmB.le)
      linarith
    -- No light atom goes to output `0`.
    have hz : ∀ i : Fin (3 * m), d i.succ ≠ 0 := by
      intro i hi
      have h := hd 0
      unfold tpSeed heavyVec at h
      rw [outMass_cons, hlight] at h
      simp only [h0, ↓reduceIte] at h
      simp only [tpTarget, Fin.cons_zero] at h
      have hpos : 0 < ∑ k ∈ univ.filter (fun k => d k.succ = 0), (a k : ℝ) :=
        lt_of_lt_of_le (by exact_mod_cast ha i)
          (single_le_sum (fun k _ => Nat.cast_nonneg (a k)) (by simp [hi]))
      have : 0 < ε * ((∑ k ∈ univ.filter (fun k => d k.succ = 0), (a k : ℝ)) /
          ((m : ℝ) * B)) := mul_pos hε0 (div_pos hpos hmB)
      linarith
    refine ⟨fun i => (d i.succ).pred (hz i), fun j => ?_⟩
    have h := hd j.succ
    unfold tpSeed heavyVec at h
    have h0j : ¬ d 0 = j.succ := by rw [h0]; exact (Fin.succ_ne_zero j).symm
    rw [outMass_cons, hlight] at h
    simp only [h0j, ↓reduceIte, zero_add] at h
    simp only [tpTarget, Fin.cons_succ] at h
    have hf : univ.filter (fun i => (d i.succ).pred (hz i) = j) =
        univ.filter (fun i => d i.succ = j.succ) := by
      ext i; simp [Fin.pred_eq_iff_eq_succ]
    rw [hf]
    have : (∑ i ∈ univ.filter (fun i => d i.succ = j.succ), (a i : ℝ)) = B := by
      field_simp at h
      nlinarith [h]
    exact_mod_cast this
  · rintro ⟨f, hf⟩
    refine ⟨Fin.cons 0 (fun i => (f i).succ), fun j => ?_⟩
    unfold tpSeed heavyVec
    rw [outMass_cons, hlight]
    refine Fin.cases ?_ (fun j => ?_) j
    · have he : univ.filter (fun i : Fin (3 * m) =>
          (Fin.cons 0 (fun i => (f i).succ) : Fin (3 * m + 1) → Fin (m + 1)) i.succ = 0) = ∅ := by
        ext i; simp
      rw [he]
      simp [tpTarget]
    · have he : univ.filter (fun i : Fin (3 * m) =>
          (Fin.cons 0 (fun i => (f i).succ) : Fin (3 * m + 1) → Fin (m + 1)) i.succ = j.succ) =
            univ.filter (fun i => f i = j) := by
        ext i; simp
      rw [he]
      have hs : (∑ i ∈ univ.filter (fun i => f i = j), (a i : ℝ)) = B := by
        exact_mod_cast hf j
      rw [hs]
      simp [tpTarget, (Fin.succ_ne_zero j).symm]
      field_simp

/-- With `B/4 < a_i < B/2`, the classes are triples. -/
theorem fiberSums_iff_threePartition (a : Fin (3 * m) → ℕ) (B : ℕ) (hB : 0 < B)
    (hlo : ∀ i, B < 4 * a i) (hhi : ∀ i, 2 * a i < B) :
    FiberSums a B ↔ ThreePartitionYes a B := by
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨f, fun j => ⟨card_eq_three _ a hB (fun i _ => hlo i) (fun i _ => hhi i) (hf j),
      hf j⟩⟩
  · rintro ⟨f, hf⟩
    exact ⟨f, fun j => (hf j).2⟩

/-- 3-Partition reduction in full: under `B/4 < a_i < B/2`, an exact decoder
exists exactly when the integers split into `m` triples of sum `B`. -/
theorem three_partition_iff_triples (a : Fin (3 * m) → ℕ) (B : ℕ) (hm : 0 < m)
    (hB : 0 < B) (hlo : ∀ i, B < 4 * a i) (hhi : ∀ i, 2 * a i < B) {ε : ℝ}
    (hε0 : 0 < ε) (hε : ε / m < 1 - ε) :
    (∃ d, IsExact (tpSeed ε a B) (tpTarget m ε) d) ↔ ThreePartitionYes a B := by
  have ha : ∀ i, 0 < a i := fun i => by have := hlo i; omega
  rw [three_partition_iff a B hm hB ha hε0 hε, fiberSums_iff_threePartition a B hB hlo hhi]

/-- The specific parameter `ε = (n + 1)⁻²` with `n = 3m`. -/
def tpEps (m : ℕ) : ℝ := ((3 * m + 1 : ℝ) ^ 2)⁻¹

theorem tpEps_pos (m : ℕ) : 0 < tpEps m := by unfold tpEps; positivity

theorem tpEps_le (hm : 0 < m) : tpEps m ≤ 1 / 16 := by
  unfold tpEps
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  nlinarith

theorem tpEps_ok (hm : 0 < m) : tpEps m / m < 1 - tpEps m := by
  have h := tpEps_le hm
  have hp := tpEps_pos m
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have : tpEps m / m ≤ tpEps m := div_le_self hp.le hm'
  linarith

/-- 3-Partition reduction with `ε = (3m + 1)⁻²`. -/
theorem three_partition_iff_eps (a : Fin (3 * m) → ℕ) (B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hlo : ∀ i, B < 4 * a i) (hhi : ∀ i, 2 * a i < B) :
    (∃ d, IsExact (tpSeed (tpEps m) a B) (tpTarget m (tpEps m)) d) ↔
      ThreePartitionYes a B :=
  three_partition_iff_triples a B hm hB hlo hhi (tpEps_pos m) (tpEps_ok hm)

end ThreePartition

/-! ### Entropy of the seed -/

section Entropy

/-- `entTerm` in bits is `negMulLog` divided by `ln 2`. -/
theorem entTerm_eq_negMulLog_div (x : ℝ) : entTerm x = Real.negMulLog x / Real.log 2 := by
  by_cases hx : x = 0
  · simp [hx, entTerm]
  · simp [entTerm, hx, infoMass, Real.logb, Real.negMulLog]
    ring

/-- The binary entropy in bits, `h₂(ε)`. -/
theorem binEntropy_bits (ε : ℝ) :
    entTerm ε + entTerm (1 - ε) = Real.binEntropy ε / Real.log 2 := by
  rw [entTerm_eq_negMulLog_div, entTerm_eq_negMulLog_div,
    Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_div]

/-- Chain rule for the heavy-atom seed:
`H(w) = h₂(ε) + ε H(u)`, in bits. -/
theorem heavy_entropy {n : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε) {u : Fin n → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu : ∑ i, u i = 1) :
    pmfEntropy (heavyVec ε u) = Real.binEntropy ε / Real.log 2 + ε * pmfEntropy u := by
  rw [← binEntropy_bits]
  unfold pmfEntropy heavyVec
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  have h : ∀ i, entTerm (ε * u i) = u i * entTerm ε + ε * entTerm (u i) :=
    fun i => entTerm_mul hε0 (hu0 i)
  simp only [h, sum_add_distrib, ← sum_mul, hu, ← mul_sum]
  ring

/-- Maximal entropy: a probability vector on `n` points has at most
`log₂ n` bits. -/
theorem pmfEntropy_le_logb {n : ℕ} (hn : 0 < n) {u : Fin n → ℝ} (hu0 : ∀ i, 0 ≤ u i)
    (hu : ∑ i, u i = 1) : pmfEntropy u ≤ Real.logb 2 n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- termwise: `negMulLog x ≤ 1/n - x + x log n`
  have hterm : ∀ x : ℝ, 0 ≤ x → Real.negMulLog x ≤ 1 / n - x + x * Real.log n := by
    intro x hx
    rcases hx.eq_or_lt with rfl | hx
    · simp only [Real.negMulLog_zero, zero_mul, sub_zero, add_zero]; positivity
    · have hy : 0 < (n : ℝ) * x := mul_pos hn' hx
      have hlog := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
      rw [Real.log_inv, Real.log_mul hn'.ne' hx.ne'] at hlog
      have hx' : x * ((n : ℝ) * x)⁻¹ = 1 / n := by field_simp
      unfold Real.negMulLog
      have := mul_le_mul_of_nonneg_left hlog hx.le
      rw [mul_sub, hx'] at this
      nlinarith
  have hsum : ∑ i, Real.negMulLog (u i) ≤ Real.log n := by
    calc ∑ i, Real.negMulLog (u i) ≤ ∑ i, (1 / n - u i + u i * Real.log n) :=
          sum_le_sum fun i _ => hterm _ (hu0 i)
      _ = Real.log n := by
          rw [sum_add_distrib, sum_sub_distrib, ← sum_mul, hu]
          simp [hn'.ne']
  unfold pmfEntropy
  simp only [entTerm_eq_negMulLog_div, ← sum_div, Real.logb]
  exact div_le_div_of_nonneg_right hsum hl2.le

/-- Entropy bound for the heavy-atom seed:
`H(w) ≤ h₂(ε) + ε log₂ n`. -/
theorem heavy_entropy_le {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε0 : 0 ≤ ε) {u : Fin n → ℝ}
    (hu0 : ∀ i, 0 ≤ u i) (hu : ∑ i, u i = 1) :
    pmfEntropy (heavyVec ε u) ≤ Real.binEntropy ε / Real.log 2 + ε * Real.logb 2 n := by
  rw [heavy_entropy hε0 hu0 hu]
  have := pmfEntropy_le_logb hn hu0 hu
  nlinarith

/-- The 3-Partition seed has entropy at most `h₂(ε) + ε log₂ (3m)` bits. -/
theorem tp_entropy_le {m : ℕ} (a : Fin (3 * m) → ℕ) (B : ℕ) (hm : 0 < m) (hB : 0 < B)
    (hsum : ∑ i, a i = m * B) {ε : ℝ} (hε0 : 0 ≤ ε) :
    pmfEntropy (tpSeed ε a B) ≤
      Real.binEntropy ε / Real.log 2 + ε * Real.logb 2 ((3 * m : ℕ) : ℝ) :=
  heavy_entropy_le (by omega) hε0
    (fun i => by unfold tpWeights; positivity) (tpWeights_sum a B hm hB hsum)

/-- The heavy-atom binary seed has entropy at most `h₂(ε) + ε log₂ n` bits. -/
theorem binary_entropy_le {n : ℕ} (a : Fin n → ℕ) (hA : 0 < total a) {ε : ℝ}
    (hε0 : 0 ≤ ε) :
    pmfEntropy (heavyVec ε (subsetWeights a)) ≤
      Real.binEntropy ε / Real.log 2 + ε * Real.logb 2 n := by
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp [total] at hA
    · exact h
  exact heavy_entropy_le hn hε0 (subsetWeights_nonneg a) (subsetWeights_sum a hA)

end Entropy

/-! ### A freely chosen seed law -/

/-- Any law is decoded exactly from itself by the identity. -/
theorem free_law {l : ℕ} (q : Fin l → ℝ) : IsExact q q id := by
  intro j
  rw [outMass_eq_sum]
  simp

/-- With a freely chosen seed law, two atoms realise any binary target. -/
theorem free_law_two_atoms {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ w : Fin 2 → ℝ, (∀ i, 0 ≤ w i) ∧ ∑ i, w i = 1 ∧
      ∃ d, IsExact w (binTarget p) d := by
  refine ⟨binTarget p, fun i => ?_, by simp [binTarget], id, free_law _⟩
  fin_cases i <;> simp [binTarget] <;> linarith

end ExactDecoding
end CausalSpectrum

/-
From exact finite atoms to the countable-seed cost, and `C_n = L_n` for dyadic kernels.

`finiteCost_le_atoms`: any exact finite seed of `trunc ι n []` (positive atoms, total
mass one), extended to the infinite tree, is a countable seed exact to horizon `n`
with the same entropy; hence `finiteCost ι n ≤ log 2 · seedShannon`.  This generalizes
the greedy-seed upper bound of `EnvelopeBridge`.  Combined with `Dyadic.dyadic_exact`,
the optimal cost of a stationary dyadic kernel equals the envelope mean exactly.
-/
import CausalSeed.DyadicTree
import CausalSeed.SqrtMain

noncomputable section
open Classical Finset
namespace CausalSpectrum.Completion

variable (ι : ITree) (n : ℕ) (atoms : List (Atom (trunc ι n [])))

/-- Strategy of atom `i` (a default past the end). -/
def aStrat (i : ℕ) : Strategy (trunc ι n []) :=
  if h : i < atoms.length then (atoms[i]).2 else zeroStrategy _

/-- The countable seed of a finite atom list. -/
def aCode (i : ℕ) : IStrategy ι := extend ι n (aStrat ι n atoms i)

theorem aTerm (todo : List (ℕ × ℕ)) (hn : todo.length ≤ n) (i : ℕ) :
    atomWeight atoms i * indAgree ι (aCode ι n atoms i) todo =
      if hi : i < atoms.length then
        if stratAgrees (atoms[i]'hi).2 todo then (atoms[i]'hi).1 else 0
      else 0 := by
  by_cases hi : i < atoms.length
  · rw [atomWeight_lt _ hi, dif_pos hi]
    have hag : iAgree ι (aCode ι n atoms i) todo ↔ stratAgrees (atoms[i]'hi).2 todo := by
      rw [iAgree_iff, aCode, extend, extendAbs_agreesFrom ι n [] todo _ hn, aStrat, dif_pos hi]
    by_cases hs : stratAgrees (atoms[i]'hi).2 todo
    · simp [indAgree, hs, hag.mpr hs]
    · have : ¬ iAgree ι (aCode ι n atoms i) todo := fun h => hs (hag.mp h)
      simp [indAgree, hs, this]
  · rw [atomWeight_ge _ (not_lt.mp hi), dif_neg hi, zero_mul]

variable {ι n atoms}

theorem atoms_hitSum (hpos : ∀ a ∈ atoms, 0 < a.1)
    (hex : ∀ (π : Policy (trunc ι n [])) (ℓ : Leaf (trunc ι n [])),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (todo : List (ℕ × ℕ)) (hn : todo.length ≤ n) :
    hitSum atoms todo = pathMass ι todo := by
  have hnn : ∀ a ∈ atoms, 0 ≤ a.1 := fun a ha => (hpos a ha).le
  have hle : hitSum atoms todo ≤ pathMass ι todo := by
    have := hit_le_prefix atoms todo hnn (fun ℓ => by
      rw [hex]; split_ifs
      · exact le_rfl
      · exact (leafMass_pos ℓ).le)
    have hmass := prefix_mass ι n [] todo hn
    simpa [pathMass] using le_trans this (le_of_eq hmass)
  apply le_antisymm hle
  have hmass := prefix_mass ι n [] todo hn
  have hsum : ∑ ℓ ∈ prefixLeaves (T := trunc ι n []) todo, leafMass ℓ =
      ∑ ℓ ∈ prefixLeaves (T := trunc ι n []) todo, transcriptWeight atoms (followPol todo) ℓ := by
    apply Finset.sum_congr rfl
    intro ℓ hℓ
    have hc : CompatiblePolicy ℓ (followPol todo) := by
      simp only [prefixLeaves, Finset.mem_filter] at hℓ
      exact hℓ.2.2
    rw [hex, if_pos hc]
  calc pathMass ι todo = ∑ ℓ ∈ prefixLeaves (T := trunc ι n []) todo, leafMass ℓ := by
        simpa [pathMass] using hmass.symm
    _ = _ := hsum
    _ ≤ hitSum atoms todo := prefix_transcript_le_hitSum todo atoms hnn

theorem atomWeight_nonneg' (hpos : ∀ a ∈ atoms, 0 < a.1) (i : ℕ) : 0 ≤ atomWeight atoms i := by
  unfold atomWeight; split_ifs with h
  · exact (hpos _ (List.getElem_mem h)).le
  · exact le_rfl

/-- The countable seed of an exact finite atom list. -/
def atomSeed (hpos : ∀ a ∈ atoms, 0 < a.1) (htot : totalWeight atoms = 1) : CountableSeed ι :=
  ⟨atomWeight atoms, atomWeight_nonneg' hpos, by
    have hz : ∀ i ∉ range atoms.length, atomWeight atoms i = 0 := fun i hi =>
      atomWeight_ge _ (by simpa using hi)
    have h : HasSum (atomWeight atoms) (∑ i ∈ range atoms.length, atomWeight atoms i) :=
      hasSum_sum_of_ne_finset_zero hz
    have he : ∑ i ∈ range atoms.length, atomWeight atoms i = 1 := by
      rw [sum_range_atomWeight (fun x => x) atoms, ← htot]; rfl
    rwa [he] at h, aCode ι n atoms⟩

theorem atomSeed_exactTo (hpos : ∀ a ∈ atoms, 0 < a.1) (htot : totalWeight atoms = 1)
    (hex : ∀ (π : Policy (trunc ι n [])) (ℓ : Leaf (trunc ι n [])),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    (atomSeed hpos htot).ExactTo n := by
  intro todo hn
  have hz : ∀ i ∉ range atoms.length,
      atomWeight atoms i * indAgree ι (aCode ι n atoms i) todo = 0 := fun i hi => by
    rw [atomWeight_ge _ (by simpa using hi), zero_mul]
  show ∑' i, atomWeight atoms i * indAgree ι (aCode ι n atoms i) todo = pathMass ι todo
  rw [tsum_eq_sum hz, Finset.sum_congr rfl (fun i _ => aTerm ι n atoms todo hn i),
    ← hitSum_eq_range, atoms_hitSum hpos hex todo hn]

theorem atomSeed_entropy (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    (atomSeed hpos htot).entropy = ENNReal.ofReal (Real.log 2 * seedShannon atoms) := by
  have hmem : ∀ i, atomWeight atoms i ≤ 1 := fun i => by
    unfold atomWeight; split_ifs with h
    · exact hle _ (List.getElem_mem h)
    · norm_num
  have hz : ∀ i ∉ range atoms.length, ENNReal.ofReal (Real.negMulLog (atomWeight atoms i)) = 0 :=
    fun i hi => by rw [atomWeight_ge _ (by simpa using hi)]; simp
  unfold CountableSeed.entropy atomSeed
  simp only
  rw [tsum_eq_sum hz, ← ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    Real.negMulLog_nonneg (atomWeight_nonneg' hpos i) (hmem i))]
  congr 1
  rw [sum_range_atomWeight Real.negMulLog atoms, seedShannon]
  exact list_negMulLog_eq atoms

/-- `C_n ≤ log 2 · H(atoms)` for every exact finite seed of the horizon-`n` tree. -/
theorem finiteCost_le_atoms (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1)
    (hex : ∀ (π : Policy (trunc ι n [])) (ℓ : Leaf (trunc ι n [])),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0) :
    finiteCost ι n ≤ ENNReal.ofReal (Real.log 2 * seedShannon atoms) := by
  rw [← atomSeed_entropy hpos hle htot, ← (atomSeed hpos htot).ranked_entropy]
  exact finiteCost_le_seed ι n _
    (((atomSeed hpos htot).ranked_exactTo_iff n).mpr (atomSeed_exactTo hpos htot hex))

end CausalSpectrum.Completion

namespace CausalSpectrum.Kernel
variable (κ : Kernel)

/-- Every kernel entry is a power of `1/2`. -/
def IsDyadic : Prop := ∀ a y, ∃ c : ℕ, κ.K a y = CausalSpectrum.Dyadic.wt c

theorem rounds_dyadic (h : κ.IsDyadic) : ∀ n, CausalSpectrum.Dyadic.DyadicTree (κ.rounds n)
  | 0 => trivial
  | n + 1 => ⟨h, fun _ _ => rounds_dyadic h n⟩

/-- **Exact optimality for dyadic kernels: `C_n = L_n`** (bits), every horizon. -/
theorem cost_eq_envelope_of_dyadic (h : κ.IsDyadic) (n : ℕ) :
    κ.costBits n = envelopeMean (κ.rounds n) := by
  refine le_antisymm ?_ (κ.costBits_sandwich n).1
  have hT : CausalSpectrum.Dyadic.DyadicTree (trunc κ.toITree n []) := by
    rw [κ.trunc_toITree]; exact κ.rounds_dyadic h n
  obtain ⟨atoms, hpos, hle, htot, hex, -, hsh⟩ := CausalSpectrum.Dyadic.dyadic_exact _ hT
  have hc := Completion.finiteCost_le_atoms hpos hle htot hex
  rw [hsh, κ.trunc_toITree] at hc
  have hl := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  have hL := envelopeMean_nonneg (κ.rounds n)
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
  rw [ENNReal.toReal_ofReal (by positivity)] at this
  unfold costBits
  rw [div_le_iff₀ hl]; linarith

end CausalSpectrum.Kernel

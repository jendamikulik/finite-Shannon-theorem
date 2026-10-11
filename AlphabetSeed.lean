/- Candidate, not locally compiled. Arbitrary countable source alphabets. -/
import CausalSeed.SeedRanking

noncomputable section
open Classical
open scoped ENNReal
namespace CausalSpectrum.Completion

structure AlphabetSeed (ι : ITree) (Ω : Type*) where
  weight : Ω → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  mass : HasSum weight 1
  strategy : Ω → IStrategy ι

namespace AlphabetSeed
variable {ι : ITree} {Ω : Type*} [Countable Ω]

def entropy (S : AlphabetSeed ι Ω) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (S.weight i))

def hit (S : AlphabetSeed ι Ω) (h : List (ℕ × ℕ)) (i : Ω) : ℝ :=
  S.weight i * indAgree ι (S.strategy i) h

def ExactTo (S : AlphabetSeed ι Ω) (n : ℕ) : Prop :=
  ∀ h, h.length ≤ n → ∑' i, S.hit h i = pathMass ι h

def Exact (S : AlphabetSeed ι Ω) : Prop := ∀ n, S.ExactTo n

private def relabel {M : Type*} [Zero M] (F : Ω → M) (n : ℕ) : M :=
  letI := Encodable.ofCountable Ω
  match Encodable.decode₂ Ω n with | none => 0 | some i => F i

private theorem tsum_relabel {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [T2Space M] (F : Ω → M) :
    ∑' n, relabel F n = ∑' i, F i := by
  letI := Encodable.ofCountable Ω
  apply tsum_eq_tsum_of_ne_zero_bij (fun i : Function.support F => Encodable.encode i.val)
  · intro i j hij
    exact Subtype.ext (Encodable.encode_injective hij)
  · intro n hn
    cases hc : Encodable.decode₂ Ω n with
    | none => exact False.elim (hn (by simp [relabel, hc]))
    | some i =>
      have hi : F i ≠ 0 := by simpa [relabel, hc] using hn
      exact ⟨⟨i, hi⟩, Encodable.decode₂_eq_some.mp hc⟩
  · intro i
    simp [relabel, Encodable.decode₂_encode]

def toSeed (S : AlphabetSeed ι Ω) : Seed ι where
  weight := relabel S.weight
  nonneg := by
    letI := Encodable.ofCountable Ω
    intro n
    cases hc : Encodable.decode₂ Ω n <;> simp [relabel, hc, S.nonneg]
  mass := by
    have he : ∑' n, relabel S.weight n = 1 := (tsum_relabel S.weight).trans S.mass.tsum_eq
    have hs : Summable (relabel S.weight) := by
      by_contra h
      rw [tsum_eq_zero_of_not_summable h] at he
      norm_num at he
    simpa [he] using hs.hasSum
  strategy := fun n =>
    letI := Encodable.ofCountable Ω
    match Encodable.decode₂ Ω n with
    | some i => S.strategy i
    | none => fun p => ⟨0, ι.hY p.1 p.2⟩

theorem toSeed_entropy (S : AlphabetSeed ι Ω) : S.toSeed.entropy = S.entropy := by
  letI := Encodable.ofCountable Ω
  calc
    _ = ∑' n, relabel (fun i => ENNReal.ofReal (Real.negMulLog (S.weight i))) n := by
      apply tsum_congr
      intro n
      cases hc : Encodable.decode₂ Ω n <;>
        simp [Seed.entropy, toSeed, relabel, hc, Real.negMulLog_def]
    _ = _ := tsum_relabel _

theorem toSeed_hit (S : AlphabetSeed ι Ω) (h) :
    ∑' n, S.toSeed.hit h n = ∑' i, S.hit h i := by
  letI := Encodable.ofCountable Ω
  calc
    _ = ∑' n, relabel (S.hit h) n := by
      apply tsum_congr
      intro n
      cases hc : Encodable.decode₂ Ω n <;>
        simp [Seed.hit, CountableSeed.hit, hit, toSeed, relabel, hc]
    _ = _ := tsum_relabel _

theorem toSeed_exactTo (S : AlphabetSeed ι Ω) (n) :
    S.toSeed.ExactTo n ↔ S.ExactTo n := by
  simp only [Seed.ExactTo, CountableSeed.ExactTo, ExactTo]
  simp only [show ∀ h, ∑' i, CountableSeed.hit S.toSeed h i = ∑' i, S.hit h i from S.toSeed_hit]

/-- Sorting preserves entropy and every finite-horizon law simultaneously. -/
theorem exists_ranked (S : AlphabetSeed ι Ω) :
    ∃ R : RankedSeed ι, R.entropy = S.entropy ∧
      (∀ h, (∑' i, R.hit h i) = ∑' i, S.hit h i) ∧
      (∀ n, R.ExactTo n ↔ S.ExactTo n) ∧ (R.Exact ↔ S.Exact) := by
  refine ⟨S.toSeed.ranked, ?_, ?_, ?_, ?_⟩
  · exact S.toSeed.ranked_entropy.trans S.toSeed_entropy
  · intro h
    exact (S.toSeed.ranked_hit h).trans (S.toSeed_hit h)
  · intro n
    exact (S.toSeed.ranked_exactTo n).trans (S.toSeed_exactTo n)
  · simp only [RankedSeed.Exact, Exact, S.toSeed.ranked_exactTo, S.toSeed_exactTo]

#print axioms exists_ranked
end AlphabetSeed
end CausalSpectrum.Completion

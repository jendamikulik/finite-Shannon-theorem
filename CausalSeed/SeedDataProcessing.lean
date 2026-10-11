/- Compiled in the lake build of 11 October 2026 (Lean 4.35.0-rc3, mathlib 7d6757bc). Entropy is in nats, with values in ENNReal. -/
import CausalSeed.SeedRanking
import CausalSeed.Penalty

noncomputable section
open Classical Finset
open scoped ENNReal
namespace CausalSpectrum.Completion
namespace Seed
variable {ι : ITree}

theorem weight_le_one (S : Seed ι) (i) : S.weight i ≤ 1 :=
  le_hasSum S.mass i (fun j _ => S.nonneg j)

theorem dominated_summable (S : Seed ι) {f : ℕ → ℝ}
    (hf : ∀ i, 0 ≤ f i) (hle : ∀ i, f i ≤ S.weight i) : Summable f := by
  apply summable_of_sum_range_le hf
  intro K
  exact (Finset.sum_le_sum fun i _ => hle i).trans
    (sum_le_hasSum (range K) (fun i _ => S.nonneg i) S.mass)

def fiberWeight {β : Type*} (S : Seed ι) (f : ℕ → β) (b : β) (i : ℕ) : ℝ :=
  if f i = b then S.weight i else 0

def push {β : Type*} (S : Seed ι) (f : ℕ → β) (b : β) : ℝ :=
  ∑' i, S.fiberWeight f b i

theorem fiber_nonneg {β : Type*} (S : Seed ι) (f : ℕ → β) (b i) :
    0 ≤ S.fiberWeight f b i := by
  simp only [fiberWeight]; split_ifs <;> simp [S.nonneg]

theorem fiber_le {β : Type*} (S : Seed ι) (f : ℕ → β) (b i) :
    S.fiberWeight f b i ≤ S.weight i := by
  simp only [fiberWeight]; split_ifs <;> simp [S.nonneg]

theorem fiber_summable {β : Type*} (S : Seed ι) (f : ℕ → β) (b) :
    Summable (S.fiberWeight f b) :=
  S.dominated_summable (S.fiber_nonneg f b) (S.fiber_le f b)

theorem push_nonneg {β : Type*} (S : Seed ι) (f : ℕ → β) (b) :
    0 ≤ S.push f b := tsum_nonneg (S.fiber_nonneg f b)

theorem push_le_one {β : Type*} (S : Seed ι) (f : ℕ → β) (b) :
    S.push f b ≤ 1 := by
  rw [← S.mass.tsum_eq]
  exact (S.fiber_summable f b).tsum_le_tsum (S.fiber_le f b) S.mass.summable

theorem weight_le_push {β : Type*} (S : Seed ι) (f : ℕ → β) (i) :
    S.weight i ≤ S.push f (f i) := by
  have h := le_hasSum (S.fiber_summable f (f i)).hasSum i
    (fun j _ => S.fiber_nonneg f (f i) j)
  simpa [fiberWeight, push] using h

theorem push_event {β : Type*} [Fintype β] (S : Seed ι) (f : ℕ → β)
    (P : β → Prop) :
    (∑ b, if P b then S.push f b else 0) =
      ∑' i, if P (f i) then S.weight i else 0 := by
  have hs : ∀ b ∈ (univ : Finset β),
      Summable (fun i => if P b then S.fiberWeight f b i else 0) := by
    intro b _
    by_cases hb : P b
    · simpa [hb] using S.fiber_summable f b
    · simp [hb]
  calc
    _ = ∑ b, ∑' i, if P b then S.fiberWeight f b i else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : P b <;> simp [hb, push]
    _ = ∑' i, ∑ b, if P b then S.fiberWeight f b i else 0 :=
      (Summable.tsum_finsetSum hs).symm
    _ = _ := tsum_congr fun i => by
      simp only [fiberWeight]
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro b _ hb
        simp [Ne.symm hb]
      · simp

theorem push_total {β : Type*} [Fintype β] (S : Seed ι) (f : ℕ → β) :
    ∑ b, S.push f b = 1 := by
  simpa [S.mass.tsum_eq] using S.push_event f (fun _ => True)

/-- Data processing without assuming the source entropy is finite. -/
theorem push_entropy_le {β : Type*} [Fintype β] (S : Seed ι) (f : ℕ → β) :
    (∑ b, ENNReal.ofReal (Real.negMulLog (S.push f b))) ≤ S.entropy := by
  have bound : ∀ b, ENNReal.ofReal (Real.negMulLog (S.push f b)) ≤
      ∑' i, if f i = b then ENNReal.ofReal (Real.negMulLog (S.weight i)) else 0 := by
    intro b
    by_cases hz : S.push f b = 0
    · simp [hz, Real.negMulLog_def]
    have hp : 0 < S.push f b := lt_of_le_of_ne (S.push_nonneg f b) (Ne.symm hz)
    have hl : 0 ≤ -Real.log (S.push f b) := by
      have := Real.log_le_log hp (S.push_le_one f b)
      simpa using this
    have he : Real.negMulLog (S.push f b) =
        ∑' i, S.fiberWeight f b i * (-Real.log (S.push f b)) := by
      rw [tsum_mul_right]
      simp [push, Real.negMulLog_def]
    rw [he, ENNReal.ofReal_tsum_of_nonneg
      (fun i => mul_nonneg (S.fiber_nonneg f b i) hl)
      ((S.fiber_summable f b).mul_right _)]
    apply ENNReal.tsum_le_tsum
    intro i
    by_cases hb : f i = b
    · simp only [fiberWeight, hb, if_true]
      apply ENNReal.ofReal_le_ofReal
      by_cases hwi : S.weight i = 0
      · simp [hwi, Real.negMulLog_def]
      have hpos : 0 < S.weight i := lt_of_le_of_ne (S.nonneg i) (Ne.symm hwi)
      have hle : S.weight i ≤ S.push f b := hb ▸ S.weight_le_push f i
      have hlog := Real.log_le_log hpos hle
      have hm := mul_le_mul_of_nonneg_left hlog (S.nonneg i)
      simp only [Real.negMulLog_def]
      nlinarith
    · simp [fiberWeight, hb]
  calc
    _ ≤ ∑ b, ∑' i, if f i = b then
        ENNReal.ofReal (Real.negMulLog (S.weight i)) else 0 :=
      Finset.sum_le_sum fun b _ => bound b
    _ = ∑' i, ∑ b, if f i = b then
        ENNReal.ofReal (Real.negMulLog (S.weight i)) else 0 := by
      exact (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
    _ = S.entropy := by simp [entropy, CountableSeed.entropy]

def transcriptCoupling (S : Seed ι) (n : ℕ) (hex : S.ExactTo n) :
    CausalSpectrum.Coupling (trunc ι n []) where
  mass := S.push (fun i => CausalSpectrum.realizes (restrict ι n [] (S.strategy i)))
  nonneg := S.push_nonneg _
  total := S.push_total _
  marginal := by
    intro π ℓ hℓ
    rw [S.push_event]
    let t : Transcript ι n π := ⟨ℓ, hℓ⟩
    have hevent : ∀ i,
        (CausalSpectrum.realizes (restrict ι n [] (S.strategy i)) π).val = ℓ ↔
          iAgree ι (S.strategy i) (truncPath ι n [] ℓ) := by
      intro i
      have h := Set.ext_iff.mp (policyRead_fiber ι n π t) (S.strategy i)
      simpa [policyRead, CausalSpectrum.realizes, t, cylinder, Subtype.ext_iff] using h
    have hterm : (fun i => if
        (CausalSpectrum.realizes (restrict ι n [] (S.strategy i)) π).val = ℓ
          then S.weight i else 0) = S.hit (truncPath ι n [] ℓ) := by
      funext i
      simp only [hit, CountableSeed.hit, indAgree, hevent i]
      split_ifs <;> simp
    rw [hterm]
    have hh := hex (truncPath ι n [] ℓ) (by rw [truncPath_length])
    rw [pathMass_leaf] at hh
    exact hh

end Seed

theorem entTerm_nats (w : ℝ) :
    CausalSpectrum.entTerm w * Real.log 2 = Real.negMulLog w := by
  by_cases h : w = 0
  · simp [h, CausalSpectrum.entTerm, Real.negMulLog_def]
  · have hl : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
    simp only [CausalSpectrum.entTerm, h, if_false, infoMass, Real.logb, Real.negMulLog_def]
    field_simp

theorem finite_envelope_lower (ι : ITree) (n : ℕ) (S : Seed ι) (hex : S.ExactTo n) :
    ENNReal.ofReal (envelopeMean (trunc ι n []) * Real.log 2) ≤ S.entropy := by
  let Γ := S.transcriptCoupling n hex
  have hl := mul_le_mul_of_nonneg_right (entropy_ge_envelope Γ)
    (le_of_lt (Real.log_pos (by norm_num : (1:ℝ) < 2)))
  apply (ENNReal.ofReal_le_ofReal hl).trans
  have he : Γ.entropy * Real.log 2 =
      ∑ a, Real.negMulLog (Γ.mass a) := by
    simp only [CausalSpectrum.Coupling.entropy, pmfEntropy, Finset.sum_mul, entTerm_nats]
  rw [he]
  show ENNReal.ofReal (∑ a, Real.negMulLog (S.push _ a)) ≤ _
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ =>
    Real.negMulLog_nonneg (S.push_nonneg _ a) (S.push_le_one _ a))]
  exact S.push_entropy_le _

end CausalSpectrum.Completion

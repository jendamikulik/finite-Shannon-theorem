/- Candidate, not locally compiled. L∞ is the actual finite-envelope supremum. -/
import CausalSeed.FiniteSeedExtension

noncomputable section
open Classical
open scoped ENNReal
namespace CausalSpectrum.Completion

/-- Bits, not nats. No seed-cost definition is substituted for the envelope. -/
def infiniteEnvelope (ι : ITree) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (envelopeMean (trunc ι n []))

def natPerBit : ℝ≥0∞ := ENNReal.ofReal (Real.log 2)

theorem natPerBit_ne_zero : natPerBit ≠ 0 := by
  exact ne_of_gt (ENNReal.ofReal_pos.mpr (Real.log_pos (by norm_num)))

theorem natPerBit_ne_top : natPerBit ≠ ∞ := ENNReal.ofReal_ne_top

def countableInfiniteCostBits (ι : ITree) : ℝ≥0∞ :=
  countableInfiniteCost ι / natPerBit

theorem ofReal_nats (x : ℝ) :
    ENNReal.ofReal (x * Real.log 2) = ENNReal.ofReal x * natPerBit := by
  exact ENNReal.ofReal_mul' (le_of_lt (Real.log_pos (by norm_num)))

theorem infinite_envelope_sandwich_nats (ι : ITree) :
    infiniteEnvelope ι * natPerBit ≤ countableInfiniteCost ι ∧
    countableInfiniteCost ι ≤
      (infiniteEnvelope ι + ENNReal.ofReal shannonOverhead) * natPerBit := by
  constructor
  · rw [infiniteEnvelope, ENNReal.iSup_mul]
    apply iSup_le
    intro n
    have hlo : ENNReal.ofReal (envelopeMean (trunc ι n []) * Real.log 2) ≤
        countableFiniteCost ι n := by
      apply le_iInf
      intro S
      exact finite_envelope_lower ι n S.val S.property
    rw [ofReal_nats] at hlo
    exact hlo.trans (by
      rw [countable_projective_entropy_identity]
      exact le_iSup (countableFiniteCost ι) n)
  · rw [countable_projective_entropy_identity]
    apply iSup_le
    intro n
    calc
      countableFiniteCost ι n ≤
          ENNReal.ofReal ((envelopeMean (trunc ι n []) + shannonOverhead) * Real.log 2) :=
        finite_envelope_upper ι n
      _ = ENNReal.ofReal (envelopeMean (trunc ι n []) + shannonOverhead) * natPerBit :=
        ofReal_nats _
      _ ≤ (ENNReal.ofReal (envelopeMean (trunc ι n [])) +
          ENNReal.ofReal shannonOverhead) * natPerBit :=
        by gcongr; exact ENNReal.ofReal_add_le
      _ ≤ (infiniteEnvelope ι + ENNReal.ofReal shannonOverhead) * natPerBit :=
        by gcongr; exact le_iSup (fun n => ENNReal.ofReal (envelopeMean (trunc ι n []))) n

/-- The requested infinite-horizon Shannon sandwich, in bits, including ∞. -/
theorem infinite_envelope_sandwich (ι : ITree) :
    infiniteEnvelope ι ≤ countableInfiniteCostBits ι ∧
    countableInfiniteCostBits ι ≤ infiniteEnvelope ι + ENNReal.ofReal shannonOverhead := by
  obtain ⟨hl, hu⟩ := infinite_envelope_sandwich_nats ι
  constructor
  · have h := ENNReal.div_le_div_right hl natPerBit
    simpa [countableInfiniteCostBits,
      ENNReal.mul_div_cancel_right natPerBit_ne_zero natPerBit_ne_top] using h
  · have h := ENNReal.div_le_div_right hu natPerBit
    simpa [countableInfiniteCostBits,
      ENNReal.mul_div_cancel_right natPerBit_ne_zero natPerBit_ne_top] using h

theorem finite_envelope_finite_cost (ι : ITree) (hL : infiniteEnvelope ι ≠ ∞) :
    countableInfiniteCost ι ≠ ∞ := by
  have hu := (infinite_envelope_sandwich_nats ι).2
  have hf : (infiniteEnvelope ι + ENNReal.ofReal shannonOverhead) * natPerBit < ∞ := by
    apply ENNReal.mul_lt_top
    · exact ENNReal.add_lt_top.mpr ⟨lt_top_iff_ne_top.mpr hL, ENNReal.ofReal_lt_top⟩
    · exact ENNReal.ofReal_lt_top
  exact ne_of_lt (lt_of_le_of_lt hu hf)

/-- A single exact countable seed attains the optimum whenever L∞ is finite. -/
theorem infinite_envelope_attained (ι : ITree) (hL : infiniteEnvelope ι ≠ ∞) :
    ∃ S : Seed ι, S.Exact ∧
      S.entropy / natPerBit = countableInfiniteCostBits ι ∧
      S.entropy / natPerBit ≤ infiniteEnvelope ι + ENNReal.ofReal shannonOverhead := by
  have hf := finite_envelope_finite_cost ι hL
  rw [countable_projective_entropy_identity] at hf
  obtain ⟨S, hex, he⟩ := countable_entropy_attained ι hf
  refine ⟨S, hex, ?_, ?_⟩
  · simp [he, countableInfiniteCostBits]
  · simpa [he, countableInfiniteCostBits] using (infinite_envelope_sandwich ι).2

theorem finite_envelope_implies_atomQ_one (ι : ITree) (hL : infiniteEnvelope ι ≠ ∞) :
    atomQ ι = 1 := by
  apply bounded_entropy_implies_atomQ_one ι
  have h := finite_envelope_finite_cost ι hL
  simpa [countableInfiniteCost_eq, projective_entropy_identity] using h

#print axioms countable_projective_entropy_identity
#print axioms infinite_envelope_sandwich
#print axioms infinite_envelope_attained
#print axioms finite_envelope_implies_atomQ_one
end CausalSpectrum.Completion

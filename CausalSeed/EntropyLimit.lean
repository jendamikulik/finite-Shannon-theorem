/-
Countable ranked seeds, the projective entropy identity and attainment.
The seed alphabet is N, with weights in decreasing order (zero padding allowed).
Entropy is in nats. Costs are extended nonnegative reals, so empty feasible
sets and divergent entropy are represented by infinity, never by Real.tsum=0.
-/
import CausalSeed.AtomicCapacity
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Sequences
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic

noncomputable section
open Classical Finset Filter MeasureTheory
open scoped Topology ENNReal
namespace CausalSpectrum.Completion

structure RankedSeed (ι : ITree) where
  weight : ℕ → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  decreasing : Antitone weight
  mass : HasSum weight 1
  strategy : ℕ → IStrategy ι

namespace RankedSeed
variable {ι : ITree}

def head (S : RankedSeed ι) (K : ℕ) : ℝ := ∑ i ∈ range K, S.weight i

def entropyHead (S : RankedSeed ι) (K : ℕ) : ℝ :=
  ∑ i ∈ range K, Real.negMulLog (S.weight i)

def entropy (S : RankedSeed ι) : ℝ≥0∞ :=
  ⨆ K : ℕ, ENNReal.ofReal (S.entropyHead K)

def hit (S : RankedSeed ι) (h : List (ℕ × ℕ)) (i : ℕ) : ℝ :=
  S.weight i * indAgree ι (S.strategy i) h

def miss (S : RankedSeed ι) (h : List (ℕ × ℕ)) (i : ℕ) : ℝ :=
  S.weight i * (1 - indAgree ι (S.strategy i) h)

def ExactTo (S : RankedSeed ι) (n : ℕ) : Prop :=
  ∀ h : List (ℕ × ℕ), h.length ≤ n → ∑' i, S.hit h i = pathMass ι h

def Exact (S : RankedSeed ι) : Prop := ∀ n, S.ExactTo n

theorem weight_le_one (S : RankedSeed ι) (i : ℕ) : S.weight i ≤ 1 :=
  le_hasSum S.mass i (fun j _ => S.nonneg j)

theorem head_le_one (S : RankedSeed ι) (K : ℕ) : S.head K ≤ 1 :=
  sum_le_hasSum (range K) (fun i _ => S.nonneg i) S.mass

theorem entropyHead_nonneg (S : RankedSeed ι) (K : ℕ) :
    0 ≤ S.entropyHead K :=
  Finset.sum_nonneg fun i _ => Real.negMulLog_nonneg (S.nonneg i) (S.weight_le_one i)

theorem entropy_le_iff (S : RankedSeed ι) {B : ℝ} (hB : 0 ≤ B) :
    S.entropy ≤ ENNReal.ofReal B ↔ ∀ K, S.entropyHead K ≤ B := by
  simp only [entropy, iSup_le_iff, ENNReal.ofReal_le_ofReal_iff hB]

theorem entropy_eq_tsum (S : RankedSeed ι) :
    S.entropy = ∑' i, ENNReal.ofReal (Real.negMulLog (S.weight i)) := by
  rw [ENNReal.tsum_eq_iSup_nat]
  unfold entropy entropyHead
  congr 1
  funext K
  exact ENNReal.ofReal_sum_of_nonneg (fun i _ =>
    Real.negMulLog_nonneg (S.nonneg i) (S.weight_le_one i))

theorem rank_bound (S : RankedSeed ι) (K : ℕ) :
    ((K : ℝ) + 1) * S.weight K ≤ 1 := by
  have hh : ∑ i ∈ range (K+1), S.weight K ≤ S.head (K+1) := by
    apply Finset.sum_le_sum
    intro i hi
    exact S.decreasing (by have := Finset.mem_range.mp hi; omega)
  have he : (∑ i ∈ range (K+1), S.weight K) = ((K : ℝ)+1)*S.weight K := by
    simp [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
  rw [he] at hh
  exact hh.trans (S.head_le_one (K+1))

/- The quantitative no-escape estimate. -/
theorem tail_entropy (S : RankedSeed ι) {B : ℝ}
    (hB : ∀ M, S.entropyHead M ≤ B) (K : ℕ) :
    (1 - S.head K) * Real.log ((K : ℝ)+1) ≤ B := by
  have hk : 0 < (K : ℝ)+1 := by positivity
  have term : ∀ j, S.weight (j+K) * Real.log ((K : ℝ)+1) ≤
      Real.negMulLog (S.weight (j+K)) := by
    intro j
    by_cases hz : S.weight (j+K) = 0
    · simp [hz, Real.negMulLog_def]
    · have hw : 0 < S.weight (j+K) := lt_of_le_of_ne (S.nonneg _) (Ne.symm hz)
      have hb : ((K : ℝ)+1) * S.weight (j+K) ≤ 1 :=
        (mul_le_mul_of_nonneg_left (S.decreasing (Nat.le_add_left K j)) hk.le).trans
          (S.rank_bound K)
      have hl := Real.log_le_log (mul_pos hk hw) hb
      rw [Real.log_mul hk.ne' hw.ne', Real.log_one] at hl
      have hm := mul_le_mul_of_nonneg_left hl hw.le
      simp only [Real.negMulLog_def]
      nlinarith
  have finite : ∀ M, (∑ j ∈ range M, S.weight (j+K)) * Real.log ((K : ℝ)+1) ≤ B := by
    intro M
    rw [Finset.sum_mul]
    calc
      (∑ j ∈ range M, S.weight (j+K) * Real.log ((K : ℝ)+1)) ≤
          ∑ j ∈ range M, Real.negMulLog (S.weight (j+K)) :=
        Finset.sum_le_sum fun j _ => term j
      _ ≤ S.entropyHead (K+M) := by
        unfold entropyHead
        rw [Finset.sum_range_add]
        have hn : 0 ≤ ∑ j ∈ range K, Real.negMulLog (S.weight j) :=
          S.entropyHead_nonneg K
        simpa only [Nat.add_comm] using le_add_of_nonneg_left hn
      _ ≤ B := hB (K+M)
  have hs : Summable (fun j => S.weight (j+K)) :=
    (summable_nat_add_iff K).mpr S.mass.summable
  have hlim := hs.hasSum.tendsto_sum_nat.mul_const (Real.log ((K : ℝ)+1))
  have hineq := le_of_tendsto' hlim finite
  have he := S.mass.summable.sum_add_tsum_nat_add K
  rw [S.mass.tsum_eq] at he
  have ht : (∑' j, S.weight (j+K)) = 1 - S.head K := by
    change S.head K + (∑' j, S.weight (j+K)) = 1 at he
    linarith
  simpa [ht] using hineq

theorem hit_nonneg (S : RankedSeed ι) (h) (i) : 0 ≤ S.hit h i :=
  mul_nonneg (S.nonneg i) (indAgree_nonneg ι _ h)

theorem hit_le (S : RankedSeed ι) (h) (i) : S.hit h i ≤ S.weight i := by
  exact mul_le_of_le_one_right (S.nonneg i) (indAgree_le_one ι _ h)

theorem miss_nonneg (S : RankedSeed ι) (h) (i) : 0 ≤ S.miss h i :=
  mul_nonneg (S.nonneg i) (sub_nonneg.mpr (indAgree_le_one ι _ h))

theorem miss_le (S : RankedSeed ι) (h) (i) : S.miss h i ≤ S.weight i := by
  apply mul_le_of_le_one_right (S.nonneg i)
  linarith [indAgree_nonneg ι (S.strategy i) h]

theorem hit_summable (S : RankedSeed ι) (h) : Summable (S.hit h) :=
  summable_of_sum_range_le (S.hit_nonneg h) fun K =>
    (Finset.sum_le_sum (fun i _ => S.hit_le h i)).trans (S.head_le_one K)

theorem miss_summable (S : RankedSeed ι) (h) : Summable (S.miss h) :=
  summable_of_sum_range_le (S.miss_nonneg h) fun K =>
    (Finset.sum_le_sum (fun i _ => S.miss_le h i)).trans (S.head_le_one K)

theorem hit_add_miss (S : RankedSeed ι) (h) :
    (∑' i, S.hit h i) + (∑' i, S.miss h i) = 1 := by
  rw [← (S.hit_summable h).tsum_add (S.miss_summable h)]
  have he : (fun i => S.hit h i + S.miss h i) = S.weight := by
    funext i
    simp only [hit, miss]
    ring
  rw [he, S.mass.tsum_eq]

end RankedSeed

/- The next theorem is the complete analytic compactness step. Its hypotheses
   concern a supplied sequence; no limit seed or no-escape premise is assumed. -/
theorem entropy_compactness (ι : ITree) (S : ℕ → RankedSeed ι)
    (budget : ℕ → ℝ) (B U : ℝ)
    (hbudget : Tendsto budget atTop (𝓝 B))
    (hU : ∀ n, budget n ≤ U)
    (hH : ∀ n K, (S n).entropyHead K ≤ budget n)
    (hex : ∀ n, (S n).ExactTo n) :
    ∃ R : RankedSeed ι, R.Exact ∧ ∀ K, R.entropyHead K ≤ B := by
  let pack : ℕ → (ℕ → Set.Icc (0:ℝ) 1) × (ℕ → IStrategy ι) := fun n =>
    ⟨fun i => ⟨(S n).weight i, (S n).nonneg i, (S n).weight_le_one i⟩,
      (S n).strategy⟩
  obtain ⟨z,φ,hφ,ht⟩ := CompactSpace.tendsto_subseq pack
  let w : ℕ → ℝ := fun i => (z.1 i).val
  let s : ℕ → IStrategy ι := z.2
  have hw : ∀ i, Tendsto (fun n => (S (φ n)).weight i) atTop (𝓝 (w i)) := by
    intro i
    exact ((continuous_subtype_val.comp ((continuous_apply i).comp continuous_fst)).tendsto z).comp ht
  have hs : ∀ i p, Tendsto (fun n => (S (φ n)).strategy i p) atTop (𝓝 (s i p)) := by
    intro i p
    exact (((continuous_apply p).comp ((continuous_apply i).comp continuous_snd)).tendsto z).comp ht
  have wn : ∀ i, 0 ≤ w i := fun i => (z.1 i).property.1
  have wo : ∀ i, w i ≤ 1 := fun i => (z.1 i).property.2
  have wm : Antitone w := by
    intro i j hij
    exact le_of_tendsto_of_tendsto' (hw j) (hw i) (fun n => (S (φ n)).decreasing hij)
  have headlim : ∀ K, Tendsto (fun n => (S (φ n)).head K) atTop
      (𝓝 (∑ i ∈ range K, w i)) := by
    intro K
    exact tendsto_finsetSum (range K) (fun i _ => hw i)
  have headbound : ∀ K, ∑ i ∈ range K, w i ≤ 1 := by
    intro K
    exact le_of_tendsto' (headlim K) (fun n => (S (φ n)).head_le_one K)
  have wsum : Summable w := summable_of_sum_range_le wn headbound
  have wtotal_le : ∑' i, w i ≤ 1 :=
    le_of_tendsto' wsum.hasSum.tendsto_sum_nat headbound
  have tailbound : ∀ K, (1 - ∑ i ∈ range K, w i) * Real.log ((K:ℝ)+1) ≤ U := by
    intro K
    apply le_of_tendsto' ((tendsto_const_nhds.sub (headlim K)).mul_const _)
    intro n
    exact ((S (φ n)).tail_entropy (fun M => (hH (φ n) M).trans (hU (φ n))) K)
  have wtotal : ∑' i, w i = 1 := by
    apply le_antisymm wtotal_le
    by_contra hn
    have hd : 0 < 1 - ∑' i, w i := by linarith
    have hlog : Tendsto (fun K : ℕ => Real.log ((K:ℝ)+1)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right (atTop : Filter ℕ) 1 tendsto_natCast_atTop_atTop)
    obtain ⟨K,hK⟩ := (hlog.eventually (eventually_gt_atTop (U / (1-∑'i,w i)))).exists
    have hh : ∑ i ∈ range K, w i ≤ ∑' i, w i :=
      sum_le_hasSum (range K) (fun i _ => wn i) wsum.hasSum
    have hl : 0 ≤ Real.log ((K:ℝ)+1) := Real.log_nonneg (by
      have hk0 : (0:ℝ) ≤ K := by positivity
      linarith)
    have hmul := mul_le_mul_of_nonneg_right (show 1-(∑'i,w i) ≤ 1-∑i∈range K,w i by linarith) hl
    have hstrict : U < (1-∑'i,w i) * Real.log ((K:ℝ)+1) := by
      have := (div_lt_iff₀ hd).mp hK
      nlinarith
    linarith [tailbound K]
  let R : RankedSeed ι := ⟨w,wn,wm,wtotal ▸ wsum.hasSum,s⟩
  have hRhead : ∀ K, R.entropyHead K ≤ B := by
    intro K
    have he : Tendsto (fun n => (S (φ n)).entropyHead K) atTop (𝓝 (R.entropyHead K)) := by
      apply tendsto_finsetSum
      intro i _
      exact (Real.continuous_negMulLog.tendsto (w i)).comp (hw i)
    exact le_of_tendsto_of_tendsto' he (hbudget.comp hφ.tendsto_atTop)
      (fun n => hH (φ n) K)
  have hind : ∀ i h, ∀ᶠ n in atTop,
      indAgree ι ((S (φ n)).strategy i) h = indAgree ι (R.strategy i) h := by
    intro i h
    have hc : ∀ p, ∀ᶠ n in atTop, (S (φ n)).strategy i p = s i p := by
      intro p
      have hh := hs i p
      rw [nhds_discrete] at hh
      exact tendsto_pure.mp hh
    have hh := eventually_agreesFrom ι hc [] h
    filter_upwards [hh] with n hn
    have hi : iAgree ι ((S (φ n)).strategy i) h ↔ iAgree ι (R.strategy i) h := by
      simpa only [iAgree_iff] using hn
    simp only [indAgree, hi]
  have hhit : ∀ h K, Tendsto (fun n => ∑ i ∈ range K, (S (φ n)).hit h i)
      atTop (𝓝 (∑ i ∈ range K, R.hit h i)) := by
    intro h K
    apply tendsto_finsetSum
    intro i _
    have ht' := (hw i).mul (tendsto_const_nhds (x := indAgree ι (R.strategy i) h))
    exact ht'.congr' ((hind i h).mono (fun n hn => by simp [RankedSeed.hit,hn]))
  have hmiss : ∀ h K, Tendsto (fun n => ∑ i ∈ range K, (S (φ n)).miss h i)
      atTop (𝓝 (∑ i ∈ range K, R.miss h i)) := by
    intro h K
    apply tendsto_finsetSum
    intro i _
    have ht' := (hw i).mul (tendsto_const_nhds (x := 1-indAgree ι (R.strategy i) h))
    exact ht'.congr' ((hind i h).mono (fun n hn => by simp [RankedSeed.miss,hn]))
  have hb : ∀ h K, (∑ i ∈ range K, R.hit h i) ≤ pathMass ι h ∧
      (∑ i ∈ range K, R.miss h i) ≤ 1-pathMass ι h := by
    intro h K
    have hevent : ∀ᶠ n in atTop, h.length ≤ φ n :=
      hφ.tendsto_atTop.eventually (eventually_ge_atTop h.length)
    constructor
    · apply le_of_tendsto (hhit h K)
      filter_upwards [hevent] with n hn
      rw [← hex (φ n) h hn]
      exact sum_le_hasSum _ (fun i _ => (S (φ n)).hit_nonneg h i)
        ((S (φ n)).hit_summable h).hasSum
    · apply le_of_tendsto (hmiss h K)
      filter_upwards [hevent] with n hn
      have he := (S (φ n)).hit_add_miss h
      rw [hex (φ n) h hn] at he
      have hsum := sum_le_hasSum (range K) (fun i _ => (S (φ n)).miss_nonneg h i)
        ((S (φ n)).miss_summable h).hasSum
      linarith
  refine ⟨R, ?_, hRhead⟩
  intro n h _
  have hleft := le_of_tendsto' (R.hit_summable h).hasSum.tendsto_sum_nat
    (fun K => (hb h K).1)
  have hright := le_of_tendsto' (R.miss_summable h).hasSum.tendsto_sum_nat
    (fun K => (hb h K).2)
  linarith [R.hit_add_miss h]

/- Both optimizations use the same canonical seed alphabet. ExactTo imposes
   only finite-horizon constraints; arbitrary strategies beyond that horizon
   do not alter its cost or its constraints. -/
def finiteCost (ι : ITree) (n : ℕ) : ℝ≥0∞ :=
  ⨅ S : {S : RankedSeed ι // S.ExactTo n}, S.val.entropy

def infiniteCost (ι : ITree) : ℝ≥0∞ :=
  ⨅ S : {S : RankedSeed ι // S.Exact}, S.val.entropy

theorem finiteCost_mono (ι : ITree) : Monotone (finiteCost ι) := by
  intro m n hmn
  unfold finiteCost
  refine le_iInf fun S => ?_
  have hto : S.1.ExactTo m := by
    intro h hh
    exact S.2 h (hh.trans hmn)
  exact iInf_le (fun T : {T : RankedSeed ι // T.ExactTo m} => T.1.entropy) ⟨S.1, hto⟩

theorem finiteCost_le_infiniteCost (ι : ITree) (n : ℕ) :
    finiteCost ι n ≤ infiniteCost ι := by
  apply le_iInf
  intro S
  exact iInf_le_of_le ⟨S.val,S.property n⟩ le_rfl

theorem finiteCost_le_seed (ι : ITree) (n : ℕ) (S : RankedSeed ι)
    (hS : S.ExactTo n) : finiteCost ι n ≤ S.entropy :=
  iInf_le_of_le ⟨S,hS⟩ le_rfl

/- Attainment is proved, not included in the definition of finiteCost. -/
theorem entropy_attained (ι : ITree) (hfinite : (⨆ n, finiteCost ι n) ≠ ∞) :
    ∃ S : RankedSeed ι, S.Exact ∧ S.entropy = ⨆ n, finiteCost ι n := by
  let L : ℝ≥0∞ := ⨆ n, finiteCost ι n
  let B : ℝ := L.toReal
  let budget : ℕ → ℝ := fun n => B + 1 / ((n:ℝ)+1)
  have hB : 0 ≤ B := ENNReal.toReal_nonneg
  have hL : ENNReal.ofReal B = L := ENNReal.ofReal_toReal hfinite
  have chooseSeed : ∀ n, ∃ S : RankedSeed ι,
      S.ExactTo n ∧ ∀ K, S.entropyHead K ≤ budget n := by
    intro n
    have hpos : 0 < 1 / ((n:ℝ)+1) := by positivity
    have hb : L < ENNReal.ofReal (budget n) := by
      rw [← hL]
      apply (ENNReal.ofReal_lt_ofReal_iff (by dsimp [budget]; linarith)).mpr
      dsimp [budget]
      linarith
    have hc : finiteCost ι n < ENNReal.ofReal (budget n) :=
      (le_iSup (fun n => finiteCost ι n) n).trans_lt hb
    obtain ⟨S,hS⟩ := iInf_lt_iff.mp hc
    exact ⟨S.val,S.property,(S.val.entropy_le_iff (by dsimp [budget]; positivity)).mp hS.le⟩
  choose S hS hH using chooseSeed
  have ht : Tendsto budget atTop (𝓝 B) := by
    have hi : Tendsto (fun n : ℕ => 1 / ((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) := by
      exact tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right (atTop : Filter ℕ) 1 tendsto_natCast_atTop_atTop)
    simpa only [add_zero] using tendsto_const_nhds.add hi
  have hU : ∀ n, budget n ≤ B+1 := by
    intro n
    dsimp [budget]
    have hh : 1 / ((n:ℝ)+1) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).mpr
      have hn0 : (0:ℝ) ≤ n := by positivity
      nlinarith
    linarith
  obtain ⟨R,hex,hR⟩ := entropy_compactness ι S budget B (B+1) ht hU hH hS
  refine ⟨R, hex, le_antisymm ?_ ?_⟩
  · suffices R.entropy ≤ ENNReal.ofReal B by simpa [hL] using this
    exact (R.entropy_le_iff hB).mpr hR
  · apply iSup_le
    intro n
    exact finiteCost_le_seed ι n R (hex n)

theorem projective_entropy_identity (ι : ITree) :
    infiniteCost ι = ⨆ n, finiteCost ι n := by
  have lower : (⨆ n, finiteCost ι n) ≤ infiniteCost ι :=
    iSup_le (finiteCost_le_infiniteCost ι)
  by_cases htop : (⨆ n, finiteCost ι n) = ∞
  · apply le_antisymm _ lower
    rw [htop]
    exact le_top
  · obtain ⟨S,hS,hH⟩ := entropy_attained ι htop
    apply le_antisymm _ lower
    rw [← hH]
    exact iInf_le_of_le ⟨S,hS⟩ le_rfl

/- The optimal seed is realized as a probability measure, not only a list. -/
def RankedSeed.measure {ι : ITree} (S : RankedSeed ι) : Measure (IStrategy ι) :=
  Measure.sum fun i => ENNReal.ofReal (S.weight i) • Measure.dirac (S.strategy i)

instance RankedSeed.measure_probability {ι : ITree} (S : RankedSeed ι) :
    IsProbabilityMeasure S.measure :=
  HasSum.isProbabilityMeasure_sum_dirac S.nonneg S.mass

theorem RankedSeed.measure_cylinder {ι : ITree} (S : RankedSeed ι)
    (hex : S.Exact) (h : List (ℕ × ℕ)) :
    S.measure (cylinder ι h) = ENNReal.ofReal (pathMass ι h) := by
  rw [← hex h.length h le_rfl, RankedSeed.measure,
    Measure.sum_apply _ (measurable_cylinder ι h),
    ENNReal.ofReal_tsum_of_nonneg (S.hit_nonneg h) (S.hit_summable h)]
  apply tsum_congr
  intro i
  by_cases hi : iAgree ι (S.strategy i) h
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurable_cylinder ι h),
      cylinder, RankedSeed.hit, indAgree, hi]
  · simp [Measure.smul_apply, Measure.dirac_apply' _ (measurable_cylinder ι h),
      cylinder, RankedSeed.hit, indAgree, hi]

theorem bounded_entropy_implies_atomQ_one (ι : ITree)
    (hfinite : (⨆ n, finiteCost ι n) ≠ ∞) : atomQ ι = 1 := by
  obtain ⟨S,hex,_⟩ := entropy_attained ι hfinite
  apply (countable_seed_iff_atomQ_one ι).mp
  refine ⟨S.weight,S.strategy,S.nonneg,S.mass,?_⟩
  intro h
  exact hex h.length h le_rfl

#print axioms entropy_compactness
#print axioms entropy_attained
#print axioms projective_entropy_identity
#print axioms RankedSeed.measure_cylinder
#print axioms bounded_entropy_implies_atomQ_one
end CausalSpectrum.Completion
end

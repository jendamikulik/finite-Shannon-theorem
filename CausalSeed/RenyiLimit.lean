/-
Rényi spectrum, stage 4: the Lemma 2 limit seed.

For each horizon `n` take the ranked greedy seed `G_n` of `trunc ι n`.  If an
ordinary exact source exists, the stochastic sandwich `J_n ≼st Z_n + W` and
`Z_n ≼st I_U` give tightness of the ranked weights, uniformly in `n`:
`∑_{k ≥ K} r_{n,k} ≤ P(I_U > t/2) + P(W > t/2)` for `K ≥ 2^t`.
A diagonal subsequence (compactness of `[0,1]^ℕ × strategies^ℕ`) then converges to
a ranked seed `R` that is exact at every horizon; tightness keeps the full mass.
Power sums pass to the limit: Fatou for `α ≤ 1`, and with tightness for `α ≥ 1`;
Shannon heads pass to the limit for `α = 1`.
-/
import CausalSeed.RenyiSource

noncomputable section
open Classical Finset Filter
open scoped ENNReal Topology
namespace CausalSpectrum.RenyiInf
open CausalSpectrum.Completion

/-! ### The noise survival function `P(W > s)` -/

theorem wS_nonneg (s : ℝ) : 0 ≤ wSurvival s := by
  unfold wSurvival; split_ifs <;> positivity

theorem rpow_neg_le_half {s : ℝ} (hs : 1 ≤ s) : (2:ℝ) ^ (-s) ≤ 1 / 2 := by
  rw [show (1:ℝ)/2 = 2 ^ (-1:ℝ) by norm_num]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

theorem wS_le_one (s : ℝ) : wSurvival s ≤ 1 := by
  unfold wSurvival
  split_ifs with h1 h2
  · exact le_rfl
  · norm_num
  · linarith [rpow_neg_le_half (not_lt.mp h2)]

theorem wS_anti : Antitone wSurvival := by
  intro a b hab
  unfold wSurvival
  split_ifs <;> (try simp only [not_le, not_lt] at *) <;> first
    | linarith
    | linarith [rpow_neg_le_half (show 1 ≤ b by linarith)]
    | exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    | norm_num

theorem wS_tendsto : Tendsto wSurvival atTop (𝓝 0) := by
  have h : Tendsto (fun s : ℝ => (2:ℝ) ^ (-s)) atTop (𝓝 0) := by
    simp_rw [Renyi.rpow_two_eq]
    apply Real.tendsto_exp_atBot.comp
    simp_rw [mul_neg]
    exact tendsto_neg_atTop_atBot.comp
      (tendsto_id.const_mul_atTop (Real.log_pos (by norm_num : (1:ℝ) < 2)))
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with s hs
  unfold wSurvival
  rw [if_neg (by linarith), if_neg (by linarith)]

/-- `P(Z + W > t) ≤ P(Z > t/2) + P(W > t/2)` for the finite envelope variable. -/
theorem zw_split (T : Tree) (t : ℝ) :
    ∑ i ∈ Finset.range (infoValues T).length, envInc T i * wSurvival (t - Renyi.zval T i) ≤
      (1 - Fstar T (t / 2)) + wSurvival (t / 2) := by
  rw [Renyi.one_sub_Fstar_eq]
  calc _ ≤ ∑ i ∈ Finset.range (infoValues T).length,
        ((if t / 2 < Renyi.zval T i then envInc T i else 0) + envInc T i * wSurvival (t / 2)) :=
        Finset.sum_le_sum fun i _ => by
          have he := envInc_nonneg T i
          split_ifs with h
          · nlinarith [wS_le_one (t - Renyi.zval T i), wS_nonneg (t / 2)]
          · have := wS_anti (show t / 2 ≤ t - Renyi.zval T i by linarith)
            nlinarith
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.sum_mul, Renyi.sum_envInc, one_mul]

/-! ### Ranked greedy seeds -/

namespace CountableSeed'
variable {ι : ITree}

theorem ranked_tsum_enn (G : CountableSeed ι) (f : ℝ → ℝ≥0∞) (hf : f 0 = 0) :
    ∑' k, f (G.rankedWeight k) = ∑' i, f (G.weight i) := by
  have h := (G.relabel (fun i => f (G.weight i)) (fun i hi => by simp [hi, hf]) _).mp
    ENNReal.summable.hasSum
  refine HasSum.tsum_eq ?_
  convert h using 1
  funext k; unfold CountableSeed.rankedWeight; split_ifs <;> simp [hf]

theorem ranked_tsum_real (G : CountableSeed ι) (f : ℝ → ℝ) (hf : f 0 = 0)
    (hs : Summable fun i => f (G.weight i)) :
    HasSum (fun k => f (G.rankedWeight k)) (∑' i, f (G.weight i)) := by
  have h := (G.relabel (fun i => f (G.weight i)) (fun i hi => by simp [hi, hf]) _).mp hs.hasSum
  convert h using 1
  funext k; unfold CountableSeed.rankedWeight; split_ifs <;> simp [hf]

end CountableSeed'

open CountableSeed'

variable {ι : ITree}

/-- The ranked greedy seed of horizon `n`. -/
def gr (ι : ITree) (n : ℕ) : RankedSeed ι := (greedySeed ι n).ranked

theorem gr_exactTo (ι : ITree) (n : ℕ) : (gr ι n).ExactTo n :=
  ((greedySeed ι n).ranked_exactTo_iff n).mpr (greedySeed_exactTo ι n)

theorem gr_weight (ι : ITree) (n : ℕ) : (gr ι n).weight = (greedySeed ι n).rankedWeight := rfl

/-- A list sum over the greedy atoms, as a series over `gWeight`. -/
theorem tsum_gWeight (ι : ITree) (n : ℕ) (g : ℝ → ℝ) (hg : g 0 = 0) :
    HasSum (fun i => g (gWeight ι n i)) ((greedyList (trunc ι n [])).map fun a => g a.1).sum := by
  set L := (greedyList (trunc ι n [])).length
  have hz : ∀ i ∉ range L, g (gWeight ι n i) = 0 := fun i hi => by
    rw [gWeight_zero_of_ge ι n i (by simpa [L] using hi), hg]
  have h : HasSum (fun i => g (gWeight ι n i)) (∑ i ∈ range L, g (gWeight ι n i)) :=
    hasSum_sum_of_ne_finset_zero hz
  convert h using 1
  simp_rw [gWeight_eq]
  exact (sum_range_atomWeight g _).symm

theorem gr_hasSum (ι : ITree) (n : ℕ) (g : ℝ → ℝ) (hg : g 0 = 0) :
    HasSum (fun k => g ((gr ι n).weight k)) ((greedyList (trunc ι n [])).map fun a => g a.1).sum := by
  have h := tsum_gWeight ι n g hg
  have := ranked_tsum_real (greedySeed ι n) g hg h.summable
  have e : (∑' i, g ((greedySeed ι n).weight i)) = _ := h.tsum_eq
  rw [e] at this
  exact this

theorem gr_mom (ι : ITree) (n : ℕ) {α : ℝ} (hα : 0 < α) :
    mom α (gr ι n).weight =
      ENNReal.ofReal ((greedyList (trunc ι n [])).map fun a => a.1 ^ α).sum := by
  have h := gr_hasSum ι n (fun x => x ^ α) (Real.zero_rpow hα.ne')
  unfold mom
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => Real.rpow_nonneg ((gr ι n).nonneg k) _)
    h.summable, h.tsum_eq]

theorem gr_entropyHead (ι : ITree) (n K : ℕ) :
    (gr ι n).entropyHead K ≤ Real.log 2 * seedShannon (greedyList (trunc ι n [])) := by
  have hE : (gr ι n).entropy = ENNReal.ofReal (Real.log 2 * seedShannon (greedyList (trunc ι n []))) := by
    rw [gr, CountableSeed.ranked_entropy, greedySeed_entropy]
  have hnn : 0 ≤ Real.log 2 * seedShannon (greedyList (trunc ι n [])) := by
    obtain ⟨hpos, hle, -, -⟩ := Renyi.trace_data (greedyList_trace (trunc ι n []))
    refine mul_nonneg (Real.log_nonneg (by norm_num)) (List.sum_nonneg fun x hx => ?_)
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
    refine mul_nonneg (hpos a ha).le ?_
    have := Real.logb_nonpos (b := 2) (by norm_num) (hpos a ha).le (hle a ha)
    simp only [infoMass]; linarith
  exact ((gr ι n).entropy_le_iff hnn).mp hE.le K

/-! ### Tightness -/

theorem rank_le (S : RankedSeed ι) (k : ℕ) : S.weight k ≤ 1 / ((k:ℝ) + 1) := by
  have h : ((k:ℝ) + 1) * S.weight k ≤ 1 := by
    have h1 : ∑ i ∈ range (k + 1), S.weight k ≤ ∑ i ∈ range (k + 1), S.weight i :=
      Finset.sum_le_sum fun i hi => S.decreasing (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
    have h2 := S.head_le_one (k + 1)
    simp only [RankedSeed.head] at h2
    simp at h1
    push_cast at h1
    linarith
  rw [le_div_iff₀ (by positivity)]; linarith [h]

theorem tail_le_info (S : RankedSeed ι) (t : ℝ) (K : ℕ) (hK : (2:ℝ) ^ t < K + 1) :
    1 - S.head K ≤ ∑' k, if t < infoMass (S.weight k) then S.weight k else 0 := by
  set A : ℕ → ℝ := fun k => if t < infoMass (S.weight k) then S.weight k else 0
  set B : ℕ → ℝ := fun k => if t < infoMass (S.weight k) then 0 else S.weight k
  have hA : Summable A := Summable.of_nonneg_of_le (fun k => by simp only [A]; split_ifs <;> simp [S.nonneg])
    (fun k => by simp only [A]; split_ifs <;> simp [S.nonneg]) S.mass.summable
  have hB : Summable B := Summable.of_nonneg_of_le (fun k => by simp only [B]; split_ifs <;> simp [S.nonneg])
    (fun k => by simp only [B]; split_ifs <;> simp [S.nonneg]) S.mass.summable
  have hsum : ∑' k, A k + ∑' k, B k = 1 := by
    rw [← hA.tsum_add hB, ← S.mass.tsum_eq]
    exact tsum_congr fun k => by simp only [A, B]; split_ifs <;> simp
  have hz : ∀ k ∉ range K, B k = 0 := by
    intro k hk
    have hk' : K ≤ k := by simpa using hk
    simp only [B]
    by_cases h0 : S.weight k = 0
    · simp [h0]
    have hp : 0 < S.weight k := lt_of_le_of_ne (S.nonneg k) (Ne.symm h0)
    have hlt : S.weight k < (2:ℝ) ^ (-t) := by
      rw [Real.rpow_neg (by norm_num)]
      have h2 : 0 < (2:ℝ) ^ t := Real.rpow_pos_of_pos (by norm_num) t
      calc S.weight k ≤ 1 / ((k:ℝ) + 1) := rank_le S k
        _ ≤ 1 / ((K:ℝ) + 1) := by
          apply one_div_le_one_div_of_le (by positivity); exact_mod_cast Nat.succ_le_succ hk'
        _ < ((2:ℝ) ^ t)⁻¹ := by rw [one_div]; exact inv_strictAnti₀ h2 hK
    rw [if_pos ((weight_lt_dyadic_iff hp).mp hlt)]
  have hBK : ∑' k, B k ≤ S.head K := by
    rw [tsum_eq_sum hz]
    exact Finset.sum_le_sum fun k _ => by simp only [B]; split_ifs <;> simp [S.nonneg]
  linarith

theorem gr_tail (ι : ITree) (n : ℕ) (t : ℝ) :
    ∑' k, (if t < infoMass ((gr ι n).weight k) then (gr ι n).weight k else 0) =
      seedTail (greedyList (trunc ι n [])) t := by
  have h := gr_hasSum ι n (fun x => if t < infoMass x then x else 0) (by simp)
  rw [h.tsum_eq]
  unfold seedTail
  congr 1

/-- **Uniform tightness** of the ranked greedy seeds, given one ordinary exact source. -/
theorem tight (U : OrdSource ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, ∀ n, 1 - (gr ι n).head K ≤ ε := by
  have hlim := (OrdSource.tailU_tendsto U.law).add wS_tendsto
  rw [add_zero] at hlim
  obtain ⟨s0, hs0⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hε))
  set s := max s0 0
  set t := 2 * s
  refine ⟨⌈(2:ℝ) ^ t⌉₊, fun n => ?_⟩
  have hK : (2:ℝ) ^ t < (⌈(2:ℝ) ^ t⌉₊ : ℝ) + 1 := by
    have := Nat.le_ceil ((2:ℝ) ^ t); linarith
  have h1 := tail_le_info (gr ι n) t _ hK
  rw [gr_tail] at h1
  have h2 := Renyi.trace_tail_upper (greedyList_trace (trunc ι n [])) t
  have h3 := zw_split (trunc ι n []) t
  have h4 := OrdSource.one_sub_Fstar_le U n (t / 2)
  have ht2 : t / 2 = s := by simp only [t]; ring
  rw [ht2] at h3 h4
  have h5 := hs0 s (le_max_left _ _)
  linarith

/-! ### The diagonal limit -/

/-- **Lemma 2 (limit seed).**  A tight sequence of ranked seeds, the `n`-th exact to
horizon `n`, has a pointwise convergent subsequence whose limit is a ranked seed of
total mass one, exact at every horizon. -/
theorem limit_seed (S : ℕ → RankedSeed ι) (hex : ∀ n, (S n).ExactTo n)
    (htight : ∀ ε > 0, ∃ K, ∀ n, 1 - (S n).head K ≤ ε) :
    ∃ (R : RankedSeed ι) (φ : ℕ → ℕ), StrictMono φ ∧
      (∀ i, Tendsto (fun n => (S (φ n)).weight i) atTop (𝓝 (R.weight i))) ∧ R.Exact := by
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
  have wtotal : ∑' i, w i = 1 := by
    apply le_antisymm wtotal_le
    by_contra hn
    push_neg at hn
    have hd : 0 < (1 - ∑' i, w i) / 2 := by linarith
    obtain ⟨K, hK⟩ := htight _ hd
    have hge : 1 - (1 - ∑' i, w i) / 2 ≤ ∑ i ∈ range K, w i :=
      ge_of_tendsto' (headlim K) (fun n => by linarith [hK (φ n)])
    have hh : ∑ i ∈ range K, w i ≤ ∑' i, w i :=
      sum_le_hasSum (range K) (fun i _ => wn i) wsum.hasSum
    linarith
  let R : RankedSeed ι := ⟨w,wn,wm,wtotal ▸ wsum.hasSum,s⟩
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
  refine ⟨R, φ, hφ, hw, ?_⟩
  intro n h _
  have hleft := le_of_tendsto' (R.hit_summable h).hasSum.tendsto_sum_nat
    (fun K => (hb h K).1)
  have hright := le_of_tendsto' (R.miss_summable h).hasSum.tendsto_sum_nat
    (fun K => (hb h K).2)
  linarith [R.hit_add_miss h]

/-! ### Passing power sums and Shannon heads to the limit -/

theorem rlaw (R : RankedSeed ι) : IsLaw R.weight := ⟨R.nonneg, R.mass⟩

section Lim
variable {S : ℕ → RankedSeed ι} {R : RankedSeed ι} {φ : ℕ → ℕ}
  (hw : ∀ i, Tendsto (fun n => (S (φ n)).weight i) atTop (𝓝 (R.weight i)))
include hw

/-- Fatou, any `α > 0`. -/
theorem lim_mom_le {α : ℝ} (hα : 0 < α) {B : ℝ≥0∞} (hB : ∀ n, mom α (S n).weight ≤ B) :
    mom α R.weight ≤ B := by
  unfold mom
  refine ENNReal.tsum_le_of_sum_range_le fun K => ?_
  have ht : Tendsto (fun n => ∑ i ∈ range K, ENNReal.ofReal ((S (φ n)).weight i ^ α)) atTop
      (𝓝 (∑ i ∈ range K, ENNReal.ofReal (R.weight i ^ α))) :=
    tendsto_finsetSum _ fun i _ =>
      ENNReal.tendsto_ofReal (((Real.continuous_rpow_const hα.le).tendsto _).comp (hw i))
  exact le_of_tendsto' ht fun n => (ENNReal.sum_le_tsum _).trans (hB (φ n))

/-- With tightness, `α ≥ 1`. -/
theorem lim_mom_ge (htight : ∀ ε > 0, ∃ K, ∀ n, 1 - (S n).head K ≤ ε) {α : ℝ} (hα : 1 ≤ α)
    {B : ℝ} (hB : ∀ n, B ≤ ∑' i, (S n).weight i ^ α) : B ≤ ∑' i, R.weight i ^ α := by
  have hα0 : 0 < α := by linarith
  by_contra hn
  push_neg at hn
  have hd : 0 < (B - ∑' i, R.weight i ^ α) / 2 := by linarith
  obtain ⟨K, hK⟩ := htight _ hd
  have hsR := (pow_tsum_ge (rlaw R).nonneg R.mass.summable hα).1
  have hpart : ∀ n, B - (B - ∑' i, R.weight i ^ α) / 2 ≤ ∑ i ∈ range K, (S n).weight i ^ α := by
    intro n
    have hs := (pow_tsum_ge (rlaw (S n)).nonneg (S n).mass.summable hα).1
    have hd' : Summable fun i => (S n).weight i - (S n).weight i ^ α :=
      (S n).mass.summable.sub hs
    have h1 : ∑ i ∈ range K, ((S n).weight i - (S n).weight i ^ α) ≤
        ∑' i, ((S n).weight i - (S n).weight i ^ α) :=
      sum_le_hasSum _ (fun i _ => by
        linarith [rpow_le_self ((S n).nonneg i) ((S n).weight_le_one i) hα]) hd'.hasSum
    rw [Summable.tsum_sub (S n).mass.summable hs, (S n).mass.tsum_eq,
      Finset.sum_sub_distrib] at h1
    have := hK n
    simp only [RankedSeed.head] at this
    linarith [hB n]
  have hlim : Tendsto (fun n => ∑ i ∈ range K, (S (φ n)).weight i ^ α) atTop
      (𝓝 (∑ i ∈ range K, R.weight i ^ α)) :=
    tendsto_finsetSum _ fun i _ => ((Real.continuous_rpow_const hα0.le).tendsto _).comp (hw i)
  have h2 := ge_of_tendsto' hlim (fun n => hpart (φ n))
  have h3 : ∑ i ∈ range K, R.weight i ^ α ≤ ∑' i, R.weight i ^ α :=
    sum_le_hasSum _ (fun i _ => Real.rpow_nonneg (R.nonneg i) _) hsR.hasSum
  linarith

theorem lim_head_le {c : ℝ} (hc : ∀ n K, (S n).entropyHead K ≤ c) (K : ℕ) :
    R.entropyHead K ≤ c := by
  have he : Tendsto (fun n => (S (φ n)).entropyHead K) atTop (𝓝 (R.entropyHead K)) :=
    tendsto_finsetSum _ fun i _ => (Real.continuous_negMulLog.tendsto _).comp (hw i)
  exact le_of_tendsto' he fun n => hc (φ n) K

end Lim

#print axioms tight
#print axioms limit_seed
#print axioms lim_mom_ge

end CausalSpectrum.RenyiInf

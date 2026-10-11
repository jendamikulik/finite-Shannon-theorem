/-
General countable seeds and their ranked rearrangement.
A countable seed is an arbitrary labeling of atoms by ℕ: weights are
nonnegative, sum to one, may vanish, and need not be ordered.
The ranked seed is obtained by relabeling exactly the positive atoms in
decreasing order of weight (ties broken by the original label), padding with
zero weights. No limit of finite approximations is used.
The relabeling preserves every cylinder sum, the seed measure (hence every
law), and the entropy in [0,∞] (nats).
-/
import CausalSeed.EntropyLimit
import Mathlib.Data.Nat.Nth

noncomputable section
open Classical Finset Filter MeasureTheory
open scoped Topology ENNReal
namespace CausalSpectrum.Completion

/-- A general countable seed: an arbitrary labeling of atoms. -/
structure CountableSeed (ι : ITree) where
  weight : ℕ → ℝ
  nonneg : ∀ i, 0 ≤ weight i
  mass : HasSum weight 1
  strategy : ℕ → IStrategy ι

namespace CountableSeed
variable {ι : ITree}

/-- Entropy in nats, as an extended sum; zero atoms contribute nothing. -/
def entropy (G : CountableSeed ι) : ℝ≥0∞ :=
  ∑' i, ENNReal.ofReal (Real.negMulLog (G.weight i))

def hit (G : CountableSeed ι) (h : List (ℕ × ℕ)) (i : ℕ) : ℝ :=
  G.weight i * indAgree ι (G.strategy i) h

def ExactTo (G : CountableSeed ι) (n : ℕ) : Prop :=
  ∀ h : List (ℕ × ℕ), h.length ≤ n → ∑' i, G.hit h i = pathMass ι h

def Exact (G : CountableSeed ι) : Prop := ∀ n, G.ExactTo n

def measure (G : CountableSeed ι) : Measure (IStrategy ι) :=
  countableMeasure ι G.weight G.strategy

theorem weight_le_one (G : CountableSeed ι) (i : ℕ) : G.weight i ≤ 1 :=
  le_hasSum G.mass i (fun j _ => G.nonneg j)

theorem hit_nonneg (G : CountableSeed ι) (h) (i) : 0 ≤ G.hit h i :=
  mul_nonneg (G.nonneg i) (indAgree_nonneg ι _ h)

theorem hit_le (G : CountableSeed ι) (h) (i) : G.hit h i ≤ G.weight i :=
  mul_le_of_le_one_right (G.nonneg i) (indAgree_le_one ι _ h)

theorem hit_summable (G : CountableSeed ι) (h) : Summable (G.hit h) :=
  Summable.of_nonneg_of_le (G.hit_nonneg h) (G.hit_le h) G.mass.summable

end CountableSeed

/-- Every ranked seed is a countable seed with the same data. -/
def RankedSeed.toCountable {ι : ITree} (S : RankedSeed ι) : CountableSeed ι :=
  ⟨S.weight, S.nonneg, S.mass, S.strategy⟩

theorem RankedSeed.toCountable_entropy {ι : ITree} (S : RankedSeed ι) :
    S.toCountable.entropy = S.entropy := by
  rw [S.entropy_eq_tsum]; rfl

theorem RankedSeed.toCountable_exactTo {ι : ITree} (S : RankedSeed ι) (n : ℕ) :
    S.toCountable.ExactTo n ↔ S.ExactTo n := Iff.rfl

/-! ## The rank of a positive atom -/

namespace Rank

variable (w : ℕ → ℝ)

/-- `prec w j i`: atom `j` comes strictly before atom `i`. -/
def prec (j i : ℕ) : Prop := w i < w j ∨ (w j = w i ∧ j < i)

variable {w}

theorem prec_trans {i j k : ℕ} (h1 : prec w i j) (h2 : prec w j k) : prec w i k := by
  unfold prec at *
  rcases h1 with h1 | ⟨h1, h1'⟩ <;> rcases h2 with h2 | ⟨h2, h2'⟩
  · left; linarith
  · left; linarith
  · left; linarith
  · right; exact ⟨by linarith, by omega⟩

theorem prec_irrefl (i : ℕ) : ¬ prec w i i := by
  simp [prec]

theorem prec_total {i j : ℕ} (hij : i ≠ j) : prec w i j ∨ prec w j i := by
  unfold prec
  rcases lt_trichotomy (w i) (w j) with h | h | h
  · right; left; exact h
  · rcases Nat.lt_or_gt_of_ne hij with h' | h'
    · left; right; exact ⟨h, h'⟩
    · right; right; exact ⟨h.symm, h'⟩
  · left; left; exact h

theorem prec_weight {i j : ℕ} (h : prec w j i) : w i ≤ w j := by
  rcases h with h | ⟨h, _⟩
  · exact h.le
  · exact h.ge

def pred (w : ℕ → ℝ) (i : ℕ) : Set ℕ := {j | prec w j i}

theorem pred_finite (hs : Summable w) {i : ℕ} (hi : 0 < w i) : (pred w i).Finite := by
  have hev : ∀ᶠ j in cofinite, w j < w i :=
    hs.tendsto_cofinite_zero.eventually (gt_mem_nhds hi)
  rw [Filter.eventually_cofinite] at hev
  refine hev.subset ?_
  intro j hj
  have := prec_weight (w := w) hj
  simp only [Set.mem_setOf_eq, not_lt]
  exact this

def rank (w : ℕ → ℝ) (i : ℕ) : ℕ := (pred w i).ncard

theorem rank_lt (hs : Summable w) {i j : ℕ} (hi : 0 < w i) (h : prec w j i) :
    rank w j < rank w i := by
  have hsub : pred w j ⊆ pred w i := fun k hk => prec_trans hk h
  have hss : pred w j ⊂ pred w i := by
    rw [Set.ssubset_iff_subset_ne]
    refine ⟨hsub, fun he => ?_⟩
    have hj : j ∈ pred w i := h
    rw [← he] at hj
    exact prec_irrefl j hj
  exact Set.ncard_lt_ncard hss (pred_finite hs hi)

theorem rank_injOn (hs : Summable w) {i j : ℕ} (hi : 0 < w i) (hj : 0 < w j)
    (h : rank w i = rank w j) : i = j := by
  by_contra hij
  rcases prec_total (w := w) hij with hp | hp
  · have := rank_lt hs hj hp; omega
  · have := rank_lt hs hi hp; omega

/-- The set of ranks actually used by positive atoms. -/
def used (w : ℕ → ℝ) (k : ℕ) : Prop := ∃ i, 0 < w i ∧ rank w i = k

/-- Position `n` of the ranked list is occupied. -/
def Valid (w : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ hf : (Set.ofPred (used w)).Finite, n < hf.toFinset.card

/-- The original label placed at position `n`. -/
def idx (w : ℕ → ℝ) (n : ℕ) : ℕ :=
  if h : used w (Nat.nth (used w) n) then Classical.choose h else 0

theorem idx_spec {n : ℕ} (hn : Valid w n) :
    0 < w (idx w n) ∧ rank w (idx w n) = Nat.nth (used w) n := by
  have hm : used w (Nat.nth (used w) n) := Nat.nth_mem n hn
  simp only [idx, dif_pos hm]
  exact Classical.choose_spec hm

theorem valid_of_le {n m : ℕ} (hm : Valid w m) (h : n ≤ m) : Valid w n :=
  fun hf => lt_of_le_of_lt h (hm hf)

theorem idx_injOn {n m : ℕ} (hn : Valid w n) (hm : Valid w m)
    (h : idx w n = idx w m) : n = m := by
  have e : Nat.nth (used w) n = Nat.nth (used w) m := by
    rw [← (idx_spec hn).2, ← (idx_spec hm).2, h]
  rcases lt_trichotomy n m with hl | hl | hl
  · have := Nat.nth_lt_nth' hl hm; omega
  · exact hl
  · have := Nat.nth_lt_nth' hl hn; omega

theorem idx_surj (hs : Summable w) {i : ℕ} (hi : 0 < w i) :
    ∃ n, Valid w n ∧ idx w n = i := by
  obtain ⟨n, hn, he⟩ := Nat.exists_lt_card_nth_eq (p := used w) ⟨i, hi, rfl⟩
  refine ⟨n, hn, ?_⟩
  obtain ⟨h1, h2⟩ := idx_spec hn
  exact rank_injOn hs h1 hi (h2.trans he)

theorem idx_anti (hs : Summable w) {n m : ℕ} (hm : Valid w m) (h : n ≤ m) :
    w (idx w m) ≤ w (idx w n) := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · exact le_rfl
  have hn := valid_of_le hm h
  have hr : rank w (idx w n) < rank w (idx w m) := by
    rw [(idx_spec hn).2, (idx_spec hm).2]
    exact Nat.nth_lt_nth' hlt hm
  have hne : idx w n ≠ idx w m := fun he => by rw [he] at hr; omega
  rcases prec_total (w := w) hne with hp | hp
  · exact prec_weight hp
  · have := rank_lt hs (idx_spec hn).1 hp; omega

/-- The transfer principle: a series supported on the positive atoms has the
same sum after relabeling by `idx`. -/
theorem hasSum_relabel {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (hw : ∀ i, 0 ≤ w i) (hs : Summable w) (f : ℕ → M)
    (hf : ∀ i, w i = 0 → f i = 0) (a : M) :
    HasSum f a ↔ HasSum (fun n => if Valid w n then f (idx w n) else 0) a := by
  let S : Set ℕ := {n | Valid w n}
  let g : S → ℕ := fun n => idx w n.1
  have hg : Function.Injective g := by
    intro x y hxy
    exact Subtype.ext (idx_injOn x.2 y.2 hxy)
  have hrange : ∀ x, x ∉ Set.range g → f x = 0 := by
    intro x hx
    apply hf
    by_contra hne
    have hpos : 0 < w x := lt_of_le_of_ne (hw x) (Ne.symm hne)
    obtain ⟨n, hn, he⟩ := idx_surj hs hpos
    exact hx ⟨⟨n, hn⟩, he⟩
  rw [← hg.hasSum_iff hrange]
  have hc : (f ∘ g) = (fun n : ℕ => f (idx w n)) ∘ ((↑) : S → ℕ) := rfl
  rw [hc, hasSum_subtype_iff_indicator]
  have he : S.indicator (fun n => f (idx w n)) =
      (fun n => if Valid w n then f (idx w n) else 0) := by
    funext n
    simp [S, Set.indicator_apply]
  rw [he]

end Rank

open Rank

namespace CountableSeed
variable {ι : ITree}

def rankedWeight (G : CountableSeed ι) (n : ℕ) : ℝ :=
  if Valid G.weight n then G.weight (idx G.weight n) else 0

def rankedStrategy (G : CountableSeed ι) (n : ℕ) : IStrategy ι :=
  if Valid G.weight n then G.strategy (idx G.weight n) else G.strategy 0

theorem rankedWeight_nonneg (G : CountableSeed ι) (n : ℕ) : 0 ≤ G.rankedWeight n := by
  unfold rankedWeight; split_ifs
  · exact G.nonneg _
  · exact le_rfl

theorem rankedWeight_anti (G : CountableSeed ι) : Antitone G.rankedWeight := by
  intro n m hnm
  unfold rankedWeight
  by_cases hm : Valid G.weight m
  · have hn := valid_of_le hm hnm
    rw [if_pos hm, if_pos hn]
    exact idx_anti G.mass.summable hm hnm
  · rw [if_neg hm]
    split_ifs
    · exact G.nonneg _
    · exact le_rfl

theorem relabel (G : CountableSeed ι) {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    (f : ℕ → M) (hf : ∀ i, G.weight i = 0 → f i = 0) (a : M) :
    HasSum f a ↔ HasSum (fun n => if Valid G.weight n then f (idx G.weight n) else 0) a :=
  hasSum_relabel G.nonneg G.mass.summable f hf a

theorem rankedWeight_hasSum (G : CountableSeed ι) : HasSum G.rankedWeight 1 :=
  (G.relabel G.weight (fun _ h => h) 1).mp G.mass

/-- The ranked rearrangement of a countable seed. -/
def ranked (G : CountableSeed ι) : RankedSeed ι where
  weight := G.rankedWeight
  nonneg := G.rankedWeight_nonneg
  decreasing := G.rankedWeight_anti
  mass := G.rankedWeight_hasSum
  strategy := G.rankedStrategy

theorem ranked_hit (G : CountableSeed ι) (h : List (ℕ × ℕ)) :
    ∑' n, G.ranked.hit h n = ∑' i, G.hit h i := by
  have hH := (G.relabel (G.hit h) (fun i hi => by simp [hit, hi]) _).mp
    (G.hit_summable h).hasSum
  have he : (fun n => if Valid G.weight n then G.hit h (idx G.weight n) else 0) =
      G.ranked.hit h := by
    funext n
    simp only [RankedSeed.hit, ranked, rankedWeight, rankedStrategy, hit]
    split_ifs <;> simp
  rw [he] at hH
  exact hH.tsum_eq

theorem ranked_entropy (G : CountableSeed ι) : G.ranked.entropy = G.entropy := by
  have hH := (G.relabel (fun i => ENNReal.ofReal (Real.negMulLog (G.weight i)))
    (fun i hi => by simp [hi]) _).mp ENNReal.summable.hasSum
  rw [RankedSeed.entropy_eq_tsum, entropy, ← hH.tsum_eq]
  apply tsum_congr
  intro n
  simp only [ranked, rankedWeight]
  split_ifs <;> simp

theorem ranked_measure (G : CountableSeed ι) : G.ranked.measure = G.measure := by
  ext A hA
  rw [RankedSeed.measure, measure, countableMeasure, Measure.sum_apply _ hA,
    Measure.sum_apply _ hA]
  have hH := (G.relabel (fun i => (ENNReal.ofReal (G.weight i) •
      Measure.dirac (G.strategy i)) A) (fun i hi => by simp [hi]) _).mp
    ENNReal.summable.hasSum
  rw [← hH.tsum_eq]
  apply tsum_congr
  intro n
  simp only [ranked, rankedWeight, rankedStrategy]
  split_ifs <;> simp

theorem ranked_exactTo_iff (G : CountableSeed ι) (n : ℕ) :
    G.ranked.ExactTo n ↔ G.ExactTo n := by
  unfold RankedSeed.ExactTo ExactTo
  simp only [ranked_hit]

theorem ranked_exact_iff (G : CountableSeed ι) : G.ranked.Exact ↔ G.Exact := by
  unfold RankedSeed.Exact Exact
  simp only [ranked_exactTo_iff]

/-- The ranked seed is a relabeling of the positive atoms of `G`. -/
theorem ranked_positive_relabel (G : CountableSeed ι) :
    ∃ e : {n // 0 < G.ranked.weight n} ≃ {i // 0 < G.weight i},
      ∀ n, G.weight (e n) = G.ranked.weight n ∧ G.strategy (e n) = G.ranked.strategy n := by
  have hvalid : ∀ n, 0 < G.ranked.weight n → Valid G.weight n := by
    intro n hn
    by_contra hv
    simp [ranked, rankedWeight, hv] at hn
  let f : {n // 0 < G.ranked.weight n} → {i // 0 < G.weight i} := fun n =>
    ⟨idx G.weight n.1, (idx_spec (hvalid n.1 n.2)).1⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact idx_injOn (hvalid _ x.2) (hvalid _ y.2)
        (congrArg Subtype.val hxy)
    · intro i
      obtain ⟨n, hn, he⟩ := idx_surj G.mass.summable i.2
      have hpos : 0 < G.ranked.weight n := by
        simp only [ranked, rankedWeight, if_pos hn, he]; exact i.2
      exact ⟨⟨n, hpos⟩, Subtype.ext he⟩
  refine ⟨Equiv.ofBijective f hf, fun n => ?_⟩
  have hv := hvalid n.1 n.2
  have he : ((Equiv.ofBijective f hf) n : ℕ) = idx G.weight n.1 := rfl
  rw [he]
  simp [ranked, rankedWeight, rankedStrategy, hv]

/-- Main conversion theorem. -/
theorem exists_ranked (G : CountableSeed ι) :
    ∃ R : RankedSeed ι,
      (∀ h, ∑' n, R.hit h n = ∑' i, G.hit h i) ∧
      R.measure = G.measure ∧
      R.entropy = G.entropy ∧
      (∀ n, R.ExactTo n ↔ G.ExactTo n) ∧
      ∃ e : {n // 0 < R.weight n} ≃ {i // 0 < G.weight i},
        ∀ n, G.weight (e n) = R.weight n ∧ G.strategy (e n) = R.strategy n :=
  ⟨G.ranked, G.ranked_hit, G.ranked_measure, G.ranked_entropy, G.ranked_exactTo_iff,
    G.ranked_positive_relabel⟩

end CountableSeed

/-- The ranked costs are the costs over all countable seeds. -/
theorem finiteCost_eq_countable (ι : ITree) (n : ℕ) :
    finiteCost ι n = ⨅ G : {G : CountableSeed ι // G.ExactTo n}, G.val.entropy := by
  apply le_antisymm
  · refine le_iInf fun G => ?_
    rw [← G.1.ranked_entropy]
    exact finiteCost_le_seed ι n _ ((G.1.ranked_exactTo_iff n).mpr G.2)
  · refine le_iInf fun S => ?_
    rw [← S.1.toCountable_entropy]
    exact iInf_le_of_le ⟨S.1.toCountable, S.2⟩ le_rfl

theorem infiniteCost_eq_countable (ι : ITree) :
    infiniteCost ι = ⨅ G : {G : CountableSeed ι // G.Exact}, G.val.entropy := by
  apply le_antisymm
  · refine le_iInf fun G => ?_
    rw [← G.1.ranked_entropy]
    exact iInf_le_of_le ⟨G.1.ranked, G.1.ranked_exact_iff.mpr G.2⟩ le_rfl
  · refine le_iInf fun S => ?_
    rw [← S.1.toCountable_entropy]
    exact iInf_le_of_le ⟨S.1.toCountable, S.2⟩ le_rfl

#print axioms CountableSeed.exists_ranked
#print axioms finiteCost_eq_countable
#print axioms infiniteCost_eq_countable


/-! ## Compatibility names (`Seed` API used by the downstream modules) -/

abbrev Seed (ι : ITree) := CountableSeed ι

namespace Seed
variable {ι : ITree}
abbrev entropy (S : Seed ι) : ℝ≥0∞ := CountableSeed.entropy S
abbrev hit (S : Seed ι) (h : List (ℕ × ℕ)) (i : ℕ) : ℝ := CountableSeed.hit S h i
abbrev ExactTo (S : Seed ι) (n : ℕ) : Prop := CountableSeed.ExactTo S n
abbrev Exact (S : Seed ι) : Prop := CountableSeed.Exact S
abbrev ranked (S : Seed ι) : RankedSeed ι := CountableSeed.ranked S
theorem ranked_entropy (S : Seed ι) : S.ranked.entropy = S.entropy :=
  CountableSeed.ranked_entropy S
theorem ranked_hit (S : Seed ι) (h) : ∑' i, S.ranked.hit h i = ∑' i, S.hit h i :=
  CountableSeed.ranked_hit S h
theorem ranked_exactTo (S : Seed ι) (n) : S.ranked.ExactTo n ↔ S.ExactTo n :=
  CountableSeed.ranked_exactTo_iff S n
theorem ranked_exact (S : Seed ι) : S.ranked.Exact ↔ S.Exact :=
  CountableSeed.ranked_exact_iff S
end Seed

def RankedSeed.forget {ι : ITree} (S : RankedSeed ι) : Seed ι := S.toCountable

theorem RankedSeed.forget_entropy {ι : ITree} (S : RankedSeed ι) :
    S.forget.entropy = S.entropy := S.toCountable_entropy

def countableFiniteCost (ι : ITree) (n : ℕ) : ℝ≥0∞ :=
  ⨅ S : {S : Seed ι // S.ExactTo n}, S.val.entropy

def countableInfiniteCost (ι : ITree) : ℝ≥0∞ :=
  ⨅ S : {S : Seed ι // S.Exact}, S.val.entropy

theorem countableFiniteCost_eq (ι : ITree) (n : ℕ) :
    countableFiniteCost ι n = finiteCost ι n :=
  (finiteCost_eq_countable ι n).symm

theorem countableInfiniteCost_eq (ι : ITree) :
    countableInfiniteCost ι = infiniteCost ι :=
  (infiniteCost_eq_countable ι).symm

theorem countable_projective_entropy_identity (ι : ITree) :
    countableInfiniteCost ι = ⨆ n, countableFiniteCost ι n := by
  simp only [countableInfiniteCost_eq, countableFiniteCost_eq,
    projective_entropy_identity]

theorem countable_entropy_attained (ι : ITree)
    (h : (⨆ n, countableFiniteCost ι n) ≠ ∞) :
    ∃ S : Seed ι, S.Exact ∧ S.entropy = countableInfiniteCost ι := by
  simp only [countableFiniteCost_eq] at h
  obtain ⟨S, hex, he⟩ := entropy_attained ι h
  refine ⟨S.forget, hex, ?_⟩
  rw [S.forget_entropy, he, countableInfiniteCost_eq, projective_entropy_identity]

#print axioms countable_entropy_attained

end CausalSpectrum.Completion
end

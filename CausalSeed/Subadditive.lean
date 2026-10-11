/-
Subadditivity of the optimal exact seed entropy for a stationary kernel.

Two seeds, exact to horizons `m` and `n`, are concatenated: the first answers at
histories of length `< m`, the second answers at the remaining histories, read
from position `m` on. Because the kernel is stationary, path masses factor over
this split, so the product seed is exact to horizon `m + n` and its entropy is
the sum of the two entropies. Hence `C_{m+n} ≤ C_m + C_n`, and by Fekete's lemma
`C_n / n → inf_{n ≥ 1} C_n / n`, which equals `h_max` by `causal_floor`.
-/
import CausalSeed.AlphabetSeed
import CausalSeed.CausalFloor
import Mathlib.Analysis.Subadditive

noncomputable section
open Classical Filter Topology
open scoped ENNReal

namespace CausalSpectrum

/-! ## General facts on infinite trees -/

theorem pm_append (ι : ITree) :
    ∀ (u pref v : List (ℕ × ℕ)), pm ι pref (u ++ v) = pm ι pref u * pm ι (pref ++ u) v := by
  intro u
  induction u with
  | nil => intro pref v; simp [pm]
  | cons p t ih =>
      intro pref v
      simp only [List.cons_append, pm]
      split_ifs <;> simp [ih, mul_assoc, List.append_assoc]

theorem agreesFrom_append (ι : ITree) (s : IStrategy ι) :
    ∀ (u pref v : List (ℕ × ℕ)),
      agreesFrom ι s pref (u ++ v) ↔ agreesFrom ι s pref u ∧ agreesFrom ι s (pref ++ u) v := by
  intro u
  induction u with
  | nil => intro pref v; simp [agreesFrom]
  | cons p t ih =>
      intro pref v
      simp only [List.cons_append, agreesFrom, ih, List.append_assoc]
      constructor
      · rintro ⟨a, h1, h2, h3, h4⟩; exact ⟨⟨a, h1, h2, h3⟩, h4⟩
      · rintro ⟨⟨a, h1, h2, h3⟩, h4⟩; exact ⟨a, h1, h2, h3, h4⟩

namespace Kernel
variable (κ : Kernel)

theorem pm_stationary : ∀ (h pref : List (ℕ × ℕ)), pm κ.toITree pref h = pm κ.toITree [] h := by
  intro h
  induction h with
  | nil => intro pref; rfl
  | cons p t ih =>
      intro pref
      simp only [pm]
      rw [ih (pref ++ [p]), ih ([] ++ [p])]
      rfl

theorem pathMass_append (u v : List (ℕ × ℕ)) :
    pathMass κ.toITree (u ++ v) = pathMass κ.toITree u * pathMass κ.toITree v := by
  unfold pathMass
  rw [pm_append, κ.pm_stationary v]

/-- Concatenation of two strategies at round `m`. -/
def cat (m : ℕ) (s t : IStrategy κ.toITree) : IStrategy κ.toITree :=
  fun p => if p.1.length < m then s p else t ⟨p.1.drop m, p.2⟩

theorem agrees_cat_left (m : ℕ) (s t : IStrategy κ.toITree) :
    ∀ (u pref : List (ℕ × ℕ)), pref.length + u.length ≤ m →
      (agreesFrom κ.toITree (κ.cat m s t) pref u ↔ agreesFrom κ.toITree s pref u) := by
  intro u
  induction u with
  | nil => intro pref _; simp [agreesFrom]
  | cons p t' ih =>
      intro pref hl
      simp only [List.length_cons] at hl
      have hlt : pref.length < m := by omega
      have hl' : (pref ++ [p]).length + t'.length ≤ m := by simp; omega
      simp only [agreesFrom, ih _ hl', cat, hlt, ↓reduceIte]

theorem agrees_cat_right (m : ℕ) (s t : IStrategy κ.toITree) :
    ∀ (v pref : List (ℕ × ℕ)), m ≤ pref.length →
      (agreesFrom κ.toITree (κ.cat m s t) pref v ↔
        agreesFrom κ.toITree t (pref.drop m) v) := by
  intro v
  induction v with
  | nil => intro pref _; simp [agreesFrom]
  | cons p t' ih =>
      intro pref hl
      have hl' : m ≤ (pref ++ [p]).length := by simp; omega
      have hd : (pref ++ [p]).drop m = pref.drop m ++ [p] := List.drop_append_of_le_length hl
      have hn : ¬ pref.length < m := by omega
      simp only [agreesFrom, ih _ hl', hd, cat, hn]
      rfl

theorem iAgree_cat (m : ℕ) (s t : IStrategy κ.toITree) (h : List (ℕ × ℕ)) :
    iAgree κ.toITree (κ.cat m s t) h ↔
      iAgree κ.toITree s (h.take m) ∧ iAgree κ.toITree t (h.drop m) := by
  rw [iAgree_iff, iAgree_iff, iAgree_iff]
  conv_lhs => rw [← List.take_append_drop m h]
  rw [agreesFrom_append, κ.agrees_cat_left m s t _ _ (by simp)]
  by_cases hm : m ≤ h.length
  · rw [κ.agrees_cat_right m s t _ _ (by simp; omega)]
    simp [List.drop_take_self]
  · have : h.drop m = [] := List.drop_eq_nil_of_le (by omega)
    simp [this, agreesFrom]

theorem indAgree_cat (m : ℕ) (s t : IStrategy κ.toITree) (h : List (ℕ × ℕ)) :
    indAgree κ.toITree (κ.cat m s t) h =
      indAgree κ.toITree s (h.take m) * indAgree κ.toITree t (h.drop m) := by
  unfold indAgree
  rw [propext (κ.iAgree_cat m s t h)]
  split_ifs <;> simp_all


open Completion

/-- The concatenated product of two countable seeds. -/
def catSeed (m : ℕ) (S T : Seed κ.toITree) : AlphabetSeed κ.toITree (ℕ × ℕ) where
  weight p := S.weight p.1 * T.weight p.2
  nonneg p := mul_nonneg (S.nonneg _) (T.nonneg _)
  mass := by
    have := S.mass.mul T.mass
      (S.mass.summable.mul_of_nonneg T.mass.summable S.nonneg T.nonneg)
    simpa using this
  strategy p := κ.cat m (S.strategy p.1) (T.strategy p.2)

theorem hit_summable (S : Seed κ.toITree) (h : List (ℕ × ℕ)) :
    Summable fun i => S.hit h i :=
  Summable.of_nonneg_of_le
    (fun i => mul_nonneg (S.nonneg i) (indAgree_nonneg _ _ _))
    (fun i => mul_le_of_le_one_right (S.nonneg i) (indAgree_le_one _ _ _)) S.mass.summable

theorem catSeed_exactTo (m n : ℕ) (S T : Seed κ.toITree) (hS : S.ExactTo m)
    (hT : T.ExactTo n) : (κ.catSeed m S T).ExactTo (m + n) := by
  intro h hl
  have hfun : (fun p : ℕ × ℕ => (κ.catSeed m S T).hit h p) =
      fun p => S.hit (h.take m) p.1 * T.hit (h.drop m) p.2 := by
    funext p
    simp only [AlphabetSeed.hit, catSeed, CountableSeed.hit, κ.indAgree_cat]
    ring
  rw [hfun]
  have hsum := (κ.hit_summable S (h.take m)).hasSum.mul (κ.hit_summable T (h.drop m)).hasSum
    ((κ.hit_summable S _).mul_of_nonneg (κ.hit_summable T _)
      (fun i => mul_nonneg (S.nonneg i) (indAgree_nonneg _ _ _))
      (fun i => mul_nonneg (T.nonneg i) (indAgree_nonneg _ _ _)))
  rw [hsum.tsum_eq, hS _ (by simp), hT _ (by simp; omega), ← κ.pathMass_append,
    List.take_append_drop]

theorem catSeed_entropy (m : ℕ) (S T : Seed κ.toITree) :
    (κ.catSeed m S T).entropy = S.entropy + T.entropy := by
  have h1 : ∑' i, ENNReal.ofReal (S.weight i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg S.nonneg S.mass.summable, S.mass.tsum_eq]; simp
  have h2 : ∑' i, ENNReal.ofReal (T.weight i) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg T.nonneg T.mass.summable, T.mass.tsum_eq]; simp
  have hN : ∀ (G : Seed κ.toITree) i, 0 ≤ Real.negMulLog (G.weight i) := fun G i =>
    Real.negMulLog_nonneg (G.nonneg i) (CountableSeed.weight_le_one G i)
  have hterm : ∀ p : ℕ × ℕ, ENNReal.ofReal (Real.negMulLog (S.weight p.1 * T.weight p.2)) =
      ENNReal.ofReal (T.weight p.2) * ENNReal.ofReal (Real.negMulLog (S.weight p.1)) +
        ENNReal.ofReal (S.weight p.1) * ENNReal.ofReal (Real.negMulLog (T.weight p.2)) := by
    intro p
    rw [Real.negMulLog_mul, ENNReal.ofReal_add (mul_nonneg (T.nonneg _) (hN S _))
      (mul_nonneg (S.nonneg _) (hN T _)), ENNReal.ofReal_mul (T.nonneg _),
      ENNReal.ofReal_mul (S.nonneg _)]
  simp only [AlphabetSeed.entropy, catSeed, hterm]
  rw [ENNReal.tsum_add,
    ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (T.weight j) *
      ENNReal.ofReal (Real.negMulLog (S.weight i))),
    ENNReal.tsum_prod (f := fun i j => ENNReal.ofReal (S.weight i) *
      ENNReal.ofReal (Real.negMulLog (T.weight j)))]
  simp only [ENNReal.tsum_mul_left, ENNReal.tsum_mul_right, h1, h2, one_mul]
  rfl

/-- **Subadditivity** of the optimal exact seed entropy (nats). -/
theorem finiteCost_subadditive (m n : ℕ) :
    finiteCost κ.toITree (m + n) ≤ finiteCost κ.toITree m + finiteCost κ.toITree n := by
  simp only [← countableFiniteCost_eq, countableFiniteCost]
  rw [ENNReal.iInf_add]
  refine le_iInf fun S => ?_
  rw [ENNReal.add_iInf]
  refine le_iInf fun T => ?_
  have hex : (κ.catSeed m S.1 T.1).toSeed.ExactTo (m + n) :=
    ((κ.catSeed m S.1 T.1).toSeed_exactTo _).mpr (κ.catSeed_exactTo m n S.1 T.1 S.2 T.2)
  refine (iInf_le _ (⟨_, hex⟩ : {G : Seed κ.toITree // G.ExactTo (m + n)})).trans ?_
  rw [AlphabetSeed.toSeed_entropy, κ.catSeed_entropy]

theorem finiteCost_ne_top (n : ℕ) : finiteCost κ.toITree n ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top (finiteCost_sandwich κ.toITree n).2

/-- **Subadditivity** `C_{m+n} ≤ C_m + C_n` (bits). -/
theorem costBits_subadditive (m n : ℕ) :
    κ.costBits (m + n) ≤ κ.costBits m + κ.costBits n := by
  unfold costBits
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (Real.log_pos one_lt_two).le
  rw [← ENNReal.toReal_add (κ.finiteCost_ne_top m) (κ.finiteCost_ne_top n)]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨κ.finiteCost_ne_top m,
    κ.finiteCost_ne_top n⟩) (κ.finiteCost_subadditive m n)


theorem costBits_nonneg (n : ℕ) : 0 ≤ κ.costBits n :=
  (envelopeMean_nonneg _).trans (κ.costBits_sandwich n).1

theorem costBits_sub : Subadditive κ.costBits := κ.costBits_subadditive

theorem costBits_div_bdd : BddBelow (Set.range fun n : ℕ => κ.costBits n / n) :=
  ⟨0, by rintro _ ⟨n, rfl⟩; exact div_nonneg (κ.costBits_nonneg n) n.cast_nonneg⟩

/-- **Fekete.** `C_n / n` converges to `inf_{n ≥ 1} C_n / n`. -/
theorem costBits_fekete :
    Tendsto (fun n : ℕ => κ.costBits n / n) atTop
      (𝓝 (sInf ((fun n : ℕ => κ.costBits n / n) '' Set.Ici 1))) := by
  have := κ.costBits_sub.tendsto_lim κ.costBits_div_bdd
  rwa [Subadditive.lim] at this

/-- The causal Shannon floor is the infimum: `h_max = inf_{n ≥ 1} C_n / n`. -/
theorem hmax_eq_inf :
    κ.hmax = sInf ((fun n : ℕ => κ.costBits n / n) '' Set.Ici 1) :=
  tendsto_nhds_unique κ.causal_floor κ.costBits_fekete

/-- **Exact lower bound** `n · h_max ≤ C_n` for every `n ≥ 1` (bits). -/
theorem hmax_mul_le_costBits {n : ℕ} (hn : 1 ≤ n) : n * κ.hmax ≤ κ.costBits n := by
  have hlim : κ.costBits_sub.lim ≤ κ.costBits n / n :=
    κ.costBits_sub.lim_le_div κ.costBits_div_bdd (by omega)
  have he : κ.costBits_sub.lim = κ.hmax := by rw [Subadditive.lim]; exact κ.hmax_eq_inf.symm
  rw [he] at hlim
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [le_div_iff₀ hpos] at hlim
  linarith

end Kernel
end CausalSpectrum

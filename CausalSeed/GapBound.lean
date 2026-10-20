/-
The explicit block family and the bounded residual.

Under a unique maximizer `j₀` of the action entropies, the plan with product blocks of
sizes `D+1, D, …, 1` and subfamily windows of sizes `0, D+1, …, 1` gives, for the horizon
`n_D = 1 + 2 + ⋯ + (D+1)`, the bound `C_{n_D} ≤ n_D h_max + K` with `K` independent of
`D`; monotonicity of `C_n - n h_max` then bounds every horizon.
-/
import CausalSeed.GapComp
import CausalSeed.GapZero

noncomputable section
open Classical Finset
open scoped ENNReal

namespace CausalSpectrum.Gap

/-- Blocks from disjointness and total size. -/
def Blocks.ofDisj {n r : ℕ} (O s : Fin r → ℕ) (le : ∀ j, O j + s j ≤ n)
    (uniq : ∀ j j' c, O j ≤ c → c < O j + s j → O j' ≤ c → c < O j' + s j' → j = j')
    (hs : ∑ j, s j = n) : Blocks n r where
  O := O
  s := s
  le := le
  uniq := uniq
  cover := by
    intro c hc
    set U := univ.biUnion fun j => Ico (O j) (O j + s j)
    have hsub : U ⊆ range n := by
      intro x hx
      simp only [U, mem_biUnion, mem_Ico, mem_univ, true_and] at hx
      obtain ⟨j, h1, h2⟩ := hx
      exact mem_range.2 (lt_of_lt_of_le h2 (le j))
    have hcard : U.card = n := by
      rw [card_biUnion]
      · simp [hs]
      · intro j _ j' _ hne
        rw [Function.onFun, disjoint_left]
        intro x hx hx'
        simp only [mem_Ico] at hx hx'
        exact hne (uniq j j' x hx.1 hx.2 hx'.1 hx'.2)
    have hU : U = range n := eq_of_subset_of_card_le hsub (by simp [hcard])
    have : c ∈ U := hU ▸ mem_range.2 hc
    simp only [U, mem_biUnion, mem_Ico, mem_univ, true_and] at this
    exact this

/-- Consecutive blocks in increasing order. -/
def prefixBlocks (σ : ℕ → ℕ) (r n : ℕ) (hn : ∑ i ∈ range r, σ i = n) : Blocks n r :=
  Blocks.ofDisj (fun j => ∑ i ∈ range j.val, σ i) (fun j => σ j.val)
    (fun j => by
      rw [← hn, ← sum_range_succ]
      exact sum_le_sum_of_subset (range_subset_range.2 j.isLt))
    (fun j j' c h1 h2 h3 h4 => by
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · have : ∑ i ∈ range j.val, σ i + σ j.val ≤ ∑ i ∈ range j'.val, σ i := by
          rw [← sum_range_succ]; exact sum_le_sum_of_subset (range_subset_range.2 h)
        omega
      · have : ∑ i ∈ range j'.val, σ i + σ j'.val ≤ ∑ i ∈ range j.val, σ i := by
          rw [← sum_range_succ]; exact sum_le_sum_of_subset (range_subset_range.2 h)
        omega)
    (by rw [← hn]; exact Fin.sum_univ_eq_sum_range σ r)

/-- Consecutive blocks in decreasing order. -/
def suffixBlocks (σ : ℕ → ℕ) (r n : ℕ) (hn : ∑ i ∈ range r, σ i = n) : Blocks n r :=
  Blocks.ofDisj (fun j => ∑ i ∈ Ico (j.val + 1) r, σ i) (fun j => σ j.val)
    (fun j => by
      rw [← hn, add_comm, ← sum_eq_sum_Ico_succ_bot j.isLt]
      exact sum_le_sum_of_subset (fun x hx => by simp at hx ⊢; omega))
    (fun j j' c h1 h2 h3 h4 => by
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
      · have : ∑ i ∈ Ico (j'.val + 1) r, σ i + σ j'.val ≤ ∑ i ∈ Ico (j.val + 1) r, σ i := by
          rw [add_comm, ← sum_eq_sum_Ico_succ_bot j'.isLt]
          exact sum_le_sum_of_subset (fun x hx => by simp at hx ⊢; omega)
        omega
      · have : ∑ i ∈ Ico (j.val + 1) r, σ i + σ j.val ≤ ∑ i ∈ Ico (j'.val + 1) r, σ i := by
          rw [add_comm, ← sum_eq_sum_Ico_succ_bot j.isLt]
          exact sum_le_sum_of_subset (fun x hx => by simp at hx ⊢; omega)
        omega)
    (by rw [← hn]; exact Fin.sum_univ_eq_sum_range σ r)

/-! ### The family -/

/-- Product block sizes `D+1, D, …, 1, 0`. -/
def pN (D i : ℕ) : ℕ := if i ≤ D then D + 1 - i else 0

/-- Window sizes `0, D+1, …, 1`. -/
def qN (D i : ℕ) : ℕ := if i = 0 then 0 else pN D (i - 1)

/-- The horizon `n_D = 1 + ⋯ + (D+1)`. -/
def nD (D : ℕ) : ℕ := ∑ i ∈ range (D + 1), pN D i

theorem sum_pN (D : ℕ) : ∑ i ∈ range (D + 2), pN D i = nD D := by
  rw [sum_range_succ, nD]; simp [pN]

theorem sum_qN (D : ℕ) : ∑ i ∈ range (D + 2), qN D i = nD D := by
  rw [sum_range_succ', nD]; simp [qN]

theorem nD_ge (D : ℕ) : D ≤ nD D := by
  unfold nD
  rw [sum_range_succ']
  have : pN D 0 = D + 1 := by simp [pN]
  omega

theorem sep_family (D : ℕ) (j : ℕ) (hj : j < D + 2) :
    nD D ≤ (∑ i ∈ range j, pN D i) + (∑ i ∈ Ico (j + 1) (D + 2), qN D i) + 1 := by
  have h1 : ∑ i ∈ Ico (j + 1) (D + 2), qN D i = ∑ i ∈ Ico j (D + 1), pN D i := by
    rw [← sum_Ico_add' (fun i => qN D i) j (D + 1) 1]
    refine sum_congr rfl fun i _ => ?_
    simp [qN]
  rw [h1, sum_range_add_sum_Ico _ (by omega : j ≤ D + 1)]
  unfold nD; omega

end CausalSpectrum.Gap

namespace CausalSpectrum.Kernel
open Completion Gap

variable {κ : Kernel} (j₀ : Fin κ.nA) (h2 : 2 ≤ κ.nA)

/-- The plan of the family. -/
def planD (D : ℕ) : Plan (nD D) (D + 2) where
  X := prefixBlocks (pN D) (D + 2) _ (sum_pN D)
  B := suffixBlocks (qN D) (D + 2) _ (sum_qN D)
  sep := fun j => sep_family D j j.isLt

theorem actEntropy_eq_nml (a : Fin κ.nA) :
    κ.actEntropy a = (∑ y, Real.negMulLog (κ.K a y)) / Real.log 2 := by
  unfold actEntropy infoMass Real.logb
  rw [sum_div]
  refine sum_congr rfl fun y _ => ?_
  unfold Real.negMulLog; ring

/-- Cost of the family plan. -/
theorem costBits_family {δ δx : ℝ} (hδ : 0 < δ) (hδx : 0 ≤ δx) (D : ℕ) :
    κ.costBits (nD D) ≤ nD D * κ.actEntropy j₀ +
      (∑ j : Fin (D + 2), exc j₀ h2 δ δx (pN D j) (qN D j)) / Real.log 2 := by
  have hc := finiteCost_le_plan (planD D) (fun j => mkComp j₀ h2 δ (pN D j) (qN D j))
  have hb : ∑ j : Fin (D + 2), ∑ o, Real.negMulLog ((mkComp j₀ h2 δ (pN D j) (qN D j)).w o) ≤
      nD D * ∑ y, Real.negMulLog (κ.K j₀ y) + ∑ j : Fin (D + 2), exc j₀ h2 δ δx (pN D j) (qN D j) := by
    refine (sum_le_sum fun (j : Fin (D + 2)) _ => mkComp_entropy j₀ h2 hδ hδx (pN D j) (qN D j)).trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_mul]
    congr 2
    rw [← sum_pN D]; push_cast
    exact Fin.sum_univ_eq_sum_range (fun i => (pN D i : ℝ)) (D + 2)
  have hnn : 0 ≤ ∑ j : Fin (D + 2), ∑ o, Real.negMulLog ((mkComp j₀ h2 δ (pN D j) (qN D j)).w o) :=
    sum_nonneg fun j _ => sum_nonneg fun o _ => Real.negMulLog_nonneg
      ((mkComp j₀ h2 δ (pN D j) (qN D j)).nonneg o) (by
        have := single_le_sum (fun o _ => (mkComp j₀ h2 δ (pN D j) (qN D j)).nonneg o) (mem_univ o)
        rwa [(mkComp j₀ h2 δ (pN D j) (qN D j)).total] at this)
  have ht := ENNReal.toReal_le_of_le_ofReal hnn hc
  unfold costBits
  rw [div_le_iff₀ (Real.log_pos one_lt_two), add_mul, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne',
    actEntropy_eq_nml, mul_assoc, div_mul_cancel₀ _ (Real.log_pos one_lt_two).ne']
  linarith

/-! ### Parameters under a unique maximizer -/

/-- `j₀` is the unique maximizer of the action entropies. -/
def UniqueMax (κ : Kernel) (j₀ : Fin κ.nA) : Prop := ∀ a, a ≠ j₀ → κ.actEntropy a < κ.actEntropy j₀

theorem emb_ne (b : Fin (κ.nA - 1)) : emb j₀ b ≠ j₀ := by
  intro h
  have := congrArg Fin.val h
  simp only [emb] at this
  split_ifs at this <;> omega

theorem subK_hmax_lt (hu : UniqueMax κ j₀) : (subK j₀ h2).hmax < κ.actEntropy j₀ := by
  unfold hmax
  rw [Finset.sup'_lt_iff]
  intro b _
  exact hu _ (emb_ne j₀ b)

theorem hmax_eq_of_unique (hu : UniqueMax κ j₀) : κ.hmax = κ.actEntropy j₀ := by
  apply le_antisymm
  · unfold hmax
    refine Finset.sup'_le _ _ fun a _ => ?_
    by_cases h : a = j₀
    · rw [h]
    · exact (hu a h).le
  · exact Finset.le_sup' κ.actEntropy (Finset.mem_univ j₀)

/-- The entropy gap `g = H(K_{j₀}) - h_max(others)`. -/
def gapG : ℝ := κ.actEntropy j₀ - (subK j₀ h2).hmax

def dX : ℝ := gapG j₀ h2 / 4
def dB : ℝ := gapG j₀ h2 / 8

/-- The excess of the middle pairs, `p` samples against a window of `p + 1`. -/
def Fexc (p : ℕ) : ℝ := exc j₀ h2 (dB j₀ h2) (dX j₀ h2) p (p + 1)

theorem Hb_eq : Hb (κ.K j₀) = κ.actEntropy j₀ := rfl

theorem Tb_nonneg {δ : ℝ} (hδ : 0 < δ) (q : ℕ) : 0 ≤ Tb (subK j₀ h2) δ q := by
  have hl := lamT_pos (subK j₀ h2) hδ
  have h1 : Real.exp (-(lamT (subK j₀ h2) δ / 2)) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have h2' : (2:ℝ) ^ (-(1/2:ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have := (subK j₀ h2).hmax_nonneg
  unfold Tb tailB
  have : 0 ≤ 1 - Real.exp (-(lamT (subK j₀ h2) δ / 2)) := by linarith
  have : 0 ≤ 1 - (2:ℝ) ^ (-(1/2:ℝ)) := by linarith
  positivity

theorem exc_nonneg {δ δx : ℝ} (hδ : 0 < δ) (p q : ℕ) : 0 ≤ exc j₀ h2 δ δx p q := by
  unfold exc thA
  have : 0 ≤ Real.log ((2:ℝ) ^ uB j₀ h2 δ q + 1) :=
    Real.log_nonneg (by have : 0 ≤ (2:ℝ) ^ uB j₀ h2 δ q := by positivity
                        linarith)
  have := Tb_nonneg j₀ h2 hδ q
  positivity

theorem log_two_rpow_add_one_le {u : ℝ} (hu : 0 ≤ u) :
    Real.log ((2:ℝ) ^ u + 1) ≤ (u + 1) * Real.log 2 := by
  have h1 : (1:ℝ) ≤ 2 ^ u := Real.one_le_rpow (by norm_num) hu
  calc Real.log ((2:ℝ) ^ u + 1) ≤ Real.log ((2:ℝ) ^ (u + 1)) := by
        apply Real.log_le_log (by positivity)
        rw [Real.rpow_add (by norm_num), Real.rpow_one]; linarith
    _ = _ := by rw [Real.log_rpow (by norm_num)]

theorem pow_le_of_le {r ρ : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ ρ) (h2' : r ≤ 1) (p : ℕ) :
    r ^ (p + 1) ≤ ρ ^ p :=
  (pow_le_pow_of_le_one h0 h2' (Nat.le_succ p)).trans (pow_le_pow_left₀ h0 h1 p)

/-- **Summability of the middle excesses.** -/
theorem summable_Fexc (hu : UniqueMax κ j₀) : Summable (Fexc j₀ h2) := by
  have hg : 0 < gapG j₀ h2 := by have := subK_hmax_lt j₀ h2 hu; unfold gapG; linarith
  set g := gapG j₀ h2
  set h' := (subK j₀ h2).hmax
  have hh' : 0 ≤ h' := (subK j₀ h2).hmax_nonneg
  set δ := dB j₀ h2
  set δx := dX j₀ h2
  have hδ : 0 < δ := by simp only [δ, dB]; positivity
  have hδx : 0 < δx := by simp only [δx, dX]; positivity
  set c := h' + 2 * δ
  have hc : 0 ≤ c := by positivity
  set a := δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1))
  have ha : 0 < a := by positivity
  set ρa := Real.exp (-a)
  set ρg := (2:ℝ) ^ (-(g / 2))
  set r1 := Real.exp (-(lamT (subK j₀ h2) δ * δ / 2))
  set r2 := (2:ℝ) ^ (-δ)
  set ρ1 := Real.exp (-(lamT (subK j₀ h2) δ / 2))
  set ρ2 := (2:ℝ) ^ (-(1/2:ℝ))
  have hl := lamT_pos (subK j₀ h2) hδ
  have hρa : ρa < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hρg : ρg < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hr1 : r1 < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have hr2 : r2 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hρ1 : ρ1 < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hρ2 : ρ2 < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  set ρ := max (max ρa ρg) (max r1 r2)
  have hρ0 : 0 ≤ ρ := le_trans (Real.exp_pos _).le (le_trans (le_max_left _ _) (le_max_left _ _))
  have hρ : ρ < 1 := max_lt (max_lt hρa hρg) (max_lt hr1 hr2)
  have hL2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set A := (1 + 2 * 2 ^ c) * (c + 1) * Real.log 2 +
    Real.log 2 * (2 * c + 1 / (1 - ρ1) + 1 / (1 - ρ2))
  have hbound : ∀ p : ℕ, Fexc j₀ h2 p ≤ A * (((p:ℝ) + 1) * ρ ^ p) := by
    intro p
    unfold Fexc exc
    have hu' : uB j₀ h2 δ (p + 1) = ((p:ℝ) + 1) * c := by
      unfold uB; push_cast; ring
    rw [hu']
    have hP : (0:ℝ) ≤ p := Nat.cast_nonneg p
    have hlog := log_two_rpow_add_one_le (show 0 ≤ ((p:ℝ) + 1) * c by positivity)
    have hlog' : Real.log ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) ≤ (c + 1) * ((p:ℝ) + 1) * Real.log 2 :=
      hlog.trans (by apply mul_le_mul_of_nonneg_right _ hL2.le; nlinarith)
    have he1 : Real.exp (-(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) ≤ ρ ^ p := by
      rw [show -(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1))) = p * (-a) by simp only [a]; ring,
        Real.exp_nat_mul]
      exact pow_le_pow_left₀ (Real.exp_pos _).le (le_trans (le_max_left _ _) (le_max_left _ _)) p
    have he2 : ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) * thA j₀ δx p ≤ 2 * 2 ^ c * ρ ^ p := by
      have h1 : (1:ℝ) ≤ 2 ^ (((p:ℝ) + 1) * c) := Real.one_le_rpow (by norm_num) (by positivity)
      have hid : (2:ℝ) ^ (((p:ℝ) + 1) * c) * thA j₀ δx p = 2 ^ c * ρg ^ p := by
        unfold thA
        rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_add (by norm_num)]
        congr 1
        simp only [δx, dX, c, δ, dB, h', Hb_eq, g, gapG]; ring
      have hθ : 0 ≤ thA j₀ δx p := by unfold thA; positivity
      calc ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) * thA j₀ δx p
          ≤ 2 * ((2:ℝ) ^ (((p:ℝ) + 1) * c) * thA j₀ δx p) := by nlinarith
        _ = 2 * 2 ^ c * ρg ^ p := by rw [hid]; ring
        _ ≤ 2 * 2 ^ c * ρ ^ p := by
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _)
            (le_trans (le_max_right _ _) (le_max_left _ _)) p) (by positivity)
    have hTb : Tb (subK j₀ h2) δ (p + 1) ≤
        Real.log 2 * (2 * c + 1 / (1 - ρ1) + 1 / (1 - ρ2)) * (((p:ℝ) + 1) * ρ ^ p) := by
      unfold Tb tailB
      simp only [pow_zero, mul_one]
      have h1 : r1 ^ (p + 1) ≤ ρ ^ p := pow_le_of_le (Real.exp_pos _).le
        (le_trans (le_max_left _ _) (le_max_right _ _)) hr1.le p
      have h2'' : r2 ^ (p + 1) ≤ ρ ^ p := pow_le_of_le (by positivity)
        (le_trans (le_max_right _ _) (le_max_right _ _)) hr2.le p
      have hq : ((p + 1 : ℕ) : ℝ) = (p:ℝ) + 1 := by push_cast; ring
      rw [hq]
      have hd1 : 0 < 1 - ρ1 := by linarith
      have hd2 : 0 < 1 - ρ2 := by linarith
      have hρp : 0 ≤ ρ ^ p := pow_nonneg hρ0 p
      have k1 : r1 ^ (p + 1) / (1 - ρ1) ≤ (1 / (1 - ρ1)) * (((p:ℝ) + 1) * ρ ^ p) := by
        rw [div_eq_mul_one_div, mul_comm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      have k2 : r2 ^ (p + 1) / (1 - ρ2) ≤ (1 / (1 - ρ2)) * (((p:ℝ) + 1) * ρ ^ p) := by
        rw [div_eq_mul_one_div, mul_comm]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith
      have k0 : ((p:ℝ) + 1) * c * (r1 ^ (p + 1) + r2 ^ (p + 1)) ≤ 2 * c * (((p:ℝ) + 1) * ρ ^ p) := by
        have : r1 ^ (p + 1) + r2 ^ (p + 1) ≤ 2 * ρ ^ p := by linarith
        have : 0 ≤ ((p:ℝ) + 1) * c := by positivity
        nlinarith
      have := mul_le_mul_of_nonneg_left (add_le_add (add_le_add k0 k1) k2) hL2.le
      calc _ = Real.log 2 * (((p:ℝ) + 1) * c * (r1 ^ (p + 1) + r2 ^ (p + 1)) +
            r1 ^ (p + 1) / (1 - ρ1) + r2 ^ (p + 1) / (1 - ρ2)) := by
            simp only [c, h', r1, r2, ρ1, ρ2]; ring
        _ ≤ _ := this
        _ = _ := by ring
    have hfirst : (Real.exp (-(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) +
          ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) * thA j₀ δx p) *
          Real.log ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) ≤
        (1 + 2 * 2 ^ c) * (c + 1) * Real.log 2 * (((p:ℝ) + 1) * ρ ^ p) := by
      have hs : Real.exp (-(p * δx ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) +
          ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) * thA j₀ δx p ≤ (1 + 2 * 2 ^ c) * ρ ^ p := by
        linarith
      have hl0 : 0 ≤ Real.log ((2:ℝ) ^ (((p:ℝ) + 1) * c) + 1) :=
        Real.log_nonneg (by have : (0:ℝ) ≤ 2 ^ (((p:ℝ) + 1) * c) := by positivity
                            linarith)
      calc _ ≤ ((1 + 2 * 2 ^ c) * ρ ^ p) * ((c + 1) * ((p:ℝ) + 1) * Real.log 2) :=
            mul_le_mul hs hlog' hl0 (by positivity)
        _ = _ := by ring
    have : A * (((p:ℝ) + 1) * ρ ^ p) = (1 + 2 * 2 ^ c) * (c + 1) * Real.log 2 *
        (((p:ℝ) + 1) * ρ ^ p) + Real.log 2 * (2 * c + 1 / (1 - ρ1) + 1 / (1 - ρ2)) *
          (((p:ℝ) + 1) * ρ ^ p) := by simp only [A]; ring
    rw [this]
    exact add_le_add hfirst hTb
  have hsum : Summable fun p : ℕ => A * (((p:ℝ) + 1) * ρ ^ p) := by
    refine Summable.mul_left A ?_
    have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (show ‖ρ‖ < 1 by
      rw [Real.norm_eq_abs, abs_of_nonneg hρ0]; exact hρ)
    have h2'' := summable_geometric_of_lt_one hρ0 hρ
    simpa [add_mul] using h1.add h2''
  exact Summable.of_nonneg_of_le (fun p => exc_nonneg j₀ h2 (by simp only [dB]; have := hg; positivity) _ _)
    hbound hsum

theorem gap_pos (hu : UniqueMax κ j₀) : 0 < gapG j₀ h2 := by
  have := subK_hmax_lt j₀ h2 hu; unfold gapG; linarith

theorem dB_pos (hu : UniqueMax κ j₀) : 0 < dB j₀ h2 := by
  have := gap_pos j₀ h2 hu; unfold dB; positivity

theorem exc_first_le (hu : UniqueMax κ j₀) (p : ℕ) :
    exc j₀ h2 (dB j₀ h2) (dX j₀ h2) p 0 ≤ 3 * Real.log 2 + Tb (subK j₀ h2) (dB j₀ h2) 0 := by
  unfold exc
  have hu0 : uB j₀ h2 (dB j₀ h2) 0 = 0 := by unfold uB; simp
  rw [hu0, Real.rpow_zero, show (1:ℝ) + 1 = 2 by norm_num]
  have hh' := (subK j₀ h2).hmax_nonneg
  have hθ : thA j₀ (dX j₀ h2) p ≤ 1 := by
    unfold thA
    apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
    have : 0 ≤ Hb (κ.K j₀) - dX j₀ h2 := by
      rw [Hb_eq]; unfold dX gapG
      have := subK_hmax_lt j₀ h2 hu; linarith
    have : (0:ℝ) ≤ p := Nat.cast_nonneg p
    nlinarith
  have he : Real.exp (-(p * dX j₀ h2 ^ 2 / (2 * (Mx j₀ ^ 2 + 1)))) ≤ 1 := by
    apply Real.exp_le_one_iff.2
    have : 0 ≤ (p:ℝ) * dX j₀ h2 ^ 2 / (2 * (Mx j₀ ^ 2 + 1)) := by positivity
    linarith
  have hL := Real.log_pos one_lt_two
  nlinarith

/-- **Theorem (strict entropy gap ⇒ bounded residual).** If `j₀` is the unique action
attaining `h_max`, then `C_n ≤ n h_max + K` for a constant `K` independent of `n`. -/
theorem residual_bdd (j₀ : Fin κ.nA) (hu : UniqueMax κ j₀) :
    ∃ K : ℝ, ∀ n : ℕ, κ.costBits n - n * κ.hmax ≤ K := by
  by_cases h2 : 2 ≤ κ.nA
  · have hL := Real.log_pos one_lt_two
    have hδ := dB_pos j₀ h2 hu
    have hδx : 0 ≤ dX j₀ h2 := by have := gap_pos j₀ h2 hu; unfold dX; positivity
    have hS := summable_Fexc j₀ h2 hu
    have hF0 : ∀ p, 0 ≤ Fexc j₀ h2 p := fun p => exc_nonneg j₀ h2 hδ _ _
    refine ⟨(3 * Real.log 2 + Tb (subK j₀ h2) (dB j₀ h2) 0 +
      exc j₀ h2 (dB j₀ h2) (dX j₀ h2) 0 1 + ∑' p, Fexc j₀ h2 p) / Real.log 2,
      κ.residual_bdd_of_subseq nD (fun n => ⟨n, nD_ge n⟩) fun D => ?_⟩
    have hc := costBits_family j₀ h2 hδ hδx D
    rw [hmax_eq_of_unique j₀ hu]
    set f : ℕ → ℝ := fun i => exc j₀ h2 (dB j₀ h2) (dX j₀ h2) (pN D i) (qN D i)
    have hsum : (∑ j : Fin (D + 2), exc j₀ h2 (dB j₀ h2) (dX j₀ h2) (pN D j) (qN D j)) =
        ∑ i ∈ range (D + 2), f i := Fin.sum_univ_eq_sum_range f (D + 2)
    have hsplit : ∑ i ∈ range (D + 2), f i =
        (∑ i ∈ range D, f (i + 1)) + f (D + 1) + f 0 := by
      rw [sum_range_succ', sum_range_succ]
    have hmid : ∀ i ∈ range D, f (i + 1) = Fexc j₀ h2 (D - 1 - i + 1) := by
      intro i hi
      have hi := mem_range.1 hi
      simp only [f, Fexc, pN, qN]
      congr 1 <;> split_ifs <;> omega
    have htop : f (D + 1) = exc j₀ h2 (dB j₀ h2) (dX j₀ h2) 0 1 := by
      simp only [f, pN, qN]; congr 1 <;> split_ifs <;> omega
    have hbot : f 0 = exc j₀ h2 (dB j₀ h2) (dX j₀ h2) (D + 1) 0 := by
      simp only [f, pN, qN]; congr 1 <;> split_ifs <;> omega
    have hmid' : ∑ i ∈ range D, f (i + 1) ≤ ∑' p, Fexc j₀ h2 p := by
      rw [sum_congr rfl hmid,
        sum_range_reflect (fun i => Fexc j₀ h2 (i + 1)) D]
      calc ∑ i ∈ range D, Fexc j₀ h2 (i + 1) ≤ ∑ i ∈ range (D + 1), Fexc j₀ h2 i := by
            rw [sum_range_succ']; linarith [hF0 0]
        _ ≤ _ := hS.sum_le_tsum _ fun i _ => hF0 i
    have hb := exc_first_le j₀ h2 hu (D + 1)
    have htot : (∑ j : Fin (D + 2), exc j₀ h2 (dB j₀ h2) (dX j₀ h2) (pN D j) (qN D j)) ≤
        3 * Real.log 2 + Tb (subK j₀ h2) (dB j₀ h2) 0 +
          exc j₀ h2 (dB j₀ h2) (dX j₀ h2) 0 1 + ∑' p, Fexc j₀ h2 p := by
      rw [hsum, hsplit, htop, hbot]; linarith
    have := div_le_div_of_nonneg_right htot hL.le
    linarith
  · refine ⟨0, fun n => ?_⟩
    have h1 : κ.nA = 1 := by have := j₀.isLt; omega
    have hI : ∃ j f, κ.IsImage j f := by
      refine ⟨j₀, fun a y => if h : a = j₀ then h ▸ y else ⟨0, κ.hY a⟩, fun a z => ?_⟩
      have : a = j₀ := Fin.ext (by have := a.isLt; have := j₀.isLt; omega)
      subst this
      simp [Finset.sum_filter]
    have h12 := (κ.zero_set).out 2 3
    have := h12.1 hI n
    linarith

/-- **Corollary.** Under a unique maximizer the limit `ℓ = lim (C_n - n h_max)` exists and is
finite (the residual is nondecreasing and bounded). -/
theorem residual_limit (j₀ : Fin κ.nA) (hu : UniqueMax κ j₀) :
    ∃ ℓ : ℝ, Filter.Tendsto (fun n : ℕ => κ.costBits n - n * κ.hmax) Filter.atTop (nhds ℓ) := by
  obtain ⟨K, hK⟩ := κ.residual_bdd j₀ hu
  exact ⟨_, κ.residual_tendsto ⟨K, by rintro _ ⟨n, rfl⟩; exact hK n⟩⟩

/-- **Zero set.** Under a unique maximizer, `ℓ = 0` iff every law is a deterministic image
of `K_{j₀}`-type law (some action), iff `C_1 = h_max`. -/
theorem residual_limit_zero_iff (j₀ : Fin κ.nA) (_hu : UniqueMax κ j₀) :
    (∀ n : ℕ, κ.costBits n - n * κ.hmax = 0) ↔ ∃ j f, κ.IsImage j f := by
  exact (forall_congr' fun n => sub_eq_zero).trans ((κ.zero_set).out 2 3).symm

end CausalSpectrum.Kernel

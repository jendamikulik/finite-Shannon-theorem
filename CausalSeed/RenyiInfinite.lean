/-
Rényi spectrum, stage 5: the infinite-horizon theorem.

On a locally finite controlled tree `ι` with positive kernels, assuming one
ordinary exact source exists, there is ONE causal seed `S`, exact at every
horizon, such that for every order `α > 0` simultaneously
  `R_α(Z) ≤ O_α ≤ C_α ≤ H_α(S) ≤ R_α(Z) + d_α`        (`d_1 = c⋆`),
where `O_α` (resp. `C_α`) is the infimum of `H_α` over ordinary exact sources
(resp. exact causal seeds), and `R_α(Z) = sup_n R_α(Z_n)` (`= L_∞` at `α = 1`).
Moreover `H_∞(S) = C_∞ = O_∞`, and for each `α` the four quantities are finite
or infinite together.
-/
import CausalSeed.RenyiLimit

noncomputable section
open Classical Finset Filter
open scoped ENNReal Topology
namespace CausalSpectrum.RenyiInf
open CausalSpectrum.Completion

variable {ι : ITree}

/-- `R_α(Z)` of the infinite envelope, as the increasing limit of `R_α(Z_n)`. -/
def RZ (ι : ITree) (α : ℝ) : ℝ≥0∞ :=
  if α = 1 then LInf ι else ⨆ n, ENNReal.ofReal (Renyi.zRenyi (trunc ι n []) α)

/-- Ordinary optimum `O_α`. -/
def Oα (ι : ITree) (α : ℝ) : ℝ≥0∞ := ⨅ U : OrdSource ι, H α U.w

/-- Causal optimum `C_α`. -/
def Cα (ι : ITree) (α : ℝ) : ℝ≥0∞ := ⨅ G : {G : CountableSeed ι // G.Exact}, H α G.1.weight

def Oinf (ι : ITree) : ℝ≥0∞ := ⨅ U : OrdSource ι, Hinf U.w

def Cinf (ι : ITree) : ℝ≥0∞ := ⨅ G : {G : CountableSeed ι // G.Exact}, Hinf G.1.weight

theorem RZ_le (U : OrdSource ι) {α : ℝ} (hα : 0 < α) : RZ ι α ≤ H α U.w := by
  unfold RZ
  split_ifs with h1
  · subst h1; exact iSup_le fun n => U.envelope_le n
  · exact iSup_le fun n => U.zRenyi_le n hα h1

theorem RZ_le_O {α : ℝ} (hα : 0 < α) : RZ ι α ≤ Oα ι α := le_iInf fun U => RZ_le U hα

theorem O_le_C (α : ℝ) : Oα ι α ≤ Cα ι α :=
  le_iInf fun G => iInf_le_of_le (OrdSource.ofSeed G.1 G.2) le_rfl

theorem Oinf_le_Cinf : Oinf ι ≤ Cinf ι :=
  le_iInf fun G => iInf_le_of_le (OrdSource.ofSeed G.1 G.2) le_rfl

theorem c_nonneg : 0 ≤ shannonOverhead := by
  unfold shannonOverhead
  have := Real.log_pos (show (1:ℝ) < 2 by norm_num)
  positivity

theorem le_of_ofReal_le {x r : ℝ} (hr : 0 ≤ r) (h : ENNReal.ofReal x ≤ ENNReal.ofReal r) :
    x ≤ r := by
  by_contra hn; push_neg at hn
  exact absurd h (not_le.mpr ((ENNReal.ofReal_lt_ofReal_iff (hr.trans_lt hn)).mpr hn))

/-- The upper half: the limit seed is within `d_α` of `R_α(Z)` for all `α` at once. -/
theorem upper (U : OrdSource ι) :
    ∃ R : RankedSeed ι, R.Exact ∧
      ∀ α : ℝ, 0 < α → H α R.weight ≤ RZ ι α + ENNReal.ofReal (dA α) := by
  have htight : ∀ ε > 0, ∃ K, ∀ n, 1 - (gr ι n).head K ≤ ε := fun ε hε => tight U hε
  obtain ⟨R, φ, -, hw, hR⟩ := limit_seed (gr ι) (gr_exactTo ι) htight
  refine ⟨R, hR, fun α hα => ?_⟩
  by_cases htop : RZ ι α = ⊤
  · rw [htop, top_add]; exact le_top
  set r := (RZ ι α).toReal
  have hr0 : 0 ≤ r := ENNReal.toReal_nonneg
  have hr : RZ ι α = ENNReal.ofReal r := (ENNReal.ofReal_toReal htop).symm
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases h1 : α = 1
  · subst h1
    have hRZ : RZ ι 1 = LInf ι := by simp [RZ]
    set c := r + shannonOverhead
    have hc0 : 0 ≤ c := add_nonneg hr0 c_nonneg
    have hn : ∀ n K, (gr ι n).entropyHead K ≤ Real.log 2 * c := by
      intro n K
      have hL : envelopeMean (trunc ι n []) ≤ r := by
        apply le_of_ofReal_le hr0
        rw [← hr, hRZ]
        exact le_iSup (fun n => ENNReal.ofReal (envelopeMean (trunc ι n []))) n
      obtain ⟨hpos, hle, -, -⟩ := Renyi.trace_data (greedyList_trace (trunc ι n []))
      have hs := seedShannon_le_envelope (greedyList_trace (trunc ι n [])) hpos hle
      refine (gr_entropyHead ι n K).trans ?_
      exact mul_le_mul_of_nonneg_left (by simp only [c]; linarith) hl2.le
    have hlim := lim_head_le hw hn
    have hE : R.entropy ≤ ENNReal.ofReal (Real.log 2 * c) :=
      (R.entropy_le_iff (by positivity)).mpr hlim
    rw [R.entropy_eq_tsum] at hE
    unfold H shannonBits
    rw [if_pos rfl]
    calc (∑' i, ENNReal.ofReal (Real.negMulLog (R.weight i))) / ENNReal.ofReal (Real.log 2)
        ≤ ENNReal.ofReal c := by
          apply ENNReal.div_le_of_le_mul
          rwa [← ENNReal.ofReal_mul hc0, mul_comm]
      _ ≤ ENNReal.ofReal r + ENNReal.ofReal shannonOverhead := ENNReal.ofReal_add_le
      _ = _ := by rw [← hr]; simp [dA]
  · have hdA : dA α = Renyi.dAlpha α := by simp [dA, h1]
    rw [hdA]
    set c := r + Renyi.dAlpha α
    have hzr : ∀ n, Renyi.zRenyi (trunc ι n []) α ≤ r := fun n => by
      apply le_of_ofReal_le hr0
      rw [← hr]
      simp only [RZ, if_neg h1]
      exact le_iSup (fun n => ENNReal.ofReal (Renyi.zRenyi (trunc ι n []) α)) n
    -- the finite power sums
    have hL : ∀ n, HasSum (fun k => (gr ι n).weight k ^ α)
        ((greedyList (trunc ι n [])).map fun a => a.1 ^ α).sum := fun n =>
      gr_hasSum ι n (fun x => x ^ α) (Real.zero_rpow hα.ne')
    have hLpos : ∀ n, 0 < ((greedyList (trunc ι n [])).map fun a => a.1 ^ α).sum := fun n => by
      obtain ⟨i, hi⟩ := exists_pos (rlaw (gr ι n))
      exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi α)
        (le_hasSum (hL n) i fun j _ => Real.rpow_nonneg ((gr ι n).nonneg j) _)
    have hseed : ∀ n, Real.logb 2 (((greedyList (trunc ι n [])).map fun a => a.1 ^ α).sum) / (1 - α)
        ≤ c := fun n => by
      have := (Renyi.sandwich_of_trace (greedyList_trace (trunc ι n [])) α hα h1).2
      unfold Renyi.seedRenyi at this
      linarith [hzr n]
    obtain ⟨i0, hi0⟩ := exists_pos (rlaw R)
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · have hpos : 0 < 1 - α := by linarith
      set B := (2:ℝ) ^ ((1 - α) * c)
      have hmom : mom α R.weight ≤ ENNReal.ofReal B := by
        refine lim_mom_le hw hα fun n => ?_
        rw [gr_mom ι n hα]
        apply ENNReal.ofReal_le_ofReal
        rw [← Real.logb_le_iff_le_rpow (by norm_num) (hLpos n)]
        have := hseed n
        rw [div_le_iff₀ hpos] at this
        linarith
      have hne : mom α R.weight ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmom
      have hmpos : 0 < (mom α R.weight).toReal := by
        apply ENNReal.toReal_pos _ hne
        apply ne_of_gt
        calc (0:ℝ≥0∞) < ENNReal.ofReal (R.weight i0 ^ α) :=
              ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hi0 α)
          _ ≤ mom α R.weight := ENNReal.le_tsum (f := fun i => ENNReal.ofReal (R.weight i ^ α)) i0
      have hmB : (mom α R.weight).toReal ≤ B := by
        have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hmom
        rwa [ENNReal.toReal_ofReal (by positivity)] at this
      unfold H renyiNe
      rw [if_neg h1, if_neg hne]
      calc ENNReal.ofReal (Real.logb 2 (mom α R.weight).toReal / (1 - α)) ≤ ENNReal.ofReal c := by
            apply ENNReal.ofReal_le_ofReal
            rw [div_le_iff₀ hpos]
            have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hmpos hmB
            rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
            linarith
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal (Renyi.dAlpha α) := ENNReal.ofReal_add_le
        _ = _ := by rw [← hr]
    · have hneg : 1 - α < 0 := by linarith
      set B := (2:ℝ) ^ ((1 - α) * c)
      have hmom : B ≤ ∑' i, R.weight i ^ α := by
        refine lim_mom_ge hw htight hgt.le fun n => ?_
        rw [(hL n).tsum_eq, ← Real.le_logb_iff_rpow_le (by norm_num) (hLpos n)]
        have := hseed n
        rw [div_le_iff_of_neg hneg] at this
        linarith
      rw [H_of_gt (rlaw R) hgt]
      calc ENNReal.ofReal (hreal α R.weight) ≤ ENNReal.ofReal c := by
            apply ENNReal.ofReal_le_ofReal
            unfold hreal
            rw [div_le_iff_of_neg hneg]
            have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by positivity) hmom
            rw [Real.logb_rpow (by norm_num) (by norm_num)] at this
            linarith
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal (Renyi.dAlpha α) := ENNReal.ofReal_add_le
        _ = _ := by rw [← hr]

/-- `H_∞(S) ≤ H_∞(U)` from the bounds at all orders `α = k + 2`. -/
theorem hinf_le {w u : ℕ → ℝ} (hw : IsLaw w) (hu : IsLaw u)
    (h : ∀ α : ℝ, 1 < α → H α w ≤ H α u + ENNReal.ofReal (Renyi.dAlpha α)) :
    Hinf w ≤ Hinf u := by
  set hU := -Real.logb 2 (⨆ j, u j)
  have hk : ∀ k : ℕ, -Real.logb 2 (⨆ j, w j) ≤ hU + (hU + 1) * (1 / ((k:ℝ) + 1)) := by
    intro k
    set α : ℝ := k + 2
    have hα : 1 < α := by
      have : (0:ℝ) ≤ k := Nat.cast_nonneg k
      simp only [α]; linarith
    have h1 := h α hα
    rw [H_of_gt hw hα, H_of_gt hu hα,
      ← ENNReal.ofReal_add (hreal_nonneg hu hα) (dAlpha_le hα).1,
      ENNReal.ofReal_le_ofReal_iff (add_nonneg (hreal_nonneg hu hα) (dAlpha_le hα).1)] at h1
    have b1 := (hreal_bounds hw hα).1
    have b2 := (hreal_bounds hu hα).2
    have b3 := (dAlpha_le hα).2
    have e1 : α - 1 = (k:ℝ) + 1 := by simp only [α]; ring
    have e2 : α / (α - 1) = 1 + 1 / ((k:ℝ) + 1) := by
      rw [e1]; simp only [α]; field_simp; ring
    rw [e2] at b2; rw [e1] at b3
    nlinarith
  have hlim : Tendsto (fun k : ℕ => hU + (hU + 1) * (1 / ((k:ℝ) + 1))) atTop (𝓝 hU) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (hU + 1)
    simpa using this.const_add hU
  exact ENNReal.ofReal_le_ofReal (ge_of_tendsto' hlim hk)

/-- **Main theorem (infinite horizon, all orders at once).** -/
theorem one_seed_all_orders (hU : Nonempty (OrdSource ι)) :
    ∃ S : CountableSeed ι, S.Exact ∧
      (∀ α : ℝ, 0 < α →
        RZ ι α ≤ Oα ι α ∧ Oα ι α ≤ Cα ι α ∧ Cα ι α ≤ H α S.weight ∧
          H α S.weight ≤ RZ ι α + ENNReal.ofReal (dA α)) ∧
      Hinf S.weight = Cinf ι ∧ Cinf ι = Oinf ι := by
  obtain ⟨U⟩ := hU
  obtain ⟨R, hR, hup⟩ := upper U
  let S := R.toCountable
  have hS : S.Exact := fun n => (R.toCountable_exactTo n).mpr (hR n)
  have hSw : S.weight = R.weight := rfl
  have hCS : ∀ α, Cα ι α ≤ H α S.weight := fun α => iInf_le_of_le ⟨S, hS⟩ le_rfl
  have hall : ∀ α : ℝ, 0 < α →
      RZ ι α ≤ Oα ι α ∧ Oα ι α ≤ Cα ι α ∧ Cα ι α ≤ H α S.weight ∧
        H α S.weight ≤ RZ ι α + ENNReal.ofReal (dA α) := fun α hα =>
    ⟨RZ_le_O hα, O_le_C α, hCS α, hSw ▸ hup α hα⟩
  have hinfS : Hinf S.weight ≤ Oinf ι := by
    refine le_iInf fun V => hinf_le (rlaw R) V.law fun α hα => ?_
    have h1 := hup α (by linarith)
    have hd : dA α = Renyi.dAlpha α := by simp [dA, hα.ne']
    rw [hd] at h1
    have h2 := RZ_le V (show 0 < α by linarith)
    exact h1.trans (by gcongr)
  have hCinf : Cinf ι ≤ Hinf S.weight := iInf_le_of_le ⟨S, hS⟩ le_rfl
  refine ⟨S, hS, hall, le_antisymm (hinfS.trans Oinf_le_Cinf) hCinf,
    le_antisymm (hCinf.trans hinfS) Oinf_le_Cinf⟩

/-- **Corollary (simultaneous finiteness / attainment).**  With `S` as above, for every
`α > 0`: `H_α(S) ≤ O_α + d_α`, and `R_α(Z)`, `O_α`, `C_α`, `H_α(S)` are finite or
infinite together. -/
theorem simultaneous_finiteness (hU : Nonempty (OrdSource ι)) :
    ∃ S : CountableSeed ι, S.Exact ∧ ∀ α : ℝ, 0 < α →
      H α S.weight ≤ Oα ι α + ENNReal.ofReal (dA α) ∧
      (RZ ι α < ⊤ ↔ Oα ι α < ⊤) ∧ (Oα ι α < ⊤ ↔ Cα ι α < ⊤) ∧
      (Cα ι α < ⊤ ↔ H α S.weight < ⊤) := by
  obtain ⟨S, hS, hall, -⟩ := one_seed_all_orders hU
  refine ⟨S, hS, fun α hα => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hall α hα
  have hfin : RZ ι α < ⊤ → H α S.weight < ⊤ := fun h =>
    lt_of_le_of_lt h4 (ENNReal.add_lt_top.mpr ⟨h, ENNReal.ofReal_lt_top⟩)
  refine ⟨h4.trans (by gcongr), ⟨fun h => ?_, fun h => h1.trans_lt h⟩,
    ⟨fun h => ?_, fun h => h2.trans_lt h⟩, ⟨fun h => ?_, fun h => h3.trans_lt h⟩⟩
  · exact h2.trans_lt (h3.trans_lt (hfin h))
  · exact h3.trans_lt (hfin (h1.trans_lt h))
  · exact hfin (h1.trans_lt (h2.trans_lt h))

#print axioms upper
#print axioms one_seed_all_orders
#print axioms simultaneous_finiteness

end CausalSpectrum.RenyiInf

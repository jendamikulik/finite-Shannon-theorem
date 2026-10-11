/-
Universality for *countable* exact seeds with finite entropy.

For a countable seed `G` exact to horizon `n`, `J = -log₂ w(S)` has tail
`cTail G t = ∑' i, w_i 1[t < I(w_i)]` and CDF `cCDF G t = 1 - cTail G t`.
* `cTail_ge`: `1 - F*_n(t) ≤ cTail G t` (stochastic domination, through the coupling).
* `lintegral_cTail`: `∫⁻_{t>0} cTail = H(G)/ln 2`.
* `gap_total_countable`: `∫_ℝ |cCDF - F*_n| = E J - L_n` when `H(G) < ∞`.
* `Kernel.universality_countable`: the W₁ (CDF-L¹) universality corollary.
-/
import CausalSeed.SqrtUniversality
import CausalSeed.RenyiFinite

noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal Topology
namespace CausalSpectrum.Completion
namespace CountableSeed
variable {ι : ITree}

def cTail (G : CountableSeed ι) (t : ℝ) : ℝ :=
  ∑' i, (if t < infoMass (G.weight i) then G.weight i else 0)

def cCDF (G : CountableSeed ι) (t : ℝ) : ℝ := 1 - G.cTail t

/-- `E J` in bits. -/
def bits (G : CountableSeed ι) : ℝ := G.entropy.toReal / Real.log 2

theorem term_nonneg (G : CountableSeed ι) (t : ℝ) (i : ℕ) :
    0 ≤ (if t < infoMass (G.weight i) then G.weight i else 0) := by
  split_ifs; exacts [G.nonneg i, le_rfl]

theorem term_le (G : CountableSeed ι) (t : ℝ) (i : ℕ) :
    (if t < infoMass (G.weight i) then G.weight i else 0) ≤ G.weight i := by
  split_ifs; exacts [le_rfl, G.nonneg i]

theorem term_summable (G : CountableSeed ι) (t : ℝ) :
    Summable fun i => (if t < infoMass (G.weight i) then G.weight i else 0) :=
  Summable.of_nonneg_of_le (G.term_nonneg t) (G.term_le t) G.mass.summable

theorem cTail_le_one (G : CountableSeed ι) (t : ℝ) : G.cTail t ≤ 1 := by
  rw [← G.mass.tsum_eq]
  exact Summable.tsum_le_tsum (G.term_le t) (G.term_summable t) G.mass.summable

theorem cTail_nonneg (G : CountableSeed ι) (t : ℝ) : 0 ≤ G.cTail t :=
  tsum_nonneg (G.term_nonneg t)

theorem cTail_anti (G : CountableSeed ι) : Antitone G.cTail := fun s t hst =>
  Summable.tsum_le_tsum (fun i => by
    split_ifs with h1 h2 <;> first | exact le_rfl | exact G.nonneg i | linarith)
    (G.term_summable t) (G.term_summable s)

theorem info_nonneg_w (G : CountableSeed ι) (i : ℕ) : 0 ≤ infoMass (G.weight i) := by
  unfold infoMass
  have := Real.logb_nonpos (b := 2) (by norm_num) (G.nonneg i) (G.weight_le_one i)
  linarith

theorem cTail_neg (G : CountableSeed ι) {t : ℝ} (ht : t < 0) : G.cTail t = 1 := by
  unfold cTail
  rw [← G.mass.tsum_eq]
  congr 1; funext i
  rw [if_pos (lt_of_lt_of_le ht (G.info_nonneg_w i))]

theorem infoMass_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : infoMass b ≤ infoMass a := by
  unfold infoMass
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) ha hab
  linarith

/-- **Stochastic domination** `Z_n ≼st J`. -/
theorem cTail_ge (G : CountableSeed ι) (n : ℕ) (hG : G.ExactTo n) (t : ℝ) :
    1 - Fstar (trunc ι n []) t ≤ G.cTail t := by
  set Γ := G.coupling n hG
  refine (CausalSpectrum.Renyi.coup_tail_ge (trunc ι n []) Γ t).trans ?_
  have hstep : ∀ α, (if t < infoMass (Γ.mass α) then Γ.mass α else 0) ≤
      ∑' i, (if t < infoMass (G.weight i) then G.part n α i else 0) := by
    intro α
    split_ifs with h
    · show ∑' i, G.part n α i ≤ _
      refine Summable.tsum_le_tsum (fun i => ?_) (G.part_summable n α) ?_
      · by_cases hp : G.part n α i = 0
        · rw [hp]; split_ifs; exacts [le_rfl, le_rfl]
        · have hpi : G.part n α i = G.weight i := by
            unfold part at hp ⊢; split_ifs at hp ⊢; rfl; exact absurd rfl hp
          have hw : 0 < G.weight i := lt_of_le_of_ne (G.nonneg i) (by rw [← hpi]; exact Ne.symm hp)
          have hle : G.weight i ≤ Γ.mass α := by
            rw [← hpi]; exact le_hasSum (G.part_summable n α).hasSum i fun j _ => G.part_nonneg n α j
          rw [if_pos (lt_of_lt_of_le h (infoMass_anti hw hle))]
      · exact Summable.of_nonneg_of_le (fun i => by split_ifs; exacts [G.part_nonneg n α i, le_rfl])
          (fun i => by split_ifs; exacts [le_rfl, G.part_nonneg n α i]) (G.part_summable n α)
    · exact tsum_nonneg fun i => by split_ifs; exacts [G.part_nonneg n α i, le_rfl]
  refine (Finset.sum_le_sum fun α _ => hstep α).trans (le_of_eq ?_)
  rw [← Summable.tsum_finsetSum (fun α _ => Summable.of_nonneg_of_le
    (fun i => by split_ifs; exacts [G.part_nonneg n α i, le_rfl])
    (fun i => by split_ifs; exacts [le_rfl, G.part_nonneg n α i]) (G.part_summable n α))]
  unfold cTail
  congr 1; funext i
  split_ifs with h
  · exact G.sum_part n i
  · simp

theorem cTail_meas (G : CountableSeed ι) : Measurable G.cTail := G.cTail_anti.measurable

/-- Layer cake: `∫⁻_{t>0} P(J > t) = H(G)/ln 2`. -/
theorem lintegral_cTail (G : CountableSeed ι) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (G.cTail t) = G.entropy / ENNReal.ofReal (Real.log 2) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold cTail
  have e1 : ∀ t, ENNReal.ofReal (∑' i, (if t < infoMass (G.weight i) then G.weight i else 0)) =
      ∑' i, ENNReal.ofReal (if t < infoMass (G.weight i) then G.weight i else 0) := fun t =>
    ENNReal.ofReal_tsum_of_nonneg (G.term_nonneg t) (G.term_summable t)
  simp_rw [e1]
  have hts := lintegral_tsum (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun i t => ENNReal.ofReal (if t < infoMass (G.weight i) then G.weight i else 0))
    (fun i => (ENNReal.measurable_ofReal.comp (Measurable.ite measurableSet_Iio
    measurable_const measurable_const)).aemeasurable)
  rw [hts]
  unfold entropy
  rw [div_eq_mul_inv, ← ENNReal.tsum_mul_right]
  congr 1; funext i
  have e2 : (fun t => ENNReal.ofReal (if t < infoMass (G.weight i) then G.weight i else 0)) =
      (Iio (infoMass (G.weight i))).indicator fun _ => ENNReal.ofReal (G.weight i) := by
    funext t; simp only [indicator, mem_Iio]; split_ifs <;> simp
  rw [e2, lintegral_indicator measurableSet_Iio, setLIntegral_const, Measure.restrict_apply
    measurableSet_Iio, Iio_inter_Ioi, Real.volume_Ioo, sub_zero, ← ENNReal.ofReal_mul (G.nonneg i)]
  rw [← div_eq_mul_inv, ENNReal.eq_div_iff (ENNReal.ofReal_pos.mpr hl).ne' ENNReal.ofReal_ne_top,
    ← ENNReal.ofReal_mul hl.le]
  congr 1
  rw [← log_two_mul_entTerm]
  unfold entTerm
  split_ifs with h
  · rw [h]; ring
  · ring

theorem integrableOn_cTail (G : CountableSeed ι) (hfin : G.entropy ≠ ⊤) :
    IntegrableOn G.cTail (Ioi 0) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨G.cTail_meas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ G.cTail_nonneg), lintegral_cTail]
  exact ENNReal.div_lt_top hfin (ENNReal.ofReal_pos.mpr hl).ne'

theorem integral_cTail (G : CountableSeed ι) (hfin : G.entropy ≠ ⊤) :
    ∫ t in Ioi (0:ℝ), G.cTail t = G.bits := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ G.cTail_nonneg)
    G.cTail_meas.aestronglyMeasurable, lintegral_cTail, ENNReal.toReal_div,
    ENNReal.toReal_ofReal hl.le, bits]

/-- `∫_ℝ |cCDF - F*_n| = E J - L_n`. -/
theorem gap_total_countable (G : CountableSeed ι) (n : ℕ) (hG : G.ExactTo n)
    (hfin : G.entropy ≠ ⊤) :
    Integrable (fun t => |G.cCDF t - Fstar (trunc ι n []) t|) ∧
      ∫ t, |G.cCDF t - Fstar (trunc ι n []) t| = G.bits - envelopeMean (trunc ι n []) := by
  set T := trunc ι n []
  have habs : ∀ t, |G.cCDF t - Fstar T t| = G.cTail t - (1 - Fstar T t) := fun t => by
    rw [abs_of_nonpos (by unfold cCDF; linarith [G.cTail_ge n hG t])]; unfold cCDF; ring
  have hz : ∀ t ∉ Ici (0:ℝ), |G.cCDF t - Fstar T t| = 0 := fun t ht => by
    have ht' : t < 0 := by simpa using ht
    rw [habs, G.cTail_neg ht', Kernel.Fstar_neg T ht']; ring
  have hIoi : IntegrableOn (fun t => |G.cCDF t - Fstar T t|) (Ioi 0) := by
    simp_rw [habs]; exact (G.integrableOn_cTail hfin).sub (integrableOn_one_sub_Fstar T)
  have hIci : IntegrableOn (fun t => |G.cCDF t - Fstar T t|) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr hIoi
  refine ⟨hIci.integrable_of_forall_notMem_eq_zero hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_Ici_eq_integral_Ioi]
  simp_rw [habs]
  rw [integral_sub (G.integrableOn_cTail hfin) (integrableOn_one_sub_Fstar T),
    G.integral_cTail hfin, integral_one_sub_Fstar]

theorem cCDF_mono (G : CountableSeed ι) : Monotone G.cCDF := fun s t hst => by
  unfold cCDF; linarith [G.cTail_anti hst]

end CountableSeed
end CausalSpectrum.Completion

namespace CausalSpectrum.Kernel
open Sqrt Completion
variable (κ : Kernel)

/-- **Universality for countable exact seeds with finite entropy (W₁ in CDF form).**
If `a > 0`, `G n` is a countable seed exact to horizon `n` with `H(G n) < ∞` and
`E J_n - C_n = o(√n)`, then `∫_ℝ |P(J_n ≤ nh + x√n) - F_{a,b}(x)| dx → 0`. -/
theorem universality_countable {h : ℝ} (hh : κ.EqualEntropy h) (ha : 0 < (κ.fam h).sA)
    (G : ℕ → CountableSeed κ.toITree) (hG : ∀ n, (G n).ExactTo n) (hfin : ∀ n, (G n).entropy ≠ ⊤)
    (hopt : Tendsto (fun n : ℕ => ((G n).bits - κ.costBits n) / Real.sqrt n) atTop (𝓝 0)) :
    (∀ n, 1 ≤ n → Integrable fun x => |(G n).cCDF (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|) ∧
    Tendsto (fun n : ℕ => ∫ x, |(G n).cCDF (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|)
      atTop (𝓝 0) := by
  set F := κ.fam h
  have hc := κ.fam_centered hh
  have hT : ∀ n, trunc κ.toITree n [] = κ.rounds n := fun n => κ.trunc_toITree n []
  have hG' : ∀ n (x : ℝ), Fstar (trunc κ.toITree n []) (n * h + x * Real.sqrt n) =
      F.G n (x * Real.sqrt n) := fun n x => by
    rw [hT, κ.Fstar_eq_G h]; congr 1; ring
  set A := fun (n : ℕ) (x : ℝ) => |(G n).cCDF (n * h + x * Real.sqrt n) -
    Fstar (trunc κ.toITree n []) (n * h + x * Real.sqrt n)|
  have hAint : ∀ n, 1 ≤ n → Integrable (A n) := fun n hn => by
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    exact (((G n).gap_total_countable n (hG n) (hfin n)).1.comp_add_left (n * h)).comp_mul_right'
      hs.ne'
  have hAval : ∀ n, 1 ≤ n → ∫ x, A n x =
      ((G n).bits - envelopeMean (κ.rounds n)) / Real.sqrt n := fun n hn => by
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have := integral_affine (fun t => |(G n).cCDF t - Fstar (trunc κ.toITree n []) t|) (n * h) hs
    rw [show (∫ x, A n x) = _ from this, ((G n).gap_total_countable n (hG n) (hfin n)).2, hT]
    field_simp
  have hpt : ∀ n (x : ℝ), |(G n).cCDF (n * h + x * Real.sqrt n) - F.Flim x| ≤
      A n x + |F.G n (x * Real.sqrt n) - F.Flim x| := fun n x => by
    simp only [A, hG' n x]; exact abs_sub_le _ _ _
  have hint : ∀ n, 1 ≤ n → Integrable fun x =>
      |(G n).cCDF (n * h + x * Real.sqrt n) - F.Flim x| := fun n hn => by
    refine ((hAint n hn).add (F.integrable_gap hc ha hn)).mono' ?_
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hpt n x)
    exact (continuous_abs.measurable.comp (((G n).cCDF_mono.measurable.comp
      ((measurable_const.add (measurable_id.mul_const _)))).sub
      (F.Flim_measurable hc ha))).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have hCL : Tendsto (fun n : ℕ => (κ.costBits n - envelopeMean (κ.rounds n)) / Real.sqrt n)
      atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => shannonOverhead / Real.sqrt n) atTop (𝓝 0) := by
      have := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      simpa [div_eq_mul_inv] using this.const_mul shannonOverhead
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
      (by linarith [(κ.costBits_sandwich n).1]) (Real.sqrt_nonneg _)) ?_ hs
    exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (by linarith [(κ.costBits_sandwich n).2]) (Real.sqrt_nonneg _)
  have hgap : Tendsto (fun n : ℕ => ((G n).bits - envelopeMean (κ.rounds n)) / Real.sqrt n)
      atTop (𝓝 0) := by
    have := hopt.add hCL
    rw [add_zero] at this
    exact this.congr fun n => by ring
  have hup := hgap.add (F.L1_tendsto hc ha)
  rw [add_zero] at hup
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun x => abs_nonneg _) ?_ hup
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← hAval n hn, ← integral_add (hAint n hn) (F.integrable_gap hc ha hn)]
  exact integral_mono (hint n hn) ((hAint n hn).add (F.integrable_gap hc ha hn)) (hpt n)

end CausalSpectrum.Kernel

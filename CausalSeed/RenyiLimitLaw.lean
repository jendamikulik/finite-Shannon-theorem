/-
Rényi note: the limit envelope variable `Z` and its genuine moments.

`Z` is represented by its law on `[0, ∞]` with CDF `F_∞ = inf_n F_n` (`FInf`) on `[0,∞)`,
i.e. tail `P(Z > t) = 1 - F_∞(t)`, and mass `1 - atomQ` at `+∞`
(`atomQ_eq_lim_FInf`).  Its moments are given by the tail (layer-cake) formula
`E 2^{λZ} = 1 + ∫_0^∞ λ ln 2 · 2^{λt} (1 - F_∞(t)) dt`
(for `λ > 0` in `[0,∞]`, so that atoms at `+∞` give `+∞`; for `λ < 0` as a real number,
with `2^{λ·∞} = 0`) and `E Z = ∫_0^∞ (1 - F_∞)`.  At a finite horizon the same formula is
`zMoment_layer`.  No measure object is constructed: the law enters only through its tail.

Main result: `RZlaw ι α = RZ ι α` for every `α > 0` (no extra hypothesis:
monotone convergence for `α ≤ 1`, dominated convergence for `α > 1`), using the new
horizon monotonicity `F_{n+1} ≤ F_n` (`Fstar_succ_le`).
-/
import CausalSeed.RenyiInfinite
import CausalSeed.AtomicSpectrum
import CausalSeed.Gap

noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal Topology

namespace CausalSpectrum
open Finset in
theorem policyCDF_deepen (ι : ITree) (h : List (ℕ × ℕ)) (n : ℕ) (π : Policy (trunc ι n h)) (t : ℝ) :
    policyCDF (trunc ι (n + 1) h) (deepenPolicy ι h n π) t ≤ policyCDF (trunc ι n h) π t := by
  set ρ := deepenPolicy ι h n π
  set g := projectLeaf ι h n
  rw [policyCDF_eq, policyCDF_eq, ← Finset.sum_filter, ← Finset.sum_filter]
  set D := (univ.filter fun ℓ : Leaf (trunc ι (n+1) h) => CompatiblePolicy ℓ ρ).filter
    fun ℓ => infoMass (leafMass ℓ) ≤ t
  set E := (univ.filter fun ℓ : Leaf (trunc ι n h) => CompatiblePolicy ℓ π).filter
    fun ℓ => infoMass (leafMass ℓ) ≤ t
  have hD : ∀ ℓ ∈ D, CompatiblePolicy ℓ ρ := fun ℓ hℓ => by
    simp only [D, mem_filter] at hℓ; exact hℓ.1.2
  have hsingle : ∀ ℓ, CompatiblePolicy ℓ ρ → leafMass ℓ ≤ leafMass (g ℓ) := fun ℓ hℓ => by
    have := fiber_le ι h n π {ℓ} (by simpa using hℓ) (g ℓ) (project_compatible ι h n π ℓ hℓ)
    rwa [Finset.filter_singleton, if_pos rfl, Finset.sum_singleton] at this
  have hsub : D.image g ⊆ E := by
    intro σ hσ
    obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hσ
    simp only [D, E, Finset.mem_filter, Finset.mem_univ, true_and] at hℓ ⊢
    refine ⟨project_compatible ι h n π ℓ hℓ.1, le_trans ?_ hℓ.2⟩
    have h1 := hsingle ℓ hℓ.1
    unfold infoMass
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (leafMass_pos ℓ) h1
    linarith
  calc ∑ ℓ ∈ D, leafMass ℓ
      = ∑ σ ∈ D.image g, ∑ ℓ ∈ D.filter fun ℓ => g ℓ = σ, leafMass ℓ :=
        (sum_fiberwise_of_maps_to (fun ℓ hℓ => mem_image_of_mem g hℓ) _).symm
    _ ≤ ∑ σ ∈ D.image g, leafMass σ := sum_le_sum fun σ hσ => by
        obtain ⟨ℓ, hℓ, rfl⟩ := mem_image.mp hσ
        exact fiber_le ι h n π D hD _ (project_compatible ι h n π ℓ (hD ℓ hℓ))
    _ ≤ ∑ σ ∈ E, leafMass σ := sum_le_sum_of_subset_of_nonneg hsub fun σ _ _ => (leafMass_pos σ).le
end CausalSpectrum

namespace CausalSpectrum.RenyiInf
open CausalSpectrum.Completion CausalSpectrum.Renyi

variable (ι : ITree)

theorem Fstar_succ_le (n : ℕ) (t : ℝ) :
    Fstar (trunc ι (n + 1) []) t ≤ Fstar (trunc ι n []) t :=
  (Fstar_le _ t _).trans (policyCDF_deepen ι [] n (envelopePolicy _ t) t)

/-- Horizon monotonicity: `F_n(t)` is antitone in `n`. -/
theorem Fstar_anti (t : ℝ) : Antitone fun n => Fstar (trunc ι n []) t :=
  antitone_nat_of_succ_le fun n => Fstar_succ_le ι n t

theorem Fstar_tendsto (t : ℝ) :
    Tendsto (fun n => Fstar (trunc ι n []) t) atTop (𝓝 (FInf ι t)) :=
  tendsto_atTop_ciInf (Fstar_anti ι t) (FInf_bdd ι t)

theorem Fstar_le_one (T : Tree) (t : ℝ) : Fstar T t ≤ 1 := policyCDF_le_one _ _

theorem FInf_le_one (t : ℝ) : FInf ι t ≤ 1 := (FInf_le ι t 0).trans (Fstar_le_one _ t)

theorem FInf_nonneg (t : ℝ) : 0 ≤ FInf ι t := le_ciInf fun n => Fstar_nonneg _ t

/-- `E 2^{λZ}` for `λ = 1 - α > 0`, in `[0, ∞]`. -/
def zMomLaw (α : ℝ) : ℝ≥0∞ :=
  1 + ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (gw (1 - α) t * (1 - FInf ι t))

/-- `E 2^{λZ}` for `λ = 1 - α < 0`, a real number in `[0,1]`. -/
def zMomLawR (α : ℝ) : ℝ := 1 + ∫ t in Ioi (0:ℝ), gw (1 - α) t * (1 - FInf ι t)

/-- `E Z` in `[0, ∞]`. -/
def zMeanLaw : ℝ≥0∞ := ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 - FInf ι t)

/-- The genuine `R_α(Z) = (1-α)⁻¹ log₂ E 2^{(1-α)Z}` (`E Z` at `α = 1`), with values in
`[0, ∞]`: `+∞` when the moment is `+∞` (`α < 1`) or `0` (`α > 1`). -/
def RZlaw (α : ℝ) : ℝ≥0∞ :=
  if α = 1 then zMeanLaw ι
  else if α < 1 then
    (if zMomLaw ι α = ⊤ then ⊤ else ENNReal.ofReal (Real.logb 2 (zMomLaw ι α).toReal / (1 - α)))
  else (if zMomLawR ι α ≤ 0 then ⊤ else ENNReal.ofReal (Real.logb 2 (zMomLawR ι α) / (1 - α)))

theorem Fstar_meas (T : Tree) : Measurable (Fstar T) := (Fstar_mono T).measurable

theorem FInf_meas : Measurable (FInf ι) := (FInf_mono ι).measurable

/-- Monotone convergence for the weighted tails. -/
theorem sup_lint {w : ℝ → ℝ} (hw : Measurable w) (hw0 : ∀ t, 0 ≤ w t) :
    ⨆ n, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (w t * (1 - Fstar (trunc ι n []) t)) =
      ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (w t * (1 - FInf ι t)) := by
  have hmono : Monotone fun n t => ENNReal.ofReal (w t * (1 - Fstar (trunc ι n []) t)) :=
    fun m n hmn t => ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left (by linarith [Fstar_anti ι t hmn]) (hw0 t))
  have hL := lintegral_iSup (μ := volume.restrict (Ioi (0:ℝ)))
    (f := fun n t => ENNReal.ofReal (w t * (1 - Fstar (trunc ι n []) t)))
    (fun n => ENNReal.measurable_ofReal.comp
      (hw.mul (measurable_const.sub (Fstar_meas _)))) hmono
  rw [← hL]
  congr 1; funext t
  refine tendsto_nhds_unique (tendsto_atTop_iSup fun m n hmn => hmono hmn t) ?_
  exact ENNReal.tendsto_ofReal (((Fstar_tendsto ι t).const_sub 1).const_mul (w t))

/-- `α = 1`: `E Z = L_∞`. -/
theorem zMeanLaw_eq : zMeanLaw ι = LInf ι := by
  unfold zMeanLaw LInf
  have := sup_lint ι (w := fun _ => 1) measurable_const (fun _ => zero_le_one)
  simp only [one_mul] at this
  rw [← this]
  congr 1; funext n
  rw [← integral_one_sub_Fstar, ofReal_integral_eq_lintegral_ofReal
    (integrableOn_one_sub_Fstar _)
    (ae_of_all _ fun t => by simp only [Pi.zero_apply]; linarith [Fstar_le_one (trunc ι n []) t])]

/-- `α < 1`: `E 2^{(1-α)Z} = sup_n E 2^{(1-α)Z_n}`. -/
theorem zMomLaw_eq {α : ℝ} (hα : α < 1) :
    zMomLaw ι α = ⨆ n, ENNReal.ofReal (zMoment (trunc ι n []) (1 - α)) := by
  have hl : 0 ≤ 1 - α := by linarith
  unfold zMomLaw
  rw [← sup_lint ι (Renyi.continuous_gw _).measurable (gw_nonneg hl), ENNReal.add_iSup]
  congr 1; funext n
  obtain ⟨hi, he⟩ := zMoment_layer (trunc ι n []) (1 - α)
  rw [he, ENNReal.ofReal_add zero_le_one (setIntegral_nonneg measurableSet_Ioi fun t _ =>
      mul_nonneg (gw_nonneg hl t) (by linarith [Fstar_le_one (trunc ι n []) t])),
    ENNReal.ofReal_one, ofReal_integral_eq_lintegral_ofReal hi
      (ae_of_all _ fun t => mul_nonneg (gw_nonneg hl t) (by linarith [Fstar_le_one (trunc ι n []) t]))]

theorem integrableOn_gw {l : ℝ} (hl : l < 0) : IntegrableOn (gw l) (Ioi 0) := by
  have hb : 0 < -l * Real.log 2 := mul_pos (by linarith) (Real.log_pos (by norm_num))
  have : IntegrableOn (fun x => l * Real.log 2 * Real.exp (-(-l * Real.log 2) * x)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 hb).const_mul (l * Real.log 2)
  refine this.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only [gw, rpow_two_eq]; congr 2; ring

/-- `α > 1`: `E 2^{(1-α)Z_n} → E 2^{(1-α)Z}` (dominated convergence). -/
theorem zMomLawR_tendsto {α : ℝ} (hα : 1 < α) :
    Tendsto (fun n => zMoment (trunc ι n []) (1 - α)) atTop (𝓝 (zMomLawR ι α)) := by
  have hl : 1 - α < 0 := by linarith
  have e : ∀ n, zMoment (trunc ι n []) (1 - α) =
      1 + ∫ t in Ioi (0:ℝ), gw (1 - α) t * (1 - Fstar (trunc ι n []) t) :=
    fun n => (zMoment_layer _ _).2
  simp_rw [e]
  refine tendsto_const_nhds.add ?_
  refine tendsto_integral_of_dominated_convergence (fun t => |gw (1 - α) t|)
    (fun n => ((Renyi.continuous_gw _).measurable.mul
      (measurable_const.sub (Fstar_meas _))).aestronglyMeasurable)
    (integrableOn_gw hl).abs (fun n => ae_of_all _ fun t => ?_)
    (ae_of_all _ fun t => ((Fstar_tendsto ι t).const_sub 1).const_mul _)
  rw [Real.norm_eq_abs, abs_mul]
  have h0 := Fstar_nonneg (trunc ι n []) t
  have h1 := Fstar_le_one (trunc ι n []) t
  calc |gw (1 - α) t| * |1 - Fstar (trunc ι n []) t| ≤ |gw (1 - α) t| * 1 := by
        gcongr; rw [abs_le]; constructor <;> linarith
    _ = _ := mul_one _

theorem zMoment_anti {α : ℝ} (hα : 1 < α) :
    Antitone fun n => zMoment (trunc ι n []) (1 - α) := fun m n hmn => by
  have hl : 1 - α ≤ 0 := by linarith
  show zMoment _ _ ≤ zMoment _ _
  rw [(zMoment_layer (trunc ι n []) _).2, (zMoment_layer (trunc ι m []) _).2]
  gcongr 1
  refine setIntegral_mono_on (zMoment_layer _ _).1 (zMoment_layer _ _).1 measurableSet_Ioi
    fun t _ => mul_le_mul_of_nonpos_left (by linarith [Fstar_anti ι t hmn]) (gw_nonpos hl t)

/-- `sup` of `ofReal ∘ φ` along a monotone real sequence converging to `S`. -/
theorem iSup_ofReal_of_tendsto {u : ℕ → ℝ} (hu : Monotone u) {S : ℝ}
    (h : Tendsto u atTop (𝓝 S)) : ⨆ n, ENNReal.ofReal (u n) = ENNReal.ofReal S :=
  tendsto_nhds_unique (tendsto_atTop_iSup fun m n hmn => ENNReal.ofReal_le_ofReal (hu hmn))
    (ENNReal.tendsto_ofReal h)

theorem iSup_ofReal_top {u : ℕ → ℝ} (h : ∀ B : ℝ, ∃ n, B < u n) :
    ⨆ n, ENNReal.ofReal (u n) = ⊤ := by
  refine iSup_eq_top.mpr fun b hb => ?_
  obtain ⟨n, hn⟩ := h (b.toReal + 1)
  refine ⟨n, ?_⟩
  rw [← ENNReal.ofReal_toReal hb.ne]
  exact (ENNReal.ofReal_lt_ofReal_iff (by linarith [ENNReal.toReal_nonneg (a := b)])).mpr
    (by linarith)

theorem tendsto_logb_div {u : ℕ → ℝ} {S : ℝ} (hS : 0 < S) (h : Tendsto u atTop (𝓝 S)) (l : ℝ) :
    Tendsto (fun n => Real.logb 2 (u n) / l) atTop (𝓝 (Real.logb 2 S / l)) := by
  have := ((Real.continuousAt_log hS.ne').tendsto.comp h).div_const (Real.log 2)
  simpa [Real.logb] using this.div_const l

/-- **`R_α(Z) = sup_n R_α(Z_n)`** for every `α > 0`, infinite values included. -/
theorem RZlaw_eq {α : ℝ} (hα : 0 < α) : RZlaw ι α = RZ ι α := by
  unfold RZlaw RZ
  by_cases h1 : α = 1
  · simp only [if_pos h1]; exact zMeanLaw_eq ι
  simp only [if_neg h1]
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rcases lt_or_gt_of_ne h1 with hlt | hgt
  · rw [if_pos hlt]
    have hl : 0 < 1 - α := by linarith
    set m := fun n => zMoment (trunc ι n []) (1 - α)
    have hmono : Monotone m := fun i j hij => by
      have := zMomLaw_eq ι hlt
      show zMoment _ _ ≤ zMoment _ _
      rw [(zMoment_layer (trunc ι j []) _).2, (zMoment_layer (trunc ι i []) _).2]
      gcongr 1
      exact setIntegral_mono_on (zMoment_layer _ _).1 (zMoment_layer _ _).1 measurableSet_Ioi
        fun t _ => mul_le_mul_of_nonneg_left (by linarith [Fstar_anti ι t hij])
          (gw_nonneg hl.le t)
    have hpos : ∀ n, 0 < m n := fun n => zMoment_pos _ _
    have hR : ∀ n, zRenyi (trunc ι n []) α = Real.logb 2 (m n) / (1 - α) := fun n => rfl
    simp only [hR]
    have hφ : Monotone fun n => Real.logb 2 (m n) / (1 - α) := fun i j hij =>
      div_le_div_of_nonneg_right (Real.logb_le_logb_of_le (by norm_num) (hpos i) (hmono hij)) hl.le
    by_cases hb : BddAbove (Set.range m)
    · have ht := tendsto_atTop_ciSup hmono hb
      set S := ⨆ n, m n
      have hS : 0 < S := lt_of_lt_of_le (hpos 0) (le_ciSup hb 0)
      rw [zMomLaw_eq ι hlt, iSup_ofReal_of_tendsto hmono ht, if_neg ENNReal.ofReal_ne_top,
        ENNReal.toReal_ofReal hS.le]
      exact (iSup_ofReal_of_tendsto hφ (tendsto_logb_div hS ht _)).symm
    · have hun : ∀ B : ℝ, ∃ n, B < m n := fun B => by
        by_contra hc; push_neg at hc; exact hb ⟨B, by rintro _ ⟨n, rfl⟩; exact hc n⟩
      rw [zMomLaw_eq ι hlt, iSup_ofReal_top hun, if_pos rfl]
      refine (iSup_ofReal_top fun B => ?_).symm
      obtain ⟨n, hn⟩ := hun ((2:ℝ) ^ (B * (1 - α)))
      refine ⟨n, ?_⟩
      rw [lt_div_iff₀ hl]
      exact (Real.lt_logb_iff_rpow_lt (by norm_num) (hpos n)).mpr hn
  · rw [if_neg (not_lt.mpr hgt.le)]
    have hl : 1 - α < 0 := by linarith
    set m := fun n => zMoment (trunc ι n []) (1 - α)
    have hpos : ∀ n, 0 < m n := fun n => zMoment_pos _ _
    have ht := zMomLawR_tendsto ι hgt
    have hanti := zMoment_anti ι hgt
    have hR : ∀ n, zRenyi (trunc ι n []) α = Real.logb 2 (m n) / (1 - α) := fun n => rfl
    simp only [hR]
    have hφ : Monotone fun n => Real.logb 2 (m n) / (1 - α) := fun i j hij =>
      div_le_div_of_nonpos_of_le hl.le
        (Real.logb_le_logb_of_le (by norm_num) (hpos j) (hanti hij))
    by_cases hL : zMomLawR ι α ≤ 0
    · rw [if_pos hL]
      refine (iSup_ofReal_top fun B => ?_).symm
      have hc : (0:ℝ) < (2:ℝ) ^ (B * (1 - α)) := by positivity
      obtain ⟨n, hn⟩ := (ht.eventually (gt_mem_nhds (lt_of_le_of_lt hL hc))).exists
      refine ⟨n, ?_⟩
      rw [lt_div_iff_of_neg hl]
      exact (Real.logb_lt_iff_lt_rpow (by norm_num) (hpos n)).mpr hn
    · rw [if_neg hL]
      push_neg at hL
      exact (iSup_ofReal_of_tendsto hφ (tendsto_logb_div hL ht _)).symm

/-- **Main theorem restated with the genuine `R_α(Z)`.** -/
theorem one_seed_all_orders_law (hU : Nonempty (OrdSource ι)) :
    ∃ S : CountableSeed ι, S.Exact ∧
      (∀ α : ℝ, 0 < α →
        RZlaw ι α ≤ Oα ι α ∧ Oα ι α ≤ Cα ι α ∧ Cα ι α ≤ H α S.weight ∧
          H α S.weight ≤ RZlaw ι α + ENNReal.ofReal (dA α)) ∧
      Hinf S.weight = Cinf ι ∧ Cinf ι = Oinf ι := by
  obtain ⟨S, hS, hall, h2⟩ := one_seed_all_orders hU
  exact ⟨S, hS, fun α hα => by rw [RZlaw_eq ι hα]; exact hall α hα, h2⟩

#print axioms policyCDF_deepen
#print axioms Fstar_anti
#print axioms zMeanLaw_eq
#print axioms zMomLaw_eq
#print axioms zMomLawR_tendsto
#print axioms RZlaw_eq
#print axioms one_seed_all_orders_law

end CausalSpectrum.RenyiInf

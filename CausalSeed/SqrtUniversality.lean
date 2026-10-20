/-
Square-root note, Corollary "Universality of asymptotically optimal seeds".

`W₁` between laws on `ℝ` is formalized by its CDF form
`W₁(μ, ν) = ∫_ℝ |F_μ(x) - F_ν(x)| dx` (valid for laws with finite first moment);
we prove convergence of this integral (and integrability of the integrand).

* Analytic core: `∫ |G_n(x√n) - F_{a,b}(x)| dx → 0` for `a > 0`
  (`F_{a,0}` is the half-normal profile `F0`).
* Corollary: for exact finite seeds `S_n` of `κ.rounds n` with
  `(E J_n - C_n)/√n → 0`, the CDF of `(J_n - nh)/√n` converges to `F_{a,b}` in `L¹(ℝ)`.
-/
import CausalSeed.SqrtGeneral
import CausalSeed.Gap
import CausalSeed.AtomicSpectrum

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum.Sqrt

namespace IncFamily
variable (F : IncFamily)

/-- The limit profile `F_{a,b}` (half-normal `F0` when `b = 0`). -/
def Flim (x : ℝ) : ℝ := if 0 < F.sB then prof F.sA F.sB x else F0 F.sA x

theorem sB_nonneg : 0 ≤ F.sB :=
  Finset.le_inf' _ _ fun j _ => Real.sqrt_nonneg _

theorem pointwise (hc : F.Centered) (ha : 0 < F.sA) (x : ℝ) :
    Tendsto (fun n : ℕ => F.G n (x * Real.sqrt n)) atTop (𝓝 (F.Flim x)) := by
  unfold Flim
  split_ifs with hb
  · rw [Metric.tendsto_atTop]
    intro δ hδ
    obtain ⟨N, hN⟩ := eventually_atTop.mp (F.cdfErr_eventually hc hb (half_pos hδ))
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have h1 : (1:ℝ) ≤ Real.sqrt n := by
      rw [show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
    have := F.cdf_comparison hc hb hn1 h1 (Real.sqrt_nonneg (Real.log n)) x
    rw [Real.dist_eq]
    linarith [hN n (le_of_max_le_left hn)]
  · have hb0 : F.sB = 0 := le_antisymm (not_lt.mp hb) F.sB_nonneg
    exact F.pointwise_b0 hc hb0 ha x

theorem Flim_measurable (hc : F.Centered) (ha : 0 < F.sA) : Measurable F.Flim :=
  measurable_of_tendsto_metrizable (fun n => (F.G_measurable n).comp (measurable_id.mul_const _))
    (tendsto_pi_nhds.mpr fun x => F.pointwise hc ha x)

theorem Flim_mem (hc : F.Centered) (ha : 0 < F.sA) (x : ℝ) : 0 ≤ F.Flim x ∧ F.Flim x ≤ 1 := by
  have hl := F.pointwise hc ha x
  have hb := fun n => (F.G_cdf n).2.2.1 (x * Real.sqrt n)
  exact ⟨ge_of_tendsto' hl fun n => (hb n).1, le_of_tendsto' hl fun n => (hb n).2⟩

theorem Flim_upper (hc : F.Centered) (ha : 0 < F.sA) {x : ℝ} (hx : 0 < x) :
    1 - F.Flim x ≤ gM F.M x := by
  have hl := (tendsto_const_nhds (x := (1:ℝ))).sub (F.pointwise hc ha x)
  refine le_of_tendsto hl ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact F.G_upper_tail hc (n := n) (by omega) hx

theorem Flim_lower (hc : F.Centered) (ha : 0 < F.sA) {x : ℝ} (hx : 0 < x) :
    F.Flim (-x) ≤ gM F.M x := by
  refine le_of_tendsto (F.pointwise hc ha (-x)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [neg_mul]
  exact F.G_lower_tail hc (n := n) (by omega) hx

theorem gM_neg (M x : ℝ) : gM M (-x) = gM M x := by simp [gM]

theorem dom (hc : F.Centered) (ha : 0 < F.sA) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |F.G n (x * Real.sqrt n) - F.Flim x| ≤ gM F.M x := by
  have hG := (F.G_cdf n).2.2.1 (x * Real.sqrt n)
  have hF := F.Flim_mem hc ha x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have hy : 0 < -x := by linarith
    have h1 := F.G_lower_tail hc (n := n) (by omega) hy
    have h2 := F.Flim_lower hc ha hy
    rw [neg_neg, gM_neg] at *
    rw [show -(-x * Real.sqrt n) = x * Real.sqrt n by ring] at h1
    have h1' : F.G n (x * Real.sqrt n) ≤ gM F.M x := by rw [← gM_neg]; exact h1
    rw [abs_le]; constructor <;> linarith
  · have : gM F.M 0 = 1 := by simp [gM]
    rw [this, abs_le]; constructor <;> linarith
  · have h1 := F.G_upper_tail hc (n := n) (by omega) hx
    have h2 := F.Flim_upper hc ha hx
    have h1' : 1 - F.G n (x * Real.sqrt n) ≤ gM F.M x := h1
    rw [abs_le]; constructor <;> linarith

theorem integrable_gap (hc : F.Centered) (ha : 0 < F.sA) {n : ℕ} (hn : 1 ≤ n) :
    Integrable fun x => |F.G n (x * Real.sqrt n) - F.Flim x| := by
  have hM : 0 < F.M := lt_of_lt_of_le ha F.sA_le_M
  refine (integrable_gM hM).mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (continuous_abs.measurable.comp (((F.G_measurable n).comp
      (measurable_id.mul_const _)).sub (F.Flim_measurable hc ha))).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_abs]; exact F.dom hc ha hn x

/-- **Analytic core.** `∫_ℝ |G_n(x√n) - F_{a,b}(x)| dx → 0` when `a > 0`. -/
theorem L1_tendsto (hc : F.Centered) (ha : 0 < F.sA) :
    Tendsto (fun n : ℕ => ∫ x, |F.G n (x * Real.sqrt n) - F.Flim x|) atTop (𝓝 0) := by
  have hM : 0 < F.M := lt_of_lt_of_le ha F.sA_le_M
  have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) (x : ℝ) => |F.G n (x * Real.sqrt n) - F.Flim x|)
    (f := fun _ => (0:ℝ)) (gM F.M)
    (Eventually.of_forall fun n => (continuous_abs.measurable.comp (((F.G_measurable n).comp
      (measurable_id.mul_const _)).sub (F.Flim_measurable hc ha))).aestronglyMeasurable)
    (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      exact ae_of_all _ fun x => by rw [Real.norm_eq_abs, abs_abs]; exact F.dom hc ha hn x)
    (integrable_gM hM)
    (ae_of_all _ fun x => by
      have := ((F.pointwise hc ha x).sub_const (F.Flim x)).abs
      simpa using this)
  simpa using h

end IncFamily
end CausalSpectrum.Sqrt

namespace CausalSpectrum.Kernel
open Sqrt
variable (κ : Kernel)

theorem integral_affine (g : ℝ → ℝ) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ x, g (c + x * s) = s⁻¹ * ∫ t, g t := by
  have h1 := Measure.integral_comp_mul_right (fun y => g (c + y)) s
  rw [h1, integral_add_left_eq_self (fun y => g y) c, smul_eq_mul, abs_of_pos (inv_pos.mpr hs)]

theorem seedCDF_neg {T : Tree} (atoms : List (Atom T)) (hpos : ∀ a ∈ atoms, 0 < a.1)
    (hle : ∀ a ∈ atoms, a.1 ≤ 1) {t : ℝ} (ht : t < 0) : seedCDF atoms t = 0 := by
  unfold seedCDF
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  have : 0 ≤ infoMass a.1 := by
    have := Real.logb_nonpos (b := 2) (by norm_num) (hpos a ha).le (hle a ha)
    simp only [infoMass]; linarith
  rw [if_neg (by linarith)]

theorem Fstar_neg (T : Tree) {t : ℝ} (ht : t < 0) : Fstar T t = 0 := by
  apply le_antisymm _ (Fstar_nonneg T t)
  refine (Fstar_le T t (defaultPolicy T)).trans (le_of_eq ?_)
  rw [CausalSpectrum.policyCDF_eq]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  rw [if_neg (by linarith [infoMass_nonneg ℓ])]

/-- The total CDF gap over `ℝ` equals the Shannon gap (`one_seed_wasserstein` form). -/
theorem gap_total {T : Tree} {atoms : List (Atom T)}
    (hexact : ∀ (π : Policy T) (ℓ : Leaf T),
      transcriptWeight atoms π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (hle : ∀ a ∈ atoms, a.1 ≤ 1)
    (htot : totalWeight atoms = 1) :
    Integrable (fun t => |seedCDF atoms t - Fstar T t|) ∧
      ∫ t, |seedCDF atoms t - Fstar T t| = seedShannon atoms - envelopeMean T := by
  have hz : ∀ t ∉ Ici (0:ℝ), |seedCDF atoms t - Fstar T t| = 0 := fun t ht => by
    have ht' : t < 0 := by simpa using ht
    rw [seedCDF_neg atoms hpos hle ht', Fstar_neg T ht']; simp
  have hsym : (fun t => |seedCDF atoms t - Fstar T t|) = fun t => |Fstar T t - seedCDF atoms t| :=
    funext fun t => abs_sub_comm _ _
  have hIoi : IntegrableOn (fun t => |seedCDF atoms t - Fstar T t|) (Ioi 0) := by
    rw [hsym]; exact (integrableOn_cdfGap atoms hpos hle htot).abs
  have hIci : IntegrableOn (fun t => |seedCDF atoms t - Fstar T t|) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp)).mpr hIoi
  refine ⟨hIci.integrable_of_forall_notMem_eq_zero hz, ?_⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz, integral_Ici_eq_integral_Ioi, hsym]
  exact wasserstein_gap hexact hpos hle htot

theorem seedCDF_mono {T : Tree} : ∀ (atoms : List (Atom T)), (∀ a ∈ atoms, 0 < a.1) →
    Monotone (seedCDF atoms)
  | [], _ => fun s t _ => by simp [seedCDF]
  | a :: l, hpos => fun s t hst => by
    have ih := seedCDF_mono l (fun b hb => hpos b (List.mem_cons_of_mem a hb)) hst
    have ha := hpos a (List.mem_cons_self)
    simp only [seedCDF, List.map_cons, List.sum_cons] at ih ⊢
    refine add_le_add ?_ ih
    split_ifs with h1 h2 <;> first | exact le_rfl | exact ha.le | linarith | exact absurd (h1.trans hst) h2

theorem atom_le_one {T : Tree} {atoms : List (Atom T)} (hpos : ∀ a ∈ atoms, 0 < a.1)
    (htot : totalWeight atoms = 1) : ∀ a ∈ atoms, a.1 ≤ 1 := by
  intro a ha
  rw [← htot]
  unfold totalWeight
  exact List.single_le_sum (fun x hx => by
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx; exact (hpos b hb).le) _ (List.mem_map.mpr ⟨a, ha, rfl⟩)

/-- **Universality (W₁ in CDF form), with the Shannon-gap hypothesis.** -/
theorem universality_of_gap {h : ℝ} (hh : κ.EqualEntropy h) (ha : 0 < (κ.fam h).sA)
    (atoms : ∀ n, List (Atom (κ.rounds n)))
    (hexact : ∀ n (π : Policy (κ.rounds n)) (ℓ : Leaf (κ.rounds n)),
      transcriptWeight (atoms n) π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ n, ∀ a ∈ atoms n, 0 < a.1) (htot : ∀ n, totalWeight (atoms n) = 1)
    (hgap : Tendsto (fun n : ℕ => (seedShannon (atoms n) - envelopeMean (κ.rounds n)) / Real.sqrt n)
      atTop (𝓝 0)) :
    (∀ n, 1 ≤ n → Integrable fun x =>
        |seedCDF (atoms n) (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|) ∧
    Tendsto (fun n : ℕ => ∫ x, |seedCDF (atoms n) (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|)
      atTop (𝓝 0) := by
  set F := κ.fam h
  have hc := κ.fam_centered hh
  have hle := fun n => atom_le_one (hpos n) (htot n)
  have hG : ∀ n (x : ℝ), Fstar (κ.rounds n) (n * h + x * Real.sqrt n) = F.G n (x * Real.sqrt n) :=
    fun n x => by rw [κ.Fstar_eq_G h]; congr 1; ring
  -- the seed-vs-envelope piece
  set A := fun (n : ℕ) (x : ℝ) =>
    |seedCDF (atoms n) (n * h + x * Real.sqrt n) - Fstar (κ.rounds n) (n * h + x * Real.sqrt n)|
  have hAint : ∀ n, 1 ≤ n → Integrable (A n) := fun n hn => by
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have := (gap_total (hexact n) (hpos n) (hle n) (htot n)).1
    exact (this.comp_add_left (n * h)).comp_mul_right' hs.ne'
  have hAval : ∀ n, 1 ≤ n → ∫ x, A n x =
      (seedShannon (atoms n) - envelopeMean (κ.rounds n)) / Real.sqrt n := fun n hn => by
    have hs : (0:ℝ) < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have := integral_affine (fun t => |seedCDF (atoms n) t - Fstar (κ.rounds n) t|) (n * h) hs
    rw [show (∫ x, A n x) = _ from this, (gap_total (hexact n) (hpos n) (hle n) (htot n)).2]
    field_simp
  have hpt : ∀ n (x : ℝ), |seedCDF (atoms n) (n * h + x * Real.sqrt n) - F.Flim x| ≤
      A n x + |F.G n (x * Real.sqrt n) - F.Flim x| := fun n x => by
    simp only [A, ← hG n x]; exact abs_sub_le _ _ _
  have hint : ∀ n, 1 ≤ n → Integrable fun x =>
      |seedCDF (atoms n) (n * h + x * Real.sqrt n) - F.Flim x| := fun n hn => by
    refine ((hAint n hn).add (F.integrable_gap hc ha hn)).mono' ?_
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs, abs_abs]; exact hpt n x)
    have hmono := seedCDF_mono (atoms n) (hpos n)
    exact (continuous_abs.measurable.comp ((hmono.measurable.comp
      ((measurable_const.add (measurable_id.mul_const _)))).sub
      (F.Flim_measurable hc ha))).aestronglyMeasurable
  refine ⟨hint, ?_⟩
  have hup : Tendsto (fun n : ℕ => (seedShannon (atoms n) - envelopeMean (κ.rounds n)) / Real.sqrt n
      + ∫ x, |F.G n (x * Real.sqrt n) - F.Flim x|) atTop (𝓝 0) := by
    simpa using hgap.add (F.L1_tendsto hc ha)
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun x => abs_nonneg _) ?_ hup
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [← hAval n hn, ← integral_add (hAint n hn) (F.integrable_gap hc ha hn)]
  exact integral_mono (hint n hn) ((hAint n hn).add (F.integrable_gap hc ha hn)) (hpt n)

/-- **Corollary (Universality of asymptotically optimal seeds).** If `a > 0` and exact
seeds satisfy `E J_n - C_n = o(√n)` (`C_n = costBits n`, the optimal exact-seed entropy),
the CDF of `(J_n - nh)/√n` converges to `F_{a,b}` in `L¹(ℝ)`, i.e. in `W₁`. -/
theorem universality {h : ℝ} (hh : κ.EqualEntropy h) (ha : 0 < (κ.fam h).sA)
    (atoms : ∀ n, List (Atom (κ.rounds n)))
    (hexact : ∀ n (π : Policy (κ.rounds n)) (ℓ : Leaf (κ.rounds n)),
      transcriptWeight (atoms n) π ℓ = if CompatiblePolicy ℓ π then leafMass ℓ else 0)
    (hpos : ∀ n, ∀ a ∈ atoms n, 0 < a.1) (htot : ∀ n, totalWeight (atoms n) = 1)
    (hopt : Tendsto (fun n : ℕ => (seedShannon (atoms n) - κ.costBits n) / Real.sqrt n)
      atTop (𝓝 0)) :
    (∀ n, 1 ≤ n → Integrable fun x =>
        |seedCDF (atoms n) (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|) ∧
    Tendsto (fun n : ℕ => ∫ x, |seedCDF (atoms n) (n * h + x * Real.sqrt n) - (κ.fam h).Flim x|)
      atTop (𝓝 0) := by
  apply κ.universality_of_gap hh ha atoms hexact hpos htot
  have hCL : Tendsto (fun n : ℕ => (κ.costBits n - envelopeMean (κ.rounds n)) / Real.sqrt n)
      atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => shannonOverhead / Real.sqrt n) atTop (𝓝 0) := by
      have := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
      simpa [div_eq_mul_inv] using this.const_mul shannonOverhead
    refine squeeze_zero' (Eventually.of_forall fun n => div_nonneg
      (by linarith [(κ.costBits_sandwich n).1]) (Real.sqrt_nonneg _)) ?_ hs
    exact Eventually.of_forall fun n => div_le_div_of_nonneg_right
      (by linarith [(κ.costBits_sandwich n).2]) (Real.sqrt_nonneg _)
  have := hopt.add hCL
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring

#print axioms CausalSpectrum.Sqrt.IncFamily.L1_tendsto
#print axioms universality_of_gap
#print axioms universality

end CausalSpectrum.Kernel

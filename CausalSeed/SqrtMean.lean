/-
Stage 4: the normalized envelope mean, the explicit mean bound (meanbound).
`Mn n = ∫₀^∞ [1 - G_n(x√n)] dx - ∫₀^∞ G_n(-x√n) dx` is the right side of
(meanidentity).
-/
import CausalSeed.SqrtCompare

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum.Sqrt

/-- `e^{R²/2} ∫_R^∞ e^{-x²/2}` is antitone on `[0,∞)`, hence `2Φ(-R) ≤ e^{-R²/2}`. -/
theorem gaussTail_le_exp {R : ℝ} (hR : 0 ≤ R) :
    gaussTail R ≤ Real.exp (-(R ^ 2) / 2) * gaussTail 0 := by
  set g := fun r : ℝ => Real.exp (r ^ 2 / 2) * gaussTail r
  have hd : ∀ r, HasDerivAt g (r * Real.exp (r ^ 2 / 2) * gaussTail r -
      Real.exp (r ^ 2 / 2) * gaussRaw r) r := by
    intro r
    have h1 : HasDerivAt (fun r : ℝ => Real.exp (r ^ 2 / 2)) (Real.exp (r ^ 2 / 2) * r) r := by
      have := ((hasDerivAt_pow 2 r).div_const 2).exp
      exact this.congr_deriv (by norm_num)
    exact (h1.mul (hasDerivAt_gaussTail r)).congr_deriv (by ring)
  have hanti : AntitoneOn g (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro r _; exact (hd r).continuousAt.continuousWithinAt
    · intro r _; exact (hd r).differentiableAt.differentiableWithinAt
    · intro r hr
      rw [interior_Ici] at hr
      rw [(hd r).deriv]
      have hr' : 0 < r := hr
      have := gaussTail_le r hr'
      have hE := Real.exp_pos (r ^ 2 / 2)
      have : r * gaussTail r ≤ gaussRaw r := by rwa [le_div_iff₀ hr', mul_comm] at this
      nlinarith
  have := hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr hR) hR
  simp only [g, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    Real.exp_zero, one_mul] at this
  have e : gaussTail R = Real.exp (-(R ^ 2) / 2) * (Real.exp (R ^ 2 / 2) * gaussTail R) := by
    rw [← mul_assoc, ← Real.exp_add, show -(R ^ 2) / 2 + R ^ 2 / 2 = 0 by ring, Real.exp_zero,
      one_mul]
  rw [e]
  exact mul_le_mul_of_nonneg_left this (Real.exp_pos _).le

theorem two_PhiNeg_le {R : ℝ} (hR : 0 ≤ R) : 2 * PhiNeg R ≤ Real.exp (-(R ^ 2) / 2) := by
  have := gaussTail_le_exp hR
  rw [gaussTail_zero] at this
  have hs := sqrt2pi_pos
  unfold PhiNeg
  rw [mul_div_assoc', div_le_iff₀ hs]
  nlinarith

/-! ### Gaussian tail integrals -/

def gM (M x : ℝ) : ℝ := Real.exp (-(x ^ 2 / (2 * M ^ 2)))

theorem gM_eq (M x : ℝ) : gM M x = Real.exp (-(1 / (2 * M ^ 2)) * x ^ 2) := by
  unfold gM; congr 1; ring

theorem integrable_gM {M : ℝ} (hM : 0 < M) : Integrable (gM M) := by
  have := integrable_exp_neg_mul_sq (b := 1 / (2 * M ^ 2)) (by positivity)
  exact this.congr (ae_of_all _ fun x => (gM_eq M x).symm)

theorem gM_nonneg (M x : ℝ) : 0 ≤ gM M x := (Real.exp_pos _).le

theorem tail_integral_gM {M r : ℝ} (hM : 0 < M) (hr : 0 < r) :
    ∫ x in Ioi r, gM M x ≤ M ^ 2 / r * gM M r := by
  have hint : Integrable fun x : ℝ => x * gM M x := by
    have := integrable_mul_exp_neg_mul_sq (b := 1 / (2 * M ^ 2)) (by positivity)
    exact this.congr (ae_of_all _ fun x => by simp only [gM_eq])
  have hderiv : ∀ x ∈ Ici r, HasDerivAt (fun x => -(M ^ 2) * gM M x) (x * gM M x) x := by
    intro x _
    unfold gM
    have := (((hasDerivAt_pow 2 x).div_const (2 * M ^ 2)).neg.exp).const_mul (-(M ^ 2))
    refine this.congr_deriv ?_
    simp only [Pi.neg_apply]
    field_simp
    norm_num
    ring
  have hlim : Tendsto (fun x => -(M ^ 2) * gM M x) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => gM M x) atTop (𝓝 0) := by
      unfold gM
      apply Real.tendsto_exp_atBot.comp
      apply tendsto_neg_atTop_atBot.comp
      apply Tendsto.atTop_div_const (by positivity)
      exact tendsto_pow_atTop two_ne_zero
    simpa using this.const_mul (-(M ^ 2))
  have hI := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint.integrableOn hlim
  have hmono : ∫ x in Ioi r, gM M x ≤ ∫ x in Ioi r, x / r * gM M x := by
    apply setIntegral_mono_on (integrable_gM hM).integrableOn
    · exact IntegrableOn.congr_fun (f := fun x => x * gM M x / r)
        (hint.integrableOn.div_const r) (fun x _ => by ring) measurableSet_Ioi
    · exact measurableSet_Ioi
    · intro x hx
      have : 1 ≤ x / r := by rw [le_div_iff₀ hr]; linarith [mem_Ioi.mp hx]
      nlinarith [gM_nonneg M x]
  have e : ∫ x in Ioi r, x / r * gM M x = (∫ x in Ioi r, x * gM M x) / r := by
    rw [← integral_div]; congr 1; funext x; ring
  rw [e, hI] at hmono
  calc _ ≤ (0 - -(M ^ 2) * gM M r) / r := hmono
    _ = _ := by ring

/-- Split at `r`: a function bounded by `c` and by `gM` has integral at most
`r c + (M²/r) gM(r)` over `(0,∞)`. -/
theorem split_integral {M r c : ℝ} (hM : 0 < M) (hr : 0 < r) {h : ℝ → ℝ}
    (hmeas : AEStronglyMeasurable h (volume.restrict (Ioi 0)))
    (h0 : ∀ x ∈ Ioi (0:ℝ), 0 ≤ h x) (hc : ∀ x ∈ Ioi (0:ℝ), h x ≤ c)
    (hg : ∀ x ∈ Ioi (0:ℝ), h x ≤ gM M x) :
    ∫ x in Ioi 0, h x ≤ r * c + M ^ 2 / r * gM M r := by
  have hint : IntegrableOn h (Ioi 0) := by
    refine Integrable.mono' (integrable_gM hM).integrableOn hmeas ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun x hx => by rw [Real.norm_eq_abs, abs_of_nonneg (h0 x hx)]; exact hg x hx
  rw [← Ioc_union_Ioi_eq_Ioi hr.le, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
    (hint.mono_set Ioc_subset_Ioi_self) (hint.mono_set (Ioi_subset_Ioi hr.le))]
  have h1 : ∫ x in Ioc 0 r, h x ≤ ∫ x in Ioc 0 r, c := by
    apply setIntegral_mono_on (hint.mono_set Ioc_subset_Ioi_self)
    · exact integrableOn_const (by simp) (by simp)
    · exact measurableSet_Ioc
    · intro x hx; exact hc x (Ioc_subset_Ioi_self hx)
  have h2 : ∫ x in Ioi r, h x ≤ ∫ x in Ioi r, gM M x := by
    apply setIntegral_mono_on (hint.mono_set (Ioi_subset_Ioi hr.le))
      (integrable_gM hM).integrableOn measurableSet_Ioi
    intro x hx; exact hg x (Ioi_subset_Ioi hr.le hx)
  have h3 := tail_integral_gM hM hr
  have e : ∫ x in Ioc 0 r, c = r * c := by
    simp [hr.le]
  linarith

/-! ### Tails of the profile -/

variable {a b : ℝ}

theorem prof_upper_tail (ha : 0 < a) (hb : 0 < b) {M x : ℝ} (haM : a ≤ M) (hx : 0 < x) :
    1 - prof a b x ≤ gM M x := by
  rw [one_sub_prof ha hb hx]
  unfold profilePos
  have h1 := two_PhiNeg_le (show 0 ≤ x / a by positivity)
  have h2 : 2 * a / (a + b) * (gaussTail (x / a) / Real.sqrt (2 * Real.pi)) ≤ 2 * PhiNeg (x / a) := by
    unfold PhiNeg
    have := PhiNeg_nonneg (x / a); unfold PhiNeg at this
    have : 2 * a / (a + b) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  refine h2.trans (h1.trans ?_)
  unfold gM
  rw [Real.exp_le_exp, div_pow]
  have hM : 0 < M := lt_of_lt_of_le ha haM
  rw [neg_div, neg_le_neg_iff, div_div, div_le_div_iff_of_pos_left (by positivity) (by positivity)
    (by positivity)]
  nlinarith [pow_le_pow_left₀ ha.le haM 2]

theorem prof_lower_tail (ha : 0 < a) (hb : 0 < b) {M x : ℝ} (hab : b ≤ a) (haM : a ≤ M)
    (hx : 0 < x) : prof a b (-x) ≤ gM M x := by
  rw [prof_neg ha hb hx]
  unfold profileNeg
  have h1 := two_PhiNeg_le (show 0 ≤ x / b by positivity)
  have h2 : 2 * b / (a + b) * (gaussTail (x / b) / Real.sqrt (2 * Real.pi)) ≤ 2 * PhiNeg (x / b) := by
    unfold PhiNeg
    have := PhiNeg_nonneg (x / b); unfold PhiNeg at this
    have : 2 * b / (a + b) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    nlinarith
  refine h2.trans (h1.trans ?_)
  unfold gM
  rw [Real.exp_le_exp, div_pow]
  have hM : 0 < M := lt_of_lt_of_le ha haM
  rw [neg_div, neg_le_neg_iff, div_div, div_le_div_iff_of_pos_left (by positivity) (by positivity)
    (by positivity)]
  nlinarith [pow_le_pow_left₀ hb.le (hab.trans haM) 2]

namespace IncFamily
variable (F : IncFamily)

theorem sigma_le_M (j) : F.sigma j ≤ F.M := by
  unfold sigma
  rw [Real.sqrt_le_left F.M_nonneg]
  calc F.sig2 j ≤ ∑ y, F.P j y * F.M ^ 2 := by
        apply Finset.sum_le_sum; intro y _
        apply mul_le_mul_of_nonneg_left _ (F.Ppos _ _).le
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (F.abs_X_le j y) 2
    _ = F.M ^ 2 := by rw [← Finset.sum_mul, F.Psum, one_mul]

theorem sA_le_M : F.sA ≤ F.M := Finset.sup'_le _ _ fun j _ => F.sigma_le_M j

/-- Right side of (meanidentity): the normalized, centered envelope mean. -/
def Mn (n : ℕ) : ℝ :=
  (∫ x in Ioi (0:ℝ), (1 - F.G n (x * Real.sqrt n))) - ∫ x in Ioi (0:ℝ), F.G n (-(x * Real.sqrt n))

theorem G_measurable (n : ℕ) : Measurable (F.G n) := (F.G_cdf n).1.measurable

/-- **Mean bound (meanbound).** `|Mn - μ_{a,b}| ≤ 2 r e_n + (2M²/r) e^{-r²/(2M²)}`;
this is sharper than the note's `4M²/r` and implies it. -/
theorem mean_bound (hc : F.Centered) (hb : 0 < F.sB) {n : ℕ} (hn : 1 ≤ n) {m : ℝ} (hm : 1 ≤ m)
    {R : ℝ} (hR : 0 ≤ R) {r : ℝ} (hr : 0 < r) :
    |F.Mn n - secondOrderCoeff F.sA F.sB| ≤
      2 * r * F.cdfErr n m R + 2 * (F.M ^ 2 / r) * gM F.M r := by
  set a := F.sA
  set b := F.sB
  have hab : b ≤ a := F.sB_le_sA
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have haM : a ≤ F.M := F.sA_le_M
  have hM : 0 < F.M := lt_of_lt_of_le ha haM
  have hn0 : 0 < n := by omega
  set e := F.cdfErr n m R
  -- the four functions
  set f1 := fun x : ℝ => 1 - F.G n (x * Real.sqrt n)
  set f2 := fun x : ℝ => 1 - prof a b x
  set f3 := fun x : ℝ => F.G n (-(x * Real.sqrt n))
  set f4 := fun x : ℝ => prof a b (-x)
  have hGb := fun x => (F.G_cdf n).2.2.1 x
  have m1 : Measurable f1 :=
    measurable_const.sub ((F.G_measurable n).comp (measurable_id.mul_const _))
  have m3 : Measurable f3 :=
    (F.G_measurable n).comp ((measurable_id.mul_const _).neg)
  have m2 : Measurable f2 := measurable_const.sub (prof_monotone ha hb).measurable
  have m4 : Measurable f4 := (prof_monotone ha hb).measurable.comp measurable_neg
  have t1 : ∀ x ∈ Ioi (0:ℝ), 0 ≤ f1 x ∧ f1 x ≤ gM F.M x := fun x hx =>
    ⟨by simp only [f1]; linarith [(hGb (x * Real.sqrt n)).2], F.G_upper_tail hc hn0 hx⟩
  have t2 : ∀ x ∈ Ioi (0:ℝ), 0 ≤ f2 x ∧ f2 x ≤ gM F.M x := fun x hx =>
    ⟨by simp only [f2]; linarith [prof_le_one ha hb x], prof_upper_tail ha hb haM hx⟩
  have t3 : ∀ x ∈ Ioi (0:ℝ), 0 ≤ f3 x ∧ f3 x ≤ gM F.M x := fun x hx =>
    ⟨(hGb _).1, F.G_lower_tail hc hn0 hx⟩
  have t4 : ∀ x ∈ Ioi (0:ℝ), 0 ≤ f4 x ∧ f4 x ≤ gM F.M x := fun x hx =>
    ⟨prof_nonneg ha hb _, prof_lower_tail ha hb hab haM hx⟩
  have integ : ∀ f : ℝ → ℝ, Measurable f → (∀ x ∈ Ioi (0:ℝ), 0 ≤ f x ∧ f x ≤ gM F.M x) →
      IntegrableOn f (Ioi 0) := by
    intro f hf ht
    refine Integrable.mono' (integrable_gM hM).integrableOn hf.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Ioi]
    exact ae_of_all _ fun x hx => by
      rw [Real.norm_eq_abs, abs_of_nonneg (ht x hx).1]; exact (ht x hx).2
  have i1 := integ f1 m1 t1
  have i2 := integ f2 m2 t2
  have i3 := integ f3 m3 t3
  have i4 := integ f4 m4 t4
  have hmu := prof_mean ha hb
  have key : F.Mn n - secondOrderCoeff a b =
      (∫ x in Ioi (0:ℝ), (f1 x - f2 x)) - ∫ x in Ioi (0:ℝ), (f3 x - f4 x) := by
    rw [integral_sub i1 i2, integral_sub i3 i4, ← hmu]
    simp only [Mn, f1, f2, f3, f4]; ring
  -- pointwise bounds
  have p12 : ∀ x ∈ Ioi (0:ℝ), |f1 x - f2 x| ≤ e ∧ |f1 x - f2 x| ≤ gM F.M x := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have := F.cdf_comparison hc hb hn hm hR x
      simp only [f1, f2]; rw [abs_sub_comm]; convert this using 2; ring
    · obtain ⟨a1, b1⟩ := t1 x hx; obtain ⟨a2, b2⟩ := t2 x hx
      rw [abs_le]; constructor <;> linarith
  have p34 : ∀ x ∈ Ioi (0:ℝ), |f3 x - f4 x| ≤ e ∧ |f3 x - f4 x| ≤ gM F.M x := by
    intro x hx
    refine ⟨?_, ?_⟩
    · have := F.cdf_comparison hc hb hn hm hR (-x)
      simp only [f3, f4]; convert this using 3; ring
    · obtain ⟨a1, b1⟩ := t3 x hx; obtain ⟨a2, b2⟩ := t4 x hx
      rw [abs_le]; constructor <;> linarith
  have s12 := split_integral (h := fun x => |f1 x - f2 x|) hM hr
    ((continuous_abs.measurable.comp (m1.sub m2)).aestronglyMeasurable)
    (fun x _ => abs_nonneg _) (fun x hx => (p12 x hx).1) (fun x hx => (p12 x hx).2)
  have s34 := split_integral (h := fun x => |f3 x - f4 x|) hM hr
    ((continuous_abs.measurable.comp (m3.sub m4)).aestronglyMeasurable)
    (fun x _ => abs_nonneg _) (fun x hx => (p34 x hx).1) (fun x hx => (p34 x hx).2)
  have a12 := abs_integral_le_integral_abs (f := fun x => f1 x - f2 x) (μ := volume.restrict (Ioi 0))
  have a34 := abs_integral_le_integral_abs (f := fun x => f3 x - f4 x) (μ := volume.restrict (Ioi 0))
  rw [key]
  calc _ ≤ |∫ x in Ioi (0:ℝ), (f1 x - f2 x)| + |∫ x in Ioi (0:ℝ), (f3 x - f4 x)| := abs_sub _ _
    _ ≤ _ := by linarith

#print axioms mean_bound

end IncFamily
end CausalSpectrum.Sqrt

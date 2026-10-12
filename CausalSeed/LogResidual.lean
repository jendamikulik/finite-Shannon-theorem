/-
Stage 4: the residual lemma (`Lemma res` of the manuscript) in majorant form.

For a centered increment family of common variance `v > 0` the comparison profile is
  `u_t(x) = Φ(z) + t^{-1/2} B(z)`,  `z = (x - c ln t)/√(vt)`,
with the corrector `B` of `LogCorrector` for `α = κ₊/(6v^{3/2})`, `β = κ₋/(6v^{3/2})`
(`κ₊`, `κ₋` the largest and smallest third moments) and `c = -√v a`. We prove
`c = (κ₊ - κ₋)/(3v√(2πe))`, identify the forcing with the minimum over actions, and show
the pointwise residual bound
  `|u_{t+1}(x) - (T u_t)(x)| ≤ K t^{-2} E(z)`  for all `t ≥ 1`, `x`,
with `E(z) = (1 + z²)⁴ e^{-z²/8}`. Since `x ↦ K t^{-2} E(z)` is a `C¹` majorant with
`‖·‖₁ = O(t^{-3/2})` and `‖∂ₓ·‖₁ = O(t^{-2})`, this is the form of the manuscript's
estimate `‖R_t‖₁ + ‖R_t'‖₁ ≤ K t^{-3/2}` used by integrated amplification.
-/
import CausalSeed.LogTaylor

open MeasureTheory Set Filter Topology Real Finset

namespace CausalSpectrum.LogGauss

/-! ### Elementary inequalities -/

theorem abs_mul_le_of {a b A B : ℝ} (ha : |a| ≤ A) (hb : |b| ≤ B) : |a * b| ≤ A * B := by
  rw [abs_mul]; exact mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)

theorem abs_min_sub_min_le_add (a b c d : ℝ) : |min a b - min c d| ≤ |a - c| + |b - d| :=
  (abs_min_sub_min_le_max a b c d).trans (max_le (by linarith [abs_nonneg (b - d)])
    (by linarith [abs_nonneg (a - c)]))

theorem abs_inf'_sub_inf'_le {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {a b : ι → ℝ} {ε : ℝ}
    (h : ∀ i ∈ s, |a i - b i| ≤ ε) : |s.inf' hs a - s.inf' hs b| ≤ ε := by
  obtain ⟨i, hi, ei⟩ := exists_mem_eq_inf' hs a
  obtain ⟨j, hj, ej⟩ := exists_mem_eq_inf' hs b
  have h1 : a i ≤ a j := ei ▸ inf'_le a hj
  have h2 : b j ≤ b i := ej ▸ inf'_le b hi
  have h3 := abs_le.1 (h j hj); have h4 := abs_le.1 (h i hi)
  rw [ei, ej, abs_le]; constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

/-! ### Window bounds on segments -/

/-- Window constant. -/
noncomputable def CW (D : ℝ) : ℝ := 16 * (1 + D) ^ 8 * exp (D ^ 2 / 2)

theorem CW_nonneg {D : ℝ} (hD : 0 ≤ D) : 0 ≤ CW D := by unfold CW; positivity

theorem window_seg {D : ℝ} (hD : 0 ≤ D) {k : ℕ} (hk : k ≤ 8) {z w ξ : ℝ} (hw : |w - z| ≤ D)
    (hξ : ξ ∈ uIcc z w) : (1 + |ξ|) ^ k * phi ξ ≤ CW D * Emaj z :=
  window hD hk (lam := 1) (by norm_num) le_rfl (by norm_num)
    (by rw [one_mul]; exact (abs_sub_le_of_mem_uIcc hξ).trans hw)

theorem abs_dphi_le (z : ℝ) : |dphi z| ≤ (1 + |z|) ^ 1 * phi z := by
  rw [dphi, abs_mul, abs_neg, abs_of_pos (phi_pos z), pow_one]
  exact mul_le_mul_of_nonneg_right (by linarith) (phi_pos z).le

theorem abs_ddphi_le (z : ℝ) : |ddphi z| ≤ (1 + |z|) ^ 2 * phi z := by
  rw [ddphi, abs_mul, abs_of_pos (phi_pos z)]
  refine mul_le_mul_of_nonneg_right ?_ (phi_pos z).le
  rw [abs_le]; constructor <;> nlinarith [abs_nonneg z, sq_abs z]

theorem abs_dddphi_le (z : ℝ) : |dddphi z| ≤ 3 * ((1 + |z|) ^ 3 * phi z) := by
  rw [dddphi, abs_mul, abs_of_pos (phi_pos z), ← mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ (phi_pos z).le
  have ha := abs_nonneg z
  have : |3 * z - z ^ 3| ≤ 3 * |z| + |z| ^ 3 := by
    refine (abs_sub _ _).trans ?_; rw [abs_mul, abs_pow]; norm_num
  nlinarith [pow_le_pow_left₀ ha (show |z| ≤ 1 + |z| by linarith) 3]

theorem abs_phi_le (z : ℝ) : |phi z| ≤ (1 + |z|) ^ 0 * phi z := by
  rw [abs_of_pos (phi_pos z), pow_zero, one_mul]

/-! ### The local Lipschitz bound for `B''` (the weak `B'''`) -/

section Lip
variable (α β : ℝ)

theorem K_nonneg' {F : ℝ → ℝ} {K : ℝ} {k : ℕ}
    (h : ∀ z, |F z| ≤ K * ((1 + |z|) ^ k * phi z)) : 0 ≤ K := by
  have := (abs_nonneg _).trans (h 0); have hp := phi_pos 0
  exact nonneg_of_mul_nonneg_left this (by positivity)

/-- A function whose derivative is bounded by `K (1 + |ξ|)^k φ(ξ)`, `k ≤ 8`, has increments
`≤ K C_D E(z) |w - z|` for `|w - z| ≤ D`. -/
theorem lip_of_deriv {D : ℝ} (hD : 0 ≤ D) {F F' : ℝ → ℝ} (hF : ∀ ξ, HasDerivAt F (F' ξ) ξ)
    {K : ℝ} (hK : 0 ≤ K) {k : ℕ} (hk : k ≤ 8) (hb : ∀ ξ, |F' ξ| ≤ K * ((1 + |ξ|) ^ k * phi ξ))
    : ∀ z w : ℝ, |w - z| ≤ D → |F w - F z| ≤ K * CW D * Emaj z * |w - z| := by
  intro z w hw
  refine mvt_abs (fun ξ _ => hF ξ) fun ξ hξ => ?_
  rw [mul_assoc K]
  exact (hb ξ).trans (mul_le_mul_of_nonneg_left (window_seg hD hk hw hξ) hK)

/-- **Local Lipschitz bound for `B''`.** For every `D ≥ 0` there is `L` with
`|B''(w) - B''(z)| ≤ L E(z) |w - z|` whenever `|w - z| ≤ D`. -/
theorem cddB_lip {D : ℝ} (hD : 0 ≤ D) :
    ∃ L, 0 ≤ L ∧ ∀ z w, |w - z| ≤ D → |cddB α β w - cddB α β z| ≤ L * Emaj z * |w - z| := by
  obtain ⟨K1, h1⟩ := abs_cdB_le α β
  obtain ⟨K2, h2⟩ := abs_cddB_le α β
  have hK1 := K_nonneg' h1; have hK2 := K_nonneg' h2
  have hW := CW_nonneg hD
  -- the pieces
  have hphi := lip_of_deriv hD hasDerivAt_phi zero_le_one (k := 1) (by norm_num)
    (fun ξ => by rw [one_mul]; exact abs_dphi_le ξ)
  have hdd := lip_of_deriv hD hasDerivAt_ddphi (by norm_num : (0:ℝ) ≤ 3) (k := 3) (by norm_num)
    abs_dddphi_le
  have hB := lip_of_deriv hD (hasDerivAt_cB α β) hK1 (k := 4) (by norm_num) h1
  have hzB : ∀ ξ, |cdB α β ξ + ξ * cddB α β ξ| ≤ (K1 + K2) * ((1 + |ξ|) ^ 6 * phi ξ) := by
    intro ξ
    have a1 := (h1 ξ).trans (mul_le_mul_of_nonneg_left (wphi_mono (show 4 ≤ 6 by norm_num)) hK1)
    have a2 : |ξ * cddB α β ξ| ≤ (1 + |ξ|) * (K2 * ((1 + |ξ|) ^ 5 * phi ξ)) :=
      abs_mul_le_of (by linarith [abs_nonneg ξ]) (h2 ξ)
    have e : (1 + |ξ|) * (K2 * ((1 + |ξ|) ^ 5 * phi ξ)) = K2 * ((1 + |ξ|) ^ 6 * phi ξ) := by ring
    rw [e] at a2
    calc _ ≤ |cdB α β ξ| + |ξ * cddB α β ξ| := abs_add_le _ _
      _ ≤ _ := by linarith
  have hzd : ∀ ξ, HasDerivAt (fun ξ => ξ * cdB α β ξ) (cdB α β ξ + ξ * cddB α β ξ) ξ := by
    intro ξ; have := (hasDerivAt_id ξ).mul (hasDerivAt_cdB α β ξ)
    exact this.congr_deriv (by simp)
  have hzB' := lip_of_deriv hD hzd (by linarith) (k := 6) (by norm_num) hzB
  refine ⟨2 * |ca α β| * CW D + 2 * (|α| + |β|) * (3 * CW D) + K1 * CW D + (K1 + K2) * CW D,
    by positivity, fun z w hw => ?_⟩
  have hf : |cf α β w - cf α β z| ≤ (|α| + |β|) * (3 * CW D * Emaj z * |w - z|) := by
    unfold cf
    refine (abs_min_sub_min_le_add _ _ _ _).trans ?_
    have := hdd z w hw
    rw [show -α * ddphi w - -α * ddphi z = -α * (ddphi w - ddphi z) by ring,
      show -β * ddphi w - -β * ddphi z = -β * (ddphi w - ddphi z) by ring, abs_mul, abs_mul,
      abs_neg, abs_neg]
    nlinarith [abs_nonneg α, abs_nonneg β]
  have e : cddB α β w - cddB α β z = 2 * ca α β * (phi w - phi z) - 2 * (cf α β w - cf α β z)
      - (cB α β w - cB α β z) - (w * cdB α β w - z * cdB α β z) := by
    simp only [cddB, cg]; ring
  rw [e]
  have hp := hphi z w hw; have hb := hB z w hw; have hz := hzB' z w hw
  have hE := Emaj_nonneg z; have ha := abs_nonneg (w - z)
  have t1 : |2 * ca α β * (phi w - phi z)| ≤ 2 * |ca α β| * (1 * CW D * Emaj z * |w - z|) := by
    rw [abs_mul, abs_mul, abs_two]; gcongr
  have t2 : |2 * (cf α β w - cf α β z)| ≤ 2 * ((|α| + |β|) * (3 * CW D * Emaj z * |w - z|)) := by
    rw [abs_mul, abs_two]; gcongr
  calc _ ≤ |2 * ca α β * (phi w - phi z)| + |2 * (cf α β w - cf α β z)|
          + |cB α β w - cB α β z| + |w * cdB α β w - z * cdB α β z| := by
        refine (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans
          (add_le_add ((abs_sub _ _)) le_rfl)) le_rfl)
    _ ≤ _ := by nlinarith

end Lip
/-! ### Taylor expansions with window-weighted remainders -/

theorem ladder_all {r r' : ℝ → ℝ} {x y C : ℝ} (k : ℕ) (h0 : r x = 0)
    (hd : ∀ w ∈ uIcc x y, HasDerivAt r (r' w) w)
    (hb : ∀ w ∈ uIcc x y, |r' w| ≤ C * |w - x| ^ k) (hC : 0 ≤ C) :
    ∀ w ∈ uIcc x y, |r w| ≤ C * |w - x| ^ (k + 1) := fun _ hw =>
  ladder k h0 (fun u hu => hd u (uIcc_subset_uIcc_left hw hu))
    (fun u hu => hb u (uIcc_subset_uIcc_left hw hu)) hC

/-- **Fourth-order Taylor bound for `Φ`.** -/
theorem taylor_Phi {D : ℝ} (hD : 0 ≤ D) {z y : ℝ} (hy : |y - z| ≤ D) :
    |Phi y - (Phi z + phi z * (y - z) + dphi z * (y - z) ^ 2 / 2 + ddphi z * (y - z) ^ 3 / 6)|
      ≤ 3 * CW D * Emaj z * |y - z| ^ 4 := by
  have hC : 0 ≤ 3 * CW D * Emaj z := by have := CW_nonneg hD; have := Emaj_nonneg z; positivity
  -- level 3
  have l3 : ∀ w ∈ uIcc z y, |ddphi w - ddphi z| ≤ 3 * CW D * Emaj z * |w - z| ^ (0 + 1) := by
    refine ladder_all (r := fun w => ddphi w - ddphi z) 0 (by simp)
      (fun w _ => (hasDerivAt_ddphi w).sub_const _) (fun w hw => ?_) hC
    rw [pow_zero, mul_one, mul_assoc]
    exact (abs_dddphi_le w).trans (mul_le_mul_of_nonneg_left (window_seg hD (by norm_num) hy hw)
      (by norm_num))
  have l2 := ladder_all (r := fun w => dphi w - dphi z - ddphi z * (w - z))
    (r' := fun w => ddphi w - ddphi z) 1 (by simp)
    (fun w _ => by
      have := ((hasDerivAt_dphi w).sub_const (dphi z)).sub
        (((hasDerivAt_id w).sub_const z).const_mul (ddphi z))
      exact this.congr_deriv (by simp)) l3 hC
  have l1 := ladder_all (r := fun w => phi w - phi z - dphi z * (w - z) - ddphi z * (w - z) ^ 2 / 2)
    (r' := fun w => dphi w - dphi z - ddphi z * (w - z)) 2 (by simp)
    (fun w _ => by
      have h1 := ((hasDerivAt_phi w).sub_const (phi z)).sub
        (((hasDerivAt_id w).sub_const z).const_mul (dphi z))
      have h2 := ((((hasDerivAt_id w).sub_const z).pow 2).const_mul (ddphi z)).div_const 2
      exact (h1.sub h2).congr_deriv (by simp; ring)) l2 hC
  have l0 := ladder_all (r := fun w => Phi w - Phi z - phi z * (w - z) - dphi z * (w - z) ^ 2 / 2
      - ddphi z * (w - z) ^ 3 / 6)
    (r' := fun w => phi w - phi z - dphi z * (w - z) - ddphi z * (w - z) ^ 2 / 2) 3 (by simp)
    (fun w _ => by
      have h1 := ((hasDerivAt_Phi w).sub_const (Phi z)).sub
        (((hasDerivAt_id w).sub_const z).const_mul (phi z))
      have h2 := ((((hasDerivAt_id w).sub_const z).pow 2).const_mul (dphi z)).div_const 2
      have h3 := ((((hasDerivAt_id w).sub_const z).pow 3).const_mul (ddphi z)).div_const 6
      exact ((h1.sub h2).sub h3).congr_deriv (by simp; ring)) l1 hC y right_mem_uIcc
  convert l0 using 2; ring

/-- **Third-order Taylor bound for `B`**, using the Lipschitz bound for `B''`. -/
theorem taylor_cB (α β : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ L, 0 ≤ L ∧ ∀ z y, |y - z| ≤ D →
      |cB α β y - (cB α β z + cdB α β z * (y - z) + cddB α β z * (y - z) ^ 2 / 2)|
        ≤ L * Emaj z * |y - z| ^ 3 := by
  obtain ⟨L, hL, hlip⟩ := cddB_lip α β hD
  refine ⟨L, hL, fun z y hy => ?_⟩
  have hC : 0 ≤ L * Emaj z := mul_nonneg hL (Emaj_nonneg z)
  have l2 := ladder_all (x := z) (y := y) (r := fun w => cdB α β w - cdB α β z - cddB α β z * (w - z))
    (r' := fun w => cddB α β w - cddB α β z) 1 (by simp)
    (fun w _ => by
      have := ((hasDerivAt_cdB α β w).sub_const (cdB α β z)).sub
        (((hasDerivAt_id w).sub_const z).const_mul (cddB α β z))
      exact this.congr_deriv (by simp))
    (fun w hw => by
      rw [pow_one]; exact hlip z w ((abs_sub_le_of_mem_uIcc hw).trans hy)) hC
  have l0 := ladder_all (r := fun w => cB α β w - cB α β z - cdB α β z * (w - z)
      - cddB α β z * (w - z) ^ 2 / 2)
    (r' := fun w => cdB α β w - cdB α β z - cddB α β z * (w - z)) 2 (by simp)
    (fun w _ => by
      have h1 := ((hasDerivAt_cB α β w).sub_const (cB α β z)).sub
        (((hasDerivAt_id w).sub_const z).const_mul (cdB α β z))
      have h2 := ((((hasDerivAt_id w).sub_const z).pow 2).const_mul (cddB α β z)).div_const 2
      exact (h1.sub h2).congr_deriv (by simp; ring)) l2 hC y right_mem_uIcc
  convert l0 using 2; ring

/-! ### The increment family: constants and the two links -/

section Family
open Sqrt
variable (F : Sqrt.IncFamily) (v : ℝ)

/-- `κ₊ = max_j m3_j`. -/
noncomputable def kmax : ℝ := univ.sup' F.univ_nonempty F.m3
/-- `κ₋ = min_j m3_j`. -/
noncomputable def kmin : ℝ := univ.inf' F.univ_nonempty F.m3
/-- `α = κ₊/(6 v^{3/2})`. -/
noncomputable def calpha : ℝ := kmax F / (6 * (v * √v))
/-- `β = κ₋/(6 v^{3/2})`. -/
noncomputable def cbeta : ℝ := kmin F / (6 * (v * √v))
/-- The drift `c = -√v a`. -/
noncomputable def cdrift : ℝ := -√v * ca (calpha F v) (cbeta F v)

theorem kmin_le_kmax : kmin F ≤ kmax F :=
  (inf'_le F.m3 (mem_univ (⟨0, F.hA⟩ : Fin F.nA))).trans (le_sup' F.m3 (mem_univ _))

theorem cbeta_le_calpha (hv : 0 < v) : cbeta F v ≤ calpha F v := by
  unfold cbeta calpha
  exact div_le_div_of_nonneg_right (kmin_le_kmax F) (by positivity)

/-- **Link `f = min over actions`.** `min_j [-κ_j/(6v^{3/2}) φ''(z)] = f(z)`. -/
theorem inf'_eq_cf (hv : 0 < v) (z : ℝ) :
    univ.inf' F.univ_nonempty (fun j => -(F.m3 j / (6 * (v * √v))) * ddphi z) =
      cf (calpha F v) (cbeta F v) z := by
  have hK : 0 < 6 * (v * √v) := by have := sqrt_pos.2 hv; positivity
  obtain ⟨i, -, hi⟩ := exists_mem_eq_sup' F.univ_nonempty F.m3
  obtain ⟨j, -, hj⟩ := exists_mem_eq_inf' F.univ_nonempty F.m3
  unfold cf calpha cbeta kmax kmin
  apply le_antisymm
  · rw [hi, hj]; exact le_min (inf'_le _ (mem_univ i)) (inf'_le _ (mem_univ j))
  · refine le_inf' _ _ fun k _ => ?_
    have h1 : F.m3 k ≤ univ.sup' F.univ_nonempty F.m3 := le_sup' _ (mem_univ k)
    have h2 : univ.inf' F.univ_nonempty F.m3 ≤ F.m3 k := inf'_le _ (mem_univ k)
    rcases le_total 0 (ddphi z) with hd | hd
    · refine (min_le_left _ _).trans ?_
      have := div_le_div_of_nonneg_right h1 hK.le
      nlinarith
    · refine (min_le_right _ _).trans ?_
      have := div_le_div_of_nonneg_right h2 hK.le
      nlinarith

/-- **Link `a = -c/√v`.** -/
theorem ca_eq_neg_cdrift (hv : 0 < v) : ca (calpha F v) (cbeta F v) = -cdrift F v / √v := by
  have := sqrt_pos.2 hv
  unfold cdrift; field_simp

/-- **The coefficient.** `c = (κ₊ - κ₋)/(3 v √(2πe))`. -/
theorem cdrift_eq (hv : 0 < v) :
    cdrift F v = (kmax F - kmin F) / (3 * v * √(2 * π * exp 1)) := by
  have hs := sqrt_pos.2 hv
  have hpi : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  have he : 0 < √(exp 1) := sqrt_pos.2 (exp_pos 1)
  unfold cdrift
  rw [ca_eq _ _ (cbeta_le_calpha F v hv), sqrt_mul (by positivity : (0:ℝ) ≤ 2 * π)]
  have e1 : exp (-(1 ^ 2 / 2 : ℝ)) = (√(exp 1))⁻¹ := by
    rw [← exp_half, ← exp_neg]; norm_num
  simp only [phi, e1, calpha, cbeta]
  field_simp
  ring

/-! ### The comparison profile -/

/-- `z_t(x) = (x - c ln t)/√(vt)`. -/
noncomputable def zt (t x : ℝ) : ℝ := (x - cdrift F v * log t) / √(v * t)

/-- `u_t(x) = Φ(z) + t^{-1/2} B(z)`. -/
noncomputable def prof (t x : ℝ) : ℝ :=
  Phi (zt F v t x) + cB (calpha F v) (cbeta F v) (zt F v t x) / √t

/-- A bound for all increments. -/
noncomputable def Mx : ℝ := ∑ j, ∑ y, |F.X j y|

theorem abs_X_le (j : Fin F.nA) (y : Fin (F.nY j)) : |F.X j y| ≤ Mx F :=
  (single_le_sum (f := fun y => |F.X j y|) (fun _ _ => abs_nonneg _) (mem_univ y)).trans
    (single_le_sum (f := fun j => ∑ y, |F.X j y|) (fun _ _ => sum_nonneg fun _ _ => abs_nonneg _)
      (mem_univ j))

theorem Mx_nonneg : 0 ≤ Mx F := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _

theorem sum_cubic (j : Fin F.nA) (A B C D : ℝ) :
    ∑ y, F.P j y * (A + B * F.X j y + C * F.X j y ^ 2 + D * F.X j y ^ 3) =
      A * ∑ y, F.P j y + B * ∑ y, F.P j y * F.X j y + C * ∑ y, F.P j y * F.X j y ^ 2
        + D * ∑ y, F.P j y * F.X j y ^ 3 := by
  simp only [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun _ _ => by ring

/-- **Spatial expansion for one action.** For `t ≥ 1`,
`E_j u_t(x) = u_t + (φ'(z) + t^{-1/2}B''(z))/(2t) - t^{-3/2} κ_j/(6v^{3/2}) φ''(z) + O(t^{-2} E(z))`. -/
theorem spatial (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ K, 0 ≤ K ∧ ∀ j t x, 1 ≤ t →
      |F.expect j (prof F v t) x - (prof F v t x
        + (dphi (zt F v t x) + cddB (calpha F v) (cbeta F v) (zt F v t x) / √t) / (2 * t)
        + 1 / (t * √t) * (-(F.m3 j / (6 * (v * √v))) * ddphi (zt F v t x)))|
        ≤ K / t ^ 2 * Emaj (zt F v t x) := by
  set α := calpha F v; set β := cbeta F v
  set M := Mx F
  have hM := Mx_nonneg F
  have hsv := sqrt_pos.2 hv
  set D := M / √v
  have hD : 0 ≤ D := by positivity
  obtain ⟨L, hL, hT⟩ := taylor_cB α β hD
  refine ⟨3 * CW D * M ^ 4 / v ^ 2 + L * M ^ 3 / (v * √v), by
    have := CW_nonneg hD; positivity, fun j t x ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst := sqrt_pos.2 ht0
  set s := √(v * t) with hs_def
  have hs : 0 < s := sqrt_pos.2 (by positivity)
  have hss : s = √v * √t := sqrt_mul hv.le t
  have hs2 : s ^ 2 = v * t := sq_sqrt (by positivity)
  have hst1 : 1 ≤ √t := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt ht
  set z := zt F v t x
  have hzX : ∀ y, zt F v t (x - F.X j y) = z - F.X j y / s := fun y => by
    simp only [zt, z, s]; ring
  -- per-atom remainder
  set poly : ℝ → ℝ := fun h => Phi z + cB α β z / √t + (-(phi z + cdB α β z / √t)) * h
    + ((dphi z + cddB α β z / √t) / 2) * h ^ 2 + (-(ddphi z / 6)) * h ^ 3
  have hrem : ∀ y, |prof F v t (x - F.X j y) - poly (F.X j y / s)|
      ≤ (3 * CW D * M ^ 4 / v ^ 2 + L * M ^ 3 / (v * √v)) / t ^ 2 * Emaj z := by
    intro y
    set h := F.X j y / s
    have hh : |h| ≤ M / s := by
      simp only [h, abs_div, abs_of_pos hs]; gcongr; exact abs_X_le F j y
    have hMs : M / s ≤ D := by
      simp only [D]; gcongr; rw [hss]; exact le_mul_of_one_le_right hsv.le hst1
    have hyz : |(z - h) - z| ≤ D := by rw [sub_sub_cancel_left, abs_neg]; exact hh.trans hMs
    have t1 := taylor_Phi hD hyz
    have t2 := hT z (z - h) hyz
    rw [sub_sub_cancel_left, abs_neg] at t1 t2
    have e : prof F v t (x - F.X j y) - poly h =
        (Phi (z - h) - (Phi z + phi z * -h + dphi z * (-h) ^ 2 / 2 + ddphi z * (-h) ^ 3 / 6))
        + (cB α β (z - h) - (cB α β z + cdB α β z * -h + cddB α β z * (-h) ^ 2 / 2)) / √t := by
      have hp : prof F v t (x - F.X j y) = Phi (z - h) + cB α β (z - h) / √t := by
        simp only [prof]; rw [hzX y]
      rw [hp]; simp only [poly]; ring
    rw [e]
    have hE := Emaj_nonneg z
    have hW := CW_nonneg hD
    have h4 : |h| ^ 4 ≤ M ^ 4 / (v ^ 2 * t ^ 2) := by
      calc |h| ^ 4 ≤ (M / s) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hh 4
        _ = M ^ 4 / (v ^ 2 * t ^ 2) := by
          rw [div_pow, show s ^ 4 = (s ^ 2) ^ 2 by ring, hs2]; ring
    have h3 : |h| ^ 3 / √t ≤ M ^ 3 / (v * √v) / t ^ 2 := by
      have : |h| ^ 3 ≤ (M / s) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hh 3
      calc |h| ^ 3 / √t ≤ (M / s) ^ 3 / √t := by gcongr
        _ = M ^ 3 / (v * √v) / t ^ 2 := by
          rw [div_pow, hss]
          have e1 : √v ^ 3 = v * √v := by rw [pow_succ, sq_sqrt hv.le]
          have e2 : √t ^ 3 * √t = t ^ 2 := by
            rw [show √t ^ 3 * √t = (√t ^ 2) ^ 2 by ring, sq_sqrt ht0.le]
          rw [mul_pow, e1]; field_simp; rw [← e2]; ring
    calc _ ≤ |Phi (z - h) - (Phi z + phi z * -h + dphi z * (-h) ^ 2 / 2 + ddphi z * (-h) ^ 3 / 6)|
          + |(cB α β (z - h) - (cB α β z + cdB α β z * -h + cddB α β z * (-h) ^ 2 / 2))| / √t := by
          refine (abs_add_le _ _).trans ?_; rw [abs_div, abs_of_pos hst]
      _ ≤ 3 * CW D * Emaj z * |h| ^ 4 + L * Emaj z * |h| ^ 3 / √t := by
          gcongr
      _ ≤ 3 * CW D * Emaj z * (M ^ 4 / (v ^ 2 * t ^ 2)) + L * Emaj z * (M ^ 3 / (v * √v) / t ^ 2) := by
          rw [mul_div_assoc (L * Emaj z)]
          gcongr
      _ = _ := by field_simp
  -- sum the polynomial parts
  have hpoly : ∑ y, F.P j y * poly (F.X j y / s) = prof F v t x
      + (dphi z + cddB α β z / √t) / (2 * t)
      + 1 / (t * √t) * (-(F.m3 j / (6 * (v * √v))) * ddphi z) := by
    have e : ∀ y, poly (F.X j y / s) = (Phi z + cB α β z / √t) + (-(phi z + cdB α β z / √t) / s)
        * F.X j y + ((dphi z + cddB α β z / √t) / 2 / s ^ 2) * F.X j y ^ 2
        + (-(ddphi z / 6) / s ^ 3) * F.X j y ^ 3 := fun y => by simp only [poly]; ring
    simp only [e]
    rw [sum_cubic, F.Psum, hc j]
    have h2 : ∑ y, F.P j y * F.X j y ^ 2 = v := hσ j
    have h3 : ∑ y, F.P j y * F.X j y ^ 3 = F.m3 j := rfl
    rw [h2, h3]
    have hs3 : s ^ 3 = v * √v * (t * √t) := by
      rw [hss, show (√v * √t) ^ 3 = √v ^ 2 * √v * (√t ^ 2 * √t) by ring, sq_sqrt hv.le,
        sq_sqrt ht0.le]
    rw [hs2, hs3]; simp only [prof, z]; field_simp; ring
  have hexp : F.expect j (prof F v t) x =
      ∑ y, F.P j y * poly (F.X j y / s) + ∑ y, F.P j y * (prof F v t (x - F.X j y) - poly (F.X j y / s)) := by
    rw [← sum_add_distrib]; unfold Sqrt.IncFamily.expect; exact sum_congr rfl fun _ _ => by ring
  rw [hexp, ← hpoly, add_sub_cancel_left]
  calc _ ≤ ∑ y, |F.P j y * (prof F v t (x - F.X j y) - poly (F.X j y / s))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, F.P j y * ((3 * CW D * M ^ 4 / v ^ 2 + L * M ^ 3 / (v * √v)) / t ^ 2 * Emaj z) :=
        sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_pos (F.Ppos j y)]
          exact mul_le_mul_of_nonneg_left (hrem y) (F.Ppos j y).le
    _ = _ := by rw [← sum_mul, F.Psum, one_mul]

end Family

/-! ### Time expansion at a fixed point -/

section Time
variable (F : Sqrt.IncFamily) (v x : ℝ)

/-- `w(τ) = (vτ)^{-1/2}`. -/
noncomputable def wv (τ : ℝ) : ℝ := (√(v * τ))⁻¹
/-- `q(τ) = τ^{-1/2}`. -/
noncomputable def qt (τ : ℝ) : ℝ := (√τ)⁻¹

theorem hasDerivAt_wv (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (wv v) (-(wv v τ) / (2 * τ)) τ := by
  have hS : 0 < √(v * τ) := sqrt_pos.2 (by positivity)
  have h := (((hasDerivAt_id τ).const_mul v).sqrt (by positivity)).inv hS.ne'
  refine h.congr_deriv ?_
  have h2 : √(v * τ) ^ 2 = v * τ := sq_sqrt (by positivity)
  simp only [wv, id]; field_simp; linear_combination h2

theorem hasDerivAt_qt {τ : ℝ} (hτ : 0 < τ) : HasDerivAt qt (-(qt τ) / (2 * τ)) τ := by
  have hS : 0 < √τ := sqrt_pos.2 hτ
  have h := ((hasDerivAt_id τ).sqrt hτ.ne').inv hS.ne'
  refine h.congr_deriv ?_
  have h2 : √τ ^ 2 = τ := sq_sqrt hτ.le
  simp only [qt, id]; field_simp; linear_combination h2

/-- `ζ(τ) = z_τ(x)`. -/
noncomputable def zeta (τ : ℝ) : ℝ := zt F v τ x
/-- `ζ'(τ)`. -/
noncomputable def dzeta (τ : ℝ) : ℝ := -(cdrift F v / τ) * wv v τ - zeta F v x τ / (2 * τ)
/-- `ζ''(τ)`. -/
noncomputable def ddzeta (τ : ℝ) : ℝ :=
  3 / 2 * cdrift F v * wv v τ / τ ^ 2 - dzeta F v x τ / (2 * τ) + zeta F v x τ / (2 * τ ^ 2)

theorem zeta_eq (τ : ℝ) : zeta F v x τ = (x - cdrift F v * log τ) * wv v τ := by
  simp [zeta, zt, wv, div_eq_mul_inv]

theorem hasDerivAt_zeta (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (zeta F v x) (dzeta F v x τ) τ := by
  have hN := ((hasDerivAt_log hτ.ne').const_mul (cdrift F v)).const_sub x
  have h := hN.mul (hasDerivAt_wv v hv hτ)
  rw [show zeta F v x = fun τ => (x - cdrift F v * log τ) * wv v τ from funext (zeta_eq F v x)]
  refine h.congr_deriv ?_
  simp only [dzeta, zeta_eq]; field_simp; ring

theorem hasDerivAt_dzeta (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (dzeta F v x) (ddzeta F v x τ) τ := by
  have h1 := ((hasDerivAt_inv hτ.ne').const_mul (-(cdrift F v))).mul (hasDerivAt_wv v hv hτ)
  have h2 := (hasDerivAt_zeta F v x hv hτ).div ((hasDerivAt_id τ).const_mul 2)
    (by positivity)
  have h := h1.sub h2
  have e : dzeta F v x = fun τ => -cdrift F v * τ⁻¹ * wv v τ - zeta F v x τ / (2 * id τ) :=
    funext fun τ => by simp only [dzeta, id]; ring
  rw [e]; refine h.congr_deriv ?_
  simp only [ddzeta, dzeta, id]; field_simp; ring

/-- `F(τ) = u_τ(x)`. -/
noncomputable def Fx (τ : ℝ) : ℝ := prof F v τ x

/-- `F'(τ)`. -/
noncomputable def dFx (τ : ℝ) : ℝ :=
  let ζ := zeta F v x τ; let d := dzeta F v x τ; let q := qt τ
  phi ζ * d + (cdB (calpha F v) (cbeta F v) ζ * d * q + cB (calpha F v) (cbeta F v) ζ * (-q / (2 * τ)))

/-- `F''(τ)`. -/
noncomputable def ddFx (τ : ℝ) : ℝ :=
  let ζ := zeta F v x τ; let d := dzeta F v x τ; let dd := ddzeta F v x τ; let q := qt τ
  let α := calpha F v; let β := cbeta F v
  (dphi ζ * d * d + phi ζ * dd)
    + ((cddB α β ζ * d * d * q + cdB α β ζ * dd * q + cdB α β ζ * d * (-q / (2 * τ)))
      + (cdB α β ζ * d * (-q / (2 * τ)) + cB α β ζ * (q / (4 * τ ^ 2) + q / (2 * τ ^ 2))))

theorem Fx_eq (τ : ℝ) : Fx F v x τ =
    Phi (zeta F v x τ) + cB (calpha F v) (cbeta F v) (zeta F v x τ) * qt τ := by
  simp [Fx, prof, zeta, qt, div_eq_mul_inv]

theorem hasDerivAt_Fx (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (Fx F v x) (dFx F v x τ) τ := by
  have hz := hasDerivAt_zeta F v x hv hτ
  have h := ((hasDerivAt_Phi _).comp τ hz).add
    (((hasDerivAt_cB (calpha F v) (cbeta F v) _).comp τ hz).mul (hasDerivAt_qt hτ))
  rw [show Fx F v x = fun τ => Phi (zeta F v x τ) + cB (calpha F v) (cbeta F v) (zeta F v x τ) * qt τ
    from funext (Fx_eq F v x)]
  refine h.congr_deriv ?_
  simp only [dFx, Function.comp_apply]

theorem hasDerivAt_dFx (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (dFx F v x) (ddFx F v x τ) τ := by
  have hz := hasDerivAt_zeta F v x hv hτ
  have hd := hasDerivAt_dzeta F v x hv hτ
  have hq := hasDerivAt_qt hτ
  have hq2 : HasDerivAt (fun τ => -qt τ / (2 * τ)) (qt τ / (4 * τ ^ 2) + qt τ / (2 * τ ^ 2)) τ := by
    have := hq.neg.div ((hasDerivAt_id τ).const_mul 2) (by simp; exact hτ.ne')
    refine this.congr_deriv ?_; simp only [id, Pi.neg_apply]; field_simp; ring
  have h1 := (((hasDerivAt_phi _).comp τ hz).mul hd)
  have h2 := ((((hasDerivAt_cdB (calpha F v) (cbeta F v) _).comp τ hz).mul hd).mul hq)
  have h3 := (((hasDerivAt_cB (calpha F v) (cbeta F v) _).comp τ hz).mul hq2)
  have h := h1.add (h2.add h3)
  have e : dFx F v x = fun τ => (phi ∘ zeta F v x) τ * dzeta F v x τ
      + ((cdB (calpha F v) (cbeta F v) ∘ zeta F v x) τ * dzeta F v x τ * qt τ
        + (cB (calpha F v) (cbeta F v) ∘ zeta F v x) τ * (-qt τ / (2 * τ))) := by
    funext τ; simp only [dFx, Function.comp]
  rw [e]; refine h.congr_deriv ?_
  simp only [ddFx, Function.comp_apply, Pi.mul_apply]; ring

end Time

section TimeBounds
variable (F : Sqrt.IncFamily) (v : ℝ)

theorem qt_le_one {τ : ℝ} (hτ : 1 ≤ τ) : |qt τ| ≤ 1 := by
  have h1 : 1 ≤ √τ := by rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt hτ
  rw [qt, abs_inv, abs_of_pos (by linarith)]; exact inv_le_one_of_one_le₀ h1

theorem wv_le (hv : 0 < v) {τ : ℝ} (hτ : 1 ≤ τ) : |wv v τ| ≤ 1 / √v := by
  have hs := sqrt_pos.2 hv
  have h1 : √v ≤ √(v * τ) := sqrt_le_sqrt (by nlinarith)
  rw [wv, abs_inv, abs_of_pos (by linarith), one_div]
  exact inv_anti₀ hs h1

/-- Window for the time variable. -/
theorem zeta_window (hv : 0 < v) {t τ x : ℝ} (ht : 1 ≤ t) (hτ : τ ∈ Set.uIcc t (t + 1)) :
    ∃ lam, 0 ≤ lam ∧ lam ≤ 1 ∧ 1 / 2 ≤ lam ^ 2 ∧
      |zeta F v x τ - lam * zt F v t x| ≤ |cdrift F v| / √v := by
  rw [Set.uIcc_of_le (by linarith)] at hτ
  obtain ⟨h1, h2⟩ := hτ
  have ht0 : 0 < t := by linarith
  have hτ0 : 0 < τ := by linarith
  have hsv := sqrt_pos.2 hv
  refine ⟨√(t / τ), sqrt_nonneg _, ?_, ?_, ?_⟩
  · rw [show (1:ℝ) = √1 by simp]; exact sqrt_le_sqrt (by rw [div_le_one hτ0]; exact h1)
  · rw [sq_sqrt (by positivity), le_div_iff₀ hτ0]; linarith
  · have e : √(t / τ) * zt F v t x = (x - cdrift F v * log t) * wv v τ := by
      simp only [zt, wv]
      rw [sqrt_div ht0.le, sqrt_mul hv.le, sqrt_mul hv.le]
      have := sqrt_pos.2 ht0; have := sqrt_pos.2 hτ0
      field_simp
    rw [e, zeta_eq]
    have hl : 0 ≤ log τ - log t ∧ log τ - log t ≤ 1 := by
      rw [← log_div hτ0.ne' ht0.ne']
      constructor
      · exact log_nonneg (by rw [le_div_iff₀ ht0]; linarith)
      · have := log_le_sub_one_of_pos (show 0 < τ / t by positivity)
        have : τ / t ≤ 2 := by rw [div_le_iff₀ ht0]; linarith
        linarith
    have hw := wv_le v hv (show 1 ≤ τ by linarith)
    rw [show (x - cdrift F v * log τ) * wv v τ - (x - cdrift F v * log t) * wv v τ =
      (-cdrift F v) * ((log τ - log t) * wv v τ) by ring, abs_mul, abs_neg]
    calc |cdrift F v| * |(log τ - log t) * wv v τ| ≤ |cdrift F v| * (1 * (1 / √v)) := by
          gcongr; rw [abs_mul, abs_of_nonneg hl.1]
          exact mul_le_mul hl.2 hw (abs_nonneg _) zero_le_one
      _ = _ := by ring

/-- **Second time derivative bound.** -/
theorem ddFx_bound (hv : 0 < v) :
    ∃ K, 0 ≤ K ∧ ∀ t x τ, 1 ≤ t → τ ∈ Set.uIcc t (t + 1) →
      |ddFx F v x τ| ≤ K / t ^ 2 * Emaj (zt F v t x) := by
  set α := calpha F v; set β := cbeta F v
  obtain ⟨K0, h0⟩ := abs_cB_le α β
  obtain ⟨K1, h1⟩ := abs_cdB_le α β
  obtain ⟨K2, h2⟩ := abs_cddB_le α β
  have hK0 := K_nonneg' h0; have hK1 := K_nonneg' h1; have hK2 := K_nonneg' h2
  set KB := K0 + K1 + K2
  have hsv := sqrt_pos.2 hv
  set A := 1 + |cdrift F v| / √v
  have hA : 1 ≤ A := by simp only [A]; have := abs_nonneg (cdrift F v); have : 0 ≤ |cdrift F v| / √v := by positivity
                        linarith
  set D2 := |cdrift F v| / √v
  have hD2 : 0 ≤ D2 := by positivity
  refine ⟨(1 + (K0 + K1 + K2)) * (A ^ 2 + 5 * A + 1) * CW D2, by
    have := CW_nonneg hD2; positivity, fun t x τ ht hτ => ?_⟩
  have hτ' := hτ
  rw [Set.uIcc_of_le (by linarith)] at hτ'
  have hτ1 : 1 ≤ τ := by linarith [hτ'.1]
  have hτ0 : 0 < τ := by linarith
  have htτ : t ≤ τ := hτ'.1
  set ζ := zeta F v x τ
  set Q := 1 + |ζ|
  have hQ : 1 ≤ Q := by simp only [Q]; linarith [abs_nonneg ζ]
  set P := Q ^ 5 * phi ζ
  have hP : 0 ≤ P := by have := phi_pos ζ; positivity
  have hq := qt_le_one hτ1
  have hw := wv_le v hv hτ1
  -- bounds on ζ', ζ''
  have hd : |dzeta F v x τ| ≤ A * Q / τ := by
    simp only [dzeta]
    have e1 : |-(cdrift F v / τ) * wv v τ| ≤ D2 / τ := by
      rw [abs_mul, abs_neg, abs_div, abs_of_pos hτ0]
      calc |cdrift F v| / τ * |wv v τ| ≤ |cdrift F v| / τ * (1 / √v) := by gcongr
        _ = D2 / τ := by simp only [D2]; ring
    have e2 : |zeta F v x τ / (2 * τ)| ≤ |ζ| / τ := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * τ)]
      exact div_le_div_of_nonneg_left (abs_nonneg _) hτ0 (by linarith)
    calc _ ≤ D2 / τ + |ζ| / τ := (abs_sub _ _).trans (add_le_add e1 e2)
      _ ≤ A * Q / τ := by
          rw [← add_div]; gcongr
          have e : A * Q = 1 + |ζ| + D2 + D2 * |ζ| := by simp only [A, Q, D2]; ring
          have : 0 ≤ D2 * |ζ| := mul_nonneg hD2 (abs_nonneg _)
          linarith
  have hdd : |ddzeta F v x τ| ≤ 3 * A * Q / τ ^ 2 := by
    simp only [ddzeta]
    have e1 : |3 / 2 * cdrift F v * wv v τ / τ ^ 2| ≤ 3 / 2 * D2 / τ ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < τ ^ 2)]
      apply div_le_div_of_nonneg_right _ (by positivity)
      calc |3 / 2 * cdrift F v * wv v τ| = 3 / 2 * |cdrift F v| * |wv v τ| := by
            rw [abs_mul, abs_mul]; norm_num
        _ ≤ 3 / 2 * |cdrift F v| * (1 / √v) := by gcongr
        _ = 3 / 2 * D2 := by simp only [D2]; ring
    have e2 : |dzeta F v x τ / (2 * τ)| ≤ A * Q / τ ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * τ)]
      calc |dzeta F v x τ| / (2 * τ) ≤ A * Q / τ / τ := by
            apply div_le_div₀ (by positivity) hd (by positivity) (by linarith)
        _ = A * Q / τ ^ 2 := by ring
    have e3 : |zeta F v x τ / (2 * τ ^ 2)| ≤ Q / τ ^ 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2 * τ ^ 2)]
      apply div_le_div₀ (by positivity) (by simp only [Q]; linarith) (by positivity)
        (by linarith [sq_nonneg τ])
    calc _ ≤ 3 / 2 * D2 / τ ^ 2 + A * Q / τ ^ 2 + Q / τ ^ 2 :=
          (abs_add_le _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add e1 e2)) e3)
      _ ≤ 3 * A * Q / τ ^ 2 := by
          rw [← add_div, ← add_div]; gcongr
          have : D2 ≤ A := by simp only [A]; linarith
          have h1 : A ≤ A * Q := le_mul_of_one_le_right (by linarith) hQ
          have h2 : Q ≤ A * Q := le_mul_of_one_le_left (by linarith) hA
          have : 3 * A * Q = 3 * (A * Q) := by ring
          have e : A * Q = Q + D2 * Q := by simp only [A, D2]; ring
          have : D2 ≤ D2 * Q := le_mul_of_one_le_right hD2 hQ
          linarith
  -- bounds on B, φ
  have hB0 : |cB α β ζ| ≤ KB * P := by
    refine (h0 ζ).trans ?_
    have := wphi_mono (z := ζ) (show 3 ≤ 5 by norm_num)
    have : K0 ≤ KB := by simp only [KB]; linarith
    exact mul_le_mul this (by assumption) (by have := phi_pos ζ; positivity) (by positivity)
  have hB1 : |cdB α β ζ| ≤ KB * P := by
    refine (h1 ζ).trans ?_
    have := wphi_mono (z := ζ) (show 4 ≤ 5 by norm_num)
    have : K1 ≤ KB := by simp only [KB]; linarith
    exact mul_le_mul this (by assumption) (by have := phi_pos ζ; positivity) (by positivity)
  have hB2 : |cddB α β ζ| ≤ KB * P := by
    refine (h2 ζ).trans ?_
    have : K2 ≤ KB := by simp only [KB]; linarith
    exact mul_le_mul_of_nonneg_right this hP
  have hp0 : |phi ζ| ≤ P := (abs_phi_le ζ).trans (wphi_mono (show 0 ≤ 5 by norm_num))
  have hp1 : |dphi ζ| ≤ P := (abs_dphi_le ζ).trans (wphi_mono (show 1 ≤ 5 by norm_num))
  have hq2 : |-qt τ / (2 * τ)| ≤ 1 / τ := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * τ)]
    apply div_le_div₀ (by norm_num) hq (by positivity) (by linarith)
  have hq3 : |qt τ / (4 * τ ^ 2) + qt τ / (2 * τ ^ 2)| ≤ 1 / τ ^ 2 := by
    rw [show qt τ / (4 * τ ^ 2) + qt τ / (2 * τ ^ 2) = qt τ * (3 / 4) / τ ^ 2 by ring, abs_div,
      abs_of_pos (by positivity : (0:ℝ) < τ ^ 2), abs_mul]
    gcongr; rw [abs_of_pos (by norm_num : (0:ℝ) < 3 / 4)]; nlinarith [abs_nonneg (qt τ)]
  set a := A * Q / τ
  set b := 3 * A * Q / τ ^ 2
  have T1 := abs_mul_le_of (abs_mul_le_of hp1 hd) hd
  have T2 := abs_mul_le_of hp0 hdd
  have T3 := abs_mul_le_of (abs_mul_le_of (abs_mul_le_of hB2 hd) hd) hq
  have T4 := abs_mul_le_of (abs_mul_le_of hB1 hdd) hq
  have T5 := abs_mul_le_of (abs_mul_le_of hB1 hd) hq2
  have T6 := abs_mul_le_of hB0 hq3
  have hsum : |ddFx F v x τ| ≤ P * a * a + P * b + (KB * P * a * a * 1 + KB * P * b * 1
      + KB * P * a * (1 / τ) + (KB * P * a * (1 / τ) + KB * P * (1 / τ ^ 2))) := by
    simp only [ddFx]
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add T1 T2)) ?_)
    refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add
      ((abs_add_le _ _).trans (add_le_add T3 T4)) T5)) ((abs_add_le _ _).trans (add_le_add T5 T6)))
  have hfin : P * a * a + P * b + (KB * P * a * a * 1 + KB * P * b * 1
      + KB * P * a * (1 / τ) + (KB * P * a * (1 / τ) + KB * P * (1 / τ ^ 2)))
      ≤ (1 + KB) * (A ^ 2 + 5 * A + 1) * (Q ^ 7 * phi ζ) / τ ^ 2 := by
    have hτ2 : 0 < τ ^ 2 := by positivity
    have e : P * a * a + P * b + (KB * P * a * a * 1 + KB * P * b * 1
      + KB * P * a * (1 / τ) + (KB * P * a * (1 / τ) + KB * P * (1 / τ ^ 2)))
      = P * (A ^ 2 * Q ^ 2 + 3 * A * Q + KB * (A ^ 2 * Q ^ 2 + 3 * A * Q + 2 * A * Q + 1)) / τ ^ 2 := by
      simp only [a, b]; field_simp; ring
    rw [e, show Q ^ 7 * phi ζ = P * Q ^ 2 by simp only [P]; ring]
    apply div_le_div_of_nonneg_right _ hτ2.le
    have hKB : 0 ≤ KB := by positivity
    have hQ2 : Q ≤ Q ^ 2 := by rw [sq]; exact le_mul_of_one_le_left (by linarith) hQ
    have hQ3 : 1 ≤ Q ^ 2 := one_le_pow₀ hQ
    have hA0 : 0 ≤ A := by linarith
    have := mul_nonneg hA0 (sub_nonneg.2 hQ2)
    have := mul_nonneg (mul_nonneg hKB hA0) (sub_nonneg.2 hQ2)
    have := mul_nonneg hKB (sub_nonneg.2 hQ3)
    have hAQ : 0 ≤ A * Q ^ 2 := by positivity
    have key : (1 + KB) * (A ^ 2 + 5 * A + 1) * Q ^ 2 - (A ^ 2 * Q ^ 2 + 3 * A * Q
        + KB * (A ^ 2 * Q ^ 2 + 3 * A * Q + 2 * A * Q + 1)) = 3 * (A * (Q ^ 2 - Q))
        + 2 * (A * Q ^ 2) + Q ^ 2 + 5 * (KB * A * (Q ^ 2 - Q)) + KB * (Q ^ 2 - 1) := by ring
    have : P * (A ^ 2 * Q ^ 2 + 3 * A * Q + KB * (A ^ 2 * Q ^ 2 + 3 * A * Q + 2 * A * Q + 1))
        ≤ P * ((1 + KB) * (A ^ 2 + 5 * A + 1) * Q ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hP
      have := sq_nonneg Q
      linarith
    linarith
  -- window
  obtain ⟨lam, hl0, hl1, hl2, hlz⟩ := zeta_window F v hv (x := x) ht hτ
  have hwin := window hD2 (k := 7) (by norm_num) hl0 hl1 hl2 hlz
  have hC : 0 ≤ (1 + KB) * (A ^ 2 + 5 * A + 1) := by positivity
  calc |ddFx F v x τ| ≤ (1 + KB) * (A ^ 2 + 5 * A + 1) * (Q ^ 7 * phi ζ) / τ ^ 2 := hsum.trans hfin
    _ ≤ (1 + KB) * (A ^ 2 + 5 * A + 1) * (CW D2 * Emaj (zt F v t x)) / t ^ 2 := by
        apply div_le_div₀ (by have := CW_nonneg hD2; have := Emaj_nonneg (zt F v t x); positivity)
          (mul_le_mul_of_nonneg_left hwin hC) (by positivity) (pow_le_pow_left₀ (by linarith) htτ 2)
    _ = _ := by simp only [KB]; ring

end TimeBounds

section Assembly
variable (F : Sqrt.IncFamily) (v : ℝ)

/-- **Time Taylor bound.** -/
theorem time_taylor (hv : 0 < v) :
    ∃ K, 0 ≤ K ∧ ∀ t x, 1 ≤ t →
      |Fx F v x (t + 1) - Fx F v x t - dFx F v x t| ≤ K / t ^ 2 * Emaj (zt F v t x) := by
  obtain ⟨K, hK, hb⟩ := ddFx_bound F v hv
  refine ⟨K, hK, fun t x ht => ?_⟩
  have hC : 0 ≤ K / t ^ 2 * Emaj (zt F v t x) := by
    have := Emaj_nonneg (zt F v t x)
    positivity
  have hpos : ∀ τ ∈ Set.uIcc t (t + 1), 0 < τ := fun τ hτ => by
    rw [Set.uIcc_of_le (by linarith)] at hτ; linarith [hτ.1]
  have l1 := ladder_all (x := t) (y := t + 1) (r := fun τ => dFx F v x τ - dFx F v x t)
    (r' := ddFx F v x) 0 (by simp)
    (fun τ hτ => (hasDerivAt_dFx F v x hv (hpos τ hτ)).sub_const _)
    (fun τ hτ => by rw [pow_zero, mul_one]; exact hb t x τ ht hτ) hC
  have l0 := ladder_all (x := t) (y := t + 1)
    (r := fun τ => Fx F v x τ - Fx F v x t - dFx F v x t * (τ - t))
    (r' := fun τ => dFx F v x τ - dFx F v x t) 1 (by simp)
    (fun τ hτ => by
      have := ((hasDerivAt_Fx F v x hv (hpos τ hτ)).sub_const (Fx F v x t)).sub
        (((hasDerivAt_id τ).sub_const t).const_mul (dFx F v x t))
      exact this.congr_deriv (by simp)) l1 hC (t + 1) Set.right_mem_uIcc
  simpa using l0

/-- **The profile equation.** `∂_t u - (v/2) ∂ₓ² u = t^{-3/2} f(z) - (c/√v) t^{-2} B'(z)`,
in the form used below. -/
theorem dFx_eq (hv : 0 < v) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    dFx F v x t = (dphi (zt F v t x) + cddB (calpha F v) (cbeta F v) (zt F v t x) / √t) / (2 * t)
      + 1 / (t * √t) * cf (calpha F v) (cbeta F v) (zt F v t x)
      - cdrift F v / √v * cdB (calpha F v) (cbeta F v) (zt F v t x) / t ^ 2 := by
  have hsv := sqrt_pos.2 hv
  have hst := sqrt_pos.2 ht
  have ht2 : √t ^ 2 = t := sq_sqrt ht.le
  have hw : wv v t = (√v)⁻¹ * (√t)⁻¹ := by rw [wv, sqrt_mul hv.le, mul_inv]
  have ha := ca_eq_neg_cdrift F v hv
  simp only [dFx, dzeta, zeta, qt, hw, cddB, cg, ha, dphi]
  field_simp
  linear_combination (2 * cdrift F v * cdB (calpha F v) (cbeta F v) (zt F v t x)) * ht2

theorem inf'_affine {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (m k : ℝ) (hk : 0 ≤ k)
    (a : ι → ℝ) : s.inf' hs (fun j => m + k * a j) = m + k * s.inf' hs a := by
  obtain ⟨i, hi, ei⟩ := exists_mem_eq_inf' hs a
  apply le_antisymm
  · rw [ei]; exact inf'_le _ hi
  · exact le_inf' _ _ fun j hj => by
      have := inf'_le a hj; nlinarith

/-- **Lemma res (pointwise majorant form).** For a centered family of common variance
`v > 0` there is `K` with `|u_{t+1}(x) - (T u_t)(x)| ≤ K t^{-2} E(z_t(x))` for all `t ≥ 1`. -/
theorem residual_pointwise (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ K, 0 ≤ K ∧ ∀ t x, 1 ≤ t →
      |prof F v (t + 1) x - F.T (prof F v t) x| ≤ K / t ^ 2 * Emaj (zt F v t x) := by
  obtain ⟨KS, hKS, hS⟩ := spatial F v hc hv hσ
  obtain ⟨KT, hKT, hT⟩ := time_taylor F v hv
  obtain ⟨K1, h1⟩ := abs_cdB_le (calpha F v) (cbeta F v)
  have hK1 := K_nonneg' h1
  have hsv := sqrt_pos.2 hv
  refine ⟨KT + KS + |cdrift F v| / √v * K1 * CW 0, by
    have := CW_nonneg (le_refl (0:ℝ)); positivity, fun t x ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst := sqrt_pos.2 ht0
  set z := zt F v t x
  set main := prof F v t x + (dphi z + cddB (calpha F v) (cbeta F v) z / √t) / (2 * t)
  have hinf : univ.inf' F.univ_nonempty (fun j => main + 1 / (t * √t) *
      (-(F.m3 j / (6 * (v * √v))) * ddphi z)) = main + 1 / (t * √t) * cf (calpha F v) (cbeta F v) z := by
    rw [inf'_affine _ main _ (by positivity), inf'_eq_cf F v hv]
  have hTb : |F.T (prof F v t) x - (main + 1 / (t * √t) * cf (calpha F v) (cbeta F v) z)|
      ≤ KS / t ^ 2 * Emaj z := by
    rw [← hinf]
    exact abs_inf'_sub_inf'_le _ fun j _ => hS j t x ht
  have hmid : |cdrift F v / √v * cdB (calpha F v) (cbeta F v) z / t ^ 2|
      ≤ |cdrift F v| / √v * K1 * CW 0 / t ^ 2 * Emaj z := by
    have hw := window (le_refl (0:ℝ)) (k := 4) (by norm_num) (lam := 1) (z := z) (w := z)
      zero_le_one le_rfl (by norm_num) (by simp)
    have hcw : (1 + |z|) ^ 4 * phi z ≤ CW 0 * Emaj z := by simpa [CW] using hw
    rw [abs_div, abs_mul, abs_div, abs_of_pos hsv, abs_of_pos (by positivity : (0:ℝ) < t ^ 2)]
    have := (h1 z).trans (mul_le_mul_of_nonneg_left hcw hK1)
    have hc0 : 0 ≤ |cdrift F v| / √v := by positivity
    calc |cdrift F v| / √v * |cdB (calpha F v) (cbeta F v) z| / t ^ 2
        ≤ |cdrift F v| / √v * (K1 * (CW 0 * Emaj z)) / t ^ 2 := by gcongr
      _ = _ := by ring
  have hT' := hT t x ht
  have hF1 : prof F v (t + 1) x = Fx F v x (t + 1) := rfl
  have hF0 : prof F v t x = Fx F v x t := rfl
  have e : prof F v (t + 1) x - F.T (prof F v t) x =
      (Fx F v x (t + 1) - Fx F v x t - dFx F v x t)
      - cdrift F v / √v * cdB (calpha F v) (cbeta F v) z / t ^ 2
      - (F.T (prof F v t) x - (main + 1 / (t * √t) * cf (calpha F v) (cbeta F v) z)) := by
    rw [dFx_eq F v hv x ht0, hF1]; simp only [main, hF0]; ring
  rw [e]
  calc _ ≤ |Fx F v x (t + 1) - Fx F v x t - dFx F v x t|
        + |cdrift F v / √v * cdB (calpha F v) (cbeta F v) z / t ^ 2|
        + |F.T (prof F v t) x - (main + 1 / (t * √t) * cf (calpha F v) (cbeta F v) z)| :=
        (abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ KT / t ^ 2 * Emaj z + |cdrift F v| / √v * K1 * CW 0 / t ^ 2 * Emaj z
        + KS / t ^ 2 * Emaj z := add_le_add (add_le_add hT' hmid) hTb
    _ = _ := by ring

/-- **Lemma res (majorant form, with norms).** There are `K, K₁, K₂ ≥ 0` such that for every
`t ≥ 1` the residual `R_t = u_{t+1} - T u_t` is dominated by the `C¹` majorant
`S_t(x) = K t^{-2} E(z_t(x))`, whose norms are `‖S_t‖₁ = K₁ t^{-3/2}` and
`‖S_t'‖₁ = K₂ t^{-2}`. -/
theorem residual_majorant (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ K K₁ K₂ : ℝ, 0 ≤ K ∧ 0 ≤ K₁ ∧ 0 ≤ K₂ ∧ ∀ t, 1 ≤ t →
      Sqrt.IncFamily.Majorant (fun x => K / t ^ 2 * Emaj ((x - cdrift F v * log t) / √(v * t)))
        (fun x => K / t ^ 2 * (dEmaj ((x - cdrift F v * log t) / √(v * t)) / √(v * t))) ∧
      (∀ x, |prof F v (t + 1) x - F.T (prof F v t) x| ≤
        K / t ^ 2 * Emaj ((x - cdrift F v * log t) / √(v * t))) ∧
      (∫⁻ x, ‖K / t ^ 2 * Emaj ((x - cdrift F v * log t) / √(v * t))‖ₑ) =
        ENNReal.ofReal (K₁ / (t * √t)) ∧
      (∫⁻ x, ‖K / t ^ 2 * (dEmaj ((x - cdrift F v * log t) / √(v * t)) / √(v * t))‖ₑ) =
        ENNReal.ofReal (K₂ / t ^ 2) := by
  obtain ⟨K, hK, hR⟩ := residual_pointwise F v hc hv hσ
  have hE : 0 ≤ ∫ z, Emaj z := integral_nonneg Emaj_nonneg
  have hE' : 0 ≤ ∫ z, |dEmaj z| := integral_nonneg fun _ => abs_nonneg _
  refine ⟨K, K * √v * ∫ z, Emaj z, K * ∫ z, |dEmaj z|, hK, by positivity, by positivity,
    fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hs : 0 < √(v * t) := sqrt_pos.2 (by positivity)
  have hKt : 0 ≤ K / t ^ 2 := by positivity
  obtain ⟨n1, n2⟩ := lintegral_majorant_scaled hKt (cdrift F v * log t) hs
  refine ⟨majorant_scaled hKt _ hs, fun x => hR t x ht, ?_, ?_⟩
  · rw [n1]; congr 1
    rw [sqrt_mul hv.le]
    have h2 : √t ^ 2 = t := sq_sqrt ht0.le
    have := sqrt_pos.2 ht0
    field_simp
    rw [h2]
  · rw [n2]; congr 1; ring

end Assembly

end CausalSpectrum.LogGauss

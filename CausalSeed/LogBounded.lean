/-
A bounded remainder in the sharp logarithmic law.

The upper Bellman semigroup `U` has uniformly bounded integrated amplification on broad
Gaussian densities: `∫ U^n γ_t ≤ 2` for `t ≥ A`. The proof is a strong induction over the
horizon, using the one-step Gaussian defect `|U γ_t - γ_{t+1}| ≤ D t^{-3/2} γ_{8t}`. Combined
with the residual bound of `LogResidual`, this gives an `O(1)` remainder for the CDF-`L¹`
distance and the mean.
-/
import CausalSeed.LogCost

open MeasureTheory Set Filter Topology Real Finset
open scoped ENNReal

namespace CausalSpectrum.Sqrt.IncFamily
variable (F : IncFamily)

/-- `U^{n+1} g = U^n (U g)`. -/
theorem U_succ' (g : ℝ → ℝ) : ∀ n, F.U (n + 1) g = F.U n (F.Tmax g)
  | 0 => rfl
  | n + 1 => by
    show F.Tmax (F.U (n + 1) g) = F.Tmax (F.U n (F.Tmax g))
    rw [U_succ' g n]

/-- Subadditivity of `U^n`. -/
theorem U_add_le (f g : ℝ → ℝ) : ∀ (n : ℕ) (x : ℝ),
    F.U n (fun y => f y + g y) x ≤ F.U n f x + F.U n g x
  | 0, _ => le_rfl
  | n + 1, x => (F.Tmax_mono (U_add_le f g n) x).trans (F.Tmax_add_le _ _ x)

theorem Tmax_smul_le {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ) (x : ℝ) :
    F.Tmax (fun y => c * f y) x ≤ c * F.Tmax f x :=
  Finset.sup'_le _ _ fun j _ => by
    have : F.expect j (fun y => c * f y) x = c * F.expect j f x := by
      simp only [expect, Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (Finset.le_sup' (fun j => F.expect j f x) (Finset.mem_univ j)) hc

/-- Positive homogeneity of `U^n` (one direction suffices). -/
theorem U_smul_le {c : ℝ} (hc : 0 ≤ c) (f : ℝ → ℝ) : ∀ (n : ℕ) (x : ℝ),
    F.U n (fun y => c * f y) x ≤ c * F.U n f x
  | 0, _ => le_rfl
  | n + 1, x => (F.Tmax_mono (U_smul_le hc f n) x).trans (F.Tmax_smul_le hc _ x)

theorem Tmax_translate (f : ℝ → ℝ) (c x : ℝ) :
    F.Tmax (fun z => f (z + c)) x = F.Tmax f (x + c) := by
  unfold Tmax expect
  congr 1; funext j; apply Finset.sum_congr rfl; intro y _
  simp only [show x - F.X j y + c = x + c - F.X j y by ring]

/-- Translation invariance of `U^n`. -/
theorem U_translate (f : ℝ → ℝ) (c : ℝ) :
    ∀ (n : ℕ) (x : ℝ), F.U n (fun z => f (z + c)) x = F.U n f (x + c)
  | 0, _ => rfl
  | n + 1, x => by
    have e : F.U n (fun z => f (z + c)) = fun z => F.U n f (z + c) := funext (U_translate f c n)
    show F.Tmax (F.U n (fun z => f (z + c))) x = F.Tmax (F.U n f) (x + c)
    rw [e]; exact F.Tmax_translate _ c x

end CausalSpectrum.Sqrt.IncFamily

namespace CausalSpectrum.LogGauss

/-! ### Gaussian densities `γ_t` and the constant `D_E` -/

/-- The `N(0, vt)` density `γ_t(x) = w φ(x w)` with `w = (vt)^{-1/2}`. -/
noncomputable def gam (v t x : ℝ) : ℝ := wv v t * phi (x * wv v t)

theorem wv_pos {v t : ℝ} (hv : 0 < v) (ht : 0 < t) : 0 < wv v t :=
  inv_pos.2 (sqrt_pos.2 (mul_pos hv ht))

theorem gam_nonneg {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (x : ℝ) : 0 ≤ gam v t x :=
  mul_nonneg (wv_pos hv ht).le (phi_pos _).le

theorem continuous_gam (v t : ℝ) : Continuous (gam v t) := by
  unfold gam; exact continuous_const.mul (continuous_phi.comp (by fun_prop))

theorem gam_eq (v t x : ℝ) : gam v t x = phi (x / √(v * t)) / √(v * t) := by
  simp [gam, wv, div_eq_mul_inv, mul_comm]

/-- `∫ γ_t(x - m) dx = 1`. -/
theorem lintegral_gam {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (m : ℝ) :
    ∫⁻ x, ENNReal.ofReal (gam v t (x - m)) = 1 := by
  have hs : 0 < √(v * t) := sqrt_pos.2 (mul_pos hv ht)
  have hi : Integrable fun x => phi ((x - m) / √(v * t)) / √(v * t) := by
    have : Integrable fun x => phi ((√(v * t))⁻¹ * x) :=
      (integrable_comp_mul_left_iff phi (inv_ne_zero hs.ne')).2 integrable_phi
    exact ((this.comp_sub_right m).div_const (√(v * t))).congr (ae_of_all _ fun x => by
      simp only [div_eq_inv_mul (x - m)])
  simp_rw [gam_eq]
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by
    have := phi_pos ((x - m) / √(v * t)); positivity)]
  have := (gauss_scaled_norms m hs).1
  rw [show (∫ x, phi ((x - m) / √(v * t)) / √(v * t)) = ∫ x, |phi ((x - m) / √(v * t)) / √(v * t)|
    from integral_congr_ae (ae_of_all _ fun x => by
      simp only; rw [abs_of_nonneg (by have := phi_pos ((x - m) / √(v * t)); positivity)])]
  rw [this, ENNReal.ofReal_one]

/-- `D_E = 64⁴ e^{-63/16}`. -/
noncomputable def DE : ℝ := 64 ^ 4 * exp (-(63 / 16))

theorem DE_pos : 0 < DE := by unfold DE; positivity

/-- `(1 + y)⁴ e^{-y/16} ≤ 64⁴ e^{-63/16}` (the maximum is at `y = 63`). -/
theorem pow_four_mul_exp_le {y : ℝ} (hy : 0 ≤ y) : (1 + y) ^ 4 * exp (-(y / 16)) ≤ DE := by
  have h1 : (1 + y) / 64 ≤ exp ((1 + y) / 64 - 1) := by
    have := add_one_le_exp ((1 + y) / 64 - 1); linarith
  have h2 : ((1 + y) / 64) ^ 4 ≤ exp ((1 + y) / 64 - 1) ^ 4 :=
    pow_le_pow_left₀ (by positivity) h1 4
  rw [← exp_nat_mul] at h2
  have e : (1 + y) ^ 4 = 64 ^ 4 * ((1 + y) / 64) ^ 4 := by ring
  rw [e, DE, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  calc ((1 + y) / 64) ^ 4 * exp (-(y / 16)) ≤ exp (↑4 * ((1 + y) / 64 - 1)) * exp (-(y / 16)) :=
        mul_le_mul_of_nonneg_right h2 (exp_pos _).le
    _ = exp (-(63 / 16)) := by rw [← exp_add]; congr 1; ring

/-- `E(z) ≤ D_E e^{-z²/16}`. -/
theorem Emaj_le_DE (z : ℝ) : Emaj z ≤ DE * exp (-(z ^ 2 / 16)) := by
  have := pow_four_mul_exp_le (sq_nonneg z)
  unfold Emaj
  calc (1 + z ^ 2) ^ 4 * exp (-(z ^ 2 / 8))
      = (1 + z ^ 2) ^ 4 * exp (-(z ^ 2 / 16)) * exp (-(z ^ 2 / 16)) := by
        rw [mul_assoc, ← exp_add]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right this (exp_pos _).le

/-- `w e^{-(x w)²/16} = √(2π) √8 γ_{8t}(x)` for `w = (vt)^{-1/2}`. -/
theorem exp_sixteen_eq {v t : ℝ} (hv : 0 < v) (ht : 0 < t) (x : ℝ) :
    wv v t * exp (-((x * wv v t) ^ 2 / 16)) = √(2 * π) * √8 * gam v (8 * t) x := by
  have h8 : wv v (8 * t) = wv v t / √8 := by
    simp only [wv]
    rw [show v * (8 * t) = 8 * (v * t) by ring, sqrt_mul (by norm_num), mul_inv, div_eq_mul_inv,
      mul_comm]
  have hp : 0 < √(2 * π) := sqrt_pos.2 (by positivity)
  have h8p : 0 < √8 := sqrt_pos.2 (by norm_num)
  have h88 : √8 ^ 2 = 8 := sq_sqrt (by norm_num)
  rw [gam, h8, phi]
  have : -((x * (wv v t / √8)) ^ 2 / 2) = -((x * wv v t) ^ 2 / 16) := by
    rw [show x * (wv v t / √8) = x * wv v t / √8 by ring, div_pow, h88]; ring
  rw [this]; field_simp

/-! ### Third-order Taylor bound for `φ` -/

theorem taylor_phi {D : ℝ} (hD : 0 ≤ D) {z y : ℝ} (hy : |y - z| ≤ D) :
    |phi y - (phi z + dphi z * (y - z) + ddphi z * (y - z) ^ 2 / 2)|
      ≤ 3 * CW D * Emaj z * |y - z| ^ 3 := by
  have hC : 0 ≤ 3 * CW D * Emaj z := by have := CW_nonneg hD; have := Emaj_nonneg z; positivity
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
      exact (h1.sub h2).congr_deriv (by simp; ring)) l2 hC y right_mem_uIcc
  convert l1 using 2; ring

/-! ### Time expansion of `γ_τ(x)` -/

section GamTime
variable (v x : ℝ)

/-- `∂_τ γ_τ(x) = w φ''(xw)/(2τ)`. -/
noncomputable def gam1 (τ : ℝ) : ℝ := wv v τ * ddphi (x * wv v τ) / (2 * τ)
/-- `∂²_τ γ_τ(x)`. -/
noncomputable def gam2 (τ : ℝ) : ℝ :=
  -(wv v τ * (3 * ddphi (x * wv v τ) + x * wv v τ * dddphi (x * wv v τ))) / (4 * τ ^ 2)

theorem hasDerivAt_gam (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (fun τ => gam v τ x) (gam1 v x τ) τ := by
  have hW := hasDerivAt_wv v hv hτ
  have h := hW.mul ((hasDerivAt_phi _).comp τ (hW.const_mul x))
  refine h.congr_deriv ?_
  simp only [gam1, dphi, ddphi, Function.comp_apply]; field_simp; ring

theorem hasDerivAt_gam1 (hv : 0 < v) {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (gam1 v x) (gam2 v x τ) τ := by
  have hW := hasDerivAt_wv v hv hτ
  have h := (hW.mul ((hasDerivAt_ddphi _).comp τ (hW.const_mul x))).div
    ((hasDerivAt_id τ).const_mul 2) (by simp only [id]; positivity)
  have e : gam1 v x = fun τ => (wv v τ * (ddphi ∘ fun τ => x * wv v τ) τ) / (2 * id τ) := by
    funext τ; simp [gam1]
  rw [e]; refine h.congr_deriv ?_
  simp only [gam2, Function.comp_apply, id, Pi.mul_apply]; field_simp; ring

theorem wv_sq {v τ : ℝ} (hv : 0 < v) (hτ : 0 < τ) : wv v τ ^ 2 = 1 / (v * τ) := by
  rw [wv, inv_pow, sq_sqrt (by positivity), one_div]

theorem wv_anti {v τ τ' : ℝ} (hv : 0 < v) (hτ : 0 < τ) (h : τ ≤ τ') : wv v τ' ≤ wv v τ :=
  inv_anti₀ (sqrt_pos.2 (by positivity)) (sqrt_le_sqrt (by nlinarith))

/-- `|∂²_τ γ_τ(x)| ≤ 2 w_t C_W(0) E(x w_t)/t²` for `τ ∈ [t, t+1]`, `t ≥ 1`. -/
theorem abs_gam2_le (hv : 0 < v) {t τ : ℝ} (ht : 1 ≤ t) (h1 : t ≤ τ) (h2 : τ ≤ t + 1) :
    |gam2 v x τ| ≤ 2 * wv v t * CW 0 * Emaj (x * wv v t) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hτ0 : 0 < τ := by linarith
  set w := x * wv v τ
  have hwt := wv_pos hv ht0
  have hwτ := wv_pos hv hτ0
  have hp := phi_pos w
  -- polynomial bound
  have hpoly : |3 * ddphi w + w * dddphi w| ≤ 6 * ((1 + |w|) ^ 4 * phi w) := by
    have a1 := abs_ddphi_le w
    have a2 := abs_dddphi_le w
    have q1 : (1 + |w|) ^ 2 ≤ (1 + |w|) ^ 4 :=
      pow_le_pow_right₀ (by linarith [abs_nonneg w]) (by norm_num)
    have q2 : |w| * (1 + |w|) ^ 3 ≤ (1 + |w|) ^ 4 := by
      rw [pow_succ' _ 3]; exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    calc _ ≤ 3 * |ddphi w| + |w| * |dddphi w| := by
          refine (abs_add_le _ _).trans ?_; rw [abs_mul, abs_mul]; norm_num
      _ ≤ 3 * ((1 + |w|) ^ 2 * phi w) + |w| * (3 * ((1 + |w|) ^ 3 * phi w)) := by gcongr
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right q1 hp.le, mul_le_mul_of_nonneg_right q2 hp.le]
  -- window
  set lam := wv v τ / wv v t
  have hl0 : 0 ≤ lam := by positivity
  have hl1 : lam ≤ 1 := by rw [div_le_one hwt]; exact wv_anti hv ht0 h1
  have hl2 : 1 / 2 ≤ lam ^ 2 := by
    rw [div_pow, wv_sq hv hτ0, wv_sq hv ht0, le_div_iff₀ (by positivity)]
    field_simp; nlinarith
  have hwz : w = lam * (x * wv v t) := by simp only [w, lam]; field_simp
  have hwin := window (le_refl (0:ℝ)) (k := 4) (by norm_num) hl0 hl1 hl2
    (show |w - lam * (x * wv v t)| ≤ 0 by rw [hwz, sub_self, abs_zero])
  rw [show 16 * (1 + (0:ℝ)) ^ 8 * exp (0 ^ 2 / 2) = CW 0 from rfl] at hwin
  rw [gam2, abs_div, abs_neg, abs_mul, abs_of_pos hwτ, abs_of_pos (by positivity : (0:ℝ) < 4 * τ ^ 2)]
  have hE := Emaj_nonneg (x * wv v t)
  have hC := CW_nonneg (le_refl (0:ℝ))
  calc wv v τ * |3 * ddphi w + w * dddphi w| / (4 * τ ^ 2)
      ≤ wv v t * (6 * (CW 0 * Emaj (x * wv v t))) / (4 * t ^ 2) := by
        gcongr
        · exact wv_anti hv ht0 h1
        · exact hpoly.trans (by linarith)
    _ ≤ _ := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [mul_nonneg (mul_nonneg hwt.le hC) hE]

/-- **Time Taylor bound.** `|γ_{t+1} - γ_t - ∂_tγ_t| ≤ 2 w_t C_W(0) E(x w_t)/t²`. -/
theorem time_gam (hv : 0 < v) {t : ℝ} (ht : 1 ≤ t) :
    |gam v (t + 1) x - gam v t x - gam1 v x t| ≤ 2 * wv v t * CW 0 * Emaj (x * wv v t) / t ^ 2 := by
  have ht0 : 0 < t := by linarith
  set C2 := 2 * wv v t * CW 0 * Emaj (x * wv v t) / t ^ 2
  have hC2 : 0 ≤ C2 := by
    have := wv_pos hv ht0; have := CW_nonneg (le_refl (0:ℝ)); have := Emaj_nonneg (x * wv v t)
    positivity
  have hI : ∀ w ∈ uIcc t (t + 1), t ≤ w ∧ w ≤ t + 1 := fun w hw => by
    rw [Set.uIcc_of_le (by linarith)] at hw; exact hw
  have l1 := ladder_all (x := t) (y := t + 1) (r := fun τ => gam1 v x τ - gam1 v x t)
    (r' := gam2 v x) 0 (by simp)
    (fun w hw => (hasDerivAt_gam1 v x hv (by linarith [(hI w hw).1])).sub_const _)
    (fun w hw => by rw [pow_zero, mul_one]; exact abs_gam2_le v x hv ht (hI w hw).1 (hI w hw).2) hC2
  have l0 := ladder (x := t) (y := t + 1)
    (r := fun τ => gam v τ x - gam v t x - gam1 v x t * (τ - t))
    (r' := fun τ => gam1 v x τ - gam1 v x t) 1 (by simp)
    (fun w hw => by
      have h := ((hasDerivAt_gam v x hv (by linarith [(hI w hw).1])).sub_const (gam v t x)).sub
        (((hasDerivAt_id w).sub_const t).const_mul (gam1 v x t))
      exact h.congr_deriv (by simp)) l1 hC2
  simp only [add_sub_cancel_left, mul_one, abs_one, one_pow] at l0
  exact l0

end GamTime

/-! ### The one-step Gaussian defect -/

section Defect
variable (F : Sqrt.IncFamily) (v : ℝ)

theorem wv_cube {t : ℝ} (hv : 0 < v) (ht : 0 < t) : wv v t ^ 3 = 1 / (v * √v * (t * √t)) := by
  have e1 : √v ^ 3 = v * √v := by rw [pow_succ, sq_sqrt hv.le]
  have e2 : √t ^ 3 = t * √t := by rw [pow_succ, sq_sqrt ht.le]
  rw [wv, sqrt_mul hv.le, inv_pow, mul_pow, e1, e2, one_div]

/-- **Spatial expansion of `A_j γ_t`.** -/
theorem spatial_gam (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ K, 0 ≤ K ∧ ∀ j t x, 1 ≤ t →
      |F.expect j (gam v t) x - (gam v t x + gam1 v x t)| ≤
        K * (wv v t * Emaj (x * wv v t)) / (t * √t) := by
  set M := Mx F
  have hM := Mx_nonneg F
  have hsv := sqrt_pos.2 hv
  set D := M / √v
  have hD : 0 ≤ D := by positivity
  refine ⟨3 * CW D * M ^ 3 / (v * √v), by have := CW_nonneg hD; positivity, fun j t x ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hw := wv_pos hv ht0
  set w := wv v t
  set z := x * w
  have hwle : w ≤ 1 / √v := by
    have := wv_anti hv one_pos ht
    show wv v t ≤ 1 / √v
    refine this.trans (le_of_eq ?_)
    simp [wv]
  have hE := Emaj_nonneg z
  have hW := CW_nonneg hD
  -- per-atom remainder
  set poly : ℝ → ℝ := fun h => w * (phi z + dphi z * -h + ddphi z * (-h) ^ 2 / 2)
  have hrem : ∀ y, |gam v t (x - F.X j y) - poly (F.X j y * w)|
      ≤ w * (3 * CW D * Emaj z * (M ^ 3 / (v * √v) / (t * √t))) := by
    intro y
    set h := F.X j y * w
    have hh : |h| ≤ M * w := by
      simp only [h, abs_mul, abs_of_pos hw]; gcongr; exact abs_X_le F j y
    have hMw : M * w ≤ D := by
      simp only [D]; rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hwle hM
    have hyz : |(z - h) - z| ≤ D := by rw [sub_sub_cancel_left, abs_neg]; exact hh.trans hMw
    have t1 := taylor_phi hD hyz
    rw [sub_sub_cancel_left, abs_neg] at t1
    have e : gam v t (x - F.X j y) - poly h =
        w * (phi (z - h) - (phi z + dphi z * -h + ddphi z * (-h) ^ 2 / 2)) := by
      have g : gam v t (x - F.X j y) = w * phi (z - h) := by
        simp only [gam, z, h, w]; ring_nf
      rw [g]; simp only [poly]; ring
    rw [e, abs_mul, abs_of_pos hw]
    refine mul_le_mul_of_nonneg_left (t1.trans ?_) hw.le
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    calc |h| ^ 3 ≤ (M * w) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hh 3
      _ = M ^ 3 / (v * √v) / (t * √t) := by rw [mul_pow, wv_cube v hv ht0]; field_simp
  have hpoly : ∑ y, F.P j y * poly (F.X j y * w) = gam v t x + gam1 v x t := by
    have e : ∀ y, poly (F.X j y * w) = w * phi z + (-(w * dphi z * w)) * F.X j y
        + (w * ddphi z * w ^ 2 / 2) * F.X j y ^ 2 + 0 * F.X j y ^ 3 := fun y => by
      simp only [poly]; ring
    simp only [e]
    rw [sum_cubic, F.Psum, hc j]
    have h2 : ∑ y, F.P j y * F.X j y ^ 2 = v := hσ j
    rw [h2, gam, gam1, show w * ddphi z * w ^ 2 / 2 * v = w * ddphi z * (v * w ^ 2) / 2 by ring,
      wv_sq hv ht0]
    simp only [z, w]; field_simp; ring
  have hexp : F.expect j (gam v t) x =
      ∑ y, F.P j y * poly (F.X j y * w) +
        ∑ y, F.P j y * (gam v t (x - F.X j y) - poly (F.X j y * w)) := by
    rw [← sum_add_distrib]; unfold Sqrt.IncFamily.expect; exact sum_congr rfl fun _ _ => by ring
  rw [hexp, ← hpoly, add_sub_cancel_left]
  calc _ ≤ ∑ y, |F.P j y * (gam v t (x - F.X j y) - poly (F.X j y * w))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, F.P j y * (w * (3 * CW D * Emaj z * (M ^ 3 / (v * √v) / (t * √t)))) :=
        sum_le_sum fun y _ => by
          rw [abs_mul, abs_of_pos (F.Ppos j y)]
          exact mul_le_mul_of_nonneg_left (hrem y) (F.Ppos j y).le
    _ = _ := by rw [← sum_mul, F.Psum, one_mul]; field_simp

/-- **Lemma (one-step Gaussian defect).** There is `D` with
`|U γ_t(x) - γ_{t+1}(x)| ≤ D t^{-3/2} γ_{8t}(x)` for all `t ≥ 1` and `x`. -/
theorem defect (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ D, 0 ≤ D ∧ ∀ t x, 1 ≤ t →
      |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x := by
  obtain ⟨K, hK, hS⟩ := spatial_gam F v hc hv hσ
  have hC0 := CW_nonneg (le_refl (0:ℝ))
  refine ⟨(K + 2 * CW 0) * DE * √(2 * π) * √8, by have := DE_pos; positivity, fun t x ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst := sqrt_pos.2 ht0
  have hw := wv_pos hv ht0
  set z := x * wv v t
  have hE := Emaj_nonneg z
  have hsq : √t ≤ t := by rw [sqrt_le_left ht0.le]; nlinarith
  have hone : ∀ j, |F.expect j (gam v t) x - gam v (t + 1) x| ≤
      (K + 2 * CW 0) * (wv v t * Emaj z) / (t * √t) := by
    intro j
    have h1 := hS j t x ht
    have h2 := time_gam v x hv ht
    have h3 : 2 * wv v t * CW 0 * Emaj z / t ^ 2 ≤ 2 * CW 0 * (wv v t * Emaj z) / (t * √t) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : 0 ≤ 2 * CW 0 * (wv v t * Emaj z) * t := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hsq this]
    calc _ = |(F.expect j (gam v t) x - (gam v t x + gam1 v x t)) -
          (gam v (t + 1) x - gam v t x - gam1 v x t)| := by ring_nf
      _ ≤ _ := abs_sub _ _
      _ ≤ K * (wv v t * Emaj z) / (t * √t) + 2 * CW 0 * (wv v t * Emaj z) / (t * √t) :=
          add_le_add h1 (h2.trans h3)
      _ = _ := by ring
  have hconv : (K + 2 * CW 0) * (wv v t * Emaj z) / (t * √t) ≤
      (K + 2 * CW 0) * DE * √(2 * π) * √8 / (t * √t) * gam v (8 * t) x := by
    have hb : wv v t * Emaj z ≤ DE * (√(2 * π) * √8 * gam v (8 * t) x) := by
      rw [← exp_sixteen_eq hv ht0 x]
      calc wv v t * Emaj z ≤ wv v t * (DE * exp (-(z ^ 2 / 16))) :=
            mul_le_mul_of_nonneg_left (Emaj_le_DE z) hw.le
        _ = _ := by ring
    calc _ ≤ (K + 2 * CW 0) * (DE * (√(2 * π) * √8 * gam v (8 * t) x)) / (t * √t) := by gcongr
      _ = _ := by ring
  have hall : ∀ j, |F.expect j (gam v t) x - gam v (t + 1) x| ≤
      (K + 2 * CW 0) * DE * √(2 * π) * √8 / (t * √t) * gam v (8 * t) x :=
    fun j => (hone j).trans hconv
  set e := (K + 2 * CW 0) * DE * √(2 * π) * √8 / (t * √t) * gam v (8 * t) x
  rw [abs_le]
  constructor
  · have := (abs_le.1 (hall ⟨0, F.hA⟩)).1
    have h0 : F.expect ⟨0, F.hA⟩ (gam v t) x ≤ F.Tmax (gam v t) x :=
      Finset.le_sup' (fun j => F.expect j (gam v t) x) (Finset.mem_univ _)
    linarith
  · have : F.Tmax (gam v t) x ≤ gam v (t + 1) x + e :=
      Finset.sup'_le _ _ fun j _ => by linarith [(abs_le.1 (hall j)).2]
    linarith

end Defect

/-! ### Gaussian telescoping and bounded amplification -/

section Amp
variable (F : Sqrt.IncFamily) (v : ℝ)

/-- **Gaussian telescoping.** If the one-step defect holds with constant `D`, then for `t ≥ 1`
`U^n γ_t ≤ γ_{t+n} + D Σ_{r<n} (t+r)^{-3/2} U^{n-1-r} γ_{8(t+r)}`. -/
theorem telescope {D : ℝ} (hD : 0 ≤ D) (hv : 0 < v)
    (hdef : ∀ t x, 1 ≤ t → |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x) :
    ∀ (n : ℕ) (t x : ℝ), 1 ≤ t →
      F.U n (gam v t) x ≤ gam v (t + n) x + ∑ r ∈ range n,
        D / ((t + r) * √(t + r)) * F.U (n - 1 - r) (gam v (8 * (t + r))) x := by
  intro n
  induction n with
  | zero => intro t x _; simp [Sqrt.IncFamily.U]
  | succ n ih =>
    intro t x ht
    have ht0 : 0 < t := by linarith
    have hc : 0 ≤ D / (t * √t) := by have := sqrt_nonneg t; positivity
    have hstep : ∀ y, F.Tmax (gam v t) y ≤ gam v (t + 1) y + D / (t * √t) * gam v (8 * t) y :=
      fun y => by linarith [(abs_le.1 (hdef t y ht)).2]
    have h1 := F.U_mono hstep n x
    rw [← F.U_succ'] at h1
    have h2 := F.U_add_le (gam v (t + 1)) (fun y => D / (t * √t) * gam v (8 * t) y) n x
    have h3 := F.U_smul_le hc (gam v (8 * t)) n x
    have h4 := ih (t + 1) x (by linarith)
    rw [sum_range_succ']
    have e1 : t + 1 + (n : ℝ) = t + ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    have e2 : ∑ r ∈ range n, D / ((t + 1 + r) * √(t + 1 + r)) *
        F.U (n - 1 - r) (gam v (8 * (t + 1 + r))) x =
        ∑ r ∈ range n, D / ((t + ((r + 1 : ℕ) : ℝ)) * √(t + ((r + 1 : ℕ) : ℝ))) *
          F.U (n + 1 - 1 - (r + 1)) (gam v (8 * (t + ((r + 1 : ℕ) : ℝ)))) x := by
      refine sum_congr rfl fun r _ => ?_
      rw [show n + 1 - 1 - (r + 1) = n - 1 - r by omega]
      have : t + 1 + (r : ℝ) = t + ((r + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [this]
    rw [e1, e2] at h4
    simp only [Nat.cast_zero, add_zero, show n + 1 - 1 - 0 = n by omega]
    linarith

/-- **Lemma (bounded integrated amplification).** Let the defect hold with constant `D`, and let
`A ≥ 2` with `6D ≤ √A` (that is, `3D/√A ≤ 1/2`). Then `∫ U^n γ_t ≤ 2` for every `t ≥ A` and
every `n`. -/
theorem amp_bounded {D A : ℝ} (hD : 0 ≤ D) (hv : 0 < v)
    (hdef : ∀ t x, 1 ≤ t → |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x)
    (hA2 : 2 ≤ A) (hAD : 6 * D ≤ √A) :
    ∀ (n : ℕ) (t : ℝ), A ≤ t → ∫⁻ x, ENNReal.ofReal (F.U n (gam v t) x) ≤ 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro t ht
  have ht2 : 2 ≤ t := hA2.trans ht
  have ht1 : 1 ≤ t := by linarith
  have ht0 : 0 < t := by linarith
  have hτ : ∀ r : ℕ, 0 < t + r := fun r => by have := (Nat.cast_nonneg r : (0:ℝ) ≤ r); linarith
  set c : ℕ → ℝ := fun r => D / ((t + r) * √(t + r))
  have hc : ∀ r, 0 ≤ c r := fun r => by have := hτ r; have := sqrt_nonneg (t + r); positivity
  have hmU : ∀ k s, 0 < s → Measurable (F.U k (gam v s)) := fun k s _ =>
    F.measurable_U (continuous_gam v s).measurable k
  have hUnn : ∀ k s y, 0 < s → 0 ≤ F.U k (gam v s) y := fun k s y hs =>
    F.U_nonneg (gam_nonneg hv hs) k y
  have hpt : ∀ x, ENNReal.ofReal (F.U n (gam v t) x) ≤ ENNReal.ofReal (gam v (t + n) x) +
      ∑ r ∈ range n, ENNReal.ofReal (c r) * ENNReal.ofReal (F.U (n - 1 - r) (gam v (8 * (t + r))) x) := by
    intro x
    refine (ENNReal.ofReal_le_ofReal (telescope F v hD hv hdef n t x ht1)).trans ?_
    refine (ENNReal.ofReal_add_le).trans (add_le_add le_rfl ?_)
    refine (Sqrt.IncFamily.ofReal_sum_le _ _).trans (sum_le_sum fun r _ => ?_)
    rw [ENNReal.ofReal_mul (hc r)]
  have hsum := sum_pow_three_halves ht2 n
  have h4D : 4 * D ≤ √(t - 1) := by
    have h36 : 36 * D ^ 2 ≤ t := by
      have := mul_self_le_mul_self (by positivity) (hAD.trans (sqrt_le_sqrt ht))
      rw [mul_self_sqrt ht0.le] at this; nlinarith
    exact Real.le_sqrt_of_sq_le (by nlinarith)
  have hs0 : 0 ≤ ∑ r ∈ range n, c r := sum_nonneg fun r _ => hc r
  have hsmall : 2 * ∑ r ∈ range n, c r ≤ 1 := by
    have hl := sqrt_pos.2 (show 0 < t - 1 by linarith)
    have : 2 * (2 / √(t - 1)) * D ≤ 1 := by
      rw [show 2 * (2 / √(t - 1)) * D = 4 * D / √(t - 1) by ring, div_le_one hl]; exact h4D
    have hcD : ∑ r ∈ range n, c r = D * ∑ r ∈ range n, 1 / ((t + r) * √(t + r)) := by
      rw [mul_sum]; exact sum_congr rfl fun r _ => by simp only [c]; ring
    rw [hcD]
    have := mul_le_mul_of_nonneg_left hsum hD
    nlinarith
  have hgm : Measurable fun x => ENNReal.ofReal (gam v (t + n) x) :=
    ENNReal.measurable_ofReal.comp (continuous_gam v _).measurable
  calc ∫⁻ x, ENNReal.ofReal (F.U n (gam v t) x)
      ≤ ∫⁻ x, (ENNReal.ofReal (gam v (t + n) x) +
          ∑ r ∈ range n, ENNReal.ofReal (c r) *
            ENNReal.ofReal (F.U (n - 1 - r) (gam v (8 * (t + r))) x)) := lintegral_mono hpt
    _ = (∫⁻ x, ENNReal.ofReal (gam v (t + n) x)) + ∑ r ∈ range n, ENNReal.ofReal (c r) *
          ∫⁻ x, ENNReal.ofReal (F.U (n - 1 - r) (gam v (8 * (t + r))) x) := by
        have hm1 : ∀ r : ℕ, Measurable fun a =>
            ENNReal.ofReal (F.U (n - 1 - r) (gam v (8 * (t + r))) a) := fun r =>
          ENNReal.measurable_ofReal.comp (hmU _ _ (by have := hτ r; linarith))
        have hm2 : ∀ r ∈ range n, Measurable fun a =>
            ENNReal.ofReal (c r) * ENNReal.ofReal (F.U (n - 1 - r) (gam v (8 * (t + r))) a) :=
          fun r _ => (hm1 r).const_mul _
        rw [lintegral_add_left hgm, lintegral_finset_sum _ hm2]
        congr 1; exact sum_congr rfl fun r _ => lintegral_const_mul _ (hm1 r)
    _ ≤ 1 + ∑ r ∈ range n, ENNReal.ofReal (c r) * 2 := by
        gcongr with r hr
        · have := lintegral_gam hv (hτ n) 0; simp only [sub_zero] at this; rw [this]
        · exact ih _ (by have := mem_range.1 hr; omega) _
            (by have := (Nat.cast_nonneg r : (0:ℝ) ≤ r); linarith)
    _ = ENNReal.ofReal (1 + 2 * ∑ r ∈ range n, c r) := by
        rw [ENNReal.ofReal_add zero_le_one (by positivity), ENNReal.ofReal_one, mul_sum, ENNReal.ofReal_sum_of_nonneg (fun r _ => by
            have := hc r; positivity)]
        congr 1; refine sum_congr rfl fun r _ => ?_
        rw [ENNReal.ofReal_mul zero_le_two, mul_comm, ENNReal.ofReal_ofNat]
    _ ≤ 2 := by
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
        exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Bounded amplification of Gaussian-dominated functions.** If `|R| ≤ b γ_t(· - m)` with
`b ≥ 0` and `t ≥ A`, then `∫ U^k |R| ≤ 2b` for every `k`. -/
theorem amp_gauss {D A : ℝ} (hD : 0 ≤ D) (hv : 0 < v)
    (hdef : ∀ t x, 1 ≤ t → |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x)
    (hA2 : 2 ≤ A) (hAD : 6 * D ≤ √A) {R : ℝ → ℝ} {b t m : ℝ} (hb : 0 ≤ b) (ht : A ≤ t)
    (hR : ∀ y, |R y| ≤ b * gam v t (y - m)) (k : ℕ) :
    ∫⁻ x, ENNReal.ofReal (F.U k (fun y => |R y|) x) ≤ ENNReal.ofReal (2 * b) := by
  have hpt : ∀ x, F.U k (fun y => |R y|) x ≤ b * F.U k (gam v t) (x - m) := fun x => by
    refine (F.U_mono hR k x).trans ((F.U_smul_le hb _ k x).trans (le_of_eq ?_))
    rw [sub_eq_add_neg, ← F.U_translate (gam v t) (-m) k x]; rfl
  have hm : Measurable fun x => ENNReal.ofReal (F.U k (gam v t) x) :=
    ENNReal.measurable_ofReal.comp (F.measurable_U (continuous_gam v t).measurable k)
  calc _ ≤ ∫⁻ x, ENNReal.ofReal b * ENNReal.ofReal (F.U k (gam v t) (x - m)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_mul hb]; exact ENNReal.ofReal_le_ofReal (hpt x)
    _ = ENNReal.ofReal b * ∫⁻ x, ENNReal.ofReal (F.U k (gam v t) x) := by
        have hm' : Measurable fun x => ENNReal.ofReal (F.U k (gam v t) (x - m)) :=
          hm.comp (measurable_id.sub_const m)
        rw [lintegral_const_mul _ hm']
        congr 1
        exact lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (F.U k (gam v t) x)) m
    _ ≤ ENNReal.ofReal b * 2 := by gcongr; exact amp_bounded F v hD hv hdef hA2 hAD k t ht
    _ = _ := by rw [mul_comm, ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]

/-- **Stability.** If `|f - g| ≤ b γ_t(· - m)` with `t ≥ A`, then `‖T^n f - T^n g‖₁ ≤ 2b`. -/
theorem stability_gauss {D A : ℝ} (hD : 0 ≤ D) (hv : 0 < v)
    (hdef : ∀ t x, 1 ≤ t → |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x)
    (hA2 : 2 ≤ A) (hAD : 6 * D ≤ √A) {f g : ℝ → ℝ} {b t m : ℝ} (hb : 0 ≤ b) (ht : A ≤ t)
    (hfg : ∀ y, |f y - g y| ≤ b * gam v t (y - m)) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |F.Tit n f x - F.Tit n g x| ≤ ENNReal.ofReal (2 * b) :=
  le_trans (lintegral_mono fun x => ENNReal.ofReal_le_ofReal (F.abs_Tit_sub_le f g n x))
    (amp_gauss F v hD hv hdef hA2 hAD (R := fun y => f y - g y) hb ht hfg n)

end Amp

/-! ### Gaussian forms of the residual and of the initial error -/

section Inputs
variable (F : Sqrt.IncFamily) (v : ℝ)

theorem exp_sixteen_eq' {t : ℝ} (hv : 0 < v) (ht : 0 < t) (y : ℝ) :
    exp (-((y * wv v t) ^ 2 / 16)) = √(2 * π) * √8 / wv v t * gam v (8 * t) y := by
  have hw := wv_pos hv ht
  have := exp_sixteen_eq hv ht y
  rw [div_mul_eq_mul_div, eq_div_iff hw.ne', mul_comm]; exact this

theorem zt_eq (t x : ℝ) : zt F v t x = (x - cdrift F v * log t) * wv v t := by
  simp [zt, wv, div_eq_mul_inv]

theorem inv_wv {t : ℝ} (hv : 0 < v) (ht : 0 < t) : 1 / wv v t = √v * √t := by
  rw [wv, one_div, inv_inv, sqrt_mul hv.le]

/-- **Residual in Gaussian form.** `|u_{t+1} - T u_t| ≤ b₀ t^{-3/2} γ_{8t}(· - c ln t)`. -/
theorem residual_gauss (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ b0, 0 ≤ b0 ∧ ∀ t x, 1 ≤ t →
      |prof F v (t + 1) x - F.T (prof F v t) x| ≤
        b0 / (t * √t) * gam v (8 * t) (x - cdrift F v * log t) := by
  obtain ⟨K, hK, hR⟩ := residual_pointwise F v hc hv hσ
  have hp : 0 < √(2 * π) * √8 := by positivity
  refine ⟨K * DE * (√(2 * π) * √8) * √v, by have := DE_pos; positivity, fun t x ht => ?_⟩
  have ht0 : 0 < t := by linarith
  have hst := sqrt_pos.2 ht0
  set y := x - cdrift F v * log t
  have hg := gam_nonneg hv (show 0 < 8 * t by linarith) y
  refine (hR t x ht).trans ?_
  rw [zt_eq]
  calc K / t ^ 2 * Emaj (y * wv v t) ≤ K / t ^ 2 * (DE * exp (-((y * wv v t) ^ 2 / 16))) :=
        mul_le_mul_of_nonneg_left (Emaj_le_DE _) (by positivity)
    _ = K / t ^ 2 * (DE * (√(2 * π) * √8 * (1 / wv v t) * gam v (8 * t) y)) := by
        rw [exp_sixteen_eq' v hv ht0]; ring
    _ = _ := by
        rw [inv_wv v hv ht0]
        have hq : √t / t ^ 2 = 1 / (t * √t) := by
          rw [div_eq_div_iff (by positivity) (by positivity)]
          have := sq_sqrt ht0.le; linear_combination t * this
        calc K / t ^ 2 * (DE * (√(2 * π) * √8 * (√v * √t) * gam v (8 * t) y))
            = K * DE * (√(2 * π) * √8) * √v * (√t / t ^ 2) * gam v (8 * t) y := by ring
          _ = _ := by rw [hq]; ring

/-- **Initial Gaussian majorant.** For fixed `T ≥ 1`, `|H - u_T| ≤ b₁ γ_{8T}(· - c ln T)`. -/
theorem initial_gauss (hv : 0 < v) {T : ℝ} (hT : 1 ≤ T) :
    ∃ b1, 0 ≤ b1 ∧ ∀ x, |F.G 0 x - prof F v T x| ≤
      b1 * gam v (8 * T) (x - cdrift F v * log T) := by
  obtain ⟨KB, hKB, hB⟩ := abs_cB_le_Emaj (calpha F v) (cbeta F v)
  have hT0 : 0 < T := by linarith
  have hw := wv_pos hv hT0
  have hsT := sqrt_pos.2 hT0
  set c := cdrift F v
  set z0 := |c * log T| * wv v T
  have hp : 0 < √(2 * π) * √8 := by positivity
  refine ⟨(exp (z0 ^ 2 / 16) + KB * DE / √T) * (√(2 * π) * √8 / wv v T),
    by have := DE_pos; positivity, fun x => ?_⟩
  set y := x - c * log T
  set z := y * wv v T
  have hz : zt F v T x = z := zt_eq F v T x
  have hE : exp (-(z ^ 2 / 16)) = √(2 * π) * √8 / wv v T * gam v (8 * T) y :=
    exp_sixteen_eq' v hv hT0 y
  -- the step part
  have hH : |Hs x - Phi z| ≤ exp (z0 ^ 2 / 16) * exp (-(z ^ 2 / 16)) := by
    rw [← exp_add]
    have hP0 := Phi_nonneg z; have hP1 := Phi_le_one z
    rcases le_or_gt |z| z0 with h | h
    · have h1 : |Hs x - Phi z| ≤ 1 := by
        unfold Hs; split_ifs <;> rw [abs_le] <;> constructor <;> linarith
      refine h1.trans (one_le_exp_iff.2 ?_ |> le_of_eq_of_le rfl)
      have : z ^ 2 ≤ z0 ^ 2 := by
        rw [← sq_abs z]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
      linarith
    · have hg : exp (-(z ^ 2 / 2)) ≤ exp (z0 ^ 2 / 16 + -(z ^ 2 / 16)) :=
        exp_le_exp.2 (by nlinarith [sq_nonneg z0, sq_nonneg z])
      rcases lt_abs.1 h with h' | h'
      · -- z > z0: x > 0
        have hy : |c * log T| < y := by
          rw [← mul_lt_mul_iff_of_pos_right hw]; exact h'
        have hx : 0 ≤ x := by simp only [y] at hy; linarith [neg_le_abs (c * log T)]
        rw [show Hs x = 1 by simp [Hs, hx], abs_of_nonneg (by linarith)]
        have hz0' : 0 ≤ z0 := by positivity
        exact (one_sub_Phi_le_gauss (by linarith)).trans hg
      · -- z < -z0: x < 0
        have hy : y < -|c * log T| := by
          have : y * wv v T < -|c * log T| * wv v T := by linarith
          exact (mul_lt_mul_iff_of_pos_right hw).1 this
        have hx : x < 0 := by simp only [y] at hy; linarith [le_abs_self (c * log T)]
        rw [show Hs x = 0 by simp [Hs, not_le.2 hx], zero_sub, abs_neg, abs_of_nonneg hP0]
        have hz0 : z ≤ 0 := by
          have : 0 ≤ z0 := by positivity
          linarith
        exact (Phi_le_gauss hz0).trans hg
  have hBz : |cB (calpha F v) (cbeta F v) z| / √T ≤ KB * DE / √T * exp (-(z ^ 2 / 16)) := by
    rw [div_le_iff₀ hsT]
    calc _ ≤ KB * Emaj z := hB z
      _ ≤ KB * (DE * exp (-(z ^ 2 / 16))) := mul_le_mul_of_nonneg_left (Emaj_le_DE z) hKB
      _ = _ := by field_simp
  rw [G0_eq_Hs]
  unfold prof; rw [hz]
  calc |Hs x - (Phi z + cB (calpha F v) (cbeta F v) z / √T)|
      = |(Hs x - Phi z) - cB (calpha F v) (cbeta F v) z / √T| := by ring_nf
    _ ≤ |Hs x - Phi z| + |cB (calpha F v) (cbeta F v) z| / √T := by
        refine (abs_sub _ _).trans ?_; rw [abs_div, abs_of_pos hsT]
    _ ≤ exp (z0 ^ 2 / 16) * exp (-(z ^ 2 / 16)) + KB * DE / √T * exp (-(z ^ 2 / 16)) :=
        add_le_add hH hBz
    _ = _ := by rw [hE]; ring

end Inputs

/-! ### Propagation with bounded amplification and the main theorem -/

section Bounded
variable (F : Sqrt.IncFamily) (v : ℝ)

/-- Translated amplification bound: `∫ U^k γ_t(· - m) ≤ 2` for `t ≥ A`. -/
theorem amp_shift {D A : ℝ} (hD : 0 ≤ D) (hv : 0 < v)
    (hdef : ∀ t x, 1 ≤ t → |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x)
    (hA2 : 2 ≤ A) (hAD : 6 * D ≤ √A) {t : ℝ} (ht : A ≤ t) (m : ℝ) (k : ℕ) :
    ∫⁻ x, ENNReal.ofReal (F.U k (gam v t) (x - m)) ≤ 2 := by
  rw [lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (F.U k (gam v t) x)) m]
  exact amp_bounded F v hD hv hdef hA2 hAD k t ht

/-- **Propagation with bounded amplification.** If a profile family `P` has one-step residuals
`|P(t+1) - T P(t)| ≤ b₀ t^{-3/2} γ_{8t}(· - m(t))` for `t ≥ 1`, then for `T₀ ≥ A`
`‖T^n P(T₀) - P(T₀+n)‖₁ ≤ 4 b₀` for every `n`. -/
theorem propagation_bounded {D A : ℝ} (hD : 0 ≤ D) (hv : 0 < v)
    (hdef : ∀ t x, 1 ≤ t → |F.Tmax (gam v t) x - gam v (t + 1) x| ≤ D / (t * √t) * gam v (8 * t) x)
    (hA2 : 2 ≤ A) (hAD : 6 * D ≤ √A) (P : ℝ → ℝ → ℝ) (m : ℝ → ℝ) {b0 : ℝ} (hb0 : 0 ≤ b0)
    (hres : ∀ t x, 1 ≤ t → |P (t + 1) x - F.T (P t) x| ≤ b0 / (t * √t) * gam v (8 * t) (x - m t))
    {T : ℝ} (hT : A ≤ T) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal |F.Tit n (P T) x - P (T + n) x| ≤ ENNReal.ofReal (4 * b0) := by
  have hT2 : 2 ≤ T := hA2.trans hT
  have hτ : ∀ j : ℕ, 2 ≤ T + j := fun j => by have := (Nat.cast_nonneg j : (0:ℝ) ≤ j); linarith
  set β : ℕ → ℝ := fun j => b0 / ((T + j) * √(T + j))
  have hβ : ∀ j, 0 ≤ β j := fun j => by have := hτ j; have := sqrt_nonneg (T + j); positivity
  set u : ℕ → ℝ → ℝ := fun j => P (T + j)
  have hpt : ∀ x, ENNReal.ofReal |F.Tit n (P T) x - P (T + n) x| ≤ ∑ j ∈ range n,
      ENNReal.ofReal (β j) * ENNReal.ofReal (F.U (n - 1 - j) (gam v (8 * (T + j))) (x - m (T + j))) := by
    intro x
    have h0 := F.propagation u n x
    have hu0 : u 0 = P T := by simp [u]
    rw [hu0] at h0
    refine (ENNReal.ofReal_le_ofReal h0).trans ((Sqrt.IncFamily.ofReal_sum_le _ _).trans
      (sum_le_sum fun j _ => ?_))
    rw [← ENNReal.ofReal_mul (hβ j)]
    apply ENNReal.ofReal_le_ofReal
    have hR : ∀ y, |u (j + 1) y - F.T (u j) y| ≤ β j * gam v (8 * (T + j)) (y - m (T + j)) := by
      intro y
      have e : u (j + 1) = P (T + j + 1) := by simp only [u]; push_cast; rw [add_assoc]
      rw [e]; exact hres (T + j) y (by linarith [hτ j])
    refine (F.U_mono hR _ x).trans ((F.U_smul_le (hβ j) _ _ x).trans (le_of_eq ?_))
    rw [sub_eq_add_neg, ← F.U_translate (gam v (8 * (T + j))) (-m (T + j)) _ x]; rfl
  have hm : ∀ j : ℕ, Measurable fun x =>
      ENNReal.ofReal (F.U (n - 1 - j) (gam v (8 * (T + j))) (x - m (T + j))) := fun j =>
    ENNReal.measurable_ofReal.comp ((F.measurable_U (continuous_gam v _).measurable _).comp
      (measurable_id.sub_const _))
  have hsum := sum_pow_three_halves hT2 n
  have hsq : 1 ≤ √(T - 1) := Real.one_le_sqrt.2 (by linarith)
  have hsb : ∑ j ∈ range n, β j ≤ 2 * b0 := by
    have e : ∑ j ∈ range n, β j = b0 * ∑ j ∈ range n, 1 / ((T + j) * √(T + j)) := by
      rw [mul_sum]; exact sum_congr rfl fun j _ => by simp only [β]; ring
    rw [e]
    have : 2 / √(T - 1) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
    nlinarith [mul_le_mul_of_nonneg_left (hsum.trans this) hb0]
  calc _ ≤ ∫⁻ x, ∑ j ∈ range n, ENNReal.ofReal (β j) *
        ENNReal.ofReal (F.U (n - 1 - j) (gam v (8 * (T + j))) (x - m (T + j))) := lintegral_mono hpt
    _ = ∑ j ∈ range n, ENNReal.ofReal (β j) *
        ∫⁻ x, ENNReal.ofReal (F.U (n - 1 - j) (gam v (8 * (T + j))) (x - m (T + j))) := by
        rw [lintegral_finset_sum _ (fun j _ => (hm j).const_mul _)]
        exact sum_congr rfl fun j _ => lintegral_const_mul _ (hm j)
    _ ≤ ∑ j ∈ range n, ENNReal.ofReal (β j) * 2 := by
        gcongr with j hj
        exact amp_shift F v hD hv hdef hA2 hAD (by linarith [hτ j]) _ _
    _ = ENNReal.ofReal (2 * ∑ j ∈ range n, β j) := by
        rw [mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by have := hβ j; positivity)]
        refine sum_congr rfl fun j _ => ?_
        rw [ENNReal.ofReal_mul zero_le_two, mul_comm, ENNReal.ofReal_ofNat]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)

set_option maxHeartbeats 1000000 in
/-- **Main theorem (bounded remainder), `L¹`-CDF form.** There is `K` such that for every
`n ≥ 1`, `∫ |G_n(x) - Φ((x - c ln n)/√(vn))| dx ≤ K`, i.e. the Wasserstein-1 distance between
`ν_n` and `N(c ln n, vn)` is `O(1)`. -/
theorem bounded_L1 (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ K, ∀ n : ℕ, 1 ≤ n →
      ∫⁻ x, ENNReal.ofReal |F.G n x - Phi ((x - cdrift F v * log n) / √(v * n))| ≤
        ENNReal.ofReal K := by
  obtain ⟨D, hD, hdef⟩ := defect F v hc hv hσ
  set A := 2 + 36 * D ^ 2
  have hA2 : 2 ≤ A := by have := sq_nonneg D; linarith
  have hAD : 6 * D ≤ √A := Real.le_sqrt_of_sq_le (by nlinarith)
  have hT1 : 1 ≤ A := by linarith
  have hA0 : 0 < A := by linarith
  obtain ⟨b1, hb1, hin⟩ := initial_gauss F v hv hT1
  obtain ⟨b0, hb0, hres⟩ := residual_gauss F v hc hv hσ
  obtain ⟨KB, hKB, hB⟩ := abs_cB_le_Emaj (calpha F v) (cbeta F v)
  set c := cdrift F v
  set IE := ∫ z, Emaj z
  have hIE : 0 ≤ IE := integral_nonneg Emaj_nonneg
  have hsv := sqrt_pos.2 hv
  have hp0 := phi_pos 0
  refine ⟨2 * b1 + 4 * b0 + KB * √v * IE + √v * A * (2 * phi 0) + |c| * A, fun n hn => ?_⟩
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  -- (1) initial stability
  have E1 : ∫⁻ x, ENNReal.ofReal |F.G n x - F.Tit n (prof F v A) x| ≤ ENNReal.ofReal (2 * b1) := by
    rw [← F.Tit_H]
    exact stability_gauss F v hD hv hdef hA2 hAD hb1 (show A ≤ 8 * A by linarith) hin n
  -- (2) propagation
  have E2 := propagation_bounded F v hD hv hdef hA2 hAD (prof F v) (fun t => c * log t) hb0
    (fun t x ht => hres t x ht) le_rfl n
  -- (3) remove the corrector at time `A + n`
  set τ := A + n
  have hτ0 : 0 < τ := by linarith
  have hsτ := sqrt_pos.2 hτ0
  set s2 := √(v * τ)
  have hs2 : 0 < s2 := sqrt_pos.2 (by positivity)
  set m2 := c * log τ
  have E3 : ∫⁻ x, ENNReal.ofReal |prof F v τ x - Phi ((x - m2) / s2)| ≤
      ENNReal.ofReal (KB * √v * IE) := by
    have hK : 0 ≤ KB / √τ := by positivity
    obtain ⟨q1, -⟩ := lintegral_majorant_scaled hK m2 hs2
    calc _ ≤ ∫⁻ x, ‖KB / √τ * Emaj ((x - m2) / s2)‖ₑ := by
          refine lintegral_mono fun x => ?_
          rw [← ofReal_norm, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg hK (Emaj_nonneg _))]
          apply ENNReal.ofReal_le_ofReal
          have hz : zt F v τ x = (x - m2) / s2 := rfl
          unfold prof; rw [hz, add_sub_cancel_left, abs_div, abs_of_pos hsτ, div_le_iff₀ hsτ]
          calc _ ≤ KB * Emaj ((x - m2) / s2) := hB _
            _ = _ := by field_simp
      _ = _ := by
          rw [q1]; congr 1
          simp only [s2]; rw [sqrt_mul hv.le]; field_simp; rfl
  -- (4) scale and (5) shift
  set s1 := √(v * n)
  have hs1 : 0 < s1 := sqrt_pos.2 (by positivity)
  have h12 : s1 ≤ s2 := sqrt_le_sqrt (by nlinarith)
  have E4 := lintegral_Phi_scale hs1 h12 m2
  have E5 := lintegral_Phi_shift m2 (c * log n) hs1
  -- measurability
  have mG : Measurable (F.G n) := F.measurable_G n
  have mprof : ∀ t, Measurable (prof F v t) := fun t => by
    unfold prof zt
    exact ((continuous_Phi.comp (by fun_prop)).add
      (((continuous_cB _ _).comp (by fun_prop)).div_const _)).measurable
  have mTu : Measurable (F.Tit n (prof F v A)) := F.measurable_Tit (mprof A) n
  have mP : ∀ m s, Measurable fun x => Phi ((x - m) / s) := fun m s =>
    (continuous_Phi.comp (by fun_prop)).measurable
  have chain := (lintegral_tri (h := fun x => Phi ((x - c * log n) / s1)) mG mTu).trans
    (add_le_add E1 ((lintegral_tri mTu (mprof τ)).trans (add_le_add E2
      ((lintegral_tri (mprof τ) (mP m2 s2)).trans (add_le_add E3
        ((lintegral_tri (mP m2 s2) (mP m2 s1)).trans (add_le_add E4 E5)))))))
  refine chain.trans ?_
  -- real bounds
  have b4 : (s2 - s1) / s1 * s2 * (2 * phi 0) ≤ √v * A * (2 * phi 0) := by
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    have hq1 : s1 ^ 2 = v * n := sq_sqrt (by positivity)
    have hq2 : s2 ^ 2 = v * τ := sq_sqrt (by positivity)
    have hvs : √v ≤ s1 := sqrt_le_sqrt (by nlinarith)
    have hvv : √v ^ 2 = v := sq_sqrt hv.le
    rw [div_mul_eq_mul_div, div_le_iff₀ hs1]
    have hdiff : (s2 - s1) * (s2 + s1) = v * A := by simp only [τ] at hq2; nlinarith
    have h1 : (s2 - s1) * s2 ≤ v * A := by nlinarith [sub_nonneg.2 h12]
    have h2 : v * A ≤ √v * A * s1 := by nlinarith [mul_le_mul_of_nonneg_left hvs (mul_nonneg hsv.le hA0.le)]
    linarith
  have b5 : |m2 - c * log n| ≤ |c| * A := by
    simp only [m2]
    rw [← mul_sub, abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg c)
    have h1 : log (n:ℝ) ≤ log τ := Real.log_le_log hn0 (by linarith)
    rw [abs_of_nonneg (by linarith), ← Real.log_div hτ0.ne' hn0.ne']
    have := Real.log_le_sub_one_of_pos (show 0 < τ / n by positivity)
    have : τ / n ≤ 1 + A := by rw [div_le_iff₀ hn0]; nlinarith
    linarith
  have p1 : 0 ≤ 2 * b1 := by positivity
  have p2 : 0 ≤ 4 * b0 := by positivity
  have p3 : 0 ≤ KB * √v * IE := by positivity
  have p4 : 0 ≤ (s2 - s1) / s1 * s2 * (2 * phi 0) := by
    have := sub_nonneg.2 h12; positivity
  have p5 : 0 ≤ |m2 - c * log n| := abs_nonneg _
  rw [← ENNReal.ofReal_add p4 p5, ← ENNReal.ofReal_add p3 (by positivity),
    ← ENNReal.ofReal_add p2 (by positivity), ← ENNReal.ofReal_add p1 (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by linarith)

/-- **Main theorem (bounded remainder), mean form.** `|e_n - c ln n| ≤ K` for every `n ≥ 1`. -/
theorem bounded_mean (hc : F.Centered) (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ K, ∀ n : ℕ, 1 ≤ n → |F.eG (F.G n) - cdrift F v * log n| ≤ K := by
  obtain ⟨C, hC⟩ := bounded_L1 F v hc hv hσ
  refine ⟨|C|, fun n hn => ?_⟩
  set p := fun x => Phi ((x - cdrift F v * log n) / √(v * n))
  have hs : 0 < √(v * n) := sqrt_pos.2 (mul_pos hv (by exact_mod_cast hn))
  have hL := (hC n hn).trans (ENNReal.ofReal_le_ofReal (le_abs_self C))
  have hmeas : AEStronglyMeasurable (fun x => p x - F.G n x) volume :=
    (((continuous_Phi.comp (by fun_prop)).measurable).sub (F.measurable_G n)).aestronglyMeasurable
  have hfin : ∫⁻ x, ‖p x - F.G n x‖ₑ < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun x => ?_)) (hL.trans_lt ENNReal.ofReal_lt_top)
    rw [← ofReal_norm, Real.norm_eq_abs, abs_sub_comm]
  have hint : Integrable (fun x => p x - F.G n x) := ⟨hmeas, hfin⟩
  have hH : Integrable (fun x => Hs x - p x) := integrable_H_sub_Phi (cdrift F v * log n) hs
  have hm : ∫ x, (Hs x - p x) = cdrift F v * log n := integral_H_sub_Phi _ hs
  have e : F.eG (F.G n) = (∫ x, (Hs x - p x)) + ∫ x, (p x - F.G n x) := by
    rw [← integral_add hH hint]; unfold Sqrt.IncFamily.eG; rw [G0_eq_Hs]
    congr 1; funext x; ring
  rw [e, hm, add_sub_cancel_left]
  refine (abs_integral_le_integral_abs).trans ?_
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun x => abs_nonneg _)
    hint.abs.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (abs_nonneg C)
    (le_trans (le_of_eq (lintegral_congr fun x => ?_)) hL)
  rw [abs_sub_comm]

end Bounded

end CausalSpectrum.LogGauss

namespace CausalSpectrum.Kernel
open LogGauss

variable (κ : Kernel)

/-- **Corollary (bounded remainder for the seed entropy).** Under the hypotheses of the sharp
law, `|C_n - nh - c ln n| ≤ K` and `|L_n - nh - c ln n| ≤ K` for every `n ≥ 1`, with
`c = (κ₊ - κ₋)/(3v√(2πe))`. -/
theorem cost_bounded {h v : ℝ} (hh : κ.EqualEntropy h) (hv : 0 < v)
    (hσ : ∀ a, (κ.fam h).sig2 a = v) :
    ∃ K, ∀ n : ℕ, 1 ≤ n →
      |κ.costBits n - n * h - (kmax (κ.fam h) - kmin (κ.fam h)) / (3 * v * √(2 * π * exp 1)) *
          log n| ≤ K ∧
      |envelopeMean (κ.rounds n) - n * h -
          (kmax (κ.fam h) - kmin (κ.fam h)) / (3 * v * √(2 * π * exp 1)) * log n| ≤ K := by
  obtain ⟨C, hC⟩ := bounded_mean (κ.fam h) v (κ.fam_centered hh) hv hσ
  refine ⟨|C| + shannonOverhead, fun n hn => ?_⟩
  have hso : 0 ≤ shannonOverhead := by unfold shannonOverhead; positivity
  rw [← cdrift_eq (κ.fam h) v hv]
  have e := κ.envelope_sub_eq_eG hh hn
  have hm := (hC n hn).trans (le_abs_self C)
  obtain ⟨s1, s2⟩ := κ.costBits_sandwich n
  rw [← e] at hm
  constructor
  · rw [abs_le] at hm ⊢
    constructor <;> linarith
  · linarith

end CausalSpectrum.Kernel

namespace CausalSpectrum.Kernel.LogPair
open LogGauss

/-- **The dyadic pair, bounded remainder.** For every `n ≥ 1`, `C_n = L_n` and
`|C_n - 7n/2 - coeff · ln n| ≤ K`, with `coeff = 2/(3√(2πe))`. -/
theorem cost_bounded :
    ∃ K, ∀ n : ℕ, 1 ≤ n →
      κ.costBits n = envelopeMean (κ.rounds n) ∧
      |κ.costBits n - n * (7 / 2) - coeff * log n| ≤ K := by
  obtain ⟨C, hC⟩ := κ.cost_bounded equalEntropy (by norm_num : (0:ℝ) < 3 / 4) sig2_eq
  refine ⟨C, fun n hn => ⟨κ.cost_eq_envelope_of_dyadic isDyadic n, ?_⟩⟩
  have := (hC n hn).1
  rw [kmax_eq, kmin_eq] at this
  exact this

end CausalSpectrum.Kernel.LogPair

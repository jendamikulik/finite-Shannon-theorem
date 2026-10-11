/-
Upper bounds in the moment classification at equal entropy.

With the smoothing `Ψ = Ψ_6` of width `A = 6a`, the defects `R_{a,r} = (E_a - E_{j₀})(μ₀^r * Ψ)`
are controlled by the Taylor bound and the total-variation decay:
`∫|R_{a,r}| ≲ tv(μ₀^r Δ^{m-1})`, `∫|R'_{a,r}| ≲ tv(μ₀^r Δ^m)` when the moments of order `< m`
agree. Feeding this into the width recursion gives `L_n - n h = O(log n)` when all variances
agree, and `O(1)` when the third moments agree as well.
-/
import CausalSeed.MomentWidth

noncomputable section
open Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum.Sqrt.Decay
open AddMonoidAlgebra

variable {a : ℝ}

/-- The chain `f_i = act (c Δ^i) Ψ_{K-i}`: the `i`-th derivative of `act c Ψ_K`. -/
def chain (a : ℝ) (c : Meas) (K i : ℕ) : ℝ → ℝ := act (c * Dif a ^ i) (Psi a (K - i))

theorem chain_deriv (ha : 0 < a) (c : Meas) (K : ℕ) {i : ℕ} (hi : i + 2 ≤ K) (x : ℝ) :
    HasDerivAt (chain a c K i) (chain a c K (i + 1) x) x := by
  obtain ⟨k, hk⟩ : ∃ k, K - i = k + 2 := ⟨K - i - 2, by omega⟩
  have hk' : K - (i + 1) = k + 1 := by omega
  unfold chain
  rw [hk, hk', pow_succ, ← mul_assoc, act_mul]
  exact hasDerivAt_act _ (hasDerivAt_Psi ha k) x

theorem chain_cont (ha : 0 < a) (c : Meas) (K : ℕ) {i : ℕ} (hi : i + 1 ≤ K) :
    Continuous (chain a c K i) := by
  obtain ⟨k, hk⟩ : ∃ k, K - i = k + 1 := ⟨K - i - 1, by omega⟩
  unfold chain; rw [hk]; exact continuous_act _ (continuous_Psi_succ ha k)

theorem chain_lintegral (ha : 0 < a) (c : Meas) (K : ℕ) {i : ℕ} (hi : 1 ≤ i) (hiK : i ≤ K) :
    ∫⁻ x, ‖chain a c K i x‖ₑ ≤ ENNReal.ofReal (tv (c * Dif a ^ (i - 1))) * ENNReal.ofReal ((K - i : ℕ) + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
  have e : chain a c K (j + 1) = act (c * Dif a ^ j) (act (Dif a) (Psi a (K - (j + 1)))) := by
    funext x; unfold chain; rw [pow_succ, ← mul_assoc, act_mul]
  rw [e, Nat.add_sub_cancel]
  refine (lintegral_act_le _ (measurable_act _ (measurable_Psi ha _))).trans ?_
  gcongr
  exact lintegral_act_Dif_Psi_le ha _

theorem chain_zero (c : Meas) (K : ℕ) : chain a c K 0 = act c (Psi a K) := by
  unfold chain; simp

theorem tendsto_act_atBot (c : Meas) {g : ℝ → ℝ} {T : ℝ} (hg : ∀ y, y < T → g y = 0) :
    Tendsto (act c g) atBot (𝓝 0) := by
  refine tendsto_const_nhds.congr' ?_
  rw [EventuallyEq, eventually_atBot]
  refine ⟨T - 1 - ∑ z ∈ c.coeff.support, |z|, fun x hx => ?_⟩
  rw [act_eq_sum]
  symm
  refine Finset.sum_eq_zero fun z hz => ?_
  have : |z| ≤ ∑ z ∈ c.coeff.support, |z| :=
    Finset.single_le_sum (f := fun z => |z|) (fun _ _ => abs_nonneg _) hz
  rw [hg _ (by linarith [neg_abs_le z]), mul_zero]

theorem integrable_chain (ha : 0 < a) (c : Meas) (K : ℕ) {i : ℕ} (hi : 1 ≤ i) (hiK : i + 1 ≤ K) :
    Integrable (chain a c K i) := by
  refine ⟨(chain_cont ha c K hiK).aestronglyMeasurable, ?_⟩
  exact lt_of_le_of_lt (chain_lintegral ha c K hi (by omega)) (ENNReal.mul_lt_top (by simp) (by simp))

/-! ## Total variation of `μ^r Δ^q` -/

theorem tv_mul_Dif_pow_le (ha : 0 < a) (c : Meas) (q : ℕ) :
    tv (c * Dif a ^ q) ≤ tv c * (1 / a) ^ q :=
  (tv_mul_le _ _).trans (mul_le_mul_of_nonneg_left ((tv_pow_le _ _).trans
    (pow_le_pow_left₀ (tv_nonneg _) (tv_Dif ha) q)) (tv_nonneg _))

theorem tv_Dif_scale (b : ℝ) (hb : 0 < b) {L : ℕ} (hL : 0 < L) (q : ℕ) (X : Meas) :
    tv (X * Dif (L * b) ^ q) ≤ (1 / (2 * b)) ^ q * tv (dB b ^ q * X) := by
  rw [Dif, smul_pow, mul_smul_comm, tv_smul, abs_of_nonneg (by positivity), mul_comm X]
  have := tv_dB_scale_pow b L q X
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  calc (1 / (2 * (L * b))) ^ q * tv (dB (L * b) ^ q * X)
      ≤ (1 / (2 * (L * b))) ^ q * ((L : ℝ) ^ q * tv (dB b ^ q * X)) := by gcongr
    _ = (1 / (2 * b)) ^ q * tv (dB b ^ q * X) := by
        rw [← mul_assoc, ← mul_pow]; congr 2; field_simp

end CausalSpectrum.Sqrt.Decay

namespace CausalSpectrum.Sqrt.IncFamily
open Decay AddMonoidAlgebra
variable (F : IncFamily)

/-! ## `e(G_n) ≤ W_n` -/

theorem polE_G0_eq : ∀ (n : ℕ) (π : F.APol n) (x : ℝ),
    (x < -(n * F.M) → F.polE n π (F.G 0) x = 0) ∧ (n * F.M ≤ x → F.polE n π (F.G 0) x = 1)
  | 0, _, x => by
    simp only [polE, G, Nat.cast_zero, zero_mul, neg_zero]
    constructor <;> intro h <;> simp [h, not_le.2]
  | n + 1, π, x => by
    constructor
    · intro hx
      refine Finset.sum_eq_zero fun y _ => ?_
      have := F.abs_X_le π.1 y
      rw [((polE_G0_eq n (π.2 y) _).1 (by push_cast at hx; linarith [neg_abs_le (F.X π.1 y)])), mul_zero]
    · intro hx
      have : ∀ y, F.polE n (π.2 y) (F.G 0) (x - F.X π.1 y) = 1 := fun y => by
        have := F.abs_X_le π.1 y
        exact (polE_G0_eq n (π.2 y) _).2 (by push_cast at hx; linarith [le_abs_self (F.X π.1 y)])
      simp only [polE, this, mul_one, F.Psum]

theorem integrable_G0_sub_polE (n : ℕ) (π : F.APol n) :
    Integrable fun x => F.G 0 x - F.polE n π (F.G 0) x := by
  refine Integrable.mono' (g := (Icc (-(n * F.M)) (n * F.M)).indicator fun _ => (1:ℝ))
    ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const (by simp) (by simp)))
    ((F.measurable_G 0).sub (F.measurable_polE (F.measurable_G 0) n π)).aestronglyMeasurable
    (ae_of_all _ fun x => ?_)
  have hnM : 0 ≤ (n : ℝ) * F.M := mul_nonneg (Nat.cast_nonneg n) F.M_nonneg
  have b0 := F.G0_bounds x
  have bn := F.polE_bounds F.G0_bounds n π x
  rw [Real.norm_eq_abs]
  by_cases hx : x ∈ Icc (-(n * F.M)) (n * F.M)
  · rw [indicator_of_mem hx]; rw [abs_le]; constructor <;> linarith [b0.1, b0.2, bn.1, bn.2]
  · rw [indicator_of_notMem hx]
    simp only [mem_Icc, not_and_or, not_le] at hx
    rcases hx with hx | hx
    · rw [(F.polE_G0_eq n π x).1 hx, G0_eq, indicator_of_notMem (by simp; linarith)]; simp
    · rw [(F.polE_G0_eq n π x).2 hx.le, G0_eq, indicator_of_mem (by simp; linarith)]; simp

/-- `e(E_j f) = e(f)` for centered actions. -/
theorem eG_expect_gen (hc : F.Centered) (j) {f : ℝ → ℝ} (hf : Integrable fun x => F.G 0 x - f x) :
    F.eG (F.expect j f) = F.eG f := by
  have hsub : ∀ x, F.G 0 x - F.expect j f x =
      ∑ y, F.P j y * (-step (F.X j y) x + (F.G 0 (x - F.X j y) - f (x - F.X j y))) := fun x => by
    have : F.G 0 x = ∑ y, F.P j y * F.G 0 x := by rw [← Finset.sum_mul, F.Psum j, one_mul]
    rw [expect, this, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [← F.G0_sub_shift (F.X j y) x]; ring
  simp only [eG]
  simp_rw [hsub]
  have hi : ∀ y, Integrable fun x => F.P j y * (-step (F.X j y) x + (F.G 0 (x - F.X j y) - f (x - F.X j y))) :=
    fun y => Integrable.const_mul ((integrable_step _).neg.add (hf.comp_sub_right _)) _
  rw [integral_finsetSum _ fun y _ => hi y]
  simp only [integral_const_mul]
  have : ∀ y, ∫ x, (-step (F.X j y) x + (F.G 0 (x - F.X j y) - f (x - F.X j y))) =
      F.X j y + ∫ x, (F.G 0 x - f x) := fun y => by
    have i1 : Integrable (fun x => -step (F.X j y) x) := (integrable_step _).neg
    have i2 : Integrable (fun x => F.G 0 (x - F.X j y) - f (x - F.X j y)) := hf.comp_sub_right _
    rw [integral_add i1 i2, integral_neg, integral_step, neg_neg,
      integral_sub_right_eq_self (fun x => F.G 0 x - f x)]
  simp only [this, mul_add, Finset.sum_add_distrib, hc j, zero_add]
  rw [← Finset.sum_mul, F.Psum j, one_mul]

theorem eG_refPol (hc : F.Centered) (j₀) : ∀ n, F.eG (F.polE n (F.refPol j₀ n) (F.G 0)) = 0
  | 0 => F.eG_zero
  | n + 1 => by
    have e : F.polE (n + 1) (F.refPol j₀ (n + 1)) (F.G 0) = F.expect j₀ (F.polE n (F.refPol j₀ n) (F.G 0)) :=
      rfl
    rw [e, F.eG_expect_gen hc j₀ (F.integrable_G0_sub_polE n _), eG_refPol hc j₀ n]

/-- **`e(G_n) ≤ W_n`.** -/
theorem ofReal_eG_le_Wint (hc : F.Centered) (j₀ : Fin F.nA) (n : ℕ) :
    ENNReal.ofReal (F.eG (F.G n)) ≤ F.Wint n := by
  have i1 := F.integrable_G0_sub_polE n (F.refPol j₀ n)
  have i2 := F.integrable_G0_sub_G n
  have e : F.eG (F.G n) = ∫ x, (F.polE n (F.refPol j₀ n) (F.G 0) x - F.G n x) := by
    have := F.eG_refPol hc j₀ n
    simp only [eG] at this ⊢
    rw [show (fun x => F.polE n (F.refPol j₀ n) (F.G 0) x - F.G n x) =
      fun x => (F.G 0 x - F.G n x) - (F.G 0 x - F.polE n (F.refPol j₀ n) (F.G 0) x) by
        funext x; ring, integral_sub i2 i1, this, sub_zero]
  rw [e]
  rw [ofReal_integral_eq_lintegral_ofReal (i2.sub i1 |>.congr (ae_of_all _ fun x => by
    simp only [Pi.sub_apply]; ring)) (ae_of_all _ fun x => sub_nonneg.2 (F.G_le_polE n _ x))]
  refine lintegral_mono fun x => ENNReal.ofReal_le_ofReal ?_
  simp only [Wd]
  linarith [F.polE_le_U (F.G 0) n (F.refPol j₀ n) x]


/-! ## The smoothed width data -/

theorem integrable_act (c : Meas) {g : ℝ → ℝ} (hg : Integrable g) : Integrable (act c g) := by
  rw [act_fun]
  exact integrable_finsetSum _ fun z _ => (hg.comp_sub_right z).const_mul _

theorem expect_fun (j) (g : ℝ → ℝ) : F.expect j g = act (F.measOf j) g :=
  funext fun x => F.expect_eq_act j g x

variable {a : ℝ}

/-- The width data for `Ψ = Ψ_6`, `A = 6a`. -/
def wdata (ha : 0 < a) (j₀ : Fin F.nA) : F.WidthData where
  j₀ := j₀
  Ψ := Psi a 6
  A := 6 * a
  hA := by positivity
  hΨ := fun x => ⟨Psi_nonneg ha 6 x, Psi_le_one ha 6 x⟩
  hΨm := measurable_Psi ha 6
  hΨ0 := fun x hx => Psi_eq_zero ha (by push_cast; linarith)
  hΨ1 := fun x hx => Psi_eq_one ha (by push_cast; linarith)
  R' := fun b r x => F.expect b (chain a (F.measOf j₀ ^ r) 6 1) x - F.expect j₀ (chain a (F.measOf j₀ ^ r) 6 1) x
  hR := fun b r y => by
    have h1 := hasDerivAt_act (F.measOf b) (chain_deriv (i := 0) ha (F.measOf j₀ ^ r) 6 (by norm_num)) y
    have h2 := hasDerivAt_act (F.measOf j₀) (chain_deriv (i := 0) ha (F.measOf j₀ ^ r) 6 (by norm_num)) y
    rw [chain_zero] at h1 h2
    simp only [F.expect_fun]
    exact h1.sub h2
  hR'c := fun b r => by
    rw [F.expect_fun, F.expect_fun]
    exact (continuous_act _ (chain_cont ha _ 6 (by norm_num))).sub
      (continuous_act _ (chain_cont ha _ 6 (by norm_num)))
  hR'i := fun b r => by
    rw [F.expect_fun, F.expect_fun]
    exact (integrable_act _ (integrable_chain ha _ 6 le_rfl (by norm_num))).sub
      (integrable_act _ (integrable_chain ha _ 6 le_rfl (by norm_num)))
  hlim := fun b r => by
    rw [F.expect_fun, F.expect_fun]
    have hz : ∀ y, y < -(6 * a) → Psi a 6 y = 0 := fun y hy => Psi_eq_zero ha (by push_cast; linarith)
    have e1 : act (F.measOf b) (act (F.measOf j₀ ^ r) (Psi a 6)) = act (F.measOf b * F.measOf j₀ ^ r) (Psi a 6) :=
      funext fun x => (act_mul _ _ _ x).symm
    have e2 : act (F.measOf j₀) (act (F.measOf j₀ ^ r) (Psi a 6)) = act (F.measOf j₀ * F.measOf j₀ ^ r) (Psi a 6) :=
      funext fun x => (act_mul _ _ _ x).symm
    rw [e1, e2]
    simpa using (tendsto_act_atBot _ hz).sub (tendsto_act_atBot _ hz)

theorem wdata_Rf (ha : 0 < a) (j₀) (b : Fin F.nA) (r : ℕ) :
    (F.wdata ha j₀).Rf b r = fun x => F.expect b (chain a (F.measOf j₀ ^ r) 6 0) x -
      F.expect j₀ (chain a (F.measOf j₀ ^ r) 6 0) x := by
  funext x; simp only [WidthData.Rf, wdata, chain_zero]

/-- `Σ_b (E|X_b|^m + E|X_{j₀}|^m)`. -/
def amomSum (j₀ : Fin F.nA) (m : ℕ) : ℝ := ∑ b, (F.amom b m + F.amom j₀ m)

theorem amomSum_nonneg (j₀) (m : ℕ) : 0 ≤ F.amomSum j₀ m :=
  Finset.sum_nonneg fun b _ => add_nonneg (F.amom_nonneg _ _) (F.amom_nonneg _ _)

/-- **Defect bound.** If all actions share the moments of orders `< m` (`1 ≤ m ≤ 4`), then
`α_r ≤ Σ(E|X|^m) · 7 · tv(μ₀^r Δ^{m-1})`. -/
theorem wdata_α_le (ha : 0 < a) (j₀) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 4)
    (hmom : ∀ b, ∀ i < m, F.mom b i = F.mom j₀ i) (r : ℕ) :
    (F.wdata ha j₀).α r ≤ ENNReal.ofReal (F.amomSum j₀ m * 7 * tv (F.measOf j₀ ^ r * Dif a ^ (m - 1))) := by
  have hb : ∀ b, ∫⁻ x, ‖(F.wdata ha j₀).Rf b r x‖ₑ ≤
      ENNReal.ofReal (F.amom b m + F.amom j₀ m) * ENNReal.ofReal (tv (F.measOf j₀ ^ r * Dif a ^ (m - 1)) * 7) := by
    intro b
    rw [F.wdata_Rf]
    refine (F.lintegral_expect_sub_le m (hmom b) (chain a (F.measOf j₀ ^ r) 6)
      (fun i hi x => chain_deriv ha _ 6 (by omega) x) (chain_cont ha _ 6 (by omega))).trans ?_
    gcongr
    refine (chain_lintegral ha _ 6 hm1 (by omega)).trans ?_
    rw [← ENNReal.ofReal_mul (tv_nonneg _)]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (tv_nonneg _))
    have : ((6 - m : ℕ) : ℝ) ≤ 6 := by exact_mod_cast Nat.sub_le 6 m
    linarith
  refine (Finset.sum_le_sum fun b _ => hb b).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun b _ =>
    add_nonneg (F.amom_nonneg _ _) (F.amom_nonneg _ _), ← ENNReal.ofReal_mul (Finset.sum_nonneg fun b _ =>
    add_nonneg (F.amom_nonneg _ _) (F.amom_nonneg _ _))]
  congr 1; simp only [amomSum]; ring

/-- **Derivative-defect bound.** Same hypotheses: `β_r ≤ Σ(E|X|^m) · 7 · tv(μ₀^r Δ^m)`. -/
theorem wdata_β_le (ha : 0 < a) (j₀) {m : ℕ} (hm : m ≤ 4)
    (hmom : ∀ b, ∀ i < m, F.mom b i = F.mom j₀ i) (r : ℕ) :
    (F.wdata ha j₀).β r ≤ ENNReal.ofReal (F.amomSum j₀ m * 7 * tv (F.measOf j₀ ^ r * Dif a ^ m)) := by
  have hb : ∀ b, ∫⁻ x, ‖(F.wdata ha j₀).R' b r x‖ₑ ≤
      ENNReal.ofReal (F.amom b m + F.amom j₀ m) * ENNReal.ofReal (tv (F.measOf j₀ ^ r * Dif a ^ m) * 7) := by
    intro b
    show ∫⁻ x, ‖F.expect b (chain a (F.measOf j₀ ^ r) 6 (0 + 1)) x -
      F.expect j₀ (chain a (F.measOf j₀ ^ r) 6 (0 + 1)) x‖ₑ ≤ _
    refine (F.lintegral_expect_sub_le m (hmom b) (fun i => chain a (F.measOf j₀ ^ r) 6 (i + 1))
      (fun i hi x => chain_deriv ha _ 6 (by omega) x) (chain_cont ha _ 6 (by omega))).trans ?_
    gcongr
    refine (chain_lintegral ha _ 6 (by omega) (by omega)).trans ?_
    rw [← ENNReal.ofReal_mul (tv_nonneg _), Nat.add_sub_cancel]
    refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (tv_nonneg _))
    have : ((6 - (m + 1) : ℕ) : ℝ) ≤ 6 := by exact_mod_cast Nat.sub_le 6 _
    linarith
  refine (Finset.sum_le_sum fun b _ => hb b).trans (le_of_eq ?_)
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun b _ =>
    add_nonneg (F.amom_nonneg _ _) (F.amom_nonneg _ _), ← ENNReal.ofReal_mul (Finset.sum_nonneg fun b _ =>
    add_nonneg (F.amom_nonneg _ _) (F.amom_nonneg _ _))]
  congr 1; simp only [amomSum]; ring

end CausalSpectrum.Sqrt.IncFamily

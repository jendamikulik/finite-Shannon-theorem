/-
Uniform-noise smoothing and the derivative chain of smoothed reference walks.

`act c g x = Σ_z c_z g(x - z)` is the action of a finitely supported signed measure on a
function (convolution). `Ψ k` is the distribution function of the sum of `k` independent
uniform variables on `[-a, a]`; its derivative is `(Ψ (k-1)(x+a) - Ψ (k-1)(x-a))/(2a)`, so the
`i`-th derivative of `act c (Ψ k)` is `act (c Δ^i) (Ψ (k-i))` with `Δ = (δ_{-a} - δ_a)/(2a)`.
-/
import CausalSeed.MomentTaylor
import CausalSeed.MomentDecay

noncomputable section
open Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum.Sqrt.Decay
open AddMonoidAlgebra

/-- Convolution action `act c g x = Σ_z c_z g (x - z)`. -/
def act (c : Meas) (g : ℝ → ℝ) (x : ℝ) : ℝ := c.coeff.sum fun z w => w * g (x - z)

theorem act_zero (g : ℝ → ℝ) (x : ℝ) : act 0 g x = 0 := by simp [act]

theorem act_add (c d : Meas) (g : ℝ → ℝ) (x : ℝ) : act (c + d) g x = act c g x + act d g x := by
  simp only [act, coeff_add]
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem act_single (z w : ℝ) (g : ℝ → ℝ) (x : ℝ) : act (single z w) g x = w * g (x - z) := by
  simp only [act, coeff_single]
  exact Finsupp.sum_single_index (zero_mul _)

theorem act_smul (r : ℝ) (c : Meas) (g : ℝ → ℝ) (x : ℝ) : act (r • c) g x = r * act c g x := by
  induction c using AddMonoidAlgebra.induction_linear with
  | zero => simp [act_zero]
  | add c d hc hd => rw [smul_add, act_add, act_add, hc, hd, mul_add]
  | single z w =>
    rw [show r • (single z w : Meas) = single z (r * w) by
      apply AddMonoidAlgebra.coeff_injective; simp [coeff_single], act_single, act_single]; ring

theorem act_neg (c : Meas) (g : ℝ → ℝ) (x : ℝ) : act (-c) g x = -act c g x := by
  rw [show -c = (-1 : ℝ) • c by simp, act_smul]; ring

theorem act_sub (c d : Meas) (g : ℝ → ℝ) (x : ℝ) : act (c - d) g x = act c g x - act d g x := by
  rw [sub_eq_add_neg, act_add, act_neg]; ring

theorem act_sum {ι : Type*} (s : Finset ι) (f : ι → Meas) (g : ℝ → ℝ) (x : ℝ) :
    act (∑ i ∈ s, f i) g x = ∑ i ∈ s, act (f i) g x := by
  induction s using Finset.induction_on with
  | empty => simp [act_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, act_add, ih]

theorem act_mul (c d : Meas) (g : ℝ → ℝ) (x : ℝ) : act (c * d) g x = act c (act d g) x := by
  induction c using AddMonoidAlgebra.induction_linear generalizing x with
  | zero => simp [act_zero]
  | add c c' hc hc' => rw [add_mul, act_add, act_add, hc, hc']
  | single z w =>
    rw [act_single]
    induction d using AddMonoidAlgebra.induction_linear generalizing x with
    | zero => simp [act_zero]
    | add d d' hd hd' => rw [mul_add, act_add, hd, hd', act_add, mul_add]
    | single z' w' =>
      rw [single_mul_single, act_single, act_single, show x - (z + z') = x - z - z' by ring]; ring

theorem act_one (g : ℝ → ℝ) (x : ℝ) : act 1 g x = g x := by
  rw [AddMonoidAlgebra.one_def, act_single]; simp

theorem act_eq_sum (c : Meas) (g : ℝ → ℝ) (x : ℝ) :
    act c g x = ∑ z ∈ c.coeff.support, c.coeff z * g (x - z) := rfl

/-- `act c` commutes with translations. -/
theorem act_translate (c : Meas) (g : ℝ → ℝ) (t x : ℝ) :
    act c (fun y => g (y + t)) x = act c g (x + t) := by
  simp only [act_eq_sum]; exact Finset.sum_congr rfl fun z _ => by ring_nf

theorem act_fun (c : Meas) (g : ℝ → ℝ) :
    act c g = fun x => ∑ z ∈ c.coeff.support, c.coeff z * g (x - z) := rfl

theorem measurable_act (c : Meas) {g : ℝ → ℝ} (hg : Measurable g) : Measurable (act c g) := by
  rw [act_fun]
  exact Finset.measurable_sum _ fun z _ => (hg.comp (measurable_id.sub_const z)).const_mul _

theorem continuous_act (c : Meas) {g : ℝ → ℝ} (hg : Continuous g) : Continuous (act c g) := by
  rw [act_fun]
  exact continuous_finsetSum _ fun z _ => (hg.comp (continuous_id.sub continuous_const)).const_mul _

theorem hasDerivAt_act (c : Meas) {g g' : ℝ → ℝ} (hg : ∀ x, HasDerivAt g (g' x) x) (x : ℝ) :
    HasDerivAt (act c g) (act c g' x) x := by
  rw [act_fun, act_eq_sum]
  refine HasDerivAt.fun_sum fun z _ => ?_
  exact ((hg (x - z)).comp x ((hasDerivAt_id x).sub_const z)).const_mul _ |>.congr_deriv (by simp)

/-- **`∫ |act c g| ≤ tv c ∫ |g|`.** -/
theorem lintegral_act_le (c : Meas) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫⁻ x, ‖act c g x‖ₑ ≤ ENNReal.ofReal (tv c) * ∫⁻ x, ‖g x‖ₑ := by
  calc ∫⁻ x, ‖act c g x‖ₑ ≤ ∫⁻ x, ∑ z ∈ c.coeff.support, ENNReal.ofReal |c.coeff z| * ‖g (x - z)‖ₑ := by
        refine lintegral_mono fun x => (enorm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [enorm_mul, Real.enorm_eq_ofReal_abs]
    _ = ∑ z ∈ c.coeff.support, ENNReal.ofReal |c.coeff z| * ∫⁻ x, ‖g x‖ₑ := by
        have hm : ∀ z : ℝ, Measurable fun x => ‖g (x - z)‖ₑ := fun z =>
          (hg.comp (measurable_id.sub_const z)).enorm
        rw [lintegral_finsetSum _ fun z _ => (hm z).const_mul _]
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [lintegral_const_mul _ (hm z),
          lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) z]
    _ = ENNReal.ofReal (tv c) * ∫⁻ x, ‖g x‖ₑ := by
        rw [← Finset.sum_mul, tv, Finsupp.sum, ENNReal.ofReal_sum_of_nonneg fun _ _ => abs_nonneg _]


/-! ## Uniform splines -/

/-- `Ψ a k`: the distribution function of a sum of `k` independent uniforms on `[-a, a]`. -/
def Psi (a : ℝ) : ℕ → ℝ → ℝ
  | 0 => fun x => if 0 ≤ x then 1 else 0
  | k + 1 => fun x => (1 / (2 * a)) * ∫ t in (x - a)..(x + a), Psi a k t

variable {a : ℝ}

theorem Psi_succ (a : ℝ) (k : ℕ) (x : ℝ) :
    Psi a (k + 1) x = (1 / (2 * a)) * ∫ t in (x - a)..(x + a), Psi a k t := rfl

theorem Psi_shift (a : ℝ) (k : ℕ) (x : ℝ) :
    Psi a (k + 1) x = (1 / (2 * a)) * ∫ t in (-a)..a, Psi a k (t + x) := by
  rw [Psi_succ, intervalIntegral.integral_comp_add_right]; ring_nf

theorem Psi_props (ha : 0 < a) : ∀ k : ℕ, Monotone (Psi a k) ∧ (∀ x, 0 ≤ Psi a k x ∧ Psi a k x ≤ 1) ∧
    (∀ x, x < -(k * a) → Psi a k x = 0) ∧ (∀ x, k * a ≤ x → Psi a k x = 1)
  | 0 => by
    refine ⟨fun x y hxy => ?_, fun x => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Psi]; split_ifs <;> (try push_neg at *) <;> first | linarith | norm_num
    · simp only [Psi]; split_ifs <;> norm_num
    · simp only [Psi]; rw [ite_eq_right_iff.2 (fun h => absurd h (by simp at hx; linarith))]
    · simp only [Psi]; rw [if_pos (by simpa using hx)]
  | k + 1 => by
    obtain ⟨hm, hb, h0, h1⟩ := Psi_props ha k
    have hi : ∀ u v, IntervalIntegrable (Psi a k) volume u v := fun u v => hm.intervalIntegrable
    have h2a : 0 < 2 * a := by linarith
    refine ⟨fun x y hxy => ?_, fun x => ⟨?_, ?_⟩, fun x hx => ?_, fun x hx => ?_⟩
    · rw [Psi_shift, Psi_shift]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine intervalIntegral.integral_mono_on (by linarith) (Monotone.comp hm (monotone_id.add_const x)).intervalIntegrable
        (Monotone.comp hm (monotone_id.add_const y)).intervalIntegrable fun t _ => hm (by linarith)
    · rw [Psi_succ]
      exact mul_nonneg (by positivity) (intervalIntegral.integral_nonneg (by linarith) fun t _ => (hb t).1)
    · rw [Psi_succ]
      have : ∫ t in (x - a)..(x + a), Psi a k t ≤ ∫ t in (x - a)..(x + a), (1 : ℝ) :=
        intervalIntegral.integral_mono_on (by linarith) (hi _ _) intervalIntegrable_const fun t _ => (hb t).2
      rw [intervalIntegral.integral_const, smul_eq_mul, mul_one] at this
      rw [div_mul_eq_mul_div, one_mul, div_le_one h2a]; linarith
    · rw [Psi_succ]
      have : ∫ t in (x - a)..(x + a), Psi a k t = ∫ t in (x - a)..(x + a), (0 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => h0 t ?_
        rw [uIcc_of_le (by linarith)] at ht
        push_cast at hx; linarith [ht.2]
      rw [this]; simp
    · rw [Psi_succ]
      have : ∫ t in (x - a)..(x + a), Psi a k t = ∫ t in (x - a)..(x + a), (1 : ℝ) := by
        refine intervalIntegral.integral_congr fun t ht => h1 t ?_
        rw [uIcc_of_le (by linarith)] at ht
        push_cast at hx; linarith [ht.1]
      rw [this, intervalIntegral.integral_const, smul_eq_mul, mul_one]; field_simp; ring

theorem Psi_mono (ha : 0 < a) (k : ℕ) : Monotone (Psi a k) := (Psi_props ha k).1
theorem Psi_nonneg (ha : 0 < a) (k : ℕ) (x : ℝ) : 0 ≤ Psi a k x := ((Psi_props ha k).2.1 x).1
theorem Psi_le_one (ha : 0 < a) (k : ℕ) (x : ℝ) : Psi a k x ≤ 1 := ((Psi_props ha k).2.1 x).2
theorem Psi_eq_zero (ha : 0 < a) {k : ℕ} {x : ℝ} (hx : x < -(k * a)) : Psi a k x = 0 :=
  (Psi_props ha k).2.2.1 x hx
theorem Psi_eq_one (ha : 0 < a) {k : ℕ} {x : ℝ} (hx : k * a ≤ x) : Psi a k x = 1 :=
  (Psi_props ha k).2.2.2 x hx
theorem measurable_Psi (ha : 0 < a) (k : ℕ) : Measurable (Psi a k) := (Psi_mono ha k).measurable

theorem continuous_Psi_succ (ha : 0 < a) (k : ℕ) : Continuous (Psi a (k + 1)) := by
  have hi : ∀ u v, IntervalIntegrable (Psi a k) volume u v := fun u v => (Psi_mono ha k).intervalIntegrable
  have hp := intervalIntegral.continuous_primitive hi 0
  have e : Psi a (k + 1) = fun x => (1 / (2 * a)) *
      ((∫ t in (0 : ℝ)..(x + a), Psi a k t) - ∫ t in (0 : ℝ)..(x - a), Psi a k t) := by
    funext x; rw [Psi_succ, intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  rw [e]
  exact continuous_const.mul ((hp.comp (continuous_id.add continuous_const)).sub
    (hp.comp (continuous_id.sub continuous_const)))

/-- The difference quotient `Δ = (δ_{-a} - δ_a)/(2a)`. -/
def Dif (a : ℝ) : Meas := (1 / (2 * a)) • dB a

theorem act_Dif (g : ℝ → ℝ) (x : ℝ) : act (Dif a) g x = (1 / (2 * a)) * (g (x + a) - g (x - a)) := by
  rw [Dif, act_smul, dB, act_sub, act_single, act_single]; simp

theorem tv_Dif (ha : 0 < a) : tv (Dif a) ≤ 1 / a := by
  rw [Dif, tv_smul, abs_of_pos (by positivity)]
  calc 1 / (2 * a) * tv (dB a) ≤ 1 / (2 * a) * 2 := by gcongr; exact tv_dB a
    _ = 1 / a := by field_simp

theorem hasDerivAt_Psi (ha : 0 < a) (k : ℕ) (x : ℝ) :
    HasDerivAt (Psi a (k + 2)) (act (Dif a) (Psi a (k + 1)) x) x := by
  have hc := continuous_Psi_succ ha k
  have hi : ∀ u v, IntervalIntegrable (Psi a (k + 1)) volume u v := fun u v => hc.intervalIntegrable _ _
  have e : Psi a (k + 2) = fun x => (1 / (2 * a)) *
      ((∫ t in (0 : ℝ)..(x + a), Psi a (k + 1) t) - ∫ t in (0 : ℝ)..(x - a), Psi a (k + 1) t) := by
    funext x; rw [Psi_succ, intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
  rw [e, act_Dif]
  have d1 := ((hc.integral_hasStrictDerivAt 0 (x + a)).hasDerivAt).comp x ((hasDerivAt_id x).add_const a)
  have d2 := ((hc.integral_hasStrictDerivAt 0 (x - a)).hasDerivAt).comp x ((hasDerivAt_id x).sub_const a)
  simpa using (d1.sub d2).const_mul (1 / (2 * a))

/-- `|Δ Ψ_j| ≤ (2a)^{-1} 1_{[-(j+1)a, (j+1)a]}`, so `∫ |Δ Ψ_j| ≤ j + 1`. -/
theorem lintegral_act_Dif_Psi_le (ha : 0 < a) (j : ℕ) :
    ∫⁻ x, ‖act (Dif a) (Psi a j) x‖ₑ ≤ ENNReal.ofReal (j + 1) := by
  set S := Icc (-((j + 1) * a)) ((j + 1) * a)
  have hpt : ∀ x, ‖act (Dif a) (Psi a j) x‖ₑ ≤ S.indicator (fun _ => ENNReal.ofReal (1 / (2 * a))) x := by
    intro x
    rw [act_Dif]
    have hm := Psi_mono ha j
    have hd : 0 ≤ Psi a j (x + a) - Psi a j (x - a) := sub_nonneg.2 (hm (by linarith))
    have hd1 : Psi a j (x + a) - Psi a j (x - a) ≤ 1 := by
      linarith [Psi_le_one ha j (x + a), Psi_nonneg ha j (x - a)]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_of_nonneg (mul_nonneg (by positivity) hd)]
      calc 1 / (2 * a) * (Psi a j (x + a) - Psi a j (x - a)) ≤ 1 / (2 * a) * 1 := by gcongr
        _ = _ := mul_one _
    · rw [indicator_of_notMem hx]
      simp only [S, mem_Icc, not_and_or, not_le] at hx
      have : Psi a j (x + a) - Psi a j (x - a) = 0 := by
        rcases hx with hx | hx
        · rw [Psi_eq_zero ha (by linarith), Psi_eq_zero ha (by linarith)]; ring
        · rw [Psi_eq_one ha (by linarith), Psi_eq_one ha (by linarith)]; ring
      simp [this]
  refine (lintegral_mono hpt).trans (le_of_eq ?_)
  rw [lintegral_indicator measurableSet_Icc, setLIntegral_const, Real.volume_Icc,
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1; field_simp; ring

end CausalSpectrum.Sqrt.Decay

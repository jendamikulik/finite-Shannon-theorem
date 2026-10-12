/-
The maximal-entropy reduction.

Under exponential domination by an action of a set `S` of actions with common entropy `h`,
the causal cost of the full kernel has the same `√n` asymptotics as the kernel `κ.sub S`:
the leading term `n h`, the second-order coefficient `√(2/π) (a* - b*)` of the restricted
family, the `O(n^{1/4} log n)` remainder, and the logarithmic regime when `a* = b*`.
-/
import CausalSeed.MaxEntropy
import CausalSeed.SqrtGeneral
import CausalSeed.MomentAssembly
import CausalSeed.MomentLower

noncomputable section
open Classical Filter Topology
namespace CausalSpectrum.Kernel

variable {κ : Kernel} {S : Finset (Fin κ.nA)} (hS : S.Nonempty) {i₀ : Fin κ.nA}
  {θ M : ℝ}

/-- `B_n ≤ D₀ + log n / θ` for `n ≥ 1`. -/
theorem Bn_le (hθ : 0 < θ) (hM0 : 0 ≤ M) {n : ℕ} (hn : 1 ≤ n) :
    (1 + Real.log (1 + θ * (n * M))) / θ ≤
      (1 + Real.log (1 + θ * M)) / θ + Real.log n / θ := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : 0 < 1 + θ * M := by positivity
  have h2 : 1 + θ * (n * M) ≤ n * (1 + θ * M) := by nlinarith [mul_nonneg hθ.le hM0]
  have h3 : Real.log (1 + θ * (n * M)) ≤ Real.log n + Real.log (1 + θ * M) := by
    rw [← Real.log_mul (by positivity) h1.ne']
    exact Real.log_le_log (by positivity) h2
  rw [← add_div]; exact div_le_div_of_nonneg_right (by linarith) hθ.le

theorem log_div_sqrt_tendsto :
    Tendsto (fun n : ℕ => Real.log n / Real.sqrt n) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).tendsto_div_nhds_zero
  have h' := h.comp tendsto_natCast_atTop_atTop
  refine h'.congr fun n => ?_
  simp [Real.sqrt_eq_rpow]

/-- The comparison error is `o(√n)`. -/
theorem gap_div_sqrt_tendsto (hθ : 0 < θ) (hM0 : 0 ≤ M) {d : ℕ → ℝ}
    (hd : ∀ n, 1 ≤ n → 0 ≤ d n ∧ d n ≤ (1 + Real.log (1 + θ * (n * M))) / θ + shannonOverhead) :
    Tendsto (fun n : ℕ => d n / Real.sqrt n) atTop (𝓝 0) := by
  set D := (1 + Real.log (1 + θ * M)) / θ + shannonOverhead
  have hup : Tendsto (fun n : ℕ => D / Real.sqrt n + (1 / θ) * (Real.log n / Real.sqrt n))
      atTop (𝓝 0) := by
    have hs : Tendsto (fun n : ℕ => D / Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop
        ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
    simpa using hs.add (log_div_sqrt_tendsto.const_mul (1 / θ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_nonneg (hd n hn).1 (Real.sqrt_nonneg _)
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
    have := (hd n hn).2.trans (by linarith [Bn_le hθ hM0 hn] :
      (1 + Real.log (1 + θ * (n * M))) / θ + shannonOverhead ≤ D + Real.log n / θ)
    rw [div_le_iff₀ hsq]
    calc d n ≤ D + Real.log n / θ := this
      _ = _ := by field_simp

variable (hi₀ : i₀ ∈ S) (hθ : 0 < θ) (hdom : Dominates S i₀ θ) (hM0 : 0 ≤ M)
  (hM : ∀ a y, infoMass (κ.K a y) ≤ M)
include hi₀ hθ hdom hM0 hM

/-- **Maximal-entropy reduction (cost).** If the actions of `S` share the entropy `h`, then
`(C_n(κ) - n h)/√n → √(2/π) (a* - b*)`, computed from `κ.sub S`. -/
theorem cost_tendsto_maxEntropy {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h) :
    Tendsto (fun n : ℕ => (κ.costBits n - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff ((κ.sub S hS).fam h).sA ((κ.sub S hS).fam h).sB)) := by
  have hd := gap_div_sqrt_tendsto hθ hM0
    (d := fun n => κ.costBits n - (κ.sub S hS).costBits n)
    (fun n _ => κ.costBits_compare hS hi₀ hθ hdom hM0 hM n)
  have := ((κ.sub S hS).cost_tendsto hh).add hd
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring

/-- **Maximal-entropy reduction (envelope mean).** -/
theorem envelope_tendsto_maxEntropy {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h) :
    Tendsto (fun n : ℕ => (envelopeMean (κ.rounds n) - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff ((κ.sub S hS).fam h).sA ((κ.sub S hS).fam h).sB)) := by
  have hd := gap_div_sqrt_tendsto hθ hM0
    (d := fun n => envelopeMean (κ.rounds n) - envelopeMean ((κ.sub S hS).rounds n))
    (fun n _ => by
      have := κ.envelopeMean_compare hS hi₀ hθ hdom hM0 hM n
      have hc : (0 : ℝ) ≤ shannonOverhead := by unfold shannonOverhead; positivity
      exact ⟨by linarith [this.1], by linarith [this.2]⟩)
  have := ((κ.sub S hS).envelope_tendsto hh).add hd
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring

/-- **Maximal-entropy reduction (greedy seed).** Any seed whose Shannon entropy lies within
`c⋆` above the envelope mean of `κ` has the same second-order limit. -/
theorem greedy_tendsto_maxEntropy {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h)
    (atoms : ∀ n, List (Atom (κ.rounds n)))
    (hlo : ∀ n, envelopeMean (κ.rounds n) ≤ seedShannon (atoms n))
    (hhi : ∀ n, seedShannon (atoms n) ≤ envelopeMean (κ.rounds n) + shannonOverhead) :
    Tendsto (fun n : ℕ => (seedShannon (atoms n) - n * h) / Real.sqrt n) atTop
      (𝓝 (secondOrderCoeff ((κ.sub S hS).fam h).sA ((κ.sub S hS).fam h).sB)) := by
  have hd : Tendsto (fun n : ℕ =>
      (seedShannon (atoms n) - envelopeMean (κ.rounds n)) / Real.sqrt n) atTop (𝓝 0) :=
    gap_div_sqrt_tendsto hθ hM0 (fun n _ => ⟨by linarith [hlo n], by
      have : 0 ≤ (1 + Real.log (1 + θ * (n * M))) / θ := by
        apply div_nonneg _ hθ.le
        have : 0 ≤ Real.log (1 + θ * (n * M)) :=
          Real.log_nonneg (by nlinarith [mul_nonneg hθ.le (mul_nonneg (Nat.cast_nonneg n) hM0)])
        linarith
      linarith [hhi n]⟩)
  have := (envelope_tendsto_maxEntropy hS hi₀ hθ hdom hM0 hM hh).add hd
  rw [add_zero] at this
  refine this.congr fun n => ?_
  ring

/-- **Maximal-entropy reduction (rate).** With `b* > 0`, the remainder is `O(n^{1/4} log n)`. -/
theorem cost_rate_maxEntropy {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h)
    (hb : 0 < ((κ.sub S hS).fam h).sB) :
    ∃ K : ℝ, ∀ n : ℕ, 3 ≤ n →
      |κ.costBits n - n * h - secondOrderCoeff ((κ.sub S hS).fam h).sA
          ((κ.sub S hS).fam h).sB * Real.sqrt n| ≤
        K * (Real.sqrt (Real.sqrt n) * Real.log n) := by
  obtain ⟨K, hK⟩ := (κ.sub S hS).cost_rate hh hb
  set D := (1 + Real.log (1 + θ * M)) / θ + shannonOverhead
  have hc : (0 : ℝ) ≤ shannonOverhead := by unfold shannonOverhead; positivity
  have hD : 0 ≤ D := by
    have : 0 ≤ Real.log (1 + θ * M) := Real.log_nonneg (by nlinarith [mul_nonneg hθ.le hM0])
    have : 0 ≤ (1 + Real.log (1 + θ * M)) / θ := div_nonneg (by linarith) hθ.le
    linarith
  refine ⟨K + D + 1 / θ, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hcmp := κ.costBits_compare hS hi₀ hθ hdom hM0 hM n
  have hB := Bn_le hθ hM0 hn1
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn
    linarith [Real.exp_one_lt_d9]
  have hs : 1 ≤ Real.sqrt (Real.sqrt n) := by
    rw [Real.one_le_sqrt, Real.one_le_sqrt]; exact_mod_cast hn1
  set P := Real.sqrt (Real.sqrt n) * Real.log n
  have hP1 : 1 ≤ P := by nlinarith
  have hlP : Real.log n ≤ P := by nlinarith
  have hK0 := hK n hn
  have hθi : 0 < 1 / θ := by positivity
  rw [add_mul, add_mul]
  have e1 : Real.log n / θ ≤ 1 / θ * P := by
    rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_left hlP hθi.le
  have e2 : D ≤ D * P := le_mul_of_one_le_right hD hP1
  rw [abs_le] at hK0 ⊢
  constructor <;> nlinarith [hcmp.1, hcmp.2]

/-! ### No intermediate power-law regime -/

/-- If `a* > b*`, the excess cost is of exact order `√n`. -/
theorem excess_sqrt_order {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h)
    (hab : ((κ.sub S hS).fam h).sB < ((κ.sub S hS).fam h).sA) :
    ∃ c > 0, ∃ C, ∀ᶠ n : ℕ in atTop,
      c * Real.sqrt n ≤ κ.costBits n - n * h ∧ κ.costBits n - n * h ≤ C * Real.sqrt n := by
  set L := secondOrderCoeff ((κ.sub S hS).fam h).sA ((κ.sub S hS).fam h).sB
  have hL : 0 < L := by
    unfold L secondOrderCoeff
    exact mul_pos (Real.sqrt_pos.mpr (by positivity)) (by linarith)
  have ht := cost_tendsto_maxEntropy hS hi₀ hθ hdom hM0 hM hh
  refine ⟨L / 2, by positivity, 2 * L, ?_⟩
  filter_upwards [ht.eventually (Ioo_mem_nhds (by linarith : L / 2 < L)
    (by linarith : L < 2 * L)), eventually_ge_atTop 1] with n hn hn1
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn1)
  obtain ⟨h1, h2⟩ := hn
  rw [lt_div_iff₀ hsq] at h1; rw [div_lt_iff₀ hsq] at h2
  exact ⟨h1.le, h2.le⟩

/-- If `a* = b*` (all actions of `S` have the same surprisal variance) and one of them is
nondegenerate, the excess cost is `O(log n)`. -/
theorem excess_log_upper_maxEntropy {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h)
    {j₀ : Fin S.card} (hnd : ((κ.sub S hS).fam h).Nondeg j₀)
    (hσ : ∀ j, ((κ.sub S hS).fam h).sig2 j = ((κ.sub S hS).fam h).sig2 j₀) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → κ.costBits n - n * h ≤ C * (1 + Real.log n) := by
  obtain ⟨C, hC⟩ := (κ.sub S hS).excess_log_upper hh hnd hσ
  set D := (1 + Real.log (1 + θ * M)) / θ + shannonOverhead
  have hc : (0 : ℝ) ≤ shannonOverhead := by unfold shannonOverhead; positivity
  have hD : 0 ≤ D := by
    have : 0 ≤ Real.log (1 + θ * M) := Real.log_nonneg (by nlinarith [mul_nonneg hθ.le hM0])
    have : 0 ≤ (1 + Real.log (1 + θ * M)) / θ := div_nonneg (by linarith) hθ.le
    linarith
  refine ⟨|C| + shannonOverhead + D + 1 / θ, fun n hn => ?_⟩
  have h1 := (hC n hn).2
  have h2 := (κ.costBits_compare hS hi₀ hθ hdom hM0 hM n).2
  have h3 := Bn_le hθ hM0 hn
  have hl : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hθi : 0 < 1 / θ := by positivity
  have e1 : C * (1 + Real.log n) ≤ |C| * (1 + Real.log n) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  have e2 : Real.log n / θ ≤ 1 / θ * (1 + Real.log n) := by
    rw [div_eq_mul_one_div, mul_comm]; nlinarith
  nlinarith

/-- If `a* = b*` and two actions of `S` have different third centered surprisal moments, the
excess cost of the full kernel is of exact order `log n`. -/
theorem excess_log_theta_maxEntropy {h : ℝ} (hh : (κ.sub S hS).EqualEntropy h)
    (hσ : ∀ j k, ((κ.sub S hS).fam h).sig2 j = ((κ.sub S hS).fam h).sig2 k)
    {j k : Fin S.card} (h3 : ((κ.sub S hS).fam h).m3 j ≠ ((κ.sub S hS).fam h).m3 k) :
    ∃ c > 0, ∃ C, ∀ᶠ n : ℕ in atTop,
      c * Real.log n ≤ κ.costBits n - n * h ∧ κ.costBits n - n * h ≤ C * Real.log n := by
  obtain ⟨c, hc, C, hev⟩ := (κ.sub S hS).excess_log_theta hh hσ h3
  set D := (1 + Real.log (1 + θ * M)) / θ + shannonOverhead
  refine ⟨c, hc, C + D + 1 / θ, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 3] with n hn hn3
  have hn1 : 1 ≤ n := by omega
  have hcmp := κ.costBits_compare hS hi₀ hθ hdom hM0 hM n
  have hB := Bn_le hθ hM0 hn1
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith [Real.exp_one_lt_d9]
  have hθi : 0 < 1 / θ := by positivity
  have hD : 0 ≤ D := by
    have hc' : (0 : ℝ) ≤ shannonOverhead := by unfold shannonOverhead; positivity
    have : 0 ≤ Real.log (1 + θ * M) := Real.log_nonneg (by nlinarith [mul_nonneg hθ.le hM0])
    have : 0 ≤ (1 + Real.log (1 + θ * M)) / θ := div_nonneg (by linarith) hθ.le
    linarith
  have e2 : Real.log n / θ = 1 / θ * Real.log n := by ring
  obtain ⟨⟨-, -⟩, ⟨l2, u2⟩⟩ := hn
  constructor
  · linarith [hcmp.1]
  · nlinarith [hcmp.2]

end CausalSpectrum.Kernel

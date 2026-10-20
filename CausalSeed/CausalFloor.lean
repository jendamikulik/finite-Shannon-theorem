/-
The causal Shannon floor for a stationary kernel (unequal entropies allowed).

The causal Shannon floor `C∞ = max_a H(K_a)`, proved for every finite stationary
positive kernel. The Bellman envelope
recentred at `h_max = max_a H(K_a)` has increments of nonpositive mean, so the
conditional Hoeffding bound still controls its upper tail, while the constant policy
at a maximizing action controls the lower tail.  Result, for `n ≥ 1`:
`n h_max - √n K ≤ L_n ≤ C_n ≤ n h_max + √n K + c⋆`, `K = ∫ exp(-x²/(2M²)) dx`, hence
`C_n / n → h_max`.
-/
import CausalSeed.SqrtUniversality

noncomputable section
open Classical MeasureTheory Set Filter
open scoped Topology
namespace CausalSpectrum.Sqrt
namespace IncFamily
variable (F : IncFamily)

/-- Increments of nonpositive mean. -/
def SubCentered : Prop := ∀ j, ∑ y, F.P j y * F.X j y ≤ 0

theorem step_mgf_le {j : Fin F.nA} (hj : ∑ y, F.P j y * F.X j y ≤ 0) {θ : ℝ} (hθ : 0 ≤ θ) :
    ∑ y, F.P j y * Real.exp (θ * F.X j y) ≤ Real.exp (θ ^ 2 * F.M ^ 2 / 2) := by
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · have hx : ∀ y, F.X j y = 0 := fun y => abs_nonpos_iff.mp (h0 ▸ F.abs_X_le j y)
    simp [hx, F.Psum, ← h0]
  · calc ∑ y, F.P j y * Real.exp (θ * F.X j y)
        ≤ ∑ y, F.P j y * (Real.cosh (θ * F.M) + F.X j y / F.M * Real.sinh (θ * F.M)) :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (exp_le_chord hM (F.abs_X_le j y)) (F.Ppos _ _).le
      _ = Real.cosh (θ * F.M) + (∑ y, F.P j y * F.X j y) / F.M * Real.sinh (θ * F.M) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, F.Psum, one_mul]
          congr 1
          rw [Finset.sum_div, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro y _; ring
      _ ≤ Real.cosh (θ * F.M) := by
          have hs : 0 ≤ Real.sinh (θ * F.M) := by
            have h0 : (0:ℝ) ≤ θ * F.M := by positivity
            rw [Real.sinh_eq]
            have := Real.exp_le_exp.mpr (show -(θ * F.M) ≤ θ * F.M by linarith)
            linarith
          have : (∑ y, F.P j y * F.X j y) / F.M * Real.sinh (θ * F.M) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg (div_nonpos_of_nonpos_of_nonneg hj hM.le) hs
          linarith
      _ ≤ Real.exp ((θ * F.M) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = _ := by ring_nf

theorem mgfPol_le_sub (hs : F.SubCentered) : ∀ (n : ℕ) (π : F.APol n) {θ : ℝ}, 0 ≤ θ →
    F.mgfPol n π θ ≤ Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2))
  | 0, _, _, _ => by simp [mgfPol]
  | n + 1, π, θ, hθ => by
    calc F.mgfPol (n + 1) π θ
        ≤ ∑ y, F.P π.1 y * Real.exp (θ * F.X π.1 y) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (mgfPol_le_sub hs n _ hθ)
            (mul_nonneg (F.Ppos _ _).le (Real.exp_pos _).le)
      _ = (∑ y, F.P π.1 y * Real.exp (θ * F.X π.1 y)) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) := by
          rw [Finset.sum_mul]
      _ ≤ Real.exp (θ ^ 2 * F.M ^ 2 / 2) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right (F.step_mgf_le (hs π.1) hθ) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf

/-- Upper tail of the envelope for increments of nonpositive mean. -/
theorem G_upper_tail_sub (hs : F.SubCentered) {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 < x) :
    1 - F.G n (x * Real.sqrt n) ≤ gM F.M x := by
  show _ ≤ Real.exp (-(x ^ 2 / (2 * F.M ^ 2)))
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · rw [← h0]; simp; exact (F.G_cdf n).2.2.1 _ |>.1
  obtain ⟨π, hπ⟩ := (F.G_envelope n (x * Real.sqrt n)).2
  rw [← hπ]
  set θ := x / (F.M ^ 2 * Real.sqrt n)
  have hθ : 0 ≤ θ := by positivity
  refine (F.upper_chernoff n π _ θ hθ).trans ?_
  refine (mul_le_mul_of_nonneg_left (F.mgfPol_le_sub hs n π hθ) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, exponent_opt hn hM]

/-- The constant policy. -/
def constPol (j : Fin F.nA) : (n : ℕ) → F.APol n
  | 0 => PUnit.unit
  | n + 1 => ⟨j, fun _ => constPol j n⟩

theorem step_mgf_centered_at {j : Fin F.nA} (hj : ∑ y, F.P j y * F.X j y = 0) (θ : ℝ) :
    ∑ y, F.P j y * Real.exp (θ * F.X j y) ≤ Real.exp (θ ^ 2 * F.M ^ 2 / 2) := by
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · have hx : ∀ y, F.X j y = 0 := fun y => abs_nonpos_iff.mp (h0 ▸ F.abs_X_le j y)
    simp [hx, F.Psum, ← h0]
  · calc ∑ y, F.P j y * Real.exp (θ * F.X j y)
        ≤ ∑ y, F.P j y * (Real.cosh (θ * F.M) + F.X j y / F.M * Real.sinh (θ * F.M)) :=
          Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (exp_le_chord hM (F.abs_X_le j y)) (F.Ppos _ _).le
      _ = Real.cosh (θ * F.M) + (∑ y, F.P j y * F.X j y) / F.M * Real.sinh (θ * F.M) := by
          simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, F.Psum, one_mul]
          congr 1
          rw [Finset.sum_div, Finset.sum_mul]
          apply Finset.sum_congr rfl; intro y _; ring
      _ = Real.cosh (θ * F.M) := by rw [hj]; simp
      _ ≤ Real.exp ((θ * F.M) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
      _ = _ := by ring_nf

theorem mgf_const {j : Fin F.nA} (hj : ∑ y, F.P j y * F.X j y = 0) : ∀ (n : ℕ) (θ : ℝ),
    F.mgfPol n (F.constPol j n) θ ≤ Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2))
  | 0, _ => by simp [mgfPol]
  | n + 1, θ => by
    calc F.mgfPol (n + 1) (F.constPol j (n + 1)) θ
        ≤ ∑ y, F.P j y * Real.exp (θ * F.X j y) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) :=
          Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (mgf_const hj n θ)
            (mul_nonneg (F.Ppos _ _).le (Real.exp_pos _).le)
      _ = (∑ y, F.P j y * Real.exp (θ * F.X j y)) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) := by
          rw [Finset.sum_mul]
      _ ≤ Real.exp (θ ^ 2 * F.M ^ 2 / 2) * Real.exp (n * (θ ^ 2 * F.M ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_right (F.step_mgf_centered_at hj θ) (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; push_cast; ring_nf

/-- Lower tail of the envelope through one centred action. -/
theorem G_lower_tail_at {j : Fin F.nA} (hj : ∑ y, F.P j y * F.X j y = 0) {n : ℕ} (hn : 0 < n)
    {x : ℝ} (hx : 0 < x) : F.G n (-(x * Real.sqrt n)) ≤ gM F.M x := by
  show _ ≤ Real.exp (-(x ^ 2 / (2 * F.M ^ 2)))
  rcases eq_or_lt_of_le F.M_nonneg with h0 | hM
  · rw [← h0]; simp; exact (F.G_cdf n).2.2.1 _ |>.2
  refine ((F.G_envelope n _).1 (F.constPol j n)).trans ?_
  set θ := x / (F.M ^ 2 * Real.sqrt n)
  have hθ : 0 ≤ θ := by positivity
  refine (F.lower_chernoff n _ _ θ hθ).trans ?_
  refine (mul_le_mul_of_nonneg_left (F.mgf_const hj n (-θ)) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, neg_sq, show θ * -(x * Real.sqrt n) = -(θ * (x * Real.sqrt n)) by ring,
    exponent_opt hn hM]

theorem G_of_M_zero (hM : F.M = 0) : ∀ (n : ℕ) (x : ℝ), F.G n x = if 0 ≤ x then 1 else 0
  | 0, x => rfl
  | n + 1, x => by
    have hx : ∀ j y, F.X j y = 0 := fun j y => abs_nonpos_iff.mp (hM ▸ F.abs_X_le j y)
    obtain ⟨j, hj⟩ := F.T_attained (F.G n) x
    rw [G_succ, hj, expect]
    simp only [hx, sub_zero, G_of_M_zero hM n x, ← Finset.sum_mul, F.Psum, one_mul]

end IncFamily
end CausalSpectrum.Sqrt

namespace CausalSpectrum.Kernel
open Sqrt
variable (κ : Kernel)

/-- Shannon entropy (bits) of action `a`. -/
def actEntropy (a : Fin κ.nA) : ℝ := ∑ y, κ.K a y * infoMass (κ.K a y)

theorem univA_nonempty : (Finset.univ : Finset (Fin κ.nA)).Nonempty := ⟨⟨0, κ.hA⟩, Finset.mem_univ _⟩

/-- `h_max = max_a H(K_a)`. -/
def hmax : ℝ := Finset.univ.sup' κ.univA_nonempty κ.actEntropy

theorem actEntropy_nonneg (a : Fin κ.nA) : 0 ≤ κ.actEntropy a :=
  Finset.sum_nonneg fun y _ => mul_nonneg (κ.Kpos a y).le (κ.infoMass_K_nonneg a y)

theorem hmax_nonneg : 0 ≤ κ.hmax :=
  (κ.actEntropy_nonneg ⟨0, κ.hA⟩).trans (Finset.le_sup' _ (Finset.mem_univ _))

theorem fam_mean (h : ℝ) (a : Fin κ.nA) :
    ∑ y, (κ.fam h).P a y * (κ.fam h).X a y = κ.actEntropy a - h := by
  simp only [actEntropy, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [show ∑ y, κ.K a y = 1 from κ.Ksum a, one_mul]

theorem fam_hmax_sub : (κ.fam κ.hmax).SubCentered := fun a => by
  rw [fam_mean]
  have := Finset.le_sup' κ.actEntropy (Finset.mem_univ a)
  unfold hmax; linarith

theorem exists_hmax : ∃ a, κ.actEntropy a = κ.hmax := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_sup' κ.univA_nonempty κ.actEntropy
  exact ⟨a, ha.symm⟩

/-- `∫ g((t - c)/s) dt = s ∫ g`. -/
theorem integral_shift_scale (g : ℝ → ℝ) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    ∫ t, g ((t - c) / s) = s * ∫ t, g t := by
  have h := integral_affine g (-c / s) (s := 1 / s) (by positivity)
  rw [one_div, inv_inv] at h
  rw [← h]
  congr 1; funext t; congr 1; field_simp; ring

/-- The constant `K = ∫ exp(-x²/(2M²)) dx`. -/
def floorConst (h : ℝ) : ℝ := ∫ x, gM (κ.fam h).M x

theorem integrable_gM_shift {M : ℝ} (hM : 0 < M) (c : ℝ) {s : ℝ} (hs : 0 < s) :
    Integrable fun t => gM M ((t - c) / s) := by
  have := ((integrable_gM hM).comp_mul_right' (inv_pos.mpr hs).ne').comp_sub_right c
  refine this.congr (ae_of_all _ fun t => ?_)
  simp only [div_eq_mul_inv]

/-- **Upper bound.** `L_n ≤ n h_max + √n K` (`n ≥ 1`). -/
theorem envelope_le_floor {n : ℕ} (hn : 1 ≤ n) :
    envelopeMean (κ.rounds n) ≤ n * κ.hmax + Real.sqrt n * κ.floorConst κ.hmax := by
  set h := κ.hmax
  set F := κ.fam h
  set c : ℝ := n * h
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg n) κ.hmax_nonneg
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  rw [← integral_one_sub_Fstar]
  by_cases hM : F.M = 0
  · have he : ∀ t, 1 - Fstar (κ.rounds n) t = if t < c then (1:ℝ) else 0 := by
      intro t
      rw [κ.Fstar_eq_G h, F.G_of_M_zero hM]
      by_cases htc : t < c
      · rw [if_neg (by linarith), if_pos htc]; ring
      · rw [if_pos (by linarith [not_lt.mp htc]), if_neg htc]; ring
    simp_rw [he]
    rw [integral_lt_cutoff hc, one_mul]
    have : 0 ≤ κ.floorConst h := integral_nonneg fun x => (Real.exp_pos _).le
    nlinarith [hs.le]
  have hMpos : 0 < F.M := lt_of_le_of_ne F.M_nonneg (Ne.symm hM)
  have hgi := integrable_gM_shift hMpos c hs
  have hb : ∀ t ∈ Ioi (0:ℝ), 1 - Fstar (κ.rounds n) t ≤
      (if t ≤ c then (1:ℝ) else 0) + gM F.M ((t - c) / Real.sqrt n) := by
    intro t _
    rw [κ.Fstar_eq_G h]
    have hG := (F.G_cdf n).2.2.1 (t - c)
    have hg0 : 0 ≤ gM F.M ((t - c) / Real.sqrt n) := gM_nonneg _ _
    split_ifs with htc
    · linarith
    · have hx : 0 < (t - c) / Real.sqrt n := div_pos (by linarith [not_le.mp htc]) hs
      have := F.G_upper_tail_sub κ.fam_hmax_sub (n := n) (by omega) hx
      rw [div_mul_cancel₀ _ hs.ne'] at this
      linarith
  refine (setIntegral_mono_on (integrableOn_one_sub_Fstar _)
    ((integrableOn_le_cutoff hc).add hgi.integrableOn) measurableSet_Ioi hb).trans ?_
  simp only [Pi.add_apply]
  rw [integral_add (integrableOn_le_cutoff hc) hgi.integrableOn, integral_le_cutoff hc, one_mul]
  have h2 : ∫ t in Ioi (0:ℝ), gM F.M ((t - c) / Real.sqrt n) ≤
      ∫ t, gM F.M ((t - c) / Real.sqrt n) :=
    setIntegral_le_integral hgi (ae_of_all _ fun t => gM_nonneg _ _)
  rw [integral_shift_scale _ c hs] at h2
  unfold floorConst
  linarith

/-- **Lower bound.** `n h_max - √n K ≤ L_n` (`n ≥ 1`). -/
theorem floor_le_envelope {n : ℕ} (hn : 1 ≤ n) :
    n * κ.hmax - Real.sqrt n * κ.floorConst κ.hmax ≤ envelopeMean (κ.rounds n) := by
  set h := κ.hmax
  set F := κ.fam h
  set c : ℝ := n * h
  have hc : 0 ≤ c := mul_nonneg (Nat.cast_nonneg n) κ.hmax_nonneg
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  obtain ⟨a, ha⟩ := κ.exists_hmax
  have hj : ∑ y, F.P a y * F.X a y = 0 := by rw [fam_mean, ha]; ring
  have hK : 0 ≤ κ.floorConst h := integral_nonneg fun x => (Real.exp_pos _).le
  rw [← integral_one_sub_Fstar]
  by_cases hM : F.M = 0
  · have he : ∀ t, 1 - Fstar (κ.rounds n) t = if t < c then (1:ℝ) else 0 := by
      intro t
      rw [κ.Fstar_eq_G h, F.G_of_M_zero hM]
      by_cases htc : t < c
      · rw [if_neg (by linarith), if_pos htc]; ring
      · rw [if_pos (by linarith [not_lt.mp htc]), if_neg htc]; ring
    simp_rw [he]
    rw [integral_lt_cutoff hc, one_mul]
    nlinarith [hs.le]
  have hMpos : 0 < F.M := lt_of_le_of_ne F.M_nonneg (Ne.symm hM)
  have hgi := integrable_gM_shift hMpos c hs
  have hb : ∀ t ∈ Ioi (0:ℝ), (if t < c then (1:ℝ) else 0) - gM F.M ((t - c) / Real.sqrt n) ≤
      1 - Fstar (κ.rounds n) t := by
    intro t _
    rw [κ.Fstar_eq_G h]
    have hG := (F.G_cdf n).2.2.1 (t - c)
    have hg0 : 0 ≤ gM F.M ((t - c) / Real.sqrt n) := gM_nonneg _ _
    split_ifs with htc
    · have hx : 0 < (c - t) / Real.sqrt n := div_pos (by linarith) hs
      have := F.G_lower_tail_at hj (n := n) (by omega) hx
      rw [div_mul_cancel₀ _ hs.ne', neg_sub] at this
      rw [show (t - c) / Real.sqrt n = -((c - t) / Real.sqrt n) by ring, IncFamily.gM_neg]
      linarith
    · linarith
  have hlo := setIntegral_mono_on ((integrableOn_lt_cutoff hc).sub hgi.integrableOn)
    (integrableOn_one_sub_Fstar _) measurableSet_Ioi hb
  refine le_trans ?_ hlo
  simp only [Pi.sub_apply]
  rw [integral_sub (integrableOn_lt_cutoff hc) hgi.integrableOn, integral_lt_cutoff hc, one_mul]
  have h2 : ∫ t in Ioi (0:ℝ), gM F.M ((t - c) / Real.sqrt n) ≤
      ∫ t, gM F.M ((t - c) / Real.sqrt n) :=
    setIntegral_le_integral hgi (ae_of_all _ fun t => gM_nonneg _ _)
  rw [integral_shift_scale _ c hs] at h2
  unfold floorConst
  linarith

/-- Finite-horizon floor bounds for the optimal causal cost (bits), `n ≥ 1`. -/
theorem cost_floor_bounds {n : ℕ} (hn : 1 ≤ n) :
    n * κ.hmax - Real.sqrt n * κ.floorConst κ.hmax ≤ κ.costBits n ∧
      κ.costBits n ≤ n * κ.hmax + Real.sqrt n * κ.floorConst κ.hmax + shannonOverhead :=
  ⟨(κ.floor_le_envelope hn).trans (κ.costBits_sandwich n).1,
    (κ.costBits_sandwich n).2.trans (by linarith [κ.envelope_le_floor hn])⟩

theorem sqrt_div_self {n : ℕ} (hn : 1 ≤ n) : Real.sqrt n / n = (Real.sqrt n)⁻¹ := by
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  calc Real.sqrt n / n = Real.sqrt n / (Real.sqrt n * Real.sqrt n) := by
        rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
    _ = (Real.sqrt n)⁻¹ := by field_simp

theorem tendsto_inv_sqrt : Tendsto (fun n : ℕ => (Real.sqrt n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)

/-- Generic squeeze used for the floor. -/
theorem floor_squeeze {u : ℕ → ℝ} {h K c : ℝ}
    (hlo : ∀ n : ℕ, 1 ≤ n → n * h - Real.sqrt n * K ≤ u n)
    (hhi : ∀ n : ℕ, 1 ≤ n → u n ≤ n * h + Real.sqrt n * K + c) :
    Tendsto (fun n : ℕ => u n / n) atTop (𝓝 h) := by
  have hc : Tendsto (fun n : ℕ => c / (n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hK : Tendsto (fun n : ℕ => K * (Real.sqrt n)⁻¹) atTop (𝓝 0) := by
    simpa using tendsto_inv_sqrt.const_mul K
  have l1 : Tendsto (fun n : ℕ => h - K * (Real.sqrt n)⁻¹) atTop (𝓝 h) := by
    simpa using tendsto_const_nhds.sub hK
  have l2 : Tendsto (fun n : ℕ => h + K * (Real.sqrt n)⁻¹ + c / n) atTop (𝓝 h) := by
    simpa using (tendsto_const_nhds.add hK).add hc
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' l1 l2 ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    rw [le_div_iff₀ hn0]
    have e : (h - K * (Real.sqrt n)⁻¹) * n = n * h - Real.sqrt n * K := by
      rw [← sqrt_div_self hn]; field_simp
    rw [e]; exact hlo n hn
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : (0:ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn0]
    have e : (h + K * (Real.sqrt n)⁻¹ + c / n) * n = n * h + Real.sqrt n * K + c := by
      rw [← sqrt_div_self hn]; field_simp
    rw [e]; exact hhi n hn

/-- **Causal Shannon floor.** `C_n / n → max_a H(K_a)` (bits), for every finite
stationary positive kernel, equal or unequal entropies. -/
theorem causal_floor :
    Tendsto (fun n : ℕ => κ.costBits n / n) atTop (𝓝 κ.hmax) :=
  floor_squeeze (fun n hn => (κ.cost_floor_bounds hn).1) (fun n hn => (κ.cost_floor_bounds hn).2)

/-- The same for the envelope mean `L_n`. -/
theorem envelope_floor :
    Tendsto (fun n : ℕ => envelopeMean (κ.rounds n) / n) atTop (𝓝 κ.hmax) :=
  floor_squeeze (c := 0) (fun n hn => κ.floor_le_envelope hn)
    (fun n hn => by simpa using κ.envelope_le_floor hn)

end CausalSpectrum.Kernel

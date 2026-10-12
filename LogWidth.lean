/-
Ingredients of the sharp logarithmic coefficient that hold for every finite centered
increment family of common positive variance:

* the integrated envelope width `w_n = ∫ (V_n - G_n)` is `O(1 + log n)`, with no
  nondegeneracy hypothesis (a centered law of positive variance has two distinct atoms);
* the integrated amplification lemma `∫ U^n |R| ≤ ‖R‖₁ + ‖R'‖₁ w_n` for `C¹` functions `R`;
* pointwise stability `|T^n f - T^n g| ≤ U^n |f - g|` and the propagation bound
  `|T^n u_0 - u_n| ≤ Σ_j U^{n-1-j} |u_{j+1} - T u_j|` for any sequence of profiles.
-/
import CausalSeed.MomentAssembly

open Classical MeasureTheory Set Filter Topology Finset
open scoped ENNReal

namespace CausalSpectrum.Sqrt.IncFamily
open Decay AddMonoidAlgebra
variable (F : IncFamily)

/-! ### Nondegeneracy is automatic under positive variance -/

theorem nondeg_of_sig2_pos (hc : F.Centered) {j : Fin F.nA} (h : 0 < F.sig2 j) :
    F.Nondeg j := by
  by_contra hnd
  have hall : ∀ y₁ y₂ : Fin (F.nY j), F.X j y₁ = F.X j y₂ := fun y₁ y₂ => by
    by_contra hne; exact hnd (F.nondeg_of_ne j hne)
  set y₀ : Fin (F.nY j) := ⟨0, F.hY j⟩
  have h0 : F.X j y₀ = 0 := by
    have := hc j
    simp only [fun y => hall y y₀, ← Finset.sum_mul, F.Psum, one_mul] at this
    exact this
  have : F.sig2 j = 0 := by simp [sig2, fun y => hall y y₀, h0]
  linarith

/-! ### The width bound -/

theorem Wint_le_of_sums {a : ℝ} (ha : 0 < a) (j₀ : Fin F.nA) (S : ℕ → ℝ)
    (hS0 : ∀ n, 0 ≤ S n)
    (hα : ∀ n, ∑ r ∈ range n, (F.wdata ha j₀).α r ≤ ENNReal.ofReal (S n))
    (hβ : ∀ n, ∑ r ∈ range n, (F.wdata ha j₀).β r ≤ ENNReal.ofReal (1 / 4)) (n : ℕ) :
    F.Wint n ≤ ENNReal.ofReal (2 * (24 * a + 2 * S n)) := by
  set D := F.wdata ha j₀
  set c : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (4 * D.A) + 2 * ∑ r ∈ range n, D.α r
  have hcm : Monotone c := fun m k h => by
    simp only [c]
    gcongr
  have hb : ∀ n, ∑ r ∈ range n, 2 * D.β r ≤ 1 / 2 := fun n => by
    rw [← mul_sum, ← two_mul_quarter]; gcongr; exact hβ n
  have hW : ∀ n, F.Wint n ≤ c n + ∑ i ∈ range n, (fun r => 2 * D.β r) (n - 1 - i) * F.Wint i := by
    intro n
    refine (D.Wint_le n).trans (le_of_eq ?_)
    rw [sum_add_distrib, mul_add, sum_range_reflect (fun r => D.α r) n]
    simp only [c, mul_sum, mul_assoc, add_assoc]
  have h2 := recursion_solve _ c _ hcm hb hW n
  have hcn : c n ≤ ENNReal.ofReal (24 * a) + 2 * ENNReal.ofReal (S n) := by
    simp only [c]
    rw [show 4 * D.A = 24 * a by simp only [D, wdata]; ring]
    gcongr; exact hα n
  have h3 : 2 * c n ≤ 2 * (ENNReal.ofReal (24 * a) + 2 * ENNReal.ofReal (S n)) := by gcongr
  refine h2.trans (h3.trans (le_of_eq ?_))
  rw [eq_comm, ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num), ENNReal.ofReal_add (by positivity)
    (by have := hS0 n; positivity), ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
    ENNReal.ofReal_ofNat]

/-- **Width bound.** For a centered family in which every action has the variance of a
nondegenerate action, `w_n = ∫ (V_n - G_n) ≤ C (1 + log n)`. -/
theorem Wint_log_upper (hc : F.Centered) {j₀ : Fin F.nA} (hnd : F.Nondeg j₀)
    (hσ : ∀ j, F.sig2 j = F.sig2 j₀) :
    ∃ C, ∀ n : ℕ, F.Wint n ≤ ENNReal.ofReal (C * (1 + Real.log n)) := by
  obtain ⟨ρ, b, c, ζ, h0, h1, hb, hζ, heq⟩ := hnd
  have hmom : ∀ k, ∀ i < 3, F.mom k i = F.mom j₀ i := by
    intro k i hi
    interval_cases i
    · rw [F.mom_zero, F.mom_zero]
    · simp only [mom, pow_one]; rw [hc k, hc j₀]
    · simpa [mom, sig2] using hσ k
  obtain ⟨L, hLb, hL⟩ := F.exists_L_beta j₀ (by norm_num) (by norm_num) hmom hb
    (by positivity : (0:ℝ) ≤ 24 * Real.sqrt 3 * Real.sqrt (2 / ρ ^ 3))
    (fun r => by rw [heq]; exact tv_decay_three_gg h0 h1 hζ r)
  set a := (L : ℝ) * b
  set Sm := F.amomSum j₀ 3
  have hSm : 0 ≤ Sm := F.amomSum_nonneg j₀ 3
  set K := Sm * 7 * ((1 / (2 * b)) ^ 2 * (8 / ρ))
  have hK : 0 ≤ K := by positivity
  have hlog : ∀ n : ℕ, 0 ≤ 1 + Real.log n := fun n => by
    have := Real.log_natCast_nonneg n; linarith
  have hLn : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · simp [a, h] at hLb
    · exact h
  have hα : ∀ n, ∑ r ∈ range n, (F.wdata hLb j₀).α r ≤ ENNReal.ofReal (K * (1 + Real.log n)) := by
    intro n
    refine (sum_ofReal_le (fun r => by
        have := tv_nonneg (F.measOf j₀ ^ r * Dif a ^ (3 - 1)); positivity)
      (fun r => F.wdata_α_le hLb j₀ (by norm_num) (by norm_num) hmom r) n).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_sum]
    simp only [K, mul_assoc]
    refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hSm
    calc ∑ r ∈ range n, tv (F.measOf j₀ ^ r * Dif a ^ (3 - 1))
        ≤ ∑ r ∈ range n, (1 / (2 * b)) ^ 2 * (8 / ρ) * (1 / (r + 1)) := by
          refine sum_le_sum fun r _ => (tv_Dif_scale b hb hLn 2 _).trans ?_
          rw [heq]
          refine (mul_le_mul_of_nonneg_left (tv_decay_two b c h0 h1 hζ r) (by positivity)).trans
            (le_of_eq ?_)
          field_simp
      _ ≤ (1 / (2 * b)) ^ 2 * (8 / ρ) * (1 + Real.log n) := by
          rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (sum_inv_le_log n) (by positivity)
      _ = (1 / (2 * b)) ^ 2 * (8 / ρ * (1 + Real.log n)) := by ring
  refine ⟨2 * (24 * a + 2 * K), fun n => ?_⟩
  refine (F.Wint_le_of_sums hLb j₀ _ (fun n => mul_nonneg hK (hlog n)) hα hL n).trans
    (ENNReal.ofReal_le_ofReal ?_)
  have h1n : 1 ≤ 1 + Real.log n := by have := Real.log_natCast_nonneg n; linarith
  have ha0 : 0 ≤ a := hLb.le
  nlinarith

/-- **Width and mean bound under a common positive variance** (no nondegeneracy hypothesis):
`e_n ≤ C (1 + log n)` and `w_n ≤ C (1 + log n)`. -/
theorem width_log_upper (hc : F.Centered) {v : ℝ} (hv : 0 < v) (hσ : ∀ j, F.sig2 j = v) :
    ∃ C, ∀ n : ℕ, F.eG (F.G n) ≤ C * (1 + Real.log n) ∧
      F.Wint n ≤ ENNReal.ofReal (C * (1 + Real.log n)) := by
  set j₀ : Fin F.nA := ⟨0, F.hA⟩
  have hnd := F.nondeg_of_sig2_pos hc (j := j₀) (by rw [hσ]; exact hv)
  have hσ' : ∀ j, F.sig2 j = F.sig2 j₀ := fun j => by rw [hσ, hσ]
  obtain ⟨C₁, h₁⟩ := F.eG_log_upper hc hnd hσ'
  obtain ⟨C₂, h₂⟩ := F.Wint_log_upper hc hnd hσ'
  refine ⟨max C₁ C₂, fun n => ⟨?_, ?_⟩⟩
  · have hl : 0 ≤ 1 + Real.log n := by have := Real.log_natCast_nonneg n; linarith
    exact (h₁ n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hl)
  · have hl : 0 ≤ 1 + Real.log n := by have := Real.log_natCast_nonneg n; linarith
    exact (h₂ n).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hl))

/-! ### Integrated amplification -/

/-- **Integrated amplification** (`C¹` form). For `R ∈ C¹` with `R' ∈ L¹` continuous and
`R → 0` at `-∞`, `∫ U^n |R| ≤ ‖R‖₁ + ‖R'‖₁ · w_n`. -/
theorem amp_lintegral {R R' : ℝ → ℝ} (hR : ∀ y, HasDerivAt R (R' y) y) (hR'c : Continuous R')
    (hR'i : Integrable R') (hlim : Tendsto R atBot (𝓝 0)) (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (F.U n (fun y => |R y|) x) ≤
      (∫⁻ x, ‖R x‖ₑ) + (∫⁻ x, ‖R' x‖ₑ) * F.Wint n := by
  set j₀ : Fin F.nA := ⟨0, F.hA⟩
  have hRm : Measurable R := (continuous_iff_continuousAt.2 fun y => (hR y).continuousAt).measurable
  have hRa : Measurable fun y => |R y| := continuous_abs.measurable.comp hRm
  have hpt : ∀ x, F.U n (fun y => |R y|) x ≤ act (F.measOf j₀ ^ n) (fun y => |R y|) x +
      ∫ w, |R' (x - w)| * F.Wd n w := fun x => by
    obtain ⟨σ, hσ⟩ := (F.U_envelope (fun y => |R y|) n x).2
    rw [← hσ]
    exact F.polE_abs_le hR hR'c hR'i hlim j₀ n σ x
  have hnn : ∀ x, 0 ≤ act (F.measOf j₀ ^ n) (fun y => |R y|) x := fun x => by
    rw [← F.polE_refPol]; exact F.polE_nonneg (fun _ => abs_nonneg _) _ _ _
  calc ∫⁻ x, ENNReal.ofReal (F.U n (fun y => |R y|) x)
      ≤ ∫⁻ x, (ENNReal.ofReal (act (F.measOf j₀ ^ n) (fun y => |R y|) x) +
          ∫⁻ w, ENNReal.ofReal (|R' (x - w)| * F.Wd n w)) := by
        refine lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (hpt x)).trans ?_
        rw [← F.ofReal_conv_Wd hR'i]
        exact ENNReal.ofReal_add_le
    _ = (∫⁻ x, ENNReal.ofReal (act (F.measOf j₀ ^ n) (fun y => |R y|) x)) +
          ∫⁻ x, ∫⁻ w, ENNReal.ofReal (|R' (x - w)| * F.Wd n w) := by
        rw [lintegral_add_left]
        exact (measurable_act _ hRa).ennreal_ofReal
    _ ≤ (∫⁻ x, ‖R x‖ₑ) + (∫⁻ x, ‖R' x‖ₑ) * F.Wint n := by
        refine add_le_add ?_ (le_of_eq (F.lintegral_conv_Wd hR'c n))
        refine le_trans ?_ ((lintegral_act_le (F.measOf j₀ ^ n) hRa).trans ?_)
        · exact lintegral_mono fun x => by
            rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn x)]
        · have e : ∀ x, ‖|R x|‖ₑ = ‖R x‖ₑ := fun x => by
            rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]
          simp only [e]
          calc ENNReal.ofReal (tv (F.measOf j₀ ^ n)) * ∫⁻ x, ‖R x‖ₑ
              ≤ 1 * ∫⁻ x, ‖R x‖ₑ := by
                gcongr; exact ENNReal.ofReal_le_one.2 (F.tv_measOf_pow _ _)
            _ = _ := one_mul _

/-! ### Pointwise stability and propagation -/

/-- `T^n f`. -/
noncomputable def Tit : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, f => f
  | n + 1, f => F.T (Tit n f)

theorem Tit_H (n : ℕ) : F.Tit n (F.G 0) = F.G n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Tit, ih]; rfl

theorem Tmax_mono {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) (x : ℝ) : F.Tmax f x ≤ F.Tmax g x :=
  Finset.sup'_le _ _ fun j _ => (F.expect_mono j h x).trans
    (Finset.le_sup' (fun j => F.expect j g x) (Finset.mem_univ j))

theorem U_mono {f g : ℝ → ℝ} (h : ∀ x, f x ≤ g x) : ∀ (n : ℕ) (x : ℝ), F.U n f x ≤ F.U n g x
  | 0, x => h x
  | n + 1, x => F.Tmax_mono (U_mono h n) x

theorem expect_add (j) (f g : ℝ → ℝ) (x : ℝ) :
    F.expect j (fun y => f y + g y) x = F.expect j f x + F.expect j g x := by
  simp only [expect, mul_add, Finset.sum_add_distrib]

theorem Tmax_add_le (f g : ℝ → ℝ) (x : ℝ) :
    F.Tmax (fun y => f y + g y) x ≤ F.Tmax f x + F.Tmax g x :=
  Finset.sup'_le _ _ fun j _ => by
    rw [F.expect_add]
    exact add_le_add (Finset.le_sup' (fun j => F.expect j f x) (Finset.mem_univ j))
      (Finset.le_sup' (fun j => F.expect j g x) (Finset.mem_univ j))

theorem Tmax_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) (x : ℝ) :
    F.Tmax (fun y => ∑ i ∈ s, f i y) x ≤ ∑ i ∈ s, F.Tmax (f i) x := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact Finset.sup'_le _ _ fun j _ => by simp [expect]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (F.Tmax_add_le (f a) (fun y => ∑ i ∈ s, f i y) x).trans (by linarith)

/-- One step: `|T f - T g| ≤ T⁺ |f - g|`. -/
theorem abs_T_sub_le (f g : ℝ → ℝ) (x : ℝ) :
    |F.T f x - F.T g x| ≤ F.Tmax (fun y => |f y - g y|) x := by
  have key : ∀ f g : ℝ → ℝ, F.T f x - F.T g x ≤ F.Tmax (fun y => |f y - g y|) x := by
    intro f g
    obtain ⟨j, hj⟩ := F.T_attained g x
    rw [hj]
    have h1 := F.T_le f x j
    have h2 : F.expect j f x - F.expect j g x ≤ F.expect j (fun y => |f y - g y|) x := by
      simp only [expect, ← Finset.sum_sub_distrib, ← mul_sub]
      exact Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left (le_abs_self _) (F.Ppos _ _).le
    exact (by linarith : F.T f x - F.expect j g x ≤ F.expect j f x - F.expect j g x).trans
      (h2.trans (Finset.le_sup' (fun j => F.expect j _ x) (Finset.mem_univ j)))
  rw [abs_le]
  constructor
  · have := key g f
    have e : (fun y => |g y - f y|) = fun y => |f y - g y| := funext fun y => abs_sub_comm _ _
    rw [e] at this; linarith
  · exact key f g

/-- **Stability.** `|T^n f - T^n g| ≤ U^n |f - g|` pointwise. -/
theorem abs_Tit_sub_le (f g : ℝ → ℝ) :
    ∀ (n : ℕ) (x : ℝ), |F.Tit n f x - F.Tit n g x| ≤ F.U n (fun y => |f y - g y|) x
  | 0, _ => le_rfl
  | n + 1, x => (F.abs_T_sub_le _ _ x).trans (F.Tmax_mono (abs_Tit_sub_le f g n) x)

/-- **Propagation.** For any sequence of profiles `u`, with one-step residuals
`R_j = u_{j+1} - T u_j`, `|T^n u_0 - u_n| ≤ Σ_{j<n} U^{n-1-j} |R_j|` pointwise. -/
theorem propagation (u : ℕ → ℝ → ℝ) :
    ∀ (n : ℕ) (x : ℝ), |F.Tit n (u 0) x - u n x| ≤
      ∑ j ∈ range n, F.U (n - 1 - j) (fun y => |u (j + 1) y - F.T (u j) y|) x
  | 0, x => by simp [Tit]
  | n + 1, x => by
    have ih := propagation u n
    have h1 : |F.Tit (n + 1) (u 0) x - F.T (u n) x| ≤
        ∑ j ∈ range n, F.U (n - j) (fun y => |u (j + 1) y - F.T (u j) y|) x := by
      refine (F.abs_T_sub_le _ _ x).trans ((F.Tmax_mono ih x).trans ?_)
      refine (F.Tmax_sum_le _ _ x).trans (le_of_eq (Finset.sum_congr rfl fun j hj => ?_))
      have : n - j = (n - 1 - j) + 1 := by
        have := Finset.mem_range.1 hj; omega
      rw [this]; rfl
    rw [Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self]
    have h2 : |F.T (u n) x - u (n + 1) x| = F.U 0 (fun y => |u (n + 1) y - F.T (u n) y|) x := by
      simp [U, abs_sub_comm]
    calc |F.Tit (n + 1) (u 0) x - u (n + 1) x|
        ≤ |F.Tit (n + 1) (u 0) x - F.T (u n) x| + |F.T (u n) x - u (n + 1) x| :=
          abs_sub_le _ _ _
      _ ≤ _ := by rw [h2]; linarith

end CausalSpectrum.Sqrt.IncFamily

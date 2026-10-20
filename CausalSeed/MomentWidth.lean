/-
The width contraction for the Bellman envelopes.

`polE n π g x = E g(x - S_n^π)` for an adaptive policy `π`; `U n g` is the upper envelope
`sup_π polE n π g` (Bellman recursion with `max`), `act (μ_{j₀}^n) g` the reference walk.
Telescoping along the policy gives
`|polE n π g - μ_{j₀}^n * g| ≤ Σ_{i<n} U i (K_{n-1-i})` with
`K_r = Σ_a |E_a(μ_{j₀}^r * g) - E_{j₀}(μ_{j₀}^r * g)|`, and an integration by parts against
the policy CDF gives, for `R ∈ C¹` with `R' ∈ L¹`,
`polE n π |R| x ≤ μ_{j₀}^n * |R| (x) + ∫ |R'(x - w)| (U_n - G_n)(w) dw`.
-/
import CausalSeed.MomentSmooth

noncomputable section
open Classical MeasureTheory Set Filter Topology
open scoped ENNReal

namespace CausalSpectrum.Sqrt.IncFamily
open Decay AddMonoidAlgebra
variable (F : IncFamily)

/-- `polE n π g x = E g(x - S_n^π)`. -/
def polE : (n : ℕ) → F.APol n → (ℝ → ℝ) → ℝ → ℝ
  | 0, _, g => g
  | n + 1, π, g => fun x => ∑ y, F.P π.1 y * polE n (π.2 y) g (x - F.X π.1 y)

theorem cdfPol_eq_polE : ∀ (n : ℕ) (π : F.APol n), F.cdfPol n π = F.polE n π (F.G 0)
  | 0, _ => rfl
  | n + 1, π => by
    funext x; simp only [cdfPol, polE, cdfPol_eq_polE n]

theorem polE_mono {g₁ g₂ : ℝ → ℝ} (h : ∀ x, g₁ x ≤ g₂ x) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ), F.polE n π g₁ x ≤ F.polE n π g₂ x
  | 0, _, x => h x
  | n + 1, π, x => Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (polE_mono h n _ _) (F.Ppos _ _).le

theorem polE_add_const (g : ℝ → ℝ) (c : ℝ) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ), F.polE n π (fun y => g y + c) x = F.polE n π g x + c
  | 0, _, x => rfl
  | n + 1, π, x => by
    simp only [polE, polE_add_const g c n, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      F.Psum, one_mul]

theorem polE_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ),
      F.polE n π (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, F.polE n π (f i) x
  | 0, _, x => rfl
  | n + 1, π, x => by
    simp only [polE, polE_sum s f n, Finset.mul_sum]
    exact Finset.sum_comm

theorem polE_translate (g : ℝ → ℝ) (t : ℝ) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ), F.polE n π (fun y => g (y + t)) x = F.polE n π g (x + t)
  | 0, _, x => rfl
  | n + 1, π, x => by
    simp only [polE, polE_translate g t n]
    exact Finset.sum_congr rfl fun y _ => by ring_nf

theorem polE_bounds {g : ℝ → ℝ} (h : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ), 0 ≤ F.polE n π g x ∧ F.polE n π g x ≤ 1
  | 0, _, x => h x
  | n + 1, π, x => by
    constructor
    · exact Finset.sum_nonneg fun y _ => mul_nonneg (F.Ppos _ _).le (polE_bounds h n _ _).1
    · calc _ ≤ ∑ y, F.P π.1 y * 1 := Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (polE_bounds h n _ _).2 (F.Ppos _ _).le
        _ = 1 := by rw [← Finset.sum_mul, F.Psum, one_mul]

theorem measurable_polE {g : ℝ → ℝ} (hg : Measurable g) :
    ∀ (n : ℕ) (π : F.APol n), Measurable (F.polE n π g)
  | 0, _ => hg
  | n + 1, π => Finset.measurable_sum _ fun y _ =>
      ((measurable_polE hg n _).comp (measurable_id.sub_const _)).const_mul _

/-! ### Reference walk -/

/-- The law of one increment of action `j`, as a finitely supported measure. -/
def measOf (j : Fin F.nA) : Meas := ∑ y, single (F.X j y) (F.P j y)

theorem expect_eq_act (j) (g : ℝ → ℝ) (x : ℝ) : F.expect j g x = act (F.measOf j) g x := by
  rw [measOf, act_sum]; simp only [act_single]; rfl

theorem tv_measOf (j) : tv (F.measOf j) ≤ 1 := by
  refine (tv_sum_le _ _).trans (le_of_eq ?_)
  simp only [tv_single, abs_of_pos (F.Ppos _ _), F.Psum]

theorem tv_measOf_pow (j) (n : ℕ) : tv (F.measOf j ^ n) ≤ 1 :=
  (tv_pow_le _ n).trans (pow_le_one₀ (tv_nonneg _) (F.tv_measOf j))

/-- The policy that always plays `j`. -/
def refPol (j : Fin F.nA) : (n : ℕ) → F.APol n
  | 0 => PUnit.unit
  | n + 1 => ⟨j, fun _ => refPol j n⟩

theorem polE_refPol (j) (g : ℝ → ℝ) :
    ∀ (n : ℕ) (x : ℝ), F.polE n (F.refPol j n) g x = act (F.measOf j ^ n) g x
  | 0, x => by rw [pow_zero, act_one]; rfl
  | n + 1, x => by
    rw [pow_succ', act_mul, ← F.expect_eq_act]
    simp only [polE, refPol, expect]
    exact Finset.sum_congr rfl fun y _ => by rw [polE_refPol j g n]

/-! ### The upper envelope -/

/-- `(T⁺ g)(x) = max_j E g(x - X_j)`. -/
def Tmax (g : ℝ → ℝ) (x : ℝ) : ℝ := Finset.univ.sup' F.univ_nonempty (fun j => F.expect j g x)

/-- `U n g = (T⁺)^n g`. -/
def U : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0, g => g
  | n + 1, g => F.Tmax (U n g)

theorem U_envelope (g : ℝ → ℝ) : ∀ (n : ℕ) (x : ℝ),
    (∀ π : F.APol n, F.polE n π g x ≤ F.U n g x) ∧ ∃ π : F.APol n, F.polE n π g x = F.U n g x
  | 0, x => ⟨fun _ => le_rfl, ⟨PUnit.unit, rfl⟩⟩
  | n + 1, x => by
    constructor
    · intro π
      refine le_trans ?_ (Finset.le_sup' (fun j => F.expect j (F.U n g) x) (Finset.mem_univ π.1))
      exact Finset.sum_le_sum fun y _ =>
        mul_le_mul_of_nonneg_left ((U_envelope g n _).1 (π.2 y)) (F.Ppos _ _).le
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' F.univ_nonempty
        (fun j => F.expect j (F.U n g) x)
      choose k hk using fun y : Fin (F.nY j) => (U_envelope g n (x - F.X j y)).2
      refine ⟨⟨j, k⟩, ?_⟩
      change ∑ y, F.P j y * F.polE n (k y) g (x - F.X j y) = F.Tmax (F.U n g) x
      rw [Tmax, hj]; unfold expect; simp only [hk]

theorem expect_U_le (g : ℝ → ℝ) (n : ℕ) (j) (x : ℝ) : F.expect j (F.U n g) x ≤ F.U (n + 1) g x :=
  Finset.le_sup' (fun j => F.expect j (F.U n g) x) (Finset.mem_univ j)

theorem U_monotone {g : ℝ → ℝ} (hg : Monotone g) : ∀ n, Monotone (F.U n g)
  | 0 => hg
  | n + 1 => by
    intro x x' hx
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' F.univ_nonempty
        (fun j => F.expect j (F.U n g) x)
    show F.Tmax (F.U n g) x ≤ F.Tmax (F.U n g) x'
    rw [Tmax, hj]
    refine le_trans ?_ (Finset.le_sup' (fun j => F.expect j (F.U n g) x') (Finset.mem_univ j))
    exact Finset.sum_le_sum fun y _ =>
      mul_le_mul_of_nonneg_left (U_monotone hg n (by linarith)) (F.Ppos _ _).le

/-! ### Telescoping -/

/-- `K_r(x) = Σ_a |E_a(μ₀^r g) - E_{j₀}(μ₀^r g)|(x)`. -/
def Kf (j₀ : Fin F.nA) (g : ℝ → ℝ) (r : ℕ) (x : ℝ) : ℝ :=
  ∑ a, |F.expect a (act (F.measOf j₀ ^ r) g) x - F.expect j₀ (act (F.measOf j₀ ^ r) g) x|

/-- **Telescoping along the policy.** -/
theorem telescope (j₀ : Fin F.nA) (g : ℝ → ℝ) : ∀ (n : ℕ) (π : F.APol n) (x : ℝ),
    |F.polE n π g x - act (F.measOf j₀ ^ n) g x| ≤
      ∑ i ∈ Finset.range n, F.U i (F.Kf j₀ g (n - 1 - i)) x
  | 0, π, x => by simp [polE, act_one]
  | n + 1, π, x => by
    have e : F.polE (n + 1) π g x - act (F.measOf j₀ ^ (n + 1)) g x =
        ∑ y, F.P π.1 y * (F.polE n (π.2 y) g (x - F.X π.1 y) -
          act (F.measOf j₀ ^ n) g (x - F.X π.1 y)) +
        (F.expect π.1 (act (F.measOf j₀ ^ n) g) x - F.expect j₀ (act (F.measOf j₀ ^ n) g) x) := by
      rw [pow_succ', act_mul, ← F.expect_eq_act]
      simp only [polE, expect, mul_sub, Finset.sum_sub_distrib]; ring
    rw [e, Finset.sum_range_succ']
    have hK : |F.expect π.1 (act (F.measOf j₀ ^ n) g) x - F.expect j₀ (act (F.measOf j₀ ^ n) g) x| ≤
        F.U 0 (F.Kf j₀ g (n + 1 - 1 - 0)) x := by
      simp only [U, Kf, Nat.add_sub_cancel, Nat.sub_zero]
      exact Finset.single_le_sum (f := fun a => |F.expect a (act (F.measOf j₀ ^ n) g) x -
        F.expect j₀ (act (F.measOf j₀ ^ n) g) x|) (fun a _ => abs_nonneg _) (Finset.mem_univ _)
    have hS : |∑ y, F.P π.1 y * (F.polE n (π.2 y) g (x - F.X π.1 y) -
          act (F.measOf j₀ ^ n) g (x - F.X π.1 y))| ≤
        ∑ i ∈ Finset.range n, F.U (i + 1) (F.Kf j₀ g (n + 1 - 1 - (i + 1))) x := by
      calc _ ≤ ∑ y, F.P π.1 y * |F.polE n (π.2 y) g (x - F.X π.1 y) -
            act (F.measOf j₀ ^ n) g (x - F.X π.1 y)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
            exact Finset.sum_congr rfl fun y _ => by rw [abs_mul, abs_of_pos (F.Ppos _ _)]
        _ ≤ ∑ y, F.P π.1 y * ∑ i ∈ Finset.range n, F.U i (F.Kf j₀ g (n - 1 - i)) (x - F.X π.1 y) :=
            Finset.sum_le_sum fun y _ =>
              mul_le_mul_of_nonneg_left (telescope j₀ g n _ _) (F.Ppos _ _).le
        _ = ∑ i ∈ Finset.range n, F.expect π.1 (F.U i (F.Kf j₀ g (n - 1 - i))) x := by
            simp only [expect, Finset.mul_sum]; exact Finset.sum_comm
        _ ≤ _ := Finset.sum_le_sum fun i _ => by
            rw [show n + 1 - 1 - (i + 1) = n - 1 - i by omega]
            exact F.expect_U_le _ i _ x
    exact (abs_add_le _ _).trans (by linarith)


/-! ### Integration by parts against a policy CDF -/

theorem G0_bounds (x : ℝ) : 0 ≤ F.G 0 x ∧ F.G 0 x ≤ 1 := (F.G_cdf 0).2.2.1 x

theorem integrable_mul_polE {k' : ℝ → ℝ} (hk' : Integrable k') (n : ℕ) (π : F.APol n) (x : ℝ) :
    Integrable fun w => k' (x - w) * F.polE n π (F.G 0) w := by
  refine (hk'.comp_sub_left x).mul_bdd (c := 1)
    (F.measurable_polE (F.measurable_G 0) n π).aestronglyMeasurable (ae_of_all _ fun w => ?_)
  have := F.polE_bounds F.G0_bounds n π w
  rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2

/-- **Integration by parts:** `E k(x - S) = ∫ k'(x - w) P(S ≤ w) dw`. -/
theorem polE_ibp {k k' : ℝ → ℝ} (hk : ∀ y, HasDerivAt k (k' y) y) (hk' : Integrable k')
    (hlim : Tendsto k atBot (𝓝 0)) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ), F.polE n π k x = ∫ w, k' (x - w) * F.polE n π (F.G 0) w
  | 0, _, x => by
    simp only [polE]
    have e : ∫ w, k' (x - w) * F.G 0 w = ∫ u, k' u * F.G 0 (x - u) := by
      have := integral_sub_left_eq_self (fun u => k' u * F.G 0 (x - u)) (μ := volume) x
      simpa using this
    rw [e]
    have e2 : (fun u => k' u * F.G 0 (x - u)) = (Iic x).indicator k' := by
      funext u
      simp only [G, indicator, mem_Iic, sub_nonneg]
      split_ifs <;> simp
    rw [e2, integral_indicator measurableSet_Iic,
      integral_Iic_of_hasDerivAt_of_tendsto (hk x).continuousAt.continuousWithinAt
        (fun y _ => hk y) hk'.integrableOn hlim, sub_zero]
  | n + 1, π, x => by
    simp only [polE]
    have hi : ∀ y, Integrable fun w => F.P π.1 y *
        (k' (x - w) * F.polE n (π.2 y) (F.G 0) (w - F.X π.1 y)) := fun y => by
      have := (F.integrable_mul_polE hk' n (π.2 y) (x - F.X π.1 y)).comp_sub_right (F.X π.1 y)
      refine (this.const_mul (F.P π.1 y)).congr (ae_of_all _ fun w => ?_)
      simp only [Function.comp_apply]; ring_nf
    have e : ∀ w, k' (x - w) * ∑ y, F.P π.1 y * F.polE n (π.2 y) (F.G 0) (w - F.X π.1 y) =
        ∑ y, F.P π.1 y * (k' (x - w) * F.polE n (π.2 y) (F.G 0) (w - F.X π.1 y)) := fun w => by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun y _ => by ring
    simp_rw [e]
    rw [integral_finsetSum _ fun y _ => hi y]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [integral_const_mul, polE_ibp hk hk' hlim n (π.2 y) (x - F.X π.1 y)]
    congr 1
    have := integral_sub_right_eq_self (fun w => k' (x - w) * F.polE n (π.2 y) (F.G 0) (w - F.X π.1 y))
      (μ := volume) (-F.X π.1 y)
    rw [← this]
    refine integral_congr_ae (ae_of_all _ fun w => ?_)
    simp only [sub_neg_eq_add]; ring_nf


/-! ### The width `W_n = U_n - G_n` -/

/-- `W_n(w) = sup_π P(S_n^π ≤ w) - inf_π P(S_n^π ≤ w)`. -/
def Wd (n : ℕ) (w : ℝ) : ℝ := F.U n (F.G 0) w - F.G n w

theorem G_le_polE (n : ℕ) (π : F.APol n) (x : ℝ) : F.G n x ≤ F.polE n π (F.G 0) x := by
  rw [← F.cdfPol_eq_polE]; exact (F.G_envelope n x).1 π

theorem polE_le_U (g : ℝ → ℝ) (n : ℕ) (π : F.APol n) (x : ℝ) : F.polE n π g x ≤ F.U n g x :=
  (F.U_envelope g n x).1 π

theorem Wd_bounds (n : ℕ) (w : ℝ) : 0 ≤ F.Wd n w ∧ F.Wd n w ≤ 1 := by
  obtain ⟨π, hπ⟩ := (F.U_envelope (F.G 0) n w).2
  have h1 := F.G_le_polE n π w
  have h2 := F.polE_bounds F.G0_bounds n π w
  have h3 := (F.G_cdf n).2.2.1 w
  simp only [Wd, ← hπ]; constructor <;> linarith [h2.1, h2.2, h3.1]

theorem measurable_Wd (n : ℕ) : Measurable (F.Wd n) :=
  ((F.U_monotone (F.G_cdf 0).1 n).measurable).sub (F.measurable_G n)

theorem abs_polE_sub_le (n : ℕ) (π σ : F.APol n) (w : ℝ) :
    |F.polE n π (F.G 0) w - F.polE n σ (F.G 0) w| ≤ F.Wd n w := by
  have a1 := F.G_le_polE n π w
  have a2 := F.G_le_polE n σ w
  have b1 := F.polE_le_U (F.G 0) n π w
  have b2 := F.polE_le_U (F.G 0) n σ w
  rw [abs_le]; simp only [Wd]; constructor <;> linarith

theorem integrable_mul_Wd {k : ℝ → ℝ} (hk : Integrable k) (n : ℕ) (x : ℝ) :
    Integrable fun w => |k (x - w)| * F.Wd n w := by
  refine (hk.comp_sub_left x).abs.mul_bdd (c := 1) (F.measurable_Wd n).aestronglyMeasurable
    (ae_of_all _ fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (F.Wd_bounds n w).1]; exact (F.Wd_bounds n w).2

/-- **Contraction step.** For `R ∈ C¹` with `R' ∈ L¹` continuous and `R → 0` at `-∞`,
`E |R|(x - S_n^π) ≤ (μ₀^n * |R|)(x) + ∫ |R'(x - w)| W_n(w) dw`. -/
theorem polE_abs_le {R R' : ℝ → ℝ} (hR : ∀ y, HasDerivAt R (R' y) y) (hR'c : Continuous R')
    (hR'i : Integrable R') (hlim : Tendsto R atBot (𝓝 0)) (j₀ : Fin F.nA) (n : ℕ)
    (π : F.APol n) (x : ℝ) :
    F.polE n π (fun y => |R y|) x ≤
      act (F.measOf j₀ ^ n) (fun y => |R y|) x + ∫ w, |R' (x - w)| * F.Wd n w := by
  have hRc : Continuous R := continuous_iff_continuousAt.2 fun y => (hR y).continuousAt
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set k : ℝ → ℝ := fun y => Real.sqrt (R y ^ 2 + ε ^ 2) - ε
  set k' : ℝ → ℝ := fun y => R y * R' y / Real.sqrt (R y ^ 2 + ε ^ 2)
  have hpos : ∀ y, 0 < Real.sqrt (R y ^ 2 + ε ^ 2) := fun y => Real.sqrt_pos.2 (by positivity)
  have hk : ∀ y, HasDerivAt k (k' y) y := fun y => by
    have h1 : HasDerivAt (fun y => R y ^ 2 + ε ^ 2) (2 * R y * R' y) y := by
      have := ((hR y).mul (hR y)).add_const (ε ^ 2)
      convert this using 1
      · funext z; simp only [Pi.mul_apply]; ring
      · ring
    have h2 := h1.sqrt (by positivity)
    convert h2.sub_const ε using 1
    simp only [k']
    field_simp
  have hRle : ∀ y, |R y| ≤ Real.sqrt (R y ^ 2 + ε ^ 2) := fun y => by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith)
  have hk'le : ∀ y, |k' y| ≤ |R' y| := fun y => by
    simp only [k', abs_div, abs_mul, abs_of_pos (hpos y)]
    rw [div_le_iff₀ (hpos y)]
    calc |R y| * |R' y| ≤ Real.sqrt (R y ^ 2 + ε ^ 2) * |R' y| :=
          mul_le_mul_of_nonneg_right (hRle y) (abs_nonneg _)
      _ = _ := by ring
  have hk'c : Continuous k' :=
    (hRc.mul hR'c).div (((hRc.pow 2).add continuous_const).sqrt) fun y => (hpos y).ne'
  have hk'i : Integrable k' :=
    hR'i.mono hk'c.aestronglyMeasurable (ae_of_all _ fun y => by
      simpa only [Real.norm_eq_abs] using hk'le y)
  have hklim : Tendsto k atBot (𝓝 0) := by
    have := (((hlim.pow 2).add_const (ε ^ 2)).sqrt).sub_const ε
    simpa [Real.sqrt_sq hε.le] using this
  have hup : ∀ y, |R y| ≤ k y + ε := fun y => by simp only [k]; linarith [hRle y]
  have hdown : ∀ y, k y ≤ |R y| := fun y => by
    simp only [k]
    have : Real.sqrt (R y ^ 2 + ε ^ 2) ≤ |R y| + ε := by
      rw [Real.sqrt_le_left (by positivity)]
      nlinarith [abs_nonneg (R y), sq_abs (R y)]
    linarith
  have s1 := F.polE_mono hup n π x
  rw [F.polE_add_const] at s1
  have s2 := F.polE_mono hdown n (F.refPol j₀ n) x
  rw [F.polE_refPol, F.polE_refPol] at s2
  have i1 := F.polE_ibp hk hk'i hklim n π x
  have i2 := F.polE_ibp hk hk'i hklim n (F.refPol j₀ n) x
  rw [F.polE_refPol] at i2
  have hdiff : F.polE n π k x - act (F.measOf j₀ ^ n) k x ≤ ∫ w, |R' (x - w)| * F.Wd n w := by
    rw [i1, i2, ← integral_sub (F.integrable_mul_polE hk'i n π x)
      (F.integrable_mul_polE hk'i n _ x)]
    refine integral_mono ((F.integrable_mul_polE hk'i n π x).sub (F.integrable_mul_polE hk'i n _ x))
      (F.integrable_mul_Wd hR'i n x) fun w => ?_
    simp only
    rw [← mul_sub]
    refine (le_abs_self _).trans ?_
    rw [abs_mul]
    exact mul_le_mul (hk'le _) (F.abs_polE_sub_le n π _ w) (abs_nonneg _) (abs_nonneg _)
  linarith


/-! ### Integrated form -/

theorem ofReal_conv_Wd {k : ℝ → ℝ} (hki : Integrable k) (n : ℕ) (x : ℝ) :
    ENNReal.ofReal (∫ w, |k (x - w)| * F.Wd n w) =
      ∫⁻ w, ENNReal.ofReal (|k (x - w)| * F.Wd n w) :=
  ofReal_integral_eq_lintegral_ofReal (F.integrable_mul_Wd hki n x)
    (ae_of_all _ fun w => mul_nonneg (abs_nonneg _) (F.Wd_bounds n w).1)

theorem measurable_conv_Wd {k : ℝ → ℝ} (hk : Continuous k) (n : ℕ) :
    Measurable (Function.uncurry fun x w => ENNReal.ofReal (|k (x - w)| * F.Wd n w)) := by
  refine ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)
  · exact (hk.comp (continuous_fst.sub continuous_snd)).abs.measurable
  · exact (F.measurable_Wd n).comp measurable_snd

theorem lintegral_conv_Wd {k : ℝ → ℝ} (hk : Continuous k) (n : ℕ) :
    ∫⁻ x, ∫⁻ w, ENNReal.ofReal (|k (x - w)| * F.Wd n w) =
      (∫⁻ x, ‖k x‖ₑ) * ∫⁻ w, ENNReal.ofReal (F.Wd n w) := by
  have hm := F.measurable_conv_Wd hk n
  have hkm := hk.measurable
  calc ∫⁻ x, ∫⁻ w, ENNReal.ofReal (|k (x - w)| * F.Wd n w)
      = ∫⁻ w, ∫⁻ x, ENNReal.ofReal (|k (x - w)| * F.Wd n w) := lintegral_lintegral_swap hm.aemeasurable
    _ = ∫⁻ w, (∫⁻ x, ‖k x‖ₑ) * ENNReal.ofReal (F.Wd n w) := by
        refine lintegral_congr fun w => ?_
        simp_rw [ENNReal.ofReal_mul (abs_nonneg _)]
        rw [lintegral_mul_const _ (by fun_prop : Measurable fun x => ENNReal.ofReal |k (x - w)|)]
        congr 1
        have := lintegral_sub_right_eq_self (μ := volume) (fun x => ‖k x‖ₑ) w
        rw [← this]; exact lintegral_congr fun x => by rw [Real.enorm_eq_ofReal_abs]
    _ = _ := by rw [lintegral_const_mul _ (F.measurable_Wd n).ennreal_ofReal]

/-- `W_n = ∫ (U_n - G_n)`. -/
def Wint (n : ℕ) : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (F.Wd n w)

theorem polE_zero : ∀ (n : ℕ) (π : F.APol n) (x : ℝ), F.polE n π (fun _ => 0) x = 0
  | 0, _, _ => rfl
  | n + 1, π, x => by simp only [polE, polE_zero n, mul_zero, Finset.sum_const_zero]

theorem ofReal_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ENNReal.ofReal (∑ i ∈ s, f i) ≤ ∑ i ∈ s, ENNReal.ofReal (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ENNReal.ofReal_add_le.trans (add_le_add le_rfl ih)

theorem polE_nonneg {g : ℝ → ℝ} (h : ∀ x, 0 ≤ g x) :
    ∀ (n : ℕ) (π : F.APol n) (x : ℝ), 0 ≤ F.polE n π g x := fun n π x => by
  have := F.polE_mono h n π x
  rw [F.polE_zero] at this; exact this

/-- The data of the contraction: reference action, the smoothing CDF `Ψ` of width `A`, and
the defects `R_{a,r} = (E_a - E_{j₀})(μ₀^r * Ψ)` with their derivatives. -/
structure WidthData where
  j₀ : Fin F.nA
  Ψ : ℝ → ℝ
  A : ℝ
  hA : 0 ≤ A
  hΨ : ∀ x, 0 ≤ Ψ x ∧ Ψ x ≤ 1
  hΨm : Measurable Ψ
  hΨ0 : ∀ x, x < -A → Ψ x = 0
  hΨ1 : ∀ x, A ≤ x → Ψ x = 1
  R' : Fin F.nA → ℕ → ℝ → ℝ
  hR : ∀ a r y, HasDerivAt (fun x => F.expect a (act (F.measOf j₀ ^ r) Ψ) x -
    F.expect j₀ (act (F.measOf j₀ ^ r) Ψ) x) (R' a r y) y
  hR'c : ∀ a r, Continuous (R' a r)
  hR'i : ∀ a r, Integrable (R' a r)
  hlim : ∀ a r, Tendsto (fun x => F.expect a (act (F.measOf j₀ ^ r) Ψ) x -
    F.expect j₀ (act (F.measOf j₀ ^ r) Ψ) x) atBot (𝓝 0)

namespace WidthData
variable {F} (D : F.WidthData)

/-- The defect `R_{a,r}`. -/
def Rf (a : Fin F.nA) (r : ℕ) (x : ℝ) : ℝ :=
  F.expect a (act (F.measOf D.j₀ ^ r) D.Ψ) x - F.expect D.j₀ (act (F.measOf D.j₀ ^ r) D.Ψ) x

/-- `α_r = Σ_a ∫ |R_{a,r}|`. -/
def α (r : ℕ) : ℝ≥0∞ := ∑ a, ∫⁻ x, ‖D.Rf a r x‖ₑ

/-- `β_r = Σ_a ∫ |R'_{a,r}|`. -/
def β (r : ℕ) : ℝ≥0∞ := ∑ a, ∫⁻ x, ‖D.R' a r x‖ₑ

theorem Kf_eq (r : ℕ) (x : ℝ) : F.Kf D.j₀ D.Ψ r x = ∑ a, |D.Rf a r x| := rfl

theorem measurable_Rf (a r) : Measurable (D.Rf a r) :=
  (continuous_iff_continuousAt.2 fun y => (D.hR a r y).continuousAt).measurable

theorem lintegral_U_Kf (i r : ℕ) :
    ∫⁻ x, ENNReal.ofReal (F.U i (F.Kf D.j₀ D.Ψ r) x) ≤ D.α r + D.β r * F.Wint i := by
  have hpt : ∀ x, F.U i (F.Kf D.j₀ D.Ψ r) x ≤ ∑ a, (act (F.measOf D.j₀ ^ i) (fun y => |D.Rf a r y|) x +
      ∫ w, |D.R' a r (x - w)| * F.Wd i w) := fun x => by
    obtain ⟨σ, hσ⟩ := (F.U_envelope (F.Kf D.j₀ D.Ψ r) i x).2
    rw [← hσ, show F.Kf D.j₀ D.Ψ r = fun y => ∑ a, |D.Rf a r y| from rfl,
      F.polE_sum Finset.univ (fun a y => |D.Rf a r y|) i σ x]
    exact Finset.sum_le_sum fun a _ =>
      F.polE_abs_le (D.hR a r) (D.hR'c a r) (D.hR'i a r) (D.hlim a r) D.j₀ i σ x
  have hnn : ∀ a x, 0 ≤ act (F.measOf D.j₀ ^ i) (fun y => |D.Rf a r y|) x := fun a x => by
    rw [← F.polE_refPol]; exact F.polE_nonneg (fun _ => abs_nonneg _) _ _ _
  have hRa : ∀ a, Measurable fun y => |D.Rf a r y| := fun a =>
    continuous_abs.measurable.comp (D.measurable_Rf a r)
  calc ∫⁻ x, ENNReal.ofReal (F.U i (F.Kf D.j₀ D.Ψ r) x)
      ≤ ∫⁻ x, ∑ a, (ENNReal.ofReal (act (F.measOf D.j₀ ^ i) (fun y => |D.Rf a r y|) x) +
          ∫⁻ w, ENNReal.ofReal (|D.R' a r (x - w)| * F.Wd i w)) := by
        refine lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (hpt x)).trans
          ((ofReal_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_))
        rw [← F.ofReal_conv_Wd (D.hR'i a r)]
        exact ENNReal.ofReal_add_le
    _ = ∑ a, ((∫⁻ x, ENNReal.ofReal (act (F.measOf D.j₀ ^ i) (fun y => |D.Rf a r y|) x)) +
          ∫⁻ x, ∫⁻ w, ENNReal.ofReal (|D.R' a r (x - w)| * F.Wd i w)) := by
        rw [lintegral_finsetSum']
        · refine Finset.sum_congr rfl fun a _ => ?_
          rw [lintegral_add_left]
          exact (measurable_act _ (hRa a)).ennreal_ofReal
        · intro a _
          exact (((measurable_act _ (hRa a)).ennreal_ofReal).add
            (F.measurable_conv_Wd (D.hR'c a r) i).lintegral_prod_right').aemeasurable
    _ ≤ ∑ a, ((∫⁻ x, ‖D.Rf a r x‖ₑ) + (∫⁻ x, ‖D.R' a r x‖ₑ) * F.Wint i) := by
        refine Finset.sum_le_sum fun a _ => add_le_add ?_ (le_of_eq ?_)
        · refine le_trans ?_ ((lintegral_act_le (F.measOf D.j₀ ^ i) (hRa a)).trans ?_)
          · exact lintegral_mono fun x => by
              rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn a x)]
          · have e : ∀ x, ‖|D.Rf a r x|‖ₑ = ‖D.Rf a r x‖ₑ := fun x => by
              rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_abs]
            simp only [e]
            calc ENNReal.ofReal (tv (F.measOf D.j₀ ^ i)) * ∫⁻ x, ‖D.Rf a r x‖ₑ
                ≤ 1 * ∫⁻ x, ‖D.Rf a r x‖ₑ := by
                  gcongr; exact ENNReal.ofReal_le_one.2 (F.tv_measOf_pow _ _)
              _ = _ := one_mul _
        · exact F.lintegral_conv_Wd (D.hR'c a r) i
    _ = D.α r + D.β r * F.Wint i := by
        rw [Finset.sum_add_distrib, α, β, Finset.sum_mul]


theorem _root_.CausalSpectrum.Sqrt.IncFamily.measurable_U (F : IncFamily) {g : ℝ → ℝ}
    (hg : Measurable g) : ∀ n, Measurable (F.U n g)
  | 0 => hg
  | n + 1 => by
    have e : F.U (n + 1) g = Finset.univ.sup' F.univ_nonempty (fun j => F.expect j (F.U n g)) := by
      funext x; simp only [U, Tmax, Finset.sup'_apply]
    rw [e]
    refine Finset.measurable_sup' _ fun j _ => ?_
    have : F.expect j (F.U n g) = act (F.measOf j) (F.U n g) := funext fun x => F.expect_eq_act j _ x
    rw [this]; exact measurable_act _ (F.measurable_U hg n)

/-- `S_n(y) = Σ_{i<n} U_i(K_{n-1-i})(y)`. -/
def S (n : ℕ) (y : ℝ) : ℝ := ∑ i ∈ Finset.range n, F.U i (F.Kf D.j₀ D.Ψ (n - 1 - i)) y

theorem measurable_S (n : ℕ) : Measurable (D.S n) := by
  refine Finset.measurable_sum _ fun i _ => F.measurable_U ?_ i
  exact Finset.measurable_sum _ fun a _ => continuous_abs.measurable.comp (D.measurable_Rf a _)

theorem S_nonneg (n : ℕ) (y : ℝ) : 0 ≤ D.S n y := by
  refine Finset.sum_nonneg fun i _ => ?_
  obtain ⟨σ, hσ⟩ := (F.U_envelope (F.Kf D.j₀ D.Ψ (n - 1 - i)) i y).2
  rw [← hσ]; exact F.polE_nonneg (fun _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) _ _ _

theorem H_le_Ψ (y : ℝ) : F.G 0 y ≤ D.Ψ (y + D.A) := by
  simp only [G]
  split_ifs with h
  · rw [D.hΨ1 _ (by linarith)]
  · exact (D.hΨ _).1

theorem Ψ_le_H (y : ℝ) : D.Ψ (y + -D.A) ≤ F.G 0 y := by
  simp only [G]
  split_ifs with h
  · exact (D.hΨ _).2
  · rw [D.hΨ0 _ (by push_neg at h; linarith)]

/-- **Pointwise width bound** through the smoothed walk. -/
theorem Wd_le (n : ℕ) (x : ℝ) : F.Wd n x ≤
    (act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) - act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A)) +
      D.S n (x + D.A) + D.S n (x - D.A) := by
  obtain ⟨π₁, h₁⟩ := (F.U_envelope (F.G 0) n x).2
  obtain ⟨π₂, h₂⟩ := (F.G_envelope n x).2
  rw [F.cdfPol_eq_polE] at h₂
  have u1 := F.polE_mono D.H_le_Ψ n π₁ x
  rw [F.polE_translate] at u1
  have u2 := (abs_le.1 (F.telescope D.j₀ D.Ψ n π₁ (x + D.A))).2
  have l1 := F.polE_mono D.Ψ_le_H n π₂ x
  rw [F.polE_translate] at l1
  have l2 := (abs_le.1 (F.telescope D.j₀ D.Ψ n π₂ (x + -D.A))).1
  simp only [Wd, S, ← h₁, ← h₂, ← sub_eq_add_neg] at *
  linarith

theorem lintegral_shift_Ψ (n : ℕ) :
    ∫⁻ x, ENNReal.ofReal (act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) - act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A))
      ≤ ENNReal.ofReal (4 * D.A) := by
  set φ : ℝ → ℝ := fun y => D.Ψ (y + D.A) - D.Ψ (y - D.A)
  have hφm : Measurable φ := (D.hΨm.comp (measurable_id.add_const _)).sub
    (D.hΨm.comp (measurable_id.sub_const _))
  have e : ∀ x, act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) - act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A) =
      act (F.measOf D.j₀ ^ n) φ x := fun x => by
    simp only [act_eq_sum, φ, mul_sub, Finset.sum_sub_distrib]
    congr 1 <;> exact Finset.sum_congr rfl fun z _ => by ring_nf
  simp_rw [e]
  refine (lintegral_mono fun x => ?_).trans ((lintegral_act_le (F.measOf D.j₀ ^ n) hφm).trans ?_)
  · rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  · have hpt : ∀ y, ‖φ y‖ₑ ≤ (Set.Icc (-(2 * D.A)) (2 * D.A)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
      intro y
      by_cases hy : y ∈ Set.Icc (-(2 * D.A)) (2 * D.A)
      · rw [Set.indicator_of_mem hy, Real.enorm_eq_ofReal_abs, ENNReal.ofReal_le_one]
        have := D.hΨ (y + D.A); have := D.hΨ (y - D.A)
        rw [abs_le]; constructor <;> simp only [φ] <;> linarith
      · rw [Set.indicator_of_notMem hy]
        simp only [Set.mem_Icc, not_and_or, not_le] at hy
        have hA := D.hA
        have : φ y = 0 := by
          rcases hy with hy | hy
          · simp only [φ]; rw [D.hΨ0 _ (by linarith), D.hΨ0 _ (by linarith)]; ring
          · simp only [φ]; rw [D.hΨ1 _ (by linarith), D.hΨ1 _ (by linarith)]; ring
        simp [this]
    calc ENNReal.ofReal (tv (F.measOf D.j₀ ^ n)) * ∫⁻ y, ‖φ y‖ₑ ≤ 1 * ∫⁻ y,
          (Set.Icc (-(2 * D.A)) (2 * D.A)).indicator (fun _ => (1 : ℝ≥0∞)) y := by
          gcongr
          · exact ENNReal.ofReal_le_one.2 (F.tv_measOf_pow _ _)
          · exact hpt _
      _ = ENNReal.ofReal (4 * D.A) := by
          rw [one_mul, lintegral_indicator measurableSet_Icc, setLIntegral_const, one_mul,
            Real.volume_Icc]; congr 1; ring

/-- **Width recursion.** `W_n ≤ 4A + 2 Σ_{i<n} (α_{n-1-i} + β_{n-1-i} W_i)`. -/
theorem Wint_le (n : ℕ) : F.Wint n ≤ ENNReal.ofReal (4 * D.A) +
    2 * ∑ i ∈ Finset.range n, (D.α (n - 1 - i) + D.β (n - 1 - i) * F.Wint i) := by
  have hSm := D.measurable_S n
  have hint : ∫⁻ x, ENNReal.ofReal (D.S n x) ≤
      ∑ i ∈ Finset.range n, (D.α (n - 1 - i) + D.β (n - 1 - i) * F.Wint i) := by
    calc ∫⁻ x, ENNReal.ofReal (D.S n x)
        ≤ ∫⁻ x, ∑ i ∈ Finset.range n, ENNReal.ofReal (F.U i (F.Kf D.j₀ D.Ψ (n - 1 - i)) x) :=
          lintegral_mono fun x => ofReal_sum_le _ _
      _ = ∑ i ∈ Finset.range n, ∫⁻ x, ENNReal.ofReal (F.U i (F.Kf D.j₀ D.Ψ (n - 1 - i)) x) := by
          refine lintegral_finsetSum _ fun i _ => (F.measurable_U ?_ i).ennreal_ofReal
          exact Finset.measurable_sum _ fun a _ => continuous_abs.measurable.comp (D.measurable_Rf a _)
      _ ≤ _ := Finset.sum_le_sum fun i _ => D.lintegral_U_Kf i _
  have t1 : ∫⁻ x, ENNReal.ofReal (D.S n (x + D.A)) = ∫⁻ x, ENNReal.ofReal (D.S n x) :=
    lintegral_add_right_eq_self (fun x => ENNReal.ofReal (D.S n x)) D.A
  have t2 : ∫⁻ x, ENNReal.ofReal (D.S n (x - D.A)) = ∫⁻ x, ENNReal.ofReal (D.S n x) :=
    lintegral_sub_right_eq_self (fun x => ENNReal.ofReal (D.S n x)) D.A
  have hm1 : Measurable fun x => ENNReal.ofReal (act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) -
      act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A)) :=
    (((measurable_act _ D.hΨm).comp (measurable_id.add_const _)).sub
      ((measurable_act _ D.hΨm).comp (measurable_id.sub_const _))).ennreal_ofReal
  calc F.Wint n ≤ ∫⁻ x, (ENNReal.ofReal (act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) -
          act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A)) + ENNReal.ofReal (D.S n (x + D.A)) +
          ENNReal.ofReal (D.S n (x - D.A))) := by
        refine lintegral_mono fun x => (ENNReal.ofReal_le_ofReal (D.Wd_le n x)).trans ?_
        exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
    _ = (∫⁻ x, ENNReal.ofReal (act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) -
          act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A))) + (∫⁻ x, ENNReal.ofReal (D.S n (x + D.A))) +
          ∫⁻ x, ENNReal.ofReal (D.S n (x - D.A)) := by
        have hm2 : Measurable fun x => ENNReal.ofReal (act (F.measOf D.j₀ ^ n) D.Ψ (x + D.A) -
            act (F.measOf D.j₀ ^ n) D.Ψ (x - D.A)) + ENNReal.ofReal (D.S n (x + D.A)) :=
          hm1.add (hSm.comp (measurable_id.add_const _)).ennreal_ofReal
        rw [lintegral_add_left hm2, lintegral_add_left hm1]
    _ ≤ _ := by
        rw [t1, t2, two_mul, ← add_assoc]
        exact add_le_add (add_le_add (D.lintegral_shift_Ψ n) hint) hint

end WidthData

/-- **Solving the recursion.** If `W_n ≤ c_n + Σ_{i<n} b_{n-1-i} W_i` with `c` monotone and
`Σ_{r<n} b_r ≤ 1/2`, then `W_n ≤ 2 c_n`. -/
theorem recursion_solve (W c b : ℕ → ℝ≥0∞) (hc : Monotone c)
    (hb : ∀ n, ∑ r ∈ Finset.range n, b r ≤ 1 / 2)
    (hW : ∀ n, W n ≤ c n + ∑ i ∈ Finset.range n, b (n - 1 - i) * W i) : ∀ n, W n ≤ 2 * c n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    refine (hW n).trans ?_
    have : ∑ i ∈ Finset.range n, b (n - 1 - i) * W i ≤ ∑ i ∈ Finset.range n, b (n - 1 - i) * (2 * c n) :=
      Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left
        ((ih i (Finset.mem_range.1 hi)).trans (mul_le_mul_of_nonneg_left (hc (Finset.mem_range.1 hi).le)
          zero_le')) zero_le'
    refine (add_le_add le_rfl this).trans ?_
    rw [← Finset.sum_mul, Finset.sum_range_reflect b n]
    calc c n + (∑ r ∈ Finset.range n, b r) * (2 * c n) ≤ c n + 1 / 2 * (2 * c n) := by
          gcongr; exact hb n
      _ = 2 * c n := by
          rw [← mul_assoc, ENNReal.div_mul_cancel (by norm_num) (by norm_num), one_mul, two_mul]

end CausalSpectrum.Sqrt.IncFamily

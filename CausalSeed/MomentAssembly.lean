import CausalSeed.MomentUpper
import Mathlib.NumberTheory.Harmonic.Bounds
import CausalSeed.MomentLower

/-!
# Upper bounds of the moment classification

Assembly of the Taylor bound (`MomentTaylor`), the total-variation decay (`MomentDecay`)
and the width contraction (`MomentWidth`, `MomentUpper`):

* equal variances: `e(G_n) ≤ C (1 + log n)`;
* equal variances and equal third moments: `e(G_n) ≤ C`.

The **nondegeneracy hypothesis** is on one reference action `j₀`: its law contains a
symmetric pair, `μ_{j₀} = ρ δ_c (δ_{-b}+δ_b)/2 + ζ` with `b > 0`, `0 < ρ ≤ 1` and
`tv ζ ≤ 1 - ρ` (`Nondeg`). Any law with two distinct atoms has this
form (`nondeg_of_two_atoms`). The moment hypotheses are required for **all** actions against
`j₀`; there is no restriction on the number of actions.
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal

namespace CausalSpectrum.Sqrt.Decay
open AddMonoidAlgebra

/-- `g(r) = (r+1)^{-3/2}`. -/
noncomputable def gg (r : ℕ) : ℝ := 1 / ((r + 1) * Real.sqrt (r + 1))

theorem gg_nonneg (r : ℕ) : 0 ≤ gg r := by unfold gg; positivity

theorem gg_le_tel {r : ℕ} (hr : 1 ≤ r) :
    gg r ≤ 2 * (1 / Real.sqrt r - 1 / Real.sqrt (r + 1)) := by
  have hr' : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hu0 : 0 < Real.sqrt r := Real.sqrt_pos.2 (by linarith)
  have hv0 : 0 < Real.sqrt (r + 1) := Real.sqrt_pos.2 (by linarith)
  have hu2 : Real.sqrt r ^ 2 = r := Real.sq_sqrt (by linarith)
  have hv2 : Real.sqrt (r + 1) ^ 2 = r + 1 := Real.sq_sqrt (by linarith)
  have huv : Real.sqrt r ≤ Real.sqrt (r + 1) := Real.sqrt_le_sqrt (by linarith)
  unfold gg
  set u := Real.sqrt r
  set v := Real.sqrt (r + 1)
  rw [← hv2]
  have h1 : v ^ 2 = u ^ 2 + 1 := by rw [hv2, hu2]
  rw [← sub_nonneg]
  have e : 2 * (1 / u - 1 / v) - 1 / (v ^ 2 * v) = (2 * v ^ 2 * (v - u) - u) / (u * v ^ 3) := by
    field_simp
  rw [e]
  refine div_nonneg ?_ (by positivity)
  have hp : 0 ≤ (v - u) * (2 * v ^ 2 - u * v - u ^ 2) :=
    mul_nonneg (sub_nonneg.2 huv) (by nlinarith)
  have : 2 * v ^ 2 * (v - u) - u = (v - u) * (2 * v ^ 2 - u * v - u ^ 2) := by
    linear_combination u * h1
  rw [this]; exact hp

theorem sum_Ico_gg_le {N : ℕ} (hN : 1 ≤ N) : ∀ M, N ≤ M →
    ∑ r ∈ Ico N M, gg r ≤ 2 / Real.sqrt N - 2 / Real.sqrt M := by
  intro M
  induction M with
  | zero => intro h; omega
  | succ M ih =>
    intro h
    by_cases hM : N ≤ M
    · rw [sum_Ico_succ_top hM]
      have := gg_le_tel (r := M) (hN.trans hM)
      have := ih hM
      have h' : 2 * (1 / Real.sqrt M - 1 / Real.sqrt (M + 1)) = 2 / Real.sqrt M - 2 / Real.sqrt (M + 1) := by
        ring
      push_cast
      linarith
    · have : N = M + 1 := by omega
      subst this; simp

theorem sum_Ico_gg_le' {N : ℕ} (hN : 1 ≤ N) (M : ℕ) :
    ∑ r ∈ Ico N M, gg r ≤ 2 / Real.sqrt N := by
  by_cases h : N ≤ M
  · have := sum_Ico_gg_le hN M h
    have : 0 ≤ 2 / Real.sqrt M := by positivity
    linarith
  · rw [Ico_eq_empty_of_le (by omega), sum_empty]; positivity

/-- Splitting a partial sum at `N`: `Σ_{r<n} t_r ≤ N X + 2K/√N` if `t ≤ X` and `t_r ≤ K g(r)`. -/
theorem sum_split (t : ℕ → ℝ) {X K : ℝ} (hK : 0 ≤ K) {N : ℕ} (hN : 1 ≤ N)
    (ht : ∀ r, 0 ≤ t r) (h1 : ∀ r, t r ≤ X) (h2 : ∀ r, t r ≤ K * gg r) (n : ℕ) :
    ∑ r ∈ range n, t r ≤ N * X + K * (2 / Real.sqrt N) := by
  calc ∑ r ∈ range n, t r ≤ ∑ r ∈ range (max n N), t r :=
        sum_le_sum_of_subset_of_nonneg (range_subset_range.2 (le_max_left _ _)) fun r _ _ => ht r
    _ = ∑ r ∈ range N, t r + ∑ r ∈ Ico N (max n N), t r :=
        (sum_range_add_sum_Ico _ (le_max_right _ _)).symm
    _ ≤ N * X + K * (2 / Real.sqrt N) := by
        refine add_le_add ((sum_le_sum fun r _ => h1 r).trans (by simp)) ?_
        refine (sum_le_sum fun r _ => h2 r).trans ?_
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_Ico_gg_le' hN _) hK

variable {b c ρ : ℝ} {ζ : Meas}

theorem tv_decay_three_gg (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hζ : tv ζ ≤ 1 - ρ) (r : ℕ) :
    tv (dB b ^ 3 * mix ρ b c ζ ^ r) ≤ 24 * Real.sqrt 3 * Real.sqrt (2 / ρ ^ 3) * gg r := by
  refine (tv_decay_three b c h0 h1 hζ r).trans ?_
  rw [mul_assoc (24 * Real.sqrt 3)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hx : (0:ℝ) < r + 1 := by positivity
  calc Real.sqrt (1 / (ρ * (r + 1)) * (2 / (ρ ^ 2 * ((r + 1) * (r + 2)))))
      ≤ Real.sqrt (2 / ρ ^ 3 * (gg r) ^ 2) := by
        apply Real.sqrt_le_sqrt
        have hg : gg r ^ 2 = 1 / (r + 1) ^ 3 := by
          unfold gg; rw [div_pow, mul_pow, Real.sq_sqrt hx.le]; ring
        rw [hg, div_mul_div_comm, div_mul_div_comm, one_mul, mul_one]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : ρ * (r + 1) * (ρ ^ 2 * ((r + 1) * (r + 2))) = ρ ^ 3 * (r + 1) ^ 3 + ρ ^ 3 * (r + 1) ^ 2 := by
          ring
        rw [this]; exact le_add_of_nonneg_right (by positivity)
    _ = Real.sqrt (2 / ρ ^ 3) * gg r := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (gg_nonneg r)]

theorem tv_decay_four_gg (h0 : 0 < ρ) (h1 : ρ ≤ 1) (hζ : tv ζ ≤ 1 - ρ) (r : ℕ) :
    tv (dB b ^ 4 * mix ρ b c ζ ^ r) ≤ 512 / ρ ^ 2 * gg r := by
  refine (tv_decay_four b c h0 h1 hζ r).trans ?_
  have hx : (0:ℝ) < r + 1 := by positivity
  rw [gg, mul_one_div, div_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ hx.le) (by positivity)
  nlinarith [Real.sq_sqrt hx.le, Real.sqrt_nonneg ((r:ℝ) + 1)]

/-- With `Δ = Dif(L b)`, the partial sums of `tv(μ^r Δ^q)` can be made small by taking `L`
large, provided `tv(dB_b^q μ^r) ≤ K g(r)`. -/
theorem small_sum {μ : Meas} (hμ : ∀ r, tv (μ ^ r) ≤ 1) (hb : 0 < b) {q : ℕ} (hq : 1 ≤ q) {K : ℝ}
    (hK : 0 ≤ K) (hdec : ∀ r, tv (dB b ^ q * μ ^ r) ≤ K * gg r) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, 0 < L ∧ ∀ n, ∑ r ∈ range n, tv (μ ^ r * Dif (L * b) ^ q) ≤ ε := by
  set K' := (1 / (2 * b)) ^ q * K
  have hK' : 0 ≤ K' := by positivity
  have ht : Tendsto (fun N : ℕ => K' * (2 * (Real.sqrt N)⁻¹)) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.comp
      (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).const_mul 2).const_mul K'
  obtain ⟨N, hN1, hNe⟩ := ((eventually_ge_atTop 1).and (ht.eventually (gt_mem_nhds (half_pos hε)))).exists
  obtain ⟨L, hL⟩ := exists_nat_ge (1 / b + (2 * N / ε) / b)
  have hq1 : 0 ≤ 2 * (N : ℝ) / ε / b := by positivity
  have hL1 : 1 / b ≤ L := by linarith
  have hL2 : 2 * (N : ℝ) / ε / b ≤ L := by linarith [one_div_pos.2 hb]
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le (one_div_pos.2 hb) hL1
  refine ⟨L, by exact_mod_cast hLpos, fun n => ?_⟩
  have hLb : 0 < (L : ℝ) * b := mul_pos hLpos hb
  have hLb1 : 1 ≤ (L : ℝ) * b := (div_le_iff₀ hb).1 hL1
  have hLb2 : 2 * (N : ℝ) / ε ≤ L * b := (div_le_iff₀ hb).1 hL2
  have hLb2' : 2 * (N : ℝ) ≤ L * b * ε := (div_le_iff₀ hε).1 hLb2
  set x := 1 / ((L : ℝ) * b)
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [div_le_one hLb]; exact hLb1
  have hNx : (N : ℝ) * x ≤ ε / 2 := by
    rw [mul_one_div, div_le_iff₀ hLb]; nlinarith
  have hLn : 0 < L := by exact_mod_cast hLpos
  refine (sum_split _ hK' hN1 (fun r => tv_nonneg _) (X := x) (fun r => ?_) (fun r => ?_) n).trans ?_
  · refine (tv_mul_Dif_pow_le hLb _ q).trans ?_
    calc tv (μ ^ r) * x ^ q ≤ 1 * x := mul_le_mul (hμ r) (pow_le_of_le_one hx0 hx1 (by omega))
          (pow_nonneg hx0 _) zero_le_one
      _ = x := one_mul x
  · refine (tv_Dif_scale b hb hLn q _).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hdec r) (by positivity)
  · have : K' * (2 / Real.sqrt N) = K' * (2 * (Real.sqrt N)⁻¹) := by rw [div_eq_mul_inv]
    rw [this]; linarith

/-- The harmonic bound `Σ_{r<n} 1/(r+1) ≤ 1 + log n`. -/
theorem sum_inv_le_log (n : ℕ) : ∑ r ∈ range n, (1 : ℝ) / (r + 1) ≤ 1 + Real.log n := by
  have := harmonic_le_one_add_log n
  simpa [harmonic, one_div] using this

end CausalSpectrum.Sqrt.Decay

namespace CausalSpectrum.Sqrt.IncFamily
open Decay AddMonoidAlgebra
variable (F : IncFamily)

/-- **Nondegeneracy** of a reference action: its law contains a symmetric pair of atoms. -/
def Nondeg (j₀ : Fin F.nA) : Prop :=
  ∃ ρ b c : ℝ, ∃ ζ : Meas, 0 < ρ ∧ ρ ≤ 1 ∧ 0 < b ∧ tv ζ ≤ 1 - ρ ∧ F.measOf j₀ = mix ρ b c ζ

theorem nondeg_of_lt (j₀ : Fin F.nA) {y₁ y₂ : Fin (F.nY j₀)} (hlt : F.X j₀ y₁ < F.X j₀ y₂) :
    F.Nondeg j₀ := by
  have hne : y₁ ≠ y₂ := fun h => by rw [h] at hlt; exact lt_irrefl _ hlt
  set u := F.X j₀ y₁ with hu
  set v := F.X j₀ y₂ with hv
  set p := F.P j₀ y₁ with hpd
  set q := F.P j₀ y₂ with hqd
  set ρ := 2 * min p q
  set s := (Finset.univ.erase y₁).erase y₂
  have hy2 : y₂ ∈ Finset.univ.erase y₁ := Finset.mem_erase.2 ⟨hne.symm, Finset.mem_univ _⟩
  have hsplit : ∀ f : Fin (F.nY j₀) → ℝ, ∑ y, f y = f y₁ + (f y₂ + ∑ y ∈ s, f y) := fun f => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y₁), ← Finset.add_sum_erase _ _ hy2]
  have hsplitM : ∀ f : Fin (F.nY j₀) → Meas, ∑ y, f y = f y₁ + (f y₂ + ∑ y ∈ s, f y) := fun f => by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y₁), ← Finset.add_sum_erase _ _ hy2]
  have hsum := F.Psum j₀
  rw [hsplit] at hsum
  have hs0 : 0 ≤ ∑ y ∈ s, F.P j₀ y := Finset.sum_nonneg fun y _ => (F.Ppos _ _).le
  have hp := F.Ppos j₀ y₁
  have hq := F.Ppos j₀ y₂
  have hmp : min p q ≤ p := min_le_left _ _
  have hmq : min p q ≤ q := min_le_right _ _
  have hm0 : 0 < min p q := lt_min hp hq
  refine ⟨ρ, (v - u) / 2, (u + v) / 2,
    ∑ y ∈ s, single (F.X j₀ y) (F.P j₀ y) + single u (p - ρ / 2) + single v (q - ρ / 2),
    by positivity, by linarith, by linarith, ?_, ?_⟩
  · refine (tv_add_le _ _).trans ?_
    refine (add_le_add (tv_add_le _ _) le_rfl).trans ?_
    refine (add_le_add (add_le_add (tv_sum_le _ _) le_rfl) le_rfl).trans (le_of_eq ?_)
    simp only [tv_single, abs_of_pos (F.Ppos _ _)]
    rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
    linarith
  · rw [measOf, hsplitM, mix, ← hu, ← hv, ← hpd, ← hqd]
    unfold Decay.sB
    rw [mul_add, single_mul_single, single_mul_single, smul_add,
      smul_single, smul_single, mul_one, smul_eq_mul]
    have e1 : (u + v) / 2 + -((v - u) / 2) = u := by ring
    have e2 : (u + v) / 2 + (v - u) / 2 = v := by ring
    rw [e1, e2]
    have f1 : (single u p : Meas) = single u (p - ρ / 2) + single u (ρ * (1 / 2)) := by
      rw [← single_add]; congr 1; ring
    have f2 : (single v q : Meas) = single v (q - ρ / 2) + single v (ρ * (1 / 2)) := by
      rw [← single_add]; congr 1; ring
    rw [f1, f2]; abel

/-- Any action whose information law has two distinct values is nondegenerate. -/
theorem nondeg_of_ne (j₀ : Fin F.nA) {y₁ y₂ : Fin (F.nY j₀)} (hne : F.X j₀ y₁ ≠ F.X j₀ y₂) :
    F.Nondeg j₀ := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact F.nondeg_of_lt j₀ h
  · exact F.nondeg_of_lt j₀ h

theorem two_mul_quarter : (2 : ℝ≥0∞) * ENNReal.ofReal (1 / 4) = 1 / 2 := by
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    show (2:ℝ) * (1 / 4) = 1 / 2 by norm_num, ENNReal.ofReal_div_of_pos two_pos]
  simp

/-- **Assembly.** Partial-sum bounds on `α` and `β` give `e(G_n) ≤ 2(24a + 2 S_n)`. -/
theorem eG_le_of_sums (hc : F.Centered) {a : ℝ} (ha : 0 < a) (j₀ : Fin F.nA) (S : ℕ → ℝ)
    (hS0 : ∀ n, 0 ≤ S n)
    (hα : ∀ n, ∑ r ∈ range n, (F.wdata ha j₀).α r ≤ ENNReal.ofReal (S n))
    (hβ : ∀ n, ∑ r ∈ range n, (F.wdata ha j₀).β r ≤ ENNReal.ofReal (1 / 4)) (n : ℕ) :
    F.eG (F.G n) ≤ 2 * (24 * a + 2 * S n) := by
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
  have h3 := (F.ofReal_eG_le_Wint hc j₀ n).trans h2
  have hcn : c n ≤ ENNReal.ofReal (24 * a) + 2 * ENNReal.ofReal (S n) := by
    simp only [c]
    rw [show 4 * D.A = 24 * a by simp only [D, wdata]; ring]
    gcongr; exact hα n
  have h4 : ENNReal.ofReal (F.eG (F.G n)) ≤ 2 * (ENNReal.ofReal (24 * a) + 2 * ENNReal.ofReal (S n)) :=
    h3.trans (by gcongr)
  rw [show (2 : ℝ≥0∞) * (ENNReal.ofReal (24 * a) + 2 * ENNReal.ofReal (S n)) =
      ENNReal.ofReal (2 * (24 * a + 2 * S n)) by
    rw [eq_comm, ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num), ENNReal.ofReal_add (by positivity)
      (by have := hS0 n; positivity), ENNReal.ofReal_mul (show (0:ℝ) ≤ 2 by norm_num),
      ENNReal.ofReal_ofNat]] at h4
  exact (ENNReal.ofReal_le_ofReal_iff (by have := hS0 n; positivity)).1 h4

theorem mom_zero (j) : F.mom j 0 = 1 := by simp [mom, F.Psum]

/-- Sum of `ofReal`s of a nonnegative family. -/
theorem sum_ofReal_le {t : ℕ → ℝ} (ht : ∀ r, 0 ≤ t r) {s : ℕ → ℝ≥0∞}
    (hs : ∀ r, s r ≤ ENNReal.ofReal (t r)) (n : ℕ) :
    ∑ r ∈ range n, s r ≤ ENNReal.ofReal (∑ r ∈ range n, t r) := by
  rw [ENNReal.ofReal_sum_of_nonneg fun r _ => ht r]
  exact sum_le_sum fun r _ => hs r

/-- Small `β` partial sums for moments matched below `m`, when `tv(dB^m μ^r) ≤ K g(r)`. -/
theorem exists_L_beta (j₀ : Fin F.nA) {m : ℕ} (hm1 : 1 ≤ m) (hm : m ≤ 4)
    (hmom : ∀ b, ∀ i < m, F.mom b i = F.mom j₀ i) {b : ℝ} (hb : 0 < b) {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ r, tv (dB b ^ m * F.measOf j₀ ^ r) ≤ K * gg r) :
    ∃ L : ℕ, ∃ hL : 0 < (L : ℝ) * b,
      ∀ n, ∑ r ∈ range n, (F.wdata hL j₀).β r ≤ ENNReal.ofReal (1 / 4) := by
  set Sm := F.amomSum j₀ m
  have hSm : 0 ≤ Sm := F.amomSum_nonneg j₀ m
  obtain ⟨L, hL0, hL⟩ := small_sum (F.tv_measOf_pow j₀) hb hm1 hK hdec
    (ε := 1 / (28 * Sm + 4)) (by positivity)
  have hLb : 0 < (L : ℝ) * b := mul_pos (by exact_mod_cast hL0) hb
  refine ⟨L, hLb, fun n => ?_⟩
  refine (sum_ofReal_le (fun r => by have := tv_nonneg (F.measOf j₀ ^ r * Dif (L * b) ^ m); positivity)
    (fun r => F.wdata_β_le hLb j₀ hm hmom r) n).trans (ENNReal.ofReal_le_ofReal ?_)
  rw [← mul_sum]
  calc Sm * 7 * ∑ r ∈ range n, tv (F.measOf j₀ ^ r * Dif (L * b) ^ m)
      ≤ Sm * 7 * (1 / (28 * Sm + 4)) := mul_le_mul_of_nonneg_left (hL n) (by positivity)
    _ ≤ 1 / 4 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith

/-- **`e(G_n) = O(log n)`.** If all actions share the variance of a nondegenerate reference
action `j₀` (and the family is centered), then `e(G_n) ≤ C (1 + log n)` for all `n`. -/
theorem eG_log_upper (hc : F.Centered) {j₀ : Fin F.nA} (hnd : F.Nondeg j₀)
    (hσ : ∀ j, F.sig2 j = F.sig2 j₀) : ∃ C, ∀ n : ℕ, F.eG (F.G n) ≤ C * (1 + Real.log n) := by
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
  refine (F.eG_le_of_sums hc hLb j₀ _ (fun n => mul_nonneg hK (hlog n)) hα hL n).trans ?_
  have h1n : 1 ≤ 1 + Real.log n := by have := Real.log_natCast_nonneg n; linarith
  have ha0 : 0 ≤ a := hLb.le
  nlinarith

/-- **`e(G_n) = O(1)`.** If moreover all third moments agree with those of `j₀`, then
`e(G_n)` is bounded. -/
theorem eG_bdd_upper (hc : F.Centered) {j₀ : Fin F.nA} (hnd : F.Nondeg j₀)
    (hσ : ∀ j, F.sig2 j = F.sig2 j₀) (h3 : ∀ j, F.m3 j = F.m3 j₀) :
    ∃ C, ∀ n : ℕ, F.eG (F.G n) ≤ C := by
  obtain ⟨ρ, b, c, ζ, h0, h1, hb, hζ, heq⟩ := hnd
  have hmom : ∀ k, ∀ i < 4, F.mom k i = F.mom j₀ i := by
    intro k i hi
    interval_cases i
    · rw [F.mom_zero, F.mom_zero]
    · simp only [mom, pow_one]; rw [hc k, hc j₀]
    · simpa [mom, sig2] using hσ k
    · simpa [mom, m3] using h3 k
  obtain ⟨L, hLb, hL⟩ := F.exists_L_beta j₀ (by norm_num) le_rfl hmom hb
    (by positivity : (0:ℝ) ≤ 512 / ρ ^ 2)
    (fun r => by rw [heq]; exact tv_decay_four_gg h0 h1 hζ r)
  set a := (L : ℝ) * b
  set Sm := F.amomSum j₀ 4
  have hSm : 0 ≤ Sm := F.amomSum_nonneg j₀ 4
  have hLn : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · simp [a, h] at hLb
    · exact h
  set K3 := 24 * Real.sqrt 3 * Real.sqrt (2 / ρ ^ 3)
  set K := Sm * 7 * ((1 / a) ^ 3 + (1 / (2 * b)) ^ 3 * K3 * 2)
  have hK : 0 ≤ K := by positivity
  have hα : ∀ n, ∑ r ∈ range n, (F.wdata hLb j₀).α r ≤ ENNReal.ofReal K := by
    intro n
    refine (sum_ofReal_le (fun r => by
        have := tv_nonneg (F.measOf j₀ ^ r * Dif a ^ (4 - 1)); positivity)
      (fun r => F.wdata_α_le hLb j₀ (by norm_num) le_rfl hmom r) n).trans
      (ENNReal.ofReal_le_ofReal ?_)
    rw [← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := sum_split (fun r => tv (F.measOf j₀ ^ r * Dif a ^ 3)) (X := (1 / a) ^ 3)
      (K := (1 / (2 * b)) ^ 3 * K3) (by positivity) le_rfl (fun r => tv_nonneg _)
      (fun r => (tv_mul_Dif_pow_le hLb _ 3).trans (by
        have := F.tv_measOf_pow j₀ r
        have : 0 ≤ (1 / a) ^ 3 := by positivity
        nlinarith))
      (fun r => (tv_Dif_scale b hb hLn 3 _).trans (by
        rw [mul_assoc, heq]
        exact mul_le_mul_of_nonneg_left (tv_decay_three_gg h0 h1 hζ r) (by positivity))) n
    simpa [mul_assoc] using this
  refine ⟨2 * (24 * a + 2 * K), fun n => ?_⟩
  exact F.eG_le_of_sums hc hLb j₀ (fun _ => K) (fun _ => hK) hα hL n

end CausalSpectrum.Sqrt.IncFamily

namespace CausalSpectrum.Sqrt.IncFamily
variable (F : IncFamily)

/-- A centered action with nonzero third moment is nondegenerate. -/
theorem nondeg_of_m3_ne_zero (hc : F.Centered) {j : Fin F.nA} (h : F.m3 j ≠ 0) : F.Nondeg j := by
  by_contra hnd
  have hall : ∀ y₁ y₂ : Fin (F.nY j), F.X j y₁ = F.X j y₂ := fun y₁ y₂ => by
    by_contra hne; exact hnd (F.nondeg_of_ne j hne)
  set y₀ : Fin (F.nY j) := ⟨0, F.hY j⟩
  have h0 : F.X j y₀ = 0 := by
    have := hc j
    simp only [fun y => hall y y₀, ← Finset.sum_mul, F.Psum, one_mul] at this
    exact this
  apply h
  simp [m3, fun y => hall y y₀, h0]

end CausalSpectrum.Sqrt.IncFamily

namespace CausalSpectrum.Kernel
variable (κ : Kernel)
open Sqrt

/-- **`L_n - nh = O(log n)`, `C_n - nh = O(log n)`** when every action has the variance of a
nondegenerate reference action. -/
theorem excess_log_upper {h : ℝ} (hh : κ.EqualEntropy h) {j₀ : Fin κ.nA}
    (hnd : (κ.fam h).Nondeg j₀) (hσ : ∀ j, (κ.fam h).sig2 j = (κ.fam h).sig2 j₀) :
    ∃ C, ∀ n : ℕ, 1 ≤ n →
      envelopeMean (κ.rounds n) - n * h ≤ C * (1 + Real.log n) ∧
      κ.costBits n - n * h ≤ C * (1 + Real.log n) + shannonOverhead := by
  obtain ⟨C, hC⟩ := (κ.fam h).eG_log_upper (κ.fam_centered hh) hnd hσ
  refine ⟨C, fun n hn => ?_⟩
  have e := κ.envelope_sub_eq_eG hh hn
  have s := (κ.costBits_sandwich n).2
  have := hC n
  constructor <;> linarith

/-- **`L_n - nh = O(1)`, `C_n - nh = O(1)`** when variances and third moments all agree with
those of a nondegenerate reference action. -/
theorem excess_bdd_upper {h : ℝ} (hh : κ.EqualEntropy h) {j₀ : Fin κ.nA}
    (hnd : (κ.fam h).Nondeg j₀) (hσ : ∀ j, (κ.fam h).sig2 j = (κ.fam h).sig2 j₀)
    (h3 : ∀ j, (κ.fam h).m3 j = (κ.fam h).m3 j₀) :
    ∃ C, ∀ n : ℕ, 1 ≤ n →
      envelopeMean (κ.rounds n) - n * h ≤ C ∧ κ.costBits n - n * h ≤ C + shannonOverhead := by
  obtain ⟨C, hC⟩ := (κ.fam h).eG_bdd_upper (κ.fam_centered hh) hnd hσ h3
  refine ⟨C, fun n hn => ?_⟩
  have e := κ.envelope_sub_eq_eG hh hn
  have s := (κ.costBits_sandwich n).2
  have := hC n
  constructor <;> linarith

/-- **`Θ(log n)`.** If all actions have equal variances and two of them have different third
moments, then `L_n - nh` and `C_n - nh` are both `Θ(log n)`. No further nondegeneracy
hypothesis is needed. -/
theorem excess_log_theta {h : ℝ} (hh : κ.EqualEntropy h)
    (hσ : ∀ j k, (κ.fam h).sig2 j = (κ.fam h).sig2 k) {j k : Fin κ.nA}
    (h3 : (κ.fam h).m3 j ≠ (κ.fam h).m3 k) :
    ∃ c > 0, ∃ C, ∀ᶠ n : ℕ in atTop,
      (c * Real.log n ≤ envelopeMean (κ.rounds n) - n * h ∧
        envelopeMean (κ.rounds n) - n * h ≤ C * Real.log n) ∧
      (c * Real.log n ≤ κ.costBits n - n * h ∧ κ.costBits n - n * h ≤ C * Real.log n) := by
  have hc := κ.fam_centered hh
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, (κ.fam h).m3 j₀ ≠ 0 := by
    by_contra hz; push_neg at hz; exact h3 (by rw [hz j, hz k])
  obtain ⟨C, hC⟩ := κ.excess_log_upper hh ((κ.fam h).nondeg_of_m3_ne_zero hc hj₀) (fun i => hσ i j₀)
  obtain ⟨c, hc0, hlow⟩ := κ.excess_log_lower hh (hσ j k) h3
  refine ⟨c, hc0, 2 * |C| + |shannonOverhead|, ?_⟩
  filter_upwards [hlow, eventually_ge_atTop 3] with n hn hn3
  have hlog : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have : (3:ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  obtain ⟨u1, u2⟩ := hC n (by omega)
  have hb1 : C * (1 + Real.log n) ≤ 2 * |C| * Real.log n := by
    nlinarith [le_abs_self C, abs_nonneg C]
  have hb2 : shannonOverhead ≤ |shannonOverhead| * Real.log n := by
    nlinarith [le_abs_self shannonOverhead, abs_nonneg shannonOverhead]
  refine ⟨⟨hn.1, ?_⟩, ⟨hn.2, ?_⟩⟩ <;> nlinarith [abs_nonneg shannonOverhead]

end CausalSpectrum.Kernel

namespace CausalSpectrum.Zero.NNKernel
variable (κ : NNKernel)
open Sqrt

/-- **Nonnegative kernels: `C_n - nh = O(log n)`** (via `C_n(κ) = C_n(κ_red)`). -/
theorem excess_log_upper {h : ℝ} (hh : κ.red.EqualEntropy h) {j₀ : Fin κ.red.nA}
    (hnd : (κ.red.fam h).Nondeg j₀) (hσ : ∀ j, (κ.red.fam h).sig2 j = (κ.red.fam h).sig2 j₀) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → κ.costBits n - n * h ≤ C * (1 + Real.log n) + shannonOverhead := by
  obtain ⟨C, hC⟩ := κ.red.excess_log_upper hh hnd hσ
  exact ⟨C, fun n hn => by rw [κ.costBits_eq_red]; exact (hC n hn).2⟩

/-- **Nonnegative kernels: `C_n - nh = O(1)`.** -/
theorem excess_bdd_upper {h : ℝ} (hh : κ.red.EqualEntropy h) {j₀ : Fin κ.red.nA}
    (hnd : (κ.red.fam h).Nondeg j₀) (hσ : ∀ j, (κ.red.fam h).sig2 j = (κ.red.fam h).sig2 j₀)
    (h3 : ∀ j, (κ.red.fam h).m3 j = (κ.red.fam h).m3 j₀) :
    ∃ C, ∀ n : ℕ, 1 ≤ n → κ.costBits n - n * h ≤ C + shannonOverhead := by
  obtain ⟨C, hC⟩ := κ.red.excess_bdd_upper hh hnd hσ h3
  exact ⟨C, fun n hn => by rw [κ.costBits_eq_red]; exact (hC n hn).2⟩

/-- **Nonnegative kernels: `C_n - nh = Θ(log n)`.** -/
theorem excess_log_theta {h : ℝ} (hh : κ.red.EqualEntropy h)
    (hσ : ∀ j k, (κ.red.fam h).sig2 j = (κ.red.fam h).sig2 k) {j k : Fin κ.red.nA}
    (h3 : (κ.red.fam h).m3 j ≠ (κ.red.fam h).m3 k) :
    ∃ c > 0, ∃ C, ∀ᶠ n : ℕ in atTop,
      c * Real.log n ≤ κ.costBits n - n * h ∧ κ.costBits n - n * h ≤ C * Real.log n := by
  obtain ⟨c, hc, C, hev⟩ := κ.red.excess_log_theta hh hσ h3
  exact ⟨c, hc, C, hev.mono fun n hn => by rw [κ.costBits_eq_red]; exact hn.2⟩

end CausalSpectrum.Zero.NNKernel

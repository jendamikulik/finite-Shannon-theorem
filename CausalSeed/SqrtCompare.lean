/-
Explicit CDF comparison between the Bellman envelope and the profile:
`sup_z |G_n(z√n) - F_{a,b}(z)| ≤ 2Φ(-R) + 3A/√m + B/m + ℓ a R √(m/(n+m)) + D ln(1+m/n)`.
-/
import CausalSeed.SqrtDefect
import CausalSeed.BellmanCompare

noncomputable section
open Classical Finset Set Filter
namespace CausalSpectrum.Sqrt

variable {a b : ℝ}

/-- `Φ(-R)`. -/
def PhiNeg (R : ℝ) : ℝ := gaussTail R / Real.sqrt (2 * Real.pi)

theorem PhiNeg_nonneg (R : ℝ) : 0 ≤ PhiNeg R :=
  div_nonneg (gaussTail_nonneg R) sqrt2pi_pos.le

theorem PhiNeg_zero : PhiNeg 0 = 1 / 2 := by
  have := sqrt2pi_pos
  rw [PhiNeg, gaussTail_zero]; field_simp

theorem phi_nonneg (y : ℝ) : 0 ≤ phi y := div_nonneg (Real.exp_pos _).le sqrt2pi_pos.le

theorem phi_le (y : ℝ) : phi y ≤ 1 / Real.sqrt (2 * Real.pi) := by
  unfold phi
  have h : gaussRaw y ≤ 1 := by unfold gaussRaw; rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y]
  exact div_le_div_of_nonneg_right h sqrt2pi_pos.le

theorem prof'_nonneg (ha : 0 < a) (hb : 0 < b) (z : ℝ) : 0 ≤ prof' a b z := by
  unfold prof' dL dR
  have := phi_nonneg (z / b); have := phi_nonneg (z / a)
  split_ifs <;> positivity

/-- `ℓ = 2φ₀/(a+b)`. -/
def constL (a b : ℝ) : ℝ := 2 / (a + b) * (1 / Real.sqrt (2 * Real.pi))
/-- `D = aφ₀e^{-1/2}/(a+b)`. -/
def constD (a b : ℝ) : ℝ := a * (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-1 / 2) / (a + b)

theorem prof'_le (ha : 0 < a) (hb : 0 < b) (z : ℝ) : prof' a b z ≤ constL a b := by
  unfold prof' dL dR constL
  split_ifs <;> exact mul_le_mul_of_nonneg_left (phi_le _) (by positivity)

theorem prof_monotone (ha : 0 < a) (hb : 0 < b) : Monotone (prof a b) :=
  monotone_of_deriv_nonneg (fun z => (hasDerivAt_prof ha hb z).differentiableAt)
    (fun z => by rw [(hasDerivAt_prof ha hb z).deriv]; exact prof'_nonneg ha hb z)

theorem prof_lipschitz (ha : 0 < a) (hb : 0 < b) (y z : ℝ) :
    |prof a b y - prof a b z| ≤ constL a b * |y - z| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := prof a b) (f' := prof' a b)
    (s := Set.univ) (fun x _ => (hasDerivAt_prof ha hb x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs, abs_of_nonneg (prof'_nonneg ha hb x)];
                   exact prof'_le ha hb x) convex_univ (Set.mem_univ z) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using this

theorem prof_nonneg (ha : 0 < a) (hb : 0 < b) (z : ℝ) : 0 ≤ prof a b z := by
  rcases le_or_gt z 0 with h | h
  · simp only [prof, if_pos h, FL]
    have := gaussTail_nonneg (-z / b); have := sqrt2pi_pos; positivity
  · refine le_trans ?_ (prof_monotone ha hb h.le)
    rw [prof_zero ha hb]; positivity

theorem prof_le_one (ha : 0 < a) (hb : 0 < b) (z : ℝ) : prof a b z ≤ 1 := by
  rcases le_or_gt z 0 with h | h
  · refine (prof_monotone ha hb h).trans ?_
    rw [prof_zero ha hb, div_le_one (by linarith)]; linarith
  · simp only [prof, if_neg (not_le.mpr h), FR]
    have := gaussTail_nonneg (z / a); have := sqrt2pi_pos
    have : 0 ≤ 2 * a / (a + b) * (gaussTail (z / a) / Real.sqrt (2 * Real.pi)) := by positivity
    linarith

/-- `F(-aR) ≤ 2Φ(-R)` for `b ≤ a`, `R ≥ 0`. -/
theorem prof_neg_aR_le (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) {R : ℝ} (hR : 0 ≤ R) :
    prof a b (-(a * R)) ≤ 2 * PhiNeg R := by
  simp only [prof, if_pos (show -(a * R) ≤ 0 by nlinarith), FL]
  have h1 : gaussTail (-(-(a * R)) / b) ≤ gaussTail R := by
    apply gaussTail_antitone
    rw [neg_neg, le_div_iff₀ hb]; nlinarith
  have h2 : 2 * b / (a + b) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have := sqrt2pi_pos
  have h3 : gaussTail (-(-(a * R)) / b) / Real.sqrt (2 * Real.pi) ≤ PhiNeg R :=
    div_le_div_of_nonneg_right h1 this.le
  have h4 : 0 ≤ gaussTail (-(-(a * R)) / b) / Real.sqrt (2 * Real.pi) :=
    div_nonneg (gaussTail_nonneg _) this.le
  calc 2 * b / (a + b) * (gaussTail (-(-(a * R)) / b) / Real.sqrt (2 * Real.pi))
      ≤ 2 * (gaussTail (-(-(a * R)) / b) / Real.sqrt (2 * Real.pi)) := by gcongr
    _ ≤ 2 * PhiNeg R := by gcongr

/-- `F(aR) ≥ 1 - 2Φ(-R)`. -/
theorem prof_aR_ge (ha : 0 < a) (hb : 0 < b) {R : ℝ} (hR : 0 ≤ R) :
    1 - 2 * PhiNeg R ≤ prof a b (a * R) := by
  rcases eq_or_lt_of_le hR with h | h
  · subst h; rw [PhiNeg_zero, mul_zero]; norm_num; exact prof_nonneg ha hb 0
  · simp only [prof, if_neg (not_le.mpr (mul_pos ha h)), FR, mul_div_cancel_left₀ R ha.ne']
    have h2 : 2 * a / (a + b) ≤ 2 := by rw [div_le_iff₀ (by linarith)]; nlinarith
    have := PhiNeg_nonneg R
    have e : gaussTail R / Real.sqrt (2 * Real.pi) = PhiNeg R := rfl
    rw [e]; nlinarith

/-! ### Summation bounds -/

theorem tele_cube {τ : ℝ} (hτ : 1 ≤ τ - 1) :
    1 / (τ * Real.sqrt τ) ≤ 2 / Real.sqrt (τ - 1) - 2 / Real.sqrt τ := by
  set p := Real.sqrt (τ - 1)
  set q := Real.sqrt τ
  have hp : 0 < p := Real.sqrt_pos.mpr (by linarith)
  have hq : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hp2 : p ^ 2 = τ - 1 := Real.sq_sqrt (by linarith)
  have hq2 : q ^ 2 = τ := Real.sq_sqrt (by linarith)
  have hpq : p ≤ q := Real.sqrt_le_sqrt (by linarith)
  rw [← hq2]
  have e : 2 / p - 2 / q = 2 / (p * q * (q + p)) := by
    field_simp
    nlinarith
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hp hq, mul_pos (mul_pos hp hq) hq]

theorem sum_cube_le {m : ℝ} (hm : 1 ≤ m) : ∀ n : ℕ,
    ∑ k ∈ range n, 1 / ((m + k) * Real.sqrt (m + k)) ≤ 3 / Real.sqrt m := by
  have hs : 0 < Real.sqrt m := Real.sqrt_pos.mpr (by linarith)
  have main : ∀ n : ℕ, ∑ k ∈ range (n + 1), 1 / ((m + k) * Real.sqrt (m + k)) ≤
      1 / (m * Real.sqrt m) + 2 / Real.sqrt m - 2 / Real.sqrt (m + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := tele_cube (τ := m + (n + 1 : ℕ)) (by push_cast; linarith)
      have e : m + ((n + 1 : ℕ) : ℝ) - 1 = m + n := by push_cast; ring
      rw [e] at this
      linarith
  intro n
  rcases n with _ | n
  · simp; positivity
  · refine (main n).trans ?_
    have h1 : 1 / (m * Real.sqrt m) ≤ 1 / Real.sqrt m := by
      apply one_div_le_one_div_of_le hs; nlinarith
    have h2 : 0 ≤ 2 / Real.sqrt (m + n) := by positivity
    have e : 3 / Real.sqrt m = 1 / Real.sqrt m + 2 / Real.sqrt m := by ring
    linarith

theorem sum_sq_le {m : ℝ} (hm : 1 ≤ m) : ∀ n : ℕ,
    ∑ k ∈ range n, 1 / (m + k) ^ 2 ≤ 2 / m := by
  have main : ∀ n : ℕ, ∑ k ∈ range (n + 1), 1 / (m + k) ^ 2 ≤
      1 / m ^ 2 + 1 / m - 1 / (m + n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h0 : 0 < m + n := by positivity
      have : 1 / (m + ((n + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / (m + n) - 1 / (m + ((n + 1 : ℕ) : ℝ)) := by
        push_cast
        rw [div_sub_div _ _ h0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      linarith
  intro n
  rcases n with _ | n
  · simp; positivity
  · refine (main n).trans ?_
    have h1 : 1 / m ^ 2 ≤ 1 / m := one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 : 0 ≤ 1 / (m + n) := by positivity
    have e : 2 / m = 1 / m + 1 / m := by ring
    linarith

/-! ### Time change -/

theorem time_change (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) {s t : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (x : ℝ) : |prof a b (x / Real.sqrt t) - prof a b (x / Real.sqrt s)| ≤
      constD a b * Real.log (t / s) := by
  have hD : ∀ τ, 0 < τ → |ut a b x τ| ≤ constD a b / τ := by
    intro τ hτ
    have := abs_z_prof'_le ha hb hab (x / Real.sqrt τ)
    unfold ut psi
    rw [abs_div, abs_of_pos hτ, abs_div, abs_neg, abs_two]
    gcongr
    unfold constD
    have e : a * (1 / Real.sqrt (2 * Real.pi)) * Real.exp (-1 / 2) / (a + b) =
        2 * a / (a + b) * (Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi)) / 2 := by ring
    rw [e]; linarith
  have hmono : ∀ c : ℝ, |c| ≤ 1 → MonotoneOn
      (fun τ => constD a b * Real.log τ - c * prof a b (x / Real.sqrt τ)) (Ici s) := by
    intro c hc
    have hd : ∀ τ ∈ Ici s, HasDerivAt
        (fun τ => constD a b * Real.log τ - c * prof a b (x / Real.sqrt τ))
        (constD a b * τ⁻¹ - c * ut a b x τ) τ := by
      intro τ hτ
      have hτ' : 0 < τ := lt_of_lt_of_le hs hτ
      exact ((Real.hasDerivAt_log hτ'.ne').const_mul _).sub
        ((hasDerivAt_u_t' ha hb hτ' x).const_mul c)
    apply monotoneOn_of_deriv_nonneg (convex_Ici s)
    · intro τ hτ; exact (hd τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ; rw [interior_Ici] at hτ
      exact (hd τ (mem_Ici.mpr (le_of_lt hτ))).differentiableAt.differentiableWithinAt
    · intro τ hτ; rw [interior_Ici] at hτ
      have hτ' : 0 < τ := lt_trans hs hτ
      rw [(hd τ (mem_Ici.mpr (le_of_lt hτ))).deriv]
      have h1 := hD τ hτ'
      have : c * ut a b x τ ≤ |c| * |ut a b x τ| := by rw [← abs_mul]; exact le_abs_self _
      have : |c| * |ut a b x τ| ≤ |ut a b x τ| := by
        nlinarith [abs_nonneg (ut a b x τ)]
      rw [← div_eq_mul_inv]
      linarith
  have k1 := hmono 1 (by simp) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hst) hst
  have k2 := hmono (-1) (by simp) (mem_Ici.mpr le_rfl) (mem_Ici.mpr hst) hst
  simp only at k1 k2
  rw [Real.log_div (by linarith) hs.ne']
  rw [abs_le]; constructor <;> linarith

/-! ### The comparison -/

namespace IncFamily
variable (F : IncFamily)

/-- The bound `e_n` of the note (right side of (cdfbound)). -/
def cdfErr (n : ℕ) (m R : ℝ) : ℝ :=
  2 * PhiNeg R + 3 * F.constA F.sA F.sB / Real.sqrt m + constB F.sA F.sB / m +
    constL F.sA F.sB * F.sA * R * Real.sqrt (m / (n + m)) + constD F.sA F.sB * Real.log (1 + m / n)

/-- **Lemma (Explicit CDF comparison).** -/
theorem cdf_comparison (hc : F.Centered) (hb : 0 < F.sB) {n : ℕ} (hn : 1 ≤ n) {m : ℝ}
    (hm : 1 ≤ m) {R : ℝ} (hR : 0 ≤ R) (z : ℝ) :
    |F.G n (z * Real.sqrt n) - prof F.sA F.sB z| ≤ F.cdfErr n m R := by
  set a := F.sA
  set b := F.sB
  have hab : b ≤ a := F.sB_le_sA
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have hm0 : 0 < m := by linarith
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hsm : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0
  have hA : 0 ≤ F.constA a b := by
    unfold constA; have := lipF_nonneg ha hb; have := F.M_nonneg; positivity
  have hB : 0 ≤ constB a b := by unfold constB; have := sqrt2pi_pos; positivity
  set u : ℝ → ℝ → ℝ := fun τ x => prof a b (x / Real.sqrt τ)
  set e : ℝ → ℝ := fun τ => F.constA a b / (τ * Real.sqrt τ) + constB a b / (2 * τ ^ 2)
  set d := a * R * Real.sqrt m
  set δ := 2 * PhiNeg R
  have hd0 : 0 ≤ d := by positivity
  have hdef : ∀ k : ℕ, ∀ x, |F.T (u (m + k)) x - u (m + k + 1) x| ≤ e (m + k) := by
    intro k x
    exact F.one_step_defect hc hb (by positivity) x
  have hdm : d / Real.sqrt m = a * R := by simp only [d]; field_simp
  have hlo : ∀ x, u m (x - d) - δ ≤ F.G 0 x := by
    intro x
    simp only [u, G]
    split_ifs with hx
    · have := prof_le_one ha hb ((x - d) / Real.sqrt m)
      have := PhiNeg_nonneg R; simp only [δ]; linarith
    · have h1 : (x - d) / Real.sqrt m ≤ -(a * R) := by
        rw [← hdm, ← neg_div]; gcongr; linarith [not_le.mp hx]
      have := (prof_monotone ha hb h1).trans (prof_neg_aR_le ha hb hab hR)
      simp only [δ]; linarith
  have hhi : ∀ x, F.G 0 x ≤ u m (x + d) + δ := by
    intro x
    simp only [u, G]
    split_ifs with hx
    · have h1 : a * R ≤ (x + d) / Real.sqrt m := by rw [← hdm]; gcongr; linarith
      have := (prof_aR_ge ha hb hR).trans (prof_monotone ha hb h1)
      simp only [δ]; linarith
    · have := prof_nonneg ha hb ((x + d) / Real.sqrt m)
      have := PhiNeg_nonneg R; simp only [δ]; linarith
  have hprop := F.barrier_propagation m d δ hdef hlo hhi n (z * Real.sqrt n)
  -- accumulated defect
  have hE : ∑ k ∈ range n, e (m + k) ≤ 3 * F.constA a b / Real.sqrt m + constB a b / m := by
    simp only [e, Finset.sum_add_distrib]
    have h1 := sum_cube_le hm n
    have h2 := sum_sq_le hm n
    have e1 : ∑ k ∈ range n, F.constA a b / ((m + k) * Real.sqrt (m + k)) =
        F.constA a b * ∑ k ∈ range n, 1 / ((m + k) * Real.sqrt (m + k)) := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    have e2 : ∑ k ∈ range n, constB a b / (2 * (m + k) ^ 2) =
        constB a b / 2 * ∑ k ∈ range n, 1 / (m + k) ^ 2 := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _
      have : 0 < m + k := by positivity
      field_simp
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left h1 hA
    have := mul_le_mul_of_nonneg_left h2 (show 0 ≤ constB a b / 2 by positivity)
    have e3 : F.constA a b * (3 / Real.sqrt m) = 3 * F.constA a b / Real.sqrt m := by ring
    have e4 : constB a b / 2 * (2 / m) = constB a b / m := by field_simp
    linarith
  -- spatial and temporal shifts
  set τ := m + (n : ℝ)
  have hτ : 0 < τ := by positivity
  have hsτ : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hshift : ∀ s : ℝ, |s| ≤ d →
      |u τ (z * Real.sqrt n + s) - u τ (z * Real.sqrt n)| ≤
        constL a b * a * R * Real.sqrt (m / (n + m)) := by
    intro s hs
    simp only [u]
    refine (prof_lipschitz ha hb _ _).trans ?_
    rw [← sub_div, show z * Real.sqrt n + s - z * Real.sqrt n = s by ring, abs_div,
      abs_of_pos hsτ]
    have hL : 0 ≤ constL a b := by unfold constL; have := sqrt2pi_pos; positivity
    have e : constL a b * a * R * Real.sqrt (m / (n + m)) = constL a b * (d / Real.sqrt τ) := by
      simp only [d, τ]
      rw [Real.sqrt_div hm0.le, add_comm (n : ℝ) m]; ring
    rw [e]; gcongr
  have htime : |u τ (z * Real.sqrt n) - prof a b z| ≤ constD a b * Real.log (1 + m / n) := by
    have := time_change ha hb hab hn0 (show (n : ℝ) ≤ τ by simp only [τ]; linarith)
      (z * Real.sqrt n)
    have hsn : Real.sqrt n ≠ 0 := (Real.sqrt_pos.mpr hn0).ne'
    rw [show z * Real.sqrt n / Real.sqrt n = z by field_simp] at this
    have e : τ / n = 1 + m / n := by simp only [τ]; field_simp; ring
    rw [e] at this
    exact this
  obtain ⟨hlow, hup⟩ := hprop
  have s1 := hshift (-d) (by rw [abs_neg, abs_of_nonneg hd0])
  have s2 := hshift d (by rw [abs_of_nonneg hd0])
  simp only [← sub_eq_add_neg] at s1
  unfold cdfErr
  rw [abs_le]; constructor
  · have := (abs_le.mp s2).1; have := (abs_le.mp htime).1; have := (abs_le.mp htime).2
    have := (abs_le.mp s1).1; have := (abs_le.mp s1).2; have := (abs_le.mp s2).2
    linarith
  · have := (abs_le.mp s2).2; have := (abs_le.mp htime).1; have := (abs_le.mp htime).2
    have := (abs_le.mp s1).1
    linarith

#print axioms cdf_comparison

end IncFamily
end CausalSpectrum.Sqrt

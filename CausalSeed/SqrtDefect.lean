/-
One-step defect of the explicit profile under the Bellman operator, and the
variance parameters `a = max σ_j`, `b = min σ_j`.
-/
import CausalSeed.SqrtProfile
import CausalSeed.SqrtTails

noncomputable section
open Classical Finset Set Filter
namespace CausalSpectrum.Sqrt

/-! ### Calculus helpers -/

/-- If `g(0) = g'(0) = 0` and `g'' ≤ 0` on `[0,∞)`, then `g ≤ 0` on `[0,∞)`. -/
theorem nonpos_of_second {g g' g'' : ℝ → ℝ}
    (hg : ∀ s, 0 ≤ s → HasDerivAt g (g' s) s) (hg' : ∀ s, 0 ≤ s → HasDerivAt g' (g'' s) s)
    (h0 : g 0 = 0) (h0' : g' 0 = 0) (hneg : ∀ s, 0 ≤ s → g'' s ≤ 0) :
    ∀ h, 0 ≤ h → g h ≤ 0 := by
  have hint : interior (Ici (0:ℝ)) = Set.Ioi 0 := interior_Ici
  have a1 : AntitoneOn g' (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s hs; exact (hg' s hs).continuousAt.continuousWithinAt
    · rw [hint]; intro s hs; exact (hg' s (le_of_lt hs)).differentiableAt.differentiableWithinAt
    · rw [hint]; intro s hs; rw [(hg' s (le_of_lt hs)).deriv]; exact hneg s (le_of_lt hs)
  have a2 : AntitoneOn g (Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro s hs; exact (hg s hs).continuousAt.continuousWithinAt
    · rw [hint]; intro s hs; exact (hg s (le_of_lt hs)).differentiableAt.differentiableWithinAt
    · rw [hint]; intro s hs; rw [(hg s (le_of_lt hs)).deriv]
      have := a1 (mem_Ici.mpr le_rfl) (mem_Ici.mpr (le_of_lt hs)) (le_of_lt hs)
      rw [h0'] at this; exact this
  intro h hh
  have := a2 (mem_Ici.mpr le_rfl) (mem_Ici.mpr hh) hh
  rw [h0] at this; exact this

/-- Second-order Taylor with a Lipschitz second derivative, `h ≥ 0`. -/
theorem taylor2_nonneg {f f' f'' : ℝ → ℝ} {L x : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hL : ∀ y, |f'' y - f'' x| ≤ L * |y - x|) {h : ℝ} (hh : 0 ≤ h) :
    |f (x + h) - f x - h * f' x - h ^ 2 / 2 * f'' x| ≤ L * h ^ 3 / 6 := by
  have hd1 : ∀ c : ℝ, ∀ s, 0 ≤ s → HasDerivAt
      (fun s => c * (f (x + s) - f x - s * f' x - s ^ 2 / 2 * f'' x) - L * s ^ 3 / 6)
      (c * (f' (x + s) - f' x - s * f'' x) - L * s ^ 2 / 2) s := by
    intro c s _
    have h1 : HasDerivAt (fun s => f (x + s)) (f' (x + s)) s := by
      exact ((hf (x + s)).comp s ((hasDerivAt_id s).const_add x)).congr_deriv (by simp)
    have := ((((h1.sub_const (f x)).sub ((hasDerivAt_id s).mul_const (f' x))).sub
      (((hasDerivAt_pow 2 s).div_const 2).mul_const (f'' x))).const_mul c).sub
      ((hasDerivAt_pow 3 s).const_mul L |>.div_const 6)
    exact this.congr_deriv (by norm_num; ring)
  have hd2 : ∀ c : ℝ, ∀ s, 0 ≤ s → HasDerivAt
      (fun s => c * (f' (x + s) - f' x - s * f'' x) - L * s ^ 2 / 2)
      (c * (f'' (x + s) - f'' x) - L * s) s := by
    intro c s _
    have h1 : HasDerivAt (fun s => f' (x + s)) (f'' (x + s)) s := by
      exact ((hf' (x + s)).comp s ((hasDerivAt_id s).const_add x)).congr_deriv (by simp)
    have := (((h1.sub_const (f' x)).sub ((hasDerivAt_id s).mul_const (f'' x))).const_mul c).sub
      ((hasDerivAt_pow 2 s).const_mul L |>.div_const 2)
    exact this.congr_deriv (by norm_num; ring)
  have hsec : ∀ c : ℝ, |c| ≤ 1 → ∀ s, 0 ≤ s → c * (f'' (x + s) - f'' x) - L * s ≤ 0 := by
    intro c hc s hs
    have h1 := hL (x + s)
    rw [show x + s - x = s by ring, abs_of_nonneg hs] at h1
    have : c * (f'' (x + s) - f'' x) ≤ |c| * |f'' (x + s) - f'' x| := by
      rw [← abs_mul]; exact le_abs_self _
    have hL0 : 0 ≤ L * s := (abs_nonneg _).trans h1
    nlinarith [abs_nonneg (f'' (x + s) - f'' x)]
  have key := fun c (hc : |c| ≤ 1) => nonpos_of_second (hd1 c) (hd2 c) (by simp) (by simp)
    (hsec c hc) h hh
  have k1 := key 1 (by simp)
  have k2 := key (-1) (by simp)
  rw [abs_le]; constructor <;> linarith

/-- Second-order Taylor, both signs of `h`. -/
theorem taylor2 {f f' f'' : ℝ → ℝ} {L x : ℝ}
    (hf : ∀ y, HasDerivAt f (f' y) y) (hf' : ∀ y, HasDerivAt f' (f'' y) y)
    (hL : ∀ y, |f'' y - f'' x| ≤ L * |y - x|) (h : ℝ) :
    |f (x + h) - f x - h * f' x - h ^ 2 / 2 * f'' x| ≤ L * |h| ^ 3 / 6 := by
  rcases le_or_gt 0 h with hh | hh
  · rw [abs_of_nonneg hh]; exact taylor2_nonneg hf hf' hL hh
  · -- reflect: `g y = f (-y)`
    have hg : ∀ y, HasDerivAt (fun y => f (-y)) (-f' (-y)) y := by
      intro y; exact ((hf (-y)).comp y (hasDerivAt_neg y)).congr_deriv (by simp)
    have hg' : ∀ y, HasDerivAt (fun y => -f' (-y)) (f'' (-y)) y := by
      intro y; exact ((hf' (-y)).comp y (hasDerivAt_neg y)).neg.congr_deriv (by simp)
    have hL' : ∀ y, |f'' (-y) - f'' (-(-x))| ≤ L * |y - -x| := by
      intro y; rw [neg_neg]
      have := hL (-y); rwa [show -y - x = -(y - -x) by ring, abs_neg] at this
    have := taylor2_nonneg (x := -x) hg hg' hL' (h := -h) (by linarith)
    rw [abs_of_neg hh]
    simp only [neg_neg, show -x + -h = -(x + h) by ring] at this
    convert this using 2; ring

/-! ### Elementary Gaussian maxima -/

theorem sq_mul_exp_le (y : ℝ) : y ^ 2 * Real.exp (-(y ^ 2)) ≤ Real.exp (-1) := by
  have h := Real.add_one_le_exp (y ^ 2 - 1)
  have e : Real.exp (-1) = Real.exp (y ^ 2 - 1) * Real.exp (-(y ^ 2)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e]
  exact mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

/-- `|y| φ-shape ≤ e^{-1/2}`. -/
theorem abs_mul_gaussRaw_le (y : ℝ) : |y| * gaussRaw y ≤ Real.exp (-1 / 2) := by
  have h0 : 0 ≤ |y| * gaussRaw y := mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hsq : (|y| * gaussRaw y) ^ 2 ≤ (Real.exp (-1 / 2)) ^ 2 := by
    rw [mul_pow, sq_abs, gaussRaw, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have := sq_mul_exp_le y
    convert this using 3 <;> push_cast <;> ring
  exact (pow_le_pow_iff_left₀ h0 (Real.exp_pos _).le two_ne_zero).mp hsq


theorem cube_mul_exp_aux (y : ℝ) : y ^ 6 * Real.exp (-(y ^ 2)) ≤ 27 * Real.exp (-3) := by
  set u := y ^ 2 / 3
  have hu : 0 ≤ u := by positivity
  have h1 : u ≤ Real.exp (u - 1) := by linarith [Real.add_one_le_exp (u - 1)]
  have h3 : u ^ 3 ≤ Real.exp (u - 1) ^ 3 := pow_le_pow_left₀ hu h1 3
  rw [← Real.exp_nat_mul] at h3
  have e1 : y ^ 6 = 27 * u ^ 3 := by simp only [u]; ring
  have e2 : Real.exp (-3) = Real.exp (((3:ℕ):ℝ) * (u - 1)) * Real.exp (-(y ^ 2)) := by
    rw [← Real.exp_add]; congr 1; simp only [u]; push_cast; ring
  rw [e1, e2]
  have := Real.exp_pos (-(y ^ 2))
  nlinarith

theorem abs_cube_mul_gaussRaw_le (y : ℝ) :
    |y| ^ 3 * gaussRaw y ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) := by
  have h0 : 0 ≤ |y| ^ 3 * gaussRaw y := mul_nonneg (by positivity) (Real.exp_pos _).le
  have h0' : 0 ≤ 3 * Real.sqrt 3 * Real.exp (-3 / 2) := by positivity
  have hsq : (|y| ^ 3 * gaussRaw y) ^ 2 ≤ (3 * Real.sqrt 3 * Real.exp (-3 / 2)) ^ 2 := by
    have e1 : (|y| ^ 3 * gaussRaw y) ^ 2 = y ^ 6 * Real.exp (-(y ^ 2)) := by
      rw [mul_pow, gaussRaw, ← Real.exp_nat_mul, ← pow_mul, show 3 * 2 = 6 from rfl,
        pow_abs, abs_of_nonneg (by positivity)]
      congr 2; push_cast; ring
    have e2 : (3 * Real.sqrt 3 * Real.exp (-3 / 2)) ^ 2 = 27 * Real.exp (-3) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), ← Real.exp_nat_mul]
      norm_num
    rw [e1, e2]; exact cube_mul_exp_aux y
  exact (pow_le_pow_iff_left₀ h0 h0' two_ne_zero).mp hsq

theorem abs_sq_sub_one_mul_gaussRaw_le (y : ℝ) : |(y ^ 2 - 1) * gaussRaw y| ≤ 1 := by
  have hg : 0 < gaussRaw y := Real.exp_pos _
  rw [abs_mul, abs_of_pos hg]
  rcases le_or_gt (y ^ 2) 1 with h | h
  · have hg1 : gaussRaw y ≤ 1 := by
      unfold gaussRaw; rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg y]
    rw [abs_of_nonpos (by linarith)]
    nlinarith [sq_nonneg y]
  · rw [abs_of_pos (by linarith)]
    have hq := Real.quadratic_le_exp_of_nonneg (show 0 ≤ y ^ 2 / 2 by positivity)
    have e : gaussRaw y * Real.exp (y ^ 2 / 2) = 1 := by
      unfold gaussRaw; rw [← Real.exp_add, show -(y ^ 2) / 2 + y ^ 2 / 2 = 0 by ring, Real.exp_zero]
    have : y ^ 2 - 1 ≤ Real.exp (y ^ 2 / 2) := by nlinarith [sq_nonneg (y ^ 2 - 2)]
    nlinarith

/-! ### `F''` is Lipschitz -/

variable {a b : ℝ}

def dddL (a b z : ℝ) : ℝ := 2 / ((a + b) * b ^ 2) * (((z / b) ^ 2 - 1) * phi (z / b))

theorem hasDerivAt_ddL (hb : 0 < b) (z : ℝ) : HasDerivAt (ddL a b) (dddL a b z) z := by
  have h1 : HasDerivAt (fun z => z / b) (1 / b) z := by
    simpa using ((hasDerivAt_id z).div_const b)
  have h2 : HasDerivAt (fun z => phi (z / b))
      (-(z / b) * gaussRaw (z / b) * (1 / b) / Real.sqrt (2 * Real.pi)) z :=
    ((hasDerivAt_gaussRaw (z / b)).comp z h1).div_const (Real.sqrt (2 * Real.pi))
  have hA : HasDerivAt (fun z => -(2 * z / ((a + b) * b ^ 2))) (-(2 * 1 / ((a + b) * b ^ 2))) z :=
    (((hasDerivAt_id z).const_mul 2).div_const _).neg
  have h3 := hA.mul h2
  show HasDerivAt (fun z => -(2 * z / ((a + b) * b ^ 2)) * phi (z / b)) _ z
  refine h3.congr_deriv ?_
  unfold dddL phi
  have := hb.ne'
  field_simp
  ring

theorem abs_dddL_le (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    |dddL a b z| ≤ 2 / ((a + b) * b ^ 2) / Real.sqrt (2 * Real.pi) := by
  unfold dddL phi
  have hs := sqrt2pi_pos
  rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 / ((a + b) * b ^ 2)), ← mul_div_assoc,
    abs_div, abs_of_pos hs]
  have := abs_sq_sub_one_mul_gaussRaw_le (z / b)
  calc 2 / ((a + b) * b ^ 2) * (|((z / b) ^ 2 - 1) * gaussRaw (z / b)| / Real.sqrt (2 * Real.pi))
      ≤ 2 / ((a + b) * b ^ 2) * (1 / Real.sqrt (2 * Real.pi)) := by gcongr
    _ = _ := by ring

theorem ddL_lipschitz (ha : 0 < a) (hb : 0 < b) (y z : ℝ) :
    |ddL a b y - ddL a b z| ≤ 2 / ((a + b) * b ^ 2) / Real.sqrt (2 * Real.pi) * |y - z| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := ddL a b) (f' := dddL a b)
    (s := Set.univ) (fun x _ => (hasDerivAt_ddL hb x).hasDerivWithinAt)
    (fun x _ => abs_dddL_le ha hb x) convex_univ (Set.mem_univ z) (Set.mem_univ y)
  simpa [Real.norm_eq_abs] using this

/-- `ddR a b = ddL b a`-shape: the right branch, with its own scale. -/
theorem ddR_eq (z : ℝ) : ddR a b z = ddL b a z := by
  simp only [ddR, ddL, add_comm a b]

theorem ddR_lipschitz (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (y z : ℝ) :
    |ddR a b y - ddR a b z| ≤ 2 / ((a + b) * b ^ 2) / Real.sqrt (2 * Real.pi) * |y - z| := by
  rw [ddR_eq, ddR_eq]
  refine (ddL_lipschitz hb ha y z).trans ?_
  rw [add_comm b a]
  gcongr

/-- Lipschitz constant of `F''`: `2φ₀/((a+b)b²)`. -/
def lipF (a b : ℝ) : ℝ := 2 / ((a + b) * b ^ 2) / Real.sqrt (2 * Real.pi)

theorem lipF_nonneg (ha : 0 < a) (hb : 0 < b) : 0 ≤ lipF a b := by
  unfold lipF; have := sqrt2pi_pos; positivity

theorem prof''_lipschitz (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (y z : ℝ) :
    |prof'' a b y - prof'' a b z| ≤ lipF a b * |y - z| := by
  have hL0 : ddL a b 0 = 0 := by simp [ddL]
  have hR0 : ddR a b 0 = 0 := by simp [ddR]
  have cross : ∀ y z, y ≤ 0 → 0 < z →
      |ddL a b y - ddR a b z| ≤ lipF a b * |y - z| := by
    intro y z hy hz
    have h1 := ddL_lipschitz (a := a) ha hb y 0
    have h2 := ddR_lipschitz ha hb hab 0 z
    rw [hL0, sub_zero] at h1; rw [hR0, zero_sub, abs_neg] at h2
    calc |ddL a b y - ddR a b z| ≤ |ddL a b y| + |ddR a b z| := abs_sub _ _
      _ ≤ lipF a b * |y - 0| + lipF a b * |0 - z| := add_le_add h1 h2
      _ = lipF a b * |y - z| := by
          rw [sub_zero, zero_sub, abs_neg, abs_of_nonpos hy, abs_of_pos hz,
            abs_of_nonpos (by linarith)]; ring
  unfold prof''
  split_ifs with hy hz hz
  · exact ddL_lipschitz ha hb y z
  · exact cross y z hy (lt_of_not_ge hz)
  · rw [abs_sub_comm, abs_sub_comm y z]; exact cross z y hz (lt_of_not_ge hy)
  · exact ddR_lipschitz ha hb hab y z


theorem gaussRaw_pos (y : ℝ) : 0 < gaussRaw y := Real.exp_pos _

/-! ### Time derivatives of `u(t,x) = F(x/√t)` -/

theorem hasDerivAt_comp_scale {G G' : ℝ → ℝ} (hG : ∀ z, HasDerivAt G (G' z) z)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun t => G (x / Real.sqrt t))
      (-(x / Real.sqrt t) * G' (x / Real.sqrt t) / (2 * t)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have h1 := (hasDerivAt_const t x).div (Real.hasDerivAt_sqrt ht.ne') hs.ne'
  have h := (hG (x / Real.sqrt t)).comp t h1
  refine h.congr_deriv ?_
  rw [Real.sq_sqrt ht.le]
  field_simp
  ring

/-- `ψ(z) = -z F'(z)/2`, so that `u_t(t,x) = ψ(x/√t)/t`. -/
def psi (a b z : ℝ) : ℝ := -(z * prof' a b z) / 2
def psi' (a b z : ℝ) : ℝ := -(prof' a b z + z * prof'' a b z) / 2

theorem hasDerivAt_psi (ha : 0 < a) (hb : 0 < b) (z : ℝ) :
    HasDerivAt (psi a b) (psi' a b z) z := by
  have := (((hasDerivAt_id z).mul (hasDerivAt_prof' ha hb z)).neg).div_const 2
  exact this.congr_deriv (by simp [psi'])

/-- The time derivative `u_t`, as a function of `t`. -/
def ut (a b x t : ℝ) : ℝ := psi a b (x / Real.sqrt t) / t
/-- `u_tt = (3 z F' + z² F'')/(4t²)`. -/
def utt (a b x t : ℝ) : ℝ :=
  (3 * (x / Real.sqrt t) * prof' a b (x / Real.sqrt t) +
    (x / Real.sqrt t) ^ 2 * prof'' a b (x / Real.sqrt t)) / (4 * t ^ 2)

theorem hasDerivAt_u_t' (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun t => prof a b (x / Real.sqrt t)) (ut a b x t) t := by
  refine (hasDerivAt_comp_scale (hasDerivAt_prof ha hb) ht x).congr_deriv ?_
  simp only [ut, psi]
  field_simp

theorem hasDerivAt_ut (ha : 0 < a) (hb : 0 < b) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    HasDerivAt (ut a b x) (utt a b x t) t := by
  have h1 := hasDerivAt_comp_scale (hasDerivAt_psi ha hb) ht x
  have h2 := h1.div (hasDerivAt_id t) ht.ne'
  refine h2.congr_deriv ?_
  simp only [utt, psi, psi', id]
  field_simp
  ring

/-- `zF'(z)` bound. -/
theorem abs_z_prof'_le (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (z : ℝ) :
    |z * prof' a b z| ≤ 2 * a / (a + b) * (Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi)) := by
  have hs := sqrt2pi_pos
  have key : ∀ s, 0 < s → s ≤ a →
      |z * (2 / (a + b) * phi (z / s))| ≤
        2 * a / (a + b) * (Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi)) := by
    intro s hs0 hsa
    have e : z * (2 / (a + b) * phi (z / s)) =
        2 * s / (a + b) * ((z / s) * gaussRaw (z / s) / Real.sqrt (2 * Real.pi)) := by
      unfold phi; field_simp
    rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * s / (a + b)), abs_div,
      abs_of_pos hs, abs_mul, abs_of_pos (gaussRaw_pos _)]
    have := abs_mul_gaussRaw_le (z / s)
    have h1 : |z / s| * gaussRaw (z / s) / Real.sqrt (2 * Real.pi) ≤
        Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi) := by gcongr
    have h2 : 2 * s / (a + b) ≤ 2 * a / (a + b) := by gcongr
    have h3 : 0 ≤ |z / s| * gaussRaw (z / s) / Real.sqrt (2 * Real.pi) := by
      have := (Real.exp_pos _ : 0 < gaussRaw (z / s)); positivity
    calc 2 * s / (a + b) * (|z / s| * gaussRaw (z / s) / Real.sqrt (2 * Real.pi))
        ≤ 2 * a / (a + b) * (|z / s| * gaussRaw (z / s) / Real.sqrt (2 * Real.pi)) := by gcongr
      _ ≤ _ := by gcongr
  unfold prof' dL dR
  split_ifs
  · exact key b hb hab
  · exact key a ha le_rfl

theorem abs_z2_prof''_le (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) (z : ℝ) :
    |z ^ 2 * prof'' a b z| ≤
      2 * a / (a + b) * (3 * Real.sqrt 3 * Real.exp (-3 / 2) / Real.sqrt (2 * Real.pi)) := by
  have hs := sqrt2pi_pos
  have key : ∀ s, 0 < s → s ≤ a →
      |z ^ 2 * (-(2 * z / ((a + b) * s ^ 2)) * phi (z / s))| ≤
        2 * a / (a + b) * (3 * Real.sqrt 3 * Real.exp (-3 / 2) / Real.sqrt (2 * Real.pi)) := by
    intro s hs0 hsa
    have e : |z ^ 2 * (-(2 * z / ((a + b) * s ^ 2)) * phi (z / s))| =
        2 * s / (a + b) * (|z / s| ^ 3 * gaussRaw (z / s) / Real.sqrt (2 * Real.pi)) := by
      rw [show z ^ 2 * (-(2 * z / ((a + b) * s ^ 2)) * phi (z / s)) =
          -(2 * s / (a + b) * ((z / s) ^ 3 * gaussRaw (z / s) / Real.sqrt (2 * Real.pi))) by
          unfold phi; field_simp]
      rw [abs_neg, abs_mul, abs_of_pos (by positivity : 0 < 2 * s / (a + b)), abs_div,
        abs_of_pos hs, abs_mul, abs_of_pos (gaussRaw_pos _), abs_pow]
    rw [e]
    have := abs_cube_mul_gaussRaw_le (z / s)
    have h3 : 0 ≤ |z / s| ^ 3 * gaussRaw (z / s) / Real.sqrt (2 * Real.pi) := by
      have := (Real.exp_pos _ : 0 < gaussRaw (z / s)); positivity
    calc 2 * s / (a + b) * (|z / s| ^ 3 * gaussRaw (z / s) / Real.sqrt (2 * Real.pi))
        ≤ 2 * a / (a + b) * (|z / s| ^ 3 * gaussRaw (z / s) / Real.sqrt (2 * Real.pi)) := by
          gcongr
      _ ≤ _ := by gcongr
  unfold prof'' ddL ddR
  split_ifs
  · exact key b hb hab
  · exact key a ha le_rfl

/-- The constant `B` of the note. -/
def constB (a b : ℝ) : ℝ :=
  a / Real.sqrt (2 * Real.pi) / (2 * (a + b)) *
    (3 * Real.exp (-1 / 2) + 3 * Real.sqrt 3 * Real.exp (-3 / 2))

theorem abs_utt_le (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |utt a b x t| ≤ constB a b / t ^ 2 := by
  set z := x / Real.sqrt t
  have h1 := abs_z_prof'_le ha hb hab z
  have h2 := abs_z2_prof''_le ha hb hab z
  unfold utt
  rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 4 * t ^ 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : |3 * z * prof' a b z + z ^ 2 * prof'' a b z| ≤
      3 * |z * prof' a b z| + |z ^ 2 * prof'' a b z| := by
    calc _ ≤ |3 * z * prof' a b z| + |z ^ 2 * prof'' a b z| := abs_add_le _ _
      _ = _ := by rw [mul_assoc, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 3)]
  have h4 : 3 * |z * prof' a b z| + |z ^ 2 * prof'' a b z| ≤ 4 * constB a b := by
    unfold constB
    have := sqrt2pi_pos
    have e : 4 * (a / Real.sqrt (2 * Real.pi) / (2 * (a + b)) *
        (3 * Real.exp (-1 / 2) + 3 * Real.sqrt 3 * Real.exp (-3 / 2))) =
        3 * (2 * a / (a + b) * (Real.exp (-1 / 2) / Real.sqrt (2 * Real.pi))) +
        2 * a / (a + b) * (3 * Real.sqrt 3 * Real.exp (-3 / 2) / Real.sqrt (2 * Real.pi)) := by
      field_simp; ring
    rw [e]; linarith
  have : 0 ≤ t ^ 2 := by positivity
  nlinarith

/-- Time Taylor step: `|u(t+1) - u(t) - u_t(t)| ≤ B/(2t²)`. -/
theorem time_step (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |prof a b (x / Real.sqrt (t + 1)) - prof a b (x / Real.sqrt t) - ut a b x t| ≤
      constB a b / (2 * t ^ 2) := by
  have hB : 0 ≤ constB a b := by unfold constB; have := sqrt2pi_pos; positivity
  have hd1 : ∀ c : ℝ, ∀ s, 0 ≤ s → HasDerivAt
      (fun s => c * (prof a b (x / Real.sqrt (t + s)) - prof a b (x / Real.sqrt t) - s * ut a b x t)
        - constB a b / t ^ 2 * s ^ 2 / 2)
      (c * (ut a b x (t + s) - ut a b x t) - constB a b / t ^ 2 * s) s := by
    intro c s hs
    have h0 := (hasDerivAt_u_t' ha hb (by linarith : 0 < t + s) x).comp s
      ((hasDerivAt_id s).const_add t)
    have := ((((h0.sub_const (prof a b (x / Real.sqrt t))).sub ((hasDerivAt_id s).mul_const (ut a b x t))).const_mul c).sub
      (((hasDerivAt_pow 2 s).const_mul (constB a b / t ^ 2)).div_const 2))
    exact this.congr_deriv (by simp; ring)
  have hd2 : ∀ c : ℝ, ∀ s, 0 ≤ s → HasDerivAt
      (fun s => c * (ut a b x (t + s) - ut a b x t) - constB a b / t ^ 2 * s)
      (c * utt a b x (t + s) - constB a b / t ^ 2) s := by
    intro c s hs
    have h0 := (hasDerivAt_ut ha hb (by linarith : 0 < t + s) x).comp s
      ((hasDerivAt_id s).const_add t)
    have := (((h0.sub_const (ut a b x t)).const_mul c).sub ((hasDerivAt_id s).const_mul (constB a b / t ^ 2)))
    exact this.congr_deriv (by simp)
  have hsec : ∀ c : ℝ, |c| ≤ 1 → ∀ s, 0 ≤ s → c * utt a b x (t + s) - constB a b / t ^ 2 ≤ 0 := by
    intro c hc s hs
    have h1 := abs_utt_le ha hb hab (by linarith : 0 < t + s) x
    have h2 : constB a b / (t + s) ^ 2 ≤ constB a b / t ^ 2 := by
      apply div_le_div_of_nonneg_left hB (by positivity); nlinarith
    have : c * utt a b x (t + s) ≤ |c| * |utt a b x (t + s)| := by
      rw [← abs_mul]; exact le_abs_self _
    nlinarith [abs_nonneg (utt a b x (t + s))]
  have key := fun c (hc : |c| ≤ 1) => nonpos_of_second (hd1 c) (hd2 c) (by simp) (by simp)
    (hsec c hc) 1 zero_le_one
  have k1 := key 1 (by simp)
  have k2 := key (-1) (by simp)
  simp only [one_mul, one_pow, mul_one, neg_mul] at k1 k2
  rw [abs_le]
  have e : constB a b / (2 * t ^ 2) = constB a b / t ^ 2 / 2 := by field_simp
  rw [e]
  constructor <;> linarith


/-! ### The family and the defect -/

theorem inf'_close {ι : Type*} {s : Finset ι} (hs : s.Nonempty) {E Q : ι → ℝ} {c ε : ℝ}
    (h : ∀ j ∈ s, |E j - (c + Q j)| ≤ ε) : |s.inf' hs E - (c + s.inf' hs Q)| ≤ ε := by
  obtain ⟨j1, hj1, e1⟩ := Finset.exists_mem_eq_inf' hs Q
  obtain ⟨j2, hj2, e2⟩ := Finset.exists_mem_eq_inf' hs E
  have a1 := (abs_le.mp (h j1 hj1)).2
  have a2 := (abs_le.mp (h j2 hj2)).1
  have b1 : s.inf' hs E ≤ E j1 := Finset.inf'_le _ hj1
  have b2 : s.inf' hs Q ≤ Q j2 := Finset.inf'_le _ hj2
  rw [abs_le]; constructor <;> linarith

namespace IncFamily
variable (F : IncFamily)

def sig2 (j : Fin F.nA) : ℝ := ∑ y, F.P j y * F.X j y ^ 2
def sigma (j : Fin F.nA) : ℝ := Real.sqrt (F.sig2 j)
/-- `a = max_j σ_j`. -/
def sA : ℝ := Finset.univ.sup' F.univ_nonempty F.sigma
/-- `b = min_j σ_j`. -/
def sB : ℝ := Finset.univ.inf' F.univ_nonempty F.sigma

theorem sig2_nonneg (j) : 0 ≤ F.sig2 j :=
  Finset.sum_nonneg fun y _ => mul_nonneg (F.Ppos _ _).le (sq_nonneg _)

theorem sigma_sq (j) : F.sigma j ^ 2 = F.sig2 j := Real.sq_sqrt (F.sig2_nonneg j)

theorem sB_le_sigma (j) : F.sB ≤ F.sigma j := Finset.inf'_le _ (Finset.mem_univ j)
theorem sigma_le_sA (j) : F.sigma j ≤ F.sA := Finset.le_sup' _ (Finset.mem_univ j)
theorem sB_le_sA : F.sB ≤ F.sA := (F.sB_le_sigma ⟨0, F.hA⟩).trans (F.sigma_le_sA _)

/-- `u_t = min_j σ_j²/2 u_xx`, indexed by actions. -/
theorem pde_family (hb : 0 < F.sB) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    ut F.sA F.sB x t = Finset.univ.inf' F.univ_nonempty
      (fun j => F.sig2 j / 2 * (prof'' F.sA F.sB (x / Real.sqrt t) / t)) := by
  have ha : 0 < F.sA := lt_of_lt_of_le hb F.sB_le_sA
  set z := x / Real.sqrt t
  have hpe := prof''_eq ha hb z
  have eut : ut F.sA F.sB x t = -z * prof' F.sA F.sB z / (2 * t) := by
    simp only [ut, psi, z]; field_simp
  rw [eut]
  obtain ⟨jb, -, hjb⟩ := Finset.exists_mem_eq_inf' F.univ_nonempty F.sigma
  obtain ⟨ja, -, hja⟩ := Finset.exists_mem_eq_sup' F.univ_nonempty F.sigma
  have sb : F.sig2 jb = F.sB ^ 2 := by rw [← F.sigma_sq, ← hjb]; rfl
  have sa : F.sig2 ja = F.sA ^ 2 := by rw [← F.sigma_sq, ← hja]; rfl
  by_cases hz : z ≤ 0
  · have hn : 0 ≤ prof'' F.sA F.sB z / t := div_nonneg (prof''_nonneg_of_nonpos ha hb hz) ht.le
    have e : -z * prof' F.sA F.sB z / (2 * t) = F.sB ^ 2 / 2 * (prof'' F.sA F.sB z / t) := by
      rw [hpe, if_pos hz]; field_simp
    rw [e]
    apply le_antisymm
    · apply Finset.le_inf'; intro j _
      have h1 := F.sB_le_sigma j
      have : F.sB ^ 2 ≤ F.sig2 j := by rw [← F.sigma_sq]; exact pow_le_pow_left₀ hb.le h1 2
      nlinarith
    · refine (Finset.inf'_le _ (Finset.mem_univ jb)).trans (le_of_eq ?_)
      simp only [sb]
  · have hzp : 0 < z := lt_of_not_ge hz
    have hn : prof'' F.sA F.sB z / t ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (prof''_nonpos_of_pos ha hb hzp) ht.le
    have e : -z * prof' F.sA F.sB z / (2 * t) = F.sA ^ 2 / 2 * (prof'' F.sA F.sB z / t) := by
      rw [hpe, if_neg hz]; field_simp
    rw [e]
    apply le_antisymm
    · apply Finset.le_inf'; intro j _
      have h1 := F.sigma_le_sA j
      have h0 : 0 ≤ F.sigma j := Real.sqrt_nonneg _
      have : F.sig2 j ≤ F.sA ^ 2 := by rw [← F.sigma_sq]; exact pow_le_pow_left₀ h0 h1 2
      nlinarith
    · refine (Finset.inf'_le _ (Finset.mem_univ ja)).trans (le_of_eq ?_)
      simp only [sa]

theorem abs_cube_le (j y) : |F.X j y| ^ 3 ≤ F.M ^ 3 :=
  pow_le_pow_left₀ (abs_nonneg _) (F.abs_X_le j y) 3

/-- Spatial Taylor step, uniform in `x`. -/
theorem space_step (hc : F.Centered) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : b ≤ a)
    {t : ℝ} (ht : 0 < t) (x : ℝ) (j : Fin F.nA) :
    |F.expect j (fun y => prof a b (y / Real.sqrt t)) x -
        (prof a b (x / Real.sqrt t) + F.sig2 j / 2 * (prof'' a b (x / Real.sqrt t) / t))| ≤
      lipF a b * F.M ^ 3 / 6 / (t * Real.sqrt t) := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  set f := fun y => prof a b (y / Real.sqrt t)
  set f' := fun y => prof' a b (y / Real.sqrt t) / Real.sqrt t
  set f'' := fun y => prof'' a b (y / Real.sqrt t) / t
  set L := lipF a b / (t * Real.sqrt t)
  have hL0 : 0 ≤ L := div_nonneg (lipF_nonneg ha hb) (by positivity)
  have hf : ∀ y, HasDerivAt f (f' y) y := fun y => hasDerivAt_u_x ha hb ht y
  have hf' : ∀ y, HasDerivAt f' (f'' y) y := fun y => hasDerivAt_u_xx ha hb ht y
  have hLip : ∀ y, |f'' y - f'' x| ≤ L * |y - x| := by
    intro y
    simp only [f'', L]
    rw [← sub_div, abs_div, abs_of_pos ht]
    have := prof''_lipschitz ha hb hab (y / Real.sqrt t) (x / Real.sqrt t)
    rw [← sub_div, abs_div, abs_of_pos hs] at this
    rw [div_le_iff₀ ht]
    calc |prof'' a b (y / Real.sqrt t) - prof'' a b (x / Real.sqrt t)|
        ≤ lipF a b * (|y - x| / Real.sqrt t) := this
      _ = lipF a b / (t * Real.sqrt t) * |y - x| * t := by field_simp
  have hT : ∀ y, |f (x + -F.X j y) - f x - (-F.X j y) * f' x - (-F.X j y) ^ 2 / 2 * f'' x| ≤
      L * F.M ^ 3 / 6 := by
    intro y
    refine (taylor2 hf hf' hLip (-F.X j y)).trans ?_
    rw [abs_neg]
    have := F.abs_cube_le j y
    gcongr
  have e : F.expect j f x - (f x + F.sig2 j / 2 * f'' x) =
      ∑ y, F.P j y * (f (x + -F.X j y) - f x - (-F.X j y) * f' x - (-F.X j y) ^ 2 / 2 * f'' x) := by
    have h1 := F.Psum j
    have h2 := hc j
    simp only [expect, sig2]
    have : ∑ y, F.P j y * (f (x + -F.X j y) - f x - (-F.X j y) * f' x - (-F.X j y) ^ 2 / 2 * f'' x)
        = ∑ y, F.P j y * f (x - F.X j y) - (∑ y, F.P j y) * f x + (∑ y, F.P j y * F.X j y) * f' x
          - (∑ y, F.P j y * F.X j y ^ 2) / 2 * f'' x := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_div, Finset.sum_mul,
        ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro y _
      rw [show x + -F.X j y = x - F.X j y by ring]; ring
    rw [this, h1, h2]; ring
  change |F.expect j f x - (f x + F.sig2 j / 2 * f'' x)| ≤ _
  rw [e]
  calc |∑ y, F.P j y * _| ≤ ∑ y, |F.P j y * (f (x + -F.X j y) - f x - (-F.X j y) * f' x -
        (-F.X j y) ^ 2 / 2 * f'' x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y, F.P j y * (L * F.M ^ 3 / 6) := by
        apply Finset.sum_le_sum; intro y _
        rw [abs_mul, abs_of_pos (F.Ppos j y)]
        exact mul_le_mul_of_nonneg_left (hT y) (F.Ppos j y).le
    _ = L * F.M ^ 3 / 6 := by rw [← Finset.sum_mul, F.Psum, one_mul]
    _ = _ := by simp only [L]; field_simp

/-- The constant `A = M³φ₀/(3(a+b)b²)` of the note. -/
def constA (a b : ℝ) : ℝ := lipF a b * F.M ^ 3 / 6

theorem constA_eq (a b : ℝ) :
    F.constA a b = F.M ^ 3 * (1 / Real.sqrt (2 * Real.pi)) / (3 * (a + b) * b ^ 2) := by
  have := sqrt2pi_pos
  simp only [constA, lipF]
  rcases eq_or_ne (a + b) 0 with h | h
  · simp [h]
  rcases eq_or_ne b 0 with h' | h'
  · simp [h']
  field_simp
  ring

/-- **Lemma (One-step defect).** For every `t > 0`,
`‖T u(t,·) - u(t+1,·)‖∞ ≤ A t^{-3/2} + (B/2) t^{-2}`, here pointwise in `x`. -/
theorem one_step_defect (hc : F.Centered) (hb : 0 < F.sB) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    |F.T (fun y => prof F.sA F.sB (y / Real.sqrt t)) x - prof F.sA F.sB (x / Real.sqrt (t + 1))| ≤
      F.constA F.sA F.sB / (t * Real.sqrt t) + constB F.sA F.sB / (2 * t ^ 2) := by
  have hab := F.sB_le_sA
  have ha : 0 < F.sA := lt_of_lt_of_le hb hab
  have h1 : |F.T (fun y => prof F.sA F.sB (y / Real.sqrt t)) x -
      (prof F.sA F.sB (x / Real.sqrt t) + ut F.sA F.sB x t)| ≤
      F.constA F.sA F.sB / (t * Real.sqrt t) := by
    rw [F.pde_family hb ht x]
    exact inf'_close F.univ_nonempty fun j _ => F.space_step hc ha hb hab ht x j
  have h2 := time_step ha hb hab ht x
  have h3 := abs_sub_le (F.T (fun y => prof F.sA F.sB (y / Real.sqrt t)) x)
    (prof F.sA F.sB (x / Real.sqrt t) + ut F.sA F.sB x t) (prof F.sA F.sB (x / Real.sqrt (t + 1)))
  have h4 : |prof F.sA F.sB (x / Real.sqrt t) + ut F.sA F.sB x t -
      prof F.sA F.sB (x / Real.sqrt (t + 1))| =
      |prof F.sA F.sB (x / Real.sqrt (t + 1)) - prof F.sA F.sB (x / Real.sqrt t) -
        ut F.sA F.sB x t| := by
    rw [abs_sub_comm]; ring_nf
  linarith

#print axioms one_step_defect

end IncFamily
end CausalSpectrum.Sqrt

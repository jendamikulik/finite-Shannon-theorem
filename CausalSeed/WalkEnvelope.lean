/-
The exact envelope identity for a stationary two-action kernel with one uniform action.

Action `0` returns a uniform symbol from `m` symbols, action `1` returns a symbol with a
strictly positive law `Q`. With `h = log₂ m` and `X = -log₂ Q(Y) - h`, the lower envelope at
horizon `n` is the law of the random-walk maximum: `F*_n(n h + x) = P(M_n ≤ x)`.
-/
import CausalSeed.WalkMax
import CausalSeed.DyadicKernel

noncomputable section
open Classical Finset MeasureTheory Set

namespace CausalSpectrum.Walk

/-- A two-action kernel: uniform on `m` symbols, and a strictly positive law `Q`. -/
structure TwoAction where
  m : ℕ
  hm : 0 < m
  k : ℕ
  hk : 0 < k
  Q : Fin k → ℝ
  Qpos : ∀ y, 0 < Q y
  Qsum : ∑ y, Q y = 1

namespace TwoAction
variable (A : TwoAction)

/-- `h = log₂ m`. -/
def h : ℝ := Real.logb 2 A.m

def nY (a : Fin 2) : ℕ := if a.val = 0 then A.m else A.k

def K (a : Fin 2) (y : Fin (A.nY a)) : ℝ :=
  if ha : a.val = 0 then 1 / A.m else A.Q ⟨y.val, by have := y.isLt; simp only [nY, ha] at this; exact this⟩

theorem nY0 : A.nY 0 = A.m := rfl
theorem nY1 : A.nY 1 = A.k := rfl

theorem sum_K (a : Fin 2) : ∑ y, A.K a y = 1 := by
  fin_cases a
  · show ∑ _y : Fin A.m, (1 / (A.m : ℝ)) = 1
    rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp [A.hm.ne']
  · exact A.Qsum

/-- The stationary kernel of the two actions. -/
def kernel : Kernel where
  nA := 2
  hA := by norm_num
  nY := A.nY
  hY a := by fin_cases a; exacts [A.hm, A.hk]
  K := A.K
  Kpos a y := by
    fin_cases a
    · show (0:ℝ) < 1 / A.m; have := A.hm; positivity
    · exact A.Qpos _
  Ksum := A.sum_K

/-- The increment law of `Q`: `X(y) = -log₂ Q(y) - h`. -/
def law : Law where
  k := A.k
  Q := A.Q
  Qnn y := (A.Qpos y).le
  Qsum := A.Qsum
  X y := infoMass (A.Q y) - A.h

theorem infoMass_unif : infoMass (1 / (A.m : ℝ)) = A.h := by
  unfold infoMass h
  rw [one_div, Real.logb_inv]; ring

theorem h_nonneg : 0 ≤ A.h := by
  unfold h
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast A.hm)

theorem G_eq_cdfM : ∀ (n : ℕ) (x : ℝ), (A.kernel.fam A.h).G n x = A.law.cdfM n x
  | 0, x => by rw [Law.cdfM_zero]; rfl
  | n + 1, x => by
    have e0 : (A.kernel.fam A.h).expect (0 : Fin 2) ((A.kernel.fam A.h).G n) x = A.law.cdfM n x := by
      show ∑ _y : Fin A.m, (1 / (A.m : ℝ)) *
          (A.kernel.fam A.h).G n (x - (infoMass (1 / (A.m : ℝ)) - A.h)) = _
      rw [infoMass_unif, sub_self, sub_zero, G_eq_cdfM n x, sum_const, card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      field_simp [A.hm.ne']
    have e1 : (A.kernel.fam A.h).expect (1 : Fin 2) ((A.kernel.fam A.h).G n) x =
        ∑ y, A.law.Q y * A.law.cdfM n (x - A.law.X y) := by
      show ∑ y : Fin A.k, A.Q y * (A.kernel.fam A.h).G n (x - (infoMass (A.Q y) - A.h)) = _
      simp only [G_eq_cdfM n]; rfl
    have hG : (A.kernel.fam A.h).G (n + 1) x =
        min (A.law.cdfM n x) (∑ y, A.law.Q y * A.law.cdfM n (x - A.law.X y)) := by
      apply le_antisymm
      · rw [← e0, ← e1]
        exact le_min ((A.kernel.fam A.h).T_le _ x (0 : Fin 2)) ((A.kernel.fam A.h).T_le _ x (1 : Fin 2))
      · refine (A.kernel.fam A.h).le_T fun a => ?_
        fin_cases a
        · rw [← e0]; exact min_le_left _ _
        · rw [← e1]; exact min_le_right _ _
    rw [hG, Law.cdfM_succ]
    by_cases hx : 0 ≤ x
    · rw [if_pos hx, min_eq_right]
      have := A.law.cdfM_succ_le n x
      rwa [Law.cdfM_succ, if_pos hx] at this
    · rw [if_neg hx, A.law.cdfM_neg n (not_le.1 hx), min_eq_left]
      exact sum_nonneg fun y _ => mul_nonneg (A.law.Qnn y) (A.law.cdfM_nonneg n _)

/-- **Exact envelope identity.** `F*_n(n h + x) = P(M_n ≤ x)` for every real `x`. -/
theorem envelope_eq_cdfM (n : ℕ) (x : ℝ) :
    Fstar (A.kernel.rounds n) (n * A.h + x) = A.law.cdfM n x := by
  rw [A.kernel.Fstar_eq_G A.h, show (n : ℝ) * A.h + x - n * A.h = x by ring, G_eq_cdfM]

theorem integral_ind {v : ℝ} (hv : 0 ≤ v) :
    ∫ t in Ioi (0:ℝ), (if t < v then (1:ℝ) else 0) = v := by
  have : (fun t : ℝ => if t < v then (1:ℝ) else 0) = (Iio v).indicator fun _ => 1 := by
    funext t; simp [Set.indicator, Set.mem_Iio]
  rw [this, setIntegral_indicator measurableSet_Iio, Ioi_inter_Iio, setIntegral_const,
    smul_eq_mul, mul_one, Measure.real, Real.volume_Ioo, sub_zero, ENNReal.toReal_ofReal hv]

theorem integrableOn_ind (v : ℝ) :
    IntegrableOn (fun t : ℝ => if t < v then (1:ℝ) else 0) (Ioi 0) := by
  have : (fun t : ℝ => if t < v then (1:ℝ) else 0) = (Iio v).indicator fun _ => 1 := by
    funext t; simp [Set.indicator, Set.mem_Iio]
  rw [this, IntegrableOn, integrable_indicator_iff measurableSet_Iio, IntegrableOn,
    Measure.restrict_restrict measurableSet_Iio, Iio_inter_Ioi]
  exact integrableOn_const (by simp) (by simp)

/-- **Mean identity.** `L_n = n h + E M_n`. -/
theorem envelopeMean_eq (n : ℕ) : envelopeMean (A.kernel.rounds n) = n * A.h + A.law.EM n := by
  rw [← integral_one_sub_Fstar]
  have hf : ∀ t : ℝ, 1 - Fstar (A.kernel.rounds n) t =
      ∑ ys : Fin n → Fin A.law.k, A.law.wgt ys *
        (if t < n * A.h + M (A.law.seq ys) n then (1:ℝ) else 0) := by
    intro t
    rw [show t = n * A.h + (t - n * A.h) by ring, envelope_eq_cdfM,
      show n * A.h + (t - n * A.h) = t by ring, Law.cdfM, Law.E]
    nth_rewrite 1 [← A.law.sum_wgt n]
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun ys _ => ?_
    by_cases hc : M (A.law.seq ys) n ≤ t - n * A.h
    · rw [if_pos hc, if_neg (by linarith)]; ring
    · rw [if_neg hc, if_pos (by linarith)]; ring
  simp only [hf]
  rw [integral_finset_sum _ fun ys _ => (integrableOn_ind _).const_mul _]
  simp only [integral_const_mul]
  rw [show (n : ℝ) * A.h + A.law.EM n = A.law.E n (fun x => n * A.h + M x n) by
    rw [Law.E_add, Law.E_const]; rfl]
  refine sum_congr rfl fun ys _ => ?_
  rw [integral_ind (add_nonneg (mul_nonneg (Nat.cast_nonneg n) A.h_nonneg) (M_nonneg _ _))]

/-- **General sandwich.** `n h + E M_n ≤ C_n ≤ n h + E M_n + c⋆` (bits). -/
theorem cost_sandwich (n : ℕ) :
    n * A.h + A.law.EM n ≤ A.kernel.costBits n ∧
      A.kernel.costBits n ≤ n * A.h + A.law.EM n + shannonOverhead := by
  rw [← envelopeMean_eq]; exact A.kernel.costBits_sandwich n

/-- **Spitzer form of the sandwich.** -/
theorem cost_sandwich_spitzer (n : ℕ) :
    n * A.h + ∑ j ∈ range n, A.law.ESp (j + 1) / (j + 1) ≤ A.kernel.costBits n ∧
      A.kernel.costBits n ≤ n * A.h + ∑ j ∈ range n, A.law.ESp (j + 1) / (j + 1) +
        shannonOverhead := by
  rw [← Law.spitzer]; exact A.cost_sandwich n

/-- Dyadic assumptions: `m = 2^d` and every atom of `Q` is a power of `1/2`. -/
def Dyadic (d : ℕ) : Prop := A.m = 2 ^ d ∧ ∀ y, ∃ c : ℕ, A.Q y = (1 / 2 : ℝ) ^ c

theorem h_of_dyadic {d : ℕ} (hd : A.Dyadic d) : A.h = d := by
  unfold h; rw [hd.1]; push_cast; rw [Real.logb_pow]; simp

theorem isDyadic {d : ℕ} (hd : A.Dyadic d) : A.kernel.IsDyadic := by
  intro a y
  fin_cases a
  · refine ⟨d, ?_⟩
    show 1 / (A.m : ℝ) = (1 / 2) ^ d
    rw [hd.1]; push_cast; rw [one_div_pow]
  · exact hd.2 _

/-- **Exact cost.** Under the dyadic assumptions, `C_n = n h + E M_n`. -/
theorem cost_eq {d : ℕ} (hd : A.Dyadic d) (n : ℕ) :
    A.kernel.costBits n = n * A.h + A.law.EM n := by
  rw [A.kernel.cost_eq_envelope_of_dyadic (A.isDyadic hd), envelopeMean_eq]

/-- **Exact cost, Spitzer form.** `C_n = n h + ∑_{k=1}^n E(S_k)_+ / k`. -/
theorem cost_eq_spitzer {d : ℕ} (hd : A.Dyadic d) (n : ℕ) :
    A.kernel.costBits n = n * A.h + ∑ j ∈ range n, A.law.ESp (j + 1) / (j + 1) := by
  rw [cost_eq A hd, Law.spitzer]

end TwoAction
end CausalSpectrum.Walk

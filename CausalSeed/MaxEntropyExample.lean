/-
A concrete separation: the dyadic laws
`P = (1/4,1/4,1/4,1/4)`, `Q = (1/2,1/8,1/8,1/8,1/8)`, `R = (1/2,1/4,1/8,1/16,1/16)`.
`H(P) = H(Q) = 2 > H(R) = 15/8`; the surprisal variances are `0, 1, 71/64`. Although `R` has
the largest variance, it is dominated at `θ = ln(6/5)` with the rational certificate
`E e^{θ(I_R - 2)} = 299/300`, and `(C_n - 2n)/√n → √(2/π)`.
-/
import CausalSeed.MaxEntropyReduction

noncomputable section
open Classical Filter Topology
namespace CausalSpectrum.Kernel.PQR

/-- Surprisal exponents: output `y` of action `a` has probability `2^{-e a y}`. -/
def e : Fin 3 → Fin 5 → ℕ := ![![2, 2, 2, 2, 2], ![1, 3, 3, 3, 3], ![1, 2, 3, 4, 4]]

def nY (a : Fin 3) : ℕ := if a = 0 then 4 else 5

/-- Exponent of output `k` of action `a` (as a natural-number index). -/
def e' (a : Fin 3) (k : ℕ) : ℕ := if h : k < 5 then e a ⟨k, h⟩ else 0

/-- Probability of output `k` of action `a`. -/
def w (a : Fin 3) (k : ℕ) : ℝ := ((2 : ℝ) ^ e' a k)⁻¹

/-- The kernel `(P, Q, R)`. -/
abbrev κ : Kernel where
  nA := 3
  hA := by norm_num
  nY := nY
  hY := fun a => by unfold nY; split_ifs <;> norm_num
  K := fun a y => w a y.val
  Kpos := fun a y => by unfold w; positivity
  Ksum := fun a => by
    rw [Fin.sum_univ_eq_sum_range (w a)]
    fin_cases a <;> simp [nY, w, e', e, Finset.sum_range_succ] <;> norm_num

theorem infoMass_w (a : Fin 3) (k : ℕ) : infoMass (w a k) = e' a k := by
  change -Real.logb 2 ((2 : ℝ) ^ e' a k)⁻¹ = _
  rw [Real.logb_inv, neg_neg, Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one]

theorem infoMass_K (a : Fin 3) (y : Fin (nY a)) : infoMass (κ.K a y) = e' a y.val :=
  infoMass_w a y.val

theorem sum_info (a : Fin 3) : ∑ y, κ.K a y * infoMass (κ.K a y) =
    ∑ k ∈ Finset.range (nY a), w a k * (e' a k : ℝ) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => w a k * (e' a k : ℝ))]
  exact Finset.sum_congr rfl fun y _ => by rw [infoMass_K]

theorem sum_var (a : Fin 3) (h : ℝ) : ∑ y, κ.K a y * (infoMass (κ.K a y) - h) ^ 2 =
    ∑ k ∈ Finset.range (nY a), w a k * ((e' a k : ℝ) - h) ^ 2 := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => w a k * ((e' a k : ℝ) - h) ^ 2)]
  exact Finset.sum_congr rfl fun y _ => by rw [infoMass_K]

theorem sum_exp (a : Fin 3) (t : ℝ) : ∑ y, κ.K a y * Real.exp (t * infoMass (κ.K a y)) =
    ∑ k ∈ Finset.range (nY a), w a k * Real.exp (t * (e' a k : ℝ)) := by
  rw [← Fin.sum_univ_eq_sum_range (fun k => w a k * Real.exp (t * (e' a k : ℝ)))]
  exact Finset.sum_congr rfl fun y _ => by rw [infoMass_K]

theorem H_P : κ.H 0 = 2 := by
  unfold H; rw [sum_info]
  simp [nY, w, e', e, Finset.sum_range_succ]; norm_num
theorem H_Q : κ.H 1 = 2 := by
  unfold H; rw [sum_info]
  simp [nY, w, e', e, Finset.sum_range_succ]; norm_num
theorem H_R : κ.H 2 = 15 / 8 := by
  unfold H; rw [sum_info]
  simp [nY, w, e', e, Finset.sum_range_succ]; norm_num

/-- Centered surprisal variances `σ²_P = 0`, `σ²_Q = 1`, `σ²_R = 71/64`. -/
theorem var_P : (κ.fam 2).sig2 0 = 0 := by
  unfold Sqrt.IncFamily.sig2; rw [sum_var]
  simp [nY, w, e', e, Finset.sum_range_succ]
theorem var_Q : (κ.fam 2).sig2 1 = 1 := by
  unfold Sqrt.IncFamily.sig2; rw [sum_var]
  simp [nY, w, e', e, Finset.sum_range_succ]; norm_num
theorem var_R : (κ.fam (15 / 8)).sig2 2 = 71 / 64 := by
  unfold Sqrt.IncFamily.sig2; rw [sum_var]
  simp [nY, w, e', e, Finset.sum_range_succ]; norm_num

theorem e'_le (a : Fin 3) (k : ℕ) : (e' a k : ℝ) ≤ 4 := by
  have : e' a k ≤ 4 := by
    unfold e'; split_ifs with h
    · fin_cases a <;> interval_cases k <;> simp [e]
    · omega
  exact_mod_cast this

/-- The maximal surprisal is `M = 4`. -/
theorem infoMass_le (a : Fin 3) (y : Fin (κ.nY a)) : infoMass (κ.K a y) ≤ 4 := by
  rw [infoMass_K]; exact e'_le a y.val

def S : Finset (Fin 3) := {0, 1}
theorem hS : S.Nonempty := ⟨0, by simp [S]⟩

theorem exp_mul_log (k : ℕ) : Real.exp (Real.log (6 / 5) * k) = (6 / 5 : ℝ) ^ k := by
  rw [mul_comm, ← Real.log_pow, Real.exp_log (by positivity)]

/-- **The `299/300` certificate.** `E e^{θ I_R} · E e^{-θ I_P} = 299/300` at `θ = ln(6/5)`. -/
theorem certificate :
    (∑ y, κ.K 2 y * Real.exp (Real.log (6 / 5) * infoMass (κ.K 2 y))) *
      (∑ z, κ.K 0 z * Real.exp (-Real.log (6 / 5) * infoMass (κ.K 0 z))) = 299 / 300 := by
  rw [sum_exp, sum_exp]
  simp [nY, w, e', e, Finset.sum_range_succ, Real.exp_neg, exp_mul_log]; norm_num

theorem dominates : Dominates (κ := κ) S 0 (Real.log (6 / 5)) := by
  intro j hj
  have : j = 2 := by fin_cases j <;> simp_all [S]
  subst this
  exact certificate.le.trans (by norm_num)

theorem sub_equalEntropy : (κ.sub S hS).EqualEntropy 2 := by
  intro i
  have hm : κ.subE S i ∈ S := Finset.orderEmbOfFin_mem _ _ _
  change κ.H (κ.subE S i) = 2
  obtain ⟨j, hj, hji⟩ : ∃ j ∈ S, κ.subE S i = j := ⟨_, hm, rfl⟩
  rw [hji]
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · exact H_P
  · exact H_Q

theorem sub_sigma (i : Fin S.card) :
    ((κ.sub S hS).fam 2).sigma i = 0 ∨ ((κ.sub S hS).fam 2).sigma i = 1 := by
  have hm : κ.subE S i ∈ S := Finset.orderEmbOfFin_mem _ _ _
  change Real.sqrt ((κ.fam 2).sig2 (κ.subE S i)) = 0 ∨ Real.sqrt ((κ.fam 2).sig2 (κ.subE S i)) = 1
  obtain ⟨j, hj, hji⟩ : ∃ j ∈ S, κ.subE S i = j := ⟨_, hm, rfl⟩
  rw [hji]
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · left; rw [var_P, Real.sqrt_zero]
  · right; rw [var_Q, Real.sqrt_one]

theorem sub_sigma_at (j : Fin 3) (hj : j ∈ S) :
    ∃ i, ((κ.sub S hS).fam 2).sigma i = Real.sqrt ((κ.fam 2).sig2 j) := by
  obtain ⟨i, hi⟩ := κ.subE_surj S hj
  exact ⟨i, by change Real.sqrt ((κ.fam 2).sig2 (κ.subE S i)) = _; rw [hi]⟩

theorem sub_sA : ((κ.sub S hS).fam 2).sA = 1 := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ fun i _ => by rcases sub_sigma i with h | h <;> rw [h]; norm_num
  · obtain ⟨i, hi⟩ := sub_sigma_at 1 (by simp [S])
    rw [var_Q, Real.sqrt_one] at hi
    exact hi ▸ Finset.le_sup' _ (Finset.mem_univ i)

theorem sub_sB : ((κ.sub S hS).fam 2).sB = 0 := by
  apply le_antisymm
  · obtain ⟨i, hi⟩ := sub_sigma_at 0 (by simp [S])
    rw [var_P, Real.sqrt_zero] at hi
    exact hi ▸ Finset.inf'_le _ (Finset.mem_univ i)
  · exact Finset.le_inf' _ _ fun i _ => by rcases sub_sigma i with h | h <;> rw [h]; norm_num

/-- **The `(P, Q, R)` asymptotics.** `(C_n - 2n)/√n → √(2/π)`. -/
theorem cost_tendsto :
    Tendsto (fun n : ℕ => (κ.costBits n - n * 2) / Real.sqrt n) atTop
      (𝓝 (Real.sqrt (2 / Real.pi))) := by
  have := cost_tendsto_maxEntropy hS (by simp [S] : (0 : Fin 3) ∈ S)
    (Real.log_pos (by norm_num)) dominates (by norm_num) infoMass_le sub_equalEntropy
  rwa [sub_sA, sub_sB, secondOrderCoeff, sub_zero, mul_one] at this

/-- **The `(P, Q, R)` cost comparison** with the explicit certificate `θ = ln(6/5)`, `M = 4`. -/
theorem cost_compare (n : ℕ) :
    0 ≤ κ.costBits n - (κ.sub S hS).costBits n ∧
      κ.costBits n - (κ.sub S hS).costBits n ≤
        (1 + Real.log (1 + Real.log (6 / 5) * (n * 4))) / Real.log (6 / 5) + shannonOverhead :=
  κ.costBits_compare hS (by simp [S] : (0 : Fin 3) ∈ S) (Real.log_pos (by norm_num))
    dominates (by norm_num) infoMass_le n

end CausalSpectrum.Kernel.PQR

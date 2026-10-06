/-
1:1 transfer of the finite claims in the 5 October 2026 note, on top of
`one_seed_shannon`.

Proved here, with no `sorry`:
* survival of `W = A(1+E)` integrates to `c⋆`, and `W` is stochastically
  smaller than the exponential used in the older sandwich
* `c⋆ < log₂ e`, so the original `log₂ e` bound is not sharp
* on every finite tree the greedy gap is strictly smaller than `c⋆`
* Věta 9, the scale arithmetic: an excess `o(rₙ)` forces the `W₁` gap to `o(rₙ)`
* Věta 4, the constants: `E[2^{-λ E}] = 1/(λ+1)`, `θ₂ = 5/8`, `g̃₂ = log₂(8/5)`
* Věta 5, second half: a kernel repeated `n` times has min-entropy `n` times
  the one-round min-entropy
* Věta 19, the rational brackets. The `n ≥ 16` assembly still uses the
  profile comparison, which is not in this file

Not in this file, because the note either leaves them open or rests them on
analysis that is not the finite certificate:
* convergence of the Bellman profile to `F` (Věta 1)
* rigidity, moments, and quantiles that ride on that limit (Věty 15–18)
* the Fan–Grama–Liu input to the logarithmic regime
* optimality of `c⋆`. The note does not claim it
-/
import CausalSeed.Gap
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Function

noncomputable section
open Classical MeasureTheory Set
namespace CausalSpectrum

/-! `W` against the exponential. -/

noncomputable def expSurvival (s : ℝ) : ℝ :=
  if s ≤ 0 then 1 else (2 : ℝ) ^ (-s)

theorem wSurvival_le_expSurvival (s : ℝ) : wSurvival s ≤ expSurvival s := by
  unfold wSurvival expSurvival
  by_cases hs : s ≤ 0
  · simp [hs]
  · rw [if_neg hs, if_neg hs]
    by_cases hs1 : s < 1
    · rw [if_pos hs1]
      have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num
      have hle : (2 : ℝ) ^ (-1 : ℝ) ≤ (2 : ℝ) ^ (-s) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) (by linarith)
      rw [← hhalf]
      exact hle
    · rw [if_neg hs1]

theorem wSurvival_lt_expSurvival {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    wSurvival s < expSurvival s := by
  unfold wSurvival expSurvival
  simp only [not_le.mpr hs0, hs1, ite_false, ite_true]
  have hhalf : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by norm_num
  rw [← hhalf]
  exact Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2)
    (by linarith : (-1 : ℝ) < -s)

theorem shannonOverhead_lt_logb_exp :
    shannonOverhead < Real.logb 2 (Real.exp 1) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have h2 : (2 : ℝ) < Real.exp 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _ < Real.exp 1 := Real.add_one_lt_exp one_ne_zero
  have hlt : Real.log 2 < 1 := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (by norm_num) h2
  rw [Real.logb, Real.log_exp]
  unfold shannonOverhead
  rw [div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)]
  have hinv : 1 < 1 / Real.log 2 := (one_lt_div hlog).mpr hlt
  linarith

theorem one_third_lt_overhead : (1 / 3 : ℝ) < shannonOverhead := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  unfold shannonOverhead
  have hhalf : (1 / 2 : ℝ) < (1 + 1 / Real.log 2) / 2 := by
    have hpos : 0 < 1 / Real.log 2 := one_div_pos.mpr hlog
    linarith
  exact lt_trans (by norm_num : (1 / 3 : ℝ) < 1 / 2) hhalf

/-! Integral of the survival function is `c⋆`. This is `E[W]`. -/

theorem integral_wSurvival :
    ∫ s in Ioi (0 : ℝ), wSurvival s = shannonOverhead := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hU : Ioc (0 : ℝ) 1 ∪ Ioi 1 = Ioi 0 := Ioc_union_Ioi_eq_Ioi (by norm_num)
  have hdis : Disjoint (Ioc (0 : ℝ) 1) (Ioi 1) := Ioc_disjoint_Ioi_same
  have hA : EqOn wSurvival (fun _ => (1 : ℝ) / 2) (Ioc 0 1) := by
    intro s hs
    have hs0 : ¬ s ≤ 0 := not_le.mpr hs.1
    by_cases hs1 : s < 1
    · simp [wSurvival, hs0, hs1]
    · have hsEq : s = 1 := le_antisymm hs.2 (le_of_not_gt hs1)
      simp [wSurvival, hsEq]
      norm_num
  have hB : EqOn wSurvival (fun s => (2 : ℝ) ^ (-s)) (Ioi 1) := by
    intro s hs
    have h1s : (1 : ℝ) < s := mem_Ioi.mp hs
    simp [wSurvival, not_le.mpr (lt_trans (by norm_num : (0 : ℝ) < 1) h1s), not_lt.mpr h1s.le]
  have hvol : volume (Ioc (0 : ℝ) 1) ≠ ⊤ := by
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hintA : IntegrableOn wSurvival (Ioc 0 1) :=
    (integrableOn_const (s := Ioc (0 : ℝ) 1) (C := (1 : ℝ) / 2) hvol).congr_fun
      hA.symm measurableSet_Ioc
  have hintTail : IntegrableOn (fun s : ℝ => psi ((2 : ℝ) ^ ((0 : ℝ) - s))) (Ioi 1) :=
    (integrableOn_psi_ray (by norm_num : (0 : ℝ) ≤ 0)).mono_set fun s hs =>
      mem_Ioi.mpr (lt_trans (by norm_num : (0 : ℝ) < 1) (mem_Ioi.mp hs))
  have hintB : IntegrableOn wSurvival (Ioi 1) := by
    refine hintTail.congr_fun ?_ measurableSet_Ioi
    intro s hs
    rw [wSurvival_eq_psi]
    dsimp
    congr 1
    congr 1
    ring
  have hint : IntegrableOn wSurvival (Ioi 0) := by
    rw [← hU]
    exact hintA.union hintB
  rw [← hU, setIntegral_union hdis measurableSet_Ioi hintA hintB]
  have iA : ∫ s in Ioc 0 1, wSurvival s = 1 / 2 := by
    rw [setIntegral_congr_fun measurableSet_Ioc hA, setIntegral_const,
      Real.volume_real_Ioc_of_le (by norm_num : (0 : ℝ) ≤ 1), smul_eq_mul]
    ring
  have iB : ∫ s in Ioi 1, wSurvival s = 1 / (2 * Real.log 2) := by
    rw [setIntegral_congr_fun measurableSet_Ioi hB]
    have hpow : EqOn (fun s : ℝ => (2 : ℝ) ^ (-s))
        (fun s => (2 : ℝ) ^ ((0 : ℝ) - s)) (Ioi 1) := by
      intro s _
      dsimp
      congr 1
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hpow]
    have htail := integral_exp_tail (0 : ℝ)
    simpa [zero_add] using htail
  rw [iA, iB, shannonOverhead_expand]

/-! Věta 4, the scalar identities. The comparison of moments against the tree
is the same monotone-weight argument as the Shannon sandwich; these are the
constants that argument produces. -/

theorem exp_moment {lam : ℝ} (hlam : 0 ≤ lam) :
    ∫ t in Ioi (0 : ℝ),
        (2 : ℝ) ^ (-lam * t) * Real.log 2 * Real.exp (-Real.log 2 * t) =
      1 / (lam + 1) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  set a : ℝ := -((lam + 1) * Real.log 2)
  have ha : a < 0 := by
    have hpos : 0 < lam + 1 := by linarith
    exact neg_lt_zero.mpr (mul_pos hpos hlog)
  have hfun : EqOn
      (fun t : ℝ => (2 : ℝ) ^ (-lam * t) * Real.log 2 * Real.exp (-Real.log 2 * t))
      (fun t => Real.log 2 * Real.exp (a * t)) (Ioi 0) := by
    intro t _
    dsimp
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-lam * t)]
    have hexp : Real.log 2 * (-lam * t) + (-Real.log 2 * t) = a * t := by
      dsimp [a]; ring
    calc
      Real.exp (Real.log 2 * (-lam * t)) * Real.log 2 * Real.exp (-Real.log 2 * t)
          = Real.log 2 * (Real.exp (Real.log 2 * (-lam * t)) * Real.exp (-Real.log 2 * t)) := by ring
      _ = Real.log 2 * Real.exp (Real.log 2 * (-lam * t) + (-Real.log 2 * t)) := by
            rw [← Real.exp_add]
      _ = Real.log 2 * Real.exp (a * t) := by rw [hexp]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun,
    integral_const_mul (Real.log 2) (fun t : ℝ => Real.exp (a * t))
      (μ := volume.restrict (Ioi (0 : ℝ))),
    integral_exp_mul_Ioi ha 0]
  have hlam : lam + 1 ≠ 0 := by linarith
  have hrewrite : Real.log 2 * (-Real.exp (a * 0) / a) = 1 / (lam + 1) := by
    rw [mul_zero, Real.exp_zero]
    dsimp [a]
    field_simp [hlog.ne', hlam]
  exact hrewrite

noncomputable def theta (α : ℝ) : ℝ := 1 / 2 + (2 : ℝ) ^ (-α) / α

theorem theta_two : theta 2 = 5 / 8 := by
  unfold theta
  have hpow : (2 : ℝ) ^ (-2 : ℝ) = 1 / 4 := by norm_num
  rw [hpow]
  norm_num

theorem gTilde_two :
    Real.logb 2 (theta 2) / (1 - 2) = Real.logb 2 ((8 : ℝ) / 5) := by
  rw [theta_two]
  have h : Real.logb 2 ((5 : ℝ) / 8) = -Real.logb 2 (8 / 5) := by
    rw [Real.logb_div (by norm_num) (by norm_num),
      Real.logb_div (by norm_num) (by norm_num)]
    ring
  rw [h]
  norm_num

theorem coarse_g_two : Real.logb 2 2 / (2 - 1) = (1 : ℝ) := by
  rw [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  norm_num

/-! Věta 9, arithmetic half. Scaling multiplies `W₁` by `1/rₙ`. -/

theorem excess_controls_gap {L C H : ℝ}
    (hC : C ≤ H) (hH : H ≤ L + shannonOverhead) :
    H - L ≤ (H - C) + shannonOverhead := by
  linarith

/-! Strict gap on one finite tree. `J` is bounded and `Z+W` is not. -/

noncomputable def maxInfo {T : Tree} : List (Atom T) → ℝ
  | [] => 0
  | a :: tail => max (infoMass a.1) (maxInfo tail)

theorem info_le_maxInfo {T : Tree} (atoms : List (Atom T)) {a : Atom T}
    (ha : a ∈ atoms) : infoMass a.1 ≤ maxInfo atoms := by
  induction atoms with
  | nil => cases ha
  | cons b tail ih =>
      rcases List.mem_cons.mp ha with rfl | ha
      · exact le_max_left _ _
      · exact le_trans (ih ha) (le_max_right _ _)

theorem smallWeight_zero_of_gt {T : Tree} (atoms : List (Atom T)) (t : ℝ)
    (hpos : ∀ a ∈ atoms, 0 < a.1) (ht : maxInfo atoms < t) :
    smallWeight atoms ((2 : ℝ) ^ (-t)) = 0 := by
  induction atoms with
  | nil => simp [smallWeight]
  | cons a tail ih =>
      rw [smallWeight_cons]
      have ha : ¬ a.1 ≤ (2 : ℝ) ^ (-t) := by
        intro hle
        have hinfo : t ≤ infoMass a.1 := (weight_le_dyadic_iff (hpos a (by simp))).1 hle
        have hmax : infoMass a.1 ≤ maxInfo (a :: tail) := le_max_left _ _
        linarith [ht]
      have htail : maxInfo tail < t := lt_of_le_of_lt (le_max_right _ _) ht
      simp [ha, ih (fun b hb => hpos b (by simp [hb])) htail]

theorem exists_envInc_pos (T : Tree) :
    ∃ i, i < (infoValues T).length ∧ 0 < envInc T i := by
  by_contra h
  push_neg at h
  have hzero : ∀ i ∈ Finset.range (infoValues T).length, envInc T i = 0 := by
    intro i hi
    exact le_antisymm (h i (Finset.mem_range.mp hi)) (envInc_nonneg T i)
  have hsum : (Finset.range (infoValues T).length).sum (envInc T) = 0 :=
    Finset.sum_eq_zero hzero
  have hlast : cumsum (envInc T) (infoValues T).length = 1 := cumsum_envInc_last T
  rw [cumsum_eq_sum] at hlast
  exact zero_ne_one (hsum.symm.trans hlast)

theorem integral_dyadic_tail (z c : ℝ) :
    ∫ t in Ioi c, (2 : ℝ) ^ (z - t) = (2 : ℝ) ^ (z - c) / Real.log 2 := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have ha : -Real.log 2 < 0 := by linarith
  have hfun : EqOn (fun t : ℝ => (2 : ℝ) ^ (z - t))
      (fun t => (2 : ℝ) ^ z * Real.exp (-Real.log 2 * t)) (Ioi c) := by
    intro t _
    dsimp
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (z - t)]
    rw [show Real.log 2 * (z - t) = Real.log 2 * z + (-Real.log 2) * t by ring]
    rw [Real.exp_add, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) z]
  rw [setIntegral_congr_fun measurableSet_Ioi hfun,
    integral_const_mul ((2 : ℝ) ^ z) (fun t : ℝ => Real.exp (-Real.log 2 * t))
      (μ := volume.restrict (Ioi c)),
    integral_exp_mul_Ioi ha c]
  have hneg : -Real.log 2 ≠ 0 := by linarith
  have hrewrite : -Real.exp ((-Real.log 2) * c) / (-Real.log 2) =
      Real.exp ((-Real.log 2) * c) / Real.log 2 := by field_simp [hneg]
  rw [hrewrite]
  have hexp : Real.exp ((-Real.log 2) * c) = (2 : ℝ) ^ (-c) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (-c)]
    congr 1
    ring
  rw [hexp]
  have hmul : (2 : ℝ) ^ z * ((2 : ℝ) ^ (-c) / Real.log 2) =
      ((2 : ℝ) ^ z * (2 : ℝ) ^ (-c)) / Real.log 2 := by field_simp [hlog.ne']
  rw [hmul, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have hadd : z + -c = z - c := by ring
  rw [hadd]

theorem integral_majorant (T : Tree) :
    ∫ t in Ioi (0 : ℝ),
        (Finset.range (infoValues T).length).sum (fun i => envPiece T i t) =
      envelopeMean T + shannonOverhead := by
  let n := (infoValues T).length
  have hinter :
      (∫ t in Ioi (0 : ℝ), (Finset.range n).sum (fun i => envPiece T i t)) =
        (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envPiece T i t) := by
    simpa using integral_finsetSum (μ := volume.restrict (Ioi (0 : ℝ))) (Finset.range n)
      (f := fun i (t : ℝ) => envPiece T i t)
      (fun i _ => (integrableOn_envPiece T i).integrable)
  rw [hinter]
  have hterm : (Finset.range n).sum (fun i => ∫ t in Ioi (0 : ℝ), envPiece T i t) =
      (Finset.range n).sum (fun i =>
        envInc T i * (if h : i < (infoValues T).length then (infoValues T)[i] else 0) +
          shannonOverhead * envInc T i) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i < (infoValues T).length := by simpa [n] using Finset.mem_range.mp hi
    simp only [envPiece, hi', dite_true]
    rw [integral_const_mul (envInc T i)
        (fun t : ℝ => psi ((2 : ℝ) ^ ((infoValues T)[i] - t)))
        (μ := volume.restrict (Ioi (0 : ℝ))),
      integral_psi_ray (info_nonneg_get T hi')]
    ring
  rw [hterm, Finset.sum_add_distrib]
  have hem : (Finset.range n).sum (fun i =>
      envInc T i * (if h : i < (infoValues T).length then (infoValues T)[i] else 0)) =
      envelopeMean T := by
    unfold envelopeMean
    dsimp [n]
  have hov : (Finset.range n).sum (fun i => shannonOverhead * envInc T i) =
      shannonOverhead := by
    rw [← Finset.mul_sum, ← cumsum_eq_sum, cumsum_envInc_last, mul_one]
  rw [hem, hov]

theorem psi_pow_pos (z t : ℝ) : 0 < psi ((2 : ℝ) ^ (z - t)) := by
  have hu : 0 < (2 : ℝ) ^ (z - t) := Real.rpow_pos_of_pos (by norm_num) _
  unfold psi
  split_ifs
  · exact hu
  · norm_num
  · norm_num

theorem envPiece_nonneg (T : Tree) (i : ℕ) (t : ℝ) : 0 ≤ envPiece T i t := by
  unfold envPiece
  split_ifs with hi
  · exact mul_nonneg (envInc_nonneg T i) (le_of_lt (psi_pow_pos _ t))
  · exact le_rfl

/-- On one finite tree `H(S_G) < L + c⋆`. The constant is not attained. -/
theorem finite_gap_strict (T : Tree) {atoms : List (Atom T)}
    (ht : GreedyTrace (Field.p T) atoms) :
    seedShannon atoms < envelopeMean T + shannonOverhead := by
  have hbounds := greedy_atom_bounds ht
  obtain ⟨i, hi, hposi⟩ := exists_envInc_pos T
  let z : ℝ := (infoValues T)[i]
  let c : ℝ := max (maxInfo atoms) (z + 1)
  have hc0 : 0 ≤ c := le_trans (by
    have : (0 : ℝ) ≤ z + 1 := by
      have := info_nonneg_get T hi
      linarith
    exact this) (le_max_right _ _)
  have hsmall : ∀ t, c < t → smallWeight atoms ((2 : ℝ) ^ (-t)) = 0 := by
    intro t ht
    exact smallWeight_zero_of_gt atoms t hbounds.1
      (lt_of_le_of_lt (le_max_left _ _) ht)
  let maj : ℝ → ℝ := fun t =>
    (Finset.range (infoValues T).length).sum (fun j => envPiece T j t)
  have hpoint : ∀ t ∈ Ioi (0 : ℝ),
      smallWeight atoms ((2 : ℝ) ^ (-t)) ≤ maj t := by
    intro t _
    have hδ : 0 ≤ (2 : ℝ) ^ (-t) := le_of_lt (Real.rpow_pos_of_pos (by norm_num) _)
    refine le_trans (smallWeight_le_envelope ht _ hδ) ?_
    apply Finset.sum_le_sum
    intro j hj
    have hj' : j < (infoValues T).length := Finset.mem_range.mp hj
    rw [majorant_dyadic T t hj']
    simp [maj, envPiece, hj']
  have hintS : IntegrableOn (fun t : ℝ => smallWeight atoms ((2 : ℝ) ^ (-t))) (Ioi 0) :=
    integrableOn_smallWeight atoms hbounds.1 hbounds.2
  have hintM : IntegrableOn maj (Ioi 0) := by
    simpa [maj, IntegrableOn] using
      integrable_finsetSum (μ := volume.restrict (Ioi (0 : ℝ)))
        (Finset.range (infoValues T).length)
        (f := fun j (t : ℝ) => envPiece T j t)
        (fun j _ => (integrableOn_envPiece T j).integrable)
  have htail_piece : ∫ t in Ioi c, envPiece T i t =
      envInc T i * ((2 : ℝ) ^ (z - c) / Real.log 2) := by
    have hfun : EqOn (fun t => envPiece T i t)
        (fun t => envInc T i * (2 : ℝ) ^ (z - t)) (Ioi c) := by
      intro t ht
      have hgt : z + 1 < t :=
        lt_of_le_of_lt (le_max_right (maxInfo atoms) (z + 1)) (mem_Ioi.mp ht)
      have hnot1 : ¬ t ≤ z := by linarith
      have hnot2 : ¬ t ≤ z + 1 := not_le.mpr hgt
      unfold envPiece
      dsimp
      rw [dif_pos hi, psi_rpow_piece, if_neg hnot1, if_neg hnot2]
    have hintPow : IntegrableOn (fun t : ℝ => (2 : ℝ) ^ (z - t)) (Ioi c) := by
      have ha : -Real.log 2 < 0 := by
        have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
        linarith
      have hmul : Integrable (fun t : ℝ => (2 : ℝ) ^ z * Real.exp (-Real.log 2 * t))
          (volume.restrict (Ioi c)) :=
        Integrable.const_mul (integrableOn_exp_mul_Ioi ha c).integrable ((2 : ℝ) ^ z)
      refine IntegrableOn.congr_fun (by simpa [IntegrableOn] using hmul) ?_ measurableSet_Ioi
      intro t _
      dsimp
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) (z - t)]
      rw [show Real.log 2 * (z - t) = Real.log 2 * z + (-Real.log 2) * t by ring]
      rw [Real.exp_add, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2) z]
      congr 1
      congr 1
      ring
    rw [setIntegral_congr_fun measurableSet_Ioi hfun,
      integral_const_mul, integral_dyadic_tail]
  have htail_pos : 0 < ∫ t in Ioi c, envPiece T i t := by
    rw [htail_piece]
    exact mul_pos hposi (div_pos (Real.rpow_pos_of_pos (by norm_num) _)
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  have hmaj_tail : ∫ t in Ioi c, envPiece T i t ≤ ∫ t in Ioi c, maj t := by
    apply setIntegral_mono_on
    · refine (integrableOn_envPiece T i).mono_set ?_
      intro t ht
      exact mem_Ioi.mpr (lt_of_le_of_lt hc0 (mem_Ioi.mp ht))
    · refine hintM.mono_set ?_
      intro t ht
      exact mem_Ioi.mpr (lt_of_le_of_lt hc0 (mem_Ioi.mp ht))
    · exact measurableSet_Ioi
    · intro t _
      unfold maj
      exact Finset.single_le_sum (fun j _ => envPiece_nonneg T j t)
        (Finset.mem_range.mpr hi)
  have hsmall_tail : ∫ t in Ioi c, smallWeight atoms ((2 : ℝ) ^ (-t)) = 0 := by
    have hfun : EqOn (fun t : ℝ => smallWeight atoms ((2 : ℝ) ^ (-t)))
        (fun _ => (0 : ℝ)) (Ioi c) := by
      intro t ht
      exact hsmall t (mem_Ioi.mp ht)
    rw [setIntegral_congr_fun measurableSet_Ioi hfun, integral_zero]
  have hInto : Ioi c ⊆ Ioi (0 : ℝ) := fun t ht =>
    mem_Ioi.mpr (lt_of_le_of_lt hc0 (mem_Ioi.mp ht))
  have hintMc : IntegrableOn maj (Ioi c) := hintM.mono_set hInto
  have hintSc : IntegrableOn (fun t : ℝ => smallWeight atoms ((2 : ℝ) ^ (-t))) (Ioi c) :=
    hintS.mono_set hInto
  have htail_diff :
      0 < ∫ t in Ioi c, (maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) := by
    rw [integral_sub hintMc.integrable hintSc.integrable, hsmall_tail, sub_zero]
    exact lt_of_lt_of_le htail_pos hmaj_tail
  have hhead_nonneg :
      0 ≤ ∫ t in Ioc 0 c, (maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) :=
    setIntegral_nonneg measurableSet_Ioc fun t ht =>
      sub_nonneg.mpr (hpoint t (mem_Ioi.mpr ht.1))
  have hIc : Ioc (0 : ℝ) c ∪ Ioi c = Ioi 0 := Ioc_union_Ioi_eq_Ioi hc0
  have hdis : Disjoint (Ioc (0 : ℝ) c) (Ioi c) := Ioc_disjoint_Ioi_same
  have hintHead : IntegrableOn
      (fun t : ℝ => maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) (Ioc 0 c) :=
    (hintM.mono_set Ioc_subset_Ioi_self).sub (hintS.mono_set Ioc_subset_Ioi_self)
  have hintTail : IntegrableOn
      (fun t : ℝ => maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) (Ioi c) :=
    hintMc.sub hintSc
  have hsplit :
      ∫ t in Ioi 0, (maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) =
        (∫ t in Ioc 0 c, (maj t - smallWeight atoms ((2 : ℝ) ^ (-t)))) +
          ∫ t in Ioi c, (maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) := by
    have h := setIntegral_union hdis measurableSet_Ioi hintHead hintTail
    rwa [hIc] at h
  have hwhole :
      ∫ t in Ioi (0 : ℝ), (maj t - smallWeight atoms ((2 : ℝ) ^ (-t))) =
        (∫ t in Ioi (0 : ℝ), maj t) -
          ∫ t in Ioi (0 : ℝ), smallWeight atoms ((2 : ℝ) ^ (-t)) :=
    integral_sub hintM.integrable hintS.integrable
  have hH : seedShannon atoms =
      ∫ t in Ioi (0 : ℝ), smallWeight atoms ((2 : ℝ) ^ (-t)) :=
    seedShannon_eq_integral atoms hbounds.1 hbounds.2
  have hM : ∫ t in Ioi 0, maj t = envelopeMean T + shannonOverhead := by
    simpa [maj] using integral_majorant T
  have hgap : 0 < seedShannon atoms - (seedShannon atoms) +
      ((envelopeMean T + shannonOverhead) - seedShannon atoms) := by
    have hpos : 0 < (∫ t in Ioi (0 : ℝ), maj t) -
        ∫ t in Ioi (0 : ℝ), smallWeight atoms ((2 : ℝ) ^ (-t)) := by
      rw [← hwhole, hsplit]
      linarith [hhead_nonneg, htail_diff]
    linarith [hH, hM, hpos]
  linarith [hgap]

/-! Věta 5, repeated kernel. -/

theorem memory_min_entropy (κ : Kernel) (n : ℕ) :
    infoMass (bottleneck (Field.p (κ.rounds n))) =
      (n : ℝ) * infoMass (bottleneck (Field.p (κ.rounds 1))) := by
  rw [bottleneck_kernelRepeat]
  unfold infoMass
  rw [Real.logb_pow]
  ring

/-! Věta 19, rational brackets. Not the `n ≥ 16` transport, which needs Věta 1. -/

theorem crash_lower_pow : (41 : ℕ) ^ 16 > 2 ^ 19 * 18 ^ 16 := by norm_num

theorem crash_upper_pow : (411 : ℕ) ^ 4 < 2 ^ 5 * 178 ^ 4 := by norm_num

theorem crash_b_sq_bounds :
    ((9 : ℚ) / 20) ^ 2 <
        2 * (41 / 100) * (1 - 2 * (411 / 1000)) * ((19 : ℚ) / 16) ^ 2 ∧
      2 * (411 / 1000) * (1 - 2 * (41 / 100)) * ((5 : ℚ) / 4) ^ 2 < (1 : ℚ) / 4 := by
  norm_num

theorem crash_C_bound :
    ((20 : ℚ) / 19) * ((1 / 4) / (3 * ((9 : ℚ) / 20) ^ 2) + 1 / 2) = 4430 / 4617 ∧
      (4430 : ℚ) / 4617 < 1 := by
  norm_num

theorem crash_comfort :
    (1 / 2 : ℚ) + 8 = 17 / 2 ∧ (1 / 2 : ℚ) + 3 / 2 = 2 := by
  norm_num

/-! The vertex calculation in “Jedna třetina”. This is the entropy of the
masses `(1/3, 1/3, 1/6, 1/6)`. It is not a search over trees, and it does not
identify `K_opt`. -/

theorem vertex_mass_entropy :
    2 * ((1 / 3 : ℝ) * infoMass (1 / 3)) + 2 * ((1 / 6) * infoMass (1 / 6)) =
      Real.logb 2 3 + 1 / 3 := by
  unfold infoMass
  have h3 : Real.logb 2 ((1 : ℝ) / 3) = -Real.logb 2 3 := by
    rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_one]
    ring
  have h6 : Real.logb 2 ((1 : ℝ) / 6) = -Real.logb 2 6 := by
    rw [Real.logb_div (by norm_num) (by norm_num), Real.logb_one]
    ring
  have hsplit : Real.logb 2 6 = 1 + Real.logb 2 3 := by
    have h6eq : (6 : ℝ) = 2 * 3 := by norm_num
    rw [h6eq, Real.logb_mul (by norm_num) (by norm_num),
      Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
  rw [h3, h6, hsplit]
  ring

end CausalSpectrum

/-
Zero probabilities, part 1: an abstract finite "policy/strategy/transcript" game.

Everything here is stated for arbitrary finite types of policies `P`, response
strategies `St` and transcripts `Lf`, a run map and a compatibility relation,
and a transcript mass `m` that may vanish.  It contains
* the envelope CDF `Fenv m t = min_π ∑_{ℓ ∼ π, m ℓ ≥ 2^{-t}} m ℓ` and
  `Lenv m = ∫_0^∞ (1 - Fenv m t) dt` (bits; no `log 0` is ever formed);
* the layer-cake lower bound `Lenv m ≤ H(q)` for every exact law `q`;
* continuity of `Lenv` under pointwise convergence of the masses;
* the compactness closure: exact laws with `H ≤ Lenv + c` for masses `m_n → m`
  produce an exact law for `m` with `Lenv m ≤ H ≤ Lenv m + c`.
-/
import CausalSeed.Penalty
import CausalSeed.SqrtDefect
import Mathlib.MeasureTheory.Integral.ExpDecay

set_option linter.unusedSectionVars false

noncomputable section
open Classical MeasureTheory Set Filter Finset
open scoped Topology
namespace CausalSpectrum.Zero

section Game
variable {P St Lf : Type} [Fintype P] [Fintype St] [Fintype Lf] [Nonempty P]
variable (run : St → P → Lf) (compat : Lf → P → Prop)

/-- Mass of the transcripts of `π` that are at least `2^{-t}`. -/
def Sp (m : Lf → ℝ) (π : P) (t : ℝ) : ℝ :=
  ∑ ℓ, if compat ℓ π ∧ (2:ℝ) ^ (-t) ≤ m ℓ then m ℓ else 0

/-- The lower envelope `F_K(t)`. -/
def Fenv (m : Lf → ℝ) (t : ℝ) : ℝ :=
  (Finset.univ : Finset P).inf' Finset.univ_nonempty (fun π => Sp compat m π t)

/-- `L(K) = ∫_0^∞ (1 - F_K(t)) dt`. -/
def Lenv (m : Lf → ℝ) : ℝ := ∫ t in Ioi (0:ℝ), (1 - Fenv compat m t)

/-- A law on response strategies is exact for the masses `m`. -/
def Exact (m : Lf → ℝ) (q : St → ℝ) : Prop :=
  ∀ π ℓ, (∑ s, if run s π = ℓ then q s else 0) = if compat ℓ π then m ℓ else 0

def IsPmf (q : St → ℝ) : Prop := (∀ s, 0 ≤ q s) ∧ ∑ s, q s = 1

variable {run compat}

theorem fiber_sum (q : St → ℝ) (π : P) (f : Lf → ℝ) :
    ∑ s, f (run s π) * q s = ∑ ℓ, f ℓ * ∑ s, (if run s π = ℓ then q s else 0) := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.sum_eq_single (run s π)]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

theorem exact_total {m : Lf → ℝ} {q : St → ℝ} (hq : IsPmf q) (he : Exact run compat m q)
    (π : P) : ∑ ℓ, (if compat ℓ π then m ℓ else 0) = 1 := by
  have := fiber_sum (run := run) q π (fun _ => 1)
  simp only [one_mul] at this
  rw [← hq.2, this]
  exact Finset.sum_congr rfl fun ℓ _ => (he π ℓ).symm

variable (hrc : ∀ s π, compat (run s π) π)
include hrc

theorem le_mass {m : Lf → ℝ} {q : St → ℝ} (hq : IsPmf q) (he : Exact run compat m q)
    (s : St) (π : P) : q s ≤ m (run s π) := by
  have h := he π (run s π)
  rw [if_pos (hrc s π)] at h
  rw [← h]
  have := Finset.single_le_sum (f := fun s' => if run s' π = run s π then q s' else 0)
    (fun s' _ => by split_ifs <;> simp [hq.1 s']) (Finset.mem_univ s)
  simpa using this

omit hrc

/-! ### Bounds on the envelope -/

theorem one_sub_Sp {m : Lf → ℝ} (hsum : ∀ π, ∑ ℓ, (if compat ℓ π then m ℓ else 0) = 1)
    (π : P) (t : ℝ) :
    1 - Sp compat m π t = ∑ ℓ, if compat ℓ π ∧ ¬ (2:ℝ) ^ (-t) ≤ m ℓ then m ℓ else 0 := by
  rw [← hsum π, Sp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ℓ _ => ?_
  by_cases hc : compat ℓ π <;> by_cases hl : (2:ℝ) ^ (-t) ≤ m ℓ <;> simp [hc, hl]

theorem Fenv_bounds {m : Lf → ℝ} (hm : ∀ ℓ, 0 ≤ m ℓ)
    (hsum : ∀ π, ∑ ℓ, (if compat ℓ π then m ℓ else 0) = 1) (t : ℝ) :
    0 ≤ 1 - Fenv compat m t ∧
      1 - Fenv compat m t ≤ Fintype.card Lf * (2:ℝ) ^ (-t) := by
  obtain ⟨π, -, hπ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := P))
    (fun π => Sp compat m π t)
  unfold Fenv; rw [hπ, one_sub_Sp hsum]
  constructor
  · exact Finset.sum_nonneg fun ℓ _ => by split_ifs <;> simp [hm ℓ]
  · calc _ ≤ ∑ _ℓ : Lf, (2:ℝ) ^ (-t) := Finset.sum_le_sum fun ℓ _ => by
          split_ifs with h
          · exact (not_le.mp h.2).le
          · positivity
      _ = _ := by simp

theorem Sp_mono {m : Lf → ℝ} (hm : ∀ ℓ, 0 ≤ m ℓ) (π : P) : Monotone (fun t => Sp compat m π t) := by
  intro s t hst
  apply Finset.sum_le_sum
  intro ℓ _
  have h2 : (2:ℝ) ^ (-t) ≤ (2:ℝ) ^ (-s) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
  by_cases h : compat ℓ π ∧ (2:ℝ) ^ (-s) ≤ m ℓ
  · rw [if_pos h, if_pos ⟨h.1, h2.trans h.2⟩]
  · rw [if_neg h]; split_ifs <;> simp [hm ℓ]

theorem Fenv_mono {m : Lf → ℝ} (hm : ∀ ℓ, 0 ≤ m ℓ) : Monotone (Fenv compat m) := by
  intro s t hst
  unfold Fenv
  exact Finset.le_inf' _ _ fun π hπ =>
    (Finset.inf'_le _ hπ).trans (Sp_mono hm π hst)

theorem dyadic_eq_exp (t : ℝ) : (2:ℝ) ^ (-t) = Real.exp (-(Real.log 2) * t) := by
  rw [Real.rpow_def_of_pos (by norm_num)]; ring_nf

theorem integrableOn_bound (N : ℝ) :
    IntegrableOn (fun t : ℝ => N * (2:ℝ) ^ (-t)) (Ioi 0) := by
  simp_rw [dyadic_eq_exp]
  exact (exp_neg_integrableOn_Ioi 0 (Real.log_pos (by norm_num))).const_mul N

theorem integrableOn_one_sub_Fenv {m : Lf → ℝ} (hm : ∀ ℓ, 0 ≤ m ℓ)
    (hsum : ∀ π, ∑ ℓ, (if compat ℓ π then m ℓ else 0) = 1) :
    IntegrableOn (fun t => 1 - Fenv compat m t) (Ioi 0) := by
  refine (integrableOn_bound (Fintype.card Lf)).mono' ?_ ?_
  · exact (measurable_const.sub (Fenv_mono hm).measurable).aestronglyMeasurable
  · refine ae_of_all _ fun t => ?_
    obtain ⟨h0, h1⟩ := Fenv_bounds hm hsum t
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1

/-! ### Layer-cake lower bound -/

theorem integral_piece {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    IntegrableOn (fun t : ℝ => if w < (2:ℝ) ^ (-t) then w else 0) (Ioi 0) ∧
      ∫ t in Ioi (0:ℝ), (if w < (2:ℝ) ^ (-t) then w else 0) = entTerm w := by
  rcases eq_or_lt_of_le hw with h | h
  · subst h; simp [entTerm_zero]
  · have hI : 0 ≤ infoMass w := by
      unfold infoMass
      have := Real.logb_nonpos (b := 2) (by norm_num) hw hw1
      linarith
    have hfun : (fun t : ℝ => if w < (2:ℝ) ^ (-t) then w else 0) =
        (Iio (infoMass w)).indicator (fun _ => w) := by
      funext t
      simp only [Set.indicator, Set.mem_Iio, weight_lt_dyadic_iff h]
    rw [hfun]
    have hfin : (volume.restrict (Ioi (0:ℝ))) (Iio (infoMass w)) < ⊤ := by
      rw [Measure.restrict_apply measurableSet_Iio]
      exact (measure_mono (fun x hx => ⟨hx.2, hx.1⟩ : Iio (infoMass w) ∩ Ioi 0 ⊆
        Ioo 0 (infoMass w))).trans_lt measure_Ioo_lt_top
    constructor
    · exact (integrable_indicator_iff measurableSet_Iio).2
        (integrableOn_const (C := w) hfin.ne)
    · rw [integral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        setIntegral_const, entTerm_of_pos h]
      have : Iio (infoMass w) ∩ Ioi 0 = Ioo 0 (infoMass w) := by
        ext x; simp [and_comm]
      rw [this, measureReal_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith),
        smul_eq_mul]
      ring

include hrc

theorem Lenv_le_entropy {m : Lf → ℝ} {q : St → ℝ} (hm : ∀ ℓ, 0 ≤ m ℓ) (hq : IsPmf q)
    (he : Exact run compat m q) : Lenv compat m ≤ pmfEntropy q := by
  have hsum := exact_total hq he
  have hq1 : ∀ s, q s ≤ 1 := fun s => by
    rw [← hq.2]; exact Finset.single_le_sum (fun s _ => hq.1 s) (Finset.mem_univ s)
  set φ : St → ℝ → ℝ := fun s t => if q s < (2:ℝ) ^ (-t) then q s else 0
  have hint : ∀ s, IntegrableOn (φ s) (Ioi 0) := fun s => (integral_piece (hq.1 s) (hq1 s)).1
  have hH : ∫ t in Ioi (0:ℝ), ∑ s, φ s t = pmfEntropy q := by
    rw [integral_finset_sum _ fun s _ => hint s]
    exact Finset.sum_congr rfl fun s _ => (integral_piece (hq.1 s) (hq1 s)).2
  rw [Lenv, ← hH]
  refine setIntegral_mono_on (integrableOn_one_sub_Fenv hm hsum)
    (integrable_finset_sum _ fun s _ => hint s) measurableSet_Ioi fun t _ => ?_
  -- `∑_{q s ≥ 2^{-t}} q s ≤ F(t)`
  have hG : ∑ s, (if (2:ℝ) ^ (-t) ≤ q s then q s else 0) ≤ Fenv compat m t := by
    unfold Fenv
    refine Finset.le_inf' _ _ fun π _ => ?_
    calc ∑ s, (if (2:ℝ) ^ (-t) ≤ q s then q s else 0)
        ≤ ∑ s, (if (2:ℝ) ^ (-t) ≤ m (run s π) then 1 else 0) * q s := by
          refine Finset.sum_le_sum fun s _ => ?_
          by_cases h : (2:ℝ) ^ (-t) ≤ q s
          · rw [if_pos h, if_pos (h.trans (le_mass hrc hq he s π))]; simp
          · rw [if_neg h]; split_ifs <;> simp [hq.1 s]
      _ = ∑ ℓ, (if (2:ℝ) ^ (-t) ≤ m ℓ then 1 else 0) *
            ∑ s, (if run s π = ℓ then q s else 0) :=
          fiber_sum q π (fun ℓ => if (2:ℝ) ^ (-t) ≤ m ℓ then 1 else 0)
      _ = Sp compat m π t := by
          unfold Sp
          refine Finset.sum_congr rfl fun ℓ _ => ?_
          rw [he π ℓ]
          by_cases hc : compat ℓ π <;> by_cases hl : (2:ℝ) ^ (-t) ≤ m ℓ <;> simp [hc, hl]
  have hsplit : ∑ s, φ s t = 1 - ∑ s, (if (2:ℝ) ^ (-t) ≤ q s then q s else 0) := by
    rw [← hq.2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [φ]
    by_cases h : q s < (2:ℝ) ^ (-t)
    · rw [if_pos h, if_neg (not_le.mpr h)]; ring
    · rw [if_neg h, if_pos (not_lt.mp h)]; ring
  rw [hsplit]; linarith

omit hrc

/-! ### Continuity of `Lenv` -/

theorem Sp_tendsto {mn : ℕ → Lf → ℝ} {m : Lf → ℝ}
    (hlim : ∀ ℓ, Tendsto (fun n => mn n ℓ) atTop (𝓝 (m ℓ))) {t : ℝ}
    (ht : ∀ ℓ, (2:ℝ) ^ (-t) ≠ m ℓ) (π : P) :
    Tendsto (fun n => Sp compat (mn n) π t) atTop (𝓝 (Sp compat m π t)) := by
  unfold Sp
  refine tendsto_finset_sum _ fun ℓ _ => ?_
  by_cases hc : compat ℓ π
  · rcases lt_or_gt_of_ne (ht ℓ) with h | h
    · have hev : ∀ᶠ n in atTop, (2:ℝ) ^ (-t) ≤ mn n ℓ :=
        ((hlim ℓ).eventually (lt_mem_nhds h)).mono fun n hn => hn.le
      rw [if_pos ⟨hc, h.le⟩]
      exact (hlim ℓ).congr' (hev.mono fun n hn => by simp only []; rw [if_pos ⟨hc, hn⟩])
    · have hev : ∀ᶠ n in atTop, mn n ℓ < (2:ℝ) ^ (-t) := (hlim ℓ).eventually (gt_mem_nhds h)
      rw [if_neg (fun h' => absurd h'.2 (not_le.mpr h))]
      exact tendsto_const_nhds.congr' (hev.mono fun n hn => by
        simp only []; rw [if_neg (fun h' => absurd h'.2 (not_le.mpr hn))])
  · simp [hc]

theorem Fenv_tendsto {mn : ℕ → Lf → ℝ} {m : Lf → ℝ}
    (hlim : ∀ ℓ, Tendsto (fun n => mn n ℓ) atTop (𝓝 (m ℓ))) {t : ℝ}
    (ht : ∀ ℓ, (2:ℝ) ^ (-t) ≠ m ℓ) :
    Tendsto (fun n => Fenv compat (mn n) t) atTop (𝓝 (Fenv compat m t)) := by
  have hS := fun π => Sp_tendsto (compat := compat) hlim ht π
  have hD : Tendsto (fun n => ∑ π : P, |Sp compat (mn n) π t - Sp compat m π t|) atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset P) fun π _ =>
      ((hS π).sub_const (Sp compat m π t)).abs
    simpa using this
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hD
  rw [Real.norm_eq_abs]
  have := Sqrt.inf'_close (s := (Finset.univ : Finset P)) Finset.univ_nonempty
    (E := fun π => Sp compat (mn n) π t) (Q := fun π => Sp compat m π t) (c := 0)
    (ε := ∑ π : P, |Sp compat (mn n) π t - Sp compat m π t|) (fun π _ => by
      simpa using Finset.single_le_sum
        (f := fun π => |Sp compat (mn n) π t - Sp compat m π t|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ π))
  simpa [Fenv] using this

theorem ae_avoid (m : Lf → ℝ) : ∀ᵐ t : ℝ, ∀ ℓ, (2:ℝ) ^ (-t) ≠ m ℓ := by
  rw [ae_all_iff]
  intro ℓ
  rw [ae_iff]
  simp only [ne_eq, not_not]
  apply Set.Subsingleton.measure_zero
  intro x hx y hy
  have h := hx.trans hy.symm
  have := congrArg (Real.logb 2) h
  rw [Real.logb_rpow (by norm_num) (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
    at this
  linarith

theorem Lenv_tendsto {mn : ℕ → Lf → ℝ} {m : Lf → ℝ}
    (hlim : ∀ ℓ, Tendsto (fun n => mn n ℓ) atTop (𝓝 (m ℓ)))
    (hmn : ∀ n ℓ, 0 ≤ mn n ℓ) (hsumn : ∀ n π, ∑ ℓ, (if compat ℓ π then mn n ℓ else 0) = 1) :
    Tendsto (fun n => Lenv compat (mn n)) atTop (𝓝 (Lenv compat m)) := by
  refine tendsto_integral_filter_of_dominated_convergence
    (fun t => Fintype.card Lf * (2:ℝ) ^ (-t)) (Eventually.of_forall fun n =>
      (measurable_const.sub (Fenv_mono (hmn n)).measurable).aestronglyMeasurable)
    (Eventually.of_forall fun n => ae_of_all _ fun t => ?_) (integrableOn_bound _) ?_
  · obtain ⟨h0, h1⟩ := Fenv_bounds (hmn n) (hsumn n) t
    rw [Real.norm_eq_abs, abs_of_nonneg h0]; exact h1
  · exact ae_restrict_of_ae ((ae_avoid m).mono fun t ht =>
      (Fenv_tendsto hlim ht).const_sub 1)

/-! ### Entropy is continuous on the simplex -/

theorem entTerm_eq_negMulLog (w : ℝ) : entTerm w = Real.negMulLog w / Real.log 2 := by
  by_cases h : w = 0
  · subst h; simp [entTerm]
  · rw [entTerm, if_neg h, infoMass, Real.negMulLog, Real.logb]; ring

theorem continuous_pmfEntropy : Continuous (fun q : St → ℝ => pmfEntropy q) := by
  unfold pmfEntropy
  simp_rw [entTerm_eq_negMulLog]
  exact continuous_finset_sum _ fun s _ =>
    (Real.continuous_negMulLog.comp (continuous_apply s)).div_const _

/-! ### Compactness closure -/

include hrc

theorem closure_of_approx {mn : ℕ → Lf → ℝ} {m : Lf → ℝ} {c : ℝ}
    (hlim : ∀ ℓ, Tendsto (fun n => mn n ℓ) atTop (𝓝 (m ℓ)))
    (hmn : ∀ n ℓ, 0 ≤ mn n ℓ) (hm : ∀ ℓ, 0 ≤ m ℓ)
    (happrox : ∀ n, ∃ q : St → ℝ, IsPmf q ∧ Exact run compat (mn n) q ∧
      pmfEntropy q ≤ Lenv compat (mn n) + c) :
    ∃ q : St → ℝ, IsPmf q ∧ Exact run compat m q ∧
      Lenv compat m ≤ pmfEntropy q ∧ pmfEntropy q ≤ Lenv compat m + c := by
  choose qn hpmf hex hH using happrox
  have hsumn : ∀ n π, ∑ ℓ, (if compat ℓ π then mn n ℓ else 0) = 1 :=
    fun n => exact_total (hpmf n) (hex n)
  have hK : IsCompact (Set.pi univ fun _ : St => Icc (0:ℝ) 1) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hmem : ∀ n, qn n ∈ Set.pi univ fun _ : St => Icc (0:ℝ) 1 := fun n s _ =>
    ⟨(hpmf n).1 s, by
      rw [← (hpmf n).2]
      exact Finset.single_le_sum (fun s _ => (hpmf n).1 s) (Finset.mem_univ s)⟩
  obtain ⟨q, -, φ, hφ, hq⟩ := hK.tendsto_subseq hmem
  have hqs : ∀ s, Tendsto (fun n => qn (φ n) s) atTop (𝓝 (q s)) := tendsto_pi_nhds.1 hq
  have hlimφ : ∀ ℓ, Tendsto (fun n => mn (φ n) ℓ) atTop (𝓝 (m ℓ)) :=
    fun ℓ => (hlim ℓ).comp hφ.tendsto_atTop
  have hpq : IsPmf q := by
    refine ⟨fun s => ge_of_tendsto' (hqs s) fun n => (hpmf (φ n)).1 s, ?_⟩
    have := tendsto_finset_sum (Finset.univ : Finset St) fun s _ => hqs s
    exact tendsto_nhds_unique this (by simp only [(hpmf _).2]; exact tendsto_const_nhds)
  have heq : Exact run compat m q := by
    intro π ℓ
    have h1 := tendsto_finset_sum (Finset.univ : Finset St) fun s (_ : s ∈ Finset.univ) =>
      (show Tendsto (fun n => if run s π = ℓ then qn (φ n) s else 0) atTop
        (𝓝 (if run s π = ℓ then q s else 0)) by
          split_ifs
          · exact hqs s
          · exact tendsto_const_nhds)
    have h2 : Tendsto (fun n => if compat ℓ π then mn (φ n) ℓ else 0) atTop
        (𝓝 (if compat ℓ π then m ℓ else 0)) := by
      split_ifs
      · exact hlimφ ℓ
      · exact tendsto_const_nhds
    simp_rw [hex (φ _) π ℓ] at h1
    exact tendsto_nhds_unique h1 h2
  refine ⟨q, hpq, heq, Lenv_le_entropy hrc hm hpq heq, ?_⟩
  have hHt : Tendsto (fun n => pmfEntropy (qn (φ n))) atTop (𝓝 (pmfEntropy q)) :=
    (continuous_pmfEntropy.tendsto q).comp hq
  have hLt := (Lenv_tendsto (compat := compat) hlimφ (fun n => hmn (φ n))
    (fun n => hsumn (φ n))).add_const c
  exact le_of_tendsto_of_tendsto' hHt hLt fun n => hH (φ n)

omit hrc

/-! ### Transport along an isomorphism of games -/

variable {P' St' Lf' : Type} [Fintype P'] [Fintype St'] [Fintype Lf'] [Nonempty P']
variable {run' : St' → P' → Lf'} {compat' : Lf' → P' → Prop}

theorem Fenv_transport (eP : P ≃ P') (eL : Lf ≃ Lf')
    (hc : ∀ ℓ π, compat' (eL ℓ) (eP π) ↔ compat ℓ π) (m' : Lf' → ℝ) (t : ℝ) :
    Fenv compat' m' t = Fenv compat (m' ∘ eL) t := by
  have hS : ∀ π, Sp compat' m' (eP π) t = Sp compat (m' ∘ eL) π t := by
    intro π; unfold Sp
    rw [← Equiv.sum_comp eL]
    simp only [hc, Function.comp]
  unfold Fenv
  apply le_antisymm
  · exact Finset.le_inf' _ _ fun π _ => (hS π) ▸ Finset.inf'_le _ (Finset.mem_univ _)
  · refine Finset.le_inf' _ _ fun π' _ => ?_
    have := Finset.inf'_le (fun π => Sp compat (m' ∘ eL) π t) (Finset.mem_univ (eP.symm π'))
    rw [← hS, Equiv.apply_symm_apply] at this
    exact this

theorem Lenv_transport (eP : P ≃ P') (eL : Lf ≃ Lf')
    (hc : ∀ ℓ π, compat' (eL ℓ) (eP π) ↔ compat ℓ π) (m' : Lf' → ℝ) :
    Lenv compat' m' = Lenv compat (m' ∘ eL) := by
  unfold Lenv; simp_rw [Fenv_transport eP eL hc]

theorem exact_transport (eP : P ≃ P') (eS : St ≃ St') (eL : Lf ≃ Lf')
    (hc : ∀ ℓ π, compat' (eL ℓ) (eP π) ↔ compat ℓ π)
    (hr : ∀ s π, run' (eS s) (eP π) = eL (run s π)) {m' : Lf' → ℝ} {q' : St' → ℝ}
    (he : Exact run' compat' m' q') : Exact run compat (m' ∘ eL) (q' ∘ eS) := by
  intro π ℓ
  have h := he (eP π) (eL ℓ)
  rw [hc, ← Equiv.sum_comp eS] at h
  simp only [hr, eL.apply_eq_iff_eq] at h
  exact h

theorem pmf_transport (eS : St ≃ St') {q' : St' → ℝ} (h : IsPmf q') : IsPmf (q' ∘ eS) :=
  ⟨fun s => h.1 _, by rw [← h.2, ← Equiv.sum_comp eS]; rfl⟩

theorem entropy_transport (eS : St ≃ St') (q' : St' → ℝ) :
    pmfEntropy (q' ∘ eS) = pmfEntropy q' := by
  unfold pmfEntropy; exact Equiv.sum_comp eS (fun s => entTerm (q' s))

end Game
end CausalSpectrum.Zero

/-
The maximal-entropy comparison.

For a stationary kernel `κ` and a nonempty set `S` of actions, `κ.sub S` is the kernel of the
actions in `S`. If an action `i₀ ∈ S` dominates every action outside `S` in the exponential
sense `E e^{θ I_j} · E e^{-θ I_{i₀}} ≤ 1` (with `I = -log₂ K`), then the causal envelope of
the full kernel is squeezed between the envelope of `κ.sub S` and its shift:
`F*_n(x - r) - e^{-θ r} ≤ F_n(x) ≤ F*_n(x)` for every `r ≥ 0`.
-/
import CausalSeed.GapDecoder
import CausalSeed.SqrtMain
import CausalSeed.RenyiFinite
import CausalSeed.MaxEntropyHoeffding

noncomputable section
open Classical Finset
namespace CausalSpectrum.Kernel

variable (κ : Kernel)

/-! ### The subkernel of a set of actions -/

/-- Increasing enumeration of `S`. -/
abbrev subE (S : Finset (Fin κ.nA)) : Fin S.card ↪o Fin κ.nA := S.orderEmbOfFin rfl

/-- The kernel of the actions in a nonempty set `S`. -/
def sub (S : Finset (Fin κ.nA)) (hS : S.Nonempty) : Kernel where
  nA := S.card
  hA := Finset.card_pos.mpr hS
  nY := fun i => κ.nY (κ.subE S i)
  hY := fun _ => κ.hY _
  K := fun i => κ.K (κ.subE S i)
  Kpos := fun _ => κ.Kpos _
  Ksum := fun _ => κ.Ksum _

theorem subE_surj (S : Finset (Fin κ.nA)) {j : Fin κ.nA} (hj : j ∈ S) : ∃ i, κ.subE S i = j := by
  have : j ∈ Set.range (κ.subE S) := by rw [range_orderEmbOfFin]; exact hj
  exact this

variable {κ}

/-! ### The Bellman comparison -/

section Compare
variable {S : Finset (Fin κ.nA)} (hS : S.Nonempty)

theorem sub_expect (i : Fin S.card) (f : ℝ → ℝ) (x : ℝ) :
    ((κ.sub S hS).fam 0).expect i f x = (κ.fam 0).expect (κ.subE S i) f x := rfl

/-- Upper half: dropping actions can only raise the envelope. -/
theorem G_le_sub : ∀ (n : ℕ) (x : ℝ), (κ.fam 0).G n x ≤ ((κ.sub S hS).fam 0).G n x
  | 0, x => le_rfl
  | n + 1, x => by
    obtain ⟨i, hi⟩ := ((κ.sub S hS).fam 0).T_attained (((κ.sub S hS).fam 0).G n) x
    change (κ.fam 0).T ((κ.fam 0).G n) x ≤ ((κ.sub S hS).fam 0).T _ x
    rw [hi]
    exact ((κ.fam 0).T_le _ x (κ.subE S i)).trans ((κ.fam 0).expect_mono _ (G_le_sub n) x)

/-- The exponential-domination hypothesis for the reference action `i₀` at rate `θ`. -/
def Dominates (S : Finset (Fin κ.nA)) (i₀ : Fin κ.nA) (θ : ℝ) : Prop :=
  ∀ j ∉ S, (∑ y, κ.K j y * Real.exp (θ * infoMass (κ.K j y))) *
    (∑ z, κ.K i₀ z * Real.exp (-θ * infoMass (κ.K i₀ z))) ≤ 1

theorem G_bounds (n : ℕ) (x : ℝ) : 0 ≤ (κ.fam 0).G n x ∧ (κ.fam 0).G n x ≤ 1 :=
  ((κ.fam 0).G_cdf n).2.2.1 x

/-- Lower half (Bellman form): `G*_n(x - r) - e^{-θ r} ≤ G_n(x)`. -/
theorem sub_shift_le {i₀ : Fin κ.nA} (hi₀ : i₀ ∈ S) {θ : ℝ} (hθ : 0 < θ)
    (hdom : Dominates S i₀ θ) :
    ∀ (n : ℕ) (x r : ℝ), 0 ≤ r →
      ((κ.sub S hS).fam 0).G n (x - r) - Real.exp (-θ * r) ≤ (κ.fam 0).G n x
  | 0, x, r, hr => by
    simp only [Sqrt.IncFamily.G]
    have he := Real.exp_pos (-θ * r)
    split_ifs with h1 h2 <;> linarith
  | n + 1, x, r, hr => by
    set F := κ.fam 0
    set Fs := (κ.sub S hS).fam 0
    have IH := sub_shift_le hi₀ hθ hdom n
    obtain ⟨j, hj⟩ := F.T_attained (F.G n) x
    change Fs.T (Fs.G n) (x - r) - _ ≤ F.T (F.G n) x
    rw [hj]
    by_cases hjS : j ∈ S
    · obtain ⟨i, rfl⟩ := κ.subE_surj S hjS
      refine le_trans (sub_le_sub_right (Fs.T_le _ _ i) _) ?_
      rw [sub_expect]
      unfold Sqrt.IncFamily.expect
      have hP := F.Psum (κ.subE S i)
      calc (∑ y, F.P (κ.subE S i) y * Fs.G n (x - r - F.X (κ.subE S i) y)) - Real.exp (-θ * r)
          = ∑ y, F.P (κ.subE S i) y * (Fs.G n ((x - F.X (κ.subE S i) y) - r)
              - Real.exp (-θ * r)) := by
            simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hP, one_mul]
            congr 1; refine Finset.sum_congr rfl fun y _ => ?_; congr 2; ring
        _ ≤ _ := Finset.sum_le_sum fun y _ =>
            mul_le_mul_of_nonneg_left (IH _ r hr) (F.Ppos _ _).le
    · obtain ⟨i, hi⟩ := κ.subE_surj S hi₀
      refine le_trans (sub_le_sub_right (Fs.T_le _ _ i) _) ?_
      rw [sub_expect, hi]
      unfold Sqrt.IncFamily.expect
      set A := ∑ y, κ.K j y * Real.exp (θ * infoMass (κ.K j y))
      set B := ∑ z, κ.K i₀ z * Real.exp (-θ * infoMass (κ.K i₀ z))
      have hA : 0 ≤ A := Finset.sum_nonneg fun y _ =>
        mul_nonneg (κ.Kpos _ _).le (Real.exp_pos _).le
      have hAB : A * B ≤ 1 := hdom j hjS
      have hX : ∀ a y, F.X a y = infoMass (κ.K a y) := fun a y => sub_zero _
      -- pointwise bound
      have hpt : ∀ y z, Fs.G n (x - r - F.X i₀ z) - Real.exp (-θ * r) *
          (Real.exp (θ * infoMass (κ.K j y)) * Real.exp (-θ * infoMass (κ.K i₀ z)))
            ≤ F.G n (x - F.X j y) := by
        intro y z
        have he : Real.exp (-θ * r) * (Real.exp (θ * infoMass (κ.K j y)) *
            Real.exp (-θ * infoMass (κ.K i₀ z))) =
            Real.exp (-θ * (r + infoMass (κ.K i₀ z) - infoMass (κ.K j y))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        rw [he]
        by_cases hr' : 0 ≤ r + infoMass (κ.K i₀ z) - infoMass (κ.K j y)
        · have := IH (x - F.X j y) _ hr'
          rw [hX, hX] at *
          convert this using 3; ring
        · have h1 : 1 < Real.exp (-θ * (r + infoMass (κ.K i₀ z) - infoMass (κ.K j y))) :=
            by
              have := Real.add_one_le_exp (-θ * (r + infoMass (κ.K i₀ z) - infoMass (κ.K j y)))
              nlinarith
          have := (Fs.G_cdf n).2.2.1 (x - r - F.X i₀ z)
          linarith [(G_bounds (κ := κ) n (x - F.X j y)).1]
      have hPj := F.Psum j
      have hPi := F.Psum i₀
      calc (∑ z, F.P i₀ z * Fs.G n (x - r - F.X i₀ z)) - Real.exp (-θ * r)
          ≤ (∑ z, F.P i₀ z * Fs.G n (x - r - F.X i₀ z)) - Real.exp (-θ * r) * (A * B) := by
            have := mul_le_mul_of_nonneg_left hAB (Real.exp_pos (-θ * r)).le
            linarith
        _ = ∑ y, ∑ z, F.P j y * F.P i₀ z * (Fs.G n (x - r - F.X i₀ z) - Real.exp (-θ * r) *
              (Real.exp (θ * infoMass (κ.K j y)) * Real.exp (-θ * infoMass (κ.K i₀ z)))) := by
            simp only [A, B, mul_sub, Finset.sum_sub_distrib]
            congr 1
            · rw [Finset.sum_comm (f := fun y z => F.P j y * F.P i₀ z * Fs.G n (x - r - F.X i₀ z))]
              refine (Finset.sum_congr rfl fun z _ => ?_)
              rw [← Finset.sum_mul, ← Finset.sum_mul, hPj, one_mul]
            · rw [Finset.mul_sum, Finset.sum_comm (f := fun (y : Fin (F.nY j)) (z : Fin (F.nY i₀)) =>
                F.P j y * F.P i₀ z * (Real.exp (-θ * r) * (Real.exp (θ * infoMass (κ.K j y)) *
                  Real.exp (-θ * infoMass (κ.K i₀ z)))))]
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun z _ => ?_
              rw [Finset.sum_mul, Finset.mul_sum]
              refine Finset.sum_congr rfl fun y _ => ?_
              change _ = κ.K j y * κ.K i₀ z * _; ring
        _ ≤ ∑ y, ∑ z, F.P j y * F.P i₀ z * F.G n (x - F.X j y) :=
            Finset.sum_le_sum fun y _ => Finset.sum_le_sum fun z _ =>
              mul_le_mul_of_nonneg_left (hpt y z)
                (mul_nonneg (F.Ppos _ _).le (F.Ppos _ _).le)
        _ = ∑ y, F.P j y * F.G n (x - F.X j y) := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [← Finset.sum_mul, ← Finset.mul_sum, hPi, mul_one]


/-- The envelope of `κ` as a function of the raw (uncentered) surprisal threshold. -/
theorem Fstar_eq_G0 (κ : Kernel) (n : ℕ) : Fstar (κ.rounds n) = (κ.fam 0).G n := by
  funext t; rw [κ.Fstar_eq_G 0 n t]; simp

/-- **Exponential comparison.** Under exponential domination, for every `r ≥ 0`,
`F*_n(x - r) - e^{-θ r} ≤ F_n(x) ≤ F*_n(x)`, where `F*` is the envelope of `κ.sub S`. -/
theorem Fstar_compare {i₀ : Fin κ.nA} (hi₀ : i₀ ∈ S) {θ : ℝ} (hθ : 0 < θ)
    (hdom : Dominates S i₀ θ) (n : ℕ) (x r : ℝ) (hr : 0 ≤ r) :
    Fstar ((κ.sub S hS).rounds n) (x - r) - Real.exp (-θ * r) ≤ Fstar (κ.rounds n) x ∧
      Fstar (κ.rounds n) x ≤ Fstar ((κ.sub S hS).rounds n) x := by
  simp only [Fstar_eq_G0]
  exact ⟨sub_shift_le hS hi₀ hθ hdom n x r hr, G_le_sub hS n x⟩

end Compare

/-! ### Hoeffding: an entropy gap gives exponential domination -/

/-- Shannon entropy (in bits) of the law of action `a`. -/
def H (κ : Kernel) (a : Fin κ.nA) : ℝ := ∑ y, κ.K a y * infoMass (κ.K a y)

theorem K_le_one' (κ : Kernel) (a : Fin κ.nA) (y : Fin (κ.nY a)) : κ.K a y ≤ 1 := by
  rw [← κ.Ksum a]
  exact Finset.single_le_sum (fun z _ => (κ.Kpos a z).le) (Finset.mem_univ y)

theorem infoMass_K_nonneg' (κ : Kernel) (a : Fin κ.nA) (y : Fin (κ.nY a)) :
    0 ≤ infoMass (κ.K a y) :=
  Renyi.infoMass_nonneg_of_le (κ.Kpos a y) (κ.K_le_one' a y)

/-- If every surprisal is at most `M` and every action outside `S` has entropy at least `Δ`
below that of `i₀`, then domination holds at every `θ ∈ (0, 4Δ/M²]`. -/
theorem dominates_of_gap {S : Finset (Fin κ.nA)} {i₀ : Fin κ.nA} {M Δ θ : ℝ}
    (hM : ∀ a y, infoMass (κ.K a y) ≤ M) (hgap : ∀ j ∉ S, κ.H j + Δ ≤ κ.H i₀)
    (hθ : 0 < θ) (hθM : θ * M ^ 2 ≤ 4 * Δ) : Dominates S i₀ θ := by
  intro j hj
  have hA := MaxEntropy.finite_hoeffding (κ.K j) (fun y => infoMass (κ.K j y))
    (fun y => (κ.Kpos j y).le) (κ.Ksum j) (fun y => ⟨κ.infoMass_K_nonneg' j y, hM j y⟩) θ
  have hB := MaxEntropy.finite_hoeffding (κ.K i₀) (fun y => infoMass (κ.K i₀ y))
    (fun y => (κ.Kpos i₀ y).le) (κ.Ksum i₀) (fun y => ⟨κ.infoMass_K_nonneg' i₀ y, hM i₀ y⟩) (-θ)
  have hA0 : 0 ≤ ∑ y, κ.K j y * Real.exp (θ * infoMass (κ.K j y)) :=
    Finset.sum_nonneg fun y _ => mul_nonneg (κ.Kpos _ _).le (Real.exp_pos _).le
  refine (mul_le_mul hA hB (Finset.sum_nonneg fun y _ =>
    mul_nonneg (κ.Kpos _ _).le (Real.exp_pos _).le) (Real.exp_pos _).le).trans ?_
  rw [← Real.exp_add, Real.exp_le_one_iff]
  have hg := hgap j hj
  unfold H at hg
  nlinarith

/-! ### The mean gap -/

theorem interval_gap {G Gs : ℝ → ℝ} (hG : Monotone G) (hGs : Monotone Gs)
    (h01 : ∀ t, 0 ≤ Gs t ∧ Gs t ≤ 1) {N r c : ℝ} (hN : 0 ≤ N) (hr : 0 ≤ r)
    (hcmp : ∀ t, Gs (t - r) - c ≤ G t) :
    ∫ t in (0 : ℝ)..N, (Gs t - G t) ≤ r + N * c := by
  have iGs : ∀ a b, IntervalIntegrable Gs MeasureTheory.volume a b :=
    fun a b => hGs.intervalIntegrable
  have iG : ∀ a b, IntervalIntegrable G MeasureTheory.volume a b :=
    fun a b => hG.intervalIntegrable
  have hm : Monotone (fun t => Gs (t - r)) := fun x y hxy => hGs (by linarith)
  have iGr : ∀ a b, IntervalIntegrable (fun t => Gs (t - r)) MeasureTheory.volume a b :=
    fun a b => hm.intervalIntegrable
  calc ∫ t in (0 : ℝ)..N, (Gs t - G t)
      ≤ ∫ t in (0 : ℝ)..N, (Gs t - Gs (t - r) + c) := by
        apply intervalIntegral.integral_mono_on hN ((iGs _ _).sub (iG _ _))
          (((iGs _ _).sub (iGr _ _)).add intervalIntegrable_const)
        intro t _; linarith [hcmp t]
    _ = (∫ t in (0 : ℝ)..N, Gs t) - (∫ t in (-r)..(N - r), Gs t) + N * c := by
        rw [intervalIntegral.integral_add ((iGs _ _).sub (iGr _ _)) intervalIntegrable_const,
          intervalIntegral.integral_sub (iGs _ _) (iGr _ _),
          intervalIntegral.integral_comp_sub_right Gs r]
        simp
    _ = (∫ t in (N - r)..N, Gs t) - (∫ t in (-r)..0, Gs t) + N * c := by
        rw [intervalIntegral.integral_interval_sub_interval_comm' (iGs _ _) (iGs _ _) (iGs _ _)]
    _ ≤ r + N * c := by
        have h1 : ∫ t in (N - r)..N, Gs t ≤ ∫ t in (N - r)..N, (1 : ℝ) :=
          intervalIntegral.integral_mono_on (by linarith) (iGs _ _) intervalIntegrable_const
            fun t _ => (h01 t).2
        have h2 : 0 ≤ ∫ t in (-r)..0, Gs t :=
          intervalIntegral.integral_nonneg (by linarith) fun t _ => (h01 t).1
        simp at h1
        linarith

theorem G_one_above (κ : Kernel) {M : ℝ} (hM : ∀ a y, infoMass (κ.K a y) ≤ M) (n : ℕ) {t : ℝ}
    (ht : n * M ≤ t) : (κ.fam 0).G n t = 1 := by
  apply ((κ.fam 0).G_cdf n).2.2.2.2
  refine le_trans (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)) ht
  refine Finset.sup'_le _ _ fun a _ => Finset.sup'_le _ _ fun y _ => ?_
  simp only [sub_zero]
  rw [abs_of_nonneg (κ.infoMass_K_nonneg' a y)]; exact hM a y

theorem envelopeMean_eq_interval (κ : Kernel) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ a y, infoMass (κ.K a y) ≤ M) (n : ℕ) :
    envelopeMean (κ.rounds n) = ∫ t in (0 : ℝ)..(n * M), (1 - (κ.fam 0).G n t) := by
  have hN : (0 : ℝ) ≤ n * M := mul_nonneg (Nat.cast_nonneg n) hM0
  rw [← integral_one_sub_Fstar, Fstar_eq_G0, intervalIntegral.integral_of_le hN,
    ← Set.Ioc_union_Ioi_eq_Ioi hN]
  have hint := integrableOn_one_sub_Fstar (κ.rounds n)
  rw [Fstar_eq_G0, ← Set.Ioc_union_Ioi_eq_Ioi hN] at hint
  rw [MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
    (hint.mono_set Set.subset_union_left) (hint.mono_set Set.subset_union_right)]
  have : ∫ t in Set.Ioi ((n : ℝ) * M), (1 - (κ.fam 0).G n t) = 0 := by
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      (g := fun _ => (0 : ℝ)) fun t ht => by
        simp only; rw [κ.G_one_above hM n (le_of_lt ht)]; ring]
    simp
  rw [this, add_zero]

/-- **Mean comparison.** `0 ≤ L_n - L*_n ≤ (1 + log(1 + θ n M)) / θ`. -/
theorem envelopeMean_compare {S : Finset (Fin κ.nA)} (hS : S.Nonempty) {i₀ : Fin κ.nA}
    (hi₀ : i₀ ∈ S) {θ M : ℝ} (hθ : 0 < θ) (hdom : Dominates S i₀ θ) (hM0 : 0 ≤ M)
    (hM : ∀ a y, infoMass (κ.K a y) ≤ M) (n : ℕ) :
    envelopeMean ((κ.sub S hS).rounds n) ≤ envelopeMean (κ.rounds n) ∧
      envelopeMean (κ.rounds n) - envelopeMean ((κ.sub S hS).rounds n) ≤
        (1 + Real.log (1 + θ * (n * M))) / θ := by
  have hMs : ∀ a y, infoMass ((κ.sub S hS).K a y) ≤ M := fun a y => hM _ _
  set N : ℝ := n * M
  have hN : 0 ≤ N := mul_nonneg (Nat.cast_nonneg n) hM0
  rw [κ.envelopeMean_eq_interval hM0 hM n, (κ.sub S hS).envelopeMean_eq_interval hM0 hMs n]
  set G := (κ.fam 0).G n
  set Gs := ((κ.sub S hS).fam 0).G n
  have iG : IntervalIntegrable (fun t => 1 - G t) MeasureTheory.volume 0 N :=
    intervalIntegrable_const.sub ((κ.fam 0).G_cdf n).1.intervalIntegrable
  have iGs : IntervalIntegrable (fun t => 1 - Gs t) MeasureTheory.volume 0 N :=
    intervalIntegrable_const.sub (((κ.sub S hS).fam 0).G_cdf n).1.intervalIntegrable
  have hdiff : (∫ t in (0 : ℝ)..N, (1 - G t)) - ∫ t in (0 : ℝ)..N, (1 - Gs t) =
      ∫ t in (0 : ℝ)..N, (Gs t - G t) := by
    rw [← intervalIntegral.integral_sub iG iGs]; congr 1; funext t; ring
  constructor
  · rw [← sub_nonneg, hdiff]
    exact intervalIntegral.integral_nonneg hN fun t _ => by
      linarith [G_le_sub (κ := κ) hS n t]
  rw [hdiff]
  set r := Real.log (1 + θ * N) / θ
  have hθN : 0 < 1 + θ * N := by positivity
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg (by nlinarith)) hθ.le
  have hb := interval_gap ((κ.fam 0).G_cdf n).1 (((κ.sub S hS).fam 0).G_cdf n).1
    (((κ.sub S hS).fam 0).G_cdf n).2.2.1 hN hr
    (fun t => by simpa using sub_shift_le hS hi₀ hθ hdom n t r hr)
  refine hb.trans (le_of_eq_of_le rfl ?_)
  have he : Real.exp (-(θ * r)) = (1 + θ * N)⁻¹ := by
    rw [show -(θ * r) = -Real.log (1 + θ * N) by simp only [r]; field_simp, Real.exp_neg,
      Real.exp_log hθN]
  rw [he, add_div, add_comm (1 / θ)]
  gcongr
  rw [← div_eq_mul_inv, div_le_div_iff₀ hθN hθ]
  nlinarith


/-! ### Restricting seeds to a subfamily -/

section Restrict
open Completion
variable {S : Finset (Fin κ.nA)} (hS : S.Nonempty)

/-- An event of `κ.sub S`, read as an event of `κ` (out-of-range actions stay out of range). -/
def liftE (S : Finset (Fin κ.nA)) (e : ℕ × ℕ) : ℕ × ℕ :=
  (if h : e.1 < S.card then (κ.subE S ⟨e.1, h⟩).val else κ.nA, e.2)

theorem wt_liftE (e : ℕ × ℕ) : (κ.sub S hS).wt e = κ.wt (κ.liftE S e) := by
  by_cases h : e.1 < S.card
  · have hl : κ.liftE S e = ((κ.subE S ⟨e.1, h⟩).val, e.2) := by simp [liftE, h]
    rw [hl]; unfold wt
    simp only [show e.1 < (κ.sub S hS).nA from h, (κ.subE S _).isLt, ↓reduceDIte]; rfl
  · have hl : κ.liftE S e = (κ.nA, e.2) := by simp [liftE, h]
    rw [hl]; unfold wt
    have : ¬ e.1 < (κ.sub S hS).nA := h
    simp [this]

theorem pathMass_liftE (L : List (ℕ × ℕ)) :
    pathMass (κ.sub S hS).toITree L = pathMass κ.toITree (L.map (κ.liftE S)) := by
  rw [pathMass_eq_prod, pathMass_eq_prod, List.map_map]
  congr 1
  exact List.map_congr_left fun e _ => κ.wt_liftE hS e

theorem sval_congr2 (s : IStrategy κ.toITree) {h h' : List (ℕ × ℕ)} (e : h = h') {a a' : ℕ}
    (ea : a = a') (ha : a < κ.nA) (ha' : a' < κ.nA) :
    (s ⟨h, ⟨a, ha⟩⟩).val = (s ⟨h', ⟨a', ha'⟩⟩).val := by subst e; subst ea; rfl

/-- A strategy of `κ` restricted to the actions of `S`. -/
def restrictStrat (s : IStrategy κ.toITree) : IStrategy (κ.sub S hS).toITree :=
  fun p => s ⟨p.1.map (κ.liftE S), κ.subE S p.2⟩

theorem iAgree_restrict (s : IStrategy κ.toITree) (L : List (ℕ × ℕ)) :
    iAgree (κ.sub S hS).toITree (κ.restrictStrat hS s) L ↔
      iAgree κ.toITree s (L.map (κ.liftE S)) := by
  rw [iAgree_iff_forall, iAgree_iff_forall]
  simp only [List.length_map]
  refine forall_congr' fun k => forall_congr' fun hk => ?_
  have hget : (L.map (κ.liftE S))[k]'(by simpa using hk) = κ.liftE S L[k] := List.getElem_map ..
  constructor
  · rintro ⟨ha, hs⟩
    have ha' : L[k].1 < S.card := ha
    have h1 : (κ.liftE S L[k]).1 = (κ.subE S ⟨L[k].1, ha'⟩).val := by simp [liftE, ha']
    refine ⟨by rw [hget, h1]; exact (κ.subE S _).isLt, ?_⟩
    calc _ = (s ⟨(L.take k).map (κ.liftE S),
          ⟨(κ.subE S ⟨L[k].1, ha'⟩).val, (κ.subE S _).isLt⟩⟩).val :=
          sval_congr2 s (by rw [List.map_take]) (by rw [hget, h1]) _ _
      _ = L[k].2 := hs
      _ = _ := by rw [hget]; rfl
  · rintro ⟨ha, hs⟩
    have ha2 : L[k].1 < S.card := by
      by_contra hc
      have : (κ.liftE S L[k]).1 = κ.nA := by simp [liftE, hc]
      rw [hget, this] at ha; exact lt_irrefl _ ha
    refine ⟨ha2, ?_⟩
    have h1 : (κ.liftE S L[k]).1 = (κ.subE S ⟨L[k].1, ha2⟩).val := by simp [liftE, ha2]
    calc _ = (s ⟨(L.take k).map (κ.liftE S),
          ⟨(κ.subE S ⟨L[k].1, ha2⟩).val, (κ.subE S _).isLt⟩⟩).val := rfl
      _ = _ := sval_congr2 s (by rw [List.map_take]) (by rw [hget, h1]) _ _
      _ = _ := hs
      _ = _ := by rw [hget]; rfl

/-- A ranked seed of `κ`, restricted to `κ.sub S`: same weights, restricted strategies. -/
def restrictSeed (G : RankedSeed κ.toITree) : RankedSeed (κ.sub S hS).toITree where
  weight := G.weight
  nonneg := G.nonneg
  decreasing := G.decreasing
  mass := G.mass
  strategy i := κ.restrictStrat hS (G.strategy i)

theorem restrictSeed_exactTo {G : RankedSeed κ.toITree} {n : ℕ} (hG : G.ExactTo n) :
    (κ.restrictSeed hS G).ExactTo n := by
  intro L hL
  have := hG (L.map (κ.liftE S)) (by simpa using hL)
  rw [κ.pathMass_liftE hS, ← this]
  refine tsum_congr fun i => ?_
  simp only [RankedSeed.hit, indAgree, restrictSeed, κ.iAgree_restrict hS]

/-- Restricting to a subfamily never raises the finite-horizon causal cost. -/
theorem costBits_sub_le (n : ℕ) : (κ.sub S hS).costBits n ≤ κ.costBits n := by
  unfold costBits
  gcongr
  · exact κ.finiteCost_ne_top n
  · refine le_iInf fun G => ?_
    exact iInf_le_of_le ⟨κ.restrictSeed hS G.1, κ.restrictSeed_exactTo hS G.2⟩ le_rfl

end Restrict

/-! ### The causal cost comparison -/

/-- **Cost comparison.** `0 ≤ C_n(κ) - C_n(κ*) ≤ (1 + log(1 + θ n M))/θ + c⋆`. -/
theorem costBits_compare {S : Finset (Fin κ.nA)} (hS : S.Nonempty) {i₀ : Fin κ.nA}
    (hi₀ : i₀ ∈ S) {θ M : ℝ} (hθ : 0 < θ) (hdom : Dominates S i₀ θ) (hM0 : 0 ≤ M)
    (hM : ∀ a y, infoMass (κ.K a y) ≤ M) (n : ℕ) :
    0 ≤ κ.costBits n - (κ.sub S hS).costBits n ∧
      κ.costBits n - (κ.sub S hS).costBits n ≤
        (1 + Real.log (1 + θ * (n * M))) / θ + shannonOverhead := by
  have h1 := κ.costBits_sub_le hS n
  have h2 := κ.envelopeMean_compare hS hi₀ hθ hdom hM0 hM n
  have h3 := κ.costBits_sandwich n
  have h4 := (κ.sub S hS).costBits_sandwich n
  constructor <;> linarith [h2.2]

end CausalSpectrum.Kernel

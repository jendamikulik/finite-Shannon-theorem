/-
Tail control for the subfamily seed.

For a stationary kernel `ν` and horizon `q`, the exact finite seed of `causal_truncation`
has at most `2^u` atoms of weight at least `2^{-u}`, and its tail entropy beyond
information `t₀ = q (h_max(ν) + 2δ)` is exponentially small in `q`:
`Σ_{w_i < 2^{-t₀}} -w_i log w_i ≤ Tb ν δ q`.
-/
import CausalSeed.DyadicKernel
import CausalSeed.CausalFloor

noncomputable section
open Classical Finset

namespace CausalSpectrum.Sqrt.IncFamily
variable (F : IncFamily)

/-- Chernoff form of the envelope's upper tail, valid for every `θ ≥ 0`. -/
theorem G_tail_theta (hs : F.SubCentered) (n : ℕ) (y : ℝ) {θ : ℝ} (hθ : 0 ≤ θ) :
    1 - F.G n y ≤ Real.exp (-(θ * y) + n * (θ ^ 2 * F.M ^ 2 / 2)) := by
  obtain ⟨π, hπ⟩ := (F.G_envelope n y).2
  rw [← hπ, Real.exp_add]
  exact (F.upper_chernoff n π y θ hθ).trans
    (mul_le_mul_of_nonneg_left (F.mgfPol_le_sub hs n π hθ) (Real.exp_pos _).le)

end CausalSpectrum.Sqrt.IncFamily

namespace CausalSpectrum.Gap

/-- Discrete layer cake. -/
theorem layer {x t0 : ℝ} (J : ℕ) (hx : t0 < x) (hJ : x ≤ t0 + J) :
    x ≤ t0 + ((range J).filter fun j : ℕ => t0 + j < x).card := by
  have hf : (range J).filter (fun j : ℕ => t0 + j < x) = range ⌈x - t0⌉₊ := by
    ext j
    simp only [mem_filter, mem_range]
    constructor
    · rintro ⟨-, h⟩; exact Nat.lt_ceil.2 (by linarith)
    · intro h
      have h' := Nat.lt_ceil.1 h
      refine ⟨lt_of_lt_of_le h (Nat.ceil_le.2 (by linarith)), by linarith⟩
  rw [hf, card_range]
  linarith [Nat.le_ceil (x - t0)]

/-- Count of heavy atoms. -/
theorem card_heavy_le {w : ℕ → ℝ} {L : ℕ} (hw : ∀ i, 0 ≤ w i) (hs : ∑ i ∈ range L, w i = 1)
    {θ : ℝ} (hθ : 0 < θ) : (((range L).filter fun i => θ ≤ w i).card : ℝ) ≤ 1 / θ := by
  rw [le_div_iff₀ hθ, ← hs]
  calc _ = ∑ i ∈ (range L).filter (fun i => θ ≤ w i), θ := by simp
    _ ≤ ∑ i ∈ (range L).filter (fun i => θ ≤ w i), w i :=
        sum_le_sum fun i hi => (mem_filter.1 hi).2
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun i _ _ => hw i

variable (ν : Kernel)

/-- Parameters of the tail bound. -/
def lamT (δ : ℝ) : ℝ := δ / ((ν.fam ν.hmax).M ^ 2 + 1)

/-- Bound on the tail beyond `q h + 2 δ q + j`, as two geometric terms. -/
def tailB (δ : ℝ) (q j : ℕ) : ℝ :=
  Real.exp (-(lamT ν δ * δ / 2)) ^ q * Real.exp (-(lamT ν δ / 2)) ^ j +
    ((2:ℝ) ^ (-δ)) ^ q * ((2:ℝ) ^ (-(1/2:ℝ))) ^ j

/-- The tail-entropy bound (nats). -/
def Tb (δ : ℝ) (q : ℕ) : ℝ :=
  Real.log 2 * (q * (ν.hmax + 2 * δ) * tailB ν δ q 0 +
    (Real.exp (-(lamT ν δ * δ / 2)) ^ q / (1 - Real.exp (-(lamT ν δ / 2))) +
      ((2:ℝ) ^ (-δ)) ^ q / (1 - (2:ℝ) ^ (-(1/2:ℝ)))))

theorem lamT_pos {δ : ℝ} (hδ : 0 < δ) : 0 < lamT ν δ := by unfold lamT; positivity

/-- The envelope tail and the seed tail beyond `q h + 2 δ q + j`. -/
theorem seedTail_le {δ : ℝ} (hδ : 0 < δ) (q j : ℕ) (atoms : List (Atom (trunc ν.toITree q [])))
    (htail : ∀ t s : ℝ, 0 ≤ s →
      seedTail atoms (t + s) ≤ (1 - Fstar (trunc ν.toITree q []) t) + (2 : ℝ) ^ (-s)) :
    seedTail atoms (q * ν.hmax + 2 * δ * q + j) ≤ tailB ν δ q j := by
  set s : ℝ := δ * q + j / 2
  have hs : 0 ≤ s := by positivity
  have := htail (q * ν.hmax + s) s hs
  have hF : ∀ t, Fstar (trunc ν.toITree q []) t = (ν.fam ν.hmax).G q (t - q * ν.hmax) :=
    fun t => by rw [ν.trunc_toITree, ν.Fstar_eq_G]
  rw [show q * ν.hmax + s + s = q * ν.hmax + 2 * δ * q + j by ring,
    hF, show q * ν.hmax + s - q * ν.hmax = s by ring] at this
  refine this.trans (add_le_add ?_ ?_)
  · have hl := lamT_pos ν hδ
    refine ((ν.fam ν.hmax).G_tail_theta ν.fam_hmax_sub q s hl.le).trans ?_
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have hM : lamT ν δ * (ν.fam ν.hmax).M ^ 2 ≤ δ := by
      unfold lamT
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith [sq_nonneg (ν.fam ν.hmax).M]
    have : (q:ℝ) * (lamT ν δ ^ 2 * (ν.fam ν.hmax).M ^ 2 / 2) ≤ q * (lamT ν δ * δ / 2) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      nlinarith [hl]
    simp only [s] at *
    nlinarith
  · rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
      ← Real.rpow_mul (by norm_num), ← Real.rpow_add (by norm_num)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    simp only [s]; linarith

/-- **Tail entropy.** -/
theorem tail_entropy_le {δ : ℝ} (hδ : 0 < δ) (q : ℕ) (atoms : List (Atom (trunc ν.toITree q [])))
    (hpos : ∀ a ∈ atoms, 0 < a.1)
    (htail : ∀ t s : ℝ, 0 ≤ s →
      seedTail atoms (t + s) ≤ (1 - Fstar (trunc ν.toITree q []) t) + (2 : ℝ) ^ (-s)) :
    ∑ i ∈ range atoms.length,
        (if atomWeight atoms i < (2:ℝ) ^ (-(q * ν.hmax + 2 * δ * q))
          then Real.negMulLog (atomWeight atoms i) else 0) ≤ Tb ν δ q := by
  set w := atomWeight atoms
  set L := atoms.length
  set t0 : ℝ := q * ν.hmax + 2 * δ * q
  have hwpos : ∀ i ∈ range L, 0 < w i := fun i hi => by
    show 0 < atomWeight atoms i
    unfold atomWeight; rw [dif_pos (mem_range.1 hi)]; exact hpos _ (List.getElem_mem _)
  -- tail sums as seedTail
  have htl : ∀ t : ℝ, ∑ i ∈ range L, (if t < infoMass (w i) then w i else 0) = seedTail atoms t :=
    fun t => Completion.sum_range_atomWeight (fun x => if t < infoMass x then x else 0) atoms
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, ∀ i ∈ range L, infoMass (w i) ≤ t0 + J := by
    refine ⟨⌈∑ i ∈ range L, |infoMass (w i)| + |t0|⌉₊, fun i hi => ?_⟩
    have h1 := single_le_sum (f := fun i => |infoMass (w i)|) (fun _ _ => abs_nonneg _) hi
    have h2 := Nat.le_ceil (∑ i ∈ range L, |infoMass (w i)| + |t0|)
    have := le_abs_self (infoMass (w i)); have := neg_abs_le t0
    linarith
  have hiff : ∀ i ∈ range L, (w i < (2:ℝ) ^ (-t0) ↔ t0 < infoMass (w i)) := by
    intro i hi
    have hp := hwpos i hi
    rw [infoMass, ← Real.rpow_logb (by norm_num : (0:ℝ) < 2) (by norm_num) hp]
    rw [Real.rpow_lt_rpow_left_iff (by norm_num), Real.logb_rpow (by norm_num) (by norm_num)]
    constructor <;> intro h <;> linarith
  have hpt : ∀ i ∈ range L, (if w i < (2:ℝ) ^ (-t0) then Real.negMulLog (w i) else 0) ≤
      Real.log 2 * (t0 * (if t0 < infoMass (w i) then w i else 0) +
        ∑ j ∈ range J, (if t0 + j < infoMass (w i) then w i else 0)) := by
    intro i hi
    have hp := hwpos i hi
    by_cases h : t0 < infoMass (w i)
    · rw [if_pos ((hiff i hi).2 h), if_pos h, ← sum_filter, sum_const, nsmul_eq_mul]
      have hn : Real.negMulLog (w i) = Real.log 2 * (w i * infoMass (w i)) := by
        rw [Real.negMulLog, infoMass, Real.logb]; field_simp
      rw [hn]
      have := layer J h (hJ i hi)
      have hl2 : 0 < Real.log 2 := Real.log_pos one_lt_two
      apply mul_le_mul_of_nonneg_left _ hl2.le
      nlinarith
    · rw [if_neg (fun h' => h ((hiff i hi).1 h')), if_neg h, mul_zero, zero_add]
      refine mul_nonneg (Real.log_nonneg one_le_two) (sum_nonneg fun j _ => ?_)
      split_ifs <;> simp [hp.le]
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_comm]
  simp_rw [htl]
  unfold Tb
  apply mul_le_mul_of_nonneg_left _ (Real.log_nonneg one_le_two)
  have h0 : seedTail atoms t0 ≤ tailB ν δ q 0 := by
    have := seedTail_le ν hδ q 0 atoms htail; simpa using this
  have ht0 : 0 ≤ t0 := by
    have := ν.hmax_nonneg; positivity
  have hj : ∀ j ∈ range J, seedTail atoms (t0 + j) ≤ tailB ν δ q j := fun j _ =>
    seedTail_le ν hδ q j atoms htail
  have hgeo : ∀ r : ℝ, 0 ≤ r → r < 1 → ∑ j ∈ range J, r ^ j ≤ 1 / (1 - r) := fun r h0 h1 => by
    rw [geom_sum_eq h1.ne, show (r ^ J - 1) / (r - 1) = (1 - r ^ J) / (1 - r) by
      rw [← neg_div_neg_eq]; ring_nf]
    exact div_le_div_of_nonneg_right (by linarith [pow_nonneg h0 J]) (by linarith)
  have hr1 : Real.exp (-(lamT ν δ / 2)) < 1 := Real.exp_lt_one_iff.2 (by
    have := lamT_pos ν hδ; linarith)
  have hr2 : (2:ℝ) ^ (-(1/2:ℝ)) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hsum : ∑ j ∈ range J, tailB ν δ q j ≤
      Real.exp (-(lamT ν δ * δ / 2)) ^ q / (1 - Real.exp (-(lamT ν δ / 2))) +
        ((2:ℝ) ^ (-δ)) ^ q / (1 - (2:ℝ) ^ (-(1/2:ℝ))) := by
    unfold tailB
    rw [sum_add_distrib, ← mul_sum, ← mul_sum]
    refine add_le_add ((mul_le_mul_of_nonneg_left (hgeo _ (Real.exp_pos _).le hr1)
      (by positivity)).trans_eq (by ring))
      ((mul_le_mul_of_nonneg_left (hgeo _ (by positivity) hr2) (by positivity)).trans_eq (by ring))
  have : t0 * seedTail atoms t0 ≤ q * (ν.hmax + 2 * δ) * tailB ν δ q 0 := by
    rw [show (q:ℝ) * (ν.hmax + 2 * δ) = t0 by simp only [t0]; ring]
    exact mul_le_mul_of_nonneg_left h0 ht0
  linarith [sum_le_sum hj]

end CausalSpectrum.Gap

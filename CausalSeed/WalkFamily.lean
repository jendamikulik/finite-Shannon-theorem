/-
Walks with increments in `{-1, 0, 1}`: the law of the limiting maximum, and the explicit
reciprocal-gap family `Q_h`.
-/
import CausalSeed.WalkLimit

noncomputable section
open Classical Finset Filter
open scoped Topology

namespace CausalSpectrum.Walk
namespace Law
variable (W : Law)

/-- `P(M_n ≥ u)`. -/
def tl (n : ℕ) (u : ℝ) : ℝ := W.E n (fun z => if u ≤ M z n then 1 else 0)

theorem tl_nonneg (n : ℕ) (u : ℝ) : 0 ≤ W.tl n u :=
  W.E_nonneg n fun _ => by split_ifs <;> norm_num

theorem tl_of_nonpos (n : ℕ) {u : ℝ} (hu : u ≤ 0) : W.tl n u = 1 := by
  unfold tl
  have : (fun z => if u ≤ M z n then (1:ℝ) else 0) = fun _ => 1 := by
    funext z; rw [if_pos (hu.trans (M_nonneg z n))]
  rw [this, E_const]

theorem tl_zero {u : ℝ} (hu : 0 < u) : W.tl 0 u = 0 := by
  unfold tl; rw [E_zero, M_zero, if_neg (by linarith)]

theorem tl_succ (n : ℕ) {u : ℝ} (hu : 0 < u) :
    W.tl (n + 1) u = ∑ y, W.Q y * W.tl n (u - W.X y) := by
  unfold tl
  rw [E_succ]
  refine sum_congr rfl fun y _ => ?_
  congr 1; congr 1; funext z
  rw [M_consS]
  by_cases h : u - W.X y ≤ M z n
  · rw [if_pos h, if_pos (le_max_of_le_right (by linarith))]
  · rw [if_neg h, if_neg]
    intro h'
    rcases le_max_iff.1 h' with h'' | h''
    · linarith
    · exact h (by linarith)

/-- Upper bound `P(M_n ≥ u) ≤ r^u` from the martingale identity `E r^{-X} = 1`. -/
theorem tl_le_rpow {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1)
    (hmart : ∑ y, W.Q y * r ^ (-W.X y) = 1) : ∀ (n : ℕ) (u : ℝ), W.tl n u ≤ r ^ u
  | 0, u => by
    rcases le_or_gt u 0 with hu | hu
    · rw [W.tl_of_nonpos 0 hu]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 hu
    · rw [W.tl_zero hu]; positivity
  | n + 1, u => by
    rcases le_or_gt u 0 with hu | hu
    · rw [W.tl_of_nonpos _ hu]; exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hr0 hr1 hu
    · rw [W.tl_succ n hu]
      calc ∑ y, W.Q y * W.tl n (u - W.X y) ≤ ∑ y, W.Q y * r ^ (u - W.X y) :=
            sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (tl_le_rpow hr0 hr1 hmart n _) (W.Qnn y)
        _ = r ^ u := by
            rw [← mul_one (r ^ u), ← hmart, mul_sum]
            refine sum_congr rfl fun y _ => ?_
            rw [sub_eq_add_neg, Real.rpow_add hr0]; ring

/-- Increments in `{-1, 0, 1}`. -/
def Unit3 : Prop := ∀ y, W.X y = -1 ∨ W.X y = 0 ∨ W.X y = 1

/-- Lower bound `r^j - P(M_n ≥ j) ≤ s^j φ(s)^n`, `φ(s) = E s^{-X}`, for integers `j ≥ 0`. -/
theorem tl_lower (h3 : W.Unit3) {r s : ℝ} (hr0 : 0 < r) (hrs : r ≤ s)
    (hmart : ∑ y, W.Q y * r ^ (-W.X y) = 1) :
    ∀ (n j : ℕ), r ^ (j : ℝ) - W.tl n j ≤ s ^ (j : ℝ) * (∑ y, W.Q y * s ^ (-W.X y)) ^ n
  | 0, j => by
    have := W.tl_nonneg 0 j
    have := Real.rpow_le_rpow hr0.le hrs (Nat.cast_nonneg j)
    simp only [pow_zero, mul_one]; linarith
  | n + 1, 0 => by
    rw [W.tl_of_nonpos _ (by simp)]
    have hs : 0 < s := hr0.trans_le hrs
    have : 0 ≤ ∑ y, W.Q y * s ^ (-W.X y) :=
      sum_nonneg fun y _ => mul_nonneg (W.Qnn y) (Real.rpow_nonneg hs.le _)
    simp only [Nat.cast_zero, Real.rpow_zero, sub_self, one_mul]; positivity
  | n + 1, j + 1 => by
    have hs : 0 < s := hr0.trans_le hrs
    have hu : (0:ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
    rw [W.tl_succ n hu]
    have hr : r ^ (((j + 1 : ℕ) : ℝ)) = ∑ y, W.Q y * r ^ (((j + 1 : ℕ) : ℝ) - W.X y) := by
      rw [← mul_one (r ^ _), ← hmart, mul_sum]
      refine sum_congr rfl fun y _ => ?_
      rw [sub_eq_add_neg, Real.rpow_add hr0]; ring
    have hsj : s ^ (((j + 1 : ℕ) : ℝ)) * (∑ y, W.Q y * s ^ (-W.X y)) ^ (n + 1) =
        ∑ y, W.Q y * (s ^ (((j + 1 : ℕ) : ℝ) - W.X y) * (∑ y, W.Q y * s ^ (-W.X y)) ^ n) := by
      have e : ∀ y, W.Q y * (s ^ (((j + 1 : ℕ) : ℝ) - W.X y) * (∑ y, W.Q y * s ^ (-W.X y)) ^ n) =
          W.Q y * s ^ (-W.X y) * (s ^ (((j + 1 : ℕ) : ℝ)) * (∑ y, W.Q y * s ^ (-W.X y)) ^ n) := by
        intro y; rw [sub_eq_add_neg, Real.rpow_add hs]; ring
      rw [sum_congr rfl fun y _ => e y, ← sum_mul, pow_succ]; ring
    rw [hr, hsj, ← sum_sub_distrib]
    refine sum_le_sum fun y _ => ?_
    rw [← mul_sub]
    refine mul_le_mul_of_nonneg_left ?_ (W.Qnn y)
    obtain ⟨i, hi⟩ : ∃ i : ℕ, ((j + 1 : ℕ) : ℝ) - W.X y = i := by
      rcases h3 y with h | h | h
      · exact ⟨j + 2, by rw [h]; push_cast; ring⟩
      · exact ⟨j + 1, by rw [h]; ring⟩
      · exact ⟨j, by rw [h]; push_cast; ring⟩
    rw [hi]
    exact tl_lower h3 hr0 hrs hmart n i

theorem S_int (h3 : W.Unit3) {n : ℕ} (ys : Fin n → Fin W.k) :
    ∀ j, ∃ z : ℤ, S (W.seq ys) j = z ∧ z ≤ j
  | 0 => ⟨0, by simp [S_zero]⟩
  | j + 1 => by
    obtain ⟨z, hz, hzj⟩ := S_int h3 ys j
    rw [S_succ, hz]
    unfold seq
    by_cases hj : j < n
    · rw [dif_pos hj]
      rcases h3 (ys ⟨j, hj⟩) with h | h | h <;> rw [h]
      · exact ⟨z - 1, by push_cast; ring, by omega⟩
      · exact ⟨z, by ring, by omega⟩
      · exact ⟨z + 1, by push_cast; ring, by omega⟩
    · rw [dif_neg hj]; exact ⟨z, by ring, by omega⟩

theorem sum_ind (N : ℕ) : ∀ n : ℕ, ∑ j ∈ range n, (if j + 1 ≤ N then (1:ℝ) else 0) = min n N
  | 0 => by simp
  | n + 1 => by
    rw [sum_range_succ, sum_ind N n]
    by_cases h : n + 1 ≤ N
    · rw [if_pos h, min_eq_left h, min_eq_left (by omega)]; push_cast; ring
    · rw [if_neg h, add_zero]
      rw [min_eq_right (by omega), min_eq_right (by omega)]

/-- `E M_n = ∑_{j=1}^n P(M_n ≥ j)` for increments in `{-1, 0, 1}`. -/
theorem EM_eq_tl (h3 : W.Unit3) (n : ℕ) : W.EM n = ∑ j ∈ range n, W.tl n (j + 1) := by
  unfold EM tl
  rw [← E_sum]
  refine sum_congr rfl fun ys _ => ?_
  congr 1
  dsimp only
  obtain ⟨j, hj, he⟩ := exists_mem_eq_sup' nonempty_range_add_one (S (W.seq ys))
  obtain ⟨z, hz, hzj⟩ := W.S_int h3 ys j
  have hM : M (W.seq ys) n = z := by rw [← hz]; exact he
  have hz0 : 0 ≤ z := by
    have := M_nonneg (W.seq ys) n; rw [hM] at this; exact_mod_cast this
  obtain ⟨N, rfl⟩ : ∃ N : ℕ, z = N := ⟨z.toNat, by omega⟩
  have hN : N ≤ n := by simp at hj; omega
  rw [hM]
  have : ∀ j : ℕ, ((j : ℝ) + 1 ≤ ((N : ℤ) : ℝ) ↔ j + 1 ≤ N) := fun j => by
    push_cast; exact_mod_cast Iff.rfl
  simp only [this]
  rw [sum_ind N n, min_eq_right hN]; push_cast; rfl

/-- **Limit of `E M_n`** for increments in `{-1, 0, 1}`: if `E r^{-X} = 1` with `0 < r < 1` and
`φ(s) = E s^{-X} < 1` for some `s ∈ [r, 1)`, then `E M_n → r / (1 - r)`. -/
theorem EM_tendsto (h3 : W.Unit3) {r s : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (hrs : r ≤ s) (hs1 : s < 1)
    (hmart : ∑ y, W.Q y * r ^ (-W.X y) = 1) (hφ : ∑ y, W.Q y * s ^ (-W.X y) < 1) :
    Tendsto W.EM atTop (𝓝 (r / (1 - r))) := by
  set φ := ∑ y, W.Q y * s ^ (-W.X y)
  have hs0 : 0 < s := hr0.trans_le hrs
  have hφ0 : 0 ≤ φ := sum_nonneg fun y _ => mul_nonneg (W.Qnn y) (Real.rpow_nonneg hs0.le _)
  have hgeo : ∀ (x : ℝ) (n : ℕ), x ≠ 1 → ∑ j ∈ range n, x ^ (j + 1) = x * (1 - x ^ n) / (1 - x) :=
    fun x n hx => by
      have := geom_sum_eq hx n
      rw [show ∑ j ∈ range n, x ^ (j + 1) = x * ∑ j ∈ range n, x ^ j by
        rw [mul_sum]; exact sum_congr rfl fun j _ => by ring, this]
      have : (1:ℝ) - x ≠ 0 := sub_ne_zero.2 (Ne.symm hx)
      have : x - 1 ≠ 0 := sub_ne_zero.2 hx
      field_simp; ring
  have hup : ∀ n, W.EM n ≤ r / (1 - r) := fun n => by
    rw [W.EM_eq_tl h3]
    calc ∑ j ∈ range n, W.tl n (j + 1) ≤ ∑ j ∈ range n, r ^ (j + 1) :=
          sum_le_sum fun j _ => by
            have := W.tl_le_rpow hr0 hr1.le hmart n ((j + 1 : ℕ) : ℝ)
            rw [Real.rpow_natCast] at this; push_cast at this; exact this
      _ = r * (1 - r ^ n) / (1 - r) := hgeo r n hr1.ne
      _ ≤ r / (1 - r) := by
          have : (0:ℝ) < 1 - r := by linarith
          rw [div_le_div_iff_of_pos_right this]
          have := pow_nonneg hr0.le n; nlinarith
  have hlo : ∀ n, r / (1 - r) - (r ^ (n + 1) / (1 - r) + φ ^ n * (s / (1 - s))) ≤ W.EM n := fun n => by
    rw [W.EM_eq_tl h3]
    have h1 : ∑ j ∈ range n, r ^ (j + 1) - ∑ j ∈ range n, W.tl n (j + 1) ≤
        ∑ j ∈ range n, s ^ (j + 1) * φ ^ n := by
      rw [← sum_sub_distrib]
      refine sum_le_sum fun j _ => ?_
      have := W.tl_lower h3 hr0 hrs hmart n (j + 1)
      simp only [Real.rpow_natCast] at this
      push_cast at this; exact this
    rw [← sum_mul, hgeo r n hr1.ne, hgeo s n hs1.ne] at h1
    have : (0:ℝ) < 1 - r := by linarith
    have : (0:ℝ) < 1 - s := by linarith
    have e1 : r / (1 - r) = r * (1 - r ^ n) / (1 - r) + r ^ (n + 1) / (1 - r) := by
      field_simp; ring
    have k : s * (1 - s ^ n) / (1 - s) ≤ s / (1 - s) := by
      rw [div_le_div_iff_of_pos_right (by assumption)]
      have := pow_nonneg hs0.le n; nlinarith
    have e2 : s * (1 - s ^ n) / (1 - s) * φ ^ n ≤ φ ^ n * (s / (1 - s)) :=
      (mul_le_mul_of_nonneg_right k (pow_nonneg hφ0 n)).trans (le_of_eq (mul_comm _ _))
    linarith
  have hlim : Tendsto (fun n : ℕ => r / (1 - r) - (r ^ (n + 1) / (1 - r) + φ ^ n * (s / (1 - s))))
      atTop (𝓝 (r / (1 - r))) := by
    have a : Tendsto (fun n : ℕ => r ^ (n + 1) / (1 - r)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1).comp (tendsto_add_atTop_nat 1)
      simpa using this.div_const (1 - r)
    have b : Tendsto (fun n : ℕ => φ ^ n * (s / (1 - s))) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hφ0 hφ).mul_const (s / (1 - s))
    simpa using tendsto_const_nhds.sub (a.add b)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hup

end Law
/-! ### The reciprocal-gap family `Q_h`, `h = d + 2` -/

namespace Family
variable (d : ℕ)

/-- Alphabet size of `Q_h`: `2^{h-2} + 1 + (2^h - 2)`. -/
def fk : ℕ := 2 ^ d + 1 + (2 ^ (d + 2) - 2)

/-- Atoms of `Q_h`: `2^{h-2}` atoms `2^{-(h-1)}`, one atom `2^{-h}`, `2^h - 2` atoms `2^{-(h+1)}`. -/
def qv (i : ℕ) : ℝ :=
  if i < 2 ^ d then (1 / 2) ^ (d + 1) else if i = 2 ^ d then (1 / 2) ^ (d + 2) else (1 / 2) ^ (d + 3)

/-- The centered surprisal of each atom. -/
def xv (i : ℕ) : ℝ := if i < 2 ^ d then -1 else if i = 2 ^ d then 0 else 1

/-- The entropy gap `Δ = 2^{-h}`. -/
def Δ : ℝ := (1 / 2) ^ (d + 2)

theorem Δ_pos : 0 < Δ d := by unfold Δ; positivity

theorem Δ_le : Δ d ≤ 1 / 4 := by
  unfold Δ
  calc (1 / 2 : ℝ) ^ (d + 2) ≤ (1 / 2) ^ 2 := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 4 := by norm_num

theorem two_le : 2 ≤ 2 ^ (d + 2) := by
  calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem class_sum (g : ℝ → ℝ) :
    ∑ y : Fin (fk d), qv d y * g (xv d y) =
      1 / 2 * g (-1) + Δ d * g 0 + (1 / 2 - Δ d) * g 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => qv d i * g (xv d i)), fk, add_assoc, sum_range_add,
    sum_range_add, sum_range_one]
  have h1 : ∑ i ∈ range (2 ^ d), qv d i * g (xv d i) = ∑ i ∈ range (2 ^ d), (1 / 2 : ℝ) ^ (d + 1) * g (-1) :=
    sum_congr rfl fun i hi => by rw [qv, xv, if_pos (mem_range.1 hi), if_pos (mem_range.1 hi)]
  have h3 : ∑ i ∈ range (2 ^ (d + 2) - 2), qv d (2 ^ d + (1 + i)) * g (xv d (2 ^ d + (1 + i))) =
      ∑ i ∈ range (2 ^ (d + 2) - 2), (1 / 2 : ℝ) ^ (d + 3) * g 1 :=
    sum_congr rfl fun i _ => by
      rw [qv, xv, if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
  rw [h1, h3, sum_const, sum_const, card_range, card_range, nsmul_eq_mul, nsmul_eq_mul,
    Nat.cast_sub (two_le d)]
  simp only [qv, xv, add_zero, lt_irrefl, if_false, if_true, Δ]
  push_cast
  have e1 : (2 : ℝ) ^ d * (1 / 2) ^ (d + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  have e2 : ((2 : ℝ) ^ (d + 2) - 2) * (1 / 2) ^ (d + 3) = 1 / 2 - (1 / 2) ^ (d + 2) := by
    have a : (2 : ℝ) ^ (d + 2) * (1 / 2) ^ (d + 2) = 1 := by rw [← mul_pow]; norm_num
    have b : (1 / 2 : ℝ) ^ (d + 3) = (1 / 2) ^ (d + 2) / 2 := by
      rw [show d + 3 = (d + 2) + 1 by ring, pow_succ]; ring
    rw [b]; linear_combination a / 2
  linear_combination g (-1) * e1 + g 1 * e2

/-- The two-action kernel `(U_h, Q_h)` with `h = d + 2`. -/
def A : TwoAction where
  m := 2 ^ (d + 2)
  hm := by positivity
  k := fk d
  hk := by unfold fk; have := Nat.one_le_two_pow (n := d); omega
  Q y := qv d y
  Qpos y := by unfold qv; split_ifs <;> positivity
  Qsum := by
    have := class_sum d (fun _ => 1)
    simp only [mul_one] at this
    rw [this]; ring

theorem h_eq : (A d).h = d + 2 := by
  show Real.logb 2 ((2 ^ (d + 2) : ℕ) : ℝ) = d + 2
  push_cast; rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)]; push_cast; ring

theorem infoMass_half_pow (c : ℕ) : infoMass ((1 / 2 : ℝ) ^ c) = c := by
  unfold infoMass
  rw [Real.logb_pow, one_div, Real.logb_inv, Real.logb_self_eq_one (by norm_num)]; ring

theorem X_eq (y : Fin (fk d)) : (A d).law.X y = xv d y := by
  show infoMass (qv d y) - (A d).h = _
  rw [h_eq]
  unfold qv xv
  split_ifs <;> rw [infoMass_half_pow] <;> push_cast <;> ring

theorem law_sum (g : ℝ → ℝ) :
    ∑ y, (A d).law.Q y * g ((A d).law.X y) = 1 / 2 * g (-1) + Δ d * g 0 + (1 / 2 - Δ d) * g 1 := by
  refine (sum_congr rfl fun y _ => ?_).trans (class_sum d g)
  have h := X_eq d y
  rw [h]; rfl

theorem dyadic : (A d).Dyadic (d + 2) := by
  refine ⟨rfl, fun y => ?_⟩
  show ∃ c : ℕ, qv d y = _
  unfold qv; split_ifs
  exacts [⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩]

theorem unit3 : (A d).law.Unit3 := fun y => by
  have h := X_eq d y
  rw [h]; unfold xv; split_ifs <;> simp

/-- **Entropy gap.** `H(U_h) - H(Q_h) = Δ = 2^{-h}`. -/
theorem gap : (A d).h - (A d).HQ = Δ d := by
  have hm := (A d).mean_eq
  have : (A d).law.mean = -Δ d := by
    have := law_sum d id
    simp only [id] at this
    unfold Law.mean; rw [this]; ring
  linarith

/-- The ratio `r = p / q = 1 - 2Δ`. -/
def r : ℝ := 1 - 2 * Δ d

theorem r_pos : 0 < r d := by unfold r; linarith [Δ_le d]
theorem r_lt : r d < 1 := by unfold r; linarith [Δ_pos d]

theorem mart : ∑ y, (A d).law.Q y * r d ^ (-(A d).law.X y) = 1 := by
  rw [law_sum d (fun x => r d ^ (-x))]
  have h := r_pos d
  simp only [neg_neg, Real.rpow_one, neg_zero, Real.rpow_zero, Real.rpow_neg_one]
  unfold r at h ⊢
  field_simp; ring

theorem phi_eq : ∑ y, (A d).law.Q y * Real.sqrt (r d) ^ (-(A d).law.X y) =
    Δ d + Real.sqrt (r d) := by
  rw [law_sum d (fun x => Real.sqrt (r d) ^ (-x))]
  have h := Real.sqrt_pos.2 (r_pos d)
  have hs := Real.sq_sqrt (r_pos d).le
  simp only [neg_neg, Real.rpow_one, neg_zero, Real.rpow_zero, Real.rpow_neg_one]
  have e : 1 / 2 - Δ d = r d / 2 := by unfold r; ring
  rw [e]
  generalize Real.sqrt (r d) = t at h hs ⊢
  rw [← hs]
  field_simp; ring

theorem lam_lt : Δ d + Real.sqrt (r d) < 1 := by
  have hΔ := Δ_pos d
  have : Real.sqrt (r d) < 1 - Δ d := by
    rw [Real.sqrt_lt' (by linarith [Δ_le d])]
    unfold r; nlinarith
  linarith

theorem EM_tendsto : Tendsto (A d).law.EM atTop (𝓝 (1 / (2 * Δ d) - 1)) := by
  have hr := r_pos d
  have hrs : r d ≤ Real.sqrt (r d) := by
    have := Real.sqrt_le_sqrt (r_lt d).le
    rw [Real.sqrt_one] at this
    calc r d = Real.sqrt (r d) * Real.sqrt (r d) := (Real.mul_self_sqrt hr.le).symm
      _ ≤ Real.sqrt (r d) * 1 := mul_le_mul_of_nonneg_left this (Real.sqrt_nonneg _)
      _ = Real.sqrt (r d) := mul_one _
  have hs1 : Real.sqrt (r d) < 1 := by linarith [lam_lt d, Δ_pos d]
  have := (A d).law.EM_tendsto (unit3 d) hr (r_lt d) hrs hs1 (mart d)
    (by rw [phi_eq]; exact lam_lt d)
  convert this using 2
  unfold r; have := Δ_pos d; field_simp; ring

/-- **Reciprocal-gap limit.** `lim (C_n - n h) = 1/(2Δ) - 1 = 2^{h-1} - 1`. -/
theorem cost_limit :
    Tendsto (fun n : ℕ => (A d).kernel.costBits n - n * (A d).h) atTop (𝓝 (1 / (2 * Δ d) - 1)) := by
  have : (fun n : ℕ => (A d).kernel.costBits n - n * (A d).h) = (A d).law.EM := by
    funext n; rw [(A d).cost_eq (dyadic d)]; ring
  rw [this]; exact EM_tendsto d

theorem limit_value : 1 / (2 * Δ d) - 1 = 2 ^ (d + 1) - 1 := by
  unfold Δ; rw [one_div_pow]; field_simp; ring

/-- `θ = ½ ln(q/p)` with `q = 1/2`, `p = 1/2 - Δ`. -/
def θ : ℝ := Real.log ((1 / 2) / (1 / 2 - Δ d)) / 2

/-- `λ = Δ + 2 √(p q)`. -/
def lam : ℝ := Δ d + 2 * Real.sqrt ((1 / 2 - Δ d) * (1 / 2))

theorem lam_eq : lam d = Δ d + Real.sqrt (r d) := by
  unfold lam
  congr 1
  rw [show (1 / 2 - Δ d) * (1 / 2) = r d / 4 by unfold r; ring, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 4),
    show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

theorem exp_θ : Real.exp (θ d) = 1 / Real.sqrt (r d) := by
  have hr := r_pos d
  have hq : (1 / 2) / (1 / 2 - Δ d) = 1 / r d := by unfold r at hr ⊢; field_simp
  have h2 : Real.exp (θ d) ^ 2 = 1 / r d := by
    rw [← Real.exp_nat_mul, θ, hq]; push_cast
    rw [show (2:ℝ) * (Real.log (1 / r d) / 2) = Real.log (1 / r d) by ring, Real.exp_log (by positivity)]
  have hs := Real.sq_sqrt hr.le
  have hp := Real.sqrt_pos.2 hr
  have : Real.exp (θ d) = Real.sqrt (1 / r d) := by
    rw [← h2, Real.sqrt_sq (Real.exp_pos _).le]
  rw [this, Real.sqrt_div' _ hr.le, Real.sqrt_one]

theorem θ_pos : 0 < θ d := by
  unfold θ
  have hΔ := Δ_pos d
  have : 1 < (1 / 2) / (1 / 2 - Δ d) := by
    rw [lt_div_iff₀ (by linarith [Δ_le d])]; linarith
  have := Real.log_pos this
  positivity

theorem mgf_θ : (A d).law.mgf (θ d) = lam d := by
  unfold Law.mgf
  rw [law_sum d (fun x => Real.exp (θ d * x)), lam_eq]
  have hr := r_pos d
  have hp := Real.sqrt_pos.2 hr
  have hs := Real.sq_sqrt hr.le
  have e1 : Real.exp (θ d * -1) = Real.sqrt (r d) := by
    rw [mul_neg_one, Real.exp_neg, exp_θ]; field_simp
  rw [e1, mul_zero, Real.exp_zero, mul_one, mul_one, exp_θ]
  have e : 1 / 2 - Δ d = r d / 2 := by unfold r; ring
  rw [e]
  generalize Real.sqrt (r d) = t at hp hs ⊢
  rw [← hs]
  field_simp; ring

/-- **Sharper error bound.**
`0 ≤ 1/(2Δ) - 1 - (C_n - n h) ≤ λ^{n+1} / ((e^θ - 1)(n+1)(1-λ))`. -/
theorem sharper_bound (n : ℕ) :
    0 ≤ 1 / (2 * Δ d) - 1 - ((A d).kernel.costBits n - n * (A d).h) ∧
      1 / (2 * Δ d) - 1 - ((A d).kernel.costBits n - n * (A d).h) ≤
        lam d ^ (n + 1) / ((Real.exp (θ d) - 1) * (n + 1) * (1 - lam d)) := by
  have hc : (A d).kernel.costBits n - n * (A d).h = (A d).law.EM n := by
    rw [(A d).cost_eq (dyadic d)]; ring
  rw [hc]
  have hint : ∀ y, ∃ z : ℤ, (A d).law.X y = z := fun y => by
    rcases unit3 d y with h | h | h <;> rw [h]
    exacts [⟨-1, by simp⟩, ⟨0, by simp⟩, ⟨1, by simp⟩]
  have he : 0 < Real.exp (θ d) - 1 := by linarith [Real.add_one_le_exp (θ d), θ_pos d]
  have hl0 : 0 ≤ lam d := by rw [lam_eq]; linarith [Δ_pos d, Real.sqrt_nonneg (r d)]
  have hl1 : lam d < 1 := by rw [lam_eq]; exact lam_lt d
  have hb : ∀ k, (A d).law.ESp k ≤ 1 / (Real.exp (θ d) - 1) * lam d ^ k := fun k => by
    rw [← mgf_θ]; exact (A d).law.ESp_le_mgf_int hint (θ_pos d) k
  obtain ⟨-, ht, -, hbd⟩ := (A d).law.tail_bound (by positivity) hl0 hl1 hb
  have hℓ : (∑' j, (A d).law.term j) = 1 / (2 * Δ d) - 1 := tendsto_nhds_unique ht (EM_tendsto d)
  rw [← hℓ]
  refine ⟨(hbd n).1, (hbd n).2.trans (le_of_eq ?_)⟩
  field_simp

theorem EM_one : (A d).law.EM 1 = 1 / 2 - Δ d := by
  rw [Law.spitzer, sum_range_one]
  simp only [Law.ESp, Law.E_succ, Law.E_zero, S_consS, S_zero, add_zero]
  rw [law_sum d (fun x => max x 0)]
  norm_num

theorem EM_two : (A d).law.EM 2 = 3 / 2 * (1 / 2 - Δ d) := by
  rw [show (A d).law.EM 2 = _ from (A d).law.EM_succ 1, EM_one]
  simp only [Law.ESp, Law.E_succ, Law.E_zero, S_consS, S_zero, add_zero]
  have inner : ∀ x, ∑ x1, (A d).law.Q x1 * max ((A d).law.X x + (A d).law.X x1) 0 =
      1 / 2 * max ((A d).law.X x + -1) 0 + Δ d * max ((A d).law.X x + 0) 0 +
        (1 / 2 - Δ d) * max ((A d).law.X x + 1) 0 :=
    fun x => law_sum d (fun t => max ((A d).law.X x + t) 0)
  simp only [inner]
  rw [law_sum d (fun a => 1 / 2 * max (a + -1) 0 + Δ d * max (a + 0) 0 +
    (1 / 2 - Δ d) * max (a + 1) 0)]
  norm_num
  ring

/-- **The `h = 2` example**: `U_2 = (1/4,1/4,1/4,1/4)`, `Q_2 = (1/2,1/4,1/8,1/8)`:
`C_1 - 2 = 1/4`, `C_2 - 4 = 3/8`, and `C_n - 2n → 1`. -/
theorem example_h2 :
    (A 0).kernel.costBits 1 - 2 = 1 / 4 ∧ (A 0).kernel.costBits 2 - 4 = 3 / 8 ∧
      Tendsto (fun n : ℕ => (A 0).kernel.costBits n - n * 2) atTop (𝓝 1) := by
  have hh : (A 0).h = 2 := by rw [h_eq]; norm_num
  have hΔ : Δ 0 = 1 / 4 := by unfold Δ; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [(A 0).cost_eq (dyadic 0), EM_one, hh, hΔ]; norm_num
  · rw [(A 0).cost_eq (dyadic 0), EM_two, hh, hΔ]; norm_num
  · have := cost_limit 0
    rw [hh, hΔ] at this; norm_num at this; exact this

/-- **Limits for `h = 2, 3, 4, 8`:** `1, 3, 7, 127` bits. -/
theorem limits_examples :
    1 / (2 * Δ 0) - 1 = 1 ∧ 1 / (2 * Δ 1) - 1 = 3 ∧ 1 / (2 * Δ 2) - 1 = 7 ∧
      1 / (2 * Δ 6) - 1 = 127 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [limit_value] <;> norm_num

/-- **No universal `o(1/Δ)` bound.** Along the family, every increment lies in `{-1, 0, 1}`
and `Δ · lim (C_n - n h) → 1/2` as `h → ∞`. -/
theorem gap_times_limit :
    Tendsto (fun d : ℕ => Δ d * (1 / (2 * Δ d) - 1)) atTop (𝓝 (1 / 2)) := by
  have e : ∀ d, Δ d * (1 / (2 * Δ d) - 1) = 1 / 2 - (1 / 2) ^ (d + 2) := fun d => by
    have := Δ_pos d; unfold Δ at this ⊢; field_simp
  simp only [e]
  have : Tendsto (fun d : ℕ => (1 / 2 : ℝ) ^ (d + 2)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)).comp (tendsto_add_atTop_nat 2)
  simpa using tendsto_const_nhds.sub this

end Family

end CausalSpectrum.Walk

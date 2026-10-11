/-
Rényi entropy of countable laws, with infinite values.

A countable law is a weight sequence `w : ℕ → ℝ`, `w ≥ 0`, `∑ w = 1`.
* `mom α w = ∑' ofReal (w i ^ α)` in `ℝ≥0∞` (may be `∞` for `α < 1`);
* `renyiNe α w = ∞` if the moment is infinite, else `log₂(mom)/(1-α)`;
* `shannonBits w` (Shannon entropy in bits, may be `∞`); `H α w` glues them at `α = 1`;
* `Hinf w = -log₂ sup w`.
Elementary facts: power-sum data processing along a map to a finite type (both
directions of `α ≶ 1`) and the sandwich `H_∞ ≤ H_α ≤ α/(α-1) H_∞` for `α > 1`.
-/
import CausalSeed.RenyiFinite

noncomputable section
open Classical Finset
open scoped ENNReal
namespace CausalSpectrum.RenyiInf

/-! ### Definitions -/

def mom (α : ℝ) (w : ℕ → ℝ) : ℝ≥0∞ := ∑' i, ENNReal.ofReal (w i ^ α)

def shannonBits (w : ℕ → ℝ) : ℝ≥0∞ :=
  (∑' i, ENNReal.ofReal (Real.negMulLog (w i))) / ENNReal.ofReal (Real.log 2)

def renyiNe (α : ℝ) (w : ℕ → ℝ) : ℝ≥0∞ :=
  if mom α w = ⊤ then ⊤ else ENNReal.ofReal (Real.logb 2 (mom α w).toReal / (1 - α))

/-- Rényi entropy of order `α > 0` (bits), with values in `[0, ∞]`. -/
def H (α : ℝ) (w : ℕ → ℝ) : ℝ≥0∞ := if α = 1 then shannonBits w else renyiNe α w

/-- Min-entropy (bits). -/
def Hinf (w : ℕ → ℝ) : ℝ≥0∞ := ENNReal.ofReal (-Real.logb 2 (⨆ i, w i))

/-- The additive constant: `d_α` for `α ≠ 1`, `c⋆` at `α = 1`. -/
def dA (α : ℝ) : ℝ := if α = 1 then shannonOverhead else Renyi.dAlpha α

/-- A countable probability law. -/
structure IsLaw (w : ℕ → ℝ) : Prop where
  nonneg : ∀ i, 0 ≤ w i
  sum : HasSum w 1

/-! ### Power inequalities -/

theorem rpow_split {x α : ℝ} (hx : 0 ≤ x) (hα : α ≠ 0) : x ^ α = x * x ^ (α - 1) := by
  have := Real.rpow_add' hx (show (1:ℝ) + (α - 1) ≠ 0 by simpa using hα)
  rw [show (1:ℝ) + (α - 1) = α by ring, Real.rpow_one] at this
  exact this

theorem pow_tsum_ge {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (hs : Summable x) {α : ℝ} (hα : 1 ≤ α) :
    Summable (fun i => x i ^ α) ∧ ∑' i, x i ^ α ≤ (∑' i, x i) ^ α := by
  set S := ∑' i, x i
  have hS : 0 ≤ S := tsum_nonneg hx
  have hle : ∀ i, x i ≤ S := fun i => le_hasSum hs.hasSum i (fun j _ => hx j)
  have hα0 : α ≠ 0 := by linarith
  have hb : ∀ i, x i ^ α ≤ x i * S ^ (α - 1) := fun i => by
    rw [rpow_split (hx i) hα0]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hx i) (hle i) (by linarith)) (hx i)
  have hsm : Summable (fun i => x i ^ α) :=
    Summable.of_nonneg_of_le (fun i => Real.rpow_nonneg (hx i) _) hb (hs.mul_right _)
  refine ⟨hsm, ?_⟩
  calc ∑' i, x i ^ α ≤ ∑' i, x i * S ^ (α - 1) := hsm.tsum_le_tsum hb (hs.mul_right _)
    _ = S ^ α := by rw [tsum_mul_right, ← rpow_split hS hα0]

theorem pow_tsum_le {x : ℕ → ℝ} (hx : ∀ i, 0 ≤ x i) (hs : Summable x) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ENNReal.ofReal ((∑' i, x i) ^ α) ≤ ∑' i, ENNReal.ofReal (x i ^ α) := by
  set S := ∑' i, x i
  have hS : 0 ≤ S := tsum_nonneg hx
  rcases hS.eq_or_lt with h0 | hpos
  · rw [← h0, Real.zero_rpow hα.ne']; simp
  have hle : ∀ i, x i ≤ S := fun i => le_hasSum hs.hasSum i (fun j _ => hx j)
  rw [rpow_split hS hα.ne', show S = ∑' i, x i from rfl, ← tsum_mul_right,
    ENNReal.ofReal_tsum_of_nonneg (fun i => mul_nonneg (hx i) (Real.rpow_nonneg hS _))
      (hs.mul_right _)]
  refine ENNReal.tsum_le_tsum fun i => ENNReal.ofReal_le_ofReal ?_
  rcases (hx i).eq_or_lt with hz | hxp
  · rw [← hz]; simp [Real.zero_rpow hα.ne']
  rw [rpow_split (hx i) hα.ne']
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos hxp (hle i) (by linarith)) (hx i)

theorem rpow_le_self {x α : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (hα : 1 ≤ α) : x ^ α ≤ x := by
  rcases hx.eq_or_lt with h | h
  · rw [← h, Real.zero_rpow (by linarith)]
  · simpa using Real.rpow_le_rpow_of_exponent_ge h hx1 hα

/-! ### Data processing along a finite readout -/

def fib {β : Type*} (w : ℕ → ℝ) (f : ℕ → β) (b : β) (i : ℕ) : ℝ := if f i = b then w i else 0

def push {β : Type*} (w : ℕ → ℝ) (f : ℕ → β) (b : β) : ℝ := ∑' i, fib w f b i

variable {w : ℕ → ℝ}

theorem IsLaw.le_one (hw : IsLaw w) (i : ℕ) : w i ≤ 1 :=
  le_hasSum hw.sum i (fun j _ => hw.nonneg j)

theorem fib_nonneg {β : Type*} (hw : IsLaw w) (f : ℕ → β) (b i) : 0 ≤ fib w f b i := by
  unfold fib; split_ifs <;> simp [hw.nonneg]

theorem fib_le {β : Type*} (hw : IsLaw w) (f : ℕ → β) (b i) : fib w f b i ≤ w i := by
  unfold fib; split_ifs <;> simp [hw.nonneg]

theorem fib_summable {β : Type*} (hw : IsLaw w) (f : ℕ → β) (b) : Summable (fib w f b) :=
  Summable.of_nonneg_of_le (fib_nonneg hw f b) (fib_le hw f b) hw.sum.summable

theorem push_nonneg {β : Type*} (hw : IsLaw w) (f : ℕ → β) (b) : 0 ≤ push w f b :=
  tsum_nonneg (fib_nonneg hw f b)

theorem weight_le_push {β : Type*} (hw : IsLaw w) (f : ℕ → β) (i) : w i ≤ push w f (f i) := by
  have h := le_hasSum (fib_summable hw f (f i)).hasSum i (fun j _ => fib_nonneg hw f (f i) j)
  simpa [fib, push] using h

theorem push_event {β : Type*} [Fintype β] (hw : IsLaw w) (f : ℕ → β) (P : β → Prop) :
    (∑ b, if P b then push w f b else 0) = ∑' i, if P (f i) then w i else 0 := by
  have hs : ∀ b ∈ (univ : Finset β), Summable (fun i => if P b then fib w f b i else 0) := by
    intro b _
    by_cases hb : P b
    · simpa [hb] using fib_summable hw f b
    · simp [hb]
  calc
    _ = ∑ b, ∑' i, if P b then fib w f b i else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : P b <;> simp [hb, push]
    _ = ∑' i, ∑ b, if P b then fib w f b i else 0 := (Summable.tsum_finsetSum hs).symm
    _ = _ := tsum_congr fun i => by
      simp only [fib]
      rw [Finset.sum_eq_single (f i)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp

theorem push_total {β : Type*} [Fintype β] (hw : IsLaw w) (f : ℕ → β) :
    ∑ b, push w f b = 1 := by
  simpa [hw.sum.tsum_eq] using push_event hw f (fun _ => True)

theorem fib_rpow {β : Type*} (f : ℕ → β) (b i) {α : ℝ} (hα : 0 < α) :
    fib w f b i ^ α = if f i = b then w i ^ α else 0 := by
  unfold fib; split_ifs <;> simp [Real.zero_rpow hα.ne']

/-- `α ≥ 1`: merging atoms can only increase the power sum. -/
theorem dp_ge {β : Type*} [Fintype β] (hw : IsLaw w) (f : ℕ → β) {α : ℝ} (hα : 1 ≤ α) :
    Summable (fun i => w i ^ α) ∧ ∑' i, w i ^ α ≤ ∑ b, push w f b ^ α := by
  have hα0 : 0 < α := by linarith
  have hsm : Summable (fun i => w i ^ α) := (pow_tsum_ge hw.nonneg hw.sum.summable hα).1
  refine ⟨hsm, ?_⟩
  have hfs : ∀ b ∈ (univ : Finset β), Summable (fun i => fib w f b i ^ α) := fun b _ =>
    (pow_tsum_ge (fib_nonneg hw f b) (fib_summable hw f b) hα).1
  calc ∑' i, w i ^ α = ∑' i, ∑ b, fib w f b i ^ α := tsum_congr fun i => by
        simp_rw [fib_rpow f _ i hα0]; rw [Finset.sum_ite_eq]; simp
    _ = ∑ b, ∑' i, fib w f b i ^ α := Summable.tsum_finsetSum hfs
    _ ≤ ∑ b, push w f b ^ α := Finset.sum_le_sum fun b _ =>
        (pow_tsum_ge (fib_nonneg hw f b) (fib_summable hw f b) hα).2

/-- `α ≤ 1`: merging atoms can only decrease the power sum (in `ℝ≥0∞`). -/
theorem dp_le {β : Type*} [Fintype β] (hw : IsLaw w) (f : ℕ → β) {α : ℝ} (hα : 0 < α)
    (hα1 : α ≤ 1) :
    ∑ b, ENNReal.ofReal (push w f b ^ α) ≤ mom α w := by
  calc ∑ b, ENNReal.ofReal (push w f b ^ α)
      ≤ ∑ b, ∑' i, ENNReal.ofReal (fib w f b i ^ α) := Finset.sum_le_sum fun b _ =>
        pow_tsum_le (fib_nonneg hw f b) (fib_summable hw f b) hα hα1
    _ = ∑' i, ∑ b, ENNReal.ofReal (fib w f b i ^ α) :=
        (Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)).symm
    _ = mom α w := tsum_congr fun i => by
        simp_rw [fib_rpow f _ i hα]
        rw [Finset.sum_eq_single (f i)]
        · simp
        · intro b _ hb; simp [Ne.symm hb]
        · simp

/-! ### Basic facts about `mom` -/

theorem exists_pos (hw : IsLaw w) : ∃ i, 0 < w i := by
  by_contra h
  push_neg at h
  have : w = 0 := funext fun i => le_antisymm (h i) (hw.nonneg i)
  have h1 := hw.sum
  rw [this] at h1
  exact zero_ne_one (h1.unique hasSum_zero).symm

theorem mom_eq_of_ge (hw : IsLaw w) {α : ℝ} (hα : 1 ≤ α) :
    mom α w = ENNReal.ofReal (∑' i, w i ^ α) :=
  (ENNReal.ofReal_tsum_of_nonneg (fun i => Real.rpow_nonneg (hw.nonneg i) _)
    (pow_tsum_ge hw.nonneg hw.sum.summable hα).1).symm

theorem tsum_rpow_pos (hw : IsLaw w) {α : ℝ} (hα : 1 ≤ α) : 0 < ∑' i, w i ^ α := by
  obtain ⟨i, hi⟩ := exists_pos hw
  have hs := (pow_tsum_ge hw.nonneg hw.sum.summable hα).1
  exact lt_of_lt_of_le (Real.rpow_pos_of_pos hi α)
    (le_hasSum hs.hasSum i (fun j _ => Real.rpow_nonneg (hw.nonneg j) _))

theorem tsum_rpow_le_one (hw : IsLaw w) {α : ℝ} (hα : 1 ≤ α) : ∑' i, w i ^ α ≤ 1 := by
  have h := (pow_tsum_ge hw.nonneg hw.sum.summable hα).2
  rwa [hw.sum.tsum_eq, Real.one_rpow] at h

/-- The real Rényi entropy for `α > 1`. -/
def hreal (α : ℝ) (w : ℕ → ℝ) : ℝ := Real.logb 2 (∑' i, w i ^ α) / (1 - α)

theorem hreal_nonneg (hw : IsLaw w) {α : ℝ} (hα : 1 < α) : 0 ≤ hreal α w := by
  unfold hreal
  apply div_nonneg_of_nonpos
  · exact Real.logb_nonpos (by norm_num) (tsum_rpow_pos hw hα.le).le (tsum_rpow_le_one hw hα.le)
  · linarith

theorem H_of_gt (hw : IsLaw w) {α : ℝ} (hα : 1 < α) : H α w = ENNReal.ofReal (hreal α w) := by
  unfold H renyiNe
  rw [if_neg hα.ne', mom_eq_of_ge hw hα.le, if_neg ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal (tsum_rpow_pos hw hα.le).le]
  rfl

/-! ### Min-entropy versus `H_α`, `α > 1` -/

theorem bdd (hw : IsLaw w) : BddAbove (Set.range w) := ⟨1, by
  rintro _ ⟨i, rfl⟩; exact hw.le_one i⟩

theorem le_sup (hw : IsLaw w) (i : ℕ) : w i ≤ ⨆ j, w j := le_ciSup (bdd hw) i

theorem sup_pos (hw : IsLaw w) : 0 < ⨆ j, w j := by
  obtain ⟨i, hi⟩ := exists_pos hw
  exact hi.trans_le (le_sup hw i)

theorem sup_le_one (hw : IsLaw w) : (⨆ j, w j) ≤ 1 := ciSup_le hw.le_one

theorem hinf_real_nonneg (hw : IsLaw w) : 0 ≤ -Real.logb 2 (⨆ j, w j) := by
  have := Real.logb_nonpos (b := 2) (by norm_num) (sup_pos hw).le (sup_le_one hw)
  linarith

theorem hreal_bounds (hw : IsLaw w) {α : ℝ} (hα : 1 < α) :
    -Real.logb 2 (⨆ j, w j) ≤ hreal α w ∧
      hreal α w ≤ α / (α - 1) * (-Real.logb 2 (⨆ j, w j)) := by
  set M := ⨆ j, w j
  set m := ∑' i, w i ^ α
  have hM := sup_pos hw
  have hm := tsum_rpow_pos hw hα.le
  have hs := (pow_tsum_ge hw.nonneg hw.sum.summable hα.le).1
  have hα0 : α ≠ 0 := by linarith
  -- m ≤ M^(α-1)
  have h1 : m ≤ M ^ (α - 1) := by
    have hb : ∀ i, w i ^ α ≤ w i * M ^ (α - 1) := fun i => by
      rw [rpow_split (hw.nonneg i) hα0]
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (hw.nonneg i) (le_sup hw i) (by linarith)) (hw.nonneg i)
    calc m ≤ ∑' i, w i * M ^ (α - 1) := hs.tsum_le_tsum hb (hw.sum.summable.mul_right _)
      _ = M ^ (α - 1) := by rw [tsum_mul_right, hw.sum.tsum_eq, one_mul]
  -- M^α ≤ m
  have h2 : M ^ α ≤ m := by
    have hM' : M ≤ m ^ (1 / α) := ciSup_le fun i => by
      have hi : w i ^ α ≤ m := le_hasSum hs.hasSum i (fun j _ => Real.rpow_nonneg (hw.nonneg j) _)
      calc w i = (w i ^ α) ^ (1 / α) := by
            rw [← Real.rpow_mul (hw.nonneg i), mul_one_div_cancel hα0, Real.rpow_one]
        _ ≤ m ^ (1 / α) := Real.rpow_le_rpow (Real.rpow_nonneg (hw.nonneg i) _) hi
            (by positivity)
    calc M ^ α ≤ (m ^ (1 / α)) ^ α := Real.rpow_le_rpow hM.le hM' (by linarith)
      _ = m := by rw [← Real.rpow_mul hm.le, one_div_mul_cancel hα0, Real.rpow_one]
  have hneg : 1 - α < 0 := by linarith
  unfold hreal
  constructor
  · have hl : Real.logb 2 m ≤ (α - 1) * Real.logb 2 M := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hm h1
      rwa [Real.logb_rpow_eq_mul_logb_of_pos hM] at this
    rw [le_div_iff_of_neg hneg]; nlinarith
  · have hl : α * Real.logb 2 M ≤ Real.logb 2 m := by
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (Real.rpow_pos_of_pos hM α) h2
      rwa [Real.logb_rpow_eq_mul_logb_of_pos hM] at this
    rw [div_le_iff_of_neg hneg]
    have ha1 : α - 1 ≠ 0 := by linarith
    have : α / (α - 1) * -Real.logb 2 M * (1 - α) = α * Real.logb 2 M := by
      field_simp; ring
    rw [this]; exact hl

theorem dAlpha_le {α : ℝ} (hα : 1 < α) : 0 ≤ Renyi.dAlpha α ∧ Renyi.dAlpha α ≤ 1 / (α - 1) := by
  unfold Renyi.dAlpha
  have ht := Renyi.theta_pos (show 0 < α by linarith)
  have hθ1 : theta α ≤ 1 := by
    unfold theta
    have h1 : (2:ℝ) ^ (-α) ≤ 1 / 2 := by
      rw [show (1:ℝ)/2 = 2 ^ (-1:ℝ) by norm_num]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have h2 : (2:ℝ) ^ (-α) / α ≤ 1 / 2 :=
      (div_le_self (by positivity) hα.le).trans h1
    linarith
  have hθh : 1 / 2 ≤ theta α := by
    unfold theta
    have : 0 ≤ (2:ℝ) ^ (-α) / α := by positivity
    linarith
  have hl0 : Real.logb 2 (theta α) ≤ 0 := Real.logb_nonpos (by norm_num) ht.le hθ1
  have hl1 : -1 ≤ Real.logb 2 (theta α) := by
    have := Real.logb_le_logb_of_le (b := 2) (by norm_num) (by norm_num) hθh
    rwa [show (1:ℝ)/2 = 2 ^ (-1:ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)] at this
  have hneg : 1 - α < 0 := by linarith
  constructor
  · exact div_nonneg_of_nonpos hl0 hneg.le
  · rw [div_le_iff_of_neg hneg]
    have ha1 : α - 1 ≠ 0 := by linarith
    have : 1 / (α - 1) * (1 - α) = -1 := by field_simp; ring
    linarith

#print axioms dp_ge
#print axioms dp_le
#print axioms hreal_bounds

end CausalSpectrum.RenyiInf

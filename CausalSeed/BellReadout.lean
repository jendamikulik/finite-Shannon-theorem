/-
Repeated Bell-label readout, 6 November 2026.

Proved here, with no sorry:

* a Bernoulli tape of `N` bits has Shannon entropy `N * h₂(e)` bits;
* a fresh tape bit has flip probability `e` after any positive-weight past;
* an exact constant-question transcript, being a function of the seed, forces
  seed entropy at least `N * h₂(e)`;
* four messages can carry the label;
* separate majorities on odd `m` recover the label with probability `uₘ(e)²`;
* a guess through `K` messages is right for at most `K` of the four labels,
  so any mixture succeeds with probability at most `K/4`, and
  `K ≥ ⌈4v⌉` when that probability equals `v`;
* `u₅(1/4) = 459/512` and `u₅(1/4)² > 3/4`, so any mixture whose
  label-recovery frequency equals that probability needs `K ≥ 4`;
* at `e = 0`, the entropy is `0` and `u₁(0) = 1`, hence `⌈4 u₁(0)²⌉ = 4`;
* for every `e < 1/2` some odd `m` has `uₘ(e)² > 3/4`.

The step from an arbitrary exact simulator to the frequency `uₘ(e)²` is the
hypothesis of `memory_of_identification`: for a fixed seed the guess factors
through the `K` messages, and the Bernoulli majority is proved separately.
Not proved: consciousness, a physical implementation, generation of the
instruments by the illustrative Hamiltonian, a quantum advantage, sharpness
of the memory bound before the four-state threshold, or noncommuting
questions under the same contract.
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

noncomputable section

namespace CausalSpectrum
namespace BellReadout

def bern (e : ℝ) : Bool → ℝ
  | true => e
  | false => 1 - e

def Hn {α : Type} [Fintype α] (p : α → ℝ) : ℝ :=
  ∑ a, Real.negMulLog (p a)

def h2 (e : ℝ) : ℝ := Real.binEntropy e / Real.log 2

def H {α : Type} [Fintype α] (p : α → ℝ) : ℝ := Hn p / Real.log 2

theorem bern_mass (e : ℝ) : ∑ b, bern e b = 1 := by
  simp [bern]

theorem Hn_bern (e : ℝ) : Hn (bern e) = Real.binEntropy e := by
  unfold Hn bern
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  simp

theorem h2_zero : h2 0 = 0 := by
  simp [h2]

theorem h2_half : h2 (1 / 2) = 1 := by
  have : (1 / 2 : ℝ) = 2⁻¹ := by norm_num
  rw [h2, this, Real.binEntropy_two_inv]
  exact div_self (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne'

def prodP {α β : Type} (p : α → ℝ) (q : β → ℝ) : α × β → ℝ :=
  fun z => p z.1 * q z.2

theorem Hn_prod {α β : Type} [Fintype α] [Fintype β] (p : α → ℝ) (q : β → ℝ)
    (hp : ∑ a, p a = 1) (hq : ∑ b, q b = 1) :
    Hn (prodP p q) = Hn p + Hn q := by
  unfold Hn prodP
  rw [Fintype.sum_prod_type]
  simp_rw [Real.negMulLog_mul, Finset.sum_add_distrib]
  have h1 : ∑ a, ∑ b, q b * Real.negMulLog (p a) =
      ∑ a, Real.negMulLog (p a) * ∑ b, q b := by
    simp_rw [mul_comm (q _), Finset.mul_sum]
  have h2 : ∑ a, ∑ b, p a * Real.negMulLog (q b) =
      (∑ a, p a) * ∑ b, Real.negMulLog (q b) := by
    simp_rw [← Finset.mul_sum, Finset.sum_mul]
  rw [h1, h2, hp, hq]
  simp only [mul_one, one_mul]

def tape (N : ℕ) (e : ℝ) : (Fin N → Bool) → ℝ :=
  fun s => ∏ i, bern e (s i)

theorem tape_zero (e : ℝ) (s : Fin 0 → Bool) : tape 0 e s = 1 := by
  simp [tape]

theorem tape_cons (N : ℕ) (e : ℝ) (b : Bool) (t : Fin N → Bool) :
    tape (N + 1) e (Fin.cons b t) = bern e b * tape N e t := by
  unfold tape
  rw [Fin.prod_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

def tapeSplit (N : ℕ) : Bool × (Fin N → Bool) ≃ (Fin (N + 1) → Bool) :=
  Fin.consEquiv fun _ => Bool

theorem tape_mass (N : ℕ) (e : ℝ) : ∑ s, tape N e s = 1 := by
  induction N with
  | zero =>
    rw [Fintype.sum_unique]
    simp [tape]
  | succ N ih =>
    rw [← Equiv.sum_comp (tapeSplit N) (fun s => tape (N + 1) e s)]
    simp_rw [show ∀ p : Bool × (Fin N → Bool),
        tape (N + 1) e ((tapeSplit N) p) = bern e p.1 * tape N e p.2 by
      intro p
      have hsplit : (tapeSplit N) p = Fin.cons p.1 p.2 := rfl
      rw [hsplit]
      exact tape_cons N e p.1 p.2]
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ih, mul_one, bern_mass]

theorem Hn_tape (N : ℕ) (e : ℝ) : Hn (tape N e) = (N : ℝ) * Hn (bern e) := by
  induction N with
  | zero =>
    unfold Hn
    simp [tape_zero, Real.negMulLog_one]
  | succ N ih =>
    have hsplit : Hn (tape (N + 1) e) = Hn (prodP (bern e) (tape N e)) := by
      unfold Hn
      rw [← Equiv.sum_comp (tapeSplit N)
        (fun s => Real.negMulLog (tape (N + 1) e s))]
      simp_rw [show ∀ p : Bool × (Fin N → Bool),
          Real.negMulLog (tape (N + 1) e ((tapeSplit N) p)) =
            Real.negMulLog (bern e p.1 * tape N e p.2) by
        intro p
        have hsplit : (tapeSplit N) p = Fin.cons p.1 p.2 := rfl
        rw [hsplit, tape_cons]]
      rfl
    rw [hsplit, Hn_prod (bern e) (tape N e) (bern_mass e) (tape_mass N e), ih,
      Nat.cast_add, Nat.cast_one]
    ring

theorem tape_entropy (N : ℕ) (e : ℝ) : H (tape N e) = (N : ℝ) * h2 e := by
  unfold H h2
  rw [Hn_tape, Hn_bern, mul_div_assoc]

theorem tape_snoc (N : ℕ) (e : ℝ) (t : Fin N → Bool) (b : Bool) :
    tape (N + 1) e (Fin.snoc t b) = tape N e t * bern e b := by
  unfold tape
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl ?_
    intro i _
    simp
  · simp

theorem conditional_next (N : ℕ) (e : ℝ) (t : Fin N → Bool) (b : Bool)
    (ht : tape N e t ≠ 0) :
    tape (N + 1) e (Fin.snoc t b) / tape N e t = bern e b := by
  rw [tape_snoc, mul_div_cancel_left₀ _ ht]

def report (bit noise : Bool) : Bool := bit != noise

theorem report_flip_prob (e : ℝ) (bit : Bool) :
    (∑ n : Bool, if report bit n ≠ bit then bern e n else 0) = e := by
  cases bit <;> rw [Fintype.sum_bool] <;> simp [report, bern]

theorem negMulLog_add_ge (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.negMulLog (x + y) ≤ Real.negMulLog x + Real.negMulLog y := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [Real.negMulLog_zero]
  rcases hy.eq_or_lt with rfl | hy
  · simp [Real.negMulLog_zero]
  have hrew :
      Real.negMulLog x + Real.negMulLog y - Real.negMulLog (x + y)
        = x * Real.log ((x + y) / x) + y * Real.log ((x + y) / y) := by
    unfold Real.negMulLog
    rw [Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity)]
    ring
  have h1 : 0 ≤ Real.log ((x + y) / x) :=
    Real.log_nonneg ((one_le_div hx).mpr (by linarith))
  have h2 : 0 ≤ Real.log ((x + y) / y) :=
    Real.log_nonneg ((one_le_div hy).mpr (by linarith))
  linarith [mul_nonneg hx.le h1, mul_nonneg hy.le h2]

theorem negMulLog_sum_ge {α : Type} (s : Finset α) (p : α → ℝ)
    (hp : ∀ a ∈ s, 0 ≤ p a) :
    Real.negMulLog (∑ a ∈ s, p a) ≤ ∑ a ∈ s, Real.negMulLog (p a) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Real.negMulLog_zero]
  | @insert a s ha ih =>
    have hpa : 0 ≤ p a := hp a (Finset.mem_insert_self a s)
    have hps : ∀ b ∈ s, 0 ≤ p b := fun b hb => hp b (Finset.mem_insert_of_mem hb)
    have hsum : 0 ≤ ∑ b ∈ s, p b := Finset.sum_nonneg hps
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    linarith [negMulLog_add_ge (p a) (∑ b ∈ s, p b) hpa hsum, ih hps]

def push {α β : Type} [Fintype α] [DecidableEq β] (f : α → β) (p : α → ℝ) (b : β) : ℝ :=
  ∑ a, if f a = b then p a else 0

theorem Hn_push_le {α β : Type} [Fintype α] [Fintype β] [DecidableEq β]
    (f : α → β) (p : α → ℝ) (hp : ∀ a, 0 ≤ p a) :
    Hn (push f p) ≤ Hn p := by
  classical
  unfold Hn push
  have hpoint : ∀ b, Real.negMulLog (∑ a, if f a = b then p a else 0) ≤
      ∑ a, Real.negMulLog (if f a = b then p a else 0) := by
    intro b
    exact negMulLog_sum_ge Finset.univ (fun a => if f a = b then p a else 0)
      (fun a _ => by
        by_cases h : f a = b
        · simp [h, hp a]
        · simp [h])
  refine le_trans (Finset.sum_le_sum fun b _ => hpoint b) ?_
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl ?_)
  intro a _
  rw [Finset.sum_eq_single (f a)]
  · rw [ite_eq_left rfl]
  · intro b _ hb
    rw [ite_eq_right (Ne.symm hb)]
    simp [Real.negMulLog_zero]
  · intro h
    exact absurd (Finset.mem_univ (f a)) h

theorem seed_lower {α : Type} [Fintype α] (N : ℕ) (e : ℝ) (p : α → ℝ)
    (f : α → Fin N → Bool) (hp : ∀ a, 0 ≤ p a)
    (hexact : ∀ t, push f p t = tape N e t) :
    (N : ℝ) * h2 e ≤ H p := by
  have hpush : Hn (push f p) ≤ Hn p := Hn_push_le f p hp
  have heq : Hn (push f p) = Hn (tape N e) := by
    unfold Hn
    simp_rw [hexact]
  have htape : Hn (tape N e) = (N : ℝ) * Real.binEntropy e := by
    rw [Hn_tape, Hn_bern]
  rw [heq, htape] at hpush
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hdiv : (N : ℝ) * Real.binEntropy e / Real.log 2 ≤ Hn p / Real.log 2 :=
    div_le_div_of_nonneg_right hpush hlog.le
  simpa [H, h2, mul_div_assoc] using hdiv

theorem four_labels_inject : ∃ enc : Fin 4 → Fin 4, Function.Injective enc :=
  ⟨id, Function.injective_id⟩

def binomProb (m k : ℕ) (e : ℝ) : ℝ :=
  (m.choose k : ℝ) * e ^ k * (1 - e) ^ (m - k)

def u (m : ℕ) (e : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m / 2 + 1), binomProb m k e

def binomTail (m : ℕ) (e : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (m + 1), ite (m / 2 + 1 ≤ k) (binomProb m k e) 0

def trueCount {m : ℕ} (s : Fin m → Bool) : ℕ :=
  (Finset.univ.filter fun i => s i = true).card

theorem binom_total (m : ℕ) (e : ℝ) :
    ∑ k ∈ Finset.range (m + 1), binomProb m k e = 1 := by
  have hpow := add_pow e (1 - e) m
  have hone : (e + (1 - e)) ^ m = 1 := by ring
  rw [hone] at hpow
  symm
  refine hpow.trans ?_
  refine Finset.sum_congr rfl ?_
  intro k _
  unfold binomProb
  ring

theorem sum_low_add_tail (n c : ℕ) (hc : c ≤ n) (f : ℕ → ℝ) :
    (∑ k ∈ Finset.range c, f k) +
      (∑ k ∈ Finset.range n, ite (c ≤ k) (f k) 0) =
      ∑ k ∈ Finset.range n, f k := by
  classical
  have hif : ∑ k ∈ Finset.range n, ite (c ≤ k) (f k) 0 =
      ∑ k ∈ Finset.Ico c n, f k := by
    rw [← Finset.sum_filter]
    have hfilter : Finset.filter (fun k => c ≤ k) (Finset.range n) = Finset.Ico c n := by
      ext k
      simp [Finset.mem_Ico, Finset.mem_range]
      omega
    rw [hfilter]
  have hunion : Finset.Ico 0 c ∪ Finset.Ico c n = Finset.Ico 0 n :=
    Finset.Ico_union_Ico_eq_Ico (Nat.zero_le c) hc
  have hdisj : Disjoint (Finset.Ico 0 c) (Finset.Ico c n) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    simp [Finset.mem_Ico] at hk1 hk2
    omega
  have hsplit : ∑ k ∈ Finset.Ico 0 n, f k =
      ∑ k ∈ Finset.Ico 0 c, f k + ∑ k ∈ Finset.Ico c n, f k := by
    rw [← hunion, Finset.sum_union hdisj]
  rw [hif, Finset.range_eq_Ico, Finset.range_eq_Ico]
  exact hsplit.symm

theorem u_add_tail (m : ℕ) (e : ℝ) : u m e + binomTail m e = 1 := by
  unfold u binomTail
  have hc : m / 2 + 1 ≤ m + 1 := by omega
  rw [sum_low_add_tail (m + 1) (m / 2 + 1) hc (fun k => binomProb m k e),
    binom_total]

theorem binomProb_nonneg (m k : ℕ) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) :
    0 ≤ binomProb m k e := by
  unfold binomProb
  positivity

theorem tail_nonneg (m : ℕ) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) : 0 ≤ binomTail m e := by
  unfold binomTail
  refine Finset.sum_nonneg ?_
  intro k _
  by_cases hk : m / 2 + 1 ≤ k
  · simpa [hk] using binomProb_nonneg m k e he0 he1
  · simp [hk]

theorem u_nonneg (m : ℕ) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) : 0 ≤ u m e := by
  unfold u
  refine Finset.sum_nonneg fun k _ => binomProb_nonneg m k e he0 he1

theorem tape_of_weight {m : ℕ} (e : ℝ) (s : Fin m → Bool) :
    tape m e s = e ^ trueCount s * (1 - e) ^ (m - trueCount s) := by
  classical
  unfold tape trueCount
  let trues := Finset.univ.filter fun i : Fin m => s i = true
  let falses := Finset.univ.filter fun i : Fin m => s i ≠ true
  have hsplit := (Finset.prod_filter_mul_prod_filter_not Finset.univ
    (fun i : Fin m => s i = true) (fun i => bern e (s i))).symm
  have htrue : ∏ i ∈ trues, bern e (s i) = ∏ i ∈ trues, e := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    simp [trues] at hi
    simp [bern, hi]
  have hfalse : ∏ i ∈ falses, bern e (s i) = ∏ i ∈ falses, (1 - e) := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    have hnot : s i ≠ true := by simpa [falses] using hi
    cases hs : s i
    · simp [bern]
    · exact absurd hs hnot
  have hcardf : falses.card = m - trues.card := by
    have hadd : trues.card + falses.card = m := by
      simpa [trues, falses, Fintype.card_fin] using
        Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset (Fin m)))
          (p := fun i => s i = true)
    omega
  rw [hsplit, htrue, hfalse, Finset.prod_const, Finset.prod_const, hcardf]

theorem card_weight (m k : ℕ) :
    (Finset.univ.filter fun s : Fin m → Bool => trueCount s = k).card = m.choose k := by
  classical
  let φ : {s : Fin m → Bool // trueCount s = k} ≃ {t : Finset (Fin m) // t.card = k} :=
    { toFun := fun s => ⟨Finset.univ.filter fun i => s.1 i = true, by
        exact s.2⟩
      invFun := fun t =>
        ⟨fun i => decide (i ∈ t.1), by
          show trueCount (fun i => decide (i ∈ t.1)) = k
          unfold trueCount
          have hset :
              (Finset.univ.filter fun i : Fin m => decide (i ∈ t.1) = true) = t.1 := by
            ext i
            simp [decide_eq_true_eq]
          rw [hset]
          exact t.2⟩
      left_inv := by
        intro s
        ext i
        cases h : s.1 i <;> simp [h, Finset.mem_filter]
      right_inv := by
        intro t
        ext i
        simp [decide_eq_true_eq] }
  have hcard := Fintype.card_congr φ
  have hleft : Fintype.card {s : Fin m → Bool // trueCount s = k} =
      (Finset.univ.filter fun s : Fin m → Bool => trueCount s = k).card :=
    Fintype.card_subtype (fun s : Fin m → Bool => trueCount s = k)
  have hright : Fintype.card {t : Finset (Fin m) // t.card = k} = m.choose k := by
    simp
  rw [← hleft, hcard, hright]

theorem weight_sum (m k : ℕ) (e : ℝ) :
    (∑ s : Fin m → Bool, if trueCount s = k then tape m e s else 0) = binomProb m k e := by
  classical
  have hconst : ∀ s : Fin m → Bool, trueCount s = k →
      tape m e s = e ^ k * (1 - e) ^ (m - k) := by
    intro s hs
    simpa [hs] using tape_of_weight (m := m) e s
  rw [← Finset.sum_filter]
  have : ∑ s ∈ Finset.univ.filter fun s : Fin m → Bool => trueCount s = k, tape m e s =
      ∑ s ∈ Finset.univ.filter fun s : Fin m → Bool => trueCount s = k,
        e ^ k * (1 - e) ^ (m - k) := by
    refine Finset.sum_congr rfl ?_
    intro s hs
    exact hconst s (by simpa using hs)
  rw [this, Finset.sum_const, card_weight]
  unfold binomProb
  ring

theorem majority_one (m : ℕ) (e : ℝ) :
    (∑ s : Fin m → Bool, if trueCount s ≤ m / 2 then tape m e s else 0) = u m e := by
  classical
  have hsplit : ∀ s : Fin m → Bool,
      (if trueCount s ≤ m / 2 then tape m e s else 0) =
        ∑ k ∈ Finset.range (m / 2 + 1), if trueCount s = k then tape m e s else 0 := by
    intro s
    by_cases hk : trueCount s ≤ m / 2
    · rw [Finset.sum_eq_single (trueCount s)]
      · simp [hk]
      · intro k _ hkne
        rw [ite_eq_right (Ne.symm hkne)]
      · intro hmem
        exact absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hk)) hmem
    · trans (0 : ℝ)
      · simp [hk]
      · symm
        refine Finset.sum_eq_zero ?_
        intro k hkmem
        have hne : trueCount s ≠ k := by
          intro heq
          have hk' : k ≤ m / 2 := by
            have : k < m / 2 + 1 := Finset.mem_range.mp hkmem
            omega
          exact hk (heq ▸ hk')
        simp [hne]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  unfold u
  refine Finset.sum_congr rfl fun k _ => weight_sum m k e

theorem majority_both (m : ℕ) (e : ℝ) :
    (∑ p : (Fin m → Bool) × (Fin m → Bool),
      if trueCount p.1 ≤ m / 2 ∧ trueCount p.2 ≤ m / 2 then
        tape m e p.1 * tape m e p.2 else 0) =
      u m e ^ 2 := by
  classical
  rw [Fintype.sum_prod_type]
  have hfac : ∀ s t : Fin m → Bool,
      (if trueCount s ≤ m / 2 ∧ trueCount t ≤ m / 2 then tape m e s * tape m e t else 0) =
        (if trueCount s ≤ m / 2 then tape m e s else 0) *
          (if trueCount t ≤ m / 2 then tape m e t else 0) := by
    intro s t
    by_cases hs : trueCount s ≤ m / 2 <;> by_cases ht : trueCount t ≤ m / 2
    · rw [ite_eq_left ⟨hs, ht⟩, ite_eq_left hs, ite_eq_left ht]
    · rw [ite_eq_right (fun h => ht h.2), ite_eq_left hs, ite_eq_right ht, mul_zero]
    · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs, ite_eq_left ht, zero_mul]
    · rw [ite_eq_right (fun h => hs h.1), ite_eq_right hs, ite_eq_right ht, zero_mul]
  simp_rw [hfac]
  simp_rw [← Finset.mul_sum]
  simp_rw [majority_one]
  rw [← Finset.sum_mul, majority_one]
  ring

def correctCount {K : ℕ} (enc : Fin 4 → Fin K) (guess : Fin K → Fin 4) : ℕ :=
  (Finset.univ.filter fun x : Fin 4 => guess (enc x) = x).card

theorem fixed_points_le (K : ℕ) (enc : Fin 4 → Fin K) (guess : Fin K → Fin 4) :
    correctCount enc guess ≤ K := by
  classical
  let s := Finset.univ.filter fun x : Fin 4 => guess (enc x) = x
  have hinj : Set.InjOn enc (s : Set (Fin 4)) := by
    intro x hx y hy hxy
    have hx' : guess (enc x) = x := by simpa [s] using hx
    have hy' : guess (enc y) = y := by simpa [s] using hy
    calc
      x = guess (enc x) := hx'.symm
      _ = guess (enc y) := by rw [hxy]
      _ = y := hy'
  have hle := Finset.card_le_card_of_injOn (s := s) (t := Finset.univ) enc
    (fun _ _ => Finset.mem_univ _) hinj
  simpa [correctCount, s, Fintype.card_fin] using hle

theorem mixture_le {ι : Type} [Fintype ι] (K : ℕ) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (enc : ι → Fin 4 → Fin K) (guess : ι → Fin K → Fin 4) :
    ∑ i, w i * ((correctCount (enc i) (guess i) : ℝ) / 4) ≤ (K : ℝ) / 4 := by
  have hpt : ∀ i, (correctCount (enc i) (guess i) : ℝ) ≤ K := by
    intro i
    exact_mod_cast fixed_points_le K (enc i) (guess i)
  have hsum : ∑ i, w i * (correctCount (enc i) (guess i) : ℝ) ≤ ∑ i, w i * (K : ℝ) := by
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw0 i)
  have hK : ∑ i, w i * (K : ℝ) = (K : ℝ) := by
    rw [← Finset.sum_mul, hw1, one_mul]
  have hdiv : ∑ i, w i * ((correctCount (enc i) (guess i) : ℝ) / 4) =
      (∑ i, w i * (correctCount (enc i) (guess i) : ℝ)) / 4 := by
    simp_rw [mul_div_assoc']
    exact Eq.symm (Finset.sum_div Finset.univ
      (fun i => w i * (correctCount (enc i) (guess i) : ℝ)) 4)
  linarith

theorem memory_of_identification {ι : Type} [Fintype ι] (K : ℕ) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (enc : ι → Fin 4 → Fin K) (guess : ι → Fin K → Fin 4)
    (v : ℝ)
    (hident : ∑ i, w i * ((correctCount (enc i) (guess i) : ℝ) / 4) = v) :
    v ≤ (K : ℝ) / 4 ∧ ⌈4 * v⌉₊ ≤ K := by
  have hv := mixture_le K w hw0 hw1 enc guess
  rw [hident] at hv
  refine ⟨hv, ?_⟩
  have h4 : 4 * v ≤ (K : ℝ) := by
    have hmul : 4 * v ≤ 4 * ((K : ℝ) / 4) := mul_le_mul_of_nonneg_left hv (by norm_num)
    have : (4 : ℝ) * ((K : ℝ) / 4) = K := by ring
    linarith
  exact Nat.ceil_le.mpr h4

theorem u_zero (m : ℕ) : u m 0 = 1 := by
  classical
  unfold u
  have h0 : binomProb m 0 0 = 1 := by
    unfold binomProb
    simp
  have hpos : ∀ k, 0 < k → binomProb m k 0 = 0 := by
    intro k hk
    unfold binomProb
    have : (0 : ℝ) ^ k = 0 := zero_pow (Nat.ne_of_gt hk)
    simp [this]
  rw [Finset.sum_eq_single 0]
  · exact h0
  · intro k _ hne
    exact hpos k (Nat.pos_of_ne_zero hne)
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem noiseless_resources : h2 0 = 0 ∧ u 1 0 = 1 ∧ ⌈4 * (u 1 0) ^ 2⌉₊ = 4 := by
  refine ⟨h2_zero, u_zero 1, ?_⟩
  rw [u_zero]
  norm_num

theorem u_five_quarter : u 5 (1 / 4) = 459 / 512 := by
  unfold u
  have hr : Finset.range (5 / 2 + 1) = Finset.range 3 := by decide
  rw [hr, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add]
  have c0 : Nat.choose 5 0 = 1 := by decide
  have c1 : Nat.choose 5 1 = 5 := by decide
  have c2 : Nat.choose 5 2 = 10 := by decide
  unfold binomProb
  simp [c0, c1, c2]
  norm_num

theorem quarter_forces_four : (3 : ℝ) / 4 < u 5 (1 / 4) ^ 2 := by
  rw [u_five_quarter]
  norm_num

theorem tail_mgf (m a : ℕ) (e t : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1) (ht : 0 ≤ t) :
    (∑ k ∈ Finset.range (m + 1), ite (a ≤ k) (binomProb m k e) 0) ≤
      Real.exp (-t * (a : ℝ)) * (1 - e + e * Real.exp t) ^ m := by
  classical
  have hterm : ∀ k, a ≤ k →
      binomProb m k e ≤ binomProb m k e * Real.exp (t * ((k : ℝ) - a)) := by
    intro k hk
    have hgap : (0 : ℝ) ≤ (k : ℝ) - a := sub_nonneg.mpr (by exact_mod_cast hk)
    have hge : 1 ≤ Real.exp (t * ((k : ℝ) - a)) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (mul_nonneg ht hgap)
    exact le_mul_of_one_le_right (binomProb_nonneg m k e he0 he1) hge
  have htail :
      (∑ k ∈ Finset.range (m + 1), ite (a ≤ k) (binomProb m k e) 0) ≤
        ∑ k ∈ Finset.range (m + 1), binomProb m k e * Real.exp (t * ((k : ℝ) - a)) := by
    refine Finset.sum_le_sum ?_
    intro k _
    by_cases ha : a ≤ k
    · simpa [ha] using hterm k ha
    · have hnn : 0 ≤ binomProb m k e * Real.exp (t * ((k : ℝ) - a)) :=
        mul_nonneg (binomProb_nonneg m k e he0 he1) (Real.exp_nonneg _)
      simpa [ha] using hnn
  have hfac : ∀ k : ℕ,
      binomProb m k e * Real.exp (t * ((k : ℝ) - a)) =
        Real.exp (-t * (a : ℝ)) * (binomProb m k e * Real.exp (t * (k : ℝ))) := by
    intro k
    have : t * ((k : ℝ) - a) = t * (k : ℝ) + (-t * (a : ℝ)) := by ring
    rw [this, Real.exp_add]
    ring
  have hsum :
      (∑ k ∈ Finset.range (m + 1),
        binomProb m k e * Real.exp (t * ((k : ℝ) - a))) =
        Real.exp (-t * (a : ℝ)) *
          ∑ k ∈ Finset.range (m + 1), binomProb m k e * Real.exp (t * (k : ℝ)) := by
    simp_rw [hfac, ← Finset.mul_sum]
  have hpow : ∀ k : ℕ, Real.exp (t * (k : ℝ)) = Real.exp t ^ k := by
    intro k
    rw [mul_comm, Real.exp_nat_mul]
  have hbin :
      (∑ k ∈ Finset.range (m + 1), binomProb m k e * Real.exp (t * (k : ℝ))) =
        (1 - e + e * Real.exp t) ^ m := by
    simp_rw [hpow]
    rw [show (1 - e + e * Real.exp t) = e * Real.exp t + (1 - e) by ring]
    rw [add_pow]
    refine Finset.sum_congr rfl ?_
    intro k _
    unfold binomProb
    rw [mul_pow]
    ring
  exact htail.trans (le_of_eq (by
    rw [hsum]
    exact congrArg (fun z => Real.exp (-t * (a : ℝ)) * z) hbin))

theorem rho_lt_one (e : ℝ) (_he0 : 0 ≤ e) (he1 : e < 1 / 2) :
    4 * e * (1 - e) < 1 := by
  have hne : 2 * e - 1 ≠ 0 := by linarith
  nlinarith [sq_pos_of_ne_zero hne]

theorem pow_inv_mul (x : ℝ) (hx : x ≠ 0) {a b : ℕ} (h : a ≤ b) :
    x ^ b * (x ^ a)⁻¹ = x ^ (b - a) :=
  (pow_sub₀ x hx h).symm

theorem chernoff_odd (m : ℕ) (hm : m % 2 = 1) (e : ℝ) (he0 : 0 < e) (he1 : e < 1 / 2) :
    binomTail m e ≤ 2 * e * (4 * e * (1 - e)) ^ (m / 2) := by
  have he1' : e ≤ 1 := by linarith
  let a : ℕ := m / 2 + 1
  have hodd : m = 2 * (m / 2) + 1 := by omega
  have hsub : m - a = m / 2 := by omega
  have hle : a ≤ m := by omega
  let t : ℝ := Real.log ((1 - e) / e)
  have hratio : 1 < (1 - e) / e := by
    rw [one_lt_div he0]
    linarith
  have ht : 0 < t := Real.log_pos hratio
  have hpos : 0 < (1 - e) / e := div_pos (by linarith) he0
  have hexp : Real.exp t = (1 - e) / e := Real.exp_log hpos
  have hmgf := tail_mgf m a e t he0.le he1' ht.le
  have htail : binomTail m e =
      ∑ k ∈ Finset.range (m + 1), ite (a ≤ k) (binomProb m k e) 0 := by
    simp [binomTail, a]
  rw [htail]
  refine le_trans hmgf ?_
  have hscale : 1 - e + e * Real.exp t = 2 * (1 - e) := by
    rw [hexp]
    field_simp [he0.ne']
    ring
  have hinv : Real.exp (-t * (a : ℝ)) = (e / (1 - e)) ^ a := by
    have hneg : -t * (a : ℝ) = -((a : ℝ) * t) := by ring
    rw [hneg, Real.exp_neg, Real.exp_nat_mul, hexp, ← inv_pow, inv_div]
  rw [hscale, hinv]
  apply le_of_eq
  have h1e : (1 - e) ≠ 0 := by linarith
  have hmulpow : (2 * (1 - e)) ^ m = 2 ^ m * (1 - e) ^ m := mul_pow _ _ _
  have hdivpow : (e / (1 - e)) ^ a = e ^ a * ((1 - e) ^ a)⁻¹ := by
    rw [div_pow, div_eq_mul_inv]
  rw [hmulpow, hdivpow, mul_assoc,
    mul_left_comm (((1 - e) ^ a)⁻¹) ((2 : ℝ) ^ m) ((1 - e) ^ m),
    ← mul_assoc, mul_comm (((1 - e) ^ a)⁻¹) ((1 - e) ^ m),
    pow_inv_mul (1 - e) h1e hle, hsub]
  have hea : e ^ a = e ^ (m / 2) * e := by
    have haeq : a = m / 2 + 1 := rfl
    rw [haeq, pow_succ]
  have htwo : (2 : ℝ) ^ m = 2 * 4 ^ (m / 2) := by
    conv_lhs => rw [hodd]
    rw [pow_add, pow_mul, pow_one]
    norm_num
    ring
  rw [hea, htwo]
  ring_nf
  rw [show (e * 4 - e ^ 2 * 4) = 4 * e * (1 - e) by ring]
  rw [mul_pow, mul_pow]
  ring

theorem exists_pow_lt {ρ ε : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hε : 0 < ε) :
    ∃ n : ℕ, ρ ^ n < ε := by
  by_cases hε1 : 1 ≤ ε
  · refine ⟨1, ?_⟩
    simpa [pow_one] using lt_of_lt_of_le hρ1 hε1
  · have hεlt : ε < 1 := lt_of_not_ge hε1
    have hlogρ : Real.log ρ < 0 := Real.log_neg hρ0 hρ1
    have hlogε : Real.log ε < 0 := Real.log_neg hε hεlt
    have _hdiv : 0 ≤ Real.log ε / Real.log ρ := by
      rw [div_nonneg_iff]
      exact Or.inr ⟨hlogε.le, hlogρ.le⟩
    set n : ℕ := Nat.ceil (Real.log ε / Real.log ρ)
    have hle : Real.log ε / Real.log ρ ≤ (n : ℝ) := (Nat.ceil_le).mp (le_refl n)
    have hmul : (n : ℝ) * Real.log ρ ≤ Real.log ε :=
      (div_le_iff_of_neg hlogρ).mp hle
    have hlogn : Real.log (ρ ^ n) ≤ Real.log ε := by
      rw [Real.log_pow]
      exact hmul
    have hρn : 0 < ρ ^ n := pow_pos hρ0 n
    have hle' : ρ ^ n ≤ ε := (Real.log_le_log_iff hρn hε).mp hlogn
    refine ⟨n + 1, ?_⟩
    calc
      ρ ^ (n + 1) = ρ ^ n * ρ := by rw [pow_succ]
      _ ≤ ε * ρ := mul_le_mul_of_nonneg_right hle' hρ0.le
      _ < ε := by nlinarith

theorem seven_eighths (m : ℕ) (e : ℝ) (he0 : 0 ≤ e) (he1 : e ≤ 1)
    (ht : binomTail m e ≤ 1 / 8) : (3 : ℝ) / 4 < u m e ^ 2 := by
  have hu : 7 / 8 ≤ u m e := by
    have hadd := u_add_tail m e
    have htail : 0 ≤ binomTail m e := tail_nonneg m e he0 he1
    linarith
  have hsq : (7 / 8 : ℝ) ^ 2 ≤ u m e ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hu 2
  have hbase : (3 : ℝ) / 4 < (7 / 8) ^ 2 := by norm_num
  linarith

theorem exists_odd_majority (e : ℝ) (he0 : 0 ≤ e) (he1 : e < 1 / 2) :
    ∃ m : ℕ, m % 2 = 1 ∧ (3 : ℝ) / 4 < u m e ^ 2 := by
  rcases he0.eq_or_lt with rfl | hepos
  · refine ⟨1, by decide, ?_⟩
    rw [u_zero]
    norm_num
  · set ρ : ℝ := 4 * e * (1 - e)
    have hρ0 : 0 < ρ := by
      have : 0 < 1 - e := by linarith
      positivity
    have hρ1 : ρ < 1 := rho_lt_one e he0 he1
    have htarget : 0 < 1 / (16 * e) := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt hρ0 hρ1 htarget
    refine ⟨2 * n + 1, by omega, ?_⟩
    have hm : (2 * n + 1) % 2 = 1 := by omega
    have hdiv : (2 * n + 1) / 2 = n := by omega
    have hch := chernoff_odd (2 * n + 1) hm e hepos he1
    rw [hdiv] at hch
    have hsmall : 2 * e * ρ ^ n < 1 / 8 := by
      have hmul := mul_lt_mul_of_pos_left hn (by positivity : (0 : ℝ) < 2 * e)
      have : (2 * e) * (1 / (16 * e)) = 1 / 8 := by
        field_simp [hepos.ne']
        ring
      linarith
    have ht : binomTail (2 * n + 1) e < 1 / 8 := lt_of_le_of_lt hch hsmall
    exact seven_eighths (2 * n + 1) e he0 (by linarith) ht.le

theorem quarter_forces_memory {ι : Type} [Fintype ι] (K : ℕ) (w : ι → ℝ)
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    (enc : ι → Fin 4 → Fin K) (guess : ι → Fin K → Fin 4)
    (hident : ∑ i, w i * ((correctCount (enc i) (guess i) : ℝ) / 4) = u 5 (1 / 4) ^ 2) :
    4 ≤ K := by
  have hK : ⌈4 * u 5 (1 / 4) ^ 2⌉₊ ≤ K :=
    (memory_of_identification K w hw0 hw1 enc guess (u 5 (1 / 4) ^ 2) hident).2
  have hgt : (3 : ℝ) < 4 * u 5 (1 / 4) ^ 2 := by
    have := quarter_forces_four
    linarith
  have hceil : 4 ≤ ⌈4 * u 5 (1 / 4) ^ 2⌉₊ := by
    have hnot : ¬ ⌈4 * u 5 (1 / 4) ^ 2⌉₊ ≤ 3 := by
      intro hle
      linarith [Nat.ceil_le.mp hle]
    omega
  exact hceil.trans hK

end BellReadout
end CausalSpectrum

end
